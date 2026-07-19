"""First-variation experiment for local rigidity of snub-cube equality poses.

The equality set consists of arbitrary outer viewing directions together with
a relative rotation that is a rotational symmetry of the snub cube.  Modulo
that finite group, fix the relative rotation to the identity.  A normal
direction to the equality set is an infinitesimal relative rotation about a
unit axis omega.

For a fixed outer view and omega this script computes, without finite
differences:

* the first derivative of the best width obstruction;
* the first derivative of the best balanced two/three-contact obstruction.

At an outer edge normal u, the support function is nonsmooth because both edge
endpoints are active.  Its one-sided directional derivative is the maximum of
the endpoint derivatives.  The translation LP dual polytope depends only on
the outer edge normals, so all of its extreme points (at most three contacts)
can be enumerated once per view.  Thousands of omega axes can then be checked
as matrix operations.

A uniformly positive three-contact derivative would support a new local
balanced-support rigidity theorem that covers the equality strata where the
existing triangle/LMD Local Theorem fails.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import time

import numpy as np
from scipy.optimize import minimize
from scipy.spatial import ConvexHull

try:
    import experiment_snub_cube as sc
    import experiment_snub_local as sl
except ModuleNotFoundError:
    from scripts import experiment_snub_cube as sc
    from scripts import experiment_snub_local as sl


def dual_extreme_points(normals: np.ndarray, tol: float = 2e-10) -> np.ndarray:
    """Rows are all <=3-supported lambda >= 0 with sum lambda=1, sum lambda*u=0."""
    m = len(normals)
    rows = []
    rhs = np.array([0.0, 0.0, 1.0])
    for size in (2, 3):
        for idx in itertools.combinations(range(m), size):
            a = np.vstack((normals[list(idx)].T, np.ones(size)))
            if size == 2:
                lam, _, _, _ = np.linalg.lstsq(a, rhs, rcond=None)
                if np.linalg.norm(a @ lam - rhs) > tol:
                    continue
            else:
                if abs(np.linalg.det(a)) < 1e-12:
                    continue
                lam = np.linalg.solve(a, rhs)
            if lam.min() < -tol:
                continue
            lam = np.maximum(lam, 0.0)
            lam /= lam.sum()
            row = np.zeros(m)
            row[list(idx)] = lam
            rows.append(row)
    if not rows:
        raise RuntimeError("no balanced dual extreme points")
    rows = np.unique(np.round(np.array(rows), 14), axis=0)
    return rows


def active_support_derivatives(q: np.ndarray, dq: np.ndarray,
                               normals: np.ndarray, active_tol: float = 2e-9) -> np.ndarray:
    """One-sided support derivatives for all axes and normals.

    q: (V,2), dq: (A,V,2), normals: (M,2).  Result: (A,M).
    """
    base = q @ normals.T
    active = base >= base.max(axis=0)[None, :] - active_tol
    deriv = np.einsum("avd,md->amv", dq, normals)
    deriv = np.where(active.T[None, :, :], deriv, -np.inf)
    return deriv.max(axis=2)


def evaluate_view_axes(theta: float, phi: float, axes: np.ndarray):
    """Return width and three-contact first derivatives for a batch of axes."""
    axes = np.asarray(axes, dtype=float)
    axes = axes / np.linalg.norm(axes, axis=1)[:, None]
    frame = sc.frame_matrix(theta, phi)
    mproj = frame[:2]
    q = sc.UNIT_VERTS @ mproj.T
    hull = ConvexHull(q)
    normals = hull.equations[:, :2]
    dual = dual_extreme_points(normals)

    # d/ds [exp(s [omega]_x) v] at zero is omega x v.
    dv3 = np.cross(axes[:, None, :], sc.UNIT_VERTS[None, :, :])
    dq = dv3 @ mproj.T
    hp = active_support_derivatives(q, dq, normals)
    hm = active_support_derivatives(q, dq, -normals)

    # Half the width derivative corresponds to balanced weights 1/2,1/2.
    width = 0.5 * (hp + hm)
    width_best = width.max(axis=1)

    # delta' = -h_B'.  clearance' is min_lambda lambda.delta'.  The
    # obstruction margin derivative is its negative.
    delta_dot = -hp
    clearance_dot = (delta_dot @ dual.T).min(axis=1)
    triple_best = -clearance_dot
    return width_best, triple_best, {
        "n_edges": len(normals),
        "n_dual_extremes": len(dual),
        "normal": frame[2],
    }


def fibonacci_sphere(n: int, phase: float = 0.5) -> np.ndarray:
    i = np.arange(n, dtype=float)
    z = 1.0 - 2.0 * (i + phase) / n
    golden = math.pi * (3.0 - math.sqrt(5.0))
    a = golden * i
    r = np.sqrt(np.maximum(0.0, 1.0 - z*z))
    return np.stack((r * np.cos(a), r * np.sin(a), z), axis=1)


def normal_to_angles(n: np.ndarray) -> tuple[float, float]:
    n = np.asarray(n, dtype=float)
    n /= np.linalg.norm(n)
    return math.atan2(n[1], n[0]), math.acos(float(np.clip(n[2], -1.0, 1.0)))


def random_views(rng: np.random.Generator, n: int):
    theta = rng.uniform(-math.pi, math.pi, n)
    phi = np.arccos(rng.uniform(-1.0, 1.0, n))
    return np.stack((theta, phi), axis=1)


def random_local_failure_views(rng: np.random.Generator, n: int):
    """Rejection-sample views where the existing triangle/LMD theorem fails."""
    out = []
    tested = 0
    while len(out) < n:
        batch = random_views(rng, max(1000, 14 * (n - len(out))))
        for theta, phi in batch:
            tested += 1
            normal = sc.frame_matrix(float(theta), float(phi))[2]
            if not sl.audit_direction(normal)["success"]:
                out.append((theta, phi))
                if len(out) == n:
                    break
    print(f"selected {n} Local-Theorem-failure views from {tested} candidates", flush=True)
    return np.array(out)


def evaluate_grid(views: np.ndarray, axes: np.ndarray, progress: int = 250):
    records = []
    t0 = time.time()
    for i, (theta, phi) in enumerate(views):
        width, triple, meta = evaluate_view_axes(float(theta), float(phi), axes)
        jw, jt = int(np.argmin(width)), int(np.argmin(triple))
        normal = meta["normal"]
        local_ok = sl.audit_direction(normal)["success"]
        records.append({
            "theta": float(theta), "phi": float(phi),
            "normal": normal.tolist(),
            "local_theorem": bool(local_ok),
            "min_width": float(width[jw]),
            "min_width_axis": axes[jw].tolist(),
            "min_triple": float(triple[jt]),
            "min_triple_axis": axes[jt].tolist(),
            "width_negative_fraction": float(np.mean(width < -2e-10)),
            "n_edges": meta["n_edges"],
            "n_dual_extremes": meta["n_dual_extremes"],
        })
        if progress and (i + 1) % progress == 0:
            best = min(r["min_triple"] for r in records)
            print(f"views {i+1}/{len(views)} elapsed={time.time()-t0:.1f}s min_triple={best:.8g}",
                  flush=True)
    return records


def first_variation(theta: float, phi: float, axis: np.ndarray):
    w, t, _ = evaluate_view_axes(theta, phi, np.asarray(axis)[None, :])
    return float(w[0]), float(t[0])


def optimize_record(record: dict, kind: str, maxiter: int):
    """Nelder-Mead refinement over view normal and rotation axis (six raw coordinates)."""
    x0 = np.r_[record["normal"], record[f"min_{kind}_axis"]]

    def objective(x):
        n, a = x[:3], x[3:]
        nn, an = np.linalg.norm(n), np.linalg.norm(a)
        if nn < 1e-8 or an < 1e-8:
            return 10.0
        theta, phi = normal_to_angles(n / nn)
        w, t = first_variation(theta, phi, a / an)
        return w if kind == "width" else t

    ans = minimize(objective, x0, method="Nelder-Mead",
                   options={"maxiter": maxiter, "xatol": 2e-11, "fatol": 2e-12})
    n = ans.x[:3] / np.linalg.norm(ans.x[:3])
    a = ans.x[3:] / np.linalg.norm(ans.x[3:])
    theta, phi = normal_to_angles(n)
    w, t = first_variation(theta, phi, a)
    return {
        "kind": kind,
        "success": bool(ans.success),
        "iterations": int(ans.nit),
        "normal": n.tolist(),
        "axis": a.tolist(),
        "width": w,
        "triple": t,
        "local_theorem": bool(sl.audit_direction(n)["success"]),
    }


def summarize(records: list[dict]):
    names = ("min", "p01", "p10", "median", "p90", "p99", "max")
    qs = [0, .01, .1, .5, .9, .99, 1]
    out = {"views": len(records)}
    for key in ("min_width", "min_triple", "width_negative_fraction"):
        vals = np.array([r[key] for r in records])
        out[key + "_quantiles"] = dict(zip(names, map(float, np.quantile(vals, qs))))
    for flag in (True, False):
        subset = [r for r in records if r["local_theorem"] == flag]
        label = "local_success" if flag else "local_failure"
        out[label + "_views"] = len(subset)
        if subset:
            out[label + "_min_triple"] = float(min(r["min_triple"] for r in subset))
            out[label + "_min_width"] = float(min(r["min_width"] for r in subset))
    return out


def validate_finite_difference(rng: np.random.Generator, n: int = 100,
                               eps: float = 1e-7):
    errors = []
    for theta, phi in random_views(rng, n):
        axis = rng.normal(size=3); axis /= np.linalg.norm(axis)
        wa, ta = first_variation(theta, phi, axis)
        pose = sc.pose_from_relative(theta, phi, sc.axis_angle(axis, eps))
        result = sc.evaluate_pose(pose)
        errors.append([abs(result.width_margin / sc.VERTEX_RADIUS / eps - wa),
                       abs((-result.clearance) / sc.VERTEX_RADIUS / eps - ta)])
    errors = np.array(errors)
    return {
        "count": n, "epsilon": eps,
        "width_max_abs_error": float(errors[:, 0].max()),
        "width_median_abs_error": float(np.median(errors[:, 0])),
        "triple_max_abs_error": float(errors[:, 1].max()),
        "triple_median_abs_error": float(np.median(errors[:, 1])),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--views", type=int, default=5000)
    ap.add_argument("--axes", type=int, default=1024)
    ap.add_argument("--optimize-starts", type=int, default=12)
    ap.add_argument("--optimize-iters", type=int, default=2500)
    ap.add_argument("--seed", type=int, default=20260719)
    ap.add_argument("--only-local-failures", action="store_true")
    ap.add_argument("--out", default=os.path.join(os.path.dirname(__file__),
                                                   "snub_rigidity_experiment.json"))
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    axes = fibonacci_sphere(args.axes)
    views = (random_local_failure_views(rng, args.views) if args.only_local_failures
             else random_views(rng, args.views))
    t0 = time.time()

    validation = validate_finite_difference(rng)
    print("finite-difference validation", json.dumps(validation, indent=2), flush=True)
    records = evaluate_grid(views, axes)
    result_summary = summarize(records)
    print("summary", json.dumps(result_summary, indent=2), flush=True)

    hard_triple = sorted(records, key=lambda r: r["min_triple"])[:args.optimize_starts]
    hard_width = sorted(records, key=lambda r: r["min_width"])[:args.optimize_starts]
    optimized = []
    for r in hard_triple:
        optimized.append(optimize_record(r, "triple", args.optimize_iters))
    for r in hard_width:
        optimized.append(optimize_record(r, "width", args.optimize_iters))
    print("optimized", json.dumps(optimized, indent=2), flush=True)

    payload = {
        "parameters": vars(args),
        "elapsed_seconds": time.time() - t0,
        "validation": validation,
        "summary": result_summary,
        "hardest_triple_views": hard_triple[:100],
        "hardest_width_views": hard_width[:100],
        "optimized": optimized,
    }
    with open(args.out, "w") as f:
        json.dump(payload, f, indent=2)
        f.write("\n")
    print(f"wrote {args.out}", flush=True)


if __name__ == "__main__":
    main()
