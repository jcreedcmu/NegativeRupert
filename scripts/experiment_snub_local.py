"""Pointwise audit of the existing Local Theorem for snub-cube equality poses.

At an equality pose, an outer vertex Q can be paired with the congruent inner
vertex obtained through a rotational symmetry, so delta=0.  In the epsilon ->
0 limit the remaining hypotheses reduce to finding three vertices which

* lie strictly on one side of the viewing plane (A_0),
* project to a triangle strictly containing the origin (Spanning_0), and
* are strictly locally maximally distant in the projected polygon (B_0).

This script searches all vertex triples for random and special viewing
directions.  Failure at a direction is a genuine warning that the existing
Local Theorem cannot cover a neighborhood centered on that equality pose.
Success is only pointwise evidence; a formal tree still needs positive,
interval-certified epsilon margins.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import time

import numpy as np

try:
    from experiment_snub_cube import UNIT_VERTS
except ModuleNotFoundError:  # imported as scripts.experiment_snub_local
    from scripts.experiment_snub_cube import UNIT_VERTS


COMBOS = np.array(list(itertools.combinations(range(24), 3)), dtype=np.int16)


def basis_from_normal(x: np.ndarray) -> np.ndarray:
    x = np.asarray(x, dtype=float)
    x /= np.linalg.norm(x)
    seed = np.array([0.0, 0.0, 1.0]) if abs(x[2]) < 0.9 else np.array([1.0, 0.0, 0.0])
    a = np.cross(seed, x)
    a /= np.linalg.norm(a)
    b = np.cross(x, a)
    return np.vstack((a, b))


def cross2(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    return a[..., 0] * b[..., 1] - a[..., 1] * b[..., 0]


def audit_direction(x: np.ndarray, tol: float = 2e-12):
    x = np.asarray(x, dtype=float)
    x /= np.linalg.norm(x)
    m = basis_from_normal(x)
    q = UNIT_VERTS @ m.T
    dv = q[:, None, :] - q[None, :, :]
    numer = np.einsum("id,ikd->ik", q, dv)
    denom = np.linalg.norm(q, axis=1)[:, None] * np.linalg.norm(dv, axis=2)
    np.fill_diagonal(numer, np.inf)
    np.fill_diagonal(denom, 1.0)
    cosine = np.divide(numer, denom, out=np.full_like(numer, -np.inf), where=denom > 1e-14)
    np.fill_diagonal(cosine, np.inf)
    bmargin = cosine.min(axis=1)
    side = UNIT_VERTS @ x

    best_score = -math.inf
    best = None
    for sigma in (1.0, -1.0):
        candidate = (sigma * side > tol) & (bmargin > tol)
        mask = candidate[COMBOS].all(axis=1)
        if not mask.any():
            continue
        triples = COMBOS[mask]
        a, b, c = q[triples[:, 0]], q[triples[:, 1]], q[triples[:, 2]]
        crosses = np.stack((cross2(a, b), cross2(b, c), cross2(c, a)), axis=1)
        contains = (crosses.min(axis=1) > tol) | (crosses.max(axis=1) < -tol)
        if not contains.any():
            continue
        triples = triples[contains]
        crosses = np.abs(crosses[contains])
        am = np.min(sigma * side[triples], axis=1)
        sm = crosses.min(axis=1)
        bm = np.min(bmargin[triples], axis=1)
        # The three margins have different units, but their minimum is a
        # useful robust selector and exposes any hypothesis approaching zero.
        score = np.minimum(np.minimum(am, sm), bm)
        j = int(np.argmax(score))
        if score[j] > best_score:
            best_score = float(score[j])
            best = {
                "vertices": triples[j].astype(int).tolist(),
                "sigma": int(sigma < 0),
                "A_margin": float(am[j]),
                "spanning_margin": float(sm[j]),
                "B_cosine_margin": float(bm[j]),
                "score": float(score[j]),
            }
    return {
        "success": best is not None,
        "normal": x.tolist(),
        "n_B_good": int(np.sum(bmargin > tol)),
        "n_B_good_positive": int(np.sum((bmargin > tol) & (side > tol))),
        "n_B_good_negative": int(np.sum((bmargin > tol) & (side < -tol))),
        "best": best,
    }


def random_normals(rng: np.random.Generator, n: int) -> np.ndarray:
    x = rng.normal(size=(n, 3))
    return x / np.linalg.norm(x, axis=1)[:, None]


def special_normals() -> list[tuple[str, np.ndarray]]:
    out = []
    for i in range(3):
        e = np.zeros(3); e[i] = 1
        out.append((f"axis_{i}", e))
    out.extend([
        ("face_diagonal_xy", np.array([1.0, 1.0, 0.0])),
        ("body_diagonal", np.array([1.0, 1.0, 1.0])),
    ])
    for i, v in enumerate(UNIT_VERTS):
        out.append((f"vertex_{i}", v))
    # Normals to planes determined by pairs of vertices are common sources of
    # coincident projections and Local-Theorem degeneracies.
    seen = set()
    for i in range(24):
        for j in range(i + 1, 24):
            d = UNIT_VERTS[i] - UNIT_VERTS[j]
            if np.linalg.norm(d) < 1e-12:
                continue
            d /= np.linalg.norm(d)
            # Canonical sign and rounded key remove duplicates.
            k = int(np.argmax(np.abs(d)))
            if d[k] < 0:
                d = -d
            key = tuple(np.round(d, 10))
            if key not in seen:
                seen.add(key)
                out.append((f"difference_{i}_{j}", d.copy()))
    return out


def summary(records: list[dict]) -> dict:
    success = [r for r in records if r["success"]]
    scores = np.array([r["best"]["score"] for r in success])
    margins = {
        key: np.array([r["best"][key] for r in success])
        for key in ("A_margin", "spanning_margin", "B_cosine_margin")
    }
    names = ("min", "p01", "p10", "median", "p90", "p99", "max")
    qs = [0, .01, .1, .5, .9, .99, 1]
    return {
        "count": len(records),
        "success_fraction": len(success) / len(records) if records else None,
        "score_quantiles": dict(zip(names, map(float, np.quantile(scores, qs)))) if len(scores) else {},
        "margin_quantiles": {
            key: dict(zip(names, map(float, np.quantile(vals, qs))))
            for key, vals in margins.items()
        },
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--random", type=int, default=100000)
    ap.add_argument("--seed", type=int, default=20260718)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(__file__),
                                                   "snub_local_experiment.json"))
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    t0 = time.time()

    random_records = []
    for i, x in enumerate(random_normals(rng, args.random)):
        random_records.append(audit_direction(x))
        if (i + 1) % 10000 == 0:
            print(f"random {i + 1}/{args.random} elapsed={time.time()-t0:.1f}s", flush=True)
    random_summary = summary(random_records)
    print("random", json.dumps(random_summary, indent=2), flush=True)

    specials = []
    for name, x in special_normals():
        rec = audit_direction(x)
        rec["name"] = name
        specials.append(rec)
    special_summary = summary(specials)
    failures = [r for r in specials if not r["success"]]
    print("special", json.dumps(special_summary, indent=2), flush=True)
    print("special failures", json.dumps(failures, indent=2), flush=True)

    hardest = sorted((r for r in random_records if r["success"]),
                     key=lambda r: r["best"]["score"])[:100]
    payload = {
        "parameters": vars(args),
        "elapsed_seconds": time.time() - t0,
        "random": random_summary,
        "special": special_summary,
        "special_failures": failures,
        "hardest_random": hardest,
    }
    with open(args.out, "w") as f:
        json.dump(payload, f, indent=2)
        f.write("\n")
    print(f"wrote {args.out}", flush=True)


if __name__ == "__main__":
    main()
