"""Eliminate the rotation-axis variables from the snub-cube local theorem.

For a fixed viewing normal, enumerate every proof-shaped balanced support
certificate and its conservative first-variation vector ``A / Bbar``.  If the
convex hull of these vectors contains the radius-``c`` ball about the origin,
then for every unit rotation axis ``omega`` some certificate satisfies

    omega . A >= c * Bbar >= c * B.

Thus one view certificate covers all rotation axes.  The centered inradius of
the convex hull is exactly ``min_omega max_certificate omega . A/Bbar`` and is
computed from its facets—there is no sampling over ``omega`` in this script.
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
    import experiment_snub_rigidity as sr
except ModuleNotFoundError:
    from scripts import experiment_snub_cube as sc
    from scripts import experiment_snub_local as sl
    from scripts import experiment_snub_rigidity as sr


def certificate_vectors(normal: np.ndarray, active_tol: float = 2e-9):
    """Return all distinct conservative A/Bbar vectors and their payloads."""
    normal = np.asarray(normal, dtype=float)
    normal /= np.linalg.norm(normal)
    theta, phi = sr.normal_to_angles(normal)
    frame = sc.frame_matrix(theta, phi)
    lmap = frame[:2]
    q = sc.UNIT_VERTS @ lmap.T
    hull = ConvexHull(q)
    normals2 = hull.equations[:, :2]
    dual = sr.dual_extreme_points(normals2)
    base = q @ normals2.T
    active = base >= base.max(axis=0)[None, :] - active_tol

    points = []
    payloads = []
    for lam in dual:
        contacts = np.flatnonzero(lam > 1e-10)
        raw_normals = []
        oriented_edges = []
        support_pairs = []
        active_vertices = []
        raw_weights = []
        for j in contacts:
            a, b = map(int, hull.simplices[j])
            edge2 = q[b] - q[a]
            raw = np.array([-edge2[1], edge2[0]])
            if raw @ normals2[j] < 0:
                raw = -raw
                sigma = -1
            else:
                sigma = 1
            scale = float(raw @ normals2[j])
            raw_normals.append(raw)
            oriented_edges.append(
                sigma * (sc.UNIT_VERTS[b] - sc.UNIT_VERTS[a]))
            support_pairs.append((a, b, sigma))
            active_vertices.append(np.flatnonzero(active[:, j]))
            raw_weights.append(lam[j] / scale)

        raw_normals = np.array(raw_normals)
        oriented_edges = np.array(oriented_edges)
        raw_weights = np.array(raw_weights)
        lifted = np.cross(normal[None, :], oriented_edges)
        bbar = float(np.sum(raw_weights
                            * np.linalg.norm(oriented_edges, axis=1)))
        for chosen in itertools.product(*active_vertices):
            verts = sc.UNIT_VERTS[np.array(chosen)]
            avec = np.einsum("i,ij->j", raw_weights,
                              np.cross(verts, lifted))
            points.append(avec / bbar)
            payloads.append({
                "support_pairs": [list(map(int, row))
                                  for row in support_pairs],
                "support_vertices": list(map(int, chosen)),
                "raw_weights": raw_weights.tolist(),
                "A": avec.tolist(),
                "Bbar": bbar,
            })

    # Qhull and later certificate selection do not benefit from duplicates.
    unique = {}
    for point, payload in zip(points, payloads):
        key = tuple(np.round(point, 12))
        unique.setdefault(key, (point, payload))
    points = np.array([row[0] for row in unique.values()])
    payloads = [row[1] for row in unique.values()]
    return points, payloads, {
        "hull_edges": len(normals2),
        "dual_extremes": len(dual),
        "certificate_vectors": len(points),
    }


def centered_inradius(points: np.ndarray):
    hull = ConvexHull(points)
    offsets = hull.equations[:, 3]
    if offsets.max() >= -1e-10:
        return 0.0, hull, None
    facet = int(np.argmax(offsets))
    return float(-offsets[facet]), hull, facet


def best_centered_tetrahedron(points: np.ndarray, hull: ConvexHull | None = None,
                              batch_size: int = 100000):
    """Brute-force the best four-point certificate containing the origin."""
    if hull is None:
        hull = ConvexHull(points)
    candidates = hull.vertices
    best_radius = 0.0
    best_indices = None
    combinations = itertools.combinations(range(len(candidates)), 4)
    while True:
        block = list(itertools.islice(combinations, batch_size))
        if not block:
            break
        local_indices = np.asarray(block, dtype=int)
        p = points[candidates[local_indices]]
        matrix = np.empty((len(p), 4, 4))
        matrix[:, :3, :] = np.transpose(p, (0, 2, 1))
        matrix[:, 3, :] = 1.0
        try:
            rhs = np.broadcast_to([0., 0., 0., 1.], (len(p), 4))[..., None]
            bary = np.linalg.solve(matrix, rhs)[..., 0]
        except np.linalg.LinAlgError:
            # Singular tetrahedra are rare; solve one at a time in this block.
            bary = np.full((len(p), 4), -1.0)
            for i, mat in enumerate(matrix):
                try:
                    bary[i] = np.linalg.solve(mat, [0., 0., 0., 1.])
                except np.linalg.LinAlgError:
                    pass
        keep = bary.min(axis=1) > 1e-10
        if not keep.any():
            continue
        p = p[keep]
        kept_indices = local_indices[keep]
        face_distances = []
        for omitted in range(4):
            face = p[:, [i for i in range(4) if i != omitted], :]
            cross = np.cross(face[:, 1] - face[:, 0],
                             face[:, 2] - face[:, 0])
            distance = np.abs(np.einsum("ij,ij->i", cross, face[:, 0]))
            distance /= np.linalg.norm(cross, axis=1)
            face_distances.append(distance)
        radii = np.min(np.stack(face_distances, axis=1), axis=1)
        j = int(np.argmax(radii))
        if radii[j] > best_radius:
            best_radius = float(radii[j])
            best_indices = candidates[kept_indices[j]]
    return best_radius, best_indices


def evaluate_normal(normal: np.ndarray, include_payload: bool = False):
    points, payloads, meta = certificate_vectors(normal)
    radius, hull, facet = centered_inradius(points)
    result = {
        "normal": (normal / np.linalg.norm(normal)).tolist(),
        "local_theorem": bool(sl.audit_direction(normal)["success"]),
        "axis_free_radius": radius,
        **meta,
        "vector_hull_vertices": int(len(hull.vertices)),
        "vector_hull_facets": int(len(hull.simplices)),
    }
    if facet is not None:
        result["worst_axis"] = hull.equations[facet, :3].tolist()
    if include_payload:
        result["points"] = points.tolist()
        result["payloads"] = payloads
        result["hull_vertex_indices"] = hull.vertices.tolist()
        if facet is not None:
            result["worst_facet_indices"] = hull.simplices[facet].tolist()
    return result


def optimize_normal(row: dict, maxiter: int = 1000):
    x0 = np.asarray(row["normal"], dtype=float)

    def objective(x):
        norm = np.linalg.norm(x)
        if norm < 1e-9:
            return 1.0
        points, _, _ = certificate_vectors(x / norm)
        radius, _, _ = centered_inradius(points)
        return radius

    answer = minimize(objective, x0, method="Nelder-Mead", options={
        "maxiter": maxiter, "xatol": 2e-11, "fatol": 2e-12,
    })
    normal = answer.x / np.linalg.norm(answer.x)
    result = evaluate_normal(normal, include_payload=True)
    result["optimizer_success"] = bool(answer.success)
    result["optimizer_iterations"] = int(answer.nit)
    return result


def random_normals(rng: np.random.Generator, count: int):
    rows = []
    t0 = time.time()
    for i in range(count):
        normal = rng.normal(size=3)
        row = evaluate_normal(normal)
        rows.append(row)
        if (i + 1) % 250 == 0:
            print(f"normals {i+1}/{count} elapsed={time.time()-t0:.1f}s "
                  f"min={min(r['axis_free_radius'] for r in rows):.8g}",
                  flush=True)
    return rows


def summarize(rows: list[dict]):
    radii = np.array([row["axis_free_radius"] for row in rows])
    names = ("min", "p01", "p10", "median", "p90", "p99", "max")
    qs = (0, .01, .1, .5, .9, .99, 1)
    failures = [row for row in rows if not row["local_theorem"]]
    return {
        "count": len(rows),
        "radius_quantiles": dict(zip(names, map(float,
                                                  np.quantile(radii, qs)))),
        "local_failure_count": len(failures),
        "local_failure_min_radius": (min(row["axis_free_radius"]
                                         for row in failures)
                                     if failures else None),
        "max_certificate_vectors": max(row["certificate_vectors"]
                                       for row in rows),
        "max_hull_vertices": max(row["vector_hull_vertices"] for row in rows),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--random", type=int, default=5000)
    ap.add_argument("--optimize-starts", type=int, default=8)
    ap.add_argument("--optimize-iters", type=int, default=1000)
    ap.add_argument("--seed", type=int, default=20260719)
    ap.add_argument("--out", default=os.path.join(
        os.path.dirname(__file__), "snub_axis_free_experiment.json"))
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    rows = random_normals(rng, args.random)
    summary = summarize(rows)
    print(json.dumps(summary, indent=2), flush=True)
    hardest = sorted(rows, key=lambda row: row["axis_free_radius"])[:100]
    hard_payloads = [evaluate_normal(np.asarray(row["normal"]), True)
                     for row in hardest[:10]]
    optimized = [optimize_normal(row, args.optimize_iters)
                 for row in hardest[:args.optimize_starts]]
    print("optimized minima",
          [row["axis_free_radius"] for row in optimized], flush=True)
    result = {"parameters": vars(args), "summary": summary,
              "hardest": hardest, "hard_payloads": hard_payloads,
              "optimized": optimized}
    with open(args.out, "w") as f:
        json.dump(result, f, indent=2)
        f.write("\n")
    print(f"wrote {args.out}", flush=True)


if __name__ == "__main__":
    main()
