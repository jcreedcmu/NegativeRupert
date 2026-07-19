"""Global and transition-focused reachability tests for the rhombicosidodecahedron."""

from __future__ import annotations

import argparse
import json
import math
import os
import time
from multiprocessing import Pool

import numpy as np
from scipy.optimize import minimize
from scipy.spatial import ConvexHull

try:
    import experiment_rhombi_balanced as rb
    import experiment_snub_cube as sc
    import experiment_snub_rigidity as sr
except ModuleNotFoundError:
    from scripts import experiment_rhombi_balanced as rb
    from scripts import experiment_snub_cube as sc
    from scripts import experiment_snub_rigidity as sr


def evaluate_maps(outer_map: np.ndarray, inner_map: np.ndarray):
    outer = rb.VERTICES @ outer_map.T
    inner = rb.VERTICES @ inner_map.T
    normals, h_outer = sc.hull_equations(outer)
    h_inner = sc.supports(inner, normals)
    clearance, idx, lam = sc.balanced_dual(normals, h_outer - h_inner)
    return float(clearance), tuple(map(int, idx)), lam


def evaluate_pose(pose: np.ndarray):
    ti, fi, to, fo, alpha = pose
    outer_map = sc.projection_matrix(to, fo)
    inner_map = sc.rot2(alpha) @ sc.projection_matrix(ti, fi)
    return evaluate_maps(outer_map, inner_map)


def evaluate_relative(normal: np.ndarray, relative: np.ndarray):
    theta, phi = sr.normal_to_angles(normal)
    frame = sc.frame_matrix(theta, phi)
    return evaluate_maps(frame[:2], (frame @ relative)[:2])


def evaluate_relative_batch(normal: np.ndarray, relatives: np.ndarray):
    """Vectorized exact-dual clearance for many rotations at one outer view."""
    theta, phi = sr.normal_to_angles(normal)
    frame = sc.frame_matrix(theta, phi)
    outer = rb.VERTICES @ frame[:2].T
    normals, h_outer = sc.hull_equations(outer)
    dual = sr.dual_extreme_points(normals)
    inner_maps = np.einsum("ij,bjk->bik", frame, relatives)[:, :2, :]
    inner = np.einsum("vj,bdj->bvd", rb.VERTICES, inner_maps)
    directional = np.einsum("bvd,md->bmv", inner, normals)
    h_inner = directional.max(axis=2)
    gaps = h_inner - h_outer[None, :]
    scores = gaps @ dual.T
    best = np.argmax(scores, axis=1)
    obstruction = scores[np.arange(len(scores)), best]
    contacts = [np.flatnonzero(dual[j] > 1e-10).astype(int).tolist()
                for j in best]
    return -obstruction, contacts


def random_poses(rng: np.random.Generator, count: int):
    return np.stack((rng.uniform(-math.pi, math.pi, count),
                     np.arccos(rng.uniform(-1.0, 1.0, count)),
                     rng.uniform(-math.pi, math.pi, count),
                     np.arccos(rng.uniform(-1.0, 1.0, count)),
                     rng.uniform(-math.pi, math.pi, count)), axis=1)


def optimize_pose(pose: np.ndarray, maxiter: int):
    def objective(x):
        return -evaluate_pose(x)[0]

    answer = minimize(objective, pose, method="Nelder-Mead", options={
        "maxiter": maxiter, "xatol": 2e-10, "fatol": 2e-12,
    })
    clearance, idx, lam = evaluate_pose(answer.x)
    return {"clearance": clearance, "pose": answer.x.tolist(),
            "dual_indices": list(idx), "dual_weights": lam.tolist(),
            "success": bool(answer.success), "iterations": int(answer.nit)}


def evaluate_pose_row(pose: np.ndarray):
    clearance, idx, _ = evaluate_pose(pose)
    return clearance, pose, idx


def optimize_pose_args(args):
    return optimize_pose(*args)


def boundary_axis_free_audit(pose: np.ndarray, score_tol: float = 2e-8,
                             active_tol: float = 2e-8):
    """First-variation inradius at a numerically zero-clearance general pose."""
    ti, fi, to, fo, alpha = pose
    outer_frame = sc.frame_matrix(to, fo)
    outer_map = outer_frame[:2]
    inner_map = sc.rot2(alpha) @ sc.projection_matrix(ti, fi)
    outer = rb.VERTICES @ outer_map.T
    inner = rb.VERTICES @ inner_map.T
    normals, h_outer = sc.hull_equations(outer)
    h_inner = sc.supports(inner, normals)
    dual = sr.dual_extreme_points(normals)
    scores = dual @ (h_inner - h_outer)
    best_score = float(scores.max())
    selected = dual[scores >= best_score - score_tol]
    lifted = normals @ outer_map
    # Recover actual inner vertices in the outer three-dimensional frame.
    relative = sc.relative_rotation(pose)
    inner3 = rb.VERTICES @ relative.T
    base = inner @ normals.T
    active = base >= base.max(axis=0)[None, :] - active_tol
    points = []
    for lam in selected:
        contacts = np.flatnonzero(lam > 1e-10)
        choices = [np.flatnonzero(active[:, j]) for j in contacts]
        for chosen in __import__("itertools").product(*choices):
            avec = np.einsum("i,ij->j", lam[contacts],
                              np.cross(inner3[list(chosen)], lifted[contacts]))
            points.append(avec)
    unique = np.array(list({tuple(np.round(p, 12)): p for p in points}.values()))
    if len(unique) < 4 or np.linalg.matrix_rank(unique - unique[0]) < 3:
        return {"radius": 0.0, "points": len(unique),
                "selected_duals": len(selected), "best_score": best_score}
    hull = ConvexHull(unique)
    radius = max(0.0, float(-hull.equations[:, 3].max()))
    return {"radius": radius, "points": len(unique),
            "hull_vertices": len(hull.vertices),
            "selected_duals": len(selected), "best_score": best_score}


def global_search(rng: np.random.Generator, count: int, optimize_starts: int,
                  optimize_iters: int, workers: int):
    poses = random_poses(rng, count)
    rows = []
    t0 = time.time()
    if workers > 1:
        with Pool(workers) as pool:
            iterator = pool.imap(evaluate_pose_row, poses, chunksize=100)
            for i, row in enumerate(iterator):
                rows.append(row)
                if (i + 1) % 5000 == 0:
                    print(f"global {i+1}/{count} max_clearance="
                          f"{max(item[0] for item in rows):.9g} "
                          f"elapsed={time.time()-t0:.1f}s", flush=True)
    else:
        for i, pose in enumerate(poses):
            rows.append(evaluate_pose_row(pose))
            if (i + 1) % 5000 == 0:
                print(f"global {i+1}/{count} max_clearance="
                      f"{max(item[0] for item in rows):.9g} "
                      f"elapsed={time.time()-t0:.1f}s", flush=True)
    rows.sort(key=lambda row: row[0], reverse=True)
    optimization_args = [(row[1], optimize_iters)
                         for row in rows[:optimize_starts]]
    if workers > 1 and optimization_args:
        with Pool(min(workers, len(optimization_args))) as pool:
            optimized = pool.map(optimize_pose_args, optimization_args)
    else:
        optimized = [optimize_pose_args(item) for item in optimization_args]
    clearances = np.array([row[0] for row in rows])
    return {
        "count": count,
        "clearance_quantiles": dict(zip(
            ("min", "p01", "p10", "median", "p90", "p99", "max"),
            map(float, np.quantile(clearances, [0, .01, .1, .5, .9, .99, 1])))),
        "positive_count": int(np.sum(clearances > 2e-10)),
        "hardest": [{"clearance": float(c), "pose": p.tolist(),
                     "dual_indices": list(idx)} for c, p, idx in rows[:100]],
        "optimized": optimized,
    }


def tangent_basis(normal: np.ndarray):
    normal = np.asarray(normal, dtype=float)
    normal /= np.linalg.norm(normal)
    seed = np.array([0., 0., 1.]) if abs(normal[2]) < .9 else np.array([1., 0., 0.])
    a = np.cross(seed, normal)
    a /= np.linalg.norm(a)
    return a, np.cross(normal, a)


def transition_search(boundaries: list[np.ndarray], tangent_angles: int,
                      axes_count: int):
    axes = sr.fibonacci_sphere(axes_count)
    ratios = np.geomspace(1e-2, 1e2, 17)
    distances = (1e-2, 1e-3, 1e-4, 1e-5)
    worst = []
    positive = []
    branch_counts = {"old_success": 0, "old_failure": 0}
    t0 = time.time()
    count = 0
    rotation_meta = []
    for ratio in ratios:
        for axis in axes:
            rotation_meta.append((float(ratio), axis))
    # These matrices are rebuilt with the distance-scaled angle below; the
    # list merely fixes a stable batch ordering.
    strata = ("identity", "reflection")
    for stratum in strata:
        for bi, center in enumerate(boundaries):
            center = center / np.linalg.norm(center)
            ta, tb = tangent_basis(center)
            for phase in np.linspace(0., 2.*math.pi, tangent_angles, endpoint=False):
                tangent = math.cos(phase) * ta + math.sin(phase) * tb
                for distance in distances:
                    normal = center + distance * tangent
                    normal /= np.linalg.norm(normal)
                    old_success = rb.old_local_audit(normal)["success"]
                    branch_counts["old_success" if old_success else "old_failure"] += 1
                    if stratum == "identity":
                        base_relative = np.eye(3)
                    else:
                        reflection = np.eye(3) - 2.0 * np.outer(normal, normal)
                        base_relative = -reflection
                    relatives = np.array([
                        sc.axis_angle(axis, distance * ratio) @ base_relative
                        for ratio, axis in rotation_meta
                    ])
                    clearances, contacts = evaluate_relative_batch(normal, relatives)
                    for clearance, idx, (ratio, axis) in zip(
                            clearances, contacts, rotation_meta):
                        obstruction = -float(clearance)
                        row = {"clearance": float(clearance),
                               "obstruction": obstruction,
                               "stratum": stratum,
                               "boundary": bi, "phase": float(phase),
                               "distance": distance, "ratio": ratio,
                               "angle": float(distance * ratio),
                               "normal": normal.tolist(), "axis": axis.tolist(),
                               "old_success": old_success,
                               "dual_indices": idx}
                        if clearance > 2e-10:
                            positive.append(row)
                        worst.append(row)
                        count += 1
                    worst.sort(key=lambda row: row["obstruction"])
                    del worst[100:]
            minimum_text = (f"{worst[0]['obstruction']:.9g}"
                            if worst else "n/a")
            print(f"transition {stratum} boundary {bi+1}/{len(boundaries)} "
                  f"count={count} min_obstruction={minimum_text} "
                  f"positives={len(positive)} elapsed={time.time()-t0:.1f}s",
                  flush=True)
    return {"count": count, "positive_count": len(positive),
            "positive_examples": positive[:100], "worst": worst,
            "view_branch_counts": branch_counts,
            "distances": list(distances), "ratios": ratios.tolist(),
            "tangent_angles": tangent_angles, "axes": axes_count,
            "strata": list(strata)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--global", dest="global_count", type=int, default=50000)
    ap.add_argument("--optimize-starts", type=int, default=12)
    ap.add_argument("--optimize-iters", type=int, default=1500)
    ap.add_argument("--workers", type=int, default=12)
    ap.add_argument("--tangent-angles", type=int, default=12)
    ap.add_argument("--axes", type=int, default=128)
    ap.add_argument("--seed", type=int, default=20260719)
    ap.add_argument("--out", default=os.path.join(
        os.path.dirname(__file__), "rhombi_reach_experiment.json"))
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    global_result = global_search(rng, args.global_count,
                                  args.optimize_starts, args.optimize_iters,
                                  args.workers)
    # Representatives of the two observed boundary orbits: a coordinate-axis
    # failure and a golden-ratio/difference-direction failure.
    boundaries = [np.array([1., 0., 0.]),
                  np.array([0.16245984809795874,
                            0.2628655560966972,
                            0.9510565162880503])]
    transition_result = transition_search(boundaries, args.tangent_angles,
                                          args.axes)
    result = {"parameters": vars(args), "global": global_result,
              "transition": transition_result}
    with open(args.out, "w") as f:
        json.dump(result, f, indent=2)
        f.write("\n")
    print("summary", json.dumps({
        "global_positive": global_result["positive_count"],
        "global_max": global_result["clearance_quantiles"]["max"],
        "optimized_max": (max(row["clearance"]
                              for row in global_result["optimized"])
                          if global_result["optimized"] else None),
        "transition_positive": transition_result["positive_count"],
        "transition_min_obstruction": (min(row["obstruction"]
                                            for row in transition_result["worst"])
                                       if transition_result["worst"] else None),
    }, indent=2), flush=True)
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
