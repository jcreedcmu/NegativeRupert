"""Extract proof-shaped balanced-support certificates for the snub cube.

``experiment_snub_rigidity.py`` optimizes over normalized hull normals and
floating dual weights. Those are convenient numerical coordinates, but they
are not what a small formal checker should trust. This script converts every
winning dual extreme point into the proposed payload:

* two named support vertices defining each projected support line;
* an orientation sign for its unnormalized normal ``J L(b-a)``;
* a named support vertex attaining the one-sided derivative;
* determinant weights (for a three-contact certificate);
* the vectors ``A`` and scalar ``B`` in the finite Rodrigues theorem.

It then checks that the resulting ratio is equal, to floating error, to the
LP-dual first variation used in the earlier experiment. This is a structural
validation, not a formal certificate.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import os

import numpy as np
from scipy.spatial import ConvexHull

try:
    import experiment_snub_cube as sc
    import experiment_snub_rigidity as sr
except ModuleNotFoundError:
    from scripts import experiment_snub_cube as sc
    from scripts import experiment_snub_rigidity as sr


def det2(a: np.ndarray, b: np.ndarray) -> float:
    return float(a[0] * b[1] - a[1] * b[0])


def determinant_weights(u: np.ndarray) -> np.ndarray:
    """Return (det(u2,u3), det(u3,u1), det(u1,u2))."""
    return np.array([det2(u[1], u[2]), det2(u[2], u[0]),
                     det2(u[0], u[1])])


def cyclic_positive_order(u: np.ndarray, tol: float = 1e-11):
    """Find an order in which all determinant weights are positive."""
    for perm in itertools.permutations(range(3)):
        weights = determinant_weights(u[list(perm)])
        if weights.min() > tol:
            return np.array(perm, dtype=int), weights
    raise RuntimeError("three directions do not strictly positively span R^2")


def extract_certificate(theta: float, phi: float, axis: np.ndarray,
                        active_tol: float = 2e-9) -> dict:
    axis = np.asarray(axis, dtype=float)
    axis /= np.linalg.norm(axis)
    frame = sc.frame_matrix(theta, phi)
    lmap = frame[:2]
    q = sc.UNIT_VERTS @ lmap.T
    hull = ConvexHull(q)
    normals = hull.equations[:, :2]
    dual = sr.dual_extreme_points(normals)

    dv = np.cross(axis[None, :], sc.UNIT_VERTS)
    dq = dv @ lmap.T
    hp = sr.active_support_derivatives(
        q, dq[None, :, :], normals, active_tol=active_tol)[0]
    scores = dual @ hp
    best_index = int(np.argmax(scores))
    lam = dual[best_index]
    contacts = np.flatnonzero(lam > 1e-10)

    raw_normals = []
    support_pairs = []
    support_vertices = []
    scales = []
    support_errors = []
    for j in contacts:
        a, b = map(int, hull.simplices[j])
        edge = q[b] - q[a]
        raw = np.array([-edge[1], edge[0]])
        if raw @ normals[j] < 0.0:
            raw = -raw
            sigma = -1
        else:
            sigma = 1
        scale = float(raw @ normals[j])
        if scale <= 1e-12:
            raise RuntimeError("degenerate projected support pair")

        base = q @ normals[j]
        active = base >= base.max() - active_tol
        deriv = dq @ normals[j]
        v = int(np.argmax(np.where(active, deriv, -np.inf)))

        raw_support = q @ raw
        h = max(raw_support[a], raw_support[b])
        support_errors.append(float(max(raw_support.max() - h,
                                        abs(raw_support[v] - h))))
        raw_normals.append(raw)
        support_pairs.append((a, b, sigma))
        support_vertices.append(v)
        scales.append(scale)

    raw_normals = np.array(raw_normals)
    support_vertices_array = np.array(support_vertices, dtype=int)
    scales = np.array(scales)
    raw_weights_from_dual = lam[contacts] / scales

    if len(contacts) == 3:
        perm, _ = cyclic_positive_order(raw_normals)
        contacts = contacts[perm]
        raw_normals = raw_normals[perm]
        raw_weights_from_dual = raw_weights_from_dual[perm]
        support_pairs = [support_pairs[i] for i in perm]
        support_vertices_array = support_vertices_array[perm]
        scales = scales[perm]
        weights = determinant_weights(raw_normals)
        factor = float(np.dot(weights, raw_weights_from_dual) /
                       np.dot(raw_weights_from_dual, raw_weights_from_dual))
        proportional_error = float(np.max(np.abs(
            weights - factor * raw_weights_from_dual)))
        weight_kind = "determinant"
    elif len(contacts) == 2:
        # Opposite support directions have a unique positive balancing ratio.
        weights = raw_weights_from_dual
        proportional_error = 0.0
        weight_kind = "opposite_pair"
    else:
        raise RuntimeError(f"unexpected dual support size {len(contacts)}")

    verts = sc.UNIT_VERTS[support_vertices_array]
    lifted = raw_normals @ lmap
    oriented_edges = np.array([
        sigma * (sc.UNIT_VERTS[b] - sc.UNIT_VERTS[a])
        for a, b, sigma in support_pairs
    ])
    coordinate_free_lifted = np.cross(frame[2][None, :], oriented_edges)
    avec_terms = np.cross(verts, lifted)
    avec = np.einsum("i,ij->j", weights, avec_terms)
    bbound = float(np.sum(weights * np.linalg.norm(lifted, axis=1)
                          * np.linalg.norm(verts, axis=1)))
    universal_bbound = float(np.sum(
        weights * np.linalg.norm(oriented_edges, axis=1)
        * np.linalg.norm(verts, axis=1)))
    ratio = float(axis @ avec / bbound)
    polynomial_ratio = float(axis @ avec / universal_bbound)
    balance = np.einsum("i,ij->j", weights, raw_normals)

    if len(contacts) == 3:
        coordinate_free_weights = np.array([
            frame[2] @ np.cross(oriented_edges[1], oriented_edges[2]),
            frame[2] @ np.cross(oriented_edges[2], oriented_edges[0]),
            frame[2] @ np.cross(oriented_edges[0], oriented_edges[1]),
        ])
        coordinate_free_weight_error = float(np.max(
            np.abs(coordinate_free_weights - weights)))
    else:
        coordinate_free_weight_error = 0.0

    return {
        "theta": float(theta),
        "phi": float(phi),
        "view_normal": frame[2].tolist(),
        "axis": axis.tolist(),
        "hull_edges": int(len(normals)),
        "dual_extremes": int(len(dual)),
        "dual_support_size": int(len(contacts)),
        "dual_score": float(scores[best_index]),
        "certificate_ratio": ratio,
        "polynomial_ratio": polynomial_ratio,
        "ratio_error": abs(ratio - float(scores[best_index])),
        "balance_error": float(np.linalg.norm(balance)),
        "support_error": float(max(support_errors, default=0.0)),
        "weight_proportional_error": proportional_error,
        "coordinate_free_lift_error": float(np.max(np.abs(
            coordinate_free_lifted - lifted))),
        "coordinate_free_weight_error": coordinate_free_weight_error,
        "weight_kind": weight_kind,
        "contacts": contacts.tolist(),
        "support_pairs": [list(map(int, row)) for row in support_pairs],
        "support_vertices": support_vertices_array.tolist(),
        "raw_normals": raw_normals.tolist(),
        "weights": weights.tolist(),
        "A": avec.tolist(),
        "B": bbound,
        "universal_B": universal_bbound,
    }


def random_validation(rng: np.random.Generator, count: int) -> dict:
    worst_ratio = None
    maxima = {"ratio_error": 0.0, "balance_error": 0.0,
              "support_error": 0.0, "weight_proportional_error": 0.0,
              "coordinate_free_lift_error": 0.0,
              "coordinate_free_weight_error": 0.0}
    support_sizes = {"2": 0, "3": 0}
    for _ in range(count):
        theta = rng.uniform(-math.pi, math.pi)
        phi = math.acos(rng.uniform(-1.0, 1.0))
        axis = rng.normal(size=3)
        cert = extract_certificate(theta, phi, axis)
        support_sizes[str(cert["dual_support_size"])] += 1
        for key in maxima:
            maxima[key] = max(maxima[key], cert[key])
        if (worst_ratio is None or cert["certificate_ratio"]
                < worst_ratio["certificate_ratio"]):
            worst_ratio = cert
    return {"count": count, "support_sizes": support_sizes,
            "max_errors": maxima, "smallest_ratio_certificate": worst_ratio}


def certificates_from_optimized(path: str) -> list[dict]:
    with open(path) as f:
        payload = json.load(f)
    out = []
    for row in payload.get("optimized", []):
        if row.get("kind") != "triple":
            continue
        theta, phi = sr.normal_to_angles(np.asarray(row["normal"]))
        cert = extract_certificate(theta, phi, np.asarray(row["axis"]))
        cert["source_triple"] = row["triple"]
        cert["source_error"] = abs(cert["certificate_ratio"] - row["triple"])
        out.append(cert)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--random", type=int, default=10000)
    ap.add_argument("--seed", type=int, default=20260719)
    ap.add_argument("--optimized", action="append", default=[])
    ap.add_argument("--out", default=os.path.join(
        os.path.dirname(__file__), "snub_edge_certificate_validation.json"))
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    result = {"random": random_validation(rng, args.random), "optimized": {}}
    for path in args.optimized:
        result["optimized"][path] = certificates_from_optimized(path)
    with open(args.out, "w") as f:
        json.dump(result, f, indent=2)
        f.write("\n")
    summary = {
        "random_count": result["random"]["count"],
        "support_sizes": result["random"]["support_sizes"],
        "max_errors": result["random"]["max_errors"],
        "smallest_ratio": result["random"]["smallest_ratio_certificate"][
            "certificate_ratio"],
        "optimized_counts": {key: len(value)
                             for key, value in result["optimized"].items()},
    }
    print(json.dumps(summary, indent=2))
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
