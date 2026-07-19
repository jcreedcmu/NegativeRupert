"""Compare SY25-local and balanced-support rigidity on the rhombicosidodecahedron."""

from __future__ import annotations

import argparse
import itertools
import json
import math
import os

import numpy as np
from scipy.spatial import ConvexHull

try:
    import experiment_snub_local as sl
    import experiment_snub_rigidity as sr
except ModuleNotFoundError:
    from scripts import experiment_snub_local as sl
    from scripts import experiment_snub_rigidity as sr


def permutation_parity(p):
    return sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3)) & 1


def rhombicosidodecahedron_vertices():
    """The standard 60 vertices, normalized to circumradius one."""
    g = (1.0 + math.sqrt(5.0)) / 2.0
    bases = [np.array([1.0, 1.0, g**3]),
             np.array([g**2, g, 2.0*g]),
             np.array([2.0+g, 0.0, g**2])]
    out = []
    even_perms = [p for p in itertools.permutations(range(3))
                  if permutation_parity(p) == 0]
    for base in bases:
        for p in even_perms:
            for signs in itertools.product((-1.0, 1.0), repeat=3):
                out.append(base[list(p)] * signs)
    vertices = np.unique(np.round(np.array(out), 14), axis=0)
    if vertices.shape != (60, 3):
        raise AssertionError(vertices.shape)
    radii = np.linalg.norm(vertices, axis=1)
    if radii.max() - radii.min() > 1e-12:
        raise AssertionError((radii.min(), radii.max()))
    return vertices / radii[0]


VERTICES = rhombicosidodecahedron_vertices()
COMBOS = np.array(list(itertools.combinations(range(len(VERTICES)), 3)),
                  dtype=np.int16)


def old_local_audit(normal: np.ndarray, tol: float = 2e-12):
    normal = np.asarray(normal, dtype=float)
    normal /= np.linalg.norm(normal)
    m = sl.basis_from_normal(normal)
    q = VERTICES @ m.T
    dv = q[:, None, :] - q[None, :, :]
    numer = np.einsum("id,ikd->ik", q, dv)
    denom = np.linalg.norm(q, axis=1)[:, None] * np.linalg.norm(dv, axis=2)
    np.fill_diagonal(numer, np.inf)
    np.fill_diagonal(denom, 1.0)
    cosine = np.divide(numer, denom, out=np.full_like(numer, -np.inf),
                       where=denom > 1e-14)
    np.fill_diagonal(cosine, np.inf)
    bmargin = cosine.min(axis=1)
    side = VERTICES @ normal
    best = None
    best_score = -math.inf
    for sigma in (1.0, -1.0):
        candidate = (sigma * side > tol) & (bmargin > tol)
        mask = candidate[COMBOS].all(axis=1)
        triples = COMBOS[mask]
        if not len(triples):
            continue
        a, b, c = q[triples[:, 0]], q[triples[:, 1]], q[triples[:, 2]]
        crosses = np.stack((sl.cross2(a, b), sl.cross2(b, c),
                            sl.cross2(c, a)), axis=1)
        contains = ((crosses.min(axis=1) > tol)
                    | (crosses.max(axis=1) < -tol))
        triples = triples[contains]
        crosses = np.abs(crosses[contains])
        if not len(triples):
            continue
        am = np.min(sigma * side[triples], axis=1)
        sm = crosses.min(axis=1)
        bm = np.min(bmargin[triples], axis=1)
        score = np.minimum(np.minimum(am, sm), bm)
        j = int(np.argmax(score))
        if score[j] > best_score:
            best_score = float(score[j])
            best = {"vertices": triples[j].astype(int).tolist(),
                    "sigma": int(sigma < 0), "A_margin": float(am[j]),
                    "spanning_margin": float(sm[j]),
                    "B_cosine_margin": float(bm[j]),
                    "score": float(score[j])}
    return {"success": best is not None, "best": best,
            "n_B_good": int(np.sum(bmargin > tol))}


def balanced_vectors(normal: np.ndarray, active_tol: float = 2e-9,
                     reflect_inner: bool = False):
    """All conservative A/Bbar certificate vectors for a fixed view."""
    normal = np.asarray(normal, dtype=float)
    normal /= np.linalg.norm(normal)
    inner3 = VERTICES
    if reflect_inner:
        reflection = np.eye(3) - 2.0 * np.outer(normal, normal)
        inner3 = VERTICES @ reflection.T
    lmap = sl.basis_from_normal(normal)
    # basis_from_normal has rows a,b with a x b = normal.
    q = VERTICES @ lmap.T
    hull2 = ConvexHull(q)
    normals2 = hull2.equations[:, :2]
    dual = sr.dual_extreme_points(normals2)
    base = q @ normals2.T
    active = base >= base.max(axis=0)[None, :] - active_tol
    chord_ratios = []
    for j in range(len(normals2)):
        ids = np.flatnonzero(active[:, j])
        best_ratio = math.inf
        for a, b in itertools.combinations(ids, 2):
            projected_length = np.linalg.norm(q[b] - q[a])
            if projected_length <= 1e-12:
                continue
            ratio = np.linalg.norm(VERTICES[b] - VERTICES[a]) / projected_length
            best_ratio = min(best_ratio, ratio)
        if not math.isfinite(best_ratio):
            raise RuntimeError("support line has no distinct projected vertices")
        chord_ratios.append(best_ratio)
    chord_ratios = np.array(chord_ratios)
    points = []
    for lam in dual:
        contacts = np.flatnonzero(lam > 1e-10)
        active_vertices = []
        for j in contacts:
            active_vertices.append(np.flatnonzero(active[:, j]))
        weights = lam[contacts]
        lifted = normals2[contacts] @ lmap
        bbar = float(np.sum(weights * chord_ratios[contacts]))
        for chosen in itertools.product(*active_vertices):
            avec = np.einsum("i,ij->j", weights,
                              np.cross(inner3[list(chosen)], lifted))
            points.append(avec / bbar)
    unique = {tuple(np.round(point, 12)): point for point in points}
    return np.array(list(unique.values())), {
        "shadow_edges": len(normals2), "dual_extremes": len(dual),
        "certificate_vectors": len(unique)}


def balanced_audit(normal: np.ndarray, reflect_inner: bool = False):
    points, meta = balanced_vectors(normal, reflect_inner=reflect_inner)
    hull = ConvexHull(points)
    offsets = hull.equations[:, 3]
    radius = max(0.0, float(-offsets.max()))
    facet = int(np.argmax(offsets))
    return {"axis_free_radius": radius,
            "worst_axis": hull.equations[facet, :3].tolist(),
            "vector_hull_vertices": len(hull.vertices), **meta}


def reflection_radius(normal: np.ndarray):
    return balanced_audit(normal, reflect_inner=True)["axis_free_radius"]


def canonical_direction(x):
    x = np.asarray(x, dtype=float)
    x /= np.linalg.norm(x)
    k = int(np.argmax(np.abs(x)))
    if x[k] < 0:
        x = -x
    return tuple(np.round(x, 10))


def special_directions():
    directions = {canonical_direction(np.eye(3)[i]): f"axis_{i}"
                  for i in range(3)}
    hull3 = ConvexHull(VERTICES)
    for i, eq in enumerate(hull3.equations):
        directions.setdefault(canonical_direction(eq[:3]), f"face_{i}")
    for i, v in enumerate(VERTICES):
        directions.setdefault(canonical_direction(v), f"vertex_{i}")
    # Great circles where projected vertices coincide or support regimes can
    # change are the other important exact directions.
    for i in range(len(VERTICES)):
        for j in range(i + 1, len(VERTICES)):
            d = VERTICES[i] - VERTICES[j]
            if np.linalg.norm(d) > 1e-12:
                directions.setdefault(canonical_direction(d),
                                      f"difference_{i}_{j}")
    return [(name, np.array(direction)) for direction, name in directions.items()]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--random", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=20260719)
    ap.add_argument("--out", default=os.path.join(
        os.path.dirname(__file__), "rhombi_balanced_experiment.json"))
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    records = []
    for name, normal in special_directions():
        old = old_local_audit(normal)
        record = {"name": name, "normal": normal.tolist(), "old": old}
        if not old["success"]:
            record["balanced"] = balanced_audit(normal)
            print("special failure", json.dumps(record), flush=True)
        records.append(record)
    random_failures = []
    min_old_score = math.inf
    for i in range(args.random):
        normal = rng.normal(size=3)
        normal /= np.linalg.norm(normal)
        old = old_local_audit(normal)
        if old["success"]:
            min_old_score = min(min_old_score, old["best"]["score"])
        else:
            row = {"normal": normal.tolist(), "old": old,
                   "balanced": balanced_audit(normal)}
            random_failures.append(row)
        if (i + 1) % 250 == 0:
            print(f"random {i+1}/{args.random} failures={len(random_failures)}",
                  flush=True)
    result = {
        "parameters": vars(args), "vertices": len(VERTICES),
        "special_count": len(records),
        "special_failures": [row for row in records
                             if not row["old"]["success"]],
        "random_failure_count": len(random_failures),
        "random_min_old_score": min_old_score,
        "random_failures": random_failures,
    }
    with open(args.out, "w") as f:
        json.dump(result, f, indent=2)
        f.write("\n")
    print(json.dumps({key: value for key, value in result.items()
                      if key not in ("special_failures", "random_failures")},
                     indent=2))
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
