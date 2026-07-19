"""Exact-rational search utilities for snub-cube proof certificates.

The functions in this file mirror the definitions in
``Noperthedron/SnubCube/{Certificate,LocalCertificate}.lean``.  Floating
geometry is used only to select promising witnesses; every accepted witness
is subsequently evaluated with ``fractions.Fraction`` using the same rounded
Taylor data as Lean.

The initial command, ``local-smoke``, searches for four balanced local
certificates around a generic identity-symmetry equality pose and prints a
complete JSON payload.  It is intentionally small enough to inspect and to
turn into a Lean smoke theorem before building the adaptive five-dimensional
tree.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from fractions import Fraction as Q

import numpy as np
from scipy.spatial import ConvexHull


KAPPA = Q(1, 10**10)
TRIBONACCI_Q = Q(1839286755214161, 10**15)
ROTATION_ERROR = 3 * KAPPA + KAPPA * KAPPA
CENTER_VECTOR_ERROR = 2 * KAPPA + KAPPA * KAPPA

PERMUTATIONS = (
    (0, 1, 2), (0, 2, 1), (1, 0, 2),
    (1, 2, 0), (2, 0, 1), (2, 1, 0),
)
PERMUTATION_ODD = (False, True, True, False, False, True)
EVEN_SIGNS = ((-1, -1, -1), (1, 1, -1), (1, -1, 1), (-1, 1, 1))
ODD_SIGNS = ((1, -1, -1), (-1, 1, -1), (-1, -1, 1), (1, 1, 1))


def qfloor(x: Q) -> int:
    return x.numerator // x.denominator


def round13(x: Q) -> Q:
    return Q(qfloor(x * 10**13), 10**13)


def sin_q(x: Q) -> Q:
    return round13(sum(
        Q((-1) ** i) * x ** (2 * i + 1) / math.factorial(2 * i + 1)
        for i in range(13)
    ))


def cos_q(x: Q) -> Q:
    return round13(sum(
        Q((-1) ** i) * x ** (2 * i) / math.factorial(2 * i)
        for i in range(13)
    ))


def qdot(a, b):
    return sum((x * y for x, y in zip(a, b)), Q(0))


def matmul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), Q(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def matvec(a, x):
    return [qdot(row, x) for row in a]


def transpose(a):
    return [list(row) for row in zip(*a)]


def matsub(a, b):
    return [[x - y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def cross3(a, b):
    return [a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0]]


def det2(a, b):
    return a[0] * b[1] - a[1] * b[0]


def normalized_vertices_q():
    base = (TRIBONACCI_Q, Q(1), TRIBONACCI_Q**2)
    out = []
    for p, perm in enumerate(PERMUTATIONS):
        signs_table = ODD_SIGNS if PERMUTATION_ODD[p] else EVEN_SIGNS
        for signs in signs_table:
            out.append([Q(signs[c]) * base[perm[c]] / 5 for c in range(3)])
    return out


VERTICES_Q = normalized_vertices_q()
VERTICES = np.asarray([[float(x) for x in v] for v in VERTICES_Q])


def vertex_matrix_int(index: int):
    p, s = divmod(index, 4)
    signs = (ODD_SIGNS if PERMUTATION_ODD[p] else EVEN_SIGNS)[s]
    ans = [[0] * 3 for _ in range(3)]
    for c in range(3):
        ans[c][PERMUTATIONS[p][c]] = signs[c]
    return ans


def symmetry_matrix_q(g: int):
    return [[Q(-x) for x in row] for row in vertex_matrix_int(g)]


def symmetry_action_table():
    matrices = [vertex_matrix_int(i) for i in range(24)]
    lookup = {tuple(sum(m, [])): i for i, m in enumerate(matrices)}
    table = []
    for g in range(24):
        sg = [[-x for x in row] for row in matrices[g]]
        table.append([lookup[tuple(sum(matmul(sg, matrices[i]), []))]
                      for i in range(24)])
    return table


SYMMETRY_ACTION = symmetry_action_table()


def frame_q(theta: Q, phi: Q):
    st, ct, sp, cp = sin_q(theta), cos_q(theta), sin_q(phi), cos_q(phi)
    return [[-st, ct, Q(0)],
            [-ct * cp, -st * cp, sp],
            [ct * sp, st * sp, cp]]


def rz_q(alpha: Q):
    sa, ca = sin_q(alpha), cos_q(alpha)
    return [[ca, -sa, Q(0)], [sa, ca, Q(0)], [Q(0), Q(0), Q(1)]]


def rot_rm_q(theta: Q, phi: Q, alpha: Q):
    return matmul(rz_q(alpha), frame_q(theta, phi))


def direction_q(angle: float, half_tangent_denominator: int = 10**6):
    """A nearby exact rational point on the unit circle."""
    wrapped = (angle + math.pi) % (2 * math.pi) - math.pi
    t = math.tan(wrapped / 2)
    q = half_tangent_denominator
    if abs(t) <= 1:
        p = int(round(t * q))
        d = q*q + p*p
        return (Q(q*q - p*p, d), Q(2*p*q, d))
    # The cotangent chart represents the same circle point without the large
    # numerator that the tangent chart develops near angle ±pi.
    p = int(round((1/t) * q))
    d = q*q + p*p
    return (Q(p*p - q*q, d), Q(2*p*q, d))


def pose_center(interval):
    return [(lo + hi) / 2 for lo, hi in interval]


def pose_eps(interval):
    return [(hi - lo) / 2 for lo, hi in interval]


def h_entries(pose, w):
    _ti, _fi, to, fo, _alpha = pose
    st, ct, sp, cp = sin_q(to), cos_q(to), sin_q(fo), cos_q(fo)
    w0, w1 = w
    rows = [
        [-st*w0 + (-ct*cp)*w1, ct*w0 + (-st*cp)*w1, sp*w1],
        [-ct*w0 + (st*cp)*w1, -st*w0 + (-ct*cp)*w1, Q(0)],
        [(ct*sp)*w1, (st*sp)*w1, cp*w1],
        [st*w0 + (ct*cp)*w1, -ct*w0 + (st*cp)*w1, Q(0)],
        [(-st*sp)*w1, (ct*sp)*w1, Q(0)],
        [(ct*cp)*w1, (st*cp)*w1, -sp*w1],
    ]
    return [[round13(x) for x in row] for row in rows]


def g_entries(pose, w):
    ti, fi, _to, _fo, alpha = pose
    st, ct, sp, cp = sin_q(ti), cos_q(ti), sin_q(fi), cos_q(fi)
    sa, ca = sin_q(alpha), cos_q(alpha)
    w0, w1 = w
    u0, u1 = ca*w0 + sa*w1, -sa*w0 + ca*w1
    up0, up1 = -sa*w0 + ca*w1, -ca*w0 - sa*w1
    rows = [
        [-st*u0 + (-ct*cp)*u1, ct*u0 + (-st*cp)*u1, sp*u1],
        [-st*up0 + (-ct*cp)*up1, ct*up0 + (-st*cp)*up1, sp*up1],
        [-ct*u0 + (st*cp)*u1, -st*u0 + (-ct*cp)*u1, Q(0)],
        [(ct*sp)*u1, (st*sp)*u1, cp*u1],
        [-ct*up0 + (st*cp)*up1, -st*up0 + (-ct*cp)*up1, Q(0)],
        [(ct*sp)*up1, (st*sp)*up1, cp*up1],
        [st*u0 + (ct*cp)*u1, -ct*u0 + (st*cp)*u1, Q(0)],
        [(-st*sp)*u1, (ct*sp)*u1, Q(0)],
        [(ct*cp)*u1, (st*cp)*u1, -sp*u1],
    ]
    return [[round13(x) for x in row] for row in rows]


def fast_h(pose, eth: Q, eph: Q, w, vertex):
    e = h_entries(pose, w)
    kt = 3*KAPPA*(1 + eth + eph + (eth + eph)**2/2)
    return (qdot(e[0], vertex) + eth*abs(qdot(e[1], vertex))
            + eph*abs(qdot(e[2], vertex))
            + Q(1, 2)*(eth**2*abs(qdot(e[3], vertex))
                       + 2*eth*eph*abs(qdot(e[4], vertex))
                       + eph**2*abs(qdot(e[5], vertex)))
            + (eth + eph)**3/6 + kt)


def fast_g(pose, ea: Q, eth: Q, eph: Q, w, vertex):
    e = g_entries(pose, w)
    E = ea + eth + eph
    return (qdot(e[0], vertex)
            - (ea*abs(qdot(e[1], vertex))
               + eth*abs(qdot(e[2], vertex))
               + eph*abs(qdot(e[3], vertex))
               + Q(1, 2)*(ea**2*abs(qdot(e[0], vertex))
                           + 2*ea*eth*abs(qdot(e[4], vertex))
                           + 2*ea*eph*abs(qdot(e[5], vertex))
                           + eth**2*abs(qdot(e[6], vertex))
                           + 2*eth*eph*abs(qdot(e[7], vertex))
                           + eph**2*abs(qdot(e[8], vertex)))
               + E**3/6 + 4*KAPPA*(1 + E + E**2/2)))


def max_h(pose, eth: Q, eph: Q, w):
    return max(fast_h(pose, eth, eph, w, vertex) for vertex in VERTICES_Q)


def outer_as_inner(pose):
    _ti, _fi, to, fo, _alpha = pose
    return [to, fo, to, fo, Q(0)]


def local_supports(pose, eps, direction, vertex_index):
    _eti, _efi, eto, efo, _ea = eps
    lower = fast_g(outer_as_inner(pose), Q(0), eto, efo, direction,
                   VERTICES_Q[vertex_index])
    return all(k == vertex_index
               or fast_h(pose, eto, efo, direction, vertex) <= lower
               for k, vertex in enumerate(VERTICES_Q))


def determinant_weights(directions):
    u0, u1, u2 = directions
    return (det2(u1, u2), det2(u2, u0), det2(u0, u1))


def normalized_a(pose, directions, vertices):
    weights = determinant_weights(directions)
    B = sum(weights, Q(0))
    lift_matrix = transpose(frame_q(pose[2], pose[3])[:2])
    avec = [Q(0), Q(0), Q(0)]
    for weight, direction, vertex in zip(weights, directions, vertices):
        lift = matvec(lift_matrix, direction)
        term = cross3(VERTICES_Q[vertex], lift)
        avec = [a + weight*t for a, t in zip(avec, term)]
    return [x/B for x in avec], weights


def solve_linear(a, b):
    """Exact Gaussian elimination for a square Fraction matrix."""
    n = len(a)
    m = [list(row) + [rhs] for row, rhs in zip(a, b)]
    for col in range(n):
        pivot = next((r for r in range(col, n) if m[r][col]), None)
        if pivot is None:
            raise ValueError("singular matrix")
        m[col], m[pivot] = m[pivot], m[col]
        scale = m[col][col]
        m[col] = [x/scale for x in m[col]]
        for row in range(n):
            if row == col:
                continue
            scale = m[row][col]
            if scale:
                m[row] = [x - scale*y for x, y in zip(m[row], m[col])]
    return [m[i][-1] for i in range(n)]


def barycentric(points, target):
    matrix = [[points[j][i] for j in range(4)] for i in range(3)]
    matrix.append([Q(1)] * 4)
    return solve_linear(matrix, list(target) + [Q(1)])


def exact_tetrahedron_axis_radius(points):
    zero = barycentric(points, [Q(0)]*3)
    if min(zero) <= 0:
        return Q(0)
    bounds = []
    for axis in range(3):
        for sign in (-1, 1):
            target = [Q(0)]*3
            target[axis] = Q(sign)
            at_one = barycentric(points, target)
            derivative = [x-z for x, z in zip(at_one, zero)]
            bounds.extend(z/(-d) for z, d in zip(zero, derivative) if d < 0)
    return min(bounds)


def sqrt_q_up16(x: Q):
    if x <= 0:
        return Q(0)
    scaled = x * 10**32
    ceiling = -((-scaled.numerator) // scaled.denominator)
    return Q(math.isqrt(ceiling) + 1, 10**16)


def mismatch_radius(interval, symmetry_index):
    pose = pose_center(interval)
    eps = pose_eps(interval)
    inner = rot_rm_q(pose[0], pose[1], pose[4])
    outer_symmetry = matmul(rot_rm_q(pose[2], pose[3], Q(0)),
                               symmetry_matrix_q(symmetry_index))
    mismatch = matsub(inner, outer_symmetry)
    frobenius_sq = sum((x*x for row in mismatch for x in row), Q(0))
    return (sqrt_q_up16(frobenius_sq) + 2*ROTATION_ERROR
            + sum(eps, Q(0))), frobenius_sq


def qjson(x):
    if isinstance(x, Q):
        return f"{x.numerator}/{x.denominator}"
    if isinstance(x, dict):
        return {k: qjson(v) for k, v in x.items()}
    if isinstance(x, (tuple, list)):
        return [qjson(v) for v in x]
    if isinstance(x, (np.integer,)):
        return int(x)
    return x


def best_tetrahedron(points):
    floating = np.asarray([[float(x) for x in p] for p in points])
    hull = ConvexHull(floating)
    candidates = hull.vertices
    best = (0.0, None)
    # Keep this smoke search predictable even if the candidate hull grows.
    if len(candidates) > 80:
        order = np.argsort(np.linalg.norm(floating[candidates], axis=1))[-80:]
        candidates = candidates[order]
    for indices in itertools.combinations(candidates, 4):
        p = floating[list(indices)]
        matrix = np.vstack((p.T, np.ones(4)))
        try:
            lam = np.linalg.solve(matrix, [0, 0, 0, 1])
        except np.linalg.LinAlgError:
            continue
        if lam.min() <= 1e-9:
            continue
        # Cheap floating proxy for the exact six-axis radius.
        radius = math.inf
        inv = np.linalg.inv(matrix)
        lam0 = inv @ np.array([0., 0., 0., 1.])
        for axis in range(3):
            for sign in (-1, 1):
                d = inv @ np.array([sign if i == axis else 0.
                                    for i in range(3)] + [0.])
                radius = min(radius, *(lam0[d < 0]/(-d[d < 0])))
        if radius > best[0]:
            best = (float(radius), tuple(map(int, indices)))
    if best[1] is None:
        raise RuntimeError("no tetrahedron containing the origin")
    return best


def floor_to(x: Q, denominator: int):
    return Q(qfloor(x * denominator), denominator)


def ceil_to(x: Q, denominator: int):
    return -floor_to(-x, denominator)


def local_smoke(theta: Q, phi: Q, half_width: Q, direction_count: int,
                direction_denominator: int):
    center = [theta, phi, theta, phi, Q(0)]
    interval = [(x-half_width, x+half_width) for x in center]
    eps = pose_eps(interval)
    frame = np.asarray([[float(x) for x in row]
                        for row in frame_q(theta, phi)[:2]])
    projected = VERTICES @ frame.T

    supported = []
    for k in range(direction_count):
        angle = -math.pi + (2*math.pi*(k + 0.37))/direction_count
        direction = direction_q(angle, direction_denominator)
        scores = projected @ np.asarray([float(x) for x in direction])
        for vertex in np.argsort(scores)[::-1][:3]:
            vertex = int(vertex)
            if local_supports(center, eps, direction, vertex):
                supported.append((angle, direction, vertex))
                break

    candidates = []
    # Restrict to triples roughly distributed around the circle.  This cuts
    # the cubic search without changing the proof-shaped candidate family.
    n = len(supported)
    for ia, ib, ic in itertools.combinations(range(n), 3):
        if ib-ia < n//8 or ic-ib < n//8 or n-(ic-ia) < n//8:
            continue
        rows = [supported[ia], supported[ib], supported[ic]]
        directions = [row[1] for row in rows]
        weights = determinant_weights(directions)
        if min(weights) <= 0:
            continue
        vertices = [row[2] for row in rows]
        point, _ = normalized_a(center, directions, vertices)
        candidates.append({"directions": directions, "vertices": vertices,
                           "weights": weights, "point": point})

    if len(candidates) < 4:
        raise RuntimeError(f"only {len(candidates)} balanced candidates")
    float_radius, chosen_indices = best_tetrahedron(
        [row["point"] for row in candidates])
    chosen = [candidates[i] for i in chosen_indices]
    points = [row["point"] for row in chosen]
    exact_axis_radius = exact_tetrahedron_axis_radius(points)
    outer_radius = eps[2] + eps[3]
    perturbation = outer_radius + CENTER_VECTOR_ERROR
    # ``octahedronTarget`` has length 7/4*(c+perturbation).  Retain 5% of
    # the exact tetrahedral axis slack against arithmetic boundary cases.
    cover_radius = Q(19, 20) * Q(4, 7) * exact_axis_radius
    c = floor_to(cover_radius - perturbation, 10**6)
    exact_r, frobenius_sq = mismatch_radius(interval, 0)
    r = ceil_to(exact_r, 10**12)
    angle_ok = r*r*(1+c*c) <= 4*c*c
    if c <= 0 or not angle_ok:
        raise RuntimeError(
            f"local angular budget failed c={float(c):.6g} r={float(r):.6g}")
    target_length = Q(7, 4) * (c + perturbation)
    bary = []
    for axis in range(3):
        for sign in (1, -1):
            target = [Q(0)]*3
            target[axis] = sign*target_length
            lam = barycentric(points, target)
            if min(lam) < 0 or sum(lam, Q(0)) != 1:
                raise AssertionError("invalid exact barycentric witness")
            bary.append(lam)

    inverse_action = {SYMMETRY_ACTION[0][i]: i for i in range(24)}
    payload = {
        "interval": interval,
        "symmetry_index": 0,
        "certificates": [{
            "contacts": [{"index": inverse_action[v], "direction": d}
                         for v, d in zip(row["vertices"], row["directions"])],
        } for row in chosen],
        "c": c,
        "r": r,
        "diagnostics": {
            "supported_directions": len(supported),
            "balanced_candidates": len(candidates),
            "floating_axis_radius": float_radius,
            "exact_axis_radius": exact_axis_radius,
            "cover_radius": cover_radius,
            "axis_perturbation": perturbation,
            "mismatch_frobenius_sq": frobenius_sq,
            "exact_mismatch_radius": exact_r,
            "minimum_barycentric": min(x for row in bary for x in row),
            "angle_bound_slack": 4*c*c-r*r*(1+c*c),
        },
    }
    return payload


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    smoke = sub.add_parser("local-smoke")
    smoke.add_argument("--theta", type=str, default="3/10")
    smoke.add_argument("--phi", type=str, default="11/10")
    smoke.add_argument("--half-width", type=str, default="1/100000")
    smoke.add_argument("--directions", type=int, default=72)
    smoke.add_argument("--direction-denominator", type=int, default=100)
    args = parser.parse_args()
    if args.command == "local-smoke":
        result = local_smoke(Q(args.theta), Q(args.phi),
                             Q(args.half_width), args.directions,
                             args.direction_denominator)
        print(json.dumps(qjson(result), indent=2))


if __name__ == "__main__":
    main()
