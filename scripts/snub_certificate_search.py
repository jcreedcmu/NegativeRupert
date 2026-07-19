"""Exact-rational search utilities for snub-cube proof certificates.

The functions in this file mirror the definitions in
``Noperthedron/SnubCube/{Certificate,LocalCertificate}.lean``.  Floating
geometry is used only to select promising witnesses; every accepted witness
is subsequently evaluated with ``fractions.Fraction`` using the same rounded
Taylor data as Lean.

The ``local-smoke`` command searches for four balanced local certificates
around a generic identity-symmetry equality pose.  The ``global-smoke``
command searches for one balanced three-contact global certificate.  Both
print complete JSON payloads small enough to inspect and turn into Lean smoke
theorems before building the adaptive five-dimensional tree.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import random
from fractions import Fraction as Q

import numpy as np
from scipy.spatial import ConvexHull


KAPPA = Q(1, 10**10)
TRIBONACCI_Q = Q(1839286755214161, 10**15)
ROTATION_ERROR = 3 * KAPPA + KAPPA * KAPPA
CENTER_VECTOR_ERROR = 2 * KAPPA + KAPPA * KAPPA
CENTER_RELATIVE_ERROR = 2 * ROTATION_ERROR + ROTATION_ERROR * ROTATION_ERROR

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


def normalized_vertices_exact_float():
    tribonacci = max(x.real for x in np.roots([1, -1, -1, -1])
                     if abs(x.imag) < 1e-12)
    base = (tribonacci, 1.0, tribonacci**2)
    out = []
    for p, perm in enumerate(PERMUTATIONS):
        signs_table = ODD_SIGNS if PERMUTATION_ODD[p] else EVEN_SIGNS
        for signs in signs_table:
            out.append([signs[c] * base[perm[c]] / 5 for c in range(3)])
    return np.asarray(out)


VERTICES_EXACT = normalized_vertices_exact_float()


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


def trace_advantages_q(pose):
    """Exact rational scores used by ``FundamentalPrune.Box.Valid``."""
    inner = rot_rm_q(pose[0], pose[1], pose[4])
    outer = rot_rm_q(pose[2], pose[3], Q(0))
    relative = matmul(transpose(outer), inner)
    identity = [[Q(int(i == j)) for j in range(3)] for i in range(3)]
    values = []
    for g in range(24):
        product = matmul(relative, matsub(symmetry_matrix_q(g), identity))
        values.append(sum((product[i][i] for i in range(3)), Q(0)))
    return values


def fundamental_prune(interval):
    """Return the best symmetry and exact slack, or ``None`` if uncertified."""
    pose = pose_center(interval)
    values = trace_advantages_q(pose)
    symmetry = max(range(24), key=values.__getitem__)
    threshold = 6 * (CENTER_RELATIVE_ERROR + sum(pose_eps(interval), Q(0)))
    slack = values[symmetry] - threshold
    return (symmetry, slack, values[symmetry]) if slack > 0 else None


def ball_const(q):
    return (Q(q), Q(0))


def ball_add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def ball_neg(a):
    return (-a[0], a[1])


def ball_sub(a, b):
    return ball_add(a, ball_neg(b))


def ball_scale(q, a):
    return (q * a[0], abs(q) * a[1])


def ball_mul(a, b):
    return (a[0] * b[0],
            abs(a[0]) * b[1] + a[1] * abs(b[0]) + a[1] * b[1])


def cayley_numerator_balls(x, y, z):
    one = ball_const(1)
    two = Q(2)
    xx, yy, zz = ball_mul(x, x), ball_mul(y, y), ball_mul(z, z)
    xy, xz, yz = ball_mul(x, y), ball_mul(x, z), ball_mul(y, z)
    return [
        [ball_sub(ball_sub(ball_add(one, xx), yy), zz),
         ball_scale(two, ball_sub(xy, z)),
         ball_scale(two, ball_add(xz, y))],
        [ball_scale(two, ball_add(xy, z)),
         ball_sub(ball_add(ball_sub(one, xx), yy), zz),
         ball_scale(two, ball_sub(yz, x))],
        [ball_scale(two, ball_sub(xz, y)),
         ball_scale(two, ball_add(yz, x)),
         ball_add(ball_sub(ball_sub(one, xx), yy), zz)],
    ]


def ball_sum3(values):
    return ball_add(ball_add(values[0], values[1]), values[2])


def cayley_advantage_ball(x, y, z, g):
    numerator = cayley_numerator_balls(x, y, z)
    symmetry = symmetry_matrix_q(g)
    rows = []
    for i in range(3):
        rows.append(ball_sum3([
            ball_scale(symmetry[j][i] - Q(int(j == i)), numerator[i][j])
            for j in range(3)
        ]))
    return ball_sum3(rows)


def cayley_prune_box(center, half_widths):
    variables = [(c, r) for c, r in zip(center, half_widths)]
    balls = [cayley_advantage_ball(*variables, g) for g in range(24)]
    g = max(range(24), key=lambda i: balls[i][0] - balls[i][1])
    return {
        "center": center,
        "half_widths": half_widths,
        "symmetry": g,
        "advantage_ball": balls[g],
        "lower_bound": balls[g][0] - balls[g][1],
    }


def cayley_denom_ball(x, y, z):
    return ball_add(ball_const(1), ball_sum3(
        [ball_mul(x, x), ball_mul(y, y), ball_mul(z, z)]))


def cayley_global_contact_ball(theta, phi, variables, direction,
                               inner_index, outer_index):
    """Polynomial numerator for one balanced Cayley displacement contact."""
    numerator = cayley_numerator_balls(*variables)
    denom = cayley_denom_ball(*variables)
    inner = VERTICES_Q[inner_index]
    outer = VERTICES_Q[outer_index]
    vector = []
    for i in range(3):
        ni = ball_sum3([ball_scale(inner[j], numerator[i][j])
                        for j in range(3)])
        vector.append(ball_sub(ni, ball_scale(outer[i], denom)))
    lift = matvec(transpose(frame_q(theta, phi)[:2]), direction)
    return ball_sum3([ball_scale(lift[i], vector[i]) for i in range(3)])


def cayley_global_smoke(center, half_widths, direction_count: int,
                        direction_denominator: int):
    """Search the proposed quadratic Cayley global-certificate checker."""
    theta, phi, x, y, z = center
    etheta, ephi, ex, ey, ez = half_widths
    variables = [(x, ex), (y, ey), (z, ez)]
    pose = [theta, phi, theta, phi, Q(0)]
    eps = [etheta, ephi, etheta, ephi, Q(0)]
    rows = []
    for k in range(direction_count):
        angle = -math.pi + (2*math.pi*(k + 0.37))/direction_count
        direction = direction_q(angle, direction_denominator)
        frame = np.asarray([[float(a) for a in row]
                            for row in frame_q(theta, phi)[:2]])
        scores = VERTICES @ frame.T @ np.asarray(
            [float(a) for a in direction])
        outer_candidates = np.argsort(scores)[::-1][:3]
        outer_index = next((int(q) for q in outer_candidates
                            if local_supports(pose, eps, direction, int(q))),
                           None)
        if outer_index is None:
            continue
        balls = [cayley_global_contact_ball(
            theta, phi, variables, direction, p, outer_index)
            for p in range(24)]
        inner_index = max(range(24), key=lambda p: balls[p][0]-balls[p][1])
        rows.append({"angle": angle, "direction": direction,
                     "inner_index": inner_index, "outer_index": outer_index,
                     "ball": balls[inner_index]})
    d_bound = 1 + sum(max(abs(c-e), abs(c+e))**2
                      for c, e in zip((x, y, z), (ex, ey, ez)))
    view_error = etheta + ephi + KAPPA
    contact_error = 2*d_bound*(KAPPA + (1+KAPPA)*view_error)
    best = None
    for indices in itertools.combinations(range(len(rows)), 3):
        chosen = [rows[i] for i in indices]
        weights = determinant_weights([row["direction"] for row in chosen])
        if min(weights) <= 0:
            continue
        total = ball_const(0)
        for weight, row in zip(weights, chosen):
            total = ball_add(total, ball_scale(weight, row["ball"]))
        error = sum(weights, Q(0))*contact_error
        lower = total[0]-total[1]-error
        normalized = lower/sum(weights, Q(0))
        if best is None or normalized > best[0]:
            best = (normalized, lower, total, error, weights, chosen)
    if best is None or best[1] <= 0:
        raise RuntimeError("no positive Cayley global certificate")
    normalized, lower, total, error, weights, chosen = best
    return {
        "center": center,
        "half_widths": half_widths,
        "contacts": [{"inner_index": row["inner_index"],
                      "outer_index": row["outer_index"],
                      "direction": row["direction"]}
                     for row in chosen],
        "diagnostics": {"supported_directions": len(rows),
                        "displacement_ball": total,
                        "error": error, "lower_bound": lower,
                        "normalized_lower_bound": normalized,
                        "d_bound": d_bound,
                        "contact_error": contact_error},
    }


def ball_dot(a, b):
    return ball_sum3([ball_mul(x, y) for x, y in zip(a, b)])


def ball_cross_const_left(a, b):
    return [ball_sub(ball_scale(a[1], b[2]), ball_scale(a[2], b[1])),
            ball_sub(ball_scale(a[2], b[0]), ball_scale(a[0], b[2])),
            ball_sub(ball_scale(a[0], b[1]), ball_scale(a[1], b[0]))]


def cayley_view_balls(theta, phi, etheta, ephi):
    """Enclose the viewing unit vector over one outer-angle rectangle."""
    st = (sin_q(theta), etheta + KAPPA)
    ct = (cos_q(theta), etheta + KAPPA)
    sp = (sin_q(phi), ephi + KAPPA)
    cp = (cos_q(phi), ephi + KAPPA)
    return [ball_mul(ct, sp), ball_mul(st, sp), cp]


def edge_orientation_ball(view, q0, q1, q):
    """`view · ((q1-q0) × (q-q0))` using rational vertices."""
    edge = [a-b for a, b in zip(VERTICES_Q[q1], VERTICES_Q[q0])]
    delta = [a-b for a, b in zip(VERTICES_Q[q], VERTICES_Q[q0])]
    cross = cross3(edge, delta)
    return ball_sum3([ball_scale(cross[i], view[i]) for i in range(3)])


def cayley_edge_contact_ball(view, variables, q0, q1, inner_index):
    """Denominator-cleared outward-edge displacement contact."""
    edge = [a-b for a, b in zip(VERTICES_Q[q1], VERTICES_Q[q0])]
    numerator = cayley_numerator_balls(*variables)
    denom = cayley_denom_ball(*variables)
    inner = VERTICES_Q[inner_index]
    outer = VERTICES_Q[q0]
    displacement = []
    for i in range(3):
        ni = ball_sum3([ball_scale(inner[j], numerator[i][j])
                        for j in range(3)])
        displacement.append(ball_sub(ni, ball_scale(outer[i], denom)))
    cross = ball_cross_const_left(edge, displacement)
    # Clockwise rotation of a CCW projected edge is its outward normal, so
    # the planar inner product is minus this scalar triple product.
    return ball_neg(ball_dot(view, cross))


# Coefficients in the basis 1,x,y,z,x²,xy,xz,y²,yz,z².
QUADRATIC_EXPONENTS = (
    (0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1),
    (2, 0, 0), (1, 1, 0), (1, 0, 1),
    (0, 2, 0), (0, 1, 1), (0, 0, 2))


def qpoly_zero():
    return [Q(0)] * 10


def qpoly_add(a, b):
    return [x+y for x, y in zip(a, b)]


def qpoly_scale(q, a):
    return [q*x for x in a]


def qpoly_eval_centered(coefficients, centers, radii):
    """Tight centered enclosure of a normalized quadratic polynomial."""
    x, y, z = centers
    rx, ry, rz = radii
    c = coefficients
    value = (c[0] + c[1]*x + c[2]*y + c[3]*z + c[4]*x*x +
             c[5]*x*y + c[6]*x*z + c[7]*y*y + c[8]*y*z + c[9]*z*z)
    gradient = [c[1] + 2*c[4]*x + c[5]*y + c[6]*z,
                c[2] + c[5]*x + 2*c[7]*y + c[8]*z,
                c[3] + c[6]*x + c[8]*y + 2*c[9]*z]
    linear_radius = sum(abs(g)*r for g, r in zip(gradient, radii))
    quadratic_radius = (abs(c[4])*rx*rx + abs(c[5])*rx*ry +
                        abs(c[6])*rx*rz + abs(c[7])*ry*ry +
                        abs(c[8])*ry*rz + abs(c[9])*rz*rz)
    return value, linear_radius + quadratic_radius


def cayley_numerator_qpolys():
    one, x, y, z, xx, xy, xz, yy, yz, zz = range(10)
    def p(**terms):
        ans = qpoly_zero()
        for name, value in terms.items():
            ans[{"one": one, "x": x, "y": y, "z": z, "xx": xx,
                 "xy": xy, "xz": xz, "yy": yy, "yz": yz,
                 "zz": zz}[name]] = Q(value)
        return ans
    return [
        [p(one=1, xx=1, yy=-1, zz=-1), p(xy=2, z=-2), p(xz=2, y=2)],
        [p(xy=2, z=2), p(one=1, xx=-1, yy=1, zz=-1), p(yz=2, x=-2)],
        [p(xz=2, y=-2), p(yz=2, x=2), p(one=1, xx=-1, yy=-1, zz=1)],
    ]


CAYLEY_NUMERATOR_QPOLYS = cayley_numerator_qpolys()
CAYLEY_DENOM_QPOLY = [Q(1), 0, 0, 0, 1, 0, 0, 1, 0, 1]


def cayley_edge_contact_qpolys(q0, q1, inner_index):
    """Three coefficients of `-edge × (N P - d Q)` for one edge."""
    edge = [a-b for a, b in zip(VERTICES_Q[q1], VERTICES_Q[q0])]
    inner = VERTICES_Q[inner_index]
    outer = VERTICES_Q[q0]
    displacement = []
    for i in range(3):
        value = qpoly_zero()
        for j in range(3):
            value = qpoly_add(value, qpoly_scale(
                inner[j], CAYLEY_NUMERATOR_QPOLYS[i][j]))
        displacement.append(qpoly_add(
            value, qpoly_scale(-outer[i], CAYLEY_DENOM_QPOLY)))
    cross = [qpoly_add(qpoly_scale(edge[1], displacement[2]),
                       qpoly_scale(-edge[2], displacement[1])),
             qpoly_add(qpoly_scale(edge[2], displacement[0]),
                       qpoly_scale(-edge[0], displacement[2])),
             qpoly_add(qpoly_scale(edge[0], displacement[1]),
                       qpoly_scale(-edge[1], displacement[0]))]
    return [qpoly_scale(-1, value) for value in cross]


def cayley_edge_smoke(center, half_widths):
    """Search a pose-dependent projected-edge balanced-support certificate.

    This prototype freezes only the outer silhouette cycle and one inner
    vertex per edge.  Edge normals themselves vary with the outer pose and
    sum identically to zero around the cycle.
    """
    theta, phi, x, y, z = center
    etheta, ephi, ex, ey, ez = half_widths
    view = cayley_view_balls(theta, phi, etheta, ephi)
    frame = np.asarray([[float(q) for q in row]
                        for row in frame_q(theta, phi)[:2]])
    projected = VERTICES_EXACT @ frame.T
    cycle = list(map(int, ConvexHull(projected).vertices))
    variables = [(x, ex), (y, ey), (z, ez)]
    contacts = []
    total_polys = [qpoly_zero(), qpoly_zero(), qpoly_zero()]
    minimum_support = None
    minimum_strict = None
    total_defect = Q(0)
    for index, q0 in enumerate(cycle):
        q1 = cycle[(index+1) % len(cycle)]
        supports = [edge_orientation_ball(view, q0, q1, q)
                    for q in range(24)]
        support_lower = min(ball[0]-ball[1] for ball in supports)
        strict_lower = max(ball[0]-ball[1] for ball in supports)
        minimum_support = (support_lower if minimum_support is None else
                           min(minimum_support, support_lower))
        minimum_strict = (strict_lower if minimum_strict is None else
                          min(minimum_strict, strict_lower))
        if strict_lower <= 0:
            raise RuntimeError(
                f"projected edge may vanish strict={float(strict_lower):.6g}")
        # `u·(K-Q) = -orientation`; its certified maximum is the support
        # defect consumed by the balanced-support-with-defect theorem.
        total_defect += max(Q(0), max(-(ball[0]-ball[1])
                                      for ball in supports))
        balls = [cayley_edge_contact_ball(view, variables, q0, q1, p)
                 for p in range(24)]
        inner = max(range(24), key=lambda p: balls[p][0]-balls[p][1])
        contact_polys = cayley_edge_contact_qpolys(q0, q1, inner)
        total_polys = [qpoly_add(a, b)
                       for a, b in zip(total_polys, contact_polys)]
        contacts.append({"outer_index": q0, "next_outer_index": q1,
                         "inner_index": inner, "ball": balls[inner]})
    component_balls = [qpoly_eval_centered(poly, (x, y, z), (ex, ey, ez))
                       for poly in total_polys]
    total = ball_dot(view, component_balls)
    # The eventual Lean bridge will use a much smaller exact-vertex error;
    # retain a visible conservative prototype allowance for now.
    error = Q(len(cycle), 10**8)
    lower = total[0]-total[1]-total_defect-error
    if lower < 0:
        raise RuntimeError(
            f"edge displacement fails by {-float(lower):.6g}")
    return {
        "center": center,
        "half_widths": half_widths,
        "cycle": cycle,
        "contacts": contacts,
        "diagnostics": {
            "edge_count": len(cycle),
            "minimum_support_lower": minimum_support,
            "minimum_strict_support_lower": minimum_strict,
            "total_support_defect": total_defect,
            "displacement_ball": total,
            "error": error,
            "lower_bound": lower,
        },
    }


def validate_cayley_global_certificate(payload, samples: int, seed: int):
    """Monte Carlo audit of the analytic error budget used by the prototype."""
    rng = random.Random(seed)
    center = payload["center"]
    widths = payload["half_widths"]
    contacts = payload["contacts"]
    weights = determinant_weights([row["direction"] for row in contacts])
    ball = payload["diagnostics"]["displacement_ball"]
    error = payload["diagnostics"]["error"]
    worst_excess = -math.inf
    minimum_numerator = math.inf
    for _ in range(samples):
        theta, phi, x, y, z = [
            float(c) + rng.uniform(-float(e), float(e))
            for c, e in zip(center, widths)]
        d = 1 + x*x + y*y + z*z
        numerator = np.array([
            [1+x*x-y*y-z*z, 2*(x*y-z), 2*(x*z+y)],
            [2*(x*y+z), 1-x*x+y*y-z*z, 2*(y*z-x)],
            [2*(x*z-y), 2*(y*z+x), 1-x*x-y*y+z*z]])
        m = np.array([[-math.sin(theta), math.cos(theta), 0.0],
                      [-math.cos(theta)*math.cos(phi),
                       -math.sin(theta)*math.cos(phi), math.sin(phi)]])
        total = 0.0
        for weight, row in zip(weights, contacts):
            direction = np.asarray([float(q) for q in row["direction"]])
            inner = VERTICES_EXACT[row["inner_index"]]
            outer = VERTICES_EXACT[row["outer_index"]]
            total += float(weight) * direction @ m @ (
                numerator @ inner - d*outer)
        excess = abs(total-float(ball[0]))-float(ball[1])-float(error)
        worst_excess = max(worst_excess, excess)
        minimum_numerator = min(minimum_numerator, total)
    return {"samples": samples, "worst_enclosure_excess": worst_excess,
            "minimum_exact_numerator": minimum_numerator}


def prune_sample(half_width: Q, samples: int, denominator: int, seed: int):
    """Estimate exact prune coverage on the bounded fundamental root.

    Sampling only chooses centers; every prune decision uses the exact same
    rational Taylor arithmetic and strict inequality as Lean.
    """
    root = [(Q(-4), Q(4)), (Q(0), Q(4)), (Q(0), Q(2)),
            (Q(0), Q(2)), (Q(-4), Q(4))]
    rng = random.Random(seed)
    pruned = 0
    inside_at_center = 0
    slacks = []
    symmetry_counts = [0] * 24
    for _ in range(samples):
        center = []
        for lo, hi in root:
            ilo = math.ceil(float((lo + half_width) * denominator))
            ihi = math.floor(float((hi - half_width) * denominator))
            center.append(Q(rng.randint(ilo, ihi), denominator))
        values = trace_advantages_q(center)
        if max(values) <= 0:
            inside_at_center += 1
        interval = [(x - half_width, x + half_width) for x in center]
        result = fundamental_prune(interval)
        if result is not None:
            symmetry, slack, _ = result
            pruned += 1
            symmetry_counts[symmetry] += 1
            slacks.append(float(slack))
    quantiles = ([float(x) for x in np.quantile(slacks, [.01, .1, .5, .9])]
                 if slacks else [])
    return {
        "half_width": half_width,
        "samples": samples,
        "pruned": pruned,
        "pruned_fraction": pruned / samples,
        "center_in_domain_fraction": inside_at_center / samples,
        "pruned_slack_quantiles_01_10_50_90": quantiles,
        "symmetry_counts": symmetry_counts,
    }


def global_domain_sample(half_width: Q, samples: int, denominator: int,
                         seed: int, directions: int,
                         direction_denominator: int):
    """Test global certificates at centers lying in the exact Dirichlet cell."""
    root = [(Q(-4), Q(4)), (Q(0), Q(4)), (Q(0), Q(2)),
            (Q(0), Q(2)), (Q(-4), Q(4))]
    rng = random.Random(seed)
    accepted = 0
    attempts = 0
    margins = []
    while accepted < samples:
        attempts += 1
        center = []
        for lo, hi in root:
            ilo = math.ceil(float((lo + half_width) * denominator))
            ihi = math.floor(float((hi - half_width) * denominator))
            center.append(Q(rng.randint(ilo, ihi), denominator))
        if max(trace_advantages_q(center)) > 0:
            continue
        accepted += 1
        try:
            result = global_smoke(center, [half_width] * 5, directions,
                                  direction_denominator)
        except RuntimeError:
            continue
        margins.append(float(result["diagnostics"]["normalized_margin"]))
    quantiles = ([float(x) for x in np.quantile(margins, [.01, .1, .5, .9])]
                 if margins else [])
    return {
        "half_width": half_width,
        "domain_samples": samples,
        "raw_attempts": attempts,
        "global_certified": len(margins),
        "global_certified_fraction": len(margins) / samples,
        "margin_quantiles_01_10_50_90": quantiles,
    }


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


def best_tetrahedron(points, trial_limit: int = 50000):
    """Choose a well-conditioned tetrahedron containing the origin.

    Older smoke generation exhausted every four-subset of as many as eighty
    hull vertices (about 1.6 million dense solves).  Tree generation needs
    this operation at many outer-view boxes, so use a deterministic bounded
    candidate family instead.  Acceptance and the eventual radius are still
    recomputed with exact rational barycentric coordinates.
    """
    floating = np.asarray([[float(x) for x in p] for p in points])
    hull = ConvexHull(floating)
    candidates = list(map(int, hull.vertices))
    best = (0.0, None)
    if len(candidates) > 96:
        order = np.argsort(np.linalg.norm(floating[candidates], axis=1))[-96:]
        candidates = [candidates[i] for i in order]

    total_combinations = math.comb(len(candidates), 4)
    if total_combinations <= trial_limit:
        candidate_sets = itertools.combinations(candidates, 4)
    else:
        rng = random.Random(0)
        seen = set()

        # Regular-tetrahedron support points supply several strong seeds.
        tetra_normals = np.asarray([
            [1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]],
            dtype=float)
        for shift in range(12):
            angle = 2 * math.pi * shift / 12
            ca, sa = math.cos(angle), math.sin(angle)
            rotation = np.asarray([[ca, -sa, 0], [sa, ca, 0], [0, 0, 1]])
            normals = tetra_normals @ rotation.T
            indices = tuple(sorted(candidates[int(np.argmax(
                floating[candidates] @ normal))] for normal in normals))
            if len(set(indices)) == 4:
                seen.add(indices)

        while len(seen) < trial_limit:
            seen.add(tuple(sorted(rng.sample(candidates, 4))))
        candidate_sets = sorted(seen)

    for indices in candidate_sets:
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


def cayley_local_smoke(center, half_widths, direction_count: int,
                       direction_denominator: int):
    """Search a strengthened equality-stratum Cayley local certificate.

    Only the two outer angles enter the geometric certificate.  The relative
    Cayley cube is accepted by the separate exact squared-radius condition;
    no generic five-Euler-parameter mismatch budget is imposed.
    """
    theta, phi, x, y, z = center
    etheta, ephi, ex, ey, ez = half_widths
    pose = [theta, phi, theta, phi, Q(0)]
    eps = [etheta, ephi, etheta, ephi, Q(0)]
    frame = np.asarray([[float(q) for q in row]
                        for row in frame_q(theta, phi)[:2]])
    projected = VERTICES @ frame.T

    supported = []
    for k in range(direction_count):
        angle = -math.pi + (2*math.pi*(k + 0.37))/direction_count
        direction = direction_q(angle, direction_denominator)
        scores = projected @ np.asarray([float(q) for q in direction])
        for vertex in np.argsort(scores)[::-1][:3]:
            vertex = int(vertex)
            if local_supports(pose, eps, direction, vertex):
                supported.append((angle, direction, vertex))
                break

    candidates = []
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
        point, _ = normalized_a(pose, directions, vertices)
        candidates.append({"directions": directions, "vertices": vertices,
                           "weights": weights, "point": point})

    if len(candidates) < 4:
        raise RuntimeError(f"only {len(candidates)} balanced candidates")
    float_radius, chosen_indices = best_tetrahedron(
        [row["point"] for row in candidates])
    chosen = [candidates[i] for i in chosen_indices]
    points = [row["point"] for row in chosen]
    exact_axis_radius = exact_tetrahedron_axis_radius(points)
    perturbation = etheta + ephi + CENTER_VECTOR_ERROR
    cover_radius = Q(19, 20) * Q(4, 7) * exact_axis_radius
    c = floor_to(cover_radius - perturbation, 10**6)
    radius_sq = sum(
        max(abs(value-width), abs(value+width))**2
        for value, width in zip((x, y, z), (ex, ey, ez)))
    if c <= 0 or radius_sq > c*c:
        raise RuntimeError(
            f"Cayley local radius failed c={float(c):.6g} "
            f"radius={math.sqrt(float(radius_sq)):.6g}")

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
    return {
        "center": center,
        "half_widths": half_widths,
        "certificates": [{
            "contacts": [{"index": inverse_action[v], "direction": d}
                         for v, d in zip(row["vertices"], row["directions"])],
        } for row in chosen],
        "c": c,
        "r": Q(0),
        "diagnostics": {
            "supported_directions": len(supported),
            "balanced_candidates": len(candidates),
            "floating_axis_radius": float_radius,
            "exact_axis_radius": exact_axis_radius,
            "cover_radius": cover_radius,
            "axis_perturbation": perturbation,
            "radius_sq": radius_sq,
            "radius_slack": c*c-radius_sq,
            "minimum_barycentric": min(x for row in bary for x in row),
        },
    }


def global_smoke(center, half_widths, direction_count: int,
                 direction_denominator: int):
    """Find the strongest determinant-balanced global triple for one box.

    Poses use the calculation-friendly order ``theta1, phi1, theta2, phi2,
    alpha`` in this script.  Each sampled direction keeps the inner vertex
    with the largest exact Taylor lower bound.  We then exhaustively compare
    positively oriented triples, using their exact determinant weights.
    """
    interval = [(x-e, x+e) for x, e in zip(center, half_widths)]
    eps = pose_eps(interval)
    rows = []
    for k in range(direction_count):
        angle = -math.pi + (2*math.pi*(k + 0.37))/direction_count
        direction = direction_q(angle, direction_denominator)
        outer = max_h(center, eps[2], eps[3], direction)
        inner_values = [fast_g(center, eps[4], eps[0], eps[1], direction, v)
                        for v in VERTICES_Q]
        inner_index = max(range(24), key=inner_values.__getitem__)
        rows.append({
            "angle": angle,
            "direction": direction,
            "inner_index": inner_index,
            "outer": outer,
            "inner": inner_values[inner_index],
            "margin": inner_values[inner_index] - outer,
        })

    best = None
    for indices in itertools.combinations(range(direction_count), 3):
        chosen = [rows[i] for i in indices]
        weights = determinant_weights([row["direction"] for row in chosen])
        if min(weights) <= 0:
            continue
        margin = sum((weight*row["margin"]
                      for weight, row in zip(weights, chosen)), Q(0))
        normalized_margin = margin / sum(weights, Q(0))
        if best is None or normalized_margin > best[0]:
            best = (normalized_margin, margin, weights, chosen)
    if best is None:
        raise RuntimeError("no positively balanced direction triple")
    normalized_margin, margin, weights, chosen = best
    if margin < 0:
        raise RuntimeError(
            f"best global triple fails by {-float(normalized_margin):.6g}")
    return {
        "interval": interval,
        "contacts": [{
            "inner_index": row["inner_index"],
            "outer_index": 0,
            "direction": row["direction"],
            "weight": weight,
        } for weight, row in zip(weights, chosen)],
        "diagnostics": {
            "weighted_margin": margin,
            "normalized_margin": normalized_margin,
            "individual_margins": [row["margin"] for row in chosen],
            "direction_angles": [row["angle"] for row in chosen],
        },
    }


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    smoke = sub.add_parser("local-smoke")
    smoke.add_argument("--theta", type=str, default="3/10")
    smoke.add_argument("--phi", type=str, default="11/10")
    smoke.add_argument("--half-width", type=str, default="1/100000")
    smoke.add_argument("--directions", type=int, default=72)
    smoke.add_argument("--direction-denominator", type=int, default=100)
    global_parser = sub.add_parser("global-smoke")
    global_parser.add_argument(
        "--center", default="0,0,1,1,0",
        help="theta1,phi1,theta2,phi2,alpha as comma-separated rationals")
    global_parser.add_argument(
        "--half-widths", default="1/100,1/100,1/100,1/100,1/100",
        help="five comma-separated rational half-widths")
    global_parser.add_argument("--directions", type=int, default=72)
    global_parser.add_argument("--direction-denominator", type=int, default=100)
    prune_parser = sub.add_parser("prune-sample")
    prune_parser.add_argument("--half-width", type=str, default="1/100")
    prune_parser.add_argument("--samples", type=int, default=10000)
    prune_parser.add_argument("--denominator", type=int, default=10000)
    prune_parser.add_argument("--seed", type=int, default=1)
    domain_parser = sub.add_parser("global-domain-sample")
    domain_parser.add_argument("--half-width", type=str, default="1/20")
    domain_parser.add_argument("--samples", type=int, default=100)
    domain_parser.add_argument("--denominator", type=int, default=10000)
    domain_parser.add_argument("--seed", type=int, default=1)
    domain_parser.add_argument("--directions", type=int, default=24)
    domain_parser.add_argument("--direction-denominator", type=int, default=100)
    cayley_prune_parser = sub.add_parser("cayley-prune")
    cayley_prune_parser.add_argument("--center", type=str, default="0,0,1")
    cayley_prune_parser.add_argument(
        "--half-widths", type=str, default="1/100,1/100,1/100")
    cayley_global_parser = sub.add_parser("cayley-global-smoke")
    cayley_global_parser.add_argument(
        "--center", default="3/10,11/10,1/5,1/10,0",
        help="theta,phi,x,y,z as comma-separated rationals")
    cayley_global_parser.add_argument(
        "--half-widths", default="1/200,1/200,1/200,1/200,1/200",
        help="five comma-separated rational half-widths")
    cayley_global_parser.add_argument("--directions", type=int, default=72)
    cayley_global_parser.add_argument("--direction-denominator", type=int,
                                      default=1000)
    cayley_global_parser.add_argument("--audit-samples", type=int, default=10000)
    cayley_global_parser.add_argument("--seed", type=int, default=1)
    cayley_local_parser = sub.add_parser("cayley-local-smoke")
    cayley_local_parser.add_argument(
        "--center", default="3/10,11/10,0,0,0",
        help="theta,phi,x,y,z as comma-separated rationals")
    cayley_local_parser.add_argument(
        "--half-widths", default="1/200,1/200,1/200,1/200,1/200",
        help="five comma-separated rational half-widths")
    cayley_local_parser.add_argument("--directions", type=int, default=72)
    cayley_local_parser.add_argument("--direction-denominator", type=int,
                                     default=100)
    cayley_edge_parser = sub.add_parser("cayley-edge-smoke")
    cayley_edge_parser.add_argument(
        "--center", default="3/10,11/10,1/5,1/10,0",
        help="theta,phi,x,y,z as comma-separated rationals")
    cayley_edge_parser.add_argument(
        "--half-widths", default="1/100,1/100,1/100,1/100,1/100",
        help="five comma-separated rational half-widths")
    args = parser.parse_args()
    if args.command == "local-smoke":
        result = local_smoke(Q(args.theta), Q(args.phi),
                             Q(args.half_width), args.directions,
                             args.direction_denominator)
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "global-smoke":
        center = [Q(x) for x in args.center.split(",")]
        half_widths = [Q(x) for x in args.half_widths.split(",")]
        if len(center) != 5 or len(half_widths) != 5:
            parser.error("center and half-widths must each have five entries")
        result = global_smoke(center, half_widths, args.directions,
                              args.direction_denominator)
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "prune-sample":
        result = prune_sample(Q(args.half_width), args.samples,
                              args.denominator, args.seed)
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "global-domain-sample":
        result = global_domain_sample(
            Q(args.half_width), args.samples, args.denominator, args.seed,
            args.directions, args.direction_denominator)
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "cayley-prune":
        center = [Q(x) for x in args.center.split(",")]
        half_widths = [Q(x) for x in args.half_widths.split(",")]
        result = cayley_prune_box(center, half_widths)
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "cayley-global-smoke":
        center = [Q(x) for x in args.center.split(",")]
        half_widths = [Q(x) for x in args.half_widths.split(",")]
        if len(center) != 5 or len(half_widths) != 5:
            parser.error("center and half-widths must each have five entries")
        result = cayley_global_smoke(
            center, half_widths, args.directions,
            args.direction_denominator)
        result["audit"] = validate_cayley_global_certificate(
            result, args.audit_samples, args.seed)
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "cayley-local-smoke":
        center = [Q(x) for x in args.center.split(",")]
        half_widths = [Q(x) for x in args.half_widths.split(",")]
        if len(center) != 5 or len(half_widths) != 5:
            parser.error("center and half-widths must each have five entries")
        result = cayley_local_smoke(
            center, half_widths, args.directions,
            args.direction_denominator)
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "cayley-edge-smoke":
        center = [Q(x) for x in args.center.split(",")]
        half_widths = [Q(x) for x in args.half_widths.split(",")]
        if len(center) != 5 or len(half_widths) != 5:
            parser.error("center and half-widths must each have five entries")
        print(json.dumps(qjson(cayley_edge_smoke(center, half_widths)),
                         indent=2))


if __name__ == "__main__":
    main()
