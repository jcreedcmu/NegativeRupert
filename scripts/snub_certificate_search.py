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
import functools
import itertools
import json
import math
import os
import random
import sys
from fractions import Fraction as Q

if os.environ.get("NOPERT_GMPY2"):
    from gmpy2 import mpq as Q  # noqa: F811 (see nopert214_certificate_search)

try:
    import numpy as np
    from scipy.spatial import ConvexHull
except ModuleNotFoundError:
    # The exact certificate generators below use only the standard library.
    # Keep them runnable on proof-checking machines without the optional
    # floating-geometry search dependencies.
    np = None
    ConvexHull = None


KAPPA = Q(1, 10**10)
SUPPORT_ERROR = 10 * KAPPA
PROJECTIVE_VARIATION_ERROR = 150 * KAPPA
PROJECTIVE_CERTIFICATE_DENOMINATOR = 10**9
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
VERTICES = (np.asarray([[float(x) for x in v] for v in VERTICES_Q])
            if np is not None else None)


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


VERTICES_EXACT = (normalized_vertices_exact_float()
                  if np is not None else None)


# Exact arithmetic in Q[t]/(t^3-t^2-t-1), matching ExactArithmetic.lean.
def texpr_add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def texpr_neg(a):
    return tuple(-x for x in a)


def texpr_sub(a, b):
    return texpr_add(a, texpr_neg(b))


def texpr_scale(q, a):
    return tuple(q*x for x in a)


def texpr_mul(a, b):
    d0 = a[0]*b[0]
    d1 = a[0]*b[1] + a[1]*b[0]
    d2 = a[0]*b[2] + a[1]*b[1] + a[2]*b[0]
    d3 = a[1]*b[2] + a[2]*b[1]
    d4 = a[2]*b[2]
    return (d0+d3+d4, d1+d3+2*d4, d2+d3+2*d4)


TEXPR_ZERO = (Q(0), Q(0), Q(0))
TEXPR_ONE = (Q(1), Q(0), Q(0))


def texpr_inv(a):
    """Inverse in Q[t]/(t^3-t^2-t-1), by exact Gaussian elimination."""
    columns = [texpr_mul(a, basis) for basis in (
        TEXPR_ONE, (Q(0), Q(1), Q(0)), (Q(0), Q(0), Q(1)))]
    matrix = [[columns[column][row] for column in range(3)] +
              [Q(1 if row == 0 else 0)] for row in range(3)]
    for column in range(3):
        pivot = next(row for row in range(column, 3)
                     if matrix[row][column] != 0)
        matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
        scale = matrix[column][column]
        matrix[column] = [value/scale for value in matrix[column]]
        for row in range(3):
            if row == column:
                continue
            scale = matrix[row][column]
            matrix[row] = [x-scale*y for x, y in
                           zip(matrix[row], matrix[column])]
    result = tuple(matrix[row][3] for row in range(3))
    assert texpr_mul(a, result) == TEXPR_ONE
    return result


# Sparse polynomials in `(d,t)` with exact tribonacci-field coefficients.
def tpoly_const(value):
    return {} if value == TEXPR_ZERO else {(0, 0): value}


def tpoly_var(index):
    return {(1, 0) if index == 0 else (0, 1): TEXPR_ONE}


def tpoly_add(a, b):
    out = dict(a)
    for power, coefficient in b.items():
        out[power] = texpr_add(out.get(power, TEXPR_ZERO), coefficient)
        if out[power] == TEXPR_ZERO:
            del out[power]
    return out


def tpoly_neg(a):
    return {power: texpr_neg(coefficient)
            for power, coefficient in a.items()}


def tpoly_sub(a, b):
    return tpoly_add(a, tpoly_neg(b))


def tpoly_mul(a, b):
    out = {}
    for (ad, at), ac in a.items():
        for (bd, bt), bc in b.items():
            power = (ad+bd, at+bt)
            out[power] = texpr_add(
                out.get(power, TEXPR_ZERO), texpr_mul(ac, bc))
            if out[power] == TEXPR_ZERO:
                del out[power]
    return out


def tpoly_scale(coefficient, value):
    return tpoly_mul(tpoly_const(coefficient), value)


# Sparse exact polynomials with an arbitrary number of variables.  These are
# used for the five-variable blow-up `(d,e,a,b,t)` after the exploratory
# scaling has been fixed.
def epoly_const(arity, value):
    return {} if value == TEXPR_ZERO else {(0,)*arity: value}


def epoly_var(arity, index):
    power = [0]*arity
    power[index] = 1
    return {tuple(power): TEXPR_ONE}


def epoly_add(left, right):
    out = dict(left)
    for power, coefficient in right.items():
        out[power] = texpr_add(out.get(power, TEXPR_ZERO), coefficient)
        if out[power] == TEXPR_ZERO:
            del out[power]
    return out


def epoly_neg(value):
    return {power: texpr_neg(coefficient)
            for power, coefficient in value.items()}


def epoly_sub(left, right):
    return epoly_add(left, epoly_neg(right))


def epoly_mul(left, right):
    out = {}
    for left_power, left_coefficient in left.items():
        for right_power, right_coefficient in right.items():
            power = tuple(a+b for a, b in zip(left_power, right_power))
            out[power] = texpr_add(out.get(power, TEXPR_ZERO),
                                  texpr_mul(left_coefficient,
                                            right_coefficient))
            if out[power] == TEXPR_ZERO:
                del out[power]
    return out


def epoly_scale(coefficient, value):
    if not value or coefficient == TEXPR_ZERO:
        return {}
    return {power: texpr_mul(coefficient, term)
            for power, term in value.items()}


def normalized_vertices_symbolic():
    base = ((Q(0), Q(1), Q(0)),
            (Q(1), Q(0), Q(0)),
            (Q(0), Q(0), Q(1)))
    out = []
    for p, perm in enumerate(PERMUTATIONS):
        signs_table = ODD_SIGNS if PERMUTATION_ODD[p] else EVEN_SIGNS
        for signs in signs_table:
            out.append([texpr_scale(Q(signs[c], 5), base[perm[c]])
                        for c in range(3)])
    return out


VERTICES_SYMBOLIC = normalized_vertices_symbolic()


def symbolic_cross(a, b):
    return [texpr_sub(texpr_mul(a[1], b[2]), texpr_mul(a[2], b[1])),
            texpr_sub(texpr_mul(a[2], b[0]), texpr_mul(a[0], b[2])),
            texpr_sub(texpr_mul(a[0], b[1]), texpr_mul(a[1], b[0]))]


def symbolic_support_zero(triangle, start, finish, selected, k):
    edge = [texpr_sub(x, y) for x, y in
            zip(VERTICES_SYMBOLIC[start], VERTICES_SYMBOLIC[finish])]
    delta = [texpr_sub(x, y) for x, y in
             zip(VERTICES_SYMBOLIC[k], VERTICES_SYMBOLIC[selected])]
    coefficient = symbolic_cross(edge, delta)
    return all(
        texpr_add(texpr_add(texpr_scale(corner[0], coefficient[0]),
                            texpr_scale(corner[1], coefficient[1])),
                  texpr_scale(corner[2], coefficient[2])) == (Q(0), Q(0), Q(0))
        for corner in triangle)


def exact_z_transition_quotient():
    """Exact seam^2 quotient for the hard z-axis transition certificate."""
    starts = [14, 8, 5]
    finishes = [4, 9, 15]
    supports = [14, 1, 15]
    competitor = None
    edges = [[texpr_sub(x, y) for x, y in zip(
        VERTICES_SYMBOLIC[start], VERTICES_SYMBOLIC[finish])]
        for start, finish in zip(starts, finishes)]
    transition_edge = [texpr_sub(x, y) for x, y in zip(
        VERTICES_SYMBOLIC[15], VERTICES_SYMBOLIC[11])]
    transition_delta = [texpr_sub(x, y) for x, y in zip(
        VERTICES_SYMBOLIC[3], VERTICES_SYMBOLIC[15])]
    seam_coefficient = symbolic_cross(transition_edge, transition_delta)
    slope = texpr_sub(seam_coefficient[1], seam_coefficient[0])
    inverse_slope = texpr_inv(slope)
    seam_u = texpr_neg(texpr_mul(seam_coefficient[0], inverse_slope))

    d = tpoly_var(0)
    ratio = tpoly_var(1)
    u = tpoly_add(tpoly_const(seam_u), tpoly_scale(inverse_slope, d))
    view = [tpoly_sub(tpoly_const(TEXPR_ONE), u), u,
            tpoly_const(TEXPR_ZERO)]

    def dot_view(vector):
        out = {}
        for coordinate in range(3):
            out = tpoly_add(out,
                tpoly_scale(vector[coordinate], view[coordinate]))
        return out

    def dot_view_poly(vector):
        out = {}
        for coordinate in range(3):
            out = tpoly_add(out,
                tpoly_mul(vector[coordinate], view[coordinate]))
        return out

    assert dot_view(seam_coefficient) == d
    weights = [dot_view(symbolic_cross(edges[1], edges[2])),
               dot_view(symbolic_cross(edges[2], edges[0])),
               dot_view(symbolic_cross(edges[0], edges[1]))]
    z = tpoly_mul(d, ratio)
    z_sq = tpoly_mul(z, z)

    displacement = {}
    contact_values = []
    for weight, edge, support in zip(weights, edges, supports):
        vertex = VERTICES_SYMBOLIC[support]
        # N(0,0,z)q - (1+z^2)q, with the Cayley convention used in Lean.
        delta = [tpoly_add(tpoly_scale(texpr_scale(-2, vertex[0]), z_sq),
                           tpoly_scale(texpr_scale(-2, vertex[1]), z)),
                 tpoly_add(tpoly_scale(texpr_scale(2, vertex[0]), z),
                           tpoly_scale(texpr_scale(-2, vertex[1]), z_sq)),
                 {}]
        contact = [tpoly_sub(tpoly_scale(edge[1], delta[2]),
                             tpoly_scale(edge[2], delta[1])),
                   tpoly_sub(tpoly_scale(edge[2], delta[0]),
                             tpoly_scale(edge[0], delta[2])),
                   tpoly_sub(tpoly_scale(edge[0], delta[1]),
                             tpoly_scale(edge[1], delta[0]))]
        contact_value = dot_view_poly(contact)
        contact_values.append(contact_value)
        displacement = tpoly_add(displacement,
            tpoly_mul(weight, contact_value))

    obstruction = displacement
    assert obstruction
    assert min(power[0] for power in obstruction) >= 2
    quotient = {(d_power-2, t_power): coefficient
                for (d_power, t_power), coefficient in obstruction.items()}
    return {
        "edge_starts": starts,
        "edge_finishes": finishes,
        "support_vertices": supports,
        "support_competitor": competitor,
        "seam_coefficient": seam_coefficient,
        "seam_u": seam_u,
        "weights": weights,
        "contact_values": contact_values,
        "quotient": quotient,
    }


def exact_z_transition_ratio_boxes():
    """Adaptive rational interval cover for the exact z-axis quotient."""
    root_ball = (Q(1839286755214161, 10**15) +
                 Q(1839286755214162, 10**15)) / 2, Q(1, 2*10**15)

    def ball_add(a, b):
        return a[0]+b[0], a[1]+b[1]

    def ball_mul(a, b):
        return (a[0]*b[0], abs(a[0])*b[1] +
                a[1]*abs(b[0]) + a[1]*b[1])

    def ball_scale(q, a):
        return q*a[0], abs(q)*a[1]

    def coefficient_ball(a):
        return ball_add(ball_add((a[0], Q(0)), ball_scale(a[1], root_ball)),
                        ball_scale(a[2], ball_mul(root_ball, root_ball)))

    q = exact_z_transition_quotient()["quotient"]
    coefficients = {power: coefficient_ball(value)
                    for power, value in q.items()}
    seam = ((Q(1, 10**9)+Q(1, 1000))/2,
            (Q(1, 1000)-Q(1, 10**9))/2)

    def quotient_ball(lo, hi):
        ratio = ((lo+hi)/2, (hi-lo)/2)
        seam_sq = ball_mul(seam, seam)
        linear = ball_add(coefficients[(0, 1)],
                          ball_mul(seam, coefficients[(1, 1)]))
        square = ball_add(ball_add(coefficients[(0, 2)],
                                   ball_mul(seam, coefficients[(1, 2)])),
                          ball_mul(seam_sq, coefficients[(2, 2)]))
        return ball_mul(ratio, ball_add(linear, ball_mul(ratio, square)))

    leaves = []

    def visit(lo, hi, depth):
        value = quotient_ball(lo, hi)
        if value[0]-value[1] > 0:
            leaves.append((lo, hi, value[0]-value[1]))
            return
        assert depth < 20
        mid = (lo+hi)/2
        visit(lo, mid, depth+1)
        visit(mid, hi, depth+1)

    visit(Q(2, 5), Q(27, 4), 0)
    return leaves


def exact_transition_blowup_polynomial(starts, finishes, supports,
                                       competitors, outers=None):
    """Exact cleared obstruction in `(d,e,a,b,t)`, with its `d` factor removed.

    `competitors[i]` is a vertex attaining the support defect for contact
    `i` on the intended chart.  Separate linear checks certify that these
    choices dominate every vertex on each generated chart box.
    """
    if outers is None:
        outers = supports
    arity = 5
    d, e, a, b, ratio = [epoly_var(arity, i) for i in range(arity)]
    one = epoly_const(arity, TEXPR_ONE)
    edges = [[texpr_sub(x, y) for x, y in zip(
        VERTICES_SYMBOLIC[start], VERTICES_SYMBOLIC[finish])]
        for start, finish in zip(starts, finishes)]
    transition_edge = [texpr_sub(x, y) for x, y in zip(
        VERTICES_SYMBOLIC[15], VERTICES_SYMBOLIC[11])]
    transition_delta = [texpr_sub(x, y) for x, y in zip(
        VERTICES_SYMBOLIC[3], VERTICES_SYMBOLIC[15])]
    seam_coefficient = symbolic_cross(transition_edge, transition_delta)
    inverse_slope = texpr_inv(
        texpr_sub(seam_coefficient[1], seam_coefficient[0]))
    h = epoly_mul(d, e)
    u_numerator = epoly_sub(
        epoly_sub(d, epoly_scale(seam_coefficient[0],
                                epoly_sub(one, h))),
        epoly_scale(seam_coefficient[2], h))
    u = epoly_scale(inverse_slope, u_numerator)
    view = [epoly_sub(epoly_sub(one, u), h), u, h]

    def dot_view_exact(vector):
        total = {}
        for coordinate in range(3):
            total = epoly_add(total,
                epoly_scale(vector[coordinate], view[coordinate]))
        return total

    weights = [dot_view_exact(symbolic_cross(edges[1], edges[2])),
               dot_view_exact(symbolic_cross(edges[2], edges[0])),
               dot_view_exact(symbolic_cross(edges[0], edges[1]))]
    x = epoly_mul(epoly_mul(d, d), a)
    y = epoly_mul(epoly_mul(d, d), b)
    z = epoly_mul(d, ratio)
    xx, yy, zz = epoly_mul(x, x), epoly_mul(y, y), epoly_mul(z, z)
    xy, xz, yz = epoly_mul(x, y), epoly_mul(x, z), epoly_mul(y, z)
    denominator = epoly_add(epoly_add(epoly_add(one, xx), yy), zz)
    two = (Q(2), Q(0), Q(0))
    minus_two = (Q(-2), Q(0), Q(0))

    def add_terms(*values):
        total = {}
        for value in values:
            total = epoly_add(total, value)
        return total

    obstruction = {}
    support_polynomials = []
    all_support_polynomials = []
    for weight, edge, support, outer, competitor in zip(
            weights, edges, supports, outers, competitors):
        q = VERTICES_SYMBOLIC[support]
        outer_q = VERTICES_SYMBOLIC[outer]
        displacement = [
            add_terms(epoly_scale(texpr_mul(minus_two, q[0]),
                                   epoly_add(yy, zz)),
                      epoly_scale(texpr_mul(two, q[1]),
                                   epoly_sub(xy, z)),
                      epoly_scale(texpr_mul(two, q[2]),
                                   epoly_add(xz, y))),
            add_terms(epoly_scale(texpr_mul(two, q[0]),
                                   epoly_add(xy, z)),
                      epoly_scale(texpr_mul(minus_two, q[1]),
                                   epoly_add(xx, zz)),
                      epoly_scale(texpr_mul(two, q[2]),
                                   epoly_sub(yz, x))),
            add_terms(epoly_scale(texpr_mul(two, q[0]),
                                   epoly_sub(xz, y)),
                      epoly_scale(texpr_mul(two, q[1]),
                                   epoly_add(yz, x)),
                      epoly_scale(texpr_mul(minus_two, q[2]),
                                   epoly_add(xx, yy))),
        ]
        for coordinate in range(3):
            displacement[coordinate] = epoly_add(
                displacement[coordinate],
                epoly_scale(texpr_sub(q[coordinate], outer_q[coordinate]),
                            denominator))
        contact = [epoly_sub(epoly_scale(edge[1], displacement[2]),
                             epoly_scale(edge[2], displacement[1])),
                   epoly_sub(epoly_scale(edge[2], displacement[0]),
                             epoly_scale(edge[0], displacement[2])),
                   epoly_sub(epoly_scale(edge[0], displacement[1]),
                             epoly_scale(edge[1], displacement[0]))]
        contact_value = {}
        for coordinate in range(3):
            contact_value = epoly_add(contact_value,
                epoly_mul(view[coordinate], contact[coordinate]))
        delta = [texpr_sub(x, y) for x, y in zip(
            VERTICES_SYMBOLIC[competitor], outer_q)]
        support_value = dot_view_exact(symbolic_cross(edge, delta))
        support_polynomials.append(support_value)
        all_support_polynomials.append([
            dot_view_exact(symbolic_cross(edge, [
                texpr_sub(x, y) for x, y in
                zip(VERTICES_SYMBOLIC[vertex], outer_q)]))
            for vertex in range(24)])
        cleared_margin = epoly_sub(
            contact_value, epoly_mul(denominator, support_value))
        obstruction = epoly_add(obstruction,
                                epoly_mul(weight, cleared_margin))
    minimum_d_power = min(power[0] for power in obstruction)
    if minimum_d_power < 1:
        raise RuntimeError("transition obstruction has no seam factor")
    quotient = {(d_power-minimum_d_power,
                 e_power, a_power, b_power, t_power): coefficient
                for (d_power, e_power, a_power, b_power, t_power), coefficient
                in obstruction.items()}
    support_quotients = []
    for i, row in enumerate(all_support_polynomials):
        quotient_row = []
        for value in row:
            working = epoly_sub(support_polynomials[i], value)
            for coordinate in range(2):
                if (working and
                        min(power[coordinate] for power in working) >= 1):
                    working = {
                        power[:coordinate] + (power[coordinate]-1,) +
                        power[coordinate+1:]: coefficient
                        for power, coefficient in working.items()
                    }
            quotient_row.append(working)
        support_quotients.append(quotient_row)
    return {"quotient": quotient, "weights": weights,
            "support_polynomials": support_polynomials,
            "all_support_polynomials": all_support_polynomials,
            "support_quotients": support_quotients,
            "minimum_d_power": minimum_d_power}


TRIBONACCI_BALL = (
    (Q(1839286755214161, 10**15) +
     Q(1839286755214162, 10**15)) / 2,
    Q(1, 2 * 10**15),
)


def texpr_ball(value):
    """Mirror ``TribonacciExpr.evalBall`` exactly."""
    root_sq = ball_mul(TRIBONACCI_BALL, TRIBONACCI_BALL)
    return ball_add(
        ball_add(ball_const(value[0]),
                 ball_scale(value[1], TRIBONACCI_BALL)),
        ball_scale(value[2], root_sq))


def ball_pow(value, power):
    answer = ball_const(1)
    for _ in range(power):
        answer = ball_mul(answer, value)
    return answer


def epoly_ball(polynomial, variables):
    """Mirror the canonical sparse Lean evaluator exactly."""
    total = ball_const(0)
    for powers in sorted(polynomial):
        monomial = ball_const(1)
        for variable, power in zip(variables, powers):
            monomial = ball_mul(monomial, ball_pow(variable, power))
        total = ball_add(total, ball_mul(
            texpr_ball(polynomial[powers]), monomial))
    return total


def epoly_pow(value, power):
    answer = epoly_const(5, TEXPR_ONE)
    for _ in range(power):
        answer = epoly_mul(answer, value)
    return answer


def epoly_recenter(polynomial, variables):
    """Exactly substitute `xᵢ = centerᵢ + radiusᵢ*yᵢ`."""
    answer = {}
    for powers, coefficient in polynomial.items():
        for new_powers in itertools.product(
                *(range(power + 1) for power in powers)):
            scalar = Q(1)
            for power, new_power, (center, radius) in zip(
                    powers, new_powers, variables):
                scalar *= (Q(math.comb(power, new_power)) *
                           center ** (power-new_power) *
                           radius ** new_power)
            if scalar == 0:
                continue
            value = texpr_scale(scalar, coefficient)
            answer[new_powers] = texpr_add(
                answer.get(new_powers, TEXPR_ZERO), value)
            if answer[new_powers] == TEXPR_ZERO:
                del answer[new_powers]
    return answer


def epoly_centered_ball(polynomial, variables):
    centered = epoly_recenter(polynomial, variables)
    unit_variables = [(Q(0), Q(1)) for _ in variables]
    return epoly_ball(centered, unit_variables)


TRIBONACCI_FLOAT = 1.8392867552141612


def texpr_float(value):
    return (float(value[0]) + float(value[1]) * TRIBONACCI_FLOAT +
            float(value[2]) * TRIBONACCI_FLOAT**2)


def epoly_float_value(polynomial, values):
    return sum(texpr_float(coefficient) * math.prod(
        value ** power for value, power in zip(values, powers))
        for powers, coefficient in polynomial.items())


def epoly_centered_float_lower(polynomial, endpoints):
    """Fast heuristic mirror of recentered interval evaluation.

    This is used only to choose a split coordinate; accepted leaves are
    always rechecked by exact rational arithmetic.
    """
    centered = {}
    variables = [(float((lo+hi)/2), float((hi-lo)/2))
                 for lo, hi in endpoints]
    for powers, coefficient in polynomial.items():
        coefficient = texpr_float(coefficient)
        for new_powers in itertools.product(
                *(range(power + 1) for power in powers)):
            scalar = coefficient
            for power, new_power, (center, radius) in zip(
                    powers, new_powers, variables):
                scalar *= (math.comb(power, new_power) *
                           center ** (power-new_power) *
                           radius ** new_power)
            centered[new_powers] = centered.get(new_powers, 0.0) + scalar
    zero = (0,) * len(endpoints)
    return centered.get(zero, 0.0) - sum(
        abs(value) for powers, value in centered.items() if powers != zero)


def epoly_compose(polynomial, substitutions):
    """Exactly compose a sparse polynomial with sparse substitutions."""
    answer = {}
    for powers, coefficient in polynomial.items():
        term = epoly_const(len(substitutions), coefficient)
        for power, substitution in zip(powers, substitutions):
            term = epoly_mul(term, epoly_pow(substitution, power))
        answer = epoly_add(answer, term)
    return answer


def epoly_leading_and_tail(polynomial):
    """Write `polynomial = leading + d * tail` in coordinate zero."""
    leading = {powers: coefficient for powers, coefficient in
               polynomial.items() if powers[0] == 0}
    tail = {(powers[0]-1,) + powers[1:]: coefficient
            for powers, coefficient in polynomial.items()
            if powers[0] > 0}
    return leading, tail


def epoly_bernstein_coefficients(polynomial, endpoints, degrees=None):
    """Exact tensor Bernstein coefficients on a rational box."""
    power_basis = epoly_recenter(
        polynomial, [(lo, hi-lo) for lo, hi in endpoints])
    natural_degrees = ((0,) * len(endpoints) if not power_basis else
        tuple(max(powers[i] for powers in power_basis)
              for i in range(len(endpoints))))
    if degrees is None:
        degrees = natural_degrees
    else:
        degrees = tuple(degrees)
        if any(actual > requested for actual, requested in
               zip(natural_degrees, degrees)):
            raise ValueError("requested Bernstein degree is too small")
    answer = {index: TEXPR_ZERO for index in
              itertools.product(*(range(d+1) for d in degrees))}
    for powers, coefficient in power_basis.items():
        for index in itertools.product(*(
                range(power, degree+1)
                for power, degree in zip(powers, degrees))):
            scalar = Q(1)
            for i, power, degree in zip(index, powers, degrees):
                scalar *= Q(math.comb(i, power), math.comb(degree, power))
            answer[index] = texpr_add(answer[index],
                                      texpr_scale(scalar, coefficient))
    return degrees, answer


def bernstein_lower(coefficients):
    return min(center-radius for center, radius in
               map(texpr_ball, coefficients.values()))


def bernstein_split(coefficients, degrees, axis):
    """Exact midpoint de Casteljau split along one tensor coordinate."""
    groups = {}
    for index, coefficient in coefficients.items():
        key = index[:axis] + index[axis+1:]
        groups.setdefault(key, [None] * (degrees[axis]+1))[index[axis]] = \
            coefficient
    left, right = {}, {}
    for key, row in groups.items():
        levels = [row]
        while len(levels[-1]) > 1:
            levels.append([texpr_scale(Q(1, 2), texpr_add(a, b))
                           for a, b in zip(levels[-1], levels[-1][1:])])
        left_row = [levels[i][0] for i in range(len(row))]
        right_row = [levels[len(row)-1-i][i]
                     for i in range(len(row))]
        for i, coefficient in enumerate(left_row):
            index = key[:axis] + (i,) + key[axis:]
            left[index] = coefficient
        for i, coefficient in enumerate(right_row):
            index = key[:axis] + (i,) + key[axis:]
            right[index] = coefficient
    return left, right


def bernstein_float_table(coefficients):
    """Numerical shadow used only to choose a subdivision coordinate."""
    return {index: texpr_float(coefficient)
            for index, coefficient in coefficients.items()}


def bernstein_split_float(coefficients, degrees, axis):
    """Fast floating de Casteljau split; never used to accept a leaf."""
    groups = {}
    for index, coefficient in coefficients.items():
        key = index[:axis] + index[axis+1:]
        groups.setdefault(key, [None] * (degrees[axis]+1))[index[axis]] = \
            coefficient
    left, right = {}, {}
    for key, row in groups.items():
        levels = [row]
        while len(levels[-1]) > 1:
            levels.append([(a+b)/2 for a, b in
                           zip(levels[-1], levels[-1][1:])])
        left_row = [levels[i][0] for i in range(len(row))]
        right_row = [levels[len(row)-1-i][i]
                     for i in range(len(row))]
        for i, coefficient in enumerate(left_row):
            index = key[:axis] + (i,) + key[axis:]
            left[index] = coefficient
        for i, coefficient in enumerate(right_row):
            index = key[:axis] + (i,) + key[axis:]
            right[index] = coefficient
    return left, right


def transition_blowup_families_exact():
    specifications = [
        ([8, 15, 10], [9, 11, 14], [1, 11, 10], [1, 3, 2],
         [1, 11, 10]),
        ([5, 10, 8], [15, 14, 9], [15, 10, 1], [15, 2, 1],
         [15, 10, 1]),
        ([14, 8, 5], [4, 9, 15], [14, 1, 15], [14, 1, 15],
         [14, 1, 15]),
        ([1, 5, 2], [9, 15, 14], [9, 15, 14], [1, 5, 2],
         [1, 5, 2]),
        # A translated-support Farkas certificate for the nested
        # `e = O(d)` transition missed by the axis-local family bank.
        ([14, 8, 15], [4, 1, 3], [14, 8, 15], [4, 1, 3],
         [4, 1, 3]),
        # A two-contact width certificate.  The first two edges are exact
        # opposites, so their weights agree and the third weight vanishes.
        ([1, 0, 4], [0, 1, 2], [11, 0, 5], [2, 0, 5],
         [2, 0, 5]),
    ]
    return [exact_transition_blowup_polynomial(*specification)
            for specification in specifications]


def transition_guarded_leading_certificate():
    """Exact low-degree certificate on the `L89 <= 3/100` branch.

    The guard region is parameterized by `(d,e,u,a,b)`, with `u` moving
    between the family-89 guard boundary and the original lower bound
    `t = 3/5`.  The returned soft maximum is

        (5 + L_transverse)^3 * L_transverse
          + (5 + L_nested)^3 * L_nested.

    Its weights are nonnegative wherever both `5 + L` terms are
    nonnegative, so positivity proves that one leading obstruction is
    positive.  Finite-seam remainder bounds are handled separately.
    """
    families = transition_blowup_families_exact()
    variables = [epoly_var(5, i) for i in range(5)]
    leading89, _ = epoly_leading_and_tail(families[1]["quotient"])
    constant = leading89[(0, 0, 0, 0, 0)]
    tangential = leading89[(0, 1, 0, 0, 0)]
    rotation = leading89[(0, 0, 0, 0, 1)]
    guard = (Q(3, 100), Q(0), Q(0))
    lower_t = (Q(3, 5), Q(0), Q(0))
    inverse_rotation = texpr_inv(rotation)
    slack_at_lower_t = texpr_sub(
        texpr_sub(guard, constant), texpr_mul(rotation, lower_t))
    maximum_slack = epoly_sub(
        epoly_const(5, slack_at_lower_t),
        epoly_scale(tangential, variables[1]))
    slack = epoly_mul(variables[2], maximum_slack)
    t_numerator = epoly_sub(
        epoly_sub(epoly_const(5, texpr_sub(guard, constant)),
                  epoly_scale(tangential, variables[1])),
        slack)
    t = epoly_scale(inverse_rotation, t_numerator)
    substitutions = [variables[0], variables[1], variables[3],
                     variables[4], t]
    leading = []
    tails = []
    for family_index in (3, 4):
        family_leading, family_tail = epoly_leading_and_tail(
            families[family_index]["quotient"])
        leading.append(epoly_compose(family_leading, substitutions))
        tails.append(epoly_compose(family_tail, substitutions))
    five = (Q(5), Q(0), Q(0))
    weights = [epoly_pow(epoly_add(value, epoly_const(5, five)), 3)
               for value in leading]
    soft_maximum = epoly_add(
        epoly_mul(weights[0], leading[0]),
        epoly_mul(weights[1], leading[1]))
    return {
        "guard": guard,
        "leading89": leading89,
        "parameter_t": t,
        "leading": leading,
        "tails": tails,
        "weights": weights,
        "soft_maximum": soft_maximum,
    }


def transition_guarded_bernstein_cover(max_nodes=5000, max_depth=100,
                                       threshold=Q(0)):
    """Exact Bernstein cover of the guarded leading soft maximum."""
    certificate = transition_guarded_leading_certificate()
    root = [(Q(0), Q(0)), (Q(0), Q(2)), (Q(0), Q(1)),
            (Q(-16), Q(16)), (Q(-16), Q(16))]
    degrees, coefficients = epoly_bernstein_coefficients(
        certificate["soft_maximum"], root)
    leaves = []
    failures = []
    node_count = 0
    truncated = False

    class NodeLimit(Exception):
        pass

    def visit(table, float_table, endpoints, depth):
        nonlocal node_count
        if node_count >= max_nodes:
            raise NodeLimit
        node_count += 1
        lower = bernstein_lower(table)
        if lower > threshold:
            leaves.append({"endpoints": endpoints, "lower": lower})
            return
        if depth >= max_depth:
            failures.append({"endpoints": endpoints, "lower": lower})
            return
        candidates = []
        for axis in range(5):
            if degrees[axis] == 0:
                continue
            children = bernstein_split_float(float_table, degrees, axis)
            lowers = [min(child.values()) for child in children]
            score = (sum(lower > threshold for lower in lowers),
                     min(lowers), sum(lowers))
            candidates.append((score, axis, children))
        _, axis, float_children = max(candidates, key=lambda item: item[0])
        children = bernstein_split(table, degrees, axis)
        lo, hi = endpoints[axis]
        mid = (lo + hi) / 2
        child_endpoints = []
        for child_range in ((lo, mid), (mid, hi)):
            child = list(endpoints)
            child[axis] = child_range
            child_endpoints.append(child)
        for child, float_child, child_box in zip(
                children, float_children, child_endpoints):
            visit(child, float_child, child_box, depth+1)

    try:
        visit(coefficients, bernstein_float_table(coefficients), root, 0)
    except NodeLimit:
        truncated = True
    return {
        "root": root,
        "degrees": degrees,
        "coefficient_count": len(coefficients),
        "root_lower": bernstein_lower(coefficients),
        "threshold": threshold,
        "node_count": node_count,
        "truncated": truncated,
        "leaves": leaves,
        "failures": failures,
    }


def transition_guarded_family_polynomials():
    """The three exact obstruction quotients used on the guarded branch.

    Unlike the experimental soft maximum, this retains family 89 on both
    sides of its guard and permits each subdivision leaf to select whichever
    of family 89, transverse, or nested has a positive quotient.
    """
    certificate = transition_guarded_leading_certificate()
    families = transition_blowup_families_exact()
    variables = [epoly_var(5, i) for i in range(5)]
    substitutions = [variables[0], variables[1], variables[3],
                     variables[4], certificate["parameter_t"]]
    family_indices = (1, 3, 4)
    return {
        "family_indices": family_indices,
        "parameter_t": certificate["parameter_t"],
        "quotients": [epoly_compose(families[i]["quotient"], substitutions)
                      for i in family_indices],
    }


def transition_guarded_piece_polynomials():
    """Exact three-piece replacement for the failed soft maximum."""
    families = transition_blowup_families_exact()
    variables = [epoly_var(5, i) for i in range(5)]
    leading89, _ = epoly_leading_and_tail(families[1]["quotient"])
    constant = leading89[(0, 0, 0, 0, 0)]
    tangential = leading89[(0, 1, 0, 0, 0)]
    rotation = leading89[(0, 0, 0, 0, 1)]
    upper_split = (Q(3, 125), Q(0), Q(0))
    lower_split = (Q(3, 100), Q(0), Q(0))
    lower_t = (Q(3, 5), Q(0), Q(0))
    maximum_slack_constant = texpr_sub(
        texpr_sub(lower_split, constant), texpr_mul(rotation, lower_t))
    maximum_slack = epoly_sub(
        epoly_const(5, maximum_slack_constant),
        epoly_scale(tangential, variables[1]))

    def substitutions(slack):
        numerator = epoly_sub(
            epoly_sub(epoly_const(5, texpr_sub(lower_split, constant)),
                      epoly_scale(tangential, variables[1])), slack)
        t = epoly_scale(texpr_inv(rotation), numerator)
        return [variables[0], variables[1], variables[3], variables[4], t]

    upper_slack = epoly_mul(variables[2],
                            epoly_const(5, upper_split))
    middle_slack = epoly_add(
        epoly_const(5, upper_split),
        epoly_mul(variables[2], epoly_const(
            5, texpr_sub(lower_split, upper_split))))
    lower_slack = epoly_add(
        epoly_const(5, lower_split),
        epoly_mul(variables[2], epoly_sub(
            maximum_slack, epoly_const(5, lower_split))))
    substitutions_by_piece = {
        "upper": substitutions(upper_slack),
        "middle": substitutions(middle_slack),
        "lower": substitutions(lower_slack),
    }

    def quotient(family_index, piece):
        return epoly_compose(families[family_index]["quotient"],
                             substitutions_by_piece[piece])

    middle_transverse = quotient(3, "middle")
    middle_nested = quotient(4, "middle")
    lower_transverse = quotient(3, "lower")
    lower_nested = quotient(4, "lower")
    leading_transverse, _ = epoly_leading_and_tail(middle_transverse)
    leading_nested, _ = epoly_leading_and_tail(middle_nested)
    transverse_weight = next(
        coefficient for powers, coefficient in leading_nested.items()
        if powers == (0, 0, 0, 1, 0))
    nested_weight = texpr_neg(next(
        coefficient for powers, coefficient in leading_transverse.items()
        if powers == (0, 0, 0, 1, 0)))

    def combination(transverse, nested):
        return epoly_add(epoly_scale(transverse_weight, transverse),
                         epoly_scale(nested_weight, nested))

    return {
        "upper_split": upper_split,
        "lower_split": lower_split,
        "maximum_slack": maximum_slack,
        "parameter_t": {piece: values[4] for piece, values in
                        substitutions_by_piece.items()},
        "transverse_weight": transverse_weight,
        "nested_weight": nested_weight,
        "upper89": quotient(1, "upper"),
        "middle89": quotient(1, "middle"),
        "middleTransverse": middle_transverse,
        "middleNested": middle_nested,
        "middleWidth": quotient(5, "middle"),
        "middleCombination": combination(
            middle_transverse, middle_nested),
        "lowerCombination": combination(
            lower_transverse, lower_nested),
    }


def transition_guarded_middle_chart(chart):
    """Polynomials and box for one exact chart of the middle band."""
    certificate = transition_guarded_piece_polynomials()
    polynomials = [certificate["middle89"],
                   certificate["middleTransverse"],
                   certificate["middleNested"],
                   certificate["middleWidth"],
                   certificate["middleCombination"]]
    labels = ["family89", "familyTransverse", "familyNested", "familyWidth",
              "transverseNestedCombination"]
    if chart == "iterated":
        # Resolve the only noncompact-looking polar corner a second time.
        # With R = 500 rho and s = 1-u, the triangle R+s <= 1 is
        # parameterized by R = sigma*q and s = sigma*(1-q).  Thus the
        # collapsed corner rho=0,u=1 is an honest coordinate face instead
        # of the limit of an infinite dyadic chain.
        variables = [epoly_var(5, i) for i in range(5)]
        one = epoly_const(5, TEXPR_ONE)
        radial_scale = epoly_const(5, (Q(1, 500), Q(0), Q(0)))
        rho = epoly_mul(radial_scale,
                        epoly_mul(variables[0], variables[1]))
        substitutions = [
            epoly_mul(rho, variables[2]),
            epoly_mul(rho, epoly_sub(one, variables[2])),
            epoly_sub(one, epoly_mul(
                variables[0], epoly_sub(one, variables[1]))),
            variables[3], variables[4],
        ]
        polynomials = [epoly_compose(polynomial, substitutions)
                       for polynomial in polynomials]
        root = [(Q(0), Q(1)), (Q(0), Q(1)), (Q(0), Q(1)),
                (Q(-16), Q(16)), (Q(-16), Q(16))]
    elif chart == "polar":
        variables = [epoly_var(5, i) for i in range(5)]
        one = epoly_const(5, TEXPR_ONE)
        substitutions = [epoly_mul(variables[0], variables[1]),
            epoly_mul(variables[0], epoly_sub(one, variables[1])),
            variables[2], variables[3], variables[4]]
        polynomials = [epoly_compose(polynomial, substitutions)
                       for polynomial in polynomials]
        root = [(Q(0), Q(1, 500)), (Q(0), Q(1)), (Q(0), Q(1)),
                (Q(-16), Q(16)), (Q(-16), Q(16))]
    elif chart == "rectangular":
        root = [(Q(0), Q(1, 1000)), (Q(0), Q(2)), (Q(0), Q(1)),
                (Q(-16), Q(16)), (Q(-16), Q(16))]
    else:
        raise ValueError(f"unknown middle chart: {chart}")
    return labels, polynomials, root


def transition_guarded_middle_profile(chart, samples=100000, seed=1):
    """Cheap pointwise search for a genuine gap before box subdivision."""
    labels, polynomials, root = transition_guarded_middle_chart(chart)
    rng = random.Random(seed)
    best_value = math.inf
    best_point = None
    best_values = None
    label_counts = [0] * len(labels)

    def inspect(point):
        nonlocal best_value, best_point, best_values
        values = [epoly_float_value(polynomial, point)
                  for polynomial in polynomials]
        label = max(range(len(values)), key=values.__getitem__)
        label_counts[label] += 1
        if values[label] < best_value:
            best_value = values[label]
            best_point = point
            best_values = values

    # Include every corner and the most important collapsed-coordinate
    # faces, then use random interior points to hunt for an actual negative
    # soft maximum.  This is discovery only; no point sample is a proof.
    for bits in itertools.product((0, 1), repeat=5):
        inspect([float(root[i][bits[i]]) for i in range(5)])
    for _ in range(samples):
        inspect([rng.uniform(float(lo), float(hi)) for lo, hi in root])
    return {
        "chart": chart,
        "samples": samples + 32,
        "minimum_envelope": best_value,
        "minimum_point": best_point,
        "values_at_minimum": dict(zip(labels, best_values)),
        "label_counts": dict(zip(labels, label_counts)),
    }


def project_probability_simplex(values):
    """Euclidean projection onto nonnegative vectors with sum one."""
    ordered = sorted(values, reverse=True)
    partial = 0.0
    threshold = 0.0
    for index, value in enumerate(ordered, 1):
        partial += value
        candidate = (partial - 1.0) / index
        if index == len(ordered) or ordered[index] <= candidate:
            threshold = candidate
            break
    return [max(value - threshold, 0.0) for value in values]


def transition_guarded_middle_combination_profile(
        chart="iterated", iterations=5000):
    """Heuristically maximize the worst Bernstein coefficient of one OR.

    A successful positive result can be rationalized and checked exactly;
    a negative result only says that fixed scalar weights are insufficient.
    """
    labels, polynomials, root = transition_guarded_middle_chart(chart)
    natural = [epoly_bernstein_coefficients(polynomial, root)[0]
               for polynomial in polynomials]
    degrees = tuple(max(row[axis] for row in natural)
                    for axis in range(5))
    tables = [epoly_bernstein_coefficients(
        polynomial, root, degrees)[1] for polynomial in polynomials]
    columns = [[texpr_float(value) for value in table.values()]
               for table in tables]
    scales = [max(abs(value) for value in column) for column in columns]
    rows = list(zip(*[[value / scale for value in column]
                      for column, scale in zip(columns, scales)]))
    weights = [1.0 / len(labels)] * len(labels)
    best = (-math.inf, None, None)
    for iteration in range(1, iterations + 1):
        worst_index, (worst, gradient) = min(enumerate(
            (sum(weight * value for weight, value in zip(weights, row)), row)
            for row in rows), key=lambda item: item[1][0])
        if worst > best[0]:
            best = (worst, list(weights), worst_index)
        norm = math.sqrt(sum(value * value for value in gradient))
        step = 0.5 / math.sqrt(iteration)
        weights = project_probability_simplex([
            weight + step * value / norm
            for weight, value in zip(weights, gradient)])
    physical_weights = [weight / scale
                        for weight, scale in zip(best[1], scales)]
    normalization = sum(physical_weights)
    physical_weights = [weight / normalization for weight in physical_weights]
    return {
        "chart": chart,
        "degrees": degrees,
        "coefficient_count": len(rows),
        "iterations": iterations,
        "normalized_worst_coefficient": best[0],
        "weights": dict(zip(labels, physical_weights)),
        "worst_index": list(tables[0])[best[2]],
        "worst_physical_coefficient": sum(
            weight * columns[i][best[2]]
            for i, weight in enumerate(physical_weights)),
    }


def transition_guarded_middle_float_cover(
        chart="iterated", max_nodes=10000, max_depth=80,
        acceptance_tolerance=1e-12):
    """Discover a subdivision using floating de Casteljau arithmetic only."""
    labels, polynomials, root = transition_guarded_middle_chart(chart)
    root_tables = [epoly_bernstein_coefficients(polynomial, root)
                   for polynomial in polynomials]
    degrees = [item[0] for item in root_tables]
    root_float = [bernstein_float_table(item[1]) for item in root_tables]
    leaves = []
    failures = []
    node_count = 0
    maximum_depth = 0
    split_axis_counts = [0] * 5

    class NodeLimit(Exception):
        pass

    def visit(tables, endpoints, depth, path):
        nonlocal node_count, maximum_depth
        if node_count >= max_nodes:
            raise NodeLimit
        node_count += 1
        maximum_depth = max(maximum_depth, depth)
        lowers = [min(table.values()) for table in tables]
        label = max(range(len(labels)), key=lowers.__getitem__)
        if lowers[label] >= -acceptance_tolerance:
            leaves.append((path, label, lowers[label]))
            return
        if depth >= max_depth:
            failures.append((path, lowers))
            return

        # Score coordinates using only the currently strongest family, then
        # split the other tables once along the selected coordinate.  The
        # older exact search split every family on every candidate axis and
        # obscured the geometry under avoidable arithmetic cost.
        candidates = []
        for axis in range(5):
            children = bernstein_split_float(tables[label], degrees[label], axis)
            child_lowers = [min(child.values()) for child in children]
            score = (sum(value >= -acceptance_tolerance
                         for value in child_lowers),
                     min(child_lowers), sum(child_lowers))
            candidates.append((score, axis))
        _, axis = max(candidates)
        split_axis_counts[axis] += 1
        split_tables = [bernstein_split_float(table, degree, axis)
                        for table, degree in zip(tables, degrees)]
        lo, hi = endpoints[axis]
        mid = (lo + hi) / 2
        for side, child_range in enumerate(((lo, mid), (mid, hi))):
            child_endpoints = list(endpoints)
            child_endpoints[axis] = child_range
            visit([children[side] for children in split_tables],
                  child_endpoints, depth + 1, path + [(axis, side)])

    truncated = False
    try:
        visit(root_float, root, 0, [])
    except NodeLimit:
        truncated = True
    return {
        "chart": chart,
        "degrees": degrees,
        "node_count": node_count,
        "maximum_depth": maximum_depth,
        "split_axis_counts": split_axis_counts,
        "truncated": truncated,
        "leaf_count": len(leaves),
        "failure_count": len(failures),
        "label_leaf_counts": {
            labels[i]: sum(label == i for _, label, _ in leaves)
            for i in range(len(labels))
        },
        "minimum_leaf_lower": min((lower for _, _, lower in leaves),
                                  default=None),
        "failure_examples": failures[:3],
        "leaves": leaves,
    }


def transition_guarded_middle_cover(max_nodes=5000, max_depth=100,
                                     polar=False, iterated=False):
    """Exact nonnegative OR-cover of the narrow overlap piece."""
    chart = "iterated" if iterated else "polar" if polar else "rectangular"
    labels, polynomials, root = transition_guarded_middle_chart(chart)
    root_tables = [epoly_bernstein_coefficients(polynomial, root)
                   for polynomial in polynomials]
    degrees = [item[0] for item in root_tables]
    tables = [item[1] for item in root_tables]
    float_tables = [bernstein_float_table(table) for table in tables]
    leaves = []
    failures = []
    node_count = 0
    maximum_depth = 0
    split_axis_counts = [0] * 5
    label_leaf_counts = [0] * len(labels)
    truncated = False

    class NodeLimit(Exception):
        pass

    def visit(current, current_float, endpoints, depth, path):
        nonlocal node_count, maximum_depth
        if node_count >= max_nodes:
            raise NodeLimit
        node_count += 1
        maximum_depth = max(maximum_depth, depth)
        lowers = [bernstein_lower(table) for table in current]
        label = max(range(len(lowers)), key=lowers.__getitem__)
        if lowers[label] >= 0:
            label_leaf_counts[label] += 1
            leaves.append({"path": path, "endpoints": endpoints,
                           "label": labels[label], "lower": lowers[label]})
            return
        if depth >= max_depth:
            failures.append({"path": path, "endpoints": endpoints,
                             "lowers": lowers})
            return
        candidates = []
        path_axis_counts = [sum(split_axis == axis
                                for split_axis, _ in path)
                            for axis in range(5)]
        for axis in range(5):
            split_labels = [bernstein_split_float(table, degree, axis)
                            for table, degree in zip(current_float, degrees)]
            child_envelopes = [max(min(split_labels[label][side].values())
                                   for label in range(len(labels)))
                               for side in range(2)]
            score = (sum(lower >= 0 for lower in child_envelopes),
                     -path_axis_counts[axis],
                     min(child_envelopes), sum(child_envelopes))
            candidates.append((score, axis, split_labels))
        _, axis, split_float = max(candidates, key=lambda item: item[0])
        split_axis_counts[axis] += 1
        split_exact = [bernstein_split(table, degree, axis)
                       for table, degree in zip(current, degrees)]
        lo, hi = endpoints[axis]
        mid = (lo + hi) / 2
        for side, child_range in enumerate(((lo, mid), (mid, hi))):
            child_endpoints = list(endpoints)
            child_endpoints[axis] = child_range
            visit([label[side] for label in split_exact],
                  [label[side] for label in split_float],
                  child_endpoints, depth+1, path + [(axis, side)])

    try:
        visit(tables, float_tables, root, 0, [])
    except NodeLimit:
        truncated = True
    return {
        "root": root,
        "labels": labels,
        "chart": chart,
        "degrees": degrees,
        "coefficient_counts": [len(table) for table in tables],
        "root_lowers": [bernstein_lower(table) for table in tables],
        "node_count": node_count,
        "maximum_depth": maximum_depth,
        "split_axis_counts": split_axis_counts,
        "label_leaf_counts": label_leaf_counts,
        "truncated": truncated,
        "leaves": leaves,
        "failures": failures,
    }


def transition_guarded_family_cover(max_nodes=5000, max_depth=100,
                                     threshold=Q(0)):
    """Exact adaptive OR-cover by three full finite-seam quotients."""
    certificate = transition_guarded_family_polynomials()
    root = [(Q(0), Q(1, 1000)), (Q(0), Q(2)), (Q(0), Q(1)),
            (Q(-16), Q(16)), (Q(-16), Q(16))]
    root_tables = [epoly_bernstein_coefficients(polynomial, root)
                   for polynomial in certificate["quotients"]]
    degrees = [item[0] for item in root_tables]
    coefficients = [item[1] for item in root_tables]
    float_coefficients = [bernstein_float_table(table)
                          for table in coefficients]
    leaves = []
    failures = []
    node_count = 0
    maximum_depth = 0
    split_axis_counts = [0] * 5
    family_leaf_counts = [0] * len(coefficients)
    truncated = False

    class NodeLimit(Exception):
        pass

    def visit(tables, float_tables, endpoints, depth, path):
        nonlocal node_count, maximum_depth
        if node_count >= max_nodes:
            raise NodeLimit
        node_count += 1
        maximum_depth = max(maximum_depth, depth)
        lowers = [bernstein_lower(table) for table in tables]
        family = max(range(len(lowers)), key=lowers.__getitem__)
        if lowers[family] > threshold:
            family_leaf_counts[family] += 1
            leaves.append({"path": path, "endpoints": endpoints,
                           "family": certificate["family_indices"][family],
                           "lower": lowers[family]})
            return
        if depth >= max_depth:
            failures.append({"path": path, "endpoints": endpoints,
                             "lowers": lowers})
            return
        candidates = []
        for axis in range(5):
            if all(family_degrees[axis] == 0
                   for family_degrees in degrees):
                continue
            split_families = [bernstein_split_float(
                table, family_degrees, axis)
                for table, family_degrees in zip(float_tables, degrees)]
            child_envelopes = [max(min(split_families[family][side].values())
                                   for family in range(len(tables)))
                               for side in range(2)]
            score = (sum(lower > float(threshold)
                         for lower in child_envelopes),
                     min(child_envelopes), sum(child_envelopes))
            candidates.append((score, axis, split_families))
        _, axis, split_float_families = max(
            candidates, key=lambda item: item[0])
        split_axis_counts[axis] += 1
        split_families = [bernstein_split(table, family_degrees, axis)
                          for table, family_degrees in zip(tables, degrees)]
        lo, hi = endpoints[axis]
        mid = (lo + hi) / 2
        for side, child_range in enumerate(((lo, mid), (mid, hi))):
            child_endpoints = list(endpoints)
            child_endpoints[axis] = child_range
            visit([family[side] for family in split_families],
                  [family[side] for family in split_float_families],
                  child_endpoints, depth+1, path + [(axis, side)])

    try:
        visit(coefficients, float_coefficients, root, 0, [])
    except NodeLimit:
        truncated = True
    return {
        "root": root,
        "family_indices": certificate["family_indices"],
        "degrees": degrees,
        "coefficient_counts": [len(table) for table in coefficients],
        "root_lowers": [bernstein_lower(table) for table in coefficients],
        "threshold": threshold,
        "node_count": node_count,
        "maximum_depth": maximum_depth,
        "split_axis_counts": split_axis_counts,
        "family_leaf_counts": family_leaf_counts,
        "truncated": truncated,
        "leaves": leaves,
        "failures": failures,
    }


def transition_box_base_diagnostics(family, endpoints):
    variables = [((lo + hi) / 2, (hi - lo) / 2)
                 for lo, hi in endpoints]
    weight_balls = [epoly_ball(value, variables)
                    for value in family["weights"]]
    support_slacks = []
    worst_support = None
    for i, row in enumerate(family["support_quotients"]):
        for vertex, quotient in enumerate(row):
            difference_ball = epoly_ball(quotient, variables)
            slack = difference_ball[0] - difference_ball[1]
            support_slacks.append(slack)
            if worst_support is None or slack < worst_support[0]:
                worst_support = (slack, i, vertex)
    return {
        "valid": (endpoints[0][0] >= 0 and endpoints[1][0] >= 0 and
                  min(center-radius for center, radius in weight_balls) > 0 and
                  min(support_slacks) >= 0),
        "weight_lowers": [center-radius for center, radius in weight_balls],
        "worst_support": worst_support,
    }


def transition_box_diagnostics(family, endpoints, base=None):
    variables = [((lo + hi) / 2, (hi - lo) / 2)
                 for lo, hi in endpoints]
    if base is None:
        base = transition_box_base_diagnostics(family, endpoints)
    quotient = epoly_centered_ball(family["quotient"], variables)
    quotient_lower = quotient[0] - quotient[1]
    return {**base, "valid": base["valid"] and quotient_lower > 0,
            "quotient_lower": quotient_lower}


def transition_box_probe():
    endpoints = [
        (Q(1, 10**9), Q(1, 1000)),
        (Q(0), Q(2)),
        (Q(-16), Q(16)),
        (Q(-16), Q(16)),
        (Q(3, 5), Q(10)),
    ]
    return {
        "endpoints": endpoints,
        "families": [transition_box_diagnostics(family, endpoints)
                     for family in transition_blowup_families_exact()],
    }


def transition_box_cover(max_nodes=20000, max_depth=100):
    """Adaptively cover a representative hard transition band exactly.

    Every accepted leaf is checked with exact rational centered-form bounds.
    Floating-point bounds only choose which coordinate to bisect next.
    """
    families = transition_blowup_families_exact()
    nested_family_index = 4
    root = [
        (Q(1, 10**9), Q(1, 1000)),
        (Q(0), Q(2)),
        (Q(-16), Q(16)),
        (Q(-16), Q(16)),
        (Q(3, 5), Q(10)),
    ]
    leaves = []
    failures = []
    node_count = 0
    max_depth_seen = 0
    truncated = False
    base_cache = {}

    class NodeLimit(Exception):
        pass

    def evaluate(endpoints):
        answer = []
        # Prefer the translated-support families: around the difficult
        # family-89/family-192 switch they have substantially larger margins
        # and therefore certify broader boxes.
        for family_index in (nested_family_index, 3, 1, 2, 0):
            family = families[family_index]
            key = (family_index, endpoints[0], endpoints[1])
            if key not in base_cache:
                base_cache[key] = transition_box_base_diagnostics(
                    family, endpoints)
            answer.append({**transition_box_diagnostics(
                family, endpoints, base_cache[key]),
                "certificate_index": family_index})
            if answer[-1]["valid"]:
                return answer
        return answer

    def visit(endpoints, depth, diagnostics=None):
        nonlocal node_count, max_depth_seen
        if node_count >= max_nodes:
            raise NodeLimit
        node_count += 1
        max_depth_seen = max(max_depth_seen, depth)
        if node_count % 500 == 0:
            print(f"checked {node_count} boxes; accepted {len(leaves)}; "
                  f"failed {len(failures)}", file=sys.stderr, flush=True)
        if diagnostics is None:
            diagnostics = evaluate(endpoints)
        valid = [row for row in diagnostics if row["valid"]]
        if valid:
            certificate = max(valid,
                key=lambda row: row["quotient_lower"])
            leaves.append({"family_index": certificate["certificate_index"],
                           "endpoints": endpoints,
                           "quotient_lower": certificate["quotient_lower"]})
            return
        if depth >= max_depth:
            if not failures:
                print("first depth-limit box:", endpoints,
                      diagnostics, file=sys.stderr, flush=True)
            failures.append(("depth-limit", endpoints, diagnostics))
            return

        candidates = []
        for coordinate in range(5):
            lo, hi = endpoints[coordinate]
            mid = (lo + hi) / 2
            candidate_children = []
            best_lowers = []
            for child_range in ((lo, mid), (mid, hi)):
                child = list(endpoints)
                child[coordinate] = child_range
                candidate_children.append(child)
                family_lowers = [epoly_centered_float_lower(
                    families[i]["quotient"], child)
                    for i in (1, 2, nested_family_index, 3)]
                best_lowers.append(max(family_lowers))
            score = (sum(lower > 0 for lower in best_lowers),
                     min(best_lowers), sum(best_lowers))
            candidates.append((score, candidate_children))
        _, chosen_children = max(candidates, key=lambda item: item[0])
        children = [(child, evaluate(child)) for child in chosen_children]
        for child, child_diagnostics in children:
            visit(child, depth + 1, child_diagnostics)

    # A modest deterministic seed grid avoids asking the greedy splitter to
    # rediscover the long, nearly diagonal family-switch curves from one
    # enormous rectangle.  Only the handful of cells crossing those curves
    # are refined recursively.
    e_parts = 8
    t_parts = 47
    try:
        for e_index in range(e_parts):
            for t_index in range(t_parts):
                seed = list(root)
                seed[1] = (Q(2 * e_index, e_parts),
                           Q(2 * (e_index + 1), e_parts))
                t_lo = Q(3, 5) + Q(47, 5) * Q(t_index, t_parts)
                t_hi = Q(3, 5) + Q(47, 5) * Q(t_index + 1, t_parts)
                seed[4] = (t_lo, t_hi)
                seed_diagnostics = evaluate(seed)
                if any(row["valid"] for row in seed_diagnostics):
                    visit(seed, 0, seed_diagnostics)
                else:
                    # The only coarse false negatives observed here come
                    # from dependency across the two broad transverse
                    # intervals.  One exact quadrant split removes it while
                    # retaining the full seam-scale range in every child.
                    for a_range in ((Q(-16), Q(0)), (Q(0), Q(16))):
                        for b_range in ((Q(-16), Q(0)), (Q(0), Q(16))):
                            child = list(seed)
                            child[2] = a_range
                            child[3] = b_range
                            visit(child, 0)
    except NodeLimit:
        truncated = True
    return {"root": root, "node_count": node_count,
            "max_depth_seen": max_depth_seen, "truncated": truncated,
            "leaves": leaves, "failures": failures,
            "family_counts": [sum(leaf["family_index"] == i
                                  for leaf in leaves) for i in range(5)]}


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


def tetrahedron_axis_radius_float(points):
    """Floating analogue used only by diagnostic profiles."""
    matrix = np.vstack((np.asarray(points, dtype=float).T, np.ones(4)))
    try:
        inverse = np.linalg.inv(matrix)
    except np.linalg.LinAlgError:
        return 0.0
    zero = inverse @ np.asarray([0., 0., 0., 1.])
    if zero.min() <= 0:
        return 0.0
    bounds = []
    for axis in range(3):
        for sign in (-1, 1):
            direction = np.zeros(4)
            direction[axis] = sign
            derivative = inverse @ direction
            bounds.extend(zero[derivative < 0]/(-derivative[derivative < 0]))
    return float(min(bounds))


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
    trig_error = KAPPA / 7
    st = (sin_q(theta), etheta + trig_error)
    ct = (cos_q(theta), etheta + trig_error)
    sp = (sin_q(phi), ephi + trig_error)
    cp = (cos_q(phi), ephi + trig_error)
    return [ball_mul(ct, sp), ball_mul(st, sp), cp]


def edge_orientation_ball(view, q0, q1, q):
    """`view · ((q1-q0) × (q-q0))` using rational vertices."""
    edge = [a-b for a, b in zip(VERTICES_Q[q1], VERTICES_Q[q0])]
    delta = [a-b for a, b in zip(VERTICES_Q[q], VERTICES_Q[q0])]
    cross = cross3(edge, delta)
    return ball_sum3([ball_scale(cross[i], view[i]) for i in range(3)])


def edge_orientation_q(view, q0, q1, q):
    """Rational orientation for a projectively normalized view vector."""
    return qdot(view, edge_cross_q(q0, q1, q))


@functools.lru_cache(maxsize=None)
def edge_cross_q(q0, q1, q):
    """Cached coefficient vector for one projective support expression."""
    edge = [a-b for a, b in zip(VERTICES_Q[q1], VERTICES_Q[q0])]
    delta = [a-b for a, b in zip(VERTICES_Q[q], VERTICES_Q[q0])]
    return tuple(cross3(edge, delta))


def silhouette_cycle_for_view(view):
    """Floating selection of the projected hull cycle perpendicular to view."""
    view = np.asarray([float(q) for q in view])
    view /= np.linalg.norm(view)
    axis = np.zeros(3)
    axis[int(np.argmin(np.abs(view)))] = 1
    first = np.cross(view, axis)
    first /= np.linalg.norm(first)
    second = np.cross(view, first)
    projected = VERTICES_EXACT @ np.vstack((first, second)).T
    return list(map(int, ConvexHull(projected).vertices))


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


def qpoly_mul_linear(a, b):
    """Product of homogeneous linear forms in the checker basis."""
    return [Q(0), Q(0), Q(0), Q(0),
            a[0]*b[0], a[0]*b[1]+a[1]*b[0],
            a[0]*b[2]+a[2]*b[0], a[1]*b[1],
            a[1]*b[2]+a[2]*b[1], a[2]*b[2]]


def projective_lift_coefficient(edge, coordinate):
    if coordinate == 0:
        return [Q(0), edge[2], -edge[1]]
    if coordinate == 1:
        return [-edge[2], Q(0), edge[0]]
    return [edge[1], -edge[0], Q(0)]


def projective_cross_lift_coefficient(edge, vertex, coordinate):
    lift = [projective_lift_coefficient(edge, c) for c in range(3)]
    if coordinate == 0:
        return [vertex[1]*lift[2][c]-vertex[2]*lift[1][c]
                for c in range(3)]
    if coordinate == 1:
        return [vertex[2]*lift[0][c]-vertex[0]*lift[2][c]
                for c in range(3)]
    return [vertex[0]*lift[1][c]-vertex[1]*lift[0][c]
            for c in range(3)]


def projective_variation_polynomials(edges, support_vertices):
    weights = [cross3(edges[1], edges[2]),
               cross3(edges[2], edges[0]),
               cross3(edges[0], edges[1])]
    answer = []
    for coordinate in range(3):
        total = qpoly_zero()
        for i in range(3):
            coefficient = projective_cross_lift_coefficient(
                edges[i], VERTICES_Q[support_vertices[i]], coordinate)
            total = qpoly_add(total,
                              qpoly_mul_linear(weights[i], coefficient))
        answer.append(total)
    return weights, answer


def projective_triangle_balls(triangle):
    balls = []
    for coordinate in range(3):
        lo = min(corner[coordinate] for corner in triangle)
        hi = max(corner[coordinate] for corner in triangle)
        balls.append(((lo+hi)/2, (hi-lo)/2))
    return balls


def projective_local_axis_row(triangle, payload):
    starts, finishes = [], []
    for a, b, sigma in payload["support_pairs"]:
        # Lean's edge is start-finish; the experiment stores sigma*(b-a).
        start, finish = ((b, a) if sigma == 1 else (a, b))
        starts.append(start)
        finishes.append(finish)
    supports = list(payload["support_vertices"])
    edges = [[x-y for x, y in zip(VERTICES_Q[a], VERTICES_Q[b])]
             for a, b in zip(starts, finishes)]
    probe_weights = [qdot(triangle[0], cross3(edges[1], edges[2])),
                     qdot(triangle[0], cross3(edges[2], edges[0])),
                     qdot(triangle[0], cross3(edges[0], edges[1]))]
    if max(probe_weights) < 0:
        for values in (starts, finishes, supports, edges):
            values[1], values[2] = values[2], values[1]
    weight_coefficients, polynomials = projective_variation_polynomials(
        edges, supports)
    weight_at = [[qdot(corner, coefficient) for corner in triangle]
                 for coefficient in weight_coefficients]
    weight_lower = [min(values)-SUPPORT_ERROR for values in weight_at]
    weight_upper = [max(values)+SUPPORT_ERROR for values in weight_at]
    if min(weight_lower) < 0 or max(weight_lower) <= 0:
        raise RuntimeError(f"weight signs fail: {weight_lower}")

    support_upper = []
    witnesses = []
    for edge, start, finish, selected in zip(
            edges, starts, finishes, supports):
        values = []
        for k in range(24):
            if symbolic_support_zero(
                    triangle, start, finish, selected, k):
                upper = Q(0)
            else:
                delta = [x-y for x, y in zip(VERTICES_Q[k],
                                              VERTICES_Q[selected])]
                coefficient = cross3(edge, delta)
                upper = max(qdot(corner, coefficient)
                            for corner in triangle) + SUPPORT_ERROR
            values.append(upper)
        if max(values) > 0:
            raise RuntimeError(
                f"support fails by {float(max(values)):.6g} on edge "
                f"{start}->{finish}")
        witness = min(range(24), key=values.__getitem__)
        if values[witness] >= 0:
            raise RuntimeError("no strict nonzero witness")
        support_upper.append(values)
        witnesses.append(witness)

    variable_balls = projective_triangle_balls(triangle)
    centers = [x[0] for x in variable_balls]
    radii = [x[1] for x in variable_balls]
    variation_balls = [qpoly_eval_centered(poly, centers, radii)
                       for poly in polynomials]
    # The exact expression below inherits several powers of the denominator
    # used for the rounded snub-cube coordinates.  Lean only needs an upper
    # bound, so round it outward before storing it in the certificate.  This
    # keeps generated terms small without weakening the checked inequality.
    exact_B = 2*sum(weight_upper, Q(0))
    B = ceil_to(exact_B, PROJECTIVE_CERTIFICATE_DENOMINATOR)
    if B <= 0:
        raise RuntimeError("nonpositive projective remainder budget")
    normalized_center = [ball[0]/B for ball in variation_balls]
    exact_delta = (sum((ball[1] for ball in variation_balls), Q(0)) +
                   3*PROJECTIVE_VARIATION_ERROR) / B
    delta = ceil_to(exact_delta, PROJECTIVE_CERTIFICATE_DENOMINATOR)
    return {
        "edge_start": starts,
        "edge_finish": finishes,
        "support_index": supports,
        "nonzero_witness": witnesses,
        "B": B,
        "normalized_center": normalized_center,
        "delta": delta,
        "diagnostics": {
            "weight_lower": weight_lower,
            "weight_upper": weight_upper,
            "variation_balls": variation_balls,
            "exact_weight_budget": exact_B,
            "exact_delta": exact_delta,
            "maximum_support_upper": max(max(row) for row in support_upper),
            "strict_witness_upper": [row[k] for row, k in
                                     zip(support_upper, witnesses)],
        },
    }


def projective_local_triangle(triangle):
    """Generate and exactly audit a local certificate on a given triangle."""
    try:
        from experiment_snub_axis_free import (certificate_vectors,
                                                best_centered_tetrahedron)
        import experiment_snub_cube as experiment_cube
    except ModuleNotFoundError:
        from scripts.experiment_snub_axis_free import (
            certificate_vectors, best_centered_tetrahedron)
        from scripts import experiment_snub_cube as experiment_cube
    if (len(triangle) != 3 or any(len(corner) != 3 for corner in triangle) or
            any(sum(corner, Q(0)) != 1 for corner in triangle) or
            min(x for corner in triangle for x in corner) < 0):
        raise ValueError("invalid rational projective triangle")
    view = [sum((corner[i] for corner in triangle), Q(0))/3
            for i in range(3)]
    # The older floating experiment uses the same chirality after the proper
    # rotation diag(-1,-1,1), and normalizes vertices to radius one instead
    # of the proof's conservative division by five.
    convention = np.diag([-1.0, -1.0, 1.0])
    experiment_view = np.asarray([float(x) for x in view]) @ convention
    points, payloads, _ = certificate_vectors(experiment_view)
    keep = [i for i, payload in enumerate(payloads)
            if len(payload["support_pairs"]) == 3]
    points = points[keep]
    payloads = [payloads[i] for i in keep]
    float_radius, chosen_indices = best_centered_tetrahedron(points)
    if chosen_indices is None:
        raise RuntimeError("no centered projective-local tetrahedron")
    normalized_search_vertices = VERTICES_EXACT / np.linalg.norm(
        VERTICES_EXACT[0])
    rotated_experiment_vertices = experiment_cube.UNIT_VERTS @ convention
    index_map = [int(np.argmin(np.linalg.norm(
        normalized_search_vertices-rotated_experiment_vertices[i], axis=1)))
                 for i in range(24)]
    if len(set(index_map)) != 24 or max(
            np.linalg.norm(normalized_search_vertices[index_map[i]]-
                           rotated_experiment_vertices[i])
            for i in range(24)) > 1e-9:
        raise AssertionError("experiment/search vertex conventions disagree")
    chosen_payloads = []
    for chosen in chosen_indices:
        payload = payloads[int(chosen)]
        chosen_payloads.append({
            **payload,
            "support_pairs": [[index_map[a], index_map[b], sigma]
                              for a, b, sigma in payload["support_pairs"]],
            "support_vertices": [index_map[i]
                                 for i in payload["support_vertices"]],
        })
    rows = [projective_local_axis_row(triangle, payload)
            for payload in chosen_payloads]
    delta = max(row["delta"] for row in rows)
    centers = [row["normalized_center"] for row in rows]
    axis_radius = exact_tetrahedron_axis_radius(centers)
    cover_radius = Q(19, 20) * Q(4, 7) * axis_radius
    # `c` occurs on the hard side of both the barycentric and radius gates,
    # so round inward.  The exact audit below is performed after rounding.
    c = floor_to(cover_radius-delta,
                 PROJECTIVE_CERTIFICATE_DENOMINATOR)
    if c <= 0:
        raise RuntimeError(
            f"axis perturbation consumes cover: radius={float(axis_radius):.6g} "
            f"delta={float(delta):.6g}")
    target_length = Q(7, 4)*(c+delta)
    bary = []
    for axis in range(3):
        for sign in (1, -1):
            target = [Q(0)]*3
            target[axis] = sign*target_length
            lam = barycentric(centers, target)
            if min(lam) < 0 or sum(lam, Q(0)) != 1:
                raise AssertionError("invalid projective-local barycentric gate")
            bary.append(lam)
    return {
        "view": view,
        "triangle": triangle,
        "certificates": [{key: value for key, value in row.items()
                          if key not in ("normalized_center", "delta")}
                         for row in rows],
        "c": c,
        "delta": delta,
        "diagnostics": {
            "floating_selected_radius": float_radius,
            "selected_indices": list(map(int, chosen_indices)),
            "normalized_centers": centers,
            "exact_axis_radius": axis_radius,
            "cover_radius": cover_radius,
            "minimum_barycentric": min(x for row in bary for x in row),
        },
    }


def projective_local_smoke(view, triangle_width):
    """Generate one symmetric projective-local row around a rational view."""
    if len(view) != 3 or sum(view, Q(0)) != 1 or min(view) <= 0:
        raise ValueError("view must be a positive rational simplex point")
    e = triangle_width
    triangle = [[view[0]+e, view[1]-e, view[2]],
                [view[0], view[1]+e, view[2]-e],
                [view[0]-e, view[1], view[2]+e]]
    if min(x for corner in triangle for x in corner) < 0:
        raise ValueError("triangle leaves the positive simplex")
    answer = projective_local_triangle(triangle)
    answer["triangle_width"] = triangle_width
    return answer


def projective_local_cover(max_depth, exact_audit_limit=25):
    """Adaptively audit projective-local rows over the outer chamber.

    This produces profile data, not a committed certificate tree.  Cells
    crossing a floating silhouette change are subdivided before invoking the
    exact rational checker, which makes the remaining failures useful maps of
    the transition strata rather than a mixture of unrelated coarse cells.
    """
    e0 = (Q(1), Q(0), Q(0))
    m01 = (Q(1, 2), Q(1, 2), Q(0))
    m02 = (Q(1, 2), Q(0), Q(1, 2))
    center = (Q(1, 3), Q(1, 3), Q(1, 3))
    stack = [((e0, m01, center), 0), ((e0, center, m02), 0)]
    counts = {"nodes": 0, "splits": 0, "silhouette_splits": 0,
              "certificate_leaves": 0, "uncovered_leaves": 0}
    radii = []
    failures = []
    exact_audit = {"attempted": 0, "passed": 0, "failed": 0,
                   "failure_reasons": {}}
    try:
        from experiment_snub_axis_free import (certificate_vectors,
                                                centered_inradius)
    except ModuleNotFoundError:
        from scripts.experiment_snub_axis_free import (certificate_vectors,
                                                        centered_inradius)
    while stack:
        triangle, depth = stack.pop()
        counts["nodes"] += 1
        cycles = [tuple(silhouette_cycle_for_view(
            np.asarray([float(x) for x in corner])))
            for corner in triangle]
        same_silhouette = cycles[0] == cycles[1] == cycles[2]
        if same_silhouette:
            try:
                centroid = np.asarray([float(sum(
                    (corner[i] for corner in triangle), Q(0))/3)
                    for i in range(3)])
                points, _, _ = certificate_vectors(
                    centroid @ np.diag([-1.0, -1.0, 1.0]))
                point_radius, _, _ = centered_inradius(points)
                if point_radius <= 1e-9:
                    raise RuntimeError("pointwise axis-free radius vanishes")
                # The floating experiment uses unit-radius vertices while
                # the proof divides by five.  This radius is diagnostic; a
                # bounded sample of accepted cells is rerun exactly below.
                radii.append(Q(4, 7) * point_radius / 5)
                if exact_audit["attempted"] < exact_audit_limit:
                    exact_audit["attempted"] += 1
                    try:
                        projective_local_triangle(triangle)
                        exact_audit["passed"] += 1
                    except (RuntimeError, ValueError) as exc:
                        exact_audit["failed"] += 1
                        audit_reason = str(exc).split(":")[0]
                        exact_audit["failure_reasons"][audit_reason] = (
                            exact_audit["failure_reasons"].get(
                                audit_reason, 0) + 1)
                        raise RuntimeError(
                            f"exact local audit failed: {exc}") from exc
                counts["certificate_leaves"] += 1
                continue
            except (RuntimeError, ValueError) as exc:
                reason = str(exc)
        else:
            counts["silhouette_splits"] += 1
            reason = "silhouette changes across triangle"
        if depth < max_depth:
            counts["splits"] += 1
            stack.extend((child, depth+1)
                         for child in split_simplex_triangle(triangle))
        else:
            counts["uncovered_leaves"] += 1
            if len(failures) < 40:
                failures.append({
                    "depth": depth,
                    "centroid": [sum((corner[i] for corner in triangle),
                                     Q(0))/3 for i in range(3)],
                    "cycles": [list(cycle) for cycle in cycles],
                    "reason": reason,
                })
    quantiles = ([float(x) for x in np.quantile(
        radii, [0, .01, .1, .5, .9, .99, 1])] if radii else [])
    return {"max_depth": max_depth, "counts": counts,
            "exact_audit": exact_audit,
            "radius_quantiles_min_01_10_50_90_99_max": quantiles,
            "failure_examples": failures}


def projective_transition_profile():
    """Measure the scale-invariant constants at the hardest symmetry-wall seam.

    The seam replaces the silhouette path `15-11-10-14` by
    `15-3-2-14`.  A strong bundle from the first side is retained as an
    approximate-support defect bundle on the second side.  The regular bundle
    on the second side has radius proportional to the exact support
    orientation `d`; the ratios below test the overlap inequality formalized
    in `BalancedSupport.Transition`.
    """
    transition_edge = VERTICES_EXACT[15] - VERTICES_EXACT[11]
    transition_delta = VERTICES_EXACT[3] - VERTICES_EXACT[15]
    transition_coefficient = np.cross(transition_edge, transition_delta)
    # Solve `(1-u,u,0) dot coefficient = 0`.
    u0 = float(-transition_coefficient[0] /
               (transition_coefficient[1]-transition_coefficient[0]))
    central_u = Q(1, 5)
    central_view_q = [1-central_u, central_u, Q(0)]
    central = projective_local_triangle(
        [central_view_q, central_view_q, central_view_q])
    rows = central["certificates"]

    def central_at(view):
        points = []
        defects = []
        minimum_weight = math.inf
        for row in rows:
            starts = row["edge_start"]
            finishes = row["edge_finish"]
            supports = row["support_index"]
            edges = [VERTICES_EXACT[a]-VERTICES_EXACT[b]
                     for a, b in zip(starts, finishes)]
            weights = np.asarray([
                view @ np.cross(edges[1], edges[2]),
                view @ np.cross(edges[2], edges[0]),
                view @ np.cross(edges[0], edges[1])])
            minimum_weight = min(minimum_weight, float(weights.min()))
            avec = np.zeros(3)
            total_defect = 0.0
            for weight, edge, selected in zip(weights, edges, supports):
                lift = np.cross(view, edge)
                avec += weight * np.cross(VERTICES_EXACT[selected], lift)
                support = max(float(view @ np.cross(
                    edge, VERTICES_EXACT[k]-VERTICES_EXACT[selected]))
                              for k in range(24))
                total_defect += weight * max(0.0, support)
            B = float(row["B"])
            points.append(avec/B)
            defects.append(total_defect/B)
        radius = tetrahedron_axis_radius_float(points)
        return {"c": 4*radius/7, "maximum_normalized_defect": max(defects),
                "minimum_weight": minimum_weight}

    samples = []
    for offset in (1e-6, 2e-6, 5e-6, 1e-5, 2e-5, 5e-5,
                   1e-4, 2e-4, 5e-4, 1e-3, 2e-3, 5e-3):
        u = u0 + offset
        view = np.asarray([1-u, u, 0.0])
        d = float(view @ transition_coefficient)
        central_row = central_at(view)
        regular_q = Q(round(u*10**12), 10**12)
        regular_view = [1-regular_q, regular_q, Q(0)]
        try:
            regular = projective_local_triangle(
                [regular_view, regular_view, regular_view])
            regular_c = float(regular["c"])
        except RuntimeError:
            regular_c = 0.0
        samples.append({
            "u_offset": offset, "support_distance": d,
            "regular_c": regular_c,
            "regular_k_ratio": regular_c/d if d > 0 else 0.0,
            "central_c": central_row["c"],
            "central_defect": central_row["maximum_normalized_defect"],
            "central_D_ratio": (central_row["maximum_normalized_defect"]/d
                                if d > 0 else math.inf),
            "central_minimum_weight": central_row["minimum_weight"],
        })
    positive_k = [row["regular_k_ratio"] for row in samples
                  if row["regular_k_ratio"] > 0]
    D = max(row["central_D_ratio"] for row in samples)
    k = min(positive_k) if positive_k else 0.0
    c = min(row["central_c"] for row in samples)
    # Largest small-rotation chart radius allowed by the formal overlap gate.
    # D(1+r²) <= 2k(c-r).
    coefficients = [D, 2*k, D-2*k*c]
    roots = np.roots(coefficients) if D > 0 else [c]
    allowed = [float(root.real) for root in roots
               if abs(root.imag) < 1e-12 and 0 < root.real < min(1, c)]

    # Retain heterogeneous defect slopes instead of replacing all of them by
    # the single worst D.  This computes the blown-up limiting problem
    #   min_axis max_j (axis dot a_j - D_j/(2t)).
    # It is the numerical target for a finite polynomial axis-case checker.
    try:
        from experiment_snub_axis_free import certificate_vectors
        import experiment_snub_cube as experiment_cube
    except ModuleNotFoundError:
        from scripts.experiment_snub_axis_free import certificate_vectors
        from scripts import experiment_snub_cube as experiment_cube
    convention = np.diag([-1.0, -1.0, 1.0])
    source_view = np.asarray(list(map(float, central_view_q)))
    _, source_payloads, _ = certificate_vectors(source_view @ convention)
    normalized_search_vertices = VERTICES_EXACT / np.linalg.norm(
        VERTICES_EXACT[0])
    rotated_experiment_vertices = experiment_cube.UNIT_VERTS @ convention
    index_map = [int(np.argmin(np.linalg.norm(
        normalized_search_vertices-rotated_experiment_vertices[i], axis=1)))
        for i in range(24)]
    transition_view = np.asarray([1-u0, u0, 0.0])
    probe_view = np.asarray([1-u0-1e-7, u0+1e-7, 0.0])
    probe_d = float(probe_view @ transition_coefficient)
    family_points = []
    family_D = []
    family_records = []
    for payload in source_payloads:
        if len(payload["support_pairs"]) != 3:
            continue
        starts, finishes = [], []
        for a, b, sigma in payload["support_pairs"]:
            a, b = index_map[a], index_map[b]
            start, finish = ((b, a) if sigma == 1 else (a, b))
            starts.append(start)
            finishes.append(finish)
        supports = [index_map[i] for i in payload["support_vertices"]]
        edges = [VERTICES_EXACT[a]-VERTICES_EXACT[b]
                 for a, b in zip(starts, finishes)]
        weights = np.asarray([
            transition_view @ np.cross(edges[1], edges[2]),
            transition_view @ np.cross(edges[2], edges[0]),
            transition_view @ np.cross(edges[0], edges[1])])
        if weights.max() < 0:
            for values in (starts, finishes, supports, edges):
                values[1], values[2] = values[2], values[1]
            weights = weights[[0, 2, 1]] * -1
        if weights.min() < -1e-9 or weights.sum() <= 1e-12:
            continue
        B = 2*weights.sum()
        avec = np.zeros(3)
        total_defect = 0.0
        for weight, edge, selected in zip(weights, edges, supports):
            avec += weight*np.cross(
                VERTICES_EXACT[selected], np.cross(transition_view, edge))
            support = max(float(probe_view @ np.cross(
                edge, VERTICES_EXACT[q]-VERTICES_EXACT[selected]))
                          for q in range(24))
            total_defect += weight*max(0.0, support)
        family_points.append(avec/B)
        family_D.append(total_defect/(B*probe_d))
        family_records.append((starts, finishes, supports))
    family_points = np.asarray(family_points)
    family_D = np.asarray(family_D)
    rng = np.random.default_rng(20260719)
    axes = rng.normal(size=(50000, 3))
    axes /= np.linalg.norm(axes, axis=1)[:, None]

    def sampled_heterogeneous_margin(t):
        values = axes @ family_points.T - family_D[None, :]/(2*t)
        maxima = values.max(axis=1)
        return float(maxima.min()), int(np.argmin(maxima))

    from scipy.optimize import minimize

    def optimized_heterogeneous_margin(t, start_count=16):
        values = axes @ family_points.T - family_D[None, :]/(2*t)
        maxima = values.max(axis=1)
        starts = axes[np.argsort(maxima)[:start_count]]

        def objective(raw):
            norm = np.linalg.norm(raw)
            if norm < 1e-12:
                return 1.0
            axis = raw/norm
            return float(np.max(family_points @ axis - family_D/(2*t)))

        best = (math.inf, None)
        for start in starts:
            result = minimize(objective, start, method="Nelder-Mead",
                              options={"maxiter": 1200, "xatol": 1e-11,
                                       "fatol": 1e-12})
            if result.fun < best[0]:
                best = (float(result.fun), result.x/np.linalg.norm(result.x))
        return best

    lo, hi = 1e-4, 128.0
    for _ in range(24):
        mid = math.sqrt(lo*hi)
        if optimized_heterogeneous_margin(mid, 8)[0] >= 0:
            hi = mid
        else:
            lo = mid
    threshold_margin, threshold_axis = optimized_heterogeneous_margin(hi, 24)
    regular_margin, regular_axis = (
        optimized_heterogeneous_margin(k, 32) if k > 0
        else (-math.inf, np.zeros(3)))
    sampled_regular_margin, _ = (
        sampled_heterogeneous_margin(k) if k > 0 else (-math.inf, 0))
    heterogeneous = {
        "certificate_count": len(family_points),
        "regular_boundary_t": k,
        "margin_at_regular_boundary": regular_margin,
        "sampled_margin_at_regular_boundary": sampled_regular_margin,
        "worst_axis_at_regular_boundary": regular_axis.tolist(),
        "estimated_defect_threshold_t": hi,
        "threshold_margin": threshold_margin,
        "threshold_axis": threshold_axis.tolist(),
        "defect_slope_quantiles": np.quantile(
            family_D, [0, .1, .5, .9, 1]).tolist(),
    }

    quadratic_rows = []
    chart_offset = 1e-5
    chart_view = np.asarray([1-u0-chart_offset, u0+chart_offset, 0.0])
    chart_d = float(chart_view @ transition_coefficient)
    for t in (.5, 1., 2., 3., 4., 5., 6., 7., 8.):
        cayley = np.asarray([0., 0., t*chart_d])
        cross_matrix = np.asarray([
            [0., -cayley[2], cayley[1]],
            [cayley[2], 0., -cayley[0]],
            [-cayley[1], cayley[0], 0.]])
        rotation = (((1-cayley@cayley)*np.eye(3) +
                     2*np.outer(cayley, cayley) + 2*cross_matrix) /
                    (1+cayley@cayley))
        best_score = -math.inf
        best_index = None
        for index, (starts, finishes, supports) in enumerate(family_records):
            edges = [VERTICES_EXACT[a]-VERTICES_EXACT[b]
                     for a, b in zip(starts, finishes)]
            weights = np.asarray([
                chart_view @ np.cross(edges[1], edges[2]),
                chart_view @ np.cross(edges[2], edges[0]),
                chart_view @ np.cross(edges[0], edges[1])])
            if weights.min() < -1e-10:
                continue
            displacement = 0.0
            defect = 0.0
            for weight, edge, selected in zip(weights, edges, supports):
                displacement += weight * float(chart_view @ np.cross(
                    edge, rotation@VERTICES_EXACT[selected]-
                    VERTICES_EXACT[selected]))
                support = max(float(chart_view @ np.cross(
                    edge, VERTICES_EXACT[q]-VERTICES_EXACT[selected]))
                              for q in range(24))
                defect += weight*max(0.0, support)
            score = displacement-defect
            if score > best_score:
                best_score, best_index = score, index
        best_starts, best_finishes, best_supports = family_records[best_index]
        best_edges = [VERTICES_EXACT[a]-VERTICES_EXACT[b]
                      for a, b in zip(best_starts, best_finishes)]
        support_competitors = [max(range(24), key=lambda q: float(
            chart_view @ np.cross(edge,
                VERTICES_EXACT[q]-VERTICES_EXACT[selected])))
            for edge, selected in zip(best_edges, best_supports)]
        quadratic_rows.append({
            "t": t, "best_score_over_d_sq": best_score/(chart_d*chart_d),
            "best_certificate": best_index,
            "edge_starts": best_starts,
            "edge_finishes": best_finishes,
            "support_vertices": best_supports,
            "support_competitors": support_competitors,
        })
    return {
        "transition_u": u0,
        "transition_coefficient": transition_coefficient.tolist(),
        "central_view": list(map(float, central_view_q)),
        "conservative_constants": {"c": c, "k": k, "D": D,
                                   "maximum_overlap_radius":
                                       max(allowed) if allowed else 0.0},
        "heterogeneous_limit": heterogeneous,
        "axis_z_exact_quadratic": quadratic_rows,
        "samples": samples,
    }


def transition_axis_families():
    """Return the oriented three-contact bank at the hard transition view."""
    try:
        from experiment_snub_axis_free import certificate_vectors
        import experiment_snub_cube as experiment_cube
    except ModuleNotFoundError:
        from scripts.experiment_snub_axis_free import certificate_vectors
        from scripts import experiment_snub_cube as experiment_cube
    convention = np.diag([-1.0, -1.0, 1.0])
    source_view = np.asarray([.8, .2, 0.0])
    _, payloads, _ = certificate_vectors(source_view @ convention)
    normalized_search_vertices = VERTICES_EXACT / np.linalg.norm(
        VERTICES_EXACT[0])
    rotated_experiment_vertices = experiment_cube.UNIT_VERTS @ convention
    index_map = [int(np.argmin(np.linalg.norm(
        normalized_search_vertices-rotated_experiment_vertices[i], axis=1)))
        for i in range(24)]
    transition_edge = VERTICES_EXACT[15] - VERTICES_EXACT[11]
    transition_delta = VERTICES_EXACT[3] - VERTICES_EXACT[15]
    seam = np.cross(transition_edge, transition_delta)
    u0 = float(-seam[0]/(seam[1]-seam[0]))
    transition_view = np.asarray([1-u0, u0, 0.0])
    families = []
    for source_index, payload in enumerate(payloads):
        if len(payload["support_pairs"]) != 3:
            continue
        starts, finishes = [], []
        for a, b, sigma in payload["support_pairs"]:
            a, b = index_map[a], index_map[b]
            start, finish = ((b, a) if sigma == 1 else (a, b))
            starts.append(start)
            finishes.append(finish)
        supports = [index_map[i] for i in payload["support_vertices"]]
        edges = [VERTICES_EXACT[a]-VERTICES_EXACT[b]
                 for a, b in zip(starts, finishes)]
        weights = np.asarray([
            transition_view @ np.cross(edges[1], edges[2]),
            transition_view @ np.cross(edges[2], edges[0]),
            transition_view @ np.cross(edges[0], edges[1])])
        if weights.max() < 0:
            starts[1], starts[2] = starts[2], starts[1]
            finishes[1], finishes[2] = finishes[2], finishes[1]
            supports[1], supports[2] = supports[2], supports[1]
            edges[1], edges[2] = edges[2], edges[1]
            weights = weights[[0, 2, 1]] * -1
        if weights.min() < -1e-9 or weights.sum() <= 1e-12:
            continue
        families.append({"name": f"axis-family-{len(families)}",
                         "source_index": source_index,
                         "starts": starts, "finishes": finishes,
                         "supports": supports, "edges": edges})
    return families


def projective_transition_blowup_profile(samples: int, seed: int):
    """Probe the full scale-invariant chart around the hardest seam.

    The exact z-axis certificate uses ``z=d*t``.  The pointwise local margin
    shows that the remaining bad axis cone narrows linearly with ``d``, so
    the transverse Cayley coordinates have the second-order scaling
    ``x=d^2*a`` and ``y=d^2*b``.  The seam is on the symmetry wall ``n_z=0``;
    its tangential projective coordinate is written ``n_z=d*e``.

    This routine is exploratory (the eventual boxes are checked exactly in
    Lean), but it evaluates the actual finite Cayley rotation, exact snub
    vertices, determinant weights, and support defects.  Its output tells us
    whether one algebraic family controls a genuine five-variable chart.
    """
    families = transition_axis_families()
    quadratic_family = families[192]
    transition_edge = VERTICES_EXACT[15] - VERTICES_EXACT[11]
    transition_delta = VERTICES_EXACT[3] - VERTICES_EXACT[15]
    seam = np.cross(transition_edge, transition_delta)
    slope = float(seam[1]-seam[0])

    def evaluate(family, d, e, a, b, t):
        h = d*e
        u = (d-float(seam[0])*(1-h)-float(seam[2])*h)/slope
        view = np.asarray([1-u-h, u, h])
        cayley = np.asarray([d*d*a, d*d*b, d*t])
        x, y, z = cayley
        denominator = 1+x*x+y*y+z*z
        numerator = np.asarray([
            [1+x*x-y*y-z*z, 2*(x*y-z), 2*(x*z+y)],
            [2*(x*y+z), 1-x*x+y*y-z*z, 2*(y*z-x)],
            [2*(x*z-y), 2*(y*z+x), 1-x*x-y*y+z*z]])
        weights = np.asarray([
            view @ np.cross(family["edges"][1], family["edges"][2]),
            view @ np.cross(family["edges"][2], family["edges"][0]),
            view @ np.cross(family["edges"][0], family["edges"][1])])
        if weights.min() < -1e-10:
            return {"quotient": -math.inf,
                    "displacement_quotient": -math.inf,
                    "defect_quotient": math.inf,
                    "minimum_weight": float(weights.min()),
                    "maximum_support_defect": math.inf,
                    "view": view.tolist()}
        cleared_displacement = 0.0
        cleared_defect = 0.0
        defects = []
        for weight, edge, selected in zip(
                weights, family["edges"], family["supports"]):
            q = VERTICES_EXACT[selected]
            displacement = numerator@q-denominator*q
            cleared_displacement += weight*float(
                view @ np.cross(edge, displacement))
            defect = max(0.0, max(float(view @ np.cross(
                edge, VERTICES_EXACT[k]-q)) for k in range(24)))
            defects.append(defect)
            cleared_defect += weight*denominator*defect
        return {
            "quotient": (cleared_displacement-cleared_defect)/(d*d),
            "displacement_quotient": cleared_displacement/(d*d),
            "defect_quotient": cleared_defect/(d*d),
            "minimum_weight": float(weights.min()),
            "maximum_support_defect": max(defects),
            "view": view.tolist(),
        }

    # Deterministic corners first, then log-uniform seam scales and random
    # chart coordinates.  Ranges are deliberately generous; ordinary local
    # leaves are expected to take over well before their boundary.
    records = []
    for d in (1e-7, 1e-6, 1e-5, 1e-4, 1e-3):
        for e in (0.0, 1.0, 4.0, 16.0):
            for a in (-16.0, 0.0, 16.0):
                for b in (-16.0, 0.0, 16.0):
                    for t in (0.4, 1.0, 3.0, 6.0, 6.75):
                        records.append((d, e, a, b, t,
                                        evaluate(quadratic_family,
                                                 d, e, a, b, t)))
    rng = random.Random(seed)
    for _ in range(samples):
        d = 10**rng.uniform(-8, -3)
        e = rng.uniform(0, 16)
        a = rng.uniform(-16, 16)
        b = rng.uniform(-16, 16)
        t = rng.uniform(.4, 6.75)
        records.append((d, e, a, b, t,
                        evaluate(quadratic_family, d, e, a, b, t)))
    records.sort(key=lambda row: row[-1]["quotient"])
    values = np.asarray([row[-1]["quotient"] for row in records])
    probe_d = 1e-5
    candidate_indices = {2, 192}
    for e, t in ((.5, 5.8), (1.0, 5.0), (1.5, 4.2),
                 (2.0, 3.2), (2.0, 3.4)):
        scores = [evaluate(family, probe_d, e, 0.0, 0.0, t)[
            "quotient"] for family in families]
        candidate_indices.add(int(np.argmax(scores)))
    transition_families = [families[i] for i in sorted(candidate_indices)]
    overlap = []
    for e in (0.0, .5, 1.0, 1.5, 2.0, 3.0):
        h = probe_d*e
        u = (probe_d-float(seam[0])*(1-h)-float(seam[2])*h)/slope
        view = [1-u-h, u, h]
        view_q = [Q(round(value*10**12), 10**12) for value in view]
        view_q[-1] += 1-sum(view_q, Q(0))
        try:
            regular = projective_local_triangle([view_q]*3)
            regular_ratio = float(regular["c"])/probe_d
        except (RuntimeError, ValueError):
            regular_ratio = 0.0
        t_grid = np.linspace(.4, 10, 49)
        worst_by_t = [min(max(evaluate(
                              family, probe_d, e, a, b, float(t))["quotient"]
                                  for family in transition_families)
                          for a in (-16.0, 0.0, 16.0)
                          for b in (-16.0, 0.0, 16.0))
                      for t in t_grid]
        covered_after_regular = [float(t) for t, value in
                                 zip(t_grid, worst_by_t)
                                 if t >= regular_ratio and value >= 0]
        overlap.append({
            "e": e,
            "regular_radius_over_d": regular_ratio,
            "family_minimum_on_transverse_corners": min(worst_by_t),
            "family_worst_t": float(t_grid[int(np.argmin(worst_by_t))]),
            "family_negative_t": [float(t) for t, value in
                                  zip(t_grid, worst_by_t) if value < 0],
            "family_positive_t_min": (min(covered_after_regular)
                                      if covered_after_regular else None),
            "family_positive_t_max": (max(covered_after_regular)
                                      if covered_after_regular else None),
            "gap_at_regular_boundary": (min(
                max(evaluate(family, probe_d, e, a, b,
                             regular_ratio)["quotient"]
                    for family in transition_families)
                for a in (-16.0, 0.0, 16.0)
                for b in (-16.0, 0.0, 16.0))
                if regular_ratio > 0 else None),
        })
    return {
        "scaling": {"n_z": "d*e", "x": "d^2*a", "y": "d^2*b",
                    "z": "d*t"},
        "family_count": len(families),
        "selected_transition_family_indices": sorted(candidate_indices),
        "selected_transition_families": [
            {key: value for key, value in families[i].items()
             if key != "edges"} for i in sorted(candidate_indices)],
        "quadratic_family": {key: value for key, value in
                             quadratic_family.items() if key != "edges"},
        "sample_count": len(records),
        "quotient_quantiles_min_01_10_50_90_max": np.quantile(
            values, [0, .01, .1, .5, .9, 1]).tolist(),
        "negative_count": int((values < 0).sum()),
        "regular_transition_overlap": overlap,
        "worst": [{
            "d": d, "e": e, "a": a, "b": b, "t": t, **result}
            for d, e, a, b, t, result in records[:20]],
    }


def transition_family_gap_profile(d=1e-6, e=0.0, a=0.0, b=-16.0,
                                  ratio=6.7):
    """Rank the complete transition bank at a discovered thin gap."""
    families = transition_axis_families()
    transition_edge = VERTICES_EXACT[15] - VERTICES_EXACT[11]
    transition_delta = VERTICES_EXACT[3] - VERTICES_EXACT[15]
    seam = np.cross(transition_edge, transition_delta)
    slope = float(seam[1] - seam[0])
    h = d * e
    u = (d-float(seam[0])*(1-h)-float(seam[2])*h)/slope
    view = np.asarray([1-u-h, u, h])
    x, y, z = d*d*a, d*d*b, d*ratio
    denominator = 1+x*x+y*y+z*z
    numerator = np.asarray([
        [1+x*x-y*y-z*z, 2*(x*y-z), 2*(x*z+y)],
        [2*(x*y+z), 1-x*x+y*y-z*z, 2*(y*z-x)],
        [2*(x*z-y), 2*(y*z+x), 1-x*x-y*y+z*z]])
    rows = []
    for index, family in enumerate(families):
        weights = np.asarray([
            view @ np.cross(family["edges"][1], family["edges"][2]),
            view @ np.cross(family["edges"][2], family["edges"][0]),
            view @ np.cross(family["edges"][0], family["edges"][1])])
        if weights.min() < -1e-10:
            continue
        obstruction = 0.0
        competitors = []
        for weight, edge, selected in zip(
                weights, family["edges"], family["supports"]):
            q = VERTICES_EXACT[selected]
            displacement = numerator @ q - denominator*q
            displacement_value = float(view @ np.cross(edge, displacement))
            support_values = [float(view @ np.cross(
                edge, VERTICES_EXACT[k]-q)) for k in range(24)]
            competitor = int(np.argmax(support_values))
            competitors.append(competitor)
            obstruction += weight * (
                displacement_value-denominator*support_values[competitor])
        rows.append({"family_index": index,
                     "quotient": obstruction/(d*d),
                     "starts": family["starts"],
                     "finishes": family["finishes"],
                     "supports": family["supports"],
                     "competitors": competitors})
    rows.sort(key=lambda row: row["quotient"], reverse=True)
    return {"point": [d, e, a, b, ratio], "bank_size": len(families),
            "top": rows[:12]}


def search_transition_farkas_family(d, e, a, b, ratio):
    """Search all projected vertex-pair normals at one transition point.

    This is a dependency-free implementation of the planar Farkas dual.
    Each candidate normal chooses an outer support vertex of the unrotated
    snub cube and an inner vertex maximizing the rotated support.  A balanced
    triple with positive weighted excess is a translated-support family.
    """
    vertices = [[texpr_float(coordinate) for coordinate in vertex]
                for vertex in VERTICES_SYMBOLIC]
    transition_edge = [x-y for x, y in
                       zip(vertices[15], vertices[11])]
    transition_delta = [x-y for x, y in
                        zip(vertices[3], vertices[15])]
    seam = cross3(transition_edge, transition_delta)
    h = d*e
    u = (d-seam[0]*(1-h)-seam[2]*h)/(seam[1]-seam[0])
    view = [1-u-h, u, h]
    view_norm = math.sqrt(qdot(view, view))
    view_unit = [x/view_norm for x in view]
    reference = [1.0, 0.0, 0.0]
    if abs(qdot(reference, view_unit)) > .9:
        reference = [0.0, 1.0, 0.0]
    basis0 = cross3(view_unit, reference)
    basis0_norm = math.sqrt(qdot(basis0, basis0))
    basis0 = [x/basis0_norm for x in basis0]
    basis1 = cross3(view_unit, basis0)

    x, y, z = d*d*a, d*d*b, d*ratio
    denominator = 1+x*x+y*y+z*z
    numerator = [
        [1+x*x-y*y-z*z, 2*(x*y-z), 2*(x*z+y)],
        [2*(x*y+z), 1-x*x+y*y-z*z, 2*(y*z-x)],
        [2*(x*z-y), 2*(y*z+x), 1-x*x-y*y+z*z],
    ]
    rotated = [[sum(numerator[i][j]*vertex[j] for j in range(3)) /
                denominator for i in range(3)] for vertex in vertices]

    # Identical projected directions can arise from several parallel chords;
    # only the one with greatest support excess can enter an optimum.
    by_direction = {}
    for start in range(24):
        for finish in range(start):
            base_edge = [vertices[start][i]-vertices[finish][i]
                         for i in range(3)]
            for reverse in (False, True):
                edge = ([-value for value in base_edge]
                        if reverse else base_edge)
                oriented_start, oriented_finish = ((finish, start)
                    if reverse else (start, finish))
                normal = cross3(view, edge)
                normal_norm = math.sqrt(qdot(normal, normal))
                if normal_norm < 1e-12:
                    continue
                normal = [value/normal_norm for value in normal]
                plane = (qdot(normal, basis0), qdot(normal, basis1))
                outer = max(range(24),
                            key=lambda i: qdot(normal, vertices[i]))
                inner = max(range(24),
                            key=lambda i: qdot(normal, rotated[i]))
                excess = (qdot(normal, rotated[inner]) -
                          qdot(normal, vertices[outer]))
                key = (round(plane[0], 10), round(plane[1], 10))
                record = {"plane": plane, "excess": excess,
                          "start": oriented_start,
                          "finish": oriented_finish,
                          "inner": inner, "outer": outer}
                if key not in by_direction or excess > \
                        by_direction[key]["excess"]:
                    by_direction[key] = record
    candidates = list(by_direction.values())

    def det(left, right):
        return left[0]*right[1]-left[1]*right[0]

    best = None
    for first, second, third in itertools.combinations(candidates, 3):
        weights = [det(second["plane"], third["plane"]),
                   det(third["plane"], first["plane"]),
                   det(first["plane"], second["plane"])]
        if max(weights) <= 1e-12:
            weights = [-weight for weight in weights]
        if min(weights) < -1e-10 or sum(weights) <= 1e-12:
            continue
        margin = sum(weight*record["excess"] for weight, record in
                     zip(weights, (first, second, third))) / sum(weights)
        if best is None or margin > best[0]:
            best = (margin, weights, (first, second, third))
    if best is None:
        raise RuntimeError("no balanced projected-normal triple")
    margin, weights, records = best
    return {
        "point": [d, e, a, b, ratio],
        "direction_count": len(candidates),
        "normalized_margin": margin,
        "normalized_weights": weights,
        "edge_starts": [record["start"] for record in records],
        "edge_finishes": [record["finish"] for record in records],
        "support_vertices": [record["inner"] for record in records],
        "outer_vertices": [record["outer"] for record in records],
        "support_competitors": [record["outer"] for record in records],
        "individual_excess": [record["excess"] for record in records],
    }


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


@functools.lru_cache(maxsize=None)
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
    return tuple(tuple(qpoly_scale(-1, value)) for value in cross)


def best_edge_cycles_for_view(relative_center, view, max_length=4,
                              count=1):
    """Rank short vertex cycles by exact-center support surplus."""
    x, y, z = map(float, relative_center)
    view = np.asarray([float(q) for q in view])
    view /= np.linalg.norm(view)
    d = 1+x*x+y*y+z*z
    numerator = np.asarray([
        [1+x*x-y*y-z*z, 2*(x*y-z), 2*(x*z+y)],
        [2*(x*y+z), 1-x*x+y*y-z*z, 2*(y*z-x)],
        [2*(x*z-y), 2*(y*z+x), 1-x*x-y*y+z*z]])
    rewards = np.full((24, 24), -math.inf)
    for q0 in range(24):
        for q1 in range(24):
            if q0 == q1:
                continue
            edge = VERTICES_EXACT[q0] - VERTICES_EXACT[q1]
            support = float(np.max(
                np.cross(edge, VERTICES_EXACT-VERTICES_EXACT[q0]) @ view))
            displacement = VERTICES_EXACT @ numerator.T - \
                d*VERTICES_EXACT[q0]
            contact = float(np.max(np.cross(edge, displacement) @ view))
            rewards[q0, q1] = contact-d*support
    # Enumerate all cycles of lengths 2--4 with NumPy broadcasts.  The old
    # nested Python permutations dominated adaptive-tree generation.
    score_arrays = []
    if max_length >= 2:
        score_arrays.append((2, (rewards + rewards.T) / 2))
    if max_length >= 3:
        score3 = (rewards[:, :, None] + rewards[None, :, :] +
                  rewards.T[:, None, :]) / 3
        score_arrays.append((3, score3))
    if max_length >= 4:
        score4 = (rewards[:, :, None, None] +
                  rewards[None, :, :, None] +
                  rewards[None, None, :, :] +
                  rewards.T[:, None, None, :]) / 4
        indices = np.arange(24)
        score4 = np.where(indices[:, None, None, None] ==
                          indices[None, None, :, None], -math.inf, score4)
        score4 = np.where(indices[None, :, None, None] ==
                          indices[None, None, None, :], -math.inf, score4)
        score_arrays.append((4, score4))
    candidates = []
    take = max(32, count*16)
    for length, scores in score_arrays:
        flat = scores.ravel()
        amount = min(take, flat.size)
        top = np.argpartition(flat, flat.size-amount)[-amount:]
        for flat_index in top:
            cycle = tuple(int(i) for i in np.unravel_index(flat_index,
                                                            scores.shape))
            if len(set(cycle)) != length:
                continue
            # Quotient cyclic rotations to avoid returning the same cycle
            # several times among the top candidates.
            rotations = [cycle[i:]+cycle[:i] for i in range(length)]
            canonical = min(rotations)
            candidates.append((float(flat[flat_index]), canonical))
    best = []
    seen = set()
    for item in sorted(candidates, reverse=True):
        if item[1] in seen:
            continue
        seen.add(item[1])
        best.append(item)
        if len(best) == count:
            break
    if not best:
        raise RuntimeError("no nondegenerate edge cycle")
    return [(list(cycle), {"point_mean_surplus": mean,
                           "point_total_surplus": mean*len(cycle)})
            for mean, cycle in best]


def best_cayley_edge_cycle(center, max_length=4):
    """Search one short vertex cycle by exact-center support surplus."""
    theta, phi, x, y, z = center
    view = [math.cos(float(theta))*math.sin(float(phi)),
            math.sin(float(theta))*math.sin(float(phi)), math.cos(float(phi))]
    return best_edge_cycles_for_view(
        (x, y, z), view, max_length=max_length, count=1)[0]


def cayley_edge_smoke(center, half_widths, cycle=None,
                      cycle_search_length=0):
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
    cycle_diagnostics = {}
    if cycle_search_length:
        cycle, cycle_diagnostics = best_cayley_edge_cycle(
            center, cycle_search_length)
    elif cycle is None:
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
        witness = max(range(24),
                      key=lambda q: supports[q][0]-supports[q][1])
        minimum_support = (support_lower if minimum_support is None else
                           min(minimum_support, support_lower))
        minimum_strict = (strict_lower if minimum_strict is None else
                          min(minimum_strict, strict_lower))
        if strict_lower <= SUPPORT_ERROR:
            raise RuntimeError(
                "projected edge may vanish "
                f"strict={float(strict_lower-SUPPORT_ERROR):.6g}")
        # `u·(K-Q) = -orientation`; its certified maximum is the support
        # defect consumed by the balanced-support-with-defect theorem.
        total_defect += max(-(ball[0]-ball[1])
                            for ball in supports) + SUPPORT_ERROR
        balls = [cayley_edge_contact_ball(view, variables, q0, q1, p)
                 for p in range(24)]
        inner = max(range(24), key=lambda p: balls[p][0]-balls[p][1])
        contact_polys = cayley_edge_contact_qpolys(q0, q1, inner)
        total_polys = [qpoly_add(a, b)
                       for a, b in zip(total_polys, contact_polys)]
        contacts.append({"outer_index": q0, "next_outer_index": q1,
                         "inner_index": inner,
                         "nonzero_witness": witness,
                         "ball": balls[inner]})
    component_balls = [qpoly_eval_centered(poly, (x, y, z), (ex, ey, ez))
                       for poly in total_polys]
    total = ball_dot(view, component_balls)
    # The polynomial is denominator-cleared.  Charge every support defect
    # at the maximum Cayley denominator over the whole box.
    endpoints = [(x-ex, x+ex), (y-ey, y+ey), (z-ez, z+ez)]
    d_bound = Q(1) + sum(max(abs(lo), abs(hi))**2
                         for lo, hi in endpoints)
    error = len(cycle) * 10 * d_bound * KAPPA
    lower = total[0]-total[1]-d_bound*total_defect-error
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
            "cayley_d_bound": d_bound,
            "displacement_ball": total,
            "error": error,
            "lower_bound": lower,
            **cycle_diagnostics,
        },
    }


def simplex_edge_smoke(relative_center, relative_half_widths, triangle,
                       cycle=None, inner_indices=None):
    """Certify one relative Cayley box uniformly over a view triangle.

    The triangle vertices are rational nonnegative vectors whose coordinates
    sum to one.  All support and displacement expressions are linear in the
    projective view vector, so their extrema occur at triangle vertices.
    Floating geometry selects witnesses only; every accepted inequality below
    is exact rational arithmetic matching the intended Lean checker.
    """
    if any(any(q < 0 for q in view) or sum(view, Q(0)) != 1
           for view in triangle):
        raise ValueError("view triangle is not in the projective simplex")
    centroid = [sum((view[i] for view in triangle), Q(0))/len(triangle)
                for i in range(3)]
    if cycle is None:
        cycle = silhouette_cycle_for_view(centroid)
    x, y, z = relative_center
    ex, ey, ez = relative_half_widths
    contacts = []
    total_polys = [qpoly_zero(), qpoly_zero(), qpoly_zero()]
    total_defect = Q(0)
    minimum_strict = None
    variables = (x, y, z)
    radii = (ex, ey, ez)
    for index, q0 in enumerate(cycle):
        q1 = cycle[(index+1) % len(cycle)]
        support_values = [
            [edge_orientation_q(view, q0, q1, q) for q in range(24)]
            for view in triangle]
        # One witness must keep the moving projected edge nonzero throughout
        # the triangle.  Linearity makes the minimum occur at a vertex.
        witness_scores = [min(row[q] for row in support_values)
                          for q in range(24)]
        witness = max(range(24), key=lambda q: witness_scores[q])
        strict_lower = witness_scores[witness] - SUPPORT_ERROR
        if strict_lower <= 0:
            raise RuntimeError(
                f"simplex projected edge may vanish strict={float(strict_lower):.6g}")
        minimum_strict = (strict_lower if minimum_strict is None else
                          min(minimum_strict, strict_lower))
        # `u·(K-Q) = -orientation`; include the exact-vertex allowance.
        total_defect += max(-value for row in support_values for value in row) \
            + SUPPORT_ERROR

        if inner_indices is None:
            best_inner = None
            for inner in range(24):
                polynomials = cayley_edge_contact_qpolys(q0, q1, inner)
                component_balls = [qpoly_eval_centered(poly, variables, radii)
                                   for poly in polynomials]
                lower = min(qdot(view, [ball[0] for ball in component_balls]) -
                            qdot(view, [ball[1] for ball in component_balls])
                            for view in triangle)
                if best_inner is None or lower > best_inner[0]:
                    best_inner = (lower, inner, polynomials)
            _, inner, polynomials = best_inner
        else:
            inner = inner_indices[index]
            polynomials = cayley_edge_contact_qpolys(q0, q1, inner)
        total_polys = [qpoly_add(a, b)
                       for a, b in zip(total_polys, polynomials)]
        contacts.append({"outer_index": q0,
                         "next_outer_index": q1,
                         "inner_index": inner,
                         "nonzero_witness": witness})

    component_balls = [qpoly_eval_centered(poly, variables, radii)
                       for poly in total_polys]
    displacement_lowers = [
        qdot(view, [ball[0] for ball in component_balls]) -
        qdot(view, [ball[1] for ball in component_balls])
        for view in triangle]
    endpoints = [(c-e, c+e) for c, e in zip(variables, radii)]
    d_bound = Q(1) + sum(max(abs(lo), abs(hi))**2
                         for lo, hi in endpoints)
    error = len(cycle) * 10 * d_bound * KAPPA
    lower = min(displacement_lowers) - d_bound*total_defect - error
    if lower < 0:
        raise RuntimeError(
            f"simplex edge displacement fails by {-float(lower):.6g}")
    return {
        "relative_center": relative_center,
        "relative_half_widths": relative_half_widths,
        "triangle": triangle,
        "cycle": cycle,
        "contacts": contacts,
        "diagnostics": {
            "edge_count": len(cycle),
            "minimum_strict_support_lower": minimum_strict,
            "total_support_defect": total_defect,
            "cayley_d_bound": d_bound,
            "displacement_lowers": displacement_lowers,
            "error": error,
            "lower_bound": lower,
        },
    }


@functools.lru_cache(maxsize=None)
def cayley_edge_contact_qpolys_float(q0, q1, inner_index):
    return np.asarray(cayley_edge_contact_qpolys(q0, q1, inner_index),
                      dtype=float)


@functools.lru_cache(maxsize=None)
def cayley_edge_all_contact_qpolys_float(q0, q1):
    """All inner-contact polynomials for one oriented edge.

    Tree profiling visits the same few silhouette edges at thousands of view
    and Cayley cells.  Cache the already-stacked dense array rather than
    rebuilding it from 24 separately cached rows at every node.
    """
    return np.asarray([
        cayley_edge_contact_qpolys_float(q0, q1, inner)
        for inner in range(24)])


@functools.lru_cache(maxsize=None)
def edge_cross_all_float(q0, q1):
    return np.asarray([
        [float(q) for q in edge_cross_q(q0, q1, k)]
        for k in range(24)])


def qpoly_eval_centered_float(coefficients, centers, radii):
    """Vectorized floating version of the exact quadratic ball evaluator."""
    c = np.asarray(coefficients)
    x, y, z = centers
    rx, ry, rz = radii
    monomials = np.asarray([1, x, y, z, x*x, x*y, x*z, y*y, y*z, z*z])
    value = c @ monomials
    gradient = np.stack((
        c[..., 1] + 2*c[..., 4]*x + c[..., 5]*y + c[..., 6]*z,
        c[..., 2] + c[..., 5]*x + 2*c[..., 7]*y + c[..., 8]*z,
        c[..., 3] + c[..., 6]*x + c[..., 8]*y + 2*c[..., 9]*z), axis=-1)
    linear_radius = np.sum(np.abs(gradient) * np.asarray(radii), axis=-1)
    quadratic_radius = (
        np.abs(c[..., 4])*rx*rx + np.abs(c[..., 5])*rx*ry +
        np.abs(c[..., 6])*rx*rz + np.abs(c[..., 7])*ry*ry +
        np.abs(c[..., 8])*ry*rz + np.abs(c[..., 9])*rz*rz)
    return value, linear_radius + quadratic_radius


def simplex_edge_float_screen(relative_center, relative_half_widths,
                              triangle, cycle=None, optimize_contacts=True):
    """Fast witness selection and rejection before exact rational checking.

    A positive result is only a heuristic: accepted leaves are always rerun
    through ``simplex_edge_smoke``.  A comfortably negative result saves the
    far more expensive Fraction computation at internal subdivision nodes.
    """
    views = np.asarray([[float(q) for q in view] for view in triangle])
    centroid = np.mean(views, axis=0)
    if cycle is None:
        cycle = silhouette_cycle_for_view(centroid)
    centers = np.asarray([float(q) for q in relative_center])
    radii = np.asarray([float(q) for q in relative_half_widths])
    total_polys = np.zeros((3, 10))
    total_defect = 0.0
    minimum_strict = math.inf
    witnesses = []
    choices = []
    edge_polys = []
    for index, q0 in enumerate(cycle):
        q1 = cycle[(index+1) % len(cycle)]
        crosses = edge_cross_all_float(q0, q1)
        support_values = views @ crosses.T
        witness_scores = np.min(support_values, axis=0)
        witness = int(np.argmax(witness_scores))
        strict = witness_scores[witness] - float(SUPPORT_ERROR)
        minimum_strict = min(minimum_strict, strict)
        total_defect += float(np.max(-support_values)) + float(SUPPORT_ERROR)

        all_polys = cayley_edge_all_contact_qpolys_float(q0, q1)
        value, radius = qpoly_eval_centered_float(
            all_polys, centers, radii)
        # Shape is (inner vertex, vector component).  Dot each component ball
        # with each projective triangle vertex and retain the worst vertex.
        lower = np.min(views @ value.T - views @ radius.T, axis=0)
        inner = int(np.argmax(lower))
        total_polys += all_polys[inner]
        choices.append(inner)
        witnesses.append(witness)
        edge_polys.append(all_polys)

    if optimize_contacts:
        # Coordinate descent chooses contacts for the radius of the *summed*
        # polynomial, retaining cancellations that independent edge choices
        # can destroy.
        for _ in range(2):
            changed = False
            for edge_index, all_polys in enumerate(edge_polys):
                base = total_polys - all_polys[choices[edge_index]]
                candidate_polys = all_polys + base[None, :, :]
                value, radius = qpoly_eval_centered_float(
                    candidate_polys, centers, radii)
                lower = np.min(views @ value.T - views @ radius.T, axis=0)
                inner = int(np.argmax(lower))
                if inner != choices[edge_index]:
                    total_polys = base + all_polys[inner]
                    choices[edge_index] = inner
                    changed = True
            if not changed:
                break

    value, radius = qpoly_eval_centered_float(total_polys, centers, radii)
    displacement_lower = float(np.min(views @ value - views @ radius))
    endpoint_abs = np.maximum(np.abs(centers-radii), np.abs(centers+radii))
    d_bound = 1 + float(np.sum(endpoint_abs**2))
    error = len(cycle) * 10 * d_bound * float(KAPPA)
    lower = displacement_lower - d_bound*total_defect - error
    return {"cycle": cycle,
            "contacts": list(zip(choices, witnesses)),
            "inner_indices": choices,
            "minimum_strict_support_lower": minimum_strict,
            "lower_bound": lower}


def screened_simplex_edge_smoke(relative_center, relative_half_widths,
                                triangle, cycle=None):
    """Exact certificate search with a sound-use-only floating prefilter."""
    screen = simplex_edge_float_screen(
        relative_center, relative_half_widths, triangle, cycle)
    # Near zero we still ask exact arithmetic.  Only clearly failed internal
    # nodes are rejected from floating arithmetic alone.
    if screen["minimum_strict_support_lower"] < -1e-7:
        raise RuntimeError(
            "simplex projected edge may vanish "
            f"strict={screen['minimum_strict_support_lower']:.6g}")
    if screen["lower_bound"] < -1e-7:
        raise RuntimeError(
            "simplex edge displacement fails by "
            f"{-screen['lower_bound']:.6g}")
    return simplex_edge_smoke(
        relative_center, relative_half_widths, triangle, screen["cycle"],
        screen["inner_indices"])


def split_simplex_triangle(triangle):
    a, b, c = triangle
    ab = [(x+y)/2 for x, y in zip(a, b)]
    bc = [(x+y)/2 for x, y in zip(b, c)]
    ca = [(x+y)/2 for x, y in zip(c, a)]
    return [(a, ab, ca), (ab, b, bc), (ca, bc, c), (ab, bc, ca)]


def simplex_edge_cover(relative_center, relative_half_widths, max_depth,
                       optimized_count=0, outer_chamber=False):
    """Adaptively cover the projective view simplex or symmetry chamber."""
    e0 = (Q(1), Q(0), Q(0))
    e1 = (Q(0), Q(1), Q(0))
    e2 = (Q(0), Q(0), Q(1))
    if outer_chamber:
        m01 = (Q(1, 2), Q(1, 2), Q(0))
        m02 = (Q(1, 2), Q(0), Q(1, 2))
        center = (Q(1, 3), Q(1, 3), Q(1, 3))
        roots = [(e0, m01, center), (e0, center, m02)]
    else:
        roots = [(e0, e1, e2)]
    stack = [(root, 0) for root in roots]
    leaves = []
    failures = []
    optimized_leaves = 0
    nodes = 0
    while stack:
        triangle, depth = stack.pop()
        nodes += 1
        try:
            leaves.append(screened_simplex_edge_smoke(
                relative_center, relative_half_widths, triangle))
            continue
        except RuntimeError as exc:
            if depth == max_depth:
                if optimized_count:
                    centroid = [sum((view[i] for view in triangle), Q(0))/3
                                for i in range(3)]
                    for cycle, _ in best_edge_cycles_for_view(
                            relative_center, centroid, 4, optimized_count):
                        try:
                            leaves.append(screened_simplex_edge_smoke(
                                relative_center, relative_half_widths,
                                triangle, cycle))
                            optimized_leaves += 1
                            break
                        except RuntimeError:
                            pass
                    else:
                        failures.append({"triangle": triangle,
                                         "reason": str(exc)})
                    continue
                failures.append({"triangle": triangle, "reason": str(exc)})
                continue
        for child in split_simplex_triangle(triangle):
            stack.append((child, depth+1))
    return {"relative_center": relative_center,
            "relative_half_widths": relative_half_widths,
            "max_depth": max_depth, "nodes": nodes,
            "outer_chamber": outer_chamber,
            "optimized_leaves": optimized_leaves,
            "leaves": leaves, "failures": failures}


def cayley_edge_profile(half_width: Q, samples: int,
                        denominator: int, seed: int):
    """Profile exact prune/edge coverage on uniformly sampled root boxes."""
    root = [(Q(0), Q(2)), (Q(0), Q(2)),
            (Q(-2), Q(2)), (Q(-2), Q(2)), (Q(-2), Q(2))]
    rng = random.Random(seed)
    counts = {"prune": 0, "edge": 0, "uncovered": 0}
    failures = {}
    uncovered = []
    edge_slacks = []
    for _ in range(samples):
        center = []
        for lo, hi in root:
            ilo = math.ceil(float((lo + half_width) * denominator))
            ihi = math.floor(float((hi - half_width) * denominator))
            center.append(Q(rng.randint(ilo, ihi), denominator))
        widths = [half_width] * 5
        prune = cayley_prune_box(center[2:], widths[2:])
        if prune["lower_bound"] > 0:
            counts["prune"] += 1
            continue
        try:
            edge = cayley_edge_smoke(center, widths)
        except RuntimeError as exc:
            counts["uncovered"] += 1
            reason = str(exc).split("=")[0].strip()
            failures[reason] = failures.get(reason, 0) + 1
            if len(uncovered) < 20:
                uncovered.append({"center": center, "reason": str(exc)})
            continue
        counts["edge"] += 1
        edge_slacks.append(float(edge["diagnostics"]["lower_bound"]))
    quantiles = ([float(x) for x in np.quantile(
        edge_slacks, [.01, .1, .5, .9])]
        if edge_slacks else [])
    return {
        "half_width": half_width,
        "samples": samples,
        "counts": counts,
        "fractions": {key: value/samples for key, value in counts.items()},
        "edge_slack_quantiles_01_10_50_90": quantiles,
        "failure_counts": failures,
        "uncovered_examples": uncovered,
    }


def cayley_edge_domain_profile(angle_half_width: Q,
                               relative_half_width: Q, samples: int,
                               denominator: int, seed: int,
                               try_local: bool = False):
    """Profile edge certificates conditioned on boxes not already pruned."""
    root = [(Q(0), Q(2)), (Q(0), Q(2)),
            (Q(-2), Q(2)), (Q(-2), Q(2)), (Q(-2), Q(2))]
    rng = random.Random(seed)
    attempts = 0
    covered_count = 0
    silhouette_count = 0
    optimized_count = 0
    local_count = 0
    failures = {}
    uncovered = []
    slacks = []
    while covered_count + len(uncovered) < samples:
        attempts += 1
        center = []
        for lo, hi in root:
            width = (angle_half_width if len(center) < 2
                     else relative_half_width)
            ilo = math.ceil(float((lo + width) * denominator))
            ihi = math.floor(float((hi - width) * denominator))
            center.append(Q(rng.randint(ilo, ihi), denominator))
        widths = [angle_half_width] * 2 + [relative_half_width] * 3
        if cayley_prune_box(center[2:], widths[2:])["lower_bound"] > 0:
            continue
        try:
            edge = cayley_edge_smoke(center, widths)
            silhouette_count += 1
        except RuntimeError:
            try:
                edge = cayley_edge_smoke(
                    center, widths, cycle_search_length=4)
                optimized_count += 1
            except RuntimeError as exc:
                if try_local:
                    try:
                        cayley_local_smoke(center, widths, 48, 10**6)
                        local_count += 1
                        covered_count += 1
                        continue
                    except RuntimeError:
                        pass
                reason = str(exc).split("=")[0].strip()
                failures[reason] = failures.get(reason, 0) + 1
                if len(uncovered) < samples:
                    uncovered.append({"center": center,
                                      "reason": str(exc)})
                continue
        covered_count += 1
        slacks.append(float(edge["diagnostics"]["lower_bound"]))
    return {
        "angle_half_width": angle_half_width,
        "relative_half_width": relative_half_width,
        "domain_samples": samples,
        "raw_attempts": attempts,
        "covered": covered_count,
        "silhouette_edge": silhouette_count,
        "optimized_edge": optimized_count,
        "local": local_count,
        "covered_fraction": covered_count/samples,
        "edge_slack_quantiles_01_10_50_90":
            ([float(x) for x in np.quantile(slacks, [.01, .1, .5, .9])]
             if slacks else []),
        "failure_counts": failures,
        "uncovered_examples": uncovered[:20],
    }


def cayley_relative_prune_tree(target_half_width: Q):
    """Count a dyadic 3D tree after exact fundamental-domain pruning."""
    stack = [([Q(0), Q(0), Q(0)], [Q(2), Q(2), Q(2)], 0)]
    nodes = 0
    pruned = 0
    retained = 0
    max_depth = 0
    retained_centers = []
    while stack:
        center, widths, depth = stack.pop()
        nodes += 1
        max_depth = max(max_depth, depth)
        if cayley_prune_box(center, widths)["lower_bound"] > 0:
            pruned += 1
            continue
        coordinate = max(range(3), key=lambda i: widths[i])
        if widths[coordinate] <= target_half_width:
            retained += 1
            if len(retained_centers) < 20:
                retained_centers.append(center)
            continue
        child_widths = list(widths)
        child_widths[coordinate] /= 2
        for sign in (-1, 1):
            child_center = list(center)
            child_center[coordinate] += sign*child_widths[coordinate]
            stack.append((child_center, child_widths, depth+1))
    return {"target_half_width": target_half_width,
            "nodes": nodes, "pruned_leaves": pruned,
            "retained_leaves": retained, "max_depth": max_depth,
            "retained_examples": retained_centers}


def projective_mixed_profile(coarse_half_width: Q, target_half_width: Q,
                             base_view_depth: int, max_view_depth: int,
                             optimized_count: int, max_nodes: int):
    """Count a joint relative-Cayley/projective-view adaptive tree.

    This is a fast floating exploration, not certificate data.  Every future
    accepted Lean leaf must still pass ``simplex_edge_smoke`` exactly.  The
    profile first shares fundamental-domain pruning down to a coarse relative
    scale.  Only retained boxes open the two chamber triangles; hard triangle
    cells then alternate view and relative subdivision.
    """
    e0 = (Q(1), Q(0), Q(0))
    m01 = (Q(1, 2), Q(1, 2), Q(0))
    m02 = (Q(1, 2), Q(0), Q(1, 2))
    center_view = (Q(1, 3), Q(1, 3), Q(1, 3))
    roots = [(e0, m01, center_view), (e0, center_view, m02)]
    counts = {"nodes": 0, "relative_splits": 0, "view_roots": 0,
              "view_splits": 0, "prune_leaves": 0,
              "projective_leaves": 0, "optimized_leaves": 0,
              "uncovered_leaves": 0}
    exact_audit = {"attempted": 0, "passed": 0, "failed": 0}
    gaps = []
    accepted_widths = []

    class NodeLimit(RuntimeError):
        pass

    def node(kind):
        counts["nodes"] += 1
        if counts["nodes"] > max_nodes:
            raise NodeLimit
        counts[kind] += 1

    def split_relative(center, widths, triangle, view_depth):
        coordinate = max(range(3), key=lambda i: widths[i])
        child_widths = list(widths)
        child_widths[coordinate] /= 2
        node("relative_splits")
        for sign in (-1, 1):
            child_center = list(center)
            child_center[coordinate] += sign*child_widths[coordinate]
            if cayley_prune_box(child_center, child_widths)["lower_bound"] > 0:
                node("prune_leaves")
            else:
                explore_triangle(child_center, child_widths,
                                 triangle, view_depth)

    def explore_triangle(center, widths, triangle, view_depth):
        screen = simplex_edge_float_screen(center, widths, triangle)
        if (screen["minimum_strict_support_lower"] > 1e-7 and
                screen["lower_bound"] > 1e-7):
            node("projective_leaves")
            accepted_widths.append(max(widths))
            # A small deterministic exact audit catches drift between the
            # floating screen and the executable rational checker.
            if exact_audit["attempted"] < 25:
                exact_audit["attempted"] += 1
                try:
                    simplex_edge_smoke(center, widths, triangle,
                                       screen["cycle"],
                                       screen["inner_indices"])
                    exact_audit["passed"] += 1
                except RuntimeError:
                    exact_audit["failed"] += 1
            return
        if view_depth < base_view_depth:
            node("view_splits")
            for child in split_simplex_triangle(triangle):
                explore_triangle(center, widths, child, view_depth+1)
            return
        if max(widths) > target_half_width:
            split_relative(center, widths, triangle, view_depth)
            return
        if view_depth < max_view_depth:
            node("view_splits")
            for child in split_simplex_triangle(triangle):
                explore_triangle(center, widths, child, view_depth+1)
            return
        if optimized_count:
            centroid = [sum((view[i] for view in triangle), Q(0))/3
                        for i in range(3)]
            for cycle, _ in best_edge_cycles_for_view(
                    center, centroid, 4, optimized_count):
                candidate = simplex_edge_float_screen(
                    center, widths, triangle, cycle)
                if (candidate["minimum_strict_support_lower"] > 1e-7 and
                        candidate["lower_bound"] > 1e-7):
                    node("optimized_leaves")
                    accepted_widths.append(max(widths))
                    return
        node("uncovered_leaves")
        if len(gaps) < 20:
            gaps.append({"center": list(center), "half_widths": list(widths),
                         "triangle": triangle, "view_depth": view_depth,
                         "strict": screen["minimum_strict_support_lower"],
                         "lower_bound": screen["lower_bound"]})

    def pre_prune(center, widths):
        if cayley_prune_box(center, widths)["lower_bound"] > 0:
            node("prune_leaves")
            return
        if max(widths) > coarse_half_width:
            coordinate = max(range(3), key=lambda i: widths[i])
            child_widths = list(widths)
            child_widths[coordinate] /= 2
            node("relative_splits")
            for sign in (-1, 1):
                child_center = list(center)
                child_center[coordinate] += sign*child_widths[coordinate]
                pre_prune(child_center, child_widths)
            return
        node("view_roots")
        for triangle in roots:
            explore_triangle(center, widths, triangle, 0)

    halted = False
    try:
        pre_prune([Q(0), Q(0), Q(0)], [Q(2), Q(2), Q(2)])
    except NodeLimit:
        halted = True
    width_frequencies = {}
    for width in accepted_widths:
        key = str(width)
        width_frequencies[key] = width_frequencies.get(key, 0) + 1
    return {"coarse_half_width": coarse_half_width,
            "target_half_width": target_half_width,
            "base_view_depth": base_view_depth,
            "max_view_depth": max_view_depth,
            "optimized_count": optimized_count,
            "max_nodes": max_nodes, "halted_at_node_limit": halted,
            "counts": counts, "exact_audit": exact_audit,
            "accepted_width_frequencies": width_frequencies,
            "gap_examples": gaps}


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
    if np is not None and isinstance(x, np.integer):
        return int(x)
    return x


def lean_rational(value):
    return f"({value.numerator} / {value.denominator} : ℚ)"


def lean_tribonacci_expr(value):
    return (f"⟨{lean_rational(value[0])}, {lean_rational(value[1])}, "
            f"{lean_rational(value[2])}⟩")


def emit_guarded_lower_lean():
    """Emit the exact full lower-piece Bernstein table as a Lean module."""
    certificate = transition_guarded_piece_polynomials()
    root = [(Q(0), Q(1, 1000)), (Q(0), Q(2)), (Q(0), Q(1)),
            (Q(-16), Q(16)), (Q(-16), Q(16))]
    degrees, coefficients = epoly_bernstein_coefficients(
        certificate["lowerCombination"], root)
    if degrees != (4, 4, 2, 2, 2):
        raise AssertionError(f"unexpected lower degrees: {degrees}")
    coefficient_values = [lean_tribonacci_expr(coefficients[index])
                          for index in sorted(coefficients)]
    chunks = [coefficient_values[start:start+27]
              for start in range(0, len(coefficient_values), 27)]
    chunk_definitions = "\n\n".join(
        f"def lowerCoefficientChunk{index} : Array TribonacciExpr := #[\n  " +
        ",\n  ".join(chunk) + "\n]"
        for index, chunk in enumerate(chunks))
    chunk_names = ", ".join(
        f"lowerCoefficientChunk{index}" for index in range(len(chunks)))
    return f'''module

public import Noperthedron.SnubCube.ProjectiveTransitionGuarded
public meta import Noperthedron.SnubCube.ProjectiveTransitionGuarded

@[expose] public section

namespace Noperthedron.SnubCube.ProjectiveTransitionGuardedGenerated

open BernsteinCertificate
open ProjectiveTransitionGuarded
open SparseTribonacciPolynomial

{chunk_definitions}

def lowerCoefficientChunks : List (Array TribonacciExpr) :=
  [{chunk_names}]

def lowerFlatIndex (index : Fin 5 → Nat) : Nat :=
  index 0 * 135 + index 1 * 27 + index 2 * 9 + index 3 * 3 + index 4

def lowerCoefficient (index : Fin 5 → Nat) : TribonacciExpr :=
  let flat := lowerFlatIndex index
  (lowerCoefficientChunks.getD (flat / 27) #[]).getD (flat % 27) 0

def lowerIndices : List (Fin 5 → Nat) :=
  (List.range 5).flatMap fun i0 =>
  (List.range 5).flatMap fun i1 =>
  (List.range 3).flatMap fun i2 =>
  (List.range 3).flatMap fun i3 =>
  (List.range 3).map fun i4 => ![i0, i1, i2, i3, i4]

def lowerTable : Table 5 where
  degrees := ![4, 4, 2, 2, 2]
  coefficient := lowerCoefficient
  indices := lowerIndices

def lowerCenters : Fin 5 → ℚ := ![1 / 2000, 1, 1 / 2, 0, 0]
def lowerRadii : Fin 5 → ℚ := ![1 / 2000, 1, 1 / 2, 16, 16]
def lowerRecentered : Polynomial 5 :=
  recenter lowerCenters lowerRadii lowerCombination

theorem lower_complete_native : lowerTable.Complete := by native_decide
theorem lower_valid_kernel : lowerTable.LowerValid 0 := by decide +kernel
theorem lower_valid_native : lowerTable.LowerValid 0 := by native_decide

-- The production module will use the sparse power-to-Bernstein identity
-- checker rather than expanding `lowerTable.toPolynomial` here.  Direct
-- normalization is correct but needlessly expensive for this tensor.

end Noperthedron.SnubCube.ProjectiveTransitionGuardedGenerated

end
'''


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
    cayley_edge_parser.add_argument("--cycle-search-length", type=int,
                                    default=0)
    edge_profile_parser = sub.add_parser("cayley-edge-profile")
    edge_profile_parser.add_argument("--half-width", default="1/100")
    edge_profile_parser.add_argument("--samples", type=int, default=100)
    edge_profile_parser.add_argument("--denominator", type=int, default=10000)
    edge_profile_parser.add_argument("--seed", type=int, default=1)
    edge_domain_parser = sub.add_parser("cayley-edge-domain-profile")
    edge_domain_parser.add_argument("--angle-half-width", default="1/100")
    edge_domain_parser.add_argument("--relative-half-width", default="1/100")
    edge_domain_parser.add_argument("--samples", type=int, default=100)
    edge_domain_parser.add_argument("--denominator", type=int, default=10000)
    edge_domain_parser.add_argument("--seed", type=int, default=1)
    edge_domain_parser.add_argument("--try-local", action="store_true")
    relative_tree_parser = sub.add_parser("cayley-relative-prune-tree")
    relative_tree_parser.add_argument("--target-half-width", default="1/32")
    simplex_edge_parser = sub.add_parser("simplex-edge-smoke")
    simplex_edge_parser.add_argument(
        "--center", default="1/5,1/10,0",
        help="x,y,z as comma-separated rationals")
    simplex_edge_parser.add_argument(
        "--half-widths", default="1/100,1/100,1/100",
        help="three comma-separated rational half-widths")
    simplex_edge_parser.add_argument("--max-depth", type=int, default=4)
    simplex_edge_parser.add_argument("--optimized-count", type=int, default=0)
    simplex_edge_parser.add_argument("--outer-chamber", action="store_true")
    mixed_profile_parser = sub.add_parser("projective-mixed-profile")
    mixed_profile_parser.add_argument("--coarse-half-width", default="1/16")
    mixed_profile_parser.add_argument("--target-half-width", default="1/128")
    mixed_profile_parser.add_argument("--base-view-depth", type=int, default=3)
    mixed_profile_parser.add_argument("--max-view-depth", type=int, default=5)
    mixed_profile_parser.add_argument("--optimized-count", type=int, default=4)
    mixed_profile_parser.add_argument("--max-nodes", type=int, default=100000)
    projective_local_parser = sub.add_parser("projective-local-smoke")
    projective_local_parser.add_argument(
        "--view", default="3/5,3/20,1/4",
        help="three positive simplex coordinates")
    projective_local_parser.add_argument("--triangle-width", default="1/100000")
    projective_local_cover_parser = sub.add_parser("projective-local-cover")
    projective_local_cover_parser.add_argument("--max-depth", type=int,
                                               default=5)
    projective_local_cover_parser.add_argument("--exact-audit-limit", type=int,
                                               default=25)
    sub.add_parser("projective-transition-profile")
    transition_blowup_parser = sub.add_parser(
        "projective-transition-blowup-profile")
    transition_blowup_parser.add_argument("--samples", type=int, default=5000)
    transition_blowup_parser.add_argument("--seed", type=int, default=1)
    sub.add_parser("projective-transition-box-probe")
    transition_cover_parser = sub.add_parser(
        "projective-transition-box-cover")
    transition_cover_parser.add_argument("--max-nodes", type=int,
                                         default=20000)
    transition_cover_parser.add_argument("--max-depth", type=int, default=100)
    guarded_cover_parser = sub.add_parser(
        "projective-transition-guarded-cover")
    guarded_cover_parser.add_argument("--max-nodes", type=int, default=5000)
    guarded_cover_parser.add_argument("--max-depth", type=int, default=100)
    guarded_cover_parser.add_argument("--threshold", default="0")
    guarded_family_parser = sub.add_parser(
        "projective-transition-guarded-family-cover")
    guarded_family_parser.add_argument("--max-nodes", type=int, default=5000)
    guarded_family_parser.add_argument("--max-depth", type=int, default=100)
    guarded_family_parser.add_argument("--threshold", default="0")
    guarded_middle_parser = sub.add_parser(
        "projective-transition-guarded-middle-cover")
    guarded_middle_parser.add_argument("--max-nodes", type=int, default=5000)
    guarded_middle_parser.add_argument("--max-depth", type=int, default=100)
    guarded_middle_parser.add_argument("--polar", action="store_true")
    guarded_middle_parser.add_argument("--iterated", action="store_true")
    guarded_middle_profile_parser = sub.add_parser(
        "projective-transition-guarded-middle-profile")
    guarded_middle_profile_parser.add_argument(
        "--chart", choices=("rectangular", "polar", "iterated"),
        default="iterated")
    guarded_middle_profile_parser.add_argument(
        "--samples", type=int, default=100000)
    guarded_middle_profile_parser.add_argument("--seed", type=int, default=1)
    guarded_middle_combination_parser = sub.add_parser(
        "projective-transition-guarded-middle-combination")
    guarded_middle_combination_parser.add_argument(
        "--chart", choices=("rectangular", "polar", "iterated"),
        default="iterated")
    guarded_middle_combination_parser.add_argument(
        "--iterations", type=int, default=5000)
    guarded_middle_float_parser = sub.add_parser(
        "projective-transition-guarded-middle-float-cover")
    guarded_middle_float_parser.add_argument(
        "--chart", choices=("rectangular", "polar", "iterated"),
        default="iterated")
    guarded_middle_float_parser.add_argument(
        "--max-nodes", type=int, default=10000)
    guarded_middle_float_parser.add_argument(
        "--max-depth", type=int, default=80)
    sub.add_parser("projective-transition-gap-profile")
    farkas_parser = sub.add_parser("projective-transition-farkas-search")
    farkas_parser.add_argument("--d", type=float, default=.0009525383113968972)
    farkas_parser.add_argument("--e", type=float, default=0.0)
    farkas_parser.add_argument("--a", type=float, default=5.9032002193099125)
    farkas_parser.add_argument("--b", type=float, default=-14.874129731767692)
    farkas_parser.add_argument("--ratio", type=float, default=6.830650718887462)
    sub.add_parser("projective-transition-guarded-lower-lean")
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
        print(json.dumps(qjson(cayley_edge_smoke(
            center, half_widths,
            cycle_search_length=args.cycle_search_length)),
                         indent=2))
    elif args.command == "cayley-edge-profile":
        result = cayley_edge_profile(
            Q(args.half_width), args.samples, args.denominator, args.seed)
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "cayley-edge-domain-profile":
        result = cayley_edge_domain_profile(
            Q(args.angle_half_width), Q(args.relative_half_width),
            args.samples, args.denominator, args.seed, args.try_local)
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "cayley-relative-prune-tree":
        result = cayley_relative_prune_tree(Q(args.target_half_width))
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "simplex-edge-smoke":
        center = [Q(x) for x in args.center.split(",")]
        half_widths = [Q(x) for x in args.half_widths.split(",")]
        if len(center) != 3 or len(half_widths) != 3:
            parser.error("center and half-widths must each have three entries")
        result = simplex_edge_cover(center, half_widths, args.max_depth,
                                    args.optimized_count, args.outer_chamber)
        summary = {key: value for key, value in result.items()
                   if key not in ("leaves", "failures")}
        summary["certified_leaves"] = len(result["leaves"])
        summary["uncovered_leaves"] = len(result["failures"])
        summary["failure_examples"] = result["failures"][:10]
        print(json.dumps(qjson(summary), indent=2))
    elif args.command == "projective-mixed-profile":
        result = projective_mixed_profile(
            Q(args.coarse_half_width), Q(args.target_half_width),
            args.base_view_depth, args.max_view_depth, args.optimized_count,
            args.max_nodes)
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "projective-local-smoke":
        view = [Q(x) for x in args.view.split(",")]
        if len(view) != 3:
            parser.error("view must have three comma-separated entries")
        result = projective_local_smoke(view, Q(args.triangle_width))
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "projective-local-cover":
        result = projective_local_cover(args.max_depth,
                                        args.exact_audit_limit)
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "projective-transition-profile":
        result = projective_transition_profile()
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "projective-transition-blowup-profile":
        result = projective_transition_blowup_profile(args.samples, args.seed)
        print(json.dumps(qjson(result), indent=2))
    elif args.command == "projective-transition-box-probe":
        print(json.dumps(qjson(transition_box_probe()), indent=2))
    elif args.command == "projective-transition-box-cover":
        result = transition_box_cover(args.max_nodes, args.max_depth)
        summary = {key: value for key, value in result.items()
                   if key not in ("leaves", "failures")}
        summary["leaf_count"] = len(result["leaves"])
        summary["failure_count"] = len(result["failures"])
        summary["failure_examples"] = result["failures"][:3]
        print(json.dumps(qjson(summary), indent=2))
    elif args.command == "projective-transition-guarded-cover":
        result = transition_guarded_bernstein_cover(
            args.max_nodes, args.max_depth, Q(args.threshold))
        summary = {key: value for key, value in result.items()
                   if key not in ("leaves", "failures")}
        summary["leaf_count"] = len(result["leaves"])
        summary["failure_count"] = len(result["failures"])
        summary["failure_examples"] = result["failures"][:3]
        print(json.dumps(qjson(summary), indent=2))
    elif args.command == "projective-transition-guarded-family-cover":
        result = transition_guarded_family_cover(
            args.max_nodes, args.max_depth, Q(args.threshold))
        summary = {key: value for key, value in result.items()
                   if key not in ("leaves", "failures")}
        summary["leaf_count"] = len(result["leaves"])
        summary["failure_count"] = len(result["failures"])
        summary["failure_examples"] = result["failures"][:3]
        print(json.dumps(qjson(summary), indent=2))
    elif args.command == "projective-transition-guarded-middle-cover":
        result = transition_guarded_middle_cover(
            args.max_nodes, args.max_depth, args.polar, args.iterated)
        summary = {key: value for key, value in result.items()
                   if key not in ("leaves", "failures")}
        summary["leaf_count"] = len(result["leaves"])
        summary["failure_count"] = len(result["failures"])
        summary["failure_examples"] = result["failures"][:3]
        print(json.dumps(qjson(summary), indent=2))
    elif args.command == "projective-transition-guarded-middle-profile":
        print(json.dumps(transition_guarded_middle_profile(
            args.chart, args.samples, args.seed), indent=2))
    elif args.command == "projective-transition-guarded-middle-combination":
        print(json.dumps(transition_guarded_middle_combination_profile(
            args.chart, args.iterations), indent=2))
    elif args.command == "projective-transition-guarded-middle-float-cover":
        result = transition_guarded_middle_float_cover(
            args.chart, args.max_nodes, args.max_depth)
        summary = {key: value for key, value in result.items()
                   if key != "leaves"}
        print(json.dumps(qjson(summary), indent=2))
    elif args.command == "projective-transition-gap-profile":
        print(json.dumps(qjson(transition_family_gap_profile()), indent=2))
    elif args.command == "projective-transition-farkas-search":
        print(json.dumps(qjson(search_transition_farkas_family(
            args.d, args.e, args.a, args.b, args.ratio)), indent=2))
    elif args.command == "projective-transition-guarded-lower-lean":
        print(emit_guarded_lower_lean(), end="")


if __name__ == "__main__":
    main()
