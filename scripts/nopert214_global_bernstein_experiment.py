#!/usr/bin/env python3
"""Measure a tensor-Bernstein strengthening of Nopert #214 global leaves.

This is discovery code: it reconstructs the exact global displacement
polynomial in two Duffy coordinates for the projective triangle and three
unit-box coordinates for the relative Cayley interval.  Its 3^5 rational
Bernstein control coefficients give a correlation-preserving lower bound.
"""

import argparse
import itertools
import json
import math
import sys
from fractions import Fraction as Q

import nopert214_certificate_search as search


N = 5
ZERO = (0,) * N


def const(value):
    return {} if value == 0 else {ZERO: Q(value)}


def var(index):
    exponent = [0] * N
    exponent[index] = 1
    return {tuple(exponent): Q(1)}


def add(left, right):
    result = dict(left)
    for exponent, coefficient in right.items():
        result[exponent] = result.get(exponent, Q(0)) + coefficient
        if result[exponent] == 0:
            del result[exponent]
    return result


def scale(coefficient, polynomial):
    coefficient = Q(coefficient)
    return {exponent: coefficient * value
            for exponent, value in polynomial.items()
            if coefficient * value != 0}


def mul(left, right):
    result = {}
    for a, ca in left.items():
        for b, cb in right.items():
            exponent = tuple(x + y for x, y in zip(a, b))
            result[exponent] = result.get(exponent, Q(0)) + ca * cb
    return {exponent: coefficient for exponent, coefficient in result.items()
            if coefficient != 0}


def sum_polynomials(items):
    result = {}
    for item in items:
        result = add(result, item)
    return result


def affine(lo, width, coordinate):
    return add(const(lo), scale(width, var(coordinate)))


def qpoly_substitute(coefficients, x, y, z):
    c = list(map(Q, coefficients))
    return sum_polynomials((
        const(c[0]), scale(c[1], x), scale(c[2], y), scale(c[3], z),
        scale(c[4], mul(x, x)), scale(c[5], mul(x, y)),
        scale(c[6], mul(x, z)), scale(c[7], mul(y, y)),
        scale(c[8], mul(y, z)), scale(c[9], mul(z, z))))


def displacement_polynomial(chart, center, radii, triangle, candidate,
                            inner_indices, multiplier):
    u, v = var(0), var(1)
    uv = mul(u, v)
    n = []
    for coordinate in range(3):
        a = triangle[0][coordinate]
        bu = triangle[1][coordinate] - a
        cv = triangle[2][coordinate] - a
        n.append(sum_polynomials((const(a), scale(bu, u), scale(cv, v),
                                  scale(-cv, uv))))
    relative = [affine(c-r, 2*r, coordinate+2)
                for coordinate, (c, r) in
                enumerate(zip(center, radii))]
    edges = [search.projective_mixed_edge_q(contact)
             for contact in candidate["contacts"]]
    weight_coefficients = [search.cross3(edges[1], edges[2]),
                           search.cross3(edges[2], edges[0]),
                           search.cross3(edges[0], edges[1])]
    terms = []
    for i, (contact, edge, inner) in enumerate(
            zip(candidate["contacts"], edges, inner_indices)):
        contact_qpolys = search.atlas_mixed_contact_qpolys(
            chart, tuple(edge), inner, contact["vertex"])
        contact_components = [qpoly_substitute(q, *relative)
                              for q in contact_qpolys]
        weight = sum_polynomials(scale(a, component)
                                 for a, component in
                                 zip(weight_coefficients[i], n))
        contact_value = sum_polynomials(mul(component, view)
                                        for component, view in
                                        zip(contact_components, n))
        terms.append(mul(weight, contact_value))
    constraint = add(sum_polynomials(mul(value, value)
                                     for value in relative), const(-3))
    return add(sum_polynomials(terms), scale(multiplier, constraint))


def bernstein_lower(polynomial):
    degree = 2
    result = None
    for index in itertools.product(range(degree + 1), repeat=N):
        value = Q(0)
        for exponent, coefficient in polynomial.items():
            if any(power > selected
                   for power, selected in zip(exponent, index)):
                continue
            factor = Q(1)
            for selected, power in zip(index, exponent):
                factor *= Q(math.comb(selected, power),
                            math.comb(degree, power))
            value += coefficient * factor
        result = value if result is None else min(result, value)
    return result


def qpoly_add(left, right):
    return tuple(a + b for a, b in zip(left, right))


def qpoly_scale(coefficient, polynomial):
    return tuple(coefficient * value for value in polynomial)


def adjusted_qpoly_at_view(chart, view, candidate, inner_indices,
                           multiplier):
    edges = [search.projective_mixed_edge_q(contact)
             for contact in candidate["contacts"]]
    weight_coefficients = [search.cross3(edges[1], edges[2]),
                           search.cross3(edges[2], edges[0]),
                           search.cross3(edges[0], edges[1])]
    total = (Q(0),) * 10
    for i, (contact, edge, inner) in enumerate(
            zip(candidate["contacts"], edges, inner_indices)):
        components = search.atlas_mixed_contact_qpolys(
            chart, tuple(edge), inner, contact["vertex"])
        scalar = (Q(0),) * 10
        for coefficient, component in zip(view, components):
            scalar = qpoly_add(scalar, qpoly_scale(coefficient, component))
        weight = sum((a*b for a, b in
                      zip(view, weight_coefficients[i])), Q(0))
        total = qpoly_add(total, qpoly_scale(weight, scalar))
    constraint = (Q(-3), Q(0), Q(0), Q(0), Q(1), Q(0), Q(0),
                  Q(1), Q(0), Q(1))
    return qpoly_add(total, qpoly_scale(multiplier, constraint))


def relative_control(coefficients, centers, radii, indices):
    x, y, z = centers
    rx, ry, rz = radii
    lx, ly, lz = x-rx, y-ry, z-rz
    wx, wy, wz = 2*rx, 2*ry, 2*rz
    c = coefficients
    a0 = (c[0]+c[1]*lx+c[2]*ly+c[3]*lz+c[4]*lx*lx+
          c[5]*lx*ly+c[6]*lx*lz+c[7]*ly*ly+c[8]*ly*lz+
          c[9]*lz*lz)
    ax = wx*(c[1]+2*c[4]*lx+c[5]*ly+c[6]*lz)
    ay = wy*(c[2]+c[5]*lx+2*c[7]*ly+c[8]*lz)
    az = wz*(c[3]+c[6]*lx+c[8]*ly+2*c[9]*lz)
    axx, ayy, azz = c[4]*wx*wx, c[7]*wy*wy, c[9]*wz*wz
    axy, axz, ayz = c[5]*wx*wy, c[6]*wx*wz, c[8]*wy*wz
    i, j, k = indices
    u, v, w = Q(i, 2), Q(j, 2), Q(k, 2)
    return (a0+u*ax+v*ay+w*az+(axx if i == 2 else 0)+
            (ayy if j == 2 else 0)+(azz if k == 2 else 0)+
            u*v*axy+u*w*axz+v*w*ayz)


def simplex_bernstein_lower(chart, center, radii, triangle, candidate,
                            inner_indices, multiplier):
    corner_polynomials = [adjusted_qpoly_at_view(
        chart, view, candidate, inner_indices, multiplier)
        for view in triangle]
    midpoint_polynomials = {}
    for i in range(3):
        for j in range(i+1, 3):
            view = tuple((a+b)/2 for a, b in
                         zip(triangle[i], triangle[j]))
            midpoint_polynomials[(i, j)] = adjusted_qpoly_at_view(
                chart, view, candidate, inner_indices, multiplier)
    answer = None
    for relative_index in itertools.product(range(3), repeat=3):
        corner = [relative_control(q, center, radii, relative_index)
                  for q in corner_polynomials]
        controls = list(corner)
        for i in range(3):
            for j in range(i+1, 3):
                middle = relative_control(midpoint_polynomials[(i, j)],
                                          center, radii, relative_index)
                controls.append(2*middle-(corner[i]+corner[j])/2)
        value = min(controls)
        answer = value if answer is None else min(answer, value)
    return answer


def audit_state(chart, state):
    _, center, radii, root, triangle, depth = state
    center = tuple(map(Q, center))
    radii = tuple(map(Q, radii))
    triangle = tuple(tuple(map(Q, corner)) for corner in triangle)
    screen = search.atlas_projective_global_float_screen(
        chart, center, radii, triangle, candidate_limit=64)
    if screen is None:
        return {"depth": depth, "screen": None}
    exact = search.atlas_projective_global_triangle(
        chart, center, radii, root, triangle,
        selected_candidate=screen["candidate"])
    if exact is None:
        return {"depth": depth, "screen": screen["lower_bound"],
                "exact": None}
    polynomial = displacement_polynomial(
        chart, center, radii, triangle, screen["candidate"],
        exact["inner_index"], exact["ball_multiplier"])
    maximum_degree = tuple(max((exponent[i] for exponent in polynomial),
                               default=0) for i in range(N))
    if any(value > 2 for value in maximum_degree):
        raise AssertionError(maximum_degree)
    lower = bernstein_lower(polynomial)
    simplex_lower = simplex_bernstein_lower(
        chart, center, radii, triangle, screen["candidate"],
        exact["inner_index"], exact["ball_multiplier"])
    diagnostics = exact["diagnostics"]
    charged = (lower - diagnostics["defect_penalty"] -
               diagnostics["error"])
    return {
        "depth": depth,
        "screen": screen["lower_bound"],
        "interval_lower": diagnostics["lower_bound"],
        "bernstein_raw": lower,
        "bernstein_charged": charged,
        "bernstein_accepts": charged >= 0,
        "simplex_raw": simplex_lower,
        "simplex_charged": (simplex_lower - diagnostics["defect_penalty"] -
                            diagnostics["error"]),
        "simplex_accepts": (simplex_lower - diagnostics["defect_penalty"] -
                            diagnostics["error"]) >= 0,
        "maximum_degree": maximum_degree,
        "term_count": len(polynomial),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("artifact")
    parser.add_argument("--last", type=int, default=8)
    args = parser.parse_args()
    with open(args.artifact, "r", encoding="utf-8") as source:
        data = json.load(source)
    states = data["pending"][-args.last:]
    results = [audit_state(data["chart"], state) for state in states]
    json.dump(results, sys.stdout, indent=2, default=str)
    print()


if __name__ == "__main__":
    main()
