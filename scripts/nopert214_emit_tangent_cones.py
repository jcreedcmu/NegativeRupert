#!/usr/bin/env python3
"""Emit exact tangent-cone certificates for the Nopert #214 checker model.

For each ordered pair of distinct vertices ``(base, target)``, find at most
three incident edge directions at ``base`` whose nonnegative rational
combination is exactly ``target - base``.  We additionally require the sum
of the coefficients to be at least one; this preserves the strict support
margin used by the local certificate checker.

All discovery and validation in this script uses ``fractions.Fraction``.
The emitted Lean theorem is then checked again by exact rational reduction.
"""

from __future__ import annotations

import argparse
import itertools
from fractions import Fraction
from pathlib import Path

from nopert214_certificate_search import VERTICES_Q


ADJACENCY = (
    (1, 4, 16, 17),
    (0, 2, 3, 4, 5, 17, 18),
    (1, 3, 5, 7),
    (1, 2, 7, 18, 19),
    (0, 1, 5, 8),
    (1, 2, 4, 6, 7, 8, 9),
    (5, 7, 9, 11),
    (2, 3, 5, 6, 11),
    (4, 5, 9, 12),
    (5, 6, 8, 10, 11, 12, 13),
    (9, 11, 13, 15),
    (6, 7, 9, 10, 15),
    (8, 9, 13, 16),
    (9, 10, 12, 14, 15, 16, 17),
    (13, 15, 17, 19),
    (10, 11, 13, 14, 19),
    (0, 12, 13, 17),
    (0, 1, 13, 14, 16, 18, 19),
    (1, 3, 17, 19),
    (3, 14, 15, 17, 18),
)


def sub(left, right):
    return tuple(x - y for x, y in zip(left, right))


def add(left, right):
    return tuple(x + y for x, y in zip(left, right))


def scale(coefficient, vector):
    return tuple(coefficient * x for x in vector)


def det(columns):
    a, b, c = columns
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - b[0] * (a[1] * c[2] - a[2] * c[1])
            + c[0] * (a[1] * b[2] - a[2] * b[1]))


def solve(columns, target):
    denominator = det(columns)
    if denominator == 0:
        return None
    return tuple(det(columns[:i] + (target,) + columns[i + 1:]) /
                 denominator for i in range(3))


def complexity(indices, coefficients):
    """Prefer small emitted numerators and denominators, then sparse rows."""
    bits = [max(abs(value.numerator).bit_length(),
                value.denominator.bit_length()) for value in coefficients]
    return (max(bits), sum(bits), sum(value != 0 for value in coefficients),
            indices)


def find_combination(base, target):
    if base == target:
        return (0, 0, 0), (Fraction(0),) * 3

    neighbors = ADJACENCY[base]
    if target in neighbors:
        position = neighbors.index(target)
        return (position, position, position), (Fraction(1), Fraction(0),
                                                Fraction(0))

    directions = tuple(sub(VERTICES_Q[vertex], VERTICES_Q[base])
                       for vertex in neighbors)
    delta = sub(VERTICES_Q[target], VERTICES_Q[base])
    candidates = []
    for indices in itertools.combinations(range(len(neighbors)), 3):
        coefficients = solve(tuple(directions[i] for i in indices), delta)
        if coefficients is None or any(value < 0 for value in coefficients):
            continue
        if sum(coefficients, Fraction(0)) < 1:
            continue
        candidates.append((complexity(indices, coefficients), indices,
                           coefficients))
    if not candidates:
        raise ValueError(f"no tangent combination for ({base}, {target})")
    _, indices, coefficients = min(candidates)
    return indices, coefficients


def validate(base, target, indices, coefficients):
    if any(value < 0 for value in coefficients):
        raise AssertionError("negative tangent coefficient")
    if sum(coefficients, Fraction(0)) < 1:
        raise AssertionError("coefficient sum does not preserve margin")
    directions = tuple(sub(VERTICES_Q[ADJACENCY[base][i]], VERTICES_Q[base])
                       for i in indices)
    reconstructed = (Fraction(0), Fraction(0), Fraction(0))
    for coefficient, direction in zip(coefficients, directions):
        reconstructed = add(reconstructed, scale(coefficient, direction))
    if reconstructed != sub(VERTICES_Q[target], VERTICES_Q[base]):
        raise AssertionError("incorrect tangent reconstruction")


def lean_rat(value):
    if value.denominator == 1:
        return str(value.numerator)
    return f"({value.numerator} / {value.denominator} : ℚ)"


def lean_combination(indices, coefficients):
    return ("{ generator := ![" + ", ".join(map(str, indices)) +
            "], coefficient := ![" +
            ", ".join(lean_rat(value) for value in coefficients) + "] }")


def emit(destination):
    table = []
    max_bits = 0
    for base in range(20):
        row = []
        for target in range(20):
            indices, coefficients = find_combination(base, target)
            if base != target:
                validate(base, target, indices, coefficients)
            for value in coefficients:
                max_bits = max(max_bits, abs(value.numerator).bit_length(),
                               value.denominator.bit_length())
            row.append((indices, coefficients))
        table.append(row)

    lines = [
        "module", "",
        "public import Noperthedron.Nopert214.SparseSupport",
        "public meta import Noperthedron.Nopert214.SparseSupport", "",
        "@[expose] public section", "",
        "namespace Noperthedron.Nopert214.GeneratedTangentCones", "",
        "set_option linter.unusedTactic false",
        "set_option linter.unreachableTactic false",
        "set_option linter.unnecessarySeqFocus false", "",
        "open SparseSupport", "",
    ]
    for base, row in enumerate(table):
        for target, (indices, coefficients) in enumerate(row):
            lines.extend([
                f"def combination_{base}_{target} : TangentCombination :=",
                f"  {lean_combination(indices, coefficients)}", "",
            ])

    lines.extend([
        "abbrev table : VertexIndex → VertexIndex → TangentCombination := ![",
    ])
    for base, row in enumerate(table):
        suffix = "," if base + 1 < len(table) else ""
        lines.append("  ![")
        for target, _ in enumerate(row):
            entry_suffix = "," if target + 1 < len(row) else ""
            lines.append(f"    combination_{base}_{target}{entry_suffix}")
        lines.append(f"  ]{suffix}")
    lines.extend(["]", ""])

    for base in range(20):
        for target in range(20):
            if base == target:
                continue
            name = f"combination_{base}_{target}"
            lines.extend([
                f"private theorem valid_{base}_{target} :",
                f"    {name}.Valid {base} {target} := by",
                "  unfold TangentCombination.Valid",
                "  constructor",
                "  · intro l",
                f"    fin_cases l <;> simp [{name}] <;> norm_num",
                "  constructor",
                f"  · simp [{name}, Fin.sum_univ_three] <;> norm_num",
                "  constructor",
                "  · intro l hnonzero",
                f"    fin_cases l <;> simp [{name}, supportGenerator]",
                "  · funext coordinate",
                "    fin_cases coordinate <;>",
                f"      simp [{name}, supportGenerator, rationalVertex,",
                "        stlVertices, Fin.sum_univ_three] <;> norm_num",
                "",
            ])

    lines.extend([
        "theorem table_valid_kernel : TangentTableValid table := by",
        "  intro base target htarget",
        "  fin_cases base <;> fin_cases target",
    ])
    for base in range(20):
        for target in range(20):
            if base == target:
                lines.append("  · exact (htarget rfl).elim")
            else:
                lines.append(f"  · exact valid_{base}_{target}")
    lines.append("")

    lines.extend([
        "theorem table_valid_native : TangentTableValid table := by",
        "  native_decide", "",
        "end Noperthedron.Nopert214.GeneratedTangentCones", "", "end", "",
    ])
    destination.write_text("\n".join(lines), encoding="utf-8")
    print(f"wrote {destination} ({destination.stat().st_size} bytes; "
          f"maximum rational component {max_bits} bits)")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    emit(args.output)


if __name__ == "__main__":
    main()
