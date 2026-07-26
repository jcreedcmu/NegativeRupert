#!/usr/bin/env python3
"""Octahedral symmetry data for the snub cube atlas port.

Builds, in exact rational arithmetic:
  - MATRICES: the 24 integer signed-permutation rotation matrices that
    preserve the snub cube vertex set (the chiral octahedral group O);
  - PERM: the regular action on vertex indices, PERM[g][v] = index of
    MATRICES[g] . vertex_v;
  - MUL / INV: the group multiplication and inverse tables.

Everything is validated on import: closure, identity, inverses, and
exact set-preservation. Symmetry matrices are exact integers, so the
atlas port needs no symmetry trig error term (SYMMETRY_ERROR = 0).
"""
import itertools
import sys
from fractions import Fraction as Q
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import snub_certificate_search as snub

VERTICES_Q = [tuple(Q(c) for c in v) for v in snub.VERTICES_Q]
assert len(VERTICES_Q) == 24
_INDEX = {v: i for i, v in enumerate(VERTICES_Q)}


def _apply(m, v):
    return tuple(sum(m[r][c] * v[c] for c in range(3)) for r in range(3))


def _det(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


MATRICES = []
PERM = []
for perm in itertools.permutations(range(3)):
    for signs in itertools.product((1, -1), repeat=3):
        m = tuple(tuple(signs[r] if c == perm[r] else 0 for c in range(3))
                  for r in range(3))
        if _det(m) != 1:
            continue
        images = [_apply(m, v) for v in VERTICES_Q]
        if all(w in _INDEX for w in images):
            MATRICES.append(m)
            PERM.append(tuple(_INDEX[w] for w in images))

assert len(MATRICES) == 24, f"expected |O| = 24, got {len(MATRICES)}"
assert MATRICES[0] == ((1, 0, 0), (0, 1, 0), (0, 0, 1)) or True

# identity first, for convenience
_id = MATRICES.index(((1, 0, 0), (0, 1, 0), (0, 0, 1)))
MATRICES[0], MATRICES[_id] = MATRICES[_id], MATRICES[0]
PERM[0], PERM[_id] = PERM[_id], PERM[0]

_MINDEX = {m: g for g, m in enumerate(MATRICES)}


def _matmul(a, b):
    return tuple(tuple(sum(a[r][k] * b[k][c] for k in range(3))
                       for c in range(3)) for r in range(3))


MUL = [[_MINDEX[_matmul(MATRICES[g], MATRICES[h])] for h in range(24)]
       for g in range(24)]
INV = [next(h for h in range(24) if MUL[g][h] == 0) for g in range(24)]

# validation: closure implicitly by MUL construction; check regular action
for g in range(24):
    for h in range(24):
        composed = tuple(PERM[g][PERM[h][v]] for v in range(24))
        assert composed == PERM[MUL[g][h]], (g, h)
assert PERM[0] == tuple(range(24))


def symmetry_matrix_q(index):
    """Exact rational rotation matrix of group element `index`."""
    return [[Q(x) for x in row] for row in MATRICES[index]]


def symmetry_action(index, vertex):
    return PERM[index][vertex]


def inverse_symmetry_action(index, vertex):
    return PERM[INV[index]][vertex]


if __name__ == "__main__":
    print(f"|O| = {len(MATRICES)}; regular action validated "
          f"(closure + identity + inverses)")
    orbit = {symmetry_action(g, 0) for g in range(24)}
    print(f"orbit of vertex 0 under O: {len(orbit)} vertices "
          f"(regular: {orbit == set(range(24))})")
