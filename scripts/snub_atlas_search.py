#!/usr/bin/env python3
"""Atlas certificate search retargeted to the snub cube.

Installs the exact octahedral group (snub_atlas_group) and the snub
vertex tables into the shared atlas machinery. Symmetry matrices are
exact integers, so SYMMETRY_ERROR is zero. The view-space roots are kept
as the eight octants (respected by O); fundamental-domain restriction to
the octahedral wedge is left to a later refinement — searching a superset
is sound, merely redundant.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import snub_atlas_group as group
import snub_certificate_search as snub
from fractions import Fraction as Q

SNUB_Q = [tuple(Q(c) for c in v) for v in snub.VERTICES_Q]

import nopert214_certificate_search as base
import snub_certificate_search as exact_certificate

base.SEEDS_Q = None  # no seed structure: one regular orbit
base.VERTICES_Q = tuple(SNUB_Q)
base.VERTICES = [tuple(map(float, v)) for v in SNUB_Q]
base.SYMMETRY_COUNT = 24
base.SYMMETRY_ERROR = Q(0)   # integer symmetry matrices are exact
base.symmetry_action = group.symmetry_action
base.inverse_symmetry_action = group.inverse_symmetry_action
base.symmetry_matrix_q = group.symmetry_matrix_q
exact_certificate.VERTICES_Q = [list(v) for v in SNUB_Q]


def main():
    base.main()


if __name__ == "__main__":
    main()
