#!/usr/bin/env python3
"""Certificate search for Tom 7's Nopert #76.

Thin wrapper over ``nopert214_certificate_search``: the search, atlas, and
exact-checker machinery there reads the vertex tables through module
globals, so retargeting it to another 4-seed fivefold solid only requires
installing the new tables in the same orbit-major layout
(``VERTICES_Q[k*4+j] ~= Rz(2*pi*k/5) . seed_j``).

Vertices are the twenty published decimals of nopert76.stl, read as exact
rationals, exactly as for #214.
"""
import math
import os
import sys
from fractions import Fraction as Q
from pathlib import Path

if os.environ.get("NOPERT_GMPY2"):
    from gmpy2 import mpq as Q  # noqa: F811 (see nopert214_certificate_search)

sys.path.insert(0, str(Path(__file__).resolve().parent))
import nopert214_certificate_search as base
import snub_certificate_search as exact_certificate

STL = Path(__file__).resolve().parents[1] / \
    ".artifacts/nopert76/nopert76.stl"

PUBLISHED_STL_SHA256 = (
    "f257c3af4036bd8e13575f31becaff3f2f620638930957ec1192cbc10a0ad7dd"
)


def _load_vertices():
    raw = set()
    for line in STL.read_text().splitlines():
        fields = line.split()
        if fields[:1] == ["vertex"]:
            assert len(fields) == 4, line
            raw.add(tuple(Q(value) for value in fields[1:]))
    assert len(raw) == 20, len(raw)

    # group the four orbits by z coordinate
    levels = {}
    for vertex in raw:
        levels.setdefault(vertex[2], []).append(vertex)
    assert len(levels) == 4 and all(len(v) == 5 for v in levels.values())
    # seed order: decreasing z, matching the #214 file's convention of an
    # arbitrary-but-fixed representative per orbit
    seeds = []
    orbits = []
    for z in sorted(levels, key=lambda z: -z):
        members = levels[z]
        seed = max(members, key=lambda v: (v[0], v[1]))  # deterministic rep
        seeds.append(seed)
        orbits.append(members)

    # place each vertex at slot k*4+j with k the rotation index
    table = [None] * 20
    for j, seed in enumerate(seeds):
        sf = tuple(map(float, seed))
        for vertex in orbits[j]:
            vf = tuple(map(float, vertex))
            best = None
            for k in range(5):
                angle = 2 * math.pi * k / 5
                c, s = math.cos(angle), math.sin(angle)
                image = (c * sf[0] - s * sf[1], s * sf[0] + c * sf[1], sf[2])
                dist = sum((a - b) ** 2 for a, b in zip(image, vf))
                if best is None or dist < best[0]:
                    best = (dist, k)
            dist, k = best
            assert dist < 1e-28, (vertex, dist)
            slot = k * 4 + j
            assert table[slot] is None, (slot, vertex)
            table[slot] = vertex
    assert all(entry is not None for entry in table)
    return tuple(seeds), tuple(table)


SEEDS_Q, VERTICES_Q = _load_vertices()

# Install the #76 tables into the shared machinery.
base.SEEDS_Q = SEEDS_Q
base.VERTICES_Q = VERTICES_Q
base.VERTICES = [tuple(map(float, vertex)) for vertex in VERTICES_Q]
base.PUBLISHED_STL_SHA256 = PUBLISHED_STL_SHA256
exact_certificate.VERTICES_Q = [list(vertex) for vertex in VERTICES_Q]


# Match the Lean Nopert76 checker: the scaled-seed exact model puts the
# published decimals within 2e-15 (not 5e-16) of the exact vertices.
base.PROJECTIVE_LOCAL_VERTEX_ERROR = Q(2, 10**15)
base.PROJECTIVE_SUPPORT_ERROR = 10 * base.PROJECTIVE_LOCAL_VERTEX_ERROR


def main():
    base.main()


if __name__ == "__main__":
    main()
