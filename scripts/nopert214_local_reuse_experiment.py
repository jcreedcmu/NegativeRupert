#!/usr/bin/env python3
"""Test exact reuse of nearby local-view certificate contact patterns."""

import argparse
import json
import time

from nopert214_certificate_search import (
    Q,
    projective_local_reaudit_certificate,
    split_projective_triangle,
)


def triangle_q(triangle):
    return tuple(tuple(map(Q, corner)) for corner in triangle)


def triangle_center_float(triangle):
    return tuple(sum(float(Q(corner[i])) for corner in triangle) / 3
                 for i in range(3))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("checkpoint")
    parser.add_argument("--sample", type=int, default=64)
    parser.add_argument("--nearest", type=int, default=8)
    parser.add_argument("--target-c", default="51/10000000")
    parser.add_argument("--split-failures", action="store_true",
                        help="also test all four children of failed cells")
    args = parser.parse_args()

    with open(args.checkpoint, encoding="utf-8") as source:
        data = json.load(source)
    target_c = Q(args.target_c)
    resolved = []
    for row in data["rows"]:
        if row is not None and row.get("kind") == "view_local":
            resolved.append((triangle_center_float(row["triangle"]),
                             row["certificate"], row["id"]))
    pending = sorted(data["pending"], key=lambda state: state[2],
                     reverse=True)[:args.sample]

    accepted = 0
    attempts = 0
    child_accepted = 0
    parents_closed_after_split = 0
    start = time.monotonic()
    for state in pending:
        triangle = triangle_q(state[1])
        center = triangle_center_float(state[1])
        nearby = sorted(resolved, key=lambda candidate: sum(
            (a-b)**2 for a, b in zip(center, candidate[0])))[:args.nearest]
        best = None
        source_id = None
        for _, certificate, row_id in nearby:
            attempts += 1
            result = projective_local_reaudit_certificate(
                triangle, certificate)
            if (result is not None and
                    (best is None or result["c"] > best["c"])):
                best = result
                source_id = row_id
            if best is not None and best["c"] >= target_c:
                break
        if best is not None and best["c"] >= target_c:
            accepted += 1
            print(f"pending {state[0]} depth {state[2]} reuses {source_id} "
                  f"with c={best['c']}")
        elif args.split_failures:
            closed = 0
            for child in split_projective_triangle(triangle):
                child_center = triangle_center_float(child)
                child_nearby = sorted(resolved, key=lambda candidate: sum(
                    (a-b)**2 for a, b in zip(
                        child_center, candidate[0])))[:args.nearest]
                for _, certificate, _ in child_nearby:
                    attempts += 1
                    result = projective_local_reaudit_certificate(
                        child, certificate)
                    if result is not None and result["c"] >= target_c:
                        closed += 1
                        break
            child_accepted += closed
            parents_closed_after_split += closed == 4
    elapsed = time.monotonic() - start
    print(f"accepted {accepted}/{len(pending)} from {attempts} exact reuse "
          f"attempts in {elapsed:.3f}s; resolved pool {len(resolved)}")
    if args.split_failures:
        failures = len(pending)-accepted
        print(f"failed parents: {child_accepted}/{4*failures} children "
              f"accepted; {parents_closed_after_split}/{failures} parents "
              "close completely after one split")


if __name__ == "__main__":
    main()
