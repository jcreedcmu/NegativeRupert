#!/usr/bin/env python3
"""Time individual certificate families on one pending local-view cell."""

import argparse
from fractions import Fraction as Q
import json
import time

import nopert214_certificate_search as search


def timed(label, action):
    start = time.monotonic()
    result = action()
    elapsed = time.monotonic() - start
    summary = None if result is None else {
        "accepted": result.get("accepted"),
        "c": result.get("c"),
        "delta": result.get("delta"),
    }
    print(json.dumps({"label": label, "seconds": elapsed,
                      "result": summary}, default=str), flush=True)


def local_candidate(triangle, cone_samples, trials, **kwargs):
    return search.atlas_projective_local_triangle(
        0, (Q(0), Q(0), Q(0)), (Q(0), Q(0), Q(0)),
        0, triangle, 0, cone_samples=cone_samples, trials=trials,
        **kwargs)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("checkpoint")
    parser.add_argument("mode", choices=(
        "nearby", "basic4", "boundary4", "boundary5", "boundary6",
        "corner4", "dense8", "zero7", "fine7", "full"))
    parser.add_argument("--pending-offset", type=int, default=-1)
    parser.add_argument("--child-path", default="0")
    args = parser.parse_args()

    with open(args.checkpoint, "r", encoding="utf-8") as source:
        data = json.load(source)
    state = data["pending"][args.pending_offset]
    triangle = tuple(tuple(map(Q, corner)) for corner in state[1])
    depth = state[2]
    for value in args.child_path.split(",") if args.child_path else ():
        triangle = search.split_projective_triangle(triangle)[int(value)]
        depth += 1
    print(json.dumps({"row": state[0], "depth": depth,
                      "child_path": args.child_path}), flush=True)

    if args.mode == "nearby":
        center = search.projective_triangle_center_float(triangle)
        candidates = []
        for row in data["rows"]:
            if row is None or row.get("kind") != "view_local":
                continue
            row_triangle = tuple(tuple(map(Q, corner))
                                 for corner in row["triangle"])
            row_center = search.projective_triangle_center_float(row_triangle)
            distance = sum((a-b)*(a-b)
                           for a, b in zip(center, row_center))
            candidates.append((distance, row["id"], row["certificate"]))
        for pool_name, pool in (
                ("recent", candidates[-4096:]), ("global", candidates)):
            for rank, (distance, row_id, certificate) in enumerate(
                    sorted(pool)[:8]):
                timed(f"{pool_name}-{rank}-row-{row_id}-distance-{distance}",
                  lambda certificate=certificate:
                  search.projective_local_reaudit_certificate(
                      triangle, certificate))
        return

    actions = {
        "basic4": lambda: local_candidate(triangle, 4, 1000),
        "boundary4": lambda: local_candidate(
            triangle, 4, 1, include_boundaries=True),
        "boundary5": lambda: local_candidate(
            triangle, 5, 1000, include_boundaries=True),
        "boundary6": lambda: local_candidate(
            triangle, 6, 1000, include_boundaries=True),
        "corner4": lambda: local_candidate(
            triangle, 4, 100_000, include_boundaries=True,
            include_corner_cycles=True),
        "dense8": lambda: local_candidate(
            triangle, 8, 1000, include_boundaries=True,
            screen_support_error=Q(0)),
        "zero7": lambda: local_candidate(
            triangle, 7, 200_000, include_boundaries=True,
            include_corner_cycles=True, screen_support_error=Q(0)),
        "fine7": lambda: local_candidate(
            triangle, 7, 200_000, include_boundaries=True,
            include_corner_cycles=True),
        "full": lambda: search.projective_local_candidate(
            (triangle, depth, Q(data["target_c"]))),
    }
    timed(args.mode, actions[args.mode])


if __name__ == "__main__":
    main()
