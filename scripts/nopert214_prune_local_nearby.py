#!/usr/bin/env python3
"""Bottom-up exact compaction of a completed Nopert #214 local table."""

import argparse
import json
import time

from nopert214_certificate_search import (
    Q,
    compact_projective_local_axis_artifact,
    projective_local_reaudit_certificate,
    projective_triangle_center_float,
)


def triangle_q(row):
    return tuple(tuple(map(Q, corner)) for corner in row["triangle"])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    parser.add_argument("--representatives", type=int, default=8)
    args = parser.parse_args()
    if args.representatives < 1:
        parser.error("--representatives must be positive")

    with open(args.input, encoding="utf-8") as source:
        data = json.load(source)
    if not data.get("complete") or data.get("pending") or data.get("failures"):
        raise SystemExit("refusing to compact an incomplete local table")
    rows = data["rows"]
    if any(row is None for row in rows):
        raise SystemExit("completed local table contains an empty row")
    target_c = Q(data["target_c"])
    tube_radius = Q(data["tube_radius"])

    # Each subtree exports a small geometrically-near set of leaf contact
    # patterns.  At its parent we rebuild and audit those patterns on the
    # larger triangle.  A successful parent becomes an ordinary certificate
    # leaf; no unchecked numerical bound is inherited from its child.
    representatives = {}
    split_rows = sorted(
        (row for row in rows if row["kind"] == "view_split"),
        key=lambda row: int(row["depth"]), reverse=True)
    for row in rows:
        if row["kind"] == "view_local":
            triangle = triangle_q(row)
            representatives[int(row["id"])] = [
                (projective_triangle_center_float(triangle),
                 row["certificate"])]

    replacements = 0
    attempts = 0
    started = time.monotonic()
    for processed, row in enumerate(split_rows, 1):
        triangle = triangle_q(row)
        center = projective_triangle_center_float(triangle)
        candidates = []
        for child in row["children"]:
            candidates.extend(representatives.get(int(child), ()))
        candidates.sort(key=lambda candidate: sum(
            (a-b)*(a-b) for a, b in zip(center, candidate[0])))
        candidates = candidates[:args.representatives]
        accepted = None
        for _, certificate in candidates:
            attempts += 1
            result = projective_local_reaudit_certificate(
                triangle, certificate)
            if (result is not None and result["c"] >= target_c and
                    tube_radius*tube_radius *
                    (1+result["c"]*result["c"]) <=
                    4*result["c"]*result["c"]):
                accepted = result
                break
        row_id = int(row["id"])
        if accepted is None:
            representatives[row_id] = candidates
        else:
            replacement = {
                "id": row_id,
                "kind": "view_local",
                "root": int(row["root"]),
                "triangle": row["triangle"],
                "depth": int(row["depth"]),
                "symmetry_index": 0,
                "r": tube_radius,
                "certificate": [
                    compact_projective_local_axis_artifact(axis)
                    for axis in accepted["certificates"]],
                "c": accepted["c"],
                "delta": accepted["delta"],
            }
            rows[row_id] = replacement
            representatives[row_id] = [(center, replacement["certificate"])]
            replacements += 1
        if processed % 500 == 0:
            print(f"audited {processed}/{len(split_rows)} parents: "
                  f"{replacements} replacements, {attempts} attempts",
                  flush=True)

    reachable = set()

    def mark(row_id):
        if row_id in reachable:
            return
        reachable.add(row_id)
        row = rows[row_id]
        if row["kind"] == "view_split":
            for child in row["children"]:
                mark(int(child))

    mark(0)
    old_ids = sorted(reachable)
    remap = {old: new for new, old in enumerate(old_ids)}
    compact_rows = []
    for old_id in old_ids:
        row = dict(rows[old_id])
        row["id"] = remap[old_id]
        if row["kind"] == "view_split":
            row["children"] = [remap[int(child)] for child in row["children"]]
        compact_rows.append(row)

    data["rows"] = compact_rows
    data["pending"] = []
    data["failures"] = []
    data["complete"] = True
    data["counts"]["view_split"] = sum(
        row["kind"] == "view_split" for row in compact_rows)
    data["counts"]["certificate"] = sum(
        row["kind"] == "view_local" for row in compact_rows)
    data["counts"]["nearby_parent_prunes"] = replacements
    with open(args.output, "w", encoding="utf-8") as output:
        json.dump(data, output, default=str)
    elapsed = time.monotonic()-started
    print(f"compacted {len(rows)} to {len(compact_rows)} rows using "
          f"{replacements} exact parent replacements and {attempts} "
          f"attempts in {elapsed:.3f}s")


if __name__ == "__main__":
    main()
