#!/usr/bin/env python3
"""Summarize a Nopert #214 search checkpoint by top-level subtree."""

import argparse
import json
from collections import Counter
from pathlib import Path


def descendants(rows_by_id, root_id):
    seen = set()
    stack = [root_id]
    while stack:
        row_id = stack.pop()
        if row_id in seen:
            continue
        seen.add(row_id)
        row = rows_by_id.get(row_id)
        if row is not None:
            stack.extend(row.get("children", ()))
    return seen


def top_level_roots(first, rows_by_id):
    if first["kind"] != "view_root":
        return first.get("children", ())

    top_parent = rows_by_id[first["child"]]
    if top_parent["kind"] != "relative_split":
        return top_parent.get("children", ())

    # Charts 1 and 2 begin by partitioning their relative-coordinate box into
    # eight fixed octants.  Report those octants rather than the two children
    # of only the first bookkeeping split.
    roots = [top_parent["id"]]
    for _ in range(3):
        next_roots = []
        for root_id in roots:
            row = rows_by_id.get(root_id)
            if row is None:
                next_roots.append(root_id)
            else:
                next_roots.extend(row.get("children", (root_id,)))
        roots = next_roots
    return roots


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("checkpoints", nargs="+")
    args = parser.parse_args()

    for checkpoint in args.checkpoints:
        path = Path(checkpoint)
        with path.open() as source:
            data = json.load(source)

        rows = data["rows"]
        rows_by_id = {row["id"]: row for row in rows if row is not None}
        first = rows_by_id[0]
        pending = data.get("pending", ())
        pending_ids = {item[0] for item in pending}
        depth_index = 5 if first["kind"] == "view_root" else 2
        pending_depths = {item[0]: item[depth_index] for item in pending}
        failures = data.get("failures", ())

        top_roots = top_level_roots(first, rows_by_id)

        print(
            f"{path}: resolved={len(rows_by_id)} pending={len(pending_ids)} "
            f"failures={len(failures)} complete={data.get('complete', False)}"
        )
        covered = set()
        for root_id in top_roots:
            subtree = descendants(rows_by_id, root_id)
            covered.update(subtree)
            kinds = Counter(
                rows_by_id[row_id]["kind"]
                for row_id in subtree
                if row_id in rows_by_id
            )
            kind_summary = ",".join(
                f"{kind}={count}" for kind, count in sorted(kinds.items())
            )
            depths = Counter(
                pending_depths[row_id] for row_id in subtree & pending_ids
            )
            depth_summary = ",".join(
                f"{depth}:{count}" for depth, count in sorted(depths.items())
            )
            print(f"  root {root_id}: cells={len(subtree)} "
                  f"pending={len(subtree & pending_ids)} "
                  f"depths={depth_summary or '-'} {kind_summary}")

        bookkeeping = set(rows_by_id) - covered
        if bookkeeping:
            print(f"  bookkeeping rows above subtrees: {len(bookkeeping)}")


if __name__ == "__main__":
    main()
