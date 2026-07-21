#!/usr/bin/env python3
"""Graft a disjoint searched local-view subtree into another checkpoint.

Both checkpoints must describe the same local table and have the same row at
the graft root.  The base root may only have unresolved descendants; donor
rows below that root are copied with fresh row IDs.  The output is a normal
generator checkpoint and can immediately be resumed.
"""

import argparse
import copy
import json
import os


def descendants(rows, root):
    seen = set()
    stack = [root]
    while stack:
        row_id = stack.pop()
        if row_id in seen:
            continue
        if not 0 <= row_id < len(rows):
            raise ValueError(f"row {row_id} is outside the table")
        seen.add(row_id)
        row = rows[row_id]
        if row is not None:
            stack.extend(row.get("children", ()))
    return seen


def validate_checkpoint(data, label):
    required = ("target_c", "tube_radius", "max_depth", "initial_child",
                "rows", "pending", "failures", "counts")
    missing = [key for key in required if key not in data]
    if missing:
        raise ValueError(f"{label} is missing {missing}")
    if data["failures"]:
        raise ValueError(f"{label} has unresolved failures")
    pending_ids = [state[0] for state in data["pending"]]
    if len(pending_ids) != len(set(pending_ids)):
        raise ValueError(f"{label} has duplicate pending row IDs")
    none_ids = {i for i, row in enumerate(data["rows"]) if row is None}
    if none_ids != set(pending_ids):
        raise ValueError(
            f"{label} pending IDs do not equal its unfilled rows")
    reachable = descendants(data["rows"], 0)
    if reachable != set(range(len(data["rows"]))):
        raise ValueError(f"{label} contains unreachable rows")


def graft(base, donor, root):
    validate_checkpoint(base, "base")
    validate_checkpoint(donor, "donor")
    for key in ("target_c", "tube_radius", "max_depth", "initial_child"):
        if base[key] != donor[key]:
            raise ValueError(f"checkpoint mismatch in {key}")

    base_rows = copy.deepcopy(base["rows"])
    donor_rows = donor["rows"]
    base_ids = descendants(base_rows, root)
    donor_ids = descendants(donor_rows, root)
    if base_rows[root] != donor_rows[root]:
        raise ValueError("graft-root rows are not identical")

    base_pending = {state[0] for state in base["pending"]}
    occupied_below_root = [
        row_id for row_id in base_ids - {root}
        if row_id not in base_pending or base_rows[row_id] is not None
    ]
    if occupied_below_root:
        raise ValueError(
            "base graft subtree already contains searched descendants: "
            f"{occupied_below_root[:8]}")

    donor_root_children = donor_rows[root].get("children", ())
    base_root_children = base_rows[root].get("children", ())
    if len(donor_root_children) != len(base_root_children):
        raise ValueError("graft roots have different child counts")

    row_map = {root: root}
    row_map.update(zip(donor_root_children, base_root_children))
    next_id = len(base_rows)
    for donor_id in sorted(donor_ids):
        if donor_id not in row_map:
            row_map[donor_id] = next_id
            next_id += 1
    base_rows.extend([None] * (next_id - len(base_rows)))

    for donor_id in donor_ids:
        target_id = row_map[donor_id]
        donor_row = donor_rows[donor_id]
        if donor_row is None:
            base_rows[target_id] = None
            continue
        row = copy.deepcopy(donor_row)
        row["id"] = target_id
        if "children" in row:
            row["children"] = [row_map[child] for child in row["children"]]
        base_rows[target_id] = row

    donor_pending = [
        [row_map[state[0]], *copy.deepcopy(state[1:])]
        for state in donor["pending"] if state[0] in donor_ids
    ]
    merged_pending = []
    inserted = False
    for state in base["pending"]:
        if state[0] in base_ids:
            if not inserted:
                merged_pending.extend(donor_pending)
                inserted = True
            continue
        merged_pending.append(copy.deepcopy(state))
    if not inserted:
        raise ValueError("base graft subtree has no pending descendants")

    result = copy.deepcopy(base)
    result["complete"] = False
    result["rows"] = base_rows
    result["pending"] = merged_pending
    result["failures"] = []
    result["counts"]["view_split"] = sum(
        row is not None and row.get("kind") == "view_split"
        for row in base_rows)
    result["counts"]["certificate"] = sum(
        row is not None and row.get("kind") == "view_local"
        for row in base_rows)
    result["counts"]["weak_rejections"] = (
        base["counts"].get("weak_rejections", 0) +
        donor["counts"].get("weak_rejections", 0))

    validate_checkpoint(result, "merged checkpoint")
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("base")
    parser.add_argument("donor")
    parser.add_argument("output")
    parser.add_argument("--root", type=int, required=True)
    args = parser.parse_args()

    with open(args.base, encoding="utf-8") as source:
        base = json.load(source)
    with open(args.donor, encoding="utf-8") as source:
        donor = json.load(source)
    merged = graft(base, donor, args.root)
    temporary = args.output + ".tmp"
    with open(temporary, "w", encoding="utf-8") as output:
        json.dump(merged, output)
    os.replace(temporary, args.output)
    print(json.dumps({
        "output": args.output,
        "rows": len(merged["rows"]),
        "pending": len(merged["pending"]),
        "counts": merged["counts"],
    }))


if __name__ == "__main__":
    main()
