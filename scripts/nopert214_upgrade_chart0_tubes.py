#!/usr/bin/env python3
"""Change chart-0 shared-local tube radii in a search checkpoint.

Existing symmetry-tube leaves remain valid at a larger radius, but the formal
global checker requires each leaf radius to equal its referenced local table
radius exactly.  This migration updates both the checkpoint configuration and
those already-emitted leaves after rechecking their exact mismatch bounds.

It also revisits expanded tree nodes.  If a new tube certifies such a node,
the whole descendant subtree is unreachable and can be replaced by one tube
leaf.  Compacting those descendants is important both for search throughput
and for the eventual native checker, which otherwise audits every stored row.

Shrinking is opt-in.  A stored tube leaf that no longer fits is safely reopened
as a pending generator state; no terminal certificate is retained by fiat.
"""

import argparse
import json
import os

from nopert214_certificate_search import (
    Q,
    atlas_projective_mismatch_radius,
)


def upgrade(data, radii, allow_decrease=False):
    if data.get("chart") != 0:
        raise ValueError("tube-radius migration requires chart 0")
    old_values = data.get("chart0_origin_tube_radii")
    if old_values is None or len(old_values) != 4:
        raise ValueError("checkpoint has no indexed chart-0 tube radii")
    old_radii = tuple(map(Q, old_values))
    if len(radii) != 4:
        raise ValueError("exactly four new radii are required")
    if any(radius <= 0 for radius in radii):
        raise ValueError("tube radii must be positive")
    if (not allow_decrease and
            any(new < old for new, old in zip(radii, old_radii))):
        raise ValueError(
            "decreasing a tube radius requires --allow-decrease")

    rows = data["rows"]
    updated = 0
    reopened = []
    for row in list(rows):
        if row is None or row.get("kind") != "symmetry_tube":
            continue
        index = int(row["shared_index"])
        if not 0 <= index < 4:
            raise ValueError(f"invalid shared index {index}")
        center = tuple(map(Q, row["center"]))
        widths = tuple(map(Q, row["widths"]))
        mismatch = atlas_projective_mismatch_radius(
            0, int(row["symmetry_index"]), center, widths)[0]
        if mismatch > Q(row["radius"]):
            raise ValueError(
                f"existing tube row {row['id']} fails its stored radius")
        if mismatch > radii[index]:
            if not allow_decrease:
                raise ValueError(
                    f"tube row {row['id']} fails new radius {radii[index]}")
            reopened.append([
                int(row["id"]), row["center"], row["widths"],
                int(row["root"]), row["triangle"],
                int(row["view_depth"]), index])
            rows[int(row["id"])] = None
            continue
        row["radius"] = str(radii[index])
        updated += 1

    data["pending"].extend(reopened)
    pending_by_id = {int(state[0]): state for state in data["pending"]}
    failures_by_id = {
        int(failure["id"]): failure for failure in data.get("failures", [])}
    replacement_rows = {}

    def geometry(row_id):
        row = rows[row_id]
        if row is not None:
            return row
        state = pending_by_id.get(row_id)
        if state is not None:
            return {
                "id": row_id,
                "center": state[1],
                "widths": state[2],
                "root": state[3],
                "triangle": state[4],
                "view_depth": state[5],
            }
        failure = failures_by_id.get(row_id)
        if failure is not None:
            return failure
        raise ValueError(f"unresolved row {row_id} has no frontier state")

    visited = set()

    def revisit(row_id, shared_index=None):
        if row_id in visited:
            raise ValueError(f"tree row {row_id} is reachable more than once")
        visited.add(row_id)
        row = rows[row_id]
        node = geometry(row_id)

        # Only expanded or unresolved nodes buy a smaller tree when replaced.
        # Existing terminal rows remain preferable to a same-size tube leaf.
        if shared_index is not None and (
                row is None or row.get("kind") in
                ("view_split", "relative_split")):
            center = tuple(map(Q, node["center"]))
            widths = tuple(map(Q, node["widths"]))
            mismatch = atlas_projective_mismatch_radius(
                0, 0, center, widths)[0]
            if mismatch <= radii[shared_index]:
                replacement_rows[row_id] = {
                    "id": row_id,
                    "kind": "symmetry_tube",
                    "center": node["center"],
                    "widths": node["widths"],
                    "root": node["root"],
                    "triangle": node["triangle"],
                    "view_depth": node["view_depth"],
                    "symmetry_index": 0,
                    "radius": str(radii[shared_index]),
                    "shared_index": shared_index,
                }
                return

        if row is None:
            return
        kind = row.get("kind")
        if kind == "view_root":
            revisit(int(row["child"]), shared_index)
        elif kind == "view_split":
            children = list(map(int, row["children"]))
            if shared_index is None:
                if len(children) != 4:
                    raise ValueError("initial indexed view split is not 4-way")
                for index, child in enumerate(children):
                    revisit(child, index)
            else:
                for child in children:
                    revisit(child, shared_index)
        elif kind == "relative_split":
            for child in row["children"]:
                revisit(int(child), shared_index)

    revisit(0)
    rows_before = len(rows)
    for row_id, replacement in replacement_rows.items():
        rows[row_id] = replacement

    # Recompute reachability after replacing expanded ancestors, then remap
    # every row reference into a dense table.  Preserving old-ID order keeps
    # the migration deterministic and makes checkpoint diffs auditable.
    reachable = set()

    def mark(row_id):
        if row_id in reachable:
            return
        reachable.add(row_id)
        row = rows[row_id]
        if row is None:
            return
        if row.get("kind") == "view_root":
            mark(int(row["child"]))
        else:
            for child in row.get("children", []):
                mark(int(child))

    mark(0)
    old_ids = sorted(reachable)
    remap = {old: new for new, old in enumerate(old_ids)}
    compact_rows = []
    for old_id in old_ids:
        row = rows[old_id]
        if row is None:
            compact_rows.append(None)
            continue
        row = dict(row)
        row["id"] = remap[old_id]
        if row.get("kind") == "view_root":
            row["child"] = remap[int(row["child"])]
        if "children" in row:
            row["children"] = [remap[int(child)]
                               for child in row["children"]]
        compact_rows.append(row)

    compact_pending = []
    for state in data["pending"]:
        old_id = int(state[0])
        if old_id not in reachable:
            continue
        state = list(state)
        state[0] = remap[old_id]
        compact_pending.append(state)
    compact_failures = []
    for failure in data.get("failures", []):
        old_id = int(failure["id"])
        if old_id not in reachable:
            continue
        failure = dict(failure)
        failure["id"] = remap[old_id]
        compact_failures.append(failure)

    data["rows"] = compact_rows
    data["pending"] = compact_pending
    data["failures"] = compact_failures
    data["complete"] = (not compact_pending and not compact_failures and
                        all(row is not None for row in compact_rows))
    row_kinds = {}
    for row in compact_rows:
        if row is not None:
            kind = row["kind"]
            row_kinds[kind] = row_kinds.get(kind, 0) + 1
    for kind in ("view_root", "view_split", "relative_split", "edge",
                 "global", "local", "radius", "fundamental_prune",
                 "symmetry_tube"):
        data["counts"][kind] = row_kinds.get(kind, 0)

    data["chart0_origin_tube_radii"] = [str(radius) for radius in radii]
    return {
        "updated_tube_rows": updated,
        "reopened_tube_rows": len(reopened),
        "replacement_tube_rows": len(replacement_rows),
        "pruned_rows": rows_before-len(compact_rows),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    parser.add_argument(
        "--radii", required=True,
        help="four comma-separated rational radii")
    parser.add_argument(
        "--allow-decrease", action="store_true",
        help="reopen any stored tube leaf that fails a smaller new radius")
    args = parser.parse_args()
    radii = tuple(Q(value) for value in args.radii.split(","))

    with open(args.input, encoding="utf-8") as source:
        data = json.load(source)
    result = upgrade(data, radii, args.allow_decrease)
    temporary = args.output + ".tmp"
    with open(temporary, "w", encoding="utf-8") as output:
        json.dump(data, output)
    os.replace(temporary, args.output)
    print(json.dumps({
        "output": args.output,
        **result,
        "radii": [str(radius) for radius in radii],
        "rows": len(data["rows"]),
        "pending": len(data["pending"]),
    }))


if __name__ == "__main__":
    main()
