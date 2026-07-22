#!/usr/bin/env python3
"""Replace chart-1/2 split subtrees certified by stronger balanced cones."""

import argparse
import json
import os

from nopert214_certificate_search import (
    Q,
    atlas_projective_global_float_screen,
    atlas_projective_global_triangle,
)


def upgrade(data):
    chart = int(data.get("chart", -1))
    if chart not in (1, 2):
        raise ValueError("strong-cone migration requires chart 1 or 2")

    rows = data["rows"]
    pending_by_id = {int(state[0]): state for state in data["pending"]}
    failures_by_id = {
        int(failure["id"]): failure for failure in data.get("failures", [])
    }
    replacements = {}
    attempts = {10: 0, 16: 0}
    positive_screens = {10: 0, 16: 0}
    exact_rejections = 0

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

    def revisit(row_id):
        nonlocal exact_rejections
        if row_id in visited:
            raise ValueError(f"tree row {row_id} is reachable more than once")
        visited.add(row_id)
        row = rows[row_id]
        node = geometry(row_id)

        if (row is None or row.get("kind") in
                ("view_split", "relative_split")):
            widths = tuple(map(Q, node["widths"]))
            view_depth = int(node["view_depth"])
            policies = []
            if ((chart == 1 and view_depth >= 4 and
                    max(widths) <= Q(1, 16)) or
                    (chart == 2 and view_depth == 1 and
                     max(widths) == Q(1, 16))):
                policies.append(10)
            if (chart == 1 and view_depth >= 4 and
                    max(widths) <= Q(1, 96)):
                policies.append(16)
            for cone_samples in policies:
                attempts[cone_samples] += 1
                center = tuple(map(Q, node["center"]))
                triangle = tuple(
                    tuple(map(Q, corner)) for corner in node["triangle"])
                screen = atlas_projective_global_float_screen(
                    chart, center, widths, triangle,
                    cone_samples=cone_samples,
                    candidate_limit=64, candidates=None)
                if screen is not None and screen["lower_bound"] > 1e-8:
                    positive_screens[cone_samples] += 1
                    exact = atlas_projective_global_triangle(
                        chart, center, widths, int(node["root"]), triangle,
                        selected_candidate=screen["candidate"])
                    if exact is not None and exact["accepted"]:
                        axis = exact["certificate"]
                        axis_keys = (
                            "edge_start", "edge_finish", "edge_start2",
                            "edge_finish2", "mix", "support_index",
                            "nonzero_witness", "B")
                        replacements[row_id] = {
                            "id": row_id,
                            "kind": "global",
                            "center": node["center"],
                            "widths": node["widths"],
                            "root": node["root"],
                            "triangle": node["triangle"],
                            "view_depth": view_depth,
                            "certificate": {
                                "axis": {
                                    key: axis[key] for key in axis_keys
                                },
                                "inner_index": exact["inner_index"],
                                "ball_multiplier":
                                    exact["ball_multiplier"],
                            },
                        }
                        return
                    exact_rejections += 1

        if row is None:
            return
        if row.get("kind") == "view_root":
            revisit(int(row["child"]))
        else:
            for child in row.get("children", []):
                revisit(int(child))

    revisit(0)
    rows_before = len(rows)
    for row_id, replacement in replacements.items():
        rows[row_id] = replacement

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
            row["children"] = [remap[int(child)] for child in row["children"]]
        compact_rows.append(row)

    compact_pending = []
    for state in data["pending"]:
        old_id = int(state[0])
        if old_id not in reachable or old_id in replacements:
            continue
        state = list(state)
        state[0] = remap[old_id]
        compact_pending.append(state)
    compact_failures = []
    for failure in data.get("failures", []):
        old_id = int(failure["id"])
        if old_id not in reachable or old_id in replacements:
            continue
        failure = dict(failure)
        failure["id"] = remap[old_id]
        compact_failures.append(failure)

    data["rows"] = compact_rows
    data["pending"] = compact_pending
    data["failures"] = compact_failures
    data["complete"] = (
        not compact_pending and not compact_failures and
        all(row is not None for row in compact_rows))
    row_kinds = {}
    for row in compact_rows:
        if row is not None:
            row_kinds[row["kind"]] = row_kinds.get(row["kind"], 0) + 1
    for kind in (
            "view_root", "view_split", "relative_split", "edge", "global",
            "local", "radius", "fundamental_prune", "symmetry_tube"):
        data["counts"][kind] = row_kinds.get(kind, 0)
    data["counts"]["global_cone10"] = (
        data["counts"].get("global_cone10", 0) + attempts[10])
    data["counts"]["global_cone16"] = (
        data["counts"].get("global_cone16", 0) + attempts[16])
    data["counts"]["exact_rejections"] = (
        data["counts"].get("exact_rejections", 0) + exact_rejections)
    return {
        "attempts": attempts,
        "positive_screens": positive_screens,
        "exact_rejections": exact_rejections,
        "replacement_rows": len(replacements),
        "pruned_rows": rows_before - len(compact_rows),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    args = parser.parse_args()

    with open(args.input, encoding="utf-8") as source:
        data = json.load(source)
    result = upgrade(data)
    temporary = args.output + ".tmp"
    with open(temporary, "w", encoding="utf-8") as output:
        json.dump(data, output, default=str)
    os.replace(temporary, args.output)
    print(json.dumps({
        "output": args.output,
        **result,
        "rows": len(data["rows"]),
        "pending": len(data["pending"]),
        "failures": len(data["failures"]),
    }))


if __name__ == "__main__":
    main()
