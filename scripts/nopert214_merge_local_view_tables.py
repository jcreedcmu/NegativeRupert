#!/usr/bin/env python3
"""Merge four independently generated local-view root children."""

import argparse
import copy
import json
import os

from nopert214_certificate_search import UPPER_WEDGE_PROJECTIVE_ROOT


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("output")
    parser.add_argument("inputs", nargs=4)
    args = parser.parse_args()

    tables = []
    for child, path in enumerate(args.inputs):
        with open(path, "r", encoding="utf-8") as source:
            table = json.load(source)
        if not table.get("complete"):
            raise SystemExit(f"child {child} is incomplete: {path}")
        if table.get("initial_child") != child:
            raise SystemExit(f"child index mismatch in {path}")
        tables.append(table)
    target_c = tables[0]["target_c"]
    tube_radius = tables[0]["tube_radius"]
    if any(table["target_c"] != target_c or
           table["tube_radius"] != tube_radius for table in tables[1:]):
        raise SystemExit("child certificate parameters differ")

    rows = [None]
    root_children = []
    counts = {"view_split": 1, "certificate": 0,
              "weak_rejections": 0}
    for table in tables:
        offset = len(rows)
        root_children.append(offset)
        for source_row in table["rows"]:
            row = copy.deepcopy(source_row)
            row["id"] += offset
            if row["kind"] == "view_split":
                row["children"] = [child + offset
                                   for child in row["children"]]
            rows.append(row)
        for key in counts:
            counts[key] += table["counts"].get(key, 0)
    rows[0] = {
        "id": 0,
        "kind": "view_split",
        "root": 0,
        "triangle": UPPER_WEDGE_PROJECTIVE_ROOT,
        "depth": 0,
        "children": root_children,
    }
    result = {
        "complete": True,
        "target_c": target_c,
        "tube_radius": tube_radius,
        "max_depth": max(table["max_depth"] for table in tables),
        "initial_child": None,
        "rows": rows,
        "pending": [],
        "counts": counts,
        "failures": [],
    }
    temporary = args.output + ".tmp"
    with open(temporary, "w", encoding="utf-8") as output:
        json.dump(result, output, default=str)
    os.replace(temporary, args.output)
    print(json.dumps({"complete": True, "row_count": len(rows),
                      "counts": counts}, indent=2))


if __name__ == "__main__":
    main()
