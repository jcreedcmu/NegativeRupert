#!/usr/bin/env python3
"""Increase chart-0 shared-local tube radii in a search checkpoint.

Existing symmetry-tube leaves remain valid at a larger radius, but the formal
global checker requires each leaf radius to equal its referenced local table
radius exactly.  This migration updates both the checkpoint configuration and
those already-emitted leaves after rechecking their exact mismatch bounds.
"""

import argparse
import json
import os

from nopert214_certificate_search import (
    Q,
    atlas_projective_mismatch_radius,
)


def upgrade(data, radii):
    if data.get("chart") != 0:
        raise ValueError("tube-radius migration requires chart 0")
    old_values = data.get("chart0_origin_tube_radii")
    if old_values is None or len(old_values) != 4:
        raise ValueError("checkpoint has no indexed chart-0 tube radii")
    old_radii = tuple(map(Q, old_values))
    if len(radii) != 4:
        raise ValueError("exactly four new radii are required")
    if any(new < old for new, old in zip(radii, old_radii)):
        raise ValueError("this migration may only increase tube radii")

    updated = 0
    for row in data["rows"]:
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
            raise ValueError(
                f"tube row {row['id']} fails new radius {radii[index]}")
        row["radius"] = str(radii[index])
        updated += 1

    data["chart0_origin_tube_radii"] = [str(radius) for radius in radii]
    return updated


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    parser.add_argument(
        "--radii", required=True,
        help="four comma-separated rational radii")
    args = parser.parse_args()
    radii = tuple(Q(value) for value in args.radii.split(","))

    with open(args.input, encoding="utf-8") as source:
        data = json.load(source)
    updated = upgrade(data, radii)
    temporary = args.output + ".tmp"
    with open(temporary, "w", encoding="utf-8") as output:
        json.dump(data, output)
    os.replace(temporary, args.output)
    print(json.dumps({
        "output": args.output,
        "updated_tube_rows": updated,
        "radii": [str(radius) for radius in radii],
        "rows": len(data["rows"]),
        "pending": len(data["pending"]),
    }))


if __name__ == "__main__":
    main()
