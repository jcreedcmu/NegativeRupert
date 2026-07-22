#!/usr/bin/env python3
"""Emit a compact runtime artifact for a completed Nopert #214 chart tree."""

import argparse
import json
from pathlib import Path

from nopert214_emit_lean import interval_key, triangle_key
from nopert214_emit_packed_local_view_lean import encoded_rat, encode_axis


TAGS = {
    "view_root": 0,
    "relative_split": 1,
    "view_split": 2,
    "edge": 3,
    "global": 4,
    "local": 5,
    "symmetry_tube": 6,
    "radius": 7,
    "fundamental_prune": 8,
    "mixed_global": 9,
}


def encode_rats(values):
    result = []
    for value in values:
        result.extend(encoded_rat(value))
    return result


def encode_row(row, interval_ids, triangle_ids):
    kind = row["kind"]
    if kind not in TAGS:
        raise ValueError(f"unsupported global row kind: {kind}")
    result = [TAGS[kind], int(row["id"]),
              interval_ids[interval_key(row)]]
    if kind == "view_root":
        return [*result, int(row["child"])]

    root = int(row["root"])
    triangle_id = triangle_ids[triangle_key(row)]
    if kind == "relative_split":
        return [*result, *(int(value) for value in row["children"]),
                int(row["coordinate"]), root, triangle_id]
    if kind == "view_split":
        return [*result, *(int(value) for value in row["children"]),
                root, triangle_id]
    if kind == "radius":
        return [*result, root, triangle_id]
    if kind == "fundamental_prune":
        direction = 1 if int(row["direction"]) == 1 else 0
        return [*result, direction, root, triangle_id]
    if kind == "symmetry_tube":
        return [*result, int(row["symmetry_index"]),
                *encoded_rat(row["radius"]), int(row["shared_index"]),
                root, triangle_id]

    certificate = row["certificate"]
    if kind == "edge":
        cycle = [int(value) for value in certificate["cycle"]]
        contacts = certificate["contacts"]
        if len(contacts) != len(cycle):
            raise ValueError("edge cycle/contact length mismatch")
        inner = [int(contact["inner_index"]) for contact in contacts]
        witnesses = [int(contact["nonzero_witness"])
                     for contact in contacts]
        return [*result, root, triangle_id, len(cycle) - 1,
                *cycle, *inner, *witnesses,
                *encode_rats(certificate["ball_multipliers"])]
    if kind == "global":
        return [*result, root, triangle_id,
                *encode_axis(certificate["axis"]),
                *(int(value) for value in certificate["inner_index"]),
                *encoded_rat(certificate["ball_multiplier"])]
    if kind == "mixed_global":
        components = certificate["components"]
        weights = certificate["weights"]
        if len(components) != 4 or len(weights) != 4:
            raise ValueError("mixed global certificates require four slots")
        encoded_components = []
        for component in components:
            encoded_components.extend(encode_axis(component["axis"]))
            encoded_components.extend(
                int(value) for value in component["inner_index"])
            encoded_components.extend(
                encoded_rat(component["ball_multiplier"]))
        return [*result, root, triangle_id, *encode_rats(weights),
                *encoded_components]
    if kind == "local":
        axes = []
        for axis in certificate["certificates"]:
            axes.extend(encode_axis(axis))
        return [*result, root, triangle_id,
                int(certificate["symmetry_index"]), *axes,
                *encoded_rat(certificate["c"]),
                *encoded_rat(certificate["delta"]),
                *encoded_rat(certificate["r"])]
    raise AssertionError("unreachable row kind")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    parser.add_argument("--unchecked-prefix", type=int,
                        help="pack this many nonempty rows for decoder testing")
    parser.add_argument(
        "--fill-pending", action="store_true",
        help=("pack an incomplete checkpoint for native benchmarking, "
              "preserving row indices by replacing pending slots with "
              "deliberately invalid self-loop rows"))
    args = parser.parse_args()

    if args.unchecked_prefix is not None and args.fill_pending:
        parser.error("--unchecked-prefix and --fill-pending are exclusive")

    with open(args.input, "r", encoding="utf-8") as source:
        data = json.load(source)
    if (args.unchecked_prefix is None and not args.fill_pending and
            not data.get("complete")):
        raise SystemExit("refusing to pack an incomplete table")
    rows = data["rows"]
    if args.unchecked_prefix is not None:
        rows = [row for row in rows if row is not None][
            :args.unchecked_prefix]
    if not args.fill_pending and any(row is None for row in rows):
        raise SystemExit("table contains unfilled rows")

    first_row = next((row for row in rows if row is not None), None)
    if first_row is None:
        raise SystemExit("table contains no resolved rows")

    intervals = []
    interval_ids = {}
    triangles = []
    triangle_ids = {}
    for row in rows:
        if row is None:
            continue
        ikey = interval_key(row)
        if ikey not in interval_ids:
            interval_ids[ikey] = len(intervals)
            intervals.append(ikey)
        if row["kind"] != "view_root":
            tkey = triangle_key(row)
            if tkey not in triangle_ids:
                triangle_ids[tkey] = len(triangles)
                triangles.append(tkey)

    natural_count = 0
    buffer = []
    with open(args.output, "w", encoding="utf-8") as output:
        def emit(values):
            nonlocal natural_count
            for value in values:
                buffer.append(str(value))
                natural_count += 1
                if len(buffer) == 8192:
                    output.write(",".join(buffer))
                    output.write(",")
                    buffer.clear()

        emit((len(rows), len(intervals)))
        for center, widths in intervals:
            emit(encode_rats([*center, *widths]))
        emit((len(triangles),))
        for triangle in triangles:
            emit(encode_rats(
                value for corner in triangle for value in corner))
        dummy_interval_id = interval_ids[interval_key(first_row)]
        for row_id, row in enumerate(rows):
            if row is None:
                # Tag 0 is a view-root row.  A self-loop is intentionally not
                # a valid certificate, but it is compact and total to decode.
                # Benchmark clients select only resolved terminal leaves, so
                # the placeholder is never accepted as proof data.
                emit((TAGS["view_root"], row_id, dummy_interval_id, row_id))
            else:
                emit(encode_row(row, interval_ids, triangle_ids))
        if buffer:
            output.write(",".join(buffer))
            output.write(",")

    packed_size = Path(args.output).stat().st_size
    mode = "benchmark " if args.fill_pending else ""
    print(f"packed {mode}{len(rows)} rows, {len(intervals)} intervals, "
          f"{len(triangles)} triangles as {natural_count} naturals, "
          f"{packed_size} bytes")


if __name__ == "__main__":
    main()
