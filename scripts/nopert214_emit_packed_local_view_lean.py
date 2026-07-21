#!/usr/bin/env python3
"""Emit a packed native-only Nopert #214 local-view certificate table."""

import argparse
import json
from fractions import Fraction
from pathlib import Path

from nopert214_emit_local_view_lean import triangle_key


def zigzag(value):
    return 2 * value if value >= 0 else -2 * value - 1


def encoded_rat(value):
    rational = Fraction(str(value))
    return [zigzag(rational.numerator), rational.denominator]


def triangle_paths(rows, initial_child):
    paths = {triangle_key(rows[0]): ()}
    for row in rows:
        if row["kind"] != "view_split":
            continue
        parent = triangle_key(row)
        if parent not in paths:
            raise ValueError("triangle parent lacks a subdivision path")
        for child_index, child_row_id in enumerate(row["children"]):
            child = triangle_key(rows[child_row_id])
            candidate = paths[parent] + (child_index,)
            old = paths.setdefault(child, candidate)
            if old != candidate:
                raise ValueError("triangle has inconsistent subdivision paths")
    missing = [row["id"] for row in rows if triangle_key(row) not in paths]
    if missing:
        raise ValueError(f"triangles lack subdivision paths: {missing[:10]}")
    return paths


def encode_axis(axis):
    result = []
    for key in ("edge_start", "edge_finish", "edge_start2", "edge_finish2",
                "mix", "support_index", "nonzero_witness"):
        result.extend(int(value) for value in axis[key])
    result.extend(encoded_rat(axis["B"]))
    return result


def encode_row(row, paths):
    path = paths[triangle_key(row)]
    common = [int(row["id"]), int(row["root"]), len(path), *path]
    if row["kind"] == "view_split":
        return [0, *common, *(int(value) for value in row["children"])]
    if row["kind"] == "view_local":
        result = [1, *common, int(row["symmetry_index"])]
        for axis in row["certificate"]:
            result.extend(encode_axis(axis))
        result.extend(encoded_rat(row["c"]))
        result.extend(encoded_rat(row["delta"]))
        result.extend(encoded_rat(row["r"]))
        return result
    raise ValueError(f"unsupported local-view row kind: {row['kind']}")


DATA_HEADER = """module

public import Noperthedron.Nopert214.PackedLocalViewTree
public import Noperthedron.Nopert214.SparseLocalViewTree

@[expose] public section

namespace Noperthedron.Nopert214.{namespace}Data

open AtlasProjectiveLocalViewTree
open SparseLocalViewTree
open PackedLocalViewTree

"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    parser.add_argument("--table-index", type=int, required=True,
                        choices=range(4))
    parser.add_argument("--namespace", required=True)
    parser.add_argument("--string-chunk-size", type=int, default=32768)
    parser.add_argument("--proof-part-size", type=int, default=256)
    args = parser.parse_args()

    with open(args.input, "r", encoding="utf-8") as source:
        data = json.load(source)
    if not data.get("complete"):
        raise SystemExit("refusing to emit an incomplete table")
    rows = data["rows"]
    if any(row is None for row in rows):
        raise SystemExit("table contains unfilled rows")
    if data.get("initial_child") != args.table_index:
        raise SystemExit("--table-index does not match input initial_child")

    paths = triangle_paths(rows, args.table_index)
    values = []
    for row in rows:
        values.extend(encode_row(row, paths))
    packed = ",".join(str(value) for value in values) + ","
    chunks = [packed[start:start + args.string_chunk_size]
              for start in range(0, len(packed), args.string_chunk_size)]

    first_certificate = next(row for row in rows
                             if row["kind"] == "view_local")
    symmetry_index = first_certificate["symmetry_index"]
    radius = Fraction(str(data["tube_radius"]))
    radius_lean = (str(radius.numerator) if radius.denominator == 1 else
                   f"({radius.numerator} / {radius.denominator})")

    destination = Path(args.output)
    data_namespace = f"{args.namespace}Data"
    data_destination = destination.with_name(f"{data_namespace}.lean")
    with data_destination.open("w", encoding="utf-8") as output:
        output.write(DATA_HEADER.format(namespace=args.namespace))
        output.write("def packedChunks : Array String := #[\n")
        output.write(",\n".join(f'  "{chunk}"' for chunk in chunks))
        output.write("\n]\n\n")
        output.write("def packed : String := packedChunks.foldl (· ++ ·) \"\"\n\n")
        output.write(f"""def table : Table :=
  decodeTable {args.table_index} {symmetry_index} {radius_lean} {len(rows)} packed

end Noperthedron.Nopert214.{data_namespace}

end
""")

    proof_parts = []
    for start in range(0, len(rows), args.proof_part_size):
        part_id = start // args.proof_part_size
        count = min(args.proof_part_size, len(rows) - start)
        part_namespace = f"{args.namespace}Part{part_id}"
        part_destination = destination.with_name(f"{part_namespace}.lean")
        proof_parts.append((part_namespace, start, count))
        part_destination.write_text(f"""module

public import Noperthedron.Nopert214.{data_namespace}
public meta import Noperthedron.Nopert214.{data_namespace}

@[expose] public section

namespace Noperthedron.Nopert214.{part_namespace}

open AtlasProjectiveLocalViewTree
open SparseLocalViewTree

theorem rows_valid :
    SparseRowsValidRangeAt {symmetry_index} {radius_lean}
      {data_namespace}.table.get {len(rows)} {start} {count} := by
  native_decide

end Noperthedron.Nopert214.{part_namespace}

end
""", encoding="utf-8")

    with destination.open("w", encoding="utf-8") as output:
        output.write("module\n\n")
        for part_namespace, _, _ in proof_parts:
            output.write(
                f"public import Noperthedron.Nopert214.{part_namespace}\n")
        output.write(f"""
@[expose] public section

namespace Noperthedron.Nopert214.{args.namespace}

open AtlasProjectiveLocalViewTree
open SparseLocalViewTree

abbrev table : Table := {data_namespace}.table

""")
        accumulated = 0
        previous = None
        for part_id, (part_namespace, start, count) in enumerate(proof_parts):
            accumulated += count
            theorem_name = f"rowsValidThrough{part_id}"
            if previous is None:
                proof = f"{part_namespace}.rows_valid"
            else:
                proof = (f"sparseRowsValidRange_append {previous} "
                         f"{part_namespace}.rows_valid")
            output.write(f"""private theorem {theorem_name} :
    SparseRowsValidRangeAt {symmetry_index} {radius_lean}
      table.get {len(rows)} 0 {accumulated} :=
  {proof}

""")
            previous = theorem_name
        output.write(f"""theorem table_sparse_valid_native :
    SparseTableValid table := by
  refine ⟨by native_decide, sparseRowsValidAt_of_range {previous}, ?_, ?_⟩
  · native_decide
  · native_decide

theorem table_valid_native : table.Valid :=
  Table.Valid.of_sparse table_sparse_valid_native

end Noperthedron.Nopert214.{args.namespace}

end
""")

    print(f"encoded {len(rows)} rows as {len(values)} naturals, "
          f"{len(packed)} bytes, {len(chunks)} string chunks, "
          f"{len(proof_parts)} proof parts")


if __name__ == "__main__":
    main()
