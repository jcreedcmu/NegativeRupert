#!/usr/bin/env python3
"""Emit a chunked kernel-only local-view proof for Nopert #214.

The exact row data lives in one generated module.  Independent proof modules
then check short contiguous ranges with kernel reduction, allowing Lake to
cache and parallelize the expensive arithmetic.  The final tiny aggregator
joins the ranges and converts sparse validity to the original semantic table
validity theorem.
"""

import argparse
import json
from pathlib import Path

import nopert214_emit_local_view_lean as direct


DATA_HEADER = """module

public import Noperthedron.Nopert214.SparseLocalViewTree

@[expose] public section

namespace Noperthedron.Nopert214.{namespace}

open AtlasProjectiveView AtlasProjectiveLocalCertificate
open AtlasProjectiveLocalViewTree
open SparseLocalViewTree
open Noperthedron.SnubCube.ProjectiveView

"""


def collect(rows):
    triangle_ids = {}
    axis_ids = {}
    axis_values = []
    template_ids = {}
    template_values = []
    for row in rows:
        key = direct.triangle_key(row)
        if key not in triangle_ids:
            triangle_ids[key] = len(triangle_ids)
        if row["kind"] == "view_local":
            for axis in row["certificate"]:
                key = direct.axis_value_key(axis)
                if key not in axis_ids:
                    axis_ids[key] = len(axis_values)
                    axis_values.append(axis)
            key = direct.local_template_key(row)
            if key not in template_ids:
                template_ids[key] = len(template_values)
                template_values.append(key)
    return (triangle_ids, axis_ids, axis_values,
            template_ids, template_values)


def emit_data(destination, namespace, rows, initial_child, chunk_size,
              symmetry_index, radius):
    (triangle_ids, axis_ids, axis_values,
     template_ids, template_values) = collect(rows)
    with destination.open("w", encoding="utf-8") as output:
        output.write(DATA_HEADER.format(namespace=namespace))
        for triangle_id, value in enumerate(direct.triangle_definitions(
                rows, triangle_ids, initial_child)):
            output.write(
                f"def triDef{triangle_id} : "
                f"AtlasProjectiveView.Triangle ℚ :=\n  {value}\n\n")
        direct.emit_function_lookup(
            output, "axis", "AxisCertificate",
            [direct.axis_certificate(value) for value in axis_values],
            chunk_size, direct.axis_certificate(axis_values[0]))
        certificate_terms = []
        for keys in template_values:
            selected = [axis_ids[key] for key in keys]
            certificate_terms.append(
                direct.vector([f"axis {index}" for index in selected]))
        direct.emit_function_lookup(
            output, "localCert", "Fin 4 → AxisCertificate",
            certificate_terms, chunk_size, certificate_terms[0])
        terms = [direct.emit_row(row, triangle_ids, template_ids)
                 for row in rows]
        direct.emit_function_lookup(
            output, "getRow", "Row", terms, chunk_size, "default")
        root_triangle_id = triangle_ids[direct.triangle_key(rows[0])]
        output.write(f"""def table : Table where
  symmetryIndex := {symmetry_index}
  r := {direct.q(radius)}
  root := {rows[0]["root"]}
  triangle := triDef{root_triangle_id}
  get := getRow
  size := {len(rows)}

end Noperthedron.Nopert214.{namespace}

end
""")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    parser.add_argument("--table-index", type=int, required=True,
                        choices=range(4))
    parser.add_argument("--namespace", required=True)
    parser.add_argument("--data-chunk-size", type=int, default=64)
    parser.add_argument("--proof-part-size", type=int, default=32)
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

    first_certificate = next(row for row in rows
                             if row["kind"] == "view_local")
    symmetry_index = first_certificate["symmetry_index"]
    radius = data["tube_radius"]
    destination = Path(args.output)
    data_namespace = f"{args.namespace}Data"
    data_destination = destination.with_name(f"{data_namespace}.lean")
    emit_data(data_destination, data_namespace, rows, args.table_index,
              args.data_chunk_size, symmetry_index, radius)

    parts = []
    for start in range(0, len(rows), args.proof_part_size):
        count = min(args.proof_part_size, len(rows) - start)
        part_id = start // args.proof_part_size
        part_namespace = f"{args.namespace}Part{part_id}"
        part_destination = destination.with_name(f"{part_namespace}.lean")
        parts.append((part_namespace, start, count))
        part_destination.write_text(f"""module

public import Noperthedron.Nopert214.{data_namespace}

@[expose] public section

namespace Noperthedron.Nopert214.{part_namespace}

open AtlasProjectiveLocalViewTree SparseLocalViewTree

theorem rows_valid :
    SparseRowsValidRangeAt {symmetry_index} {direct.q(radius)}
      {data_namespace}.getRow {len(rows)} {start} {count} := by
  decide +kernel

end Noperthedron.Nopert214.{part_namespace}

end
""", encoding="utf-8")

    with destination.open("w", encoding="utf-8") as output:
        output.write("module\n\n")
        for part_namespace, _, _ in parts:
            output.write(
                f"public import Noperthedron.Nopert214.{part_namespace}\n")
        output.write(f"""
@[expose] public section

namespace Noperthedron.Nopert214.{args.namespace}

open AtlasProjectiveLocalViewTree SparseLocalViewTree

abbrev table : Table := {data_namespace}.table

""")
        previous = None
        accumulated = 0
        for part_id, (part_namespace, _, count) in enumerate(parts):
            accumulated += count
            name = f"rowsValidThrough{part_id}"
            proof = (f"{part_namespace}.rows_valid" if previous is None else
                     f"sparseRowsValidRange_append {previous} "
                     f"{part_namespace}.rows_valid")
            output.write(f"""private theorem {name} :
    SparseRowsValidRangeAt {symmetry_index} {direct.q(radius)}
      table.get {len(rows)} 0 {accumulated} :=
  {proof}

""")
            previous = name
        output.write(f"""theorem table_sparse_valid_kernel :
    SparseTableValid table := by
  refine ⟨by decide, sparseRowsValidAt_of_range {previous}, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

theorem table_valid_kernel : table.Valid :=
  Table.Valid.of_sparse table_sparse_valid_kernel

end Noperthedron.Nopert214.{args.namespace}

end
""")

    print(f"emitted {len(rows)} rows in {len(parts)} kernel proof parts; "
          f"data source is {data_destination.stat().st_size} bytes")


if __name__ == "__main__":
    main()
