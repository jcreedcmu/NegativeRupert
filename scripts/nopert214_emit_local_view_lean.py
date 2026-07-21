#!/usr/bin/env python3
"""Emit a shared Nopert #214 projective-local view table as Lean source."""

import argparse
import json
from pathlib import Path

from nopert214_emit_lean import (
    axis_certificate,
    axis_value_key,
    emit_function_lookup,
    q,
    vector,
)


def triangle_key(row):
    return tuple(tuple(corner) for corner in row["triangle"])


def triangle_definitions(rows, triangle_ids, initial_child):
    definitions = [None] * len(triangle_ids)
    initial_triangle = ("upperWedgeTriangle" if initial_child is None else
                        f"split upperWedgeTriangle {initial_child}")
    definitions[triangle_ids[triangle_key(rows[0])]] = initial_triangle
    for row in rows:
        if row["kind"] != "view_split":
            continue
        parent_id = triangle_ids[triangle_key(row)]
        if definitions[parent_id] is None:
            raise ValueError("triangle parent was not defined before its children")
        for child_index, child_row_id in enumerate(row["children"]):
            child_id = triangle_ids[triangle_key(rows[child_row_id])]
            candidate = f"split triDef{parent_id} {child_index}"
            if definitions[child_id] is None:
                if parent_id >= child_id:
                    raise ValueError("triangle definitions are not topological")
                definitions[child_id] = candidate
    missing = [i for i, value in enumerate(definitions) if value is None]
    if missing:
        raise ValueError(f"triangles lack subdivision derivations: {missing[:10]}")
    return definitions


def local_template_key(row):
    return tuple(axis_value_key(axis) for axis in row["certificate"])


def emit_row(row, triangle_ids, local_template_ids):
    row_id = row["id"]
    triangle_id = triangle_ids[triangle_key(row)]
    tri = f"triDef{triangle_id}"
    if row["kind"] == "view_split":
        return (f".split {row_id} {vector(row['children'])} "
                f"{row['root']} ({tri})")
    if row["kind"] == "view_local":
        template_id = local_template_ids[local_template_key(row)]
        return """.certificate %d {
      interval := AtlasPose.rootInterval ℚ
      root := %d
      triangle := %s
      chart := 0
      symmetryIndex := %d
      certificate := localCert%d
      c := %s
      δ := %s
      r := %s }""" % (
            row_id, row["root"], tri, row["symmetry_index"], template_id,
            q(row["c"]), q(row["delta"]), q(row["r"]))
    raise ValueError(f"unsupported row kind: {row['kind']}")


def internal_range_proof():
    return """by
  constructor
  · norm_num
  · intro j
    fin_cases j
    constructor
    · rfl
    · intro child
      fin_cases child <;>
        exact ⟨by norm_num, by norm_num, rfl, rfl⟩"""


def kernel_range_validity(rows, range_size, symmetry_index, radius):
    size = len(rows)
    declarations = []
    nodes = []
    block_id = 0
    start = 0
    while start < size:
        if rows[start]["kind"] == "view_split":
            count = 1
            proof = internal_range_proof()
        else:
            finish = start
            while (finish < size and
                   rows[finish]["kind"] != "view_split" and
                   finish - start < range_size):
                finish += 1
            count = finish - start
            proof = "by\n  decide +kernel"
        name = f"rowsValidRange0_{block_id}"
        declarations.append(f"""private theorem {name} :
    RowsValidRangeAt {symmetry_index} {q(radius)} getRow {size} {start} {count} := {proof}
""")
        nodes.append((name, start, count))
        start += count
        block_id += 1
    level = 1
    while len(nodes) > 1:
        next_nodes = []
        for pair_id in range(0, len(nodes), 2):
            left = nodes[pair_id]
            if pair_id + 1 == len(nodes):
                next_nodes.append(left)
                continue
            right = nodes[pair_id + 1]
            if left[1] + left[2] != right[1]:
                raise ValueError("nonadjacent kernel validity ranges")
            name = f"rowsValidRange{level}_{pair_id // 2}"
            count = left[2] + right[2]
            declarations.append(f"""private theorem {name} :
    RowsValidRangeAt {symmetry_index} {q(radius)} getRow {size} {left[1]} {count} :=
  rowsValidRange_append {left[0]} {right[0]}
""")
            next_nodes.append((name, left[1], count))
        nodes = next_nodes
        level += 1
    if len(nodes) != 1 or nodes[0][1:] != (0, size):
        raise ValueError("kernel validity ranges do not cover the table")
    declarations.append(f"""theorem table_valid_kernel : table.Valid := by
  refine ⟨by decide, rowsValidAt_of_range {nodes[0][0]}, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
""")
    return "\n".join(declarations)


HEADER = """module

public import Noperthedron.Nopert214.AtlasProjectiveLocalViewTree
public meta import Noperthedron.Nopert214.AtlasProjectiveLocalViewTree

@[expose] public section

namespace Noperthedron.Nopert214.{namespace}

open AtlasProjectiveView AtlasProjectiveLocalCertificate
open AtlasProjectiveLocalViewTree
open Noperthedron.SnubCube.ProjectiveView

"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    parser.add_argument("--chunk-size", type=int, default=64)
    parser.add_argument("--kernel-range-size", type=int, default=16)
    parser.add_argument("--native-only", action="store_true")
    parser.add_argument("--table-index", type=int, choices=range(4),
                        help="emit GeneratedLocalViewN for first view child N")
    args = parser.parse_args()

    with open(args.input, "r", encoding="utf-8") as source:
        data = json.load(source)
    if not data.get("complete"):
        raise SystemExit("refusing to emit an incomplete table")
    rows = data["rows"]
    if any(row is None for row in rows):
        raise SystemExit("table contains unfilled rows")
    initial_child = data.get("initial_child")
    if args.table_index is not None and initial_child != args.table_index:
        raise SystemExit(
            f"--table-index {args.table_index} does not match "
            f"input initial_child {initial_child}")
    namespace = ("GeneratedLocalView" if args.table_index is None else
                 f"GeneratedLocalView{args.table_index}")

    triangle_ids = {}
    axis_ids = {}
    axis_values = []
    template_ids = {}
    template_values = []
    for row in rows:
        key = triangle_key(row)
        if key not in triangle_ids:
            triangle_ids[key] = len(triangle_ids)
        if row["kind"] == "view_local":
            for axis in row["certificate"]:
                key = axis_value_key(axis)
                if key not in axis_ids:
                    axis_ids[key] = len(axis_values)
                    axis_values.append(axis)
            key = local_template_key(row)
            if key not in template_ids:
                template_ids[key] = len(template_values)
                template_values.append(key)

    destination = Path(args.output)
    with destination.open("w", encoding="utf-8") as output:
        output.write(HEADER.format(namespace=namespace))
        for triangle_id, value in enumerate(
                triangle_definitions(rows, triangle_ids, initial_child)):
            output.write(
                f"def triDef{triangle_id} : "
                f"AtlasProjectiveView.Triangle ℚ :=\n  {value}\n\n")
        for axis_id, value in enumerate(axis_values):
            output.write(
                f"def axis{axis_id} : AxisCertificate := {axis_certificate(value)}\n\n")
        for template_id, keys in enumerate(template_values):
            selected = [axis_ids[key] for key in keys]
            output.write(
                f"def localCert{template_id} : Fin 4 → AxisCertificate := "
                f"{vector([f'axis{index}' for index in selected])}\n")
        output.write("\n")
        terms = [emit_row(row, triangle_ids, template_ids) for row in rows]
        emit_function_lookup(output, "getRow", "Row", terms,
                             args.chunk_size, "default")
        symmetry_index = rows[next(i for i, row in enumerate(rows)
                                   if row["kind"] == "view_local")][
                                       "symmetry_index"]
        radius = data["tube_radius"]
        root_triangle_id = triangle_ids[triangle_key(rows[0])]
        output.write(f"""def table : Table where
  symmetryIndex := {symmetry_index}
  r := {q(radius)}
  root := {rows[0]["root"]}
  triangle := triDef{root_triangle_id}
  get := getRow
  size := {len(rows)}

theorem table_valid_native : table.Valid := by native_decide

""")
        if not args.native_only:
            output.write(kernel_range_validity(
                rows, args.kernel_range_size, symmetry_index, radius))
        output.write(f"""
end Noperthedron.Nopert214.{namespace}

end
""")


if __name__ == "__main__":
    main()
