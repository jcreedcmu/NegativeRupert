#!/usr/bin/env python3
"""Emit a completed Nopert #214 projective table as chunked Lean source."""

import argparse
import json
from pathlib import Path


def q(value):
    text = str(value)
    if "/" in text:
        numerator, denominator = text.split("/", 1)
        return f"({numerator} / {denominator})"
    return text


def vector(values):
    return "![" + ", ".join(q(value) for value in values) + "]"


def triangle(value):
    return "![" + ", ".join(vector(corner) for corner in value) + "]"


def interval_key(row):
    return tuple(row["center"]), tuple(row["widths"])


def kernel_interval_definitions(rows, interval_ids):
    """Express every interval by the split path that created it.

    This makes the child-interval equalities in `Row.ValidAt` definitional,
    avoiding fresh rational normalization inside the kernel evaluator.
    """
    definitions = [None] * len(interval_ids)
    root_key = interval_key(rows[0])
    root_id = interval_ids[root_key]
    # Generated searches may use either the full Cayley cube or the smaller
    # chart-specific rational superset of the fivefold fundamental domain.
    # Reconstruct the actual saved root instead of silently replacing it by
    # the historical full cube.  Descendants are still expressed through
    # `lowerHalf`/`upperHalf`, so split equalities remain definitional for the
    # kernel checker.
    root_center, root_widths = root_key
    definitions[root_id] = (
        f"relativeInterval {vector(root_center)} {vector(root_widths)}")
    for row in rows:
        if row["kind"] != "relative_split":
            continue
        parent_id = interval_ids[interval_key(row)]
        if definitions[parent_id] is None:
            raise ValueError("interval parent was not defined before its children")
        for half, child_row_id in zip(("lowerHalf", "upperHalf"),
                                      row["children"]):
            child = rows[child_row_id]
            child_id = interval_ids[interval_key(child)]
            candidate = f"(ivDef{parent_id}).{half} {row['coordinate']}"
            if definitions[child_id] is None:
                if parent_id >= child_id:
                    raise ValueError("interval definitions are not topological")
                definitions[child_id] = candidate
    missing = [i for i, value in enumerate(definitions) if value is None]
    if missing:
        raise ValueError(f"intervals lack split derivations: {missing[:10]}")
    return definitions


def kernel_triangle_definitions(rows, triangle_ids):
    """Express projective triangles by the subdivision path that created them."""
    definitions = [None] * len(triangle_ids)
    root_child = rows[rows[0]["child"]]
    root_id = triangle_ids[triangle_key(root_child)]
    definitions[root_id] = "upperWedgeTriangle"
    for row in rows:
        if row["kind"] != "view_split":
            continue
        parent_id = triangle_ids[triangle_key(row)]
        if definitions[parent_id] is None:
            raise ValueError("triangle parent was not defined before its children")
        for child_index, child_row_id in enumerate(row["children"]):
            child = rows[child_row_id]
            child_id = triangle_ids[triangle_key(child)]
            candidate = f"split triDef{parent_id} {child_index}"
            if definitions[child_id] is None:
                if parent_id >= child_id:
                    raise ValueError("triangle definitions are not topological")
                definitions[child_id] = candidate
    missing = [i for i, value in enumerate(definitions) if value is None]
    if missing:
        raise ValueError(f"triangles lack subdivision derivations: {missing[:10]}")
    return definitions


def triangle_key(row):
    return tuple(tuple(corner) for corner in row["triangle"])


def edge_template_key(row):
    certificate = row["certificate"]
    return (tuple(certificate["cycle"]),
            tuple(contact["nonzero_witness"]
                  for contact in certificate["contacts"]))


def edge_inner_key(row):
    return tuple(contact["inner_index"]
                 for contact in row["certificate"]["contacts"])


def axis_value_key(axis):
    return tuple(tuple(axis[key]) if isinstance(axis[key], list)
                 else axis[key] for key in
                 ("edge_start", "edge_finish", "edge_start2", "edge_finish2",
                  "mix", "support_index", "nonzero_witness", "B"))


def axis_key(row):
    return axis_value_key(row["certificate"]["axis"])


def local_template_key(row):
    return tuple(axis_value_key(axis)
                 for axis in row["certificate"]["certificates"])


def region(row, triangle_ids):
    if row["kind"] == "view_root":
        return ".sphere"
    return f".triangle {row['root']} (tri {triangle_ids[triangle_key(row)]})"


def axis_certificate(axis):
    return """{
      edgeStart := %s
      edgeFinish := %s
      edgeStart₂ := %s
      edgeFinish₂ := %s
      mix := %s
      index := %s
      nonzeroWitness := %s
      B := %s }""" % (
        vector(axis["edge_start"]), vector(axis["edge_finish"]),
        vector(axis["edge_start2"]), vector(axis["edge_finish2"]),
        vector(axis["mix"]), vector(axis["support_index"]),
        vector(axis["nonzero_witness"]), q(axis["B"]))


def emit_row(row, chart, interval_ids, triangle_ids, edge_template_ids,
             edge_inner_ids, axis_ids, global_inner_ids, local_template_ids,
             kernel_friendly=False):
    kind = row["kind"]
    row_id = row["id"]
    interval_id = interval_ids[interval_key(row)]
    iv = (f"ivDef{interval_id}" if kernel_friendly else
          f"iv {interval_id}")
    tri = None if kind == "view_root" else \
        ((f"triDef{triangle_ids[triangle_key(row)]}" if kernel_friendly else
          f"tri {triangle_ids[triangle_key(row)]}"))
    if kind == "view_root":
        return f".viewRoot {row_id} {row['child']} ({iv})"
    if kind == "view_split":
        return (f".viewSplit {row_id} {vector(row['children'])} "
                f"({iv}) {row['root']} ({tri})")
    if kind == "relative_split":
        children = row["children"]
        return (f".cayleySplit {row_id} {children[0]} {children[1]} "
                f"{row['coordinate']} ({iv}) ({region(row, triangle_ids)})")
    if kind == "radius":
        return f".radiusPrune {row_id} ({iv}) ({region(row, triangle_ids)})"
    if kind == "fundamental_prune":
        direction = ".positive" if row["direction"] == 1 else ".negative"
        return (f".fundamentalPrune {row_id} "
                f"{{ interval := {iv}, chart := {chart}, "
                f"direction := {direction} }} "
                f"({region(row, triangle_ids)})")
    if kind == "edge":
        certificate = row["certificate"]
        contacts = certificate["contacts"]
        template_id = edge_template_ids[edge_template_key(row)]
        inner_id = edge_inner_ids[edge_inner_key(row)]
        return """.projective %d {
      interval := %s
      root := %d
      triangle := %s
      chart := %d
      edgePred := edgePred%d
      outerIndex := edgeOuter%d
      innerIndex := edgeInner%d
      nonzeroWitness := edgeWitness%d
      ballMultiplier := %s }""" % (
            row_id, iv, row["root"], tri,
            chart, template_id, template_id, inner_id, template_id,
            vector(certificate["ball_multipliers"]))
    if kind == "global":
        certificate = row["certificate"]
        selected_axis = axis_ids[axis_key(row)]
        selected_inner = global_inner_ids[tuple(certificate["inner_index"])]
        return """.projectiveGlobal %d {
      interval := %s
      root := %d
      triangle := %s
      chart := %d
      certificate := axis%d
      innerIndex := globalInner%d
      ballMultiplier := %s }""" % (
            row_id, iv, row["root"], tri,
            chart, selected_axis, selected_inner,
            q(certificate["ball_multiplier"]))
    if kind == "local":
        certificate = row["certificate"]
        template_id = local_template_ids[local_template_key(row)]
        return """.projectiveLocal %d {
      interval := %s
      root := %d
      triangle := %s
      chart := %d
      symmetryIndex := %d
      certificate := localCert%d
      c := %s
      δ := %s
      r := %s }""" % (
            row_id, iv, row["root"], tri, chart,
            certificate["symmetry_index"], template_id,
            q(certificate["c"]), q(certificate["delta"]),
            q(certificate["r"]))
    if kind == "symmetry_tube":
        return """.symmetryTube %d {
      interval := %s
      chart := %d
      symmetryIndex := %d
      r := %s }
      (%s)""" % (
            row_id, iv, chart, row["symmetry_index"], q(row["radius"]),
            region(row, triangle_ids))
    raise ValueError(f"unsupported row kind: {kind}")


HEADER = """module

public import Noperthedron.Nopert214.AtlasProjectiveSolutionTree
public meta import Noperthedron.Nopert214.AtlasProjectiveSolutionTree
{shared_import}

@[expose] public section

namespace Noperthedron.Nopert214.GeneratedChart{chart}

open AtlasProjectiveSolutionTree AtlasProjectiveView
open AtlasProjectiveEdgeCertificate AtlasProjectiveGlobalCertificate
open AtlasProjectiveLocalCertificate

def relativeInterval (center radius : Fin 3 → ℚ) :
    AtlasProjectiveSolutionTree.Interval :=
  AtlasInterval.mk
    {{ θ := 0, φ := 0,
      x := center 0 - |radius 0|,
      y := center 1 - |radius 1|,
      z := center 2 - |radius 2| }}
    {{ θ := 8 / 5, φ := 4,
      x := center 0 + |radius 0|,
      y := center 1 + |radius 1|,
      z := center 2 + |radius 2| }}
    (by
      rw [AtlasPose.le_iff]
      exact ⟨by norm_num, by norm_num,
        by linarith [abs_nonneg (radius 0)],
        by linarith [abs_nonneg (radius 1)],
        by linarith [abs_nonneg (radius 2)]⟩)

"""


FOOTER = """
def getRow (i : ℕ) : AtlasProjectiveSolutionTree.Row :=
  (chunks[i / {chunk_size}]!)[i % {chunk_size}]!

def table : AtlasProjectiveSolutionTree.Table where
  chart := {chart}
  get := getRow
  size := {size}
{shared_field}

{validity}
{audit}

end Noperthedron.Nopert214.GeneratedChart{chart}

end
"""


def emit_function_lookup(output, name, type_name, rendered_values,
                         chunk_size, default):
    """Emit a kernel-reducible chunked `Nat → type_name` lookup.

    Array `get!` is excellent for `native_decide`, but large nested arrays are
    expensive for kernel reduction.  Literal equation functions let a small
    `decide +kernel` range proof unfold only the entries it checks.
    """
    chunk_names = []
    chunk_count = (len(rendered_values) + chunk_size - 1) // chunk_size
    for start in range(0, len(rendered_values), chunk_size):
        chunk_id = start // chunk_size
        chunk_name = name if chunk_count == 1 else f"{name}Chunk{chunk_id}"
        chunk_names.append(chunk_name)
        output.write(f"def {chunk_name} : ℕ → {type_name}\n")
        for local_id, value in enumerate(
                rendered_values[start:start+chunk_size]):
            output.write(f"  | {local_id} => {value}\n")
        output.write(f"  | _ => {default}\n\n")
    if len(chunk_names) == 1:
        return
    output.write(f"def {name}Chunks : ℕ → ℕ → {type_name}\n")
    for chunk_id, chunk_name in enumerate(chunk_names):
        output.write(f"  | {chunk_id} => {chunk_name}\n")
    output.write(f"  | _ => fun _ => {default}\n\n")
    output.write(f"def {name} (i : ℕ) : {type_name} :=\n")
    output.write(
        f"  {name}Chunks (i / {chunk_size}) (i % {chunk_size})\n\n")


def kernel_internal_range_proof(kind):
    """Proof of a singleton internal-node range using definitional links."""
    if kind == "view_root":
        valid = "exact ⟨by norm_num, by norm_num, rfl, rfl⟩"
    elif kind == "relative_split":
        valid = ("exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, "
                 "rfl, rfl, rfl, rfl⟩")
    elif kind == "view_split":
        valid = """intro child
      fin_cases child <;>
        exact ⟨by norm_num, by norm_num, rfl, rfl⟩"""
    else:
        raise ValueError(f"not an internal row kind: {kind}")
    return f"""by
  constructor
  · norm_num
  · intro j
    fin_cases j
    constructor
    · rfl
    · {valid}"""


def kernel_range_validity(chart, rows, range_size, shared):
    """Emit local kernel checks and a balanced proof joining their ranges.

    Leaf runs are decided in chunks.  Internal rows are singleton ranges with
    explicit definitional proofs, since deciding structural interval equality
    would unnecessarily normalize equal rational endpoints.
    """
    size = len(rows)
    internal_kinds = {"view_root", "relative_split", "view_split"}
    declarations = []
    nodes = []
    block_id = 0
    start = 0
    while start < size:
        kind = rows[start]["kind"]
        if kind in internal_kinds:
            count = 1
            proof = kernel_internal_range_proof(kind)
        else:
            finish = start
            while (finish < size and
                   rows[finish]["kind"] not in internal_kinds and
                   finish-start < range_size):
                finish += 1
            count = finish-start
            proof = "by\n  decide +kernel"
        name = f"rowsValidRange0_{block_id}"
        declarations.append(f"""private theorem {name} :
    RowsValidRangeAt {chart} getRow {size} {start} {count} {shared} := {proof}
""")
        nodes.append((name, start, count))
        start += count
        block_id += 1
    level = 1
    while len(nodes) > 1:
        next_nodes = []
        for pair_id in range(0, len(nodes), 2):
            left = nodes[pair_id]
            if pair_id+1 == len(nodes):
                next_nodes.append(left)
                continue
            right = nodes[pair_id+1]
            if left[1] + left[2] != right[1]:
                raise ValueError("nonadjacent kernel validity ranges")
            name = f"rowsValidRange{level}_{pair_id // 2}"
            count = left[2] + right[2]
            declarations.append(f"""private theorem {name} :
    RowsValidRangeAt {chart} getRow {size} {left[1]} {count} {shared} :=
  rowsValidRange_append {left[0]} {right[0]}
""")
            next_nodes.append((name, left[1], count))
        nodes = next_nodes
        level += 1
    if len(nodes) != 1 or nodes[0][1:] != (0, size):
        raise ValueError("kernel validity ranges do not cover the table")
    declarations.append(f"""theorem table_valid_kernel : table.Valid := by
  refine ⟨by decide, rowsValidAt_of_range {nodes[0][0]}, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · {"trivial" if shared == "none" else "exact GeneratedLocalView.table_valid_kernel"}
""")
    return "\n".join(declarations)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    parser.add_argument("--chunk-size", type=int, default=64,
                        help="number of solution rows per Lean definition")
    parser.add_argument("--interval-chunk-size", type=int, default=16,
                        help="number of interned intervals per Lean definition")
    parser.add_argument("--unchecked-prefix", type=int)
    parser.add_argument("--audit-first-local", action="store_true")
    parser.add_argument("--kernel-friendly", action="store_true",
                        help="emit equation-function data and chunked kernel proofs")
    parser.add_argument("--kernel-range-size", type=int, default=32,
                        help="rows checked by each kernel proof")
    parser.add_argument("--shared-local-view", action="store_true",
                        help="attach GeneratedLocalView.table for symmetry-tube rows")
    args = parser.parse_args()

    with open(args.input, "r", encoding="utf-8") as source:
        data = json.load(source)
    if args.unchecked_prefix is None and not data.get("complete"):
        raise SystemExit("refusing to emit an incomplete table")
    rows = data["rows"]
    if args.unchecked_prefix is not None:
        rows = [row for row in rows if row is not None][
            :args.unchecked_prefix]
    if any(row is None for row in rows):
        raise SystemExit("table contains unfilled rows")
    chart = data["chart"]
    has_tube = any(row is not None and row["kind"] == "symmetry_tube"
                   for row in rows)
    if has_tube and not args.shared_local_view:
        raise SystemExit("symmetry-tube rows require --shared-local-view")

    interval_values = []
    interval_ids = {}
    triangle_values = []
    triangle_ids = {}
    edge_template_values = []
    edge_template_ids = {}
    edge_inner_values = []
    edge_inner_ids = {}
    axis_values = []
    axis_ids = {}
    global_inner_values = []
    global_inner_ids = {}
    local_template_values = []
    local_template_ids = {}
    for row in rows:
        key = interval_key(row)
        if key not in interval_ids:
            interval_ids[key] = len(interval_values)
            interval_values.append(key)
        if row["kind"] != "view_root":
            key = triangle_key(row)
            if key not in triangle_ids:
                triangle_ids[key] = len(triangle_values)
                triangle_values.append(key)
        if row["kind"] == "edge":
            key = edge_template_key(row)
            if key not in edge_template_ids:
                edge_template_ids[key] = len(edge_template_values)
                edge_template_values.append(key)
            key = edge_inner_key(row)
            if key not in edge_inner_ids:
                edge_inner_ids[key] = len(edge_inner_values)
                edge_inner_values.append(key)
        if row["kind"] == "global":
            key = axis_key(row)
            if key not in axis_ids:
                axis_ids[key] = len(axis_values)
                axis_values.append(row["certificate"]["axis"])
            key = tuple(row["certificate"]["inner_index"])
            if key not in global_inner_ids:
                global_inner_ids[key] = len(global_inner_values)
                global_inner_values.append(key)
        if row["kind"] == "local":
            for axis in row["certificate"]["certificates"]:
                key = axis_value_key(axis)
                if key not in axis_ids:
                    axis_ids[key] = len(axis_values)
                    axis_values.append(axis)
            key = local_template_key(row)
            if key not in local_template_ids:
                local_template_ids[key] = len(local_template_values)
                local_template_values.append(key)

    destination = Path(args.output)
    with destination.open("w", encoding="utf-8") as output:
        output.write(HEADER.format(
            chart=chart,
            shared_import=(
                "public import Noperthedron.Nopert214.GeneratedLocalView"
                if args.shared_local_view else "")))
        if args.kernel_friendly:
            interval_definitions = kernel_interval_definitions(
                rows, interval_ids)
            for interval_id, value in enumerate(interval_definitions):
                output.write(
                    f"def ivDef{interval_id} : "
                    "AtlasProjectiveSolutionTree.Interval :=\n")
                output.write(f"  {value}\n\n")
            emit_function_lookup(
                output, "iv", "AtlasProjectiveSolutionTree.Interval",
                [f"ivDef{i}" for i in range(len(interval_values))],
                args.interval_chunk_size, "AtlasPose.rootInterval ℚ")
            triangle_definitions = kernel_triangle_definitions(
                rows, triangle_ids)
            for triangle_id, value in enumerate(triangle_definitions):
                output.write(
                    f"def triDef{triangle_id} : "
                    "AtlasProjectiveSolutionTree.Triangle :=\n")
                output.write(f"  {value}\n\n")
            emit_function_lookup(
                output, "tri", "AtlasProjectiveSolutionTree.Triangle",
                [f"triDef{i}" for i in range(len(triangle_values))],
                args.interval_chunk_size, "rootTriangle 0")
        else:
            interval_chunk_names = []
            for start in range(0, len(interval_values),
                               args.interval_chunk_size):
                name = f"intervalDataChunk{start // args.interval_chunk_size}"
                interval_chunk_names.append(name)
                output.write(f"def {name} : Array ((Fin 3 → ℚ) × (Fin 3 → ℚ)) := #[\n")
                output.write(",\n".join(
                    f"  ({vector(center)}, {vector(widths)})"
                    for center, widths in
                    interval_values[start:start+args.interval_chunk_size]))
                output.write("\n]\n\n")
            output.write("def intervalDataChunks : "
                         "Array (Array ((Fin 3 → ℚ) × (Fin 3 → ℚ))) := #[")
            output.write(", ".join(interval_chunk_names))
            output.write("]\n")
            output.write("def iv (i : ℕ) : AtlasProjectiveSolutionTree.Interval :=\n")
            output.write(f"  let data := (intervalDataChunks[i / {args.interval_chunk_size}]!)"
                         f"[i % {args.interval_chunk_size}]!\n")
            output.write("  relativeInterval data.1 data.2\n\n")
            output.write("def triangles : Array AtlasProjectiveSolutionTree.Triangle := #[\n")
            output.write(",\n".join(
                f"  {triangle(value)}" for value in triangle_values))
            output.write("\n]\n\n")
            output.write("def tri (i : ℕ) : AtlasProjectiveSolutionTree.Triangle := triangles[i]!\n\n")
        for template_id, (cycle, witnesses) in enumerate(edge_template_values):
            output.write(f"def edgePred{template_id} : ℕ := {len(cycle)-1}\n")
            output.write(f"def edgeOuter{template_id} : Fin (edgePred{template_id} + 1) → VertexIndex := {vector(cycle)}\n")
            output.write(f"def edgeWitness{template_id} : Fin (edgePred{template_id} + 1) → VertexIndex := {vector(witnesses)}\n\n")
        for inner_id, values in enumerate(edge_inner_values):
            output.write(f"def edgeInner{inner_id} : Fin {len(values)} → VertexIndex := {vector(values)}\n")
        output.write("\n")
        for axis_id, value in enumerate(axis_values):
            output.write(f"def axis{axis_id} : AxisCertificate := {axis_certificate(value)}\n\n")
        for inner_id, values in enumerate(global_inner_values):
            output.write(f"def globalInner{inner_id} : Fin 3 → VertexIndex := {vector(values)}\n")
        output.write("\n")
        for template_id, keys in enumerate(local_template_values):
            selected = [axis_ids[key] for key in keys]
            output.write(f"def localCert{template_id} : Fin 4 → AxisCertificate := "
                         f"{vector([f'axis{index}' for index in selected])}\n")
        output.write("\n")
        terms = [emit_row(row, chart, interval_ids, triangle_ids,
                          edge_template_ids, edge_inner_ids, axis_ids,
                          global_inner_ids, local_template_ids,
                          args.kernel_friendly)
                 for row in rows]
        if args.kernel_friendly:
            emit_function_lookup(
                output, "getRow", "AtlasProjectiveSolutionTree.Row",
                terms, args.chunk_size, "default")
        else:
            chunk_names = []
            for start in range(0, len(rows), args.chunk_size):
                name = f"chunk{start // args.chunk_size}"
                chunk_names.append(name)
                output.write(
                    f"def {name} : Array AtlasProjectiveSolutionTree.Row := #[\n")
                output.write(",\n".join(
                    "  " + term for term in terms[start:start+args.chunk_size]))
                output.write("\n]\n\n")
            output.write("def chunks : Array "
                         "(Array AtlasProjectiveSolutionTree.Row) := #[")
            output.write(", ".join(chunk_names))
            output.write("]\n")
        validity = ("theorem table_valid_native : table.Valid := by "
                    "native_decide" if args.unchecked_prefix is None else "")
        audit = ""
        if args.audit_first_local:
            first_local = next(
                (i for i, row in enumerate(rows) if row["kind"] == "local"),
                None)
            if first_local is None:
                raise SystemExit("no projective-local row available to audit")
            audit = f"""theorem first_local_valid :
    (getRow {first_local}).ValidAt {chart} getRow {len(rows)} none := by
  native_decide

theorem first_local_valid_kernel :
    (getRow {first_local}).ValidAt {chart} getRow {len(rows)} none := by
  decide +kernel"""
        if args.kernel_friendly:
            shared = ("some GeneratedLocalView.table"
                      if args.shared_local_view else "none")
            shared_field = ("  sharedLocal := some GeneratedLocalView.table"
                            if args.shared_local_view else "")
            output.write(f"""def table : AtlasProjectiveSolutionTree.Table where
  chart := {chart}
  get := getRow
  size := {len(rows)}
{shared_field}

theorem table_valid_native : table.Valid := by native_decide

{kernel_range_validity(chart, rows, args.kernel_range_size, shared)}
{audit}

end Noperthedron.Nopert214.GeneratedChart{chart}

end
""")
        else:
            output.write(FOOTER.format(
                chart=chart, validity=validity, audit=audit,
                chunk_size=args.chunk_size, size=len(rows),
                shared_field=(
                    "  sharedLocal := some GeneratedLocalView.table"
                    if args.shared_local_view else "")))


if __name__ == "__main__":
    main()
