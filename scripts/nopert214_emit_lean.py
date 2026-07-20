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
             edge_inner_ids, axis_ids, global_inner_ids, local_template_ids):
    kind = row["kind"]
    row_id = row["id"]
    iv = f"iv {interval_ids[interval_key(row)]}"
    tri = None if kind == "view_root" else \
        f"tri {triangle_ids[triangle_key(row)]}"
    if kind == "view_root":
        return f".viewRoot {row_id} {vector(row['children'])} ({iv})"
    if kind == "view_split":
        return (f".viewSplit {row_id} {vector(row['children'])} "
                f"({iv}) {row['root']} ({tri})")
    if kind == "relative_split":
        children = row["children"]
        return (f".cayleySplit {row_id} {children[0]} {children[1]} "
                f"{row['coordinate']} ({iv}) ({region(row, triangle_ids)})")
    if kind == "radius":
        return f".radiusPrune {row_id} ({iv}) ({region(row, triangle_ids)})"
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
    raise ValueError(f"unsupported row kind: {kind}")


HEADER = """module

public import Noperthedron.Nopert214.AtlasProjectiveSolutionTree
public meta import Noperthedron.Nopert214.AtlasProjectiveSolutionTree

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

{validity}
{audit}

end Noperthedron.Nopert214.GeneratedChart{chart}

end
"""


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
        output.write(HEADER.format(chart=chart))
        interval_chunk_names = []
        for start in range(0, len(interval_values), args.interval_chunk_size):
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
        chunk_names = []
        for start in range(0, len(rows), args.chunk_size):
            name = f"chunk{start // args.chunk_size}"
            chunk_names.append(name)
            output.write(f"def {name} : Array AtlasProjectiveSolutionTree.Row := #[\n")
            terms = [emit_row(row, chart, interval_ids, triangle_ids,
                              edge_template_ids, edge_inner_ids, axis_ids,
                              global_inner_ids, local_template_ids)
                     for row in rows[start:start+args.chunk_size]]
            output.write(",\n".join("  " + term for term in terms))
            output.write("\n]\n\n")
        output.write("def chunks : Array (Array AtlasProjectiveSolutionTree.Row) := #[")
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
    (getRow {first_local}).ValidAt {chart} getRow {len(rows)} := by
  native_decide

theorem first_local_valid_kernel :
    (getRow {first_local}).ValidAt {chart} getRow {len(rows)} := by
  decide +kernel"""
        output.write(FOOTER.format(
            chart=chart, validity=validity, audit=audit,
            chunk_size=args.chunk_size, size=len(rows)))


if __name__ == "__main__":
    main()
