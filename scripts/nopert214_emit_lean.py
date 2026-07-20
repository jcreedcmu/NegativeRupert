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


def emit_row(row, chart, interval_ids, triangle_ids):
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
        return """.projective %d {
      interval := %s
      root := %d
      triangle := %s
      chart := %d
      edgePred := %d
      outerIndex := %s
      innerIndex := %s
      nonzeroWitness := %s
      ballMultiplier := %s }""" % (
            row_id, iv, row["root"], tri,
            chart, len(contacts)-1,
            vector([contact["outer_index"] for contact in contacts]),
            vector([contact["inner_index"] for contact in contacts]),
            vector([contact["nonzero_witness"] for contact in contacts]),
            vector(certificate["ball_multipliers"]))
    if kind == "global":
        certificate = row["certificate"]
        return """.projectiveGlobal %d {
      interval := %s
      root := %d
      triangle := %s
      chart := %d
      certificate := %s
      innerIndex := %s
      ballMultiplier := %s }""" % (
            row_id, iv, row["root"], tri,
            chart, axis_certificate(certificate["axis"]),
            vector(certificate["inner_index"]),
            q(certificate["ball_multiplier"]))
    raise ValueError(f"unsupported row kind: {kind}")


HEADER = """module

public import Noperthedron.Nopert214.AtlasProjectiveSolutionTree
public meta import Noperthedron.Nopert214.AtlasProjectiveSolutionTree

@[expose] public section

namespace Noperthedron.Nopert214.GeneratedChart{chart}

open AtlasProjectiveSolutionTree AtlasProjectiveView
open AtlasProjectiveEdgeCertificate AtlasProjectiveGlobalCertificate

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
def rows : Array AtlasProjectiveSolutionTree.Row := chunks.flatten

def table : AtlasProjectiveSolutionTree.Table where
  chart := {chart}
  get := fun i => rows[i]!
  size := rows.size

theorem table_valid_native : table.Valid := by native_decide

end Noperthedron.Nopert214.GeneratedChart{chart}

end
"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    parser.add_argument("--chunk-size", type=int, default=512)
    args = parser.parse_args()

    with open(args.input, "r", encoding="utf-8") as source:
        data = json.load(source)
    if not data.get("complete"):
        raise SystemExit("refusing to emit an incomplete table")
    rows = data["rows"]
    if any(row is None for row in rows):
        raise SystemExit("table contains unfilled rows")
    chart = data["chart"]

    interval_values = []
    interval_ids = {}
    triangle_values = []
    triangle_ids = {}
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

    destination = Path(args.output)
    with destination.open("w", encoding="utf-8") as output:
        output.write(HEADER.format(chart=chart))
        output.write("def intervalData : Array ((Fin 3 → ℚ) × (Fin 3 → ℚ)) := #[\n")
        output.write(",\n".join(
            f"  ({vector(center)}, {vector(widths)})"
            for center, widths in interval_values))
        output.write("\n]\n\n")
        output.write("def intervals : Array AtlasProjectiveSolutionTree.Interval :=\n")
        output.write("  intervalData.map fun data => relativeInterval data.1 data.2\n\n")
        output.write("def iv (i : ℕ) : AtlasProjectiveSolutionTree.Interval := intervals[i]!\n\n")
        output.write("def triangles : Array AtlasProjectiveSolutionTree.Triangle := #[\n")
        output.write(",\n".join(
            f"  {triangle(value)}" for value in triangle_values))
        output.write("\n]\n\n")
        output.write("def tri (i : ℕ) : AtlasProjectiveSolutionTree.Triangle := triangles[i]!\n\n")
        chunk_names = []
        for start in range(0, len(rows), args.chunk_size):
            name = f"chunk{start // args.chunk_size}"
            chunk_names.append(name)
            output.write(f"def {name} : Array AtlasProjectiveSolutionTree.Row := #[\n")
            terms = [emit_row(row, chart, interval_ids, triangle_ids)
                     for row in rows[start:start+args.chunk_size]]
            output.write(",\n".join("  " + term for term in terms))
            output.write("\n]\n\n")
        output.write("def chunks : Array (Array AtlasProjectiveSolutionTree.Row) := #[")
        output.write(", ".join(chunk_names))
        output.write("]\n")
        output.write(FOOTER.format(chart=chart))


if __name__ == "__main__":
    main()
