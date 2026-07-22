#!/usr/bin/env python3
"""Emit a parallel, kernel-only global-table proof for Nopert #214.

The exact table data lives in one generated module.  Independent proof
modules validate bounded contiguous ranges, so Lake can cache and parallelize
the expensive rational reductions without asking one Lean process to retain
the full proof environment.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

import nopert214_emit_lean as direct


INTERNAL_KINDS = {"view_root", "relative_split", "view_split"}


def joined_ranges(declarations, nodes, prefix, theorem_type):
    """Append a balanced tree of range-joining declarations."""
    level = 0
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
            name = f"{prefix}{level}_{pair_id // 2}"
            count = left[2] + right[2]
            declarations.append(f"""private theorem {name} :
    {theorem_type(left[1], count)} :=
  rowsValidRange_append {left[0]} {right[0]}
""")
            next_nodes.append((name, left[1], count))
        nodes = next_nodes
        level += 1
    return nodes[0]


def part_text(namespace, data_namespace, chart, rows, start, count,
              kernel_range_size, shared):
    size = len(rows)

    def theorem_type(block_start, block_count):
        return (f"RowsValidRangeAt {chart} {data_namespace}.getRow {size} "
                f"{block_start} {block_count} {shared}")

    declarations = []
    nodes = []
    cursor = start
    finish = start + count
    block_id = 0
    while cursor < finish:
        kind = rows[cursor]["kind"]
        if kind in INTERNAL_KINDS:
            block_count = 1
            proof = direct.kernel_internal_range_proof(kind)
        else:
            block_finish = cursor
            while (block_finish < finish and
                   rows[block_finish]["kind"] not in INTERNAL_KINDS and
                   block_finish - cursor < kernel_range_size):
                block_finish += 1
            block_count = block_finish - cursor
            proof = "by\n  decide +kernel"
        name = f"block{block_id}"
        declarations.append(f"""private theorem {name} :
    {theorem_type(cursor, block_count)} := {proof}
""")
        nodes.append((name, cursor, block_count))
        cursor += block_count
        block_id += 1
    final = joined_ranges(
        declarations, nodes, "joined", theorem_type)
    if final[1:] != (start, count):
        raise ValueError("proof part does not cover its requested range")
    declarations.append(f"""theorem rows_valid :
    {theorem_type(start, count)} :=
  {final[0]}
""")
    body = "\n".join(declarations)
    return f"""module

public import Noperthedron.Nopert214.{data_namespace}

@[expose] public section

namespace Noperthedron.Nopert214.{namespace}

open AtlasProjectiveSolutionTree

{body}
end Noperthedron.Nopert214.{namespace}

end
"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    parser.add_argument("--namespace", required=True)
    parser.add_argument("--data-chunk-size", type=int, default=64)
    parser.add_argument("--interval-chunk-size", type=int, default=16)
    parser.add_argument("--kernel-range-size", type=int, default=32)
    parser.add_argument("--proof-part-size", type=int, default=256)
    parser.add_argument("--no-shared-local", action="store_true",
                        help="attach no shared local tables (smoke tests only)")
    args = parser.parse_args()

    with open(args.input, encoding="utf-8") as source:
        data = json.load(source)
    if not data.get("complete"):
        raise SystemExit("refusing to emit an incomplete table")
    rows = data["rows"]
    if any(row is None for row in rows):
        raise SystemExit("table contains unfilled rows")
    chart = int(data["chart"])
    destination = Path(args.output)
    data_namespace = f"{args.namespace}KernelData"
    data_destination = destination.with_name(f"{data_namespace}.lean")

    direct_script = Path(__file__).with_name("nopert214_emit_lean.py")
    data_command = [
        sys.executable, str(direct_script), args.input,
        str(data_destination), "--namespace", data_namespace,
        "--kernel-friendly", "--data-only",
        "--chunk-size", str(args.data_chunk_size),
        "--interval-chunk-size", str(args.interval_chunk_size),
    ]
    if not args.no_shared_local:
        data_command.append("--shared-local-view")
    subprocess.run(data_command, check=True)

    shared = (("fun _ => none") if args.no_shared_local else
              "GeneratedLocalViews.tables")

    parts = []
    for start in range(0, len(rows), args.proof_part_size):
        count = min(args.proof_part_size, len(rows) - start)
        part_id = start // args.proof_part_size
        part_namespace = f"{args.namespace}KernelPart{part_id}"
        part_destination = destination.with_name(
            f"{part_namespace}.lean")
        part_destination.write_text(part_text(
            part_namespace, data_namespace, chart, rows, start, count,
            args.kernel_range_size, shared), encoding="utf-8")
        parts.append((part_namespace, start, count))

    def theorem_type(start, count):
        return (f"RowsValidRangeAt {chart} table.get {len(rows)} "
                f"{start} {count} {shared}")

    declarations = []
    nodes = []
    for part_namespace, start, count in parts:
        name = f"part{start // args.proof_part_size}"
        declarations.append(f"""private theorem {name} :
    {theorem_type(start, count)} :=
  {part_namespace}.rows_valid
""")
        nodes.append((name, start, count))
    final = joined_ranges(
        declarations, nodes, "allRows", theorem_type)
    if final[1:] != (0, len(rows)):
        raise ValueError("kernel proof parts do not cover the table")

    with destination.open("w", encoding="utf-8") as output:
        output.write("module\n\n")
        for part_namespace, _, _ in parts:
            output.write(
                f"public import Noperthedron.Nopert214.{part_namespace}\n")
        output.write(f"""
@[expose] public section

namespace Noperthedron.Nopert214.{args.namespace}

open AtlasProjectiveSolutionTree

abbrev table : Table := {data_namespace}.table

{"\n".join(declarations)}
theorem table_valid_kernel : table.Valid := by
  refine ⟨by decide, rowsValidAt_of_range {final[0]}, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · {"intro index\n    fin_cases index <;> trivial" if args.no_shared_local else "exact GeneratedLocalViews.tables_valid_kernel"}

end Noperthedron.Nopert214.{args.namespace}

end
""")

    print(f"emitted {len(rows)} rows in {len(parts)} kernel proof parts; "
          f"data source is {data_destination.stat().st_size} bytes")


if __name__ == "__main__":
    main()
