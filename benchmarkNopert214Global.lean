import Noperthedron.Nopert214.PackedSolutionTree

/-!
# Native timing audit for Nopert #214 global leaves

This is deliberately not a proof constructor.  It reads a benchmark pack
made from a live checkpoint with `--fill-pending`, selects only resolved
terminal rows, and times the exact Boolean predicate used by the final native
executable.  Pending placeholders and structural rows are never checked.
Shared-local tube rows are omitted because a live global checkpoint pack does
not include the separate local tables they require.
-/

open Noperthedron.Nopert214
open Noperthedron.Nopert214.AtlasProjectiveSolutionTree

private def rowKind? : Row → Option String
  | .projective .. => some "edge"
  | .projectiveGlobal .. => some "global"
  | .projectiveMixedGlobal .. => some "mixed-global"
  | .projectiveLocal .. => some "local"
  | .symmetryLocal .. => some "symmetry-local"
  | .symmetryTube .. => some "symmetry-tube"
  | .radiusPrune .. => some "radius"
  | .fundamentalPrune .. => some "fundamental"
  | _ => none

private def sampleEvenly (indices : List Nat) (limit : Nat) : List Nat :=
  if indices.length ≤ limit then indices
  else
    let values := indices.toArray
    (List.range limit).map fun i => values[i * values.size / limit]!

private def indicesOfKind (table : Table) (kind : String) : List Nat :=
  (List.range table.size).filter fun i => rowKind? (table.get i) = some kind

private def checkKind (table : Table) (kind : String) (limit : Nat) : IO Unit := do
  let all := indicesOfKind table kind
  let indices := sampleEvenly all limit
  if indices.isEmpty then
    IO.println s!"{kind}: no rows"
    return
  let start ← IO.monoNanosNow
  let tasks := indices.map fun i =>
    Task.spawn fun _ =>
      (i, validIxAtB table.chart table.get table.size table.sharedLocal i)
  let results := tasks.map Task.get
  let bad := results.filterMap fun (i, valid) => if valid then none else some i
  unless bad.isEmpty do
    throw (IO.userError s!"{kind}: invalid sampled rows {bad}")
  let finish ← IO.monoNanosNow
  IO.println (s!"{kind}: checked {indices.length}/{all.length} rows in " ++
    s!"{(finish - start) / 1000000} ms")
  (← IO.getStdout).flush

private def checkRow (table : Table) (index : Nat) : IO Unit := do
  unless index < table.size do
    throw (IO.userError s!"row {index} is outside table of size {table.size}")
  let start ← IO.monoNanosNow
  let valid := validIxAtB table.chart table.get table.size table.sharedLocal index
  let finish ← IO.monoNanosNow
  unless valid do
    throw (IO.userError s!"row {index} is invalid")
  IO.println (s!"row {index} ({rowKind? (table.get index)}): valid in " ++
    s!"{(finish - start) / 1000000} ms")

private def parseChart (value : String) : IO CayleyAtlas.ChartIndex := do
  match value.toNat? with
  | some 0 => pure 0
  | some 1 => pure 1
  | some 2 => pure 2
  | _ => throw (IO.userError "chart must be 0, 1, or 2")

def main (args : List String) : IO Unit := do
  let (chartText, path, selection, rowMode) ← match args with
    | [chart, path, limit] => pure (chart, path, limit, false)
    | [chart, path, "row", index] => pure (chart, path, index, true)
    | _ => throw (IO.userError
        "expects CHART PACK SAMPLE_COUNT or CHART PACK row ROW")
  let chart ← parseChart chartText
  let selected ← match selection.toNat? with
    | some limit =>
        if 0 < limit then pure limit
        else if rowMode then pure 0
        else throw (IO.userError "sample count must be positive")
    | none => throw (IO.userError "selection must be a natural number")
  let packed ← IO.FS.readFile path
  let shared : SharedLocalTables := fun _ => none
  let table := PackedSolutionTree.decodeTable chart shared packed
  IO.println s!"decoded benchmark chart {chart}: {table.size} rows"
  (← IO.getStdout).flush
  if rowMode then
    checkRow table selected
    return
  for kind in ["edge", "global", "mixed-global", "local",
      "symmetry-local", "radius", "fundamental"] do
    checkKind table kind selected
