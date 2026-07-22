import Noperthedron.Nopert214.PackedLocalViewTree
import Noperthedron.Nopert214.SparseLocalViewTree

/-! Native timing and validity audit for packed Nopert #214 local rows. -/

open Noperthedron.Nopert214
open Noperthedron.Nopert214.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert214.SparseLocalViewTree

private def certificateIndices (table : Table) : List Nat :=
  (List.range table.size).filter fun i => match table.get i with
    | .certificate .. => true
    | .split .. => false

private def sampleEvenly (indices : List Nat) (limit : Nat) : List Nat :=
  if indices.length ≤ limit then indices
  else
    let values := indices.toArray
    (List.range limit).map fun i => values[i * values.size / limit]!

private def checkIndices (table : Table) (indices : List Nat) : IO Unit := do
  let start ← IO.monoNanosNow
  let tasks := indices.map fun i => Task.spawn fun _ =>
    (i, sparseValidIxAtB table.symmetryIndex table.r
      table.get table.size i)
  let results := tasks.map Task.get
  let bad := results.filterMap fun (i, valid) => if valid then none else some i
  unless bad.isEmpty do
    throw (IO.userError s!"invalid sampled rows {bad}")
  let finish ← IO.monoNanosNow
  IO.println (s!"checked {indices.length} local rows in " ++
    s!"{(finish-start)/1000000} ms")

private def parseIndex (value : String) : IO Nat := do
  match value.toNat? with
  | some index =>
      if index < 4 then pure index
      else throw (IO.userError "table index must be 0, 1, 2, or 3")
  | none => throw (IO.userError "table index must be a natural number")

def main (args : List String) : IO Unit := do
  let (indexText, path, sampleText?, rowText?) ← match args with
    | [index, path, sample] =>
        pure (index, path, some sample, (none : Option String))
    | [index, path, "row", row] =>
        pure (index, path, (none : Option String), some row)
    | _ => throw (IO.userError (
        "expects TABLE_INDEX PACK SAMPLE_COUNT or TABLE_INDEX PACK row ROW"))
  let index ← parseIndex indexText
  let packed ← IO.FS.readFile path
  let decodeStart ← IO.monoNanosNow
  let table := PackedLocalViewTree.decodePackedTable index packed
  let firstId := (table.get 0).id
  unless firstId = 0 do
    throw (IO.userError "decoded table has an invalid first row")
  let decodeFinish ← IO.monoNanosNow
  IO.println (s!"decoded {table.size} local rows in " ++
    s!"{(decodeFinish-decodeStart)/1000000} ms")
  (← IO.getStdout).flush
  let indices ← match sampleText?, rowText? with
    | some sampleText, none =>
        match sampleText.toNat? with
        | some sample =>
            if 0 < sample then
              pure (sampleEvenly (certificateIndices table) sample)
            else throw (IO.userError "sample count must be positive")
        | none => throw (IO.userError "sample count must be a natural number")
    | none, some rowText =>
        match rowText.toNat? with
        | some row => pure [row]
        | none => throw (IO.userError "row must be a natural number")
    | _, _ => throw (IO.userError "invalid row selection")
  checkIndices table indices
