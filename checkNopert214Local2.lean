import Noperthedron.Nopert214.NativeExecutable
import Noperthedron.Nopert214.PackedLocalViewTree

/-!
# Executable audit of Nopert #214 local-view chart 2

This reads the compact runtime artifact and checks the same sparse row
predicates used by the generated `native_decide` proof, but as one ordinary
release-mode executable. The rows are evaluated by native worker tasks; the
kernel-proved specification of the Boolean checker then constructs the
original semantic `Table.Valid` proof.
-/

open Noperthedron.Nopert214
open Noperthedron.Nopert214.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert214.NativeExecutable

/-- Keep this aligned with the empirically faster full constructor setting. -/
private def taskCount : Nat := 64

def main (args : List String) : IO Unit := do
  let path ← match args with
    | [path] => pure path
    | _ => throw (IO.userError "expects the local-view2.pack artifact path")
  let packed ← IO.FS.readFile path
  let table := PackedLocalViewTree.decodePackedTable 2 packed
  let firstId := (table.get 0).id
  unless firstId = 0 do
    throw (IO.userError "packed table has an invalid first row id")
  let checked ← checkLocal "2" taskCount table
  let _semanticProof : table.Valid := checked.down
