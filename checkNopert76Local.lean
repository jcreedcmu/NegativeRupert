import Noperthedron.Nopert76.NativeExecutable
import Noperthedron.Nopert76.PackedLocalViewTree

/-!
# Executable audit of Nopert #214 local-view chart 2

This reads the compact runtime artifact and checks the same sparse row
predicates used by the generated `native_decide` proof, but as one ordinary
release-mode executable. The rows are evaluated by native worker tasks; the
kernel-proved specification of the Boolean checker then constructs the
original semantic `Table.Valid` proof.
-/

open Noperthedron.Nopert76
open Noperthedron.Nopert76.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert76.NativeExecutable

/-- Keep this aligned with the empirically faster full constructor setting. -/
private def taskCount : Nat := 64

def main (args : List String) : IO Unit := do
  let path ← match args with
    | path :: _ => pure path
    | _ => throw (IO.userError "expects the local-viewN.pack path and table index")
  let packed ← IO.FS.readFile path
  let table := PackedLocalViewTree.decodePackedTable ((args.getD 1 "0").toNat!) packed
  let firstId := (table.get 0).id
  unless firstId = 0 do
    throw (IO.userError "packed table has an invalid first row id")
  let checked ← checkLocal "2" taskCount table
  let _semanticProof : table.Valid := checked.down
