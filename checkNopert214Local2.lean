import Noperthedron.Nopert214.GeneratedLocalView2SparseNativeData
import Noperthedron.Nopert214.NativeExecutable

/-!
# Executable audit of Nopert #214 local-view chart 2

This checks the same sparse row predicates used by the generated
`native_decide` proof, but as one ordinary release-mode executable.  The rows
are evaluated by native worker tasks; the kernel-proved specification of the
Boolean checker then constructs the original semantic `Table.Valid` proof.
The executable is an early, low-memory audit; the generated `native_decide`
theorem remains the persistent formal certificate.
-/

open Noperthedron.Nopert214
open Noperthedron.Nopert214.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert214.NativeExecutable

private def taskCount : Nat := 64

@[noinline] private def loadTable (_ : Unit) : Table :=
  GeneratedLocalView2SparseNativeData.table

def main : IO Unit := do
  -- Keep the decoded table as one runtime value.  Re-evaluating the generated
  -- definition for every range would repeatedly parse the packed string.
  let table := loadTable ()
  -- Accessing a row forces the packed decoder; retain the result so the
  -- compiler cannot discard this timing boundary.
  let firstId := (table.get 0).id
  unless firstId = 0 do
    throw (IO.userError "generated table has an invalid first row id")
  let checked ← checkLocal "2" taskCount table
  let _semanticProof : table.Valid := checked.down
