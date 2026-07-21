import Noperthedron.Nopert214.ExecutableData
import Noperthedron.Nopert214.NativeExecutable

/-!
Native executable that checks the generated exact certificate data and
constructs a proof that the fivefold-symmetric Nopert #214 is not Rupert.

This is analogous to `constructValidTable`: the expensive Boolean checks run
as parallel native code, while kernel-proved bridge theorems turn success into
the semantic proof consumed by the public theorem.
-/

open Noperthedron.Nopert214
open Noperthedron.Nopert214.NativeExecutable

private def taskCount : Nat := 64

def main : IO Unit := do
  let checked ← constructProof taskCount
    ExecutableData.localTables ExecutableData.globalTables
    ExecutableData.globalTables_chart ExecutableData.globalTables_shared
  let _proof : ¬ IsRupert exactVerts := checked.down
