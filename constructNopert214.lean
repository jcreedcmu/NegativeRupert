import Noperthedron.Nopert214.FundamentalChart3
import Noperthedron.Nopert214.NativeExecutable
import Noperthedron.Nopert214.PackedSolutionTree

/-!
Native executable that reads and checks exact certificate data, then constructs
a proof that the fivefold-symmetric Nopert #214 is not Rupert.

This is analogous to `constructValidTable`: the expensive Boolean checks run
as parallel native code, while kernel-proved bridge theorems turn success into
the semantic proof consumed by the public theorem.
-/

open Noperthedron.Nopert214
open Noperthedron.Nopert214.AtlasProjectiveSolutionTree
open Noperthedron.Nopert214.NativeExecutable

private def taskCount : Nat := 512

private def readArtifact (directory name : String) : IO String :=
  IO.FS.readFile s!"{directory}/{name}"

def main (args : List String) : IO Unit := do
  let directory ← match args with
    | [directory] => pure directory
    | _ => throw (IO.userError (
        "expects one directory containing local-view0.pack through " ++
        "local-view3.pack and chart0.pack through chart2.pack"))
  let local0Data ← readArtifact directory "local-view0.pack"
  let local1Data ← readArtifact directory "local-view1.pack"
  let local2Data ← readArtifact directory "local-view2.pack"
  let local3Data ← readArtifact directory "local-view3.pack"
  let chart0Data ← readArtifact directory "chart0.pack"
  let chart1Data ← readArtifact directory "chart1.pack"
  let chart2Data ← readArtifact directory "chart2.pack"
  let localTables : Fin 4 → AtlasProjectiveLocalViewTree.Table :=
    ![PackedLocalViewTree.decodePackedTable 0 local0Data,
      PackedLocalViewTree.decodePackedTable 1 local1Data,
      PackedLocalViewTree.decodePackedTable 2 local2Data,
      PackedLocalViewTree.decodePackedTable 3 local3Data]
  let globalTables : SharedLocalTables →
      CayleyAtlas.ChartIndex → AtlasProjectiveSolutionTree.Table :=
    fun shared =>
      ![PackedSolutionTree.decodeTable 0 shared chart0Data,
        PackedSolutionTree.decodeTable 1 shared chart1Data,
        PackedSolutionTree.decodeTable 2 shared chart2Data,
        { FundamentalChart3.table with sharedLocal := shared }]
  let checked ← constructProof taskCount
    localTables globalTables
    (by intro shared chart; fin_cases chart <;> rfl)
    (by intro shared chart; fin_cases chart <;> rfl)
  let _proof : ¬ IsRupert exactVerts := checked.down
