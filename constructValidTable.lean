import Noperthedron.SolutionTable.Assemble
import Noperthedron.SolutionTable.Parse
-- Kernel-speed instances (Local2Nat integer core) and the `…K` rendering of
-- the parallel check: this exe is compiled ahead of time, so unlike
-- `native_decide` (which runs under the Lean interpreter) it executes the
-- integer core at full native speed — ~5× faster second-order local checks.
import Noperthedron.SolutionTable.KernelInstances

/-!
  Program that constructs a `ValidTable` value -- exactly what fits into the "hole" in
  Noperthedron/ProofOfMainTheoremWithHole.lean.

  Accepts as input a path to a csv file contains the solution data.

  This runs the same parallel parse-and-check that `native_decide`
  evaluates in NativeCaseAnalysis/ComputationalStep.lean, but compiled to native
  code, so it is considerably faster.

  Running on the solution tree from solution_tree_v7.zip takes about half a
  minute on a 16-core machine.

  To get the solution tree, make sure you have git-lfs installed and you've fetched
  the full solution_tree_v7.zip file. then unzip it into solution_tree_v7.csv.
-/

open Noperthedron.Solution

def main (args : List String) : IO Unit := do
  let csv_filepath ←
    match args with
    | [arg] => pure arg
    | _ => throw (IO.userError "expects exactly one argument")

  let csv ← IO.FS.readFile csv_filepath
  let table ←
    match parseSolutionTablePar csv 64 with
    | .ok t => pure t
    | .error e => throw (IO.userError s!"parse error: {e}")
  IO.println s!"parsing done! {table.size} rows"

  if h_nonempty : 0 < table.size then
    if h_first : table[0].interval = rowZero.interval then
      if h_valid_b : rowsValidIxAtParBK (fun j => table[j]!) table.size 512 then
        let validTable : ValidTable := validTableOfParsedChecks table h_nonempty h_first
          (validIxAt_of_rowsValidIxAtParBK h_valid_b)
        IO.println s!"ValidTable constructed with {validTable.size} rows."
      else
        throw (IO.userError "table rows are not valid")
    else
      throw (IO.userError "table[0].interval does not match rowZero.interval")
  else
    throw (IO.userError "table is empty")
