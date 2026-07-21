module

public import Noperthedron.Nopert214.IsNotRupert
public import Noperthedron.Nopert214.SparseLocalViewTree

@[expose] public section

/-!
# Native executable proof construction for Nopert #214

This module is the executable counterpart of the generated `native_decide`
proofs. A release-mode program can check data-only local and global tables in
parallel, then retain the kernel-proved semantic validity witnesses in
`PLift`. The final `CheckedChartTables.notRupert` value has exactly the public
non-Rupert proposition as its type.

Keeping the proof witnesses in `PLift` lets ordinary `IO` code sequence checks
and report useful errors. Proof fields are erased by native code generation;
their correctness comes from the specifications of the Boolean checkers.
-/

namespace Noperthedron.Nopert214.NativeExecutable

open AtlasProjectiveLocalViewTree
open SparseLocalViewTree

def log (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush

/-- Check one sparse shared-local table with native worker tasks and return its
semantic validity proof. -/
def checkLocal (label : String) (taskCount : Nat)
    (table : AtlasProjectiveLocalViewTree.Table) : IO (PLift table.Valid) := do
  let start ← IO.monoNanosNow
  log s!"checking local {label}: {table.size} rows in {taskCount} native tasks"
  if h : sparseTableValidParB table taskCount = true then
    let finish ← IO.monoNanosNow
    log s!"valid local {label}: {(finish - start) / 1000000} ms"
    pure ⟨Table.Valid.of_sparseParB h⟩
  else
    throw (IO.userError s!"local table {label} is not valid")

/-- Four checked local tables, before they are attached to the global trees. -/
structure CheckedLocalTables where
  tables : Fin 4 → AtlasProjectiveLocalViewTree.Table
  valid : ∀ index, (tables index).Valid

def CheckedLocalTables.shared (checked : CheckedLocalTables) :
    AtlasProjectiveSolutionTree.SharedLocalTables :=
  fun index => some (checked.tables index)

theorem CheckedLocalTables.sharedValid (checked : CheckedLocalTables) :
    AtlasProjectiveSolutionTree.SharedLocalValid checked.shared := by
  intro index
  simp only [CheckedLocalTables.shared,
    AtlasProjectiveSolutionTree.OptionalLocalValid]
  exact checked.valid index

/-- Check one data-only global chart table after attaching the already checked
shared-local tables. -/
def checkGlobal (label : String) (taskCount : Nat)
    (table : AtlasProjectiveSolutionTree.Table)
    (hshared : AtlasProjectiveSolutionTree.SharedLocalValid table.sharedLocal) :
    IO (PLift table.Valid) := do
  let start ← IO.monoNanosNow
  log s!"checking chart {label}: {table.size} rows in {taskCount} native tasks"
  if h : AtlasProjectiveSolutionTree.tableCoreValidParB table taskCount = true then
    let finish ← IO.monoNanosNow
    log s!"valid chart {label}: {(finish - start) / 1000000} ms"
    pure ⟨AtlasProjectiveSolutionTree.Table.Valid.of_parB hshared h⟩
  else
    throw (IO.userError s!"global chart table {label} is not valid")

/-- The complete output of the executable checker. -/
structure CheckedChartTables where
  tables : CayleyAtlas.ChartIndex → AtlasProjectiveSolutionTree.Table
  charts : ∀ chart, (tables chart).chart = chart
  valid : ∀ chart, (tables chart).Valid

/-- The proof object constructed by a successful executable run. -/
theorem CheckedChartTables.notRupert (checked : CheckedChartTables) :
    ¬ IsRupert exactVerts :=
  not_rupert_of_valid_tables checked.tables checked.charts checked.valid

end Noperthedron.Nopert214.NativeExecutable

end
