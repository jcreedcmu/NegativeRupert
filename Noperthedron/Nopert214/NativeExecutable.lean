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
  let chunkSize := table.size / taskCount + 1
  let tasks := sparseTableTasks table taskCount
  let total := tasks.length
  let progressEvery := max 1 (total / 16)
  let mut pending := tasks.zipIdx.map fun (task, index) =>
    task.map (sync := true) fun valid => (index, valid)
  let mut completed := 0
  let mut checkedRows := 0
  while h : 0 < pending.length do
    let ((index, valid), remaining) ← IO.waitAny' pending h
    pending := remaining
    unless valid do
      let first := index * chunkSize
      let afterLast := min table.size (first + chunkSize)
      throw (IO.userError (s!"local table {label} is invalid in rows " ++
        s!"[{first}, {afterLast})"))
    let first := index * chunkSize
    let rowCount := if first < table.size then
      min chunkSize (table.size - first)
    else 0
    completed := completed + 1
    checkedRows := checkedRows + rowCount
    if completed % progressEvery = 0 || completed = total then
      let now ← IO.monoNanosNow
      log (s!"local {label}: {checkedRows}/{table.size} rows checked " ++
        s!"in {completed}/{total} completed tasks " ++
        s!"({(now - start) / 1000000} ms)")
  if h : sparseTableValidWithTasksB table taskCount tasks = true then
    let finish ← IO.monoNanosNow
    log s!"valid local {label}: {(finish - start) / 1000000} ms"
    have h' : sparseTableValidWithTasksB table taskCount
        (sparseTableTasks table taskCount) = true := by
      simpa only [tasks] using h
    pure ⟨Table.Valid.of_sparseWithTasksB h'⟩
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
  let chunkSize := table.size / taskCount + 1
  let tasks := AtlasProjectiveSolutionTree.tableCoreTasks table taskCount
  let total := tasks.length
  let progressEvery := max 1 (total / 16)
  let mut pending := tasks.zipIdx.map fun (task, index) =>
    task.map (sync := true) fun valid => (index, valid)
  let mut completed := 0
  let mut checkedRows := 0
  while h : 0 < pending.length do
    let ((index, valid), remaining) ← IO.waitAny' pending h
    pending := remaining
    unless valid do
      let first := index * chunkSize
      let afterLast := min table.size (first + chunkSize)
      throw (IO.userError (s!"chart {label} is invalid in rows " ++
        s!"[{first}, {afterLast})"))
    let first := index * chunkSize
    let rowCount := if first < table.size then
      min chunkSize (table.size - first)
    else 0
    completed := completed + 1
    checkedRows := checkedRows + rowCount
    if completed % progressEvery = 0 || completed = total then
      let now ← IO.monoNanosNow
      log (s!"chart {label}: {checkedRows}/{table.size} rows checked " ++
        s!"in {completed}/{total} completed tasks " ++
        s!"({(now - start) / 1000000} ms)")
  if h : AtlasProjectiveSolutionTree.tableCoreValidWithTasksB
      table taskCount tasks = true then
    let finish ← IO.monoNanosNow
    log s!"valid chart {label}: {(finish - start) / 1000000} ms"
    have h' : AtlasProjectiveSolutionTree.tableCoreValidWithTasksB
        table taskCount
        (AtlasProjectiveSolutionTree.tableCoreTasks table taskCount) = true := by
      simpa only [tasks] using h
    pure ⟨AtlasProjectiveSolutionTree.Table.Valid.of_withTasksB hshared h'⟩
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

/-- Check all certificate data and construct the final non-Rupert proof.

Generated global data is supplied as a function of the checked shared-local
tables. The two equations prevent an executable wrapper from accidentally
checking the right rows under the wrong chart or shared-local environment. -/
def constructProof (localTaskCount globalTaskCount : Nat)
    (localTables : Fin 4 → AtlasProjectiveLocalViewTree.Table)
    (globalTables : AtlasProjectiveSolutionTree.SharedLocalTables →
      CayleyAtlas.ChartIndex → AtlasProjectiveSolutionTree.Table)
    (hchart : ∀ shared chart, (globalTables shared chart).chart = chart)
    (hshared : ∀ shared chart,
      (globalTables shared chart).sharedLocal = shared) :
    IO (PLift (¬ IsRupert exactVerts)) := do
  let local0 ← checkLocal "0" localTaskCount (localTables 0)
  let local1 ← checkLocal "1" localTaskCount (localTables 1)
  let local2 ← checkLocal "2" localTaskCount (localTables 2)
  let local3 ← checkLocal "3" localTaskCount (localTables 3)
  let checkedLocal : CheckedLocalTables := {
    tables := localTables
    valid := by
      intro index
      fin_cases index
      · exact local0.down
      · exact local1.down
      · exact local2.down
      · exact local3.down }
  let shared := checkedLocal.shared
  have sharedValid : AtlasProjectiveSolutionTree.SharedLocalValid shared :=
    checkedLocal.sharedValid
  let table0 := globalTables shared 0
  have shared0 : AtlasProjectiveSolutionTree.SharedLocalValid
      table0.sharedLocal := by
    rw [hshared shared 0]
    exact sharedValid
  let valid0 ← checkGlobal "0" globalTaskCount table0 shared0
  let table1 := globalTables shared 1
  have shared1 : AtlasProjectiveSolutionTree.SharedLocalValid
      table1.sharedLocal := by
    rw [hshared shared 1]
    exact sharedValid
  let valid1 ← checkGlobal "1" globalTaskCount table1 shared1
  let table2 := globalTables shared 2
  have shared2 : AtlasProjectiveSolutionTree.SharedLocalValid
      table2.sharedLocal := by
    rw [hshared shared 2]
    exact sharedValid
  let valid2 ← checkGlobal "2" globalTaskCount table2 shared2
  let table3 := globalTables shared 3
  have shared3 : AtlasProjectiveSolutionTree.SharedLocalValid
      table3.sharedLocal := by
    rw [hshared shared 3]
    exact sharedValid
  let valid3 ← checkGlobal "3" globalTaskCount table3 shared3
  let checkedCharts : CheckedChartTables := {
    tables := ![table0, table1, table2, table3]
    charts := by
      intro chart
      fin_cases chart
      · exact hchart shared 0
      · exact hchart shared 1
      · exact hchart shared 2
      · exact hchart shared 3
    valid := by
      intro chart
      fin_cases chart
      · exact valid0.down
      · exact valid1.down
      · exact valid2.down
      · exact valid3.down }
  log "constructed proof: exact Nopert #214 is not Rupert"
  pure ⟨checkedCharts.notRupert⟩

end Noperthedron.Nopert214.NativeExecutable

end
