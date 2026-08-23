module

public import Noperthedron.SolutionTable.Assemble
public import Noperthedron.SolutionTable.Load
-- The `load_csv_*`/`assemble_*` commands run at elaboration time.
public meta import Noperthedron.SolutionTable.Load

@[expose] public section


/-!
# Kernel-pipeline smoke test

A small-scale, end-to-end exercise of the kernel-only verification pipeline
on real solution-table rows, so that `lake build KernelCaseAnalysis` actually
runs `decide +kernel` checks today (requires `solution_tree_v7.csv` unzipped
at the repo root; the second-order local leaf costs a few kernel-seconds):

* `load_csv_rows` loads rows as literal `Row` definitions (elaboration-time
  parsing, no kernel string processing);
* leaf checks (`Row.leafOk`): three global leaves, one first-order local
  leaf, and one second-order local leaf (accepted via `Row.ValidLocal₂`);
* split checks through the exact production pipeline
  (`load_csv_chunks_curried` / `assemble_row_dispatch_curried` /
  `rowGetterC`) — `Row.ValidIxAt`, the statement shape the full run proves
  range-by-range via `RangeOk`;
* `#guard_msgs` pins every theorem to the three standard axioms — the build
  fails if `sorryAx` or `ofReduceBool` ever sneaks in.
-/

namespace Noperthedron.KernelCaseAnalysis.Smoke

open Noperthedron.Solution

/-! ### Leaf validation
Rows 8018–8022 contain three global leaves (8018, 8020, 8022) and two splits
(vacuous for `Row.leafOk`); row 71419 is the first local leaf in the table —
a second-order one (`Row.ValidLocal` fails, `Row.ValidLocal₂` accepts); row
1073456 is a first-order local leaf. -/

load_csv_rows "solution_tree_v7.csv" from 8018 to 8023

theorem csvRows_8018_8023_leafOk : csvRows_8018_8023.all Row.leafOk = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
load_csv_rows "solution_tree_v7.csv" from 71419 to 71420

set_option maxHeartbeats 8000000 in
theorem csvRows_71419_71420_leafOk :
    csvRows_71419_71420.all Row.leafOk = true := by
  decide +kernel

load_csv_rows "solution_tree_v7.csv" from 1073456 to 1073457

theorem csvRows_1073456_1073457_leafOk :
    csvRows_1073456_1073457.all Row.leafOk = true := by
  decide +kernel

/-! ### Split validation through the getter
The first 16 rows of the tree are all splits whose children (up to row 168)
lie inside the first 512 rows, so a getter over the loaded prefix suffices.
`Row.ValidIxAt` is the statement the full run proves for every index, and
the curried loader/dispatch/getter chain is exactly the one the generated
`Gen/` files use. -/

load_csv_chunks_curried "solution_tree_v7.csv" from 0 to 512 chunkSize 512

assemble_row_dispatch_curried prefixDispatch rows 512 chunkSize 512

noncomputable def getPrefix : ℕ → Row := rowGetterC prefixDispatch

theorem prefix_row0_interval : (getPrefix 0).interval = rowZero.interval := by
  decide +kernel

theorem prefix_first_splits_validIx :
    ∀ j : Fin 16, Row.ValidIxAt getPrefix 512 j.val := by
  decide +kernel

/-! ### Axiom guards: the standard three only — no `ofReduceBool`, no `sorryAx`. -/

/-- info: 'Noperthedron.KernelCaseAnalysis.Smoke.csvRows_8018_8023_leafOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms csvRows_8018_8023_leafOk

/-- info: 'Noperthedron.KernelCaseAnalysis.Smoke.csvRows_71419_71420_leafOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms csvRows_71419_71420_leafOk

/-- info: 'Noperthedron.KernelCaseAnalysis.Smoke.csvRows_1073456_1073457_leafOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms csvRows_1073456_1073457_leafOk

/-- info: 'Noperthedron.KernelCaseAnalysis.Smoke.prefix_row0_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefix_row0_interval

/-- info: 'Noperthedron.KernelCaseAnalysis.Smoke.prefix_first_splits_validIx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms prefix_first_splits_validIx

end Noperthedron.KernelCaseAnalysis.Smoke

end
