module

public import KernelCaseAnalysis.Gen.Combine02

@[expose] public section

/-! GENERATED (scripts/gen_kernel_chunks.py): every index of the full table
satisfies `Row.ValidIxAt`, and row 0 carries `rowZero.interval`. -/

namespace Noperthedron.Solution

theorem allRows_validIxAt : ∀ i : Fin 1119311, Row.ValidIxAt getRow 1119311 i :=
  validIxAt_of_rangeOk combined_1119311

theorem row0_interval : (getRow 0).interval = rowZero.interval := by
  decide +kernel

end Noperthedron.Solution

end
