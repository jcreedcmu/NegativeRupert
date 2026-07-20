module

public import Noperthedron.SnubCube.ProjectiveTransitionBlowup
public meta import Noperthedron.SnubCube.ProjectiveTransitionBlowup

@[expose] public section


namespace Noperthedron.SnubCube.ProjectiveTransitionBlowupSmoke

open ProjectiveTransitionBlowup

def AllFactorsValid : Prop :=
  family2.FactorValid ∧ family89.FactorValid ∧ family192.FactorValid ∧
    familyTransverse.FactorValid

instance : Decidable AllFactorsValid := by
  unfold AllFactorsValid
  infer_instance

theorem all_factors_valid_kernel : AllFactorsValid := by
  decide +kernel

theorem all_factors_valid_native : AllFactorsValid := by
  native_decide

def quotientTermCounts : Fin 4 → ℕ := ![
  family2.quotient.length,
  family89.quotient.length,
  family192.quotient.length,
  familyTransverse.quotient.length]

theorem quotient_term_counts_kernel :
    quotientTermCounts = ![59, 59, 53, 53] := by
  decide +kernel

theorem quotient_term_counts_native :
    quotientTermCounts = ![59, 59, 53, 53] := by
  native_decide

end Noperthedron.SnubCube.ProjectiveTransitionBlowupSmoke

end
