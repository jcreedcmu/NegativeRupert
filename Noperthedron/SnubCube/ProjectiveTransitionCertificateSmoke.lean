module

public import Noperthedron.SnubCube.ProjectiveTransitionCertificate
public meta import Noperthedron.SnubCube.ProjectiveTransitionCertificate

@[expose] public section


/-!
# Smoke test for the hard snub-cube transition quotient
-/

namespace Noperthedron.SnubCube.ProjectiveTransitionCertificateSmoke

open Noperthedron.Checker
open ProjectiveTransitionCertificate

def smokeBox : ZAxisBox where
  seam := RatBall.ofEndpoints (1 / 1000000000) (1 / 1000)
  ratio := RatBall.ofEndpoints 1 2

def coverBoxes : Fin 6 → ZAxisBox := ![
  { seam := smokeBox.seam
    ratio := RatBall.ofEndpoints (2 / 5) (159 / 80) },
  { seam := smokeBox.seam
    ratio := RatBall.ofEndpoints (159 / 80) (143 / 40) },
  { seam := smokeBox.seam
    ratio := RatBall.ofEndpoints (143 / 40) (413 / 80) },
  { seam := smokeBox.seam
    ratio := RatBall.ofEndpoints (413 / 80) (953 / 160) },
  { seam := smokeBox.seam
    ratio := RatBall.ofEndpoints (953 / 160) (2033 / 320) },
  { seam := smokeBox.seam
    ratio := RatBall.ofEndpoints (2033 / 320) (27 / 4) }]

def CoverValid : Prop := ∀ i, (coverBoxes i).Valid

instance : Decidable CoverValid := by
  unfold CoverValid
  infer_instance

theorem smoke_valid_kernel : smokeBox.Valid := by
  decide +kernel

theorem smoke_valid_native : smokeBox.Valid := by
  native_decide

theorem cover_valid_kernel : CoverValid := by
  decide +kernel

theorem cover_valid_native : CoverValid := by
  native_decide

/-- The six certified intervals have no gaps in the hard ratio band. -/
theorem ratio_mem_cover {t : ℝ} (hlo : (2 / 5 : ℝ) ≤ t)
    (hhi : t ≤ 27 / 4) :
    ∃ i, (coverBoxes i).ratio.Holds t := by
  have hlo' : ((2 / 5 : ℚ) : ℝ) ≤ t := by norm_num at hlo ⊢; exact hlo
  have hhi' : t ≤ ((27 / 4 : ℚ) : ℝ) := by norm_num at hhi ⊢; exact hhi
  by_cases h0 : t ≤ ((159 / 80 : ℚ) : ℝ)
  · exact ⟨0, RatBall.holds_of_mem_Icc ⟨hlo', h0⟩⟩
  by_cases h1 : t ≤ ((143 / 40 : ℚ) : ℝ)
  · refine ⟨1, RatBall.holds_of_mem_Icc ⟨le_of_not_ge h0, h1⟩⟩
  by_cases h2 : t ≤ ((413 / 80 : ℚ) : ℝ)
  · refine ⟨2, RatBall.holds_of_mem_Icc ⟨le_of_not_ge h1, h2⟩⟩
  by_cases h3 : t ≤ ((953 / 160 : ℚ) : ℝ)
  · refine ⟨3, RatBall.holds_of_mem_Icc ⟨le_of_not_ge h2, h3⟩⟩
  by_cases h4 : t ≤ ((2033 / 320 : ℚ) : ℝ)
  · refine ⟨4, RatBall.holds_of_mem_Icc ⟨le_of_not_ge h3, h4⟩⟩
  · refine ⟨5, RatBall.holds_of_mem_Icc ⟨le_of_not_ge h4, hhi'⟩⟩

end Noperthedron.SnubCube.ProjectiveTransitionCertificateSmoke

end
