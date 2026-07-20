module

public import Noperthedron.SnubCube.ProjectiveTransitionGeometry

@[expose] public section


/-!
# Exact reconstruction of the blown-up transition chart

The transition certificate uses five ratios `(d,e,a,b,t)`.  Here `d` is the
exact support seam equation, `e = n_z/d`, and the relative Cayley vector is
`(d²a,d²b,dt)`.  This file proves that extracting those ratios from a pose
and evaluating the generated chart polynomials reconstructs the pose
exactly.
-/

namespace Noperthedron.SnubCube.ProjectiveTransitionChart

open ProjectiveView ProjectiveTransitionBlowup
open ProjectiveTransitionCertificate
open ProjectiveTransitionGeometry
open ProjectiveTransitionBox
open SparseTribonacciPolynomial

noncomputable def seamNormal : ℝ³ := realOfExact seamCoefficient

noncomputable def seamValue (p : CayleyPose ℝ) : ℝ :=
  linearValue (normalizedView p) seamNormal

noncomputable def chartValues (p : CayleyPose ℝ) : Fin 5 → ℝ :=
  let d := seamValue p
  ![d, normalizedView p 2 / d, p.x / d ^ 2, p.y / d ^ 2, p.z / d]

theorem seamSlope_inverse_exact :
    (seamCoefficient 1 - seamCoefficient 0) * inverseSeamSlope = 1 := by
  decide +kernel

theorem seamU_exact :
    seamU = -(inverseSeamSlope * seamCoefficient 0) := by
  decide +kernel

theorem seamTangentialSlope_exact :
    seamTangentialSlope =
      inverseSeamSlope * (seamCoefficient 0 - seamCoefficient 2) := by
  rfl

theorem chartValues_chartCayley (p : CayleyPose ℝ)
    (hseam : seamValue p ≠ 0) :
    ChartCayley (chartValues p) p := by
  intro c
  fin_cases c <;>
    simp [chartValues, cayleyPolynomial] <;>
    field_simp [hseam]

theorem normalizedView_sum (p : CayleyPose ℝ) (hsum : viewSum p ≠ 0) :
    normalizedView p 0 + normalizedView p 1 + normalizedView p 2 = 1 := by
  simp [normalizedView, viewSum]
  rw [← add_div, ← add_div]
  exact div_self hsum

theorem chartValues_chartView (p : CayleyPose ℝ)
    (hsum : viewSum p ≠ 0) (hseam : seamValue p ≠ 0) :
    ChartView (chartValues p) p := by
  have hslope := congrArg TribonacciExpr.eval seamSlope_inverse_exact
  have hseamU := congrArg TribonacciExpr.eval seamU_exact
  have htangential := congrArg TribonacciExpr.eval seamTangentialSlope_exact
  simp only [TribonacciExpr.eval_mul, TribonacciExpr.eval_sub,
    TribonacciExpr.eval_one, TribonacciExpr.eval_neg] at hslope hseamU htangential
  have hn := normalizedView_sum p hsum
  have he : seamValue p * (normalizedView p 2 / seamValue p) =
      normalizedView p 2 := by
    field_simp [hseam]
  have hu :
      evalReal (chartValues p) (ProjectiveTransitionBlowup.viewPolynomial 1) =
        normalizedView p 1 := by
    simp [ProjectiveTransitionBlowup.viewPolynomial, chartValues]
    rw [he]
    unfold seamValue seamNormal realOfExact linearValue
    simp only
    rw [hseamU, htangential]
    have hn0 : normalizedView p 0 =
        1 - normalizedView p 1 - normalizedView p 2 := by
      linarith
    rw [hn0]
    linear_combination (normalizedView p 1) * hslope
  have hh :
      evalReal (chartValues p) (ProjectiveTransitionBlowup.viewPolynomial 2) =
        normalizedView p 2 := by
    simpa [ProjectiveTransitionBlowup.viewPolynomial, chartValues] using he
  have hvsum :
      evalReal (chartValues p) (ProjectiveTransitionBlowup.viewPolynomial 0) +
        evalReal (chartValues p) (ProjectiveTransitionBlowup.viewPolynomial 1) +
        evalReal (chartValues p) (ProjectiveTransitionBlowup.viewPolynomial 2) =
          1 := by
    simp [ProjectiveTransitionBlowup.viewPolynomial]
    ring
  intro c
  fin_cases c
  · change evalReal (chartValues p)
      (ProjectiveTransitionBlowup.viewPolynomial 0) = normalizedView p 0
    linarith
  · change evalReal (chartValues p)
      (ProjectiveTransitionBlowup.viewPolynomial 1) = normalizedView p 1
    exact hu
  · change evalReal (chartValues p)
      (ProjectiveTransitionBlowup.viewPolynomial 2) = normalizedView p 2
    exact hh

/-- End-to-end transition-leaf theorem in the coordinates extracted from an
actual Cayley pose. -/
theorem Box.valid_imp_not_translated_rupert_of_chart
    (box : Box) (hvalid : box.Valid) (p : CayleyPose ℝ) (offset : ℝ²)
    (hvalues : ∀ i, (box.variableBalls i).Holds (chartValues p i))
    (hsum : viewSum p ≠ 0) (hseam : seamValue p ≠ 0) :
    ¬ RupertPose (p.matrixPoseWithOffset offset)
      normalizedExactPolyhedron.hull := by
  exact ProjectiveTransitionGeometry.Box.valid_imp_not_translated_rupert
    box hvalid hvalues p offset
    (chartValues_chartView p hsum hseam)
    (chartValues_chartCayley p hseam) hsum

end Noperthedron.SnubCube.ProjectiveTransitionChart

end
