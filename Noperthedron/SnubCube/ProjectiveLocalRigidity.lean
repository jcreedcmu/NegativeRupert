module

public import Noperthedron.SnubCube.ProjectiveView

@[expose] public section


/-!
# Projective determinant weights for local rigidity

An oriented spatial edge gives a moving planar support direction by projecting
it and applying a quarter turn.  For three such directions, determinant
weights balance identically.  After dividing the directions by the positive
view sum, those weights and lifted directions are polynomial in the normalized
projective viewing vector.  These identities remove trigonometric outer-angle
boxes from the axis-free local theorem.
-/

namespace Noperthedron.SnubCube.ProjectiveLocalRigidity

open scoped RealInnerProductSpace
open Noperthedron.BalancedSupport
open CayleyEdgeCertificate ProjectiveView

abbrev EdgeTriple := Fin 3 → ℝ³
abbrev VertexTriple := Fin 3 → ℝ³

/-- Determinant of two projected spatial vectors is their scalar triple
product with the outer viewing vector. -/
theorem det2_rotM_eq_view (p : CayleyPose ℝ) (a b : ℝ³) :
    det2 (rotM p.θ p.φ a) (rotM p.θ p.φ b) =
      ∑ c, viewVector p c * cross3 a b c := by
  simp [det2, rotM, rotM_mat, viewVector, cross3, cross_apply,
    Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]
  have htrig := Real.sin_sq_add_cos_sq p.θ
  linear_combination
    (Real.cos p.φ * (a 0 * b 1 - a 1 * b 0)) * htrig

theorem det2_smul_same (c : ℝ) (a b : ℝ²) :
    det2 (c • a) (c • b) = c ^ 2 * det2 a b := by
  simp [det2]
  ring

/-- The scaled moving planar direction associated to one oriented edge. -/
noncomputable def direction (p : CayleyPose ℝ) (edge : ℝ³) : ℝ² :=
  (viewSum p)⁻¹ • quarterTurn (rotM p.θ p.φ edge)

/-- Polynomial determinant weights for three moving edge directions. -/
noncomputable def weight (p : CayleyPose ℝ) (edge : EdgeTriple) :
    Fin 3 → ℝ := ![
  linearValue (normalizedView p) (cross3 (edge 1) (edge 2)),
  linearValue (normalizedView p) (cross3 (edge 2) (edge 0)),
  linearValue (normalizedView p) (cross3 (edge 0) (edge 1))]

theorem det2_direction (p : CayleyPose ℝ) (a b : ℝ³)
    (hsum : viewSum p ≠ 0) :
    det2 (direction p a) (direction p b) =
      (viewSum p)⁻¹ *
        linearValue (normalizedView p) (cross3 a b) := by
  rw [direction, direction, det2_smul_same, det2_quarterTurn,
    det2_rotM_eq_view]
  simp [normalizedView, linearValue, Fin.sum_univ_three]
  field_simp [hsum]

theorem weight_eq_viewSum_mul_determinantWeights
    (p : CayleyPose ℝ) (edge : EdgeTriple) (hsum : viewSum p ≠ 0)
    (i : Fin 3) :
    weight p edge i = viewSum p *
      determinantWeights (fun j => direction p (edge j)) i := by
  fin_cases i <;>
    simp [weight, determinantWeights] <;>
    rw [det2_direction p _ _ hsum] <;>
    field_simp [hsum]

/-- The projective determinant weights balance the three moving directions
exactly at every positive-sum view. -/
theorem weight_balance (p : CayleyPose ℝ) (edge : EdgeTriple)
    (hsum : viewSum p ≠ 0) :
    ∑ i, weight p edge i • direction p (edge i) = 0 := by
  have hdet := determinantWeights_balance
    (fun i => direction p (edge i))
  simp_rw [weight_eq_viewSum_mul_determinantWeights p edge hsum, mul_smul]
  rw [← Finset.smul_sum, hdet, smul_zero]

/-- Pulling the scaled moving planar direction back to space gives the cross
product of the normalized projective view with the oriented edge. -/
theorem outerLift_direction (p : CayleyPose ℝ) (offset : ℝ²)
    (edge : ℝ³) (hsum : viewSum p ≠ 0) :
    outerLift (p.matrixPoseWithOffset offset) (direction p edge) =
      cross3 (WithLp.toLp 2 (normalizedView p)) edge := by
  apply ext_inner_right ℝ
  intro v
  rw [← inner_outerProjection_eq_outerLift]
  rw [direction, real_inner_smul_left]
  have hproj : outerProjectionLinear (p.matrixPoseWithOffset offset) v =
      rotM p.θ p.φ v := by
    simpa [outerProjectionLinear, ContinuousLinearMap.comp_apply] using
      p.matrixPoseWithOffset_outer_rotation_project offset v
  rw [hproj]
  rw [inner_quarterTurn_rotM_eq]
  simp [normalizedView, PiLp.inner_apply, Fin.sum_univ_three,
    cross3, cross_apply]
  field_simp [hsum]
  ring

/-- Quadratic projective first-variation vector of one moving three-contact
certificate. -/
noncomputable def variationVector (p : CayleyPose ℝ) (edge : EdgeTriple)
    (vertex : VertexTriple) : ℝ³ :=
  ∑ i, weight p edge i •
    cross3 (vertex i)
      (cross3 (WithLp.toLp 2 (normalizedView p)) (edge i))

theorem firstVariationVector_eq (p : CayleyPose ℝ) (offset : ℝ²)
    (edge : EdgeTriple) (vertex : VertexTriple)
    (hsum : viewSum p ≠ 0) :
    firstVariationVector (p.matrixPoseWithOffset offset)
        (weight p edge) (fun i => direction p (edge i)) vertex =
      variationVector p edge vertex := by
  unfold firstVariationVector variationVector
  apply Finset.sum_congr rfl
  intro i _
  rw [outerLift_direction p offset (edge i) hsum]

end Noperthedron.SnubCube.ProjectiveLocalRigidity

end
