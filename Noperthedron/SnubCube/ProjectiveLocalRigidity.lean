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

noncomputable def normalizedVariation (p : CayleyPose ℝ)
    (edge : Fin 4 → EdgeTriple) (index : Fin 4 → Fin 3 → VertexIndex)
    (B : Fin 4 → ℝ) (j : Fin 4) : ℝ³ :=
  (B j)⁻¹ • variationVector p (edge j)
    (fun i => normalizedExactVertex (index j i))

/-- Pointwise projective form of axis-free local rigidity.  Its hypotheses
are exactly the quantities that the rational triangle checker will bound:
linear determinant weights, quadratic first-variation vectors, a remainder
budget, an axis-cover tetrahedron, and exact support inequalities. -/
theorem not_rupertPose_of_projective_local_certificates
    (p : CayleyPose ℝ) (offset : ℝ²)
    (edge : Fin 4 → EdgeTriple)
    (index : Fin 4 → Fin 3 → VertexIndex)
    (B : Fin 4 → ℝ) (c : ℝ)
    (hsum : viewSum p ≠ 0)
    (hB : ∀ j, 0 < B j)
    (hcover : ∀ axis : ℝ³, ‖axis‖ = 1 →
      ∃ j, c ≤ ⟪axis, normalizedVariation p edge index B j⟫)
    (hbudget : ∀ j, ∑ i, weight p (edge j) i *
      (‖direction p (edge j i)‖ * ‖normalizedExactVertex (index j i)‖) ≤
        B j)
    (hradius : Real.sqrt (p.x ^ 2 + p.y ^ 2 + p.z ^ 2) ≤ c)
    (hdirection : ∀ j i, direction p (edge j i) ≠ 0)
    (hweight : ∀ j i, 0 ≤ weight p (edge j) i)
    (hweight_pos : ∀ j, ∃ i, 0 < weight p (edge j) i)
    (hsupport : ∀ j i k,
      ⟪direction p (edge j i),
          outerProjectionLinear (p.matrixPoseWithOffset offset)
            (normalizedExactVertex k)⟫ ≤
        ⟪direction p (edge j i),
          outerProjectionLinear (p.matrixPoseWithOffset offset)
            (normalizedExactVertex (index j i))⟫) :
    ¬ RupertPose (p.matrixPoseWithOffset offset)
      normalizedExactPolyhedron.hull := by
  let relative := relativeRotationAtSymmetry
    (p.matrixPoseWithOffset offset) (VertexIndex.ofFin24 0)
  obtain ⟨a⟩ := exists_axisAngle relative.val relative.property
  apply
    not_rupertPose_of_axisFree_geometric_certificates_of_cover_perturbation
      (p := p.matrixPoseWithOffset offset)
      (g := VertexIndex.ofFin24 0) (a := a)
      (index := index)
      (weight := fun j => weight p (edge j))
      (direction := fun j i => direction p (edge j i))
      (A := fun j => variationVector p (edge j)
        (fun i => normalizedExactVertex (index j i)))
      (normalizedA := normalizedVariation p edge index B)
      (centerNormalizedA := normalizedVariation p edge index B)
      (B := B) (c := c) (δ := 0)
  · exact hB
  · intro j
    simp only [normalizedVariation, smul_smul]
    rw [mul_inv_cancel₀ (ne_of_gt (hB j)), one_smul]
  · intro axis haxis
    simpa using hcover axis haxis
  · intro j
    simp
  · intro j
    simpa only [symmetryAction_zero] using
      (firstVariationVector_eq p offset (edge j)
        (fun i => normalizedExactVertex (index j i)) hsum).symm
  · simpa only [symmetryAction_zero] using hbudget
  · exact p.axisAngle_ratio_le offset a c hradius
  · exact hdirection
  · exact hweight
  · exact hweight_pos
  · intro j
    exact weight_balance p (edge j) hsum
  · simpa only [symmetryAction_zero] using hsupport

end Noperthedron.SnubCube.ProjectiveLocalRigidity

end
