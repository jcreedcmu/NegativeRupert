module

public import Noperthedron.Nopert214.AtlasProjectiveView
public import Noperthedron.Nopert214.SymmetryLocal

@[expose] public section

/-!
# Projective moving-direction local rigidity for Nopert #214

This is the signed-atlas analogue of the snub-cube projective local theorem.
The support directions, determinant weights, and first-variation vectors vary
polynomially with the normalized projective view.  The finite-rotation ratio
is supplied separately by the atlas-local Cayley mismatch certificate.
-/

namespace Noperthedron.Nopert214.AtlasProjectiveLocalRigidity

open scoped RealInnerProductSpace
open Noperthedron.BalancedSupport
open Noperthedron.SnubCube.ProjectiveView
open AtlasEdgeCertificate AtlasProjectiveView

abbrev EdgeTriple := Fin 3 → ℝ³
abbrev VertexTriple := Fin 3 → ℝ³

theorem det2_rotM_eq_view (p : AtlasPose ℝ) (a b : ℝ³) :
    det2 (rotM p.θ p.φ a) (rotM p.θ p.φ b) =
      ∑ c, viewVector p c * cross3 a b c := by
  simp [det2, rotM, rotM_mat, viewVector,
    cross3, cross_apply, Matrix.toLpLin_apply, dotProduct,
    Fin.sum_univ_three]
  have htrig := Real.sin_sq_add_cos_sq p.θ
  linear_combination
    (Real.cos p.φ * (a 0 * b 1 - a 1 * b 0)) * htrig

theorem det2_smul_same (c : ℝ) (a b : ℝ²) :
    det2 (c • a) (c • b) = c ^ 2 * det2 a b := by
  simp [det2]
  ring

noncomputable def direction (root : Fin 8) (p : AtlasPose ℝ)
    (edge : ℝ³) : ℝ² :=
  (viewScale root p)⁻¹ • quarterTurn
    (rotM p.θ p.φ edge)

noncomputable def weight (root : Fin 8) (p : AtlasPose ℝ)
    (edge : EdgeTriple) : Fin 3 → ℝ := ![
  linearValue (AtlasProjectiveView.normalizedView root p)
    (cross3 (edge 1) (edge 2)),
  linearValue (AtlasProjectiveView.normalizedView root p)
    (cross3 (edge 2) (edge 0)),
  linearValue (AtlasProjectiveView.normalizedView root p)
    (cross3 (edge 0) (edge 1))]

theorem det2_direction (root : Fin 8) (p : AtlasPose ℝ) (a b : ℝ³)
    (hscale : viewScale root p ≠ 0) :
    det2 (direction root p a) (direction root p b) =
      (viewScale root p)⁻¹ *
        linearValue (AtlasProjectiveView.normalizedView root p)
          (cross3 a b) := by
  rw [direction, direction, det2_smul_same,
    det2_quarterTurn, det2_rotM_eq_view]
  simp [AtlasProjectiveView.normalizedView, linearValue,
    Fin.sum_univ_three]
  field_simp [hscale]

theorem weight_eq_viewScale_mul_determinantWeights
    (root : Fin 8) (p : AtlasPose ℝ) (edge : EdgeTriple)
    (hscale : viewScale root p ≠ 0) (i : Fin 3) :
    weight root p edge i = viewScale root p *
      determinantWeights (fun j => direction root p (edge j)) i := by
  fin_cases i <;>
    simp [weight, determinantWeights] <;>
    rw [det2_direction root p _ _ hscale] <;>
    field_simp [hscale]

theorem weight_balance (root : Fin 8) (p : AtlasPose ℝ)
    (edge : EdgeTriple) (hscale : viewScale root p ≠ 0) :
    ∑ i, weight root p edge i • direction root p (edge i) = 0 := by
  have hdet := determinantWeights_balance
    (fun i => direction root p (edge i))
  simp_rw [weight_eq_viewScale_mul_determinantWeights
    root p edge hscale, mul_smul]
  rw [← Finset.smul_sum, hdet, smul_zero]

theorem inner_direction_outerProjection_eq_support
    (root : Fin 8) (p : AtlasPose ℝ) (chart : CayleyAtlas.ChartIndex)
    (offset : ℝ²) (edge delta : ℝ³)
    (hscale : viewScale root p ≠ 0) :
    inner ℝ (direction root p edge)
        (outerProjectionLinear (p.matrixPoseWithOffset chart offset) delta) =
      linearValue (AtlasProjectiveView.normalizedView root p)
        (cross3 edge delta) := by
  rw [direction, real_inner_smul_left]
  have hproj :
      outerProjectionLinear (p.matrixPoseWithOffset chart offset) delta =
        rotM p.θ p.φ delta := by
    simpa [outerProjectionLinear, ContinuousLinearMap.comp_apply] using
      p.matrixPoseWithOffset_outer_rotation_project chart offset delta
  rw [hproj, AtlasEdgeCertificate.inner_quarterTurn_rotM_eq]
  simp [AtlasProjectiveView.normalizedView, linearValue,
    Fin.sum_univ_three]
  field_simp [hscale]

theorem outerLift_direction (root : Fin 8) (p : AtlasPose ℝ)
    (chart : CayleyAtlas.ChartIndex) (offset : ℝ²) (edge : ℝ³)
    (hscale : viewScale root p ≠ 0) :
    Noperthedron.SnubCube.outerLift
        (p.matrixPoseWithOffset chart offset) (direction root p edge) =
      cross3 (WithLp.toLp 2
        (AtlasProjectiveView.normalizedView root p)) edge := by
  apply ext_inner_right ℝ
  intro v
  rw [← Noperthedron.SnubCube.inner_outerProjection_eq_outerLift]
  rw [direction, real_inner_smul_left]
  have hproj :
      outerProjectionLinear (p.matrixPoseWithOffset chart offset) v =
        rotM p.θ p.φ v := by
    simpa [outerProjectionLinear, ContinuousLinearMap.comp_apply] using
      p.matrixPoseWithOffset_outer_rotation_project chart offset v
  rw [hproj, AtlasEdgeCertificate.inner_quarterTurn_rotM_eq]
  simp [AtlasProjectiveView.normalizedView, PiLp.inner_apply,
    Fin.sum_univ_three,
    cross3, cross_apply]
  field_simp [hscale]
  ring

noncomputable def variationVector (root : Fin 8) (p : AtlasPose ℝ)
    (edge : EdgeTriple) (vertex : VertexTriple) : ℝ³ :=
  ∑ i, weight root p edge i •
    cross3 (vertex i)
      (cross3 (WithLp.toLp 2
        (AtlasProjectiveView.normalizedView root p)) (edge i))

theorem firstVariationVector_eq (root : Fin 8) (p : AtlasPose ℝ)
    (chart : CayleyAtlas.ChartIndex) (offset : ℝ²) (edge : EdgeTriple)
    (vertex : VertexTriple) (hscale : viewScale root p ≠ 0) :
    Noperthedron.SnubCube.firstVariationVector
        (p.matrixPoseWithOffset chart offset) (weight root p edge)
        (fun i => direction root p (edge i)) vertex =
      variationVector root p edge vertex := by
  unfold Noperthedron.SnubCube.firstVariationVector variationVector
  apply Finset.sum_congr rfl
  intro i _
  rw [outerLift_direction root p chart offset (edge i) hscale]

noncomputable def normalizedVariation (root : Fin 8) (p : AtlasPose ℝ)
    (edge : Fin 4 → EdgeTriple) (index : Fin 4 → Fin 3 → VertexIndex)
    (g : OrbitIndex) (B : Fin 4 → ℝ) (j : Fin 4) : ℝ³ :=
  (B j)⁻¹ • variationVector root p (edge j)
    (fun i => exactVertex (symmetryAction g (index j i)))

theorem not_rupertPose_of_projective_local_certificates
    (root : Fin 8) (p : AtlasPose ℝ) (chart : CayleyAtlas.ChartIndex)
    (offset : ℝ²) (g : OrbitIndex)
    (edge : Fin 4 → EdgeTriple)
    (index : Fin 4 → Fin 3 → VertexIndex)
    (B : Fin 4 → ℝ) (c : ℝ)
    (hscale : viewScale root p ≠ 0)
    (hB : ∀ j, 0 < B j)
    (hcover : ∀ axis : ℝ³, ‖axis‖ = 1 →
      ∃ j, c ≤ ⟪axis, normalizedVariation root p edge index g B j⟫)
    (hbudget : ∀ j, ∑ i, weight root p (edge j) i *
      (‖direction root p (edge j i)‖ *
        ‖exactVertex (symmetryAction g (index j i))‖) ≤ B j)
    (hratio : ∀ a : AxisAngle
      (Noperthedron.SnubCube.so3CLM
        (relativeRotationAtSymmetry
          (p.matrixPoseWithOffset chart offset) g)),
      1 - Real.cos a.angle ≤ |Real.sin a.angle| * c)
    (hdirection : ∀ j i, direction root p (edge j i) ≠ 0)
    (hweight : ∀ j i, 0 ≤ weight root p (edge j) i)
    (hweight_pos : ∀ j, ∃ i, 0 < weight root p (edge j) i)
    (hsupport : ∀ j i k,
      ⟪direction root p (edge j i),
          outerProjectionLinear (p.matrixPoseWithOffset chart offset)
            (exactVertex k)⟫ ≤
        ⟪direction root p (edge j i),
          outerProjectionLinear (p.matrixPoseWithOffset chart offset)
            (exactVertex (symmetryAction g (index j i)))⟫) :
    ¬ RupertPose (p.matrixPoseWithOffset chart offset)
      exactPolyhedron.hull := by
  let relative := relativeRotationAtSymmetry
    (p.matrixPoseWithOffset chart offset) g
  obtain ⟨a⟩ := exists_axisAngle relative.val relative.property
  apply
    Noperthedron.Nopert214.not_rupertPose_of_axisFree_symmetry_certificates_of_cover_perturbation
      (p := p.matrixPoseWithOffset chart offset) (g := g) (a := a)
      (index := index)
      (weight := fun j => weight root p (edge j))
      (direction := fun j i => direction root p (edge j i))
      (A := fun j => variationVector root p (edge j)
        (fun i => exactVertex (symmetryAction g (index j i))))
      (normalizedA := normalizedVariation root p edge index g B)
      (centerNormalizedA := normalizedVariation root p edge index g B)
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
    exact (firstVariationVector_eq root p chart offset (edge j)
      (fun i => exactVertex (symmetryAction g (index j i))) hscale).symm
  · exact hbudget
  · exact hratio a
  · exact hdirection
  · exact hweight
  · exact hweight_pos
  · intro j
    exact weight_balance root p (edge j) hscale
  · exact hsupport

end Noperthedron.Nopert214.AtlasProjectiveLocalRigidity

end
