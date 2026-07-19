module

public import Noperthedron.BalancedSupport.AxisFree
public import Noperthedron.BalancedSupport.LocalRigidity
public import Noperthedron.SnubCube.Symmetry

@[expose] public section


/-!
# Local rigidity around every snub-cube symmetry

The relative rotation at an equality pose is one of the 24 rotations in
`Symmetry.lean`.  Removing that rotation turns the motion into a small
axis-angle rotation, while the checked symmetry action supplies the required
inner/outer vertex reindexing.
-/

namespace Noperthedron.SnubCube

open scoped Matrix RealInnerProductSpace
open Noperthedron.BalancedSupport

/-- Relative inner/outer rotation after removing symmetry `g`. -/
def relativeRotationAtSymmetry (p : MatrixPose) (g : VertexIndex) : SO3 :=
  relativeRotation p * (symmetry g)⁻¹

/-- Orthonormal frame used by the outer shadow. -/
noncomputable def outerFrame (p : MatrixPose) : ℝ³ ≃ₗᵢ[ℝ] ℝ³ :=
  Bounding.OrthogonalGroup.toLinearIsometryEquiv
    ⟨p.outerRot.val, p.outerRot.property.1⟩

/-- Lift a planar support direction back through the outer rotation. -/
noncomputable def outerLift (p : MatrixPose) (u : ℝ²) : ℝ³ :=
  (outerFrame p).symm (inject_xy u)

private theorem inner_proj_xy (u : ℝ²) (v : ℝ³) :
    ⟪u, proj_xyL v⟫ = ⟪inject_xy u, v⟫ := by
  simp [PiLp.inner_apply, proj_xyL, proj_xy_mat, inject_xy,
    Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two, Fin.sum_univ_three]

theorem inner_outerProjection_eq_outerLift (p : MatrixPose) (u : ℝ²) (v : ℝ³) :
    ⟪u, outerProjectionLinear p v⟫ = ⟪outerLift p u, v⟫ := by
  rw [outerProjectionLinear, ContinuousLinearMap.comp_apply, inner_proj_xy]
  let R := outerFrame p
  have hR : R v = p.outerRot.val.toEuclideanLin.toContinuousLinearMap v := rfl
  rw [← hR]
  simpa [outerLift, R] using R.inner_map_map (R.symm (inject_xy u)) v

/-- Coordinate-free first-variation vector for one balanced certificate. -/
noncomputable def firstVariationVector
    {κ : Type} [Fintype κ] (p : MatrixPose)
    (weight : κ → ℝ) (direction : κ → ℝ²) (vertex : κ → ℝ³) : ℝ³ :=
  ∑ i, weight i • cross3 (vertex i) (outerLift p (direction i))

theorem axisAngle_weighted_first_identity
    {κ : Type} [Fintype κ] {Q : ℝ³ →L[ℝ] ℝ³} (a : AxisAngle Q)
    (p : MatrixPose) (weight : κ → ℝ) (direction : κ → ℝ²)
    (vertex : κ → ℝ³) :
    Real.sin a.angle *
        (∑ i, weight i *
          ⟪direction i, outerProjectionLinear p (a.first (vertex i))⟫) =
      |Real.sin a.angle| *
        ⟪a.signedAxis, firstVariationVector p weight direction vertex⟫ := by
  rw [Finset.mul_sum, firstVariationVector, inner_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_outerProjection_eq_outerLift, real_inner_smul_right]
  calc
    Real.sin a.angle *
        (weight i * ⟪outerLift p (direction i), a.first (vertex i)⟫) =
      weight i *
        (Real.sin a.angle *
          ⟪outerLift p (direction i), a.first (vertex i)⟫) := by ring
    _ = weight i *
        (|Real.sin a.angle| *
          ⟪a.signedAxis, cross3 (vertex i) (outerLift p (direction i))⟫) := by
      rw [a.sin_mul_first_inner]
    _ = |Real.sin a.angle| *
        (weight i *
          ⟪a.signedAxis, cross3 (vertex i) (outerLift p (direction i))⟫) := by ring

/-- The vertex indexed by `i` on the inner copy tracks the vertex indexed by
`symmetryAction g i` on the outer copy after symmetry `g` is removed. -/
theorem outer_relative_at_symmetry_apply
    (p : MatrixPose) (g i : VertexIndex) :
    outerProjectionLinear p
        ((relativeRotationAtSymmetry p g).val.toEuclideanLin.toContinuousLinearMap
          (normalizedExactVertex (symmetryAction g i))) =
      proj_xyL (p.innerRot.val.toEuclideanLin (normalizedExactVertex i)) := by
  rw [← symmetry_apply_normalizedExactVertex g i]
  have hgroup :
      p.outerRot * relativeRotationAtSymmetry p g * symmetry g = p.innerRot := by
    simp [relativeRotationAtSymmetry, relativeRotation, ← mul_assoc]
  have hmat := congrArg Subtype.val hgroup
  simp only [MulMemClass.coe_mul] at hmat
  simp only [outerProjectionLinear, ContinuousLinearMap.comp_apply]
  apply congrArg proj_xyL
  change WithLp.toLp 2
      (p.outerRot.val *ᵥ
        ((relativeRotationAtSymmetry p g).val *ᵥ
          ((symmetry g).val *ᵥ (normalizedExactVertex i).ofLp))) =
    WithLp.toLp 2
      (p.innerRot.val *ᵥ (normalizedExactVertex i).ofLp)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hmat]

/-- Exact finite-rotation local obstruction around any of the 24 snub-cube
symmetry strata.  A row supplies supporting outer vertices after the checked
symmetry reindexing; balance cancels every planar translation. -/
theorem not_rupertPose_of_symmetry_axisAngle_certificate
    {κ : Type} [Fintype κ] [Nonempty κ]
    (p : MatrixPose) (g : VertexIndex)
    (a : AxisAngle
      ((relativeRotationAtSymmetry p g).val.toEuclideanLin.toContinuousLinearMap))
    (index : κ → VertexIndex) (weight : κ → ℝ) (direction : κ → ℝ²)
    (hdirection : ∀ i, direction i ≠ 0)
    (hweight : ∀ i, 0 ≤ weight i) (hweight_pos : ∃ i, 0 < weight i)
    (hbalance : ∑ i, weight i • direction i = 0)
    (hsupport : ∀ i j,
      ⟪direction i, outerProjectionLinear p (normalizedExactVertex j)⟫ ≤
        ⟪direction i, outerProjectionLinear p
          (normalizedExactVertex (symmetryAction g (index i)))⟫)
    (hdominates :
      (1 - Real.cos a.angle) *
          (∑ i, weight i *
            (‖direction i‖ *
              ‖normalizedExactVertex (symmetryAction g (index i))‖)) ≤
        Real.sin a.angle *
          (∑ i, weight i *
            ⟪direction i, outerProjectionLinear p
              (a.first
                (normalizedExactVertex (symmetryAction g (index i))))⟫)) :
    ¬ RupertPose p normalizedExactPolyhedron.hull := by
  apply not_rupertPose_of_reindexed_axisAngle_certificate
    normalizedExactPolyhedron p a index
    (fun i => symmetryAction g (index i)) weight direction
    hdirection hweight hweight_pos hbalance
  · intro i
    exact (outer_relative_at_symmetry_apply p g (index i)).symm
  · simpa [normalizedExactPolyhedron] using hsupport
  · simpa [normalizedExactPolyhedron] using hdominates

/-- A finite family of symmetry-local certificates eliminates the unknown
rotation axis.  The normalized first-variation vectors must contain a ball
about the origin; the signed identity `hfirst` absorbs the possible negative
axis-angle convention returned by `exists_axisAngle`. -/
theorem not_rupertPose_of_axisFree_symmetry_certificates
    {J κ : Type} [Fintype J] [Nonempty J] [Fintype κ] [Nonempty κ]
    (p : MatrixPose) (g : VertexIndex)
    (a : AxisAngle
      ((relativeRotationAtSymmetry p g).val.toEuclideanLin.toContinuousLinearMap))
    (index : J → κ → VertexIndex)
    (weight : J → κ → ℝ) (direction : J → κ → ℝ²)
    (A normalizedA : J → ℝ³) (B : J → ℝ) (c : ℝ) (ω : ℝ³)
    (hc : 0 ≤ c) (hω : ‖ω‖ = 1)
    (hB : ∀ j, 0 < B j)
    (hA : ∀ j, A j = B j • normalizedA j)
    (hball : Metric.closedBall (0 : ℝ³) c ⊆
      convexHull ℝ {normalizedA j | j})
    (hB_eq : ∀ j, B j = ∑ i, weight j i *
      (‖direction j i‖ *
        ‖normalizedExactVertex (symmetryAction g (index j i))‖))
    (hfirst : ∀ j,
      Real.sin a.angle *
          (∑ i, weight j i *
            ⟪direction j i, outerProjectionLinear p
              (a.first
                (normalizedExactVertex (symmetryAction g (index j i))))⟫) =
        |Real.sin a.angle| * ⟪ω, A j⟫)
    (hratio : 1 - Real.cos a.angle ≤ |Real.sin a.angle| * c)
    (hdirection : ∀ j i, direction j i ≠ 0)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hweight_pos : ∀ j, ∃ i, 0 < weight j i)
    (hbalance : ∀ j, ∑ i, weight j i • direction j i = 0)
    (hsupport : ∀ j i k,
      ⟪direction j i, outerProjectionLinear p (normalizedExactVertex k)⟫ ≤
        ⟪direction j i, outerProjectionLinear p
          (normalizedExactVertex (symmetryAction g (index j i)))⟫) :
    ¬ RupertPose p normalizedExactPolyhedron.hull := by
  obtain ⟨j, hj⟩ := exists_axis_certificate_dominating_remainder
    normalizedA A B c |Real.sin a.angle| (1 - Real.cos a.angle)
    hc (abs_nonneg _) hB hA hball hratio ω hω
  apply not_rupertPose_of_symmetry_axisAngle_certificate p g a
    (index j) (weight j) (direction j)
    (hdirection j) (hweight j) (hweight_pos j) (hbalance j) (hsupport j)
  rw [← hB_eq j, hfirst j]
  exact hj

/-- Geometric form of the axis-free theorem.  Here `A` is explicitly the
cross-product first-variation vector, so the signed unit axis and `hfirst`
are discharged automatically from the exact axis-angle construction. -/
theorem not_rupertPose_of_axisFree_geometric_certificates
    {J κ : Type} [Fintype J] [Nonempty J] [Fintype κ] [Nonempty κ]
    (p : MatrixPose) (g : VertexIndex)
    (a : AxisAngle
      ((relativeRotationAtSymmetry p g).val.toEuclideanLin.toContinuousLinearMap))
    (index : J → κ → VertexIndex)
    (weight : J → κ → ℝ) (direction : J → κ → ℝ²)
    (A normalizedA : J → ℝ³) (B : J → ℝ) (c : ℝ)
    (hc : 0 ≤ c)
    (hB : ∀ j, 0 < B j)
    (hA : ∀ j, A j = B j • normalizedA j)
    (hball : Metric.closedBall (0 : ℝ³) c ⊆
      convexHull ℝ {normalizedA j | j})
    (hA_eq : ∀ j, A j = firstVariationVector p (weight j) (direction j)
      (fun i => normalizedExactVertex (symmetryAction g (index j i))))
    (hB_eq : ∀ j, B j = ∑ i, weight j i *
      (‖direction j i‖ *
        ‖normalizedExactVertex (symmetryAction g (index j i))‖))
    (hratio : 1 - Real.cos a.angle ≤ |Real.sin a.angle| * c)
    (hdirection : ∀ j i, direction j i ≠ 0)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hweight_pos : ∀ j, ∃ i, 0 < weight j i)
    (hbalance : ∀ j, ∑ i, weight j i • direction j i = 0)
    (hsupport : ∀ j i k,
      ⟪direction j i, outerProjectionLinear p (normalizedExactVertex k)⟫ ≤
        ⟪direction j i, outerProjectionLinear p
          (normalizedExactVertex (symmetryAction g (index j i)))⟫) :
    ¬ RupertPose p normalizedExactPolyhedron.hull := by
  apply not_rupertPose_of_axisFree_symmetry_certificates p g a index weight direction
    A normalizedA B c a.signedAxis hc a.signedAxis_norm hB hA hball hB_eq
  · intro j
    rw [hA_eq j]
    exact axisAngle_weighted_first_identity a p (weight j) (direction j)
      (fun i => normalizedExactVertex (symmetryAction g (index j i)))
  · exact hratio
  · exact hdirection
  · exact hweight
  · exact hweight_pos
  · exact hbalance
  · exact hsupport

end Noperthedron.SnubCube

end
