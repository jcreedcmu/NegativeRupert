module

public import Noperthedron.BalancedSupport.Basic
public import Noperthedron.BalancedSupport.FiniteRotation
public import Noperthedron.BalancedSupport.Rodrigues
public import Noperthedron.BalancedSupport.Rupert

@[expose] public section


/-!
# Finite-rotation balanced displacement

This specializes the ordered finite-rotation lemma to an actual `SO(3)`
axis-angle decomposition and an arbitrary norm-nonincreasing planar map.
-/

namespace Noperthedron.BalancedSupport

open scoped Matrix RealInnerProductSpace

/-- Inner rotation relative to the outer rotation. -/
def relativeRotation (p : MatrixPose) : SO3 := p.outerRot⁻¹ * p.innerRot

/-- Express the outer shadow map as the common projection used by the local
relative rotation. -/
noncomputable def outerProjectionLinear (p : MatrixPose) : ℝ³ →L[ℝ] ℝ² :=
  proj_xyL ∘L p.outerRot.val.toEuclideanLin.toContinuousLinearMap

theorem proj_xyL_norm_le (v : ℝ³) : ‖proj_xyL v‖ ≤ ‖v‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Fin.sum_univ_three,
    Real.norm_eq_abs, sq_abs]
  simp [proj_xyL, proj_xy_mat, Matrix.vecHead, Matrix.vecTail]
  nlinarith [sq_nonneg (v 2)]

theorem outerProjectionLinear_norm_le (p : MatrixPose) (v : ℝ³) :
    ‖outerProjectionLinear p v‖ ≤ ‖v‖ := by
  apply (proj_xyL_norm_le _).trans_eq
  let u : ℝ³ ≃ₗᵢ[ℝ] ℝ³ :=
    Bounding.OrthogonalGroup.toLinearIsometryEquiv
      ⟨p.outerRot.val, p.outerRot.property.1⟩
  have hu : u v = p.outerRot.val.toEuclideanLin.toContinuousLinearMap v := rfl
  exact (congrArg norm hu.symm).trans (u.norm_map v)

theorem outer_relative_apply (p : MatrixPose) (v : ℝ³) :
    outerProjectionLinear p
        ((relativeRotation p).val.toEuclideanLin.toContinuousLinearMap v) =
      proj_xyL (p.innerRot.val.toEuclideanLin v) := by
  have hgroup : p.outerRot * (p.outerRot⁻¹ * p.innerRot) = p.innerRot := by simp
  have hmat := congrArg Subtype.val hgroup
  simp only [MulMemClass.coe_mul] at hmat
  simp only [outerProjectionLinear, relativeRotation, ContinuousLinearMap.comp_apply]
  apply congrArg proj_xyL
  change WithLp.toLp 2
      (p.outerRot.val *ᵥ ((p.outerRot⁻¹ * p.innerRot).val *ᵥ v.ofLp)) =
    WithLp.toLp 2 (p.innerRot.val *ᵥ v.ofLp)
  rw [← hmat, Matrix.mulVec_mulVec]
  simp only [MulMemClass.coe_mul]

/-- A favorable weighted first variation dominates the exact Rodrigues
remainder, hence the balanced displacement is nonnegative. -/
theorem axisAngle_weighted_displacement_nonneg
    {κ : Type} [Fintype κ]
    {Q : ℝ³ →L[ℝ] ℝ³} (a : AxisAngle Q)
    (L : ℝ³ →L[ℝ] ℝ²) (hL : ∀ x, ‖L x‖ ≤ ‖x‖)
    (weight : κ → ℝ) (direction : κ → ℝ²) (vertex : κ → ℝ³)
    (hweight : ∀ i, 0 ≤ weight i)
    (hdominates :
      (1 - Real.cos a.angle) *
          (∑ i, weight i * (‖direction i‖ * ‖vertex i‖)) ≤
        Real.sin a.angle *
          (∑ i, weight i * ⟪direction i, L (a.first (vertex i))⟫)) :
    0 ≤ ∑ i, weight i * ⟪direction i, L (Q (vertex i) - vertex i)⟫ := by
  let displacement : κ → ℝ := fun i =>
    ⟪direction i, L (Q (vertex i) - vertex i)⟫
  let first : κ → ℝ := fun i =>
    ⟪direction i, L (a.first (vertex i))⟫
  let remainder : κ → ℝ := fun i =>
    ⟪direction i, L (a.remainder (vertex i))⟫
  let bound : κ → ℝ := fun i => ‖direction i‖ * ‖vertex i‖
  have hbend : 0 ≤ 1 - Real.cos a.angle := sub_nonneg.mpr (Real.cos_le_one _)
  have hdecomp (i : κ) : displacement i =
      Real.sin a.angle * first i + (1 - Real.cos a.angle) * remainder i := by
    dsimp [displacement, first, remainder]
    rw [a.apply_sub_exact, map_add, map_smul, map_smul,
      inner_add_right, inner_smul_right, inner_smul_right]
  have hremainder (i : κ) : -bound i ≤ remainder i := by
    dsimp [bound, remainder]
    have habs : |⟪direction i, L (a.remainder (vertex i))⟫| ≤
        ‖direction i‖ * ‖vertex i‖ := by
      calc
        |⟪direction i, L (a.remainder (vertex i))⟫|
            ≤ ‖direction i‖ * ‖L (a.remainder (vertex i))‖ :=
              abs_real_inner_le_norm _ _
        _ ≤ ‖direction i‖ * ‖a.remainder (vertex i)‖ :=
          mul_le_mul_of_nonneg_left (hL _) (norm_nonneg _)
        _ ≤ ‖direction i‖ * ‖vertex i‖ :=
          mul_le_mul_of_nonneg_left (a.remainder_norm_le _) (norm_nonneg _)
    linarith [neg_le_of_abs_le habs]
  exact weighted_displacement_nonneg_of_first_remainder
    weight displacement first remainder bound (Real.sin a.angle)
    (1 - Real.cos a.angle) hweight hbend hdecomp hremainder (by simpa using hdominates)

/-- Geometric local-rigidity obstruction at an equality pose.  The same
support vertex is followed by the relative rotation `Q`; exact balance removes
the arbitrary planar translation. -/
theorem finite_rotation_not_strictly_contained
    {ι κ : Type} [Fintype ι] [Fintype κ] [Nonempty κ]
    (poly : Polyhedron ι ℝ³)
    {Q : ℝ³ →L[ℝ] ℝ³} (a : AxisAngle Q)
    (L : ℝ³ →L[ℝ] ℝ²) (hL : ∀ x, ‖L x‖ ≤ ‖x‖)
    (index : κ → ι) (weight : κ → ℝ) (direction : κ → ℝ²)
    (hdirection : ∀ i, direction i ≠ 0)
    (hweight : ∀ i, 0 ≤ weight i) (hweight_pos : ∃ i, 0 < weight i)
    (hbalance : ∑ i, weight i • direction i = 0)
    (hsupport : ∀ i j,
      ⟪direction i, L (poly.v j)⟫ ≤ ⟪direction i, L (poly.v (index i))⟫)
    (hdominates :
      (1 - Real.cos a.angle) *
          (∑ i, weight i * (‖direction i‖ * ‖poly.v (index i)‖)) ≤
        Real.sin a.angle *
          (∑ i, weight i *
            ⟪direction i, L (a.first (poly.v (index i)))⟫))
    (offset : ℝ²) :
    ¬ ∀ i, L (Q (poly.v (index i))) + offset ∈
      interior (convexHull ℝ {L (poly.v j) | j}) := by
  intro hinner
  apply not_strictly_contained_of_balanced_support
    {L (poly.v j) | j} weight direction
    (fun i => L (Q (poly.v (index i))))
    (fun i => L (poly.v (index i))) offset
    hdirection hweight hweight_pos hbalance
  · intro i y hy
    obtain ⟨j, rfl⟩ := hy
    exact hsupport i j
  · exact hinner
  · have hdisp := axisAngle_weighted_displacement_nonneg a L hL
        weight direction (fun i => poly.v (index i)) hweight hdominates
    simpa only [← map_sub] using hdisp

/-- A finite-rotation balanced-support certificate rules out an actual
`MatrixPose`.  Unlike the original local theorem, this statement keeps the
arbitrary planar translation and cancels it using the balance equation. -/
theorem not_rupertPose_of_axisAngle_certificate
    {ι κ : Type} [Fintype ι] [Fintype κ] [Nonempty κ]
    (poly : Polyhedron ι ℝ³) (p : MatrixPose)
    (a : AxisAngle
      ((relativeRotation p).val.toEuclideanLin.toContinuousLinearMap))
    (index : κ → ι) (weight : κ → ℝ) (direction : κ → ℝ²)
    (hdirection : ∀ i, direction i ≠ 0)
    (hweight : ∀ i, 0 ≤ weight i) (hweight_pos : ∃ i, 0 < weight i)
    (hbalance : ∑ i, weight i • direction i = 0)
    (hsupport : ∀ i j,
      ⟪direction i, outerProjectionLinear p (poly.v j)⟫ ≤
        ⟪direction i, outerProjectionLinear p (poly.v (index i))⟫)
    (hdominates :
      (1 - Real.cos a.angle) *
          (∑ i, weight i * (‖direction i‖ * ‖poly.v (index i)‖)) ≤
        Real.sin a.angle *
          (∑ i, weight i *
            ⟪direction i,
              outerProjectionLinear p (a.first (poly.v (index i)))⟫)) :
    ¬ RupertPose p poly.hull := by
  refine not_rupertPose_of_balanced_support poly p index index weight direction
    hdirection hweight hweight_pos hbalance ?_ ?_
  · rintro i y ⟨v, ⟨j, rfl⟩, rfl⟩
    change ⟪direction i,
        proj_xyL (p.outerRot.val.toEuclideanLin (poly.v j))⟫ ≤
      ⟪direction i,
        proj_xyL (p.outerRot.val.toEuclideanLin (poly.v (index i)))⟫
    simpa [outerProjectionLinear] using hsupport i j
  · have hdisp := axisAngle_weighted_displacement_nonneg a
      (outerProjectionLinear p) (outerProjectionLinear_norm_le p)
      weight direction (fun i => poly.v (index i)) hweight hdominates
    simp_rw [← outer_relative_apply p]
    change 0 ≤ ∑ i, weight i *
      ⟪direction i,
        outerProjectionLinear p
            ((relativeRotation p).val.toEuclideanLin.toContinuousLinearMap
              (poly.v (index i))) -
          outerProjectionLinear p (poly.v (index i))⟫
    simpa only [← map_sub] using hdisp

/-- Symmetry-reindexed version of the local certificate.  The tracked inner
vertex `innerIndex i` may differ from its supporting outer vertex
`outerIndex i`; `htracks` states that, after removing a polyhedron symmetry,
their displacement is the small rotation `Q`. -/
theorem not_rupertPose_of_reindexed_axisAngle_certificate
    {ι κ : Type} [Fintype ι] [Fintype κ] [Nonempty κ]
    (poly : Polyhedron ι ℝ³) (p : MatrixPose)
    {Q : ℝ³ →L[ℝ] ℝ³} (a : AxisAngle Q)
    (innerIndex outerIndex : κ → ι)
    (weight : κ → ℝ) (direction : κ → ℝ²)
    (hdirection : ∀ i, direction i ≠ 0)
    (hweight : ∀ i, 0 ≤ weight i) (hweight_pos : ∃ i, 0 < weight i)
    (hbalance : ∑ i, weight i • direction i = 0)
    (htracks : ∀ i,
      proj_xyL (p.innerRot.val.toEuclideanLin (poly.v (innerIndex i))) =
        outerProjectionLinear p (Q (poly.v (outerIndex i))))
    (hsupport : ∀ i j,
      ⟪direction i, outerProjectionLinear p (poly.v j)⟫ ≤
        ⟪direction i, outerProjectionLinear p (poly.v (outerIndex i))⟫)
    (hdominates :
      (1 - Real.cos a.angle) *
          (∑ i, weight i * (‖direction i‖ * ‖poly.v (outerIndex i)‖)) ≤
        Real.sin a.angle *
          (∑ i, weight i *
            ⟪direction i,
              outerProjectionLinear p (a.first (poly.v (outerIndex i)))⟫)) :
    ¬ RupertPose p poly.hull := by
  refine not_rupertPose_of_balanced_support poly p innerIndex outerIndex
    weight direction hdirection hweight hweight_pos hbalance ?_ ?_
  · rintro i y ⟨v, ⟨j, rfl⟩, rfl⟩
    change ⟪direction i,
        proj_xyL (p.outerRot.val.toEuclideanLin (poly.v j))⟫ ≤
      ⟪direction i,
        proj_xyL (p.outerRot.val.toEuclideanLin (poly.v (outerIndex i)))⟫
    simpa [outerProjectionLinear] using hsupport i j
  · have hdisp := axisAngle_weighted_displacement_nonneg a
      (outerProjectionLinear p) (outerProjectionLinear_norm_le p)
      weight direction (fun i => poly.v (outerIndex i)) hweight hdominates
    simp_rw [htracks]
    change 0 ≤ ∑ i, weight i *
      ⟪direction i,
        outerProjectionLinear p (Q (poly.v (outerIndex i))) -
          outerProjectionLinear p (poly.v (outerIndex i))⟫
    simpa only [← map_sub] using hdisp

end Noperthedron.BalancedSupport

end
