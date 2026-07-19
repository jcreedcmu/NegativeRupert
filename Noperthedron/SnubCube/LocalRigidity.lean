module

public import Noperthedron.BalancedSupport.AxisFree
public import Noperthedron.BalancedSupport.LocalRigidity
public import Noperthedron.BalancedSupport.RotationDistance
public import Noperthedron.RationalApprox.Cast
public import Noperthedron.RationalApprox.MatrixBounds
public import Noperthedron.SnubCube.Symmetry
public import Mathlib.Analysis.InnerProductSpace.Adjoint

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

/-- Exact point on the symmetry-equality stratum above a chosen outer
rotation. -/
def equalityPose (outer : SO3) (g : VertexIndex) : MatrixPose where
  innerRot := outer * symmetry g
  outerRot := outer
  innerOffset := 0

@[simp] theorem relativeRotationAtSymmetry_equalityPose
    (outer : SO3) (g : VertexIndex) :
    relativeRotationAtSymmetry (equalityPose outer g) g = 1 := by
  simp [relativeRotationAtSymmetry, relativeRotation, equalityPose, ← mul_assoc]

noncomputable def so3CLM (r : SO3) : ℝ³ →L[ℝ] ℝ³ :=
  r.val.toEuclideanLin.toContinuousLinearMap

private noncomputable def so3Frame (r : SO3) : ℝ³ ≃ₗᵢ[ℝ] ℝ³ :=
  Bounding.OrthogonalGroup.toLinearIsometryEquiv ⟨r.val, r.property.1⟩

private theorem so3CLM_eq_frame (r : SO3) :
    so3CLM r = (so3Frame r).toLinearIsometry.toContinuousLinearMap := by
  rfl

theorem so3CLM_mul (r s : SO3) :
    so3CLM (r * s) = so3CLM r ∘L so3CLM s := by
  ext v
  simp [so3CLM, Matrix.mulVec_mulVec]

@[simp] private theorem so3CLM_one : so3CLM (1 : SO3) = 1 := by
  ext v
  simp [so3CLM]

theorem so3CLM_norm (r : SO3) : ‖so3CLM r‖ = 1 := by
  rw [so3CLM_eq_frame]
  exact (so3Frame r).toLinearIsometry.norm_toContinuousLinearMap

private theorem so3CLM_left_norm (r : SO3) (A : ℝ³ →L[ℝ] ℝ³) :
    ‖so3CLM r ∘L A‖ = ‖A‖ := by
  rw [so3CLM_eq_frame]
  exact (so3Frame r).toLinearIsometry.norm_toContinuousLinearMap_comp

private theorem so3CLM_right_norm (A : ℝ³ →L[ℝ] ℝ³) (r : SO3) :
    ‖A ∘L so3CLM r‖ = ‖A‖ := by
  rw [so3CLM_eq_frame]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv A (so3Frame r)

private theorem norm_so3CLM_inv_sub_inv (r s : SO3) :
    ‖so3CLM r⁻¹ - so3CLM s⁻¹‖ = ‖so3CLM r - so3CLM s‖ := by
  have hdecomp : so3CLM r⁻¹ - so3CLM s⁻¹ =
      so3CLM r⁻¹ ∘L (so3CLM s - so3CLM r) ∘L so3CLM s⁻¹ := by
    ext v
    have hr (x : ℝ³) : so3CLM r⁻¹ (so3CLM r x) = x := by
      rw [← ContinuousLinearMap.comp_apply, ← so3CLM_mul]
      simp
    have hs (x : ℝ³) : so3CLM s (so3CLM s⁻¹ x) = x := by
      rw [← ContinuousLinearMap.comp_apply, ← so3CLM_mul]
      simp
    simp only [sub_apply, ContinuousLinearMap.comp_apply]
    rw [hs, map_sub, hr]
  rw [hdecomp, so3CLM_left_norm, so3CLM_right_norm, norm_sub_rev]

theorem norm_relativeRotation_sub_le (p q : MatrixPose) :
    ‖so3CLM (relativeRotation p) - so3CLM (relativeRotation q)‖ ≤
      ‖so3CLM p.innerRot - so3CLM q.innerRot‖ +
        ‖so3CLM p.outerRot - so3CLM q.outerRot‖ := by
  rw [relativeRotation, relativeRotation, so3CLM_mul, so3CLM_mul]
  apply (norm_comp_sub_comp_le (so3CLM p.outerRot⁻¹) (so3CLM p.innerRot)
    (so3CLM q.outerRot⁻¹) (so3CLM q.innerRot)
    (by rw [so3CLM_norm]) (by rw [so3CLM_norm])).trans
  rw [norm_so3CLM_inv_sub_inv]
  linarith [norm_sub_rev (so3CLM p.outerRot) (so3CLM q.outerRot)]

theorem norm_relativeRotationAtSymmetry_sub_le
    (p q : MatrixPose) (g : VertexIndex) :
    ‖so3CLM (relativeRotationAtSymmetry p g) -
        so3CLM (relativeRotationAtSymmetry q g)‖ ≤
      ‖so3CLM p.innerRot - so3CLM q.innerRot‖ +
        ‖so3CLM p.outerRot - so3CLM q.outerRot‖ := by
  rw [relativeRotationAtSymmetry, relativeRotationAtSymmetry,
    so3CLM_mul, so3CLM_mul]
  rw [← ContinuousLinearMap.sub_comp, so3CLM_right_norm]
  exact norm_relativeRotation_sub_le p q

/-- Distance from the symmetry stratum is bounded by the direct inner-matrix
mismatch.  This avoids choosing Euler coordinates for an equality pose. -/
theorem norm_relativeRotationAtSymmetry_one_le_inner_mismatch
    (p : MatrixPose) (g : VertexIndex) :
    ‖so3CLM (relativeRotationAtSymmetry p g) - 1‖ ≤
      ‖so3CLM p.innerRot - so3CLM (p.outerRot * symmetry g)‖ := by
  have h := norm_relativeRotationAtSymmetry_sub_le p (equalityPose p.outerRot g) g
  rw [relativeRotationAtSymmetry_equalityPose, so3CLM_one] at h
  simpa [equalityPose] using h

/-- Division-free local-angle test from a certified inner/symmetry matrix
mismatch. -/
theorem AxisAngle.ratio_of_inner_mismatch_bound
    (p : MatrixPose) (g : VertexIndex)
    (a : AxisAngle
      ((relativeRotationAtSymmetry p g).val.toEuclideanLin.toContinuousLinearMap))
    (c r : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hmismatch : ‖so3CLM p.innerRot - so3CLM (p.outerRot * symmetry g)‖ ≤ r)
    (hsmall : r ^ 2 * (1 + c ^ 2) ≤ 4 * c ^ 2) :
    1 - Real.cos a.angle ≤ |Real.sin a.angle| * c := by
  apply a.ratio_of_norm_bound c r hc hr
  · exact (norm_relativeRotationAtSymmetry_one_le_inner_mismatch p g).trans hmismatch
  · exact hsmall

/-- The relative rotation, after removing a fixed snub-cube symmetry, is
Lipschitz in the five Euler coordinates.  The planar translations do not
appear because they do not affect either rotation. -/
theorem norm_relativeRotationAtSymmetry_matrixPoseWithOffset_sub_le
    (p q : Pose ℝ) (offset offset₀ : ℝ²) (g : VertexIndex) :
    ‖so3CLM (relativeRotationAtSymmetry (p.matrixPoseWithOffset offset) g) -
        so3CLM (relativeRotationAtSymmetry (q.matrixPoseWithOffset offset₀) g)‖ ≤
      |p.α - q.α| + |p.φ₁ - q.φ₁| + |p.θ₁ - q.θ₁| +
        (|p.φ₂ - q.φ₂| + |p.θ₂ - q.θ₂|) := by
  apply (norm_relativeRotationAtSymmetry_sub_le
    (p.matrixPoseWithOffset offset) (q.matrixPoseWithOffset offset₀) g).trans
  simp only [Pose.matrixPoseWithOffset, Pose.matrixPoseOfPose, so3CLM]
  rw [← rotRM_eq_rotRM_mat, ← rotRM_eq_rotRM_mat,
    ← rotRM_eq_rotRM_mat, ← rotRM_eq_rotRM_mat]
  have hin := norm_rotRM_sub_le p.θ₁ p.φ₁ p.α q.θ₁ q.φ₁ q.α
  have hout := norm_rotRM_sub_le p.θ₂ p.φ₂ 0 q.θ₂ q.φ₂ 0
  norm_num at hout
  linarith

/-- The unadjusted relative rotation is likewise Lipschitz in the five Euler
coordinates. -/
theorem norm_relativeRotation_matrixPoseWithOffset_sub_le
    (p q : Pose ℝ) (offset offset₀ : ℝ²) :
    ‖so3CLM (relativeRotation (p.matrixPoseWithOffset offset)) -
        so3CLM (relativeRotation (q.matrixPoseWithOffset offset₀))‖ ≤
      |p.α - q.α| + |p.φ₁ - q.φ₁| + |p.θ₁ - q.θ₁| +
        (|p.φ₂ - q.φ₂| + |p.θ₂ - q.θ₂|) := by
  apply (norm_relativeRotation_sub_le
    (p.matrixPoseWithOffset offset) (q.matrixPoseWithOffset offset₀)).trans
  simp only [Pose.matrixPoseWithOffset, Pose.matrixPoseOfPose, so3CLM]
  rw [← rotRM_eq_rotRM_mat, ← rotRM_eq_rotRM_mat,
    ← rotRM_eq_rotRM_mat, ← rotRM_eq_rotRM_mat]
  have hin := norm_rotRM_sub_le p.θ₁ p.φ₁ p.α q.θ₁ q.φ₁ q.α
  have hout := norm_rotRM_sub_le p.θ₂ p.φ₂ 0 q.θ₂ q.φ₂ 0
  norm_num at hout
  linarith

theorem norm_outerRot_matrixPoseWithOffset_sub_le
    (p q : Pose ℝ) (offset offset₀ : ℝ²) :
    ‖so3CLM (p.matrixPoseWithOffset offset).outerRot -
        so3CLM (q.matrixPoseWithOffset offset₀).outerRot‖ ≤
      |p.φ₂ - q.φ₂| + |p.θ₂ - q.θ₂| := by
  simp only [Pose.matrixPoseWithOffset, Pose.matrixPoseOfPose, so3CLM]
  rw [← rotRM_eq_rotRM_mat, ← rotRM_eq_rotRM_mat]
  have h := norm_rotRM_sub_le p.θ₂ p.φ₂ 0 q.θ₂ q.φ₂ 0
  norm_num at h
  exact h

/-- A rational bound on the five Euler-coordinate differences bounds the
operator-norm distance from a chosen equality stratum. -/
theorem norm_relativeRotationAtSymmetry_matrixPoseWithOffset_one_le
    (p center : Pose ℝ) (offset centerOffset : ℝ²) (g : VertexIndex) (r : ℝ)
    (hcenter :
      relativeRotationAtSymmetry (center.matrixPoseWithOffset centerOffset) g = 1)
    (hbox :
      |p.α - center.α| + |p.φ₁ - center.φ₁| + |p.θ₁ - center.θ₁| +
          (|p.φ₂ - center.φ₂| + |p.θ₂ - center.θ₂|) ≤ r) :
    ‖so3CLM (relativeRotationAtSymmetry (p.matrixPoseWithOffset offset) g) - 1‖ ≤ r := by
  have h := norm_relativeRotationAtSymmetry_matrixPoseWithOffset_sub_le
    p center offset centerOffset g
  rw [hcenter, so3CLM_one] at h
  exact h.trans hbox

/-- Division-free local-angle test obtained directly from a pose box.  This
is the form intended for generated rational local certificates. -/
theorem AxisAngle.ratio_of_pose_box
    (p center : Pose ℝ) (offset centerOffset : ℝ²) (g : VertexIndex)
    (a : AxisAngle ((relativeRotationAtSymmetry
      (p.matrixPoseWithOffset offset) g).val.toEuclideanLin.toContinuousLinearMap))
    (c r : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hcenter :
      relativeRotationAtSymmetry (center.matrixPoseWithOffset centerOffset) g = 1)
    (hbox :
      |p.α - center.α| + |p.φ₁ - center.φ₁| + |p.θ₁ - center.θ₁| +
          (|p.φ₂ - center.φ₂| + |p.θ₂ - center.θ₂|) ≤ r)
    (hsmall : r ^ 2 * (1 + c ^ 2) ≤ 4 * c ^ 2) :
    1 - Real.cos a.angle ≤ |Real.sin a.angle| * c := by
  apply a.ratio_of_norm_bound c r hc hr
  · exact norm_relativeRotationAtSymmetry_matrixPoseWithOffset_one_le
      p center offset centerOffset g r hcenter hbox
  · exact hsmall

/-- Orthonormal frame used by the outer shadow. -/
noncomputable def outerFrame (p : MatrixPose) : ℝ³ ≃ₗᵢ[ℝ] ℝ³ :=
  Bounding.OrthogonalGroup.toLinearIsometryEquiv
    ⟨p.outerRot.val, p.outerRot.property.1⟩

/-- Lift a planar support direction back through the outer rotation. -/
noncomputable def outerLift (p : MatrixPose) (u : ℝ²) : ℝ³ :=
  (outerFrame p).symm (inject_xy u)

private theorem norm_inject_xy (u : ℝ²) : ‖inject_xy u‖ = ‖u‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Fin.sum_univ_three, inject_xy]

private theorem outerLift_eq_inv_apply (p : MatrixPose) (u : ℝ²) :
    outerLift p u = so3CLM p.outerRot⁻¹ (inject_xy u) := by
  have hforward : so3CLM p.outerRot (outerLift p u) = inject_xy u := by
    change outerFrame p ((outerFrame p).symm (inject_xy u)) = inject_xy u
    exact (outerFrame p).apply_symm_apply (inject_xy u)
  have hinv (x : ℝ³) : so3CLM p.outerRot⁻¹ (so3CLM p.outerRot x) = x := by
    rw [← ContinuousLinearMap.comp_apply, ← so3CLM_mul]
    simp
  rw [← hforward, hinv]

theorem norm_outerLift_sub_le (p q : MatrixPose) (u : ℝ²) :
    ‖outerLift p u - outerLift q u‖ ≤
      ‖so3CLM p.outerRot - so3CLM q.outerRot‖ * ‖u‖ := by
  rw [outerLift_eq_inv_apply, outerLift_eq_inv_apply]
  rw [← sub_apply]
  apply ((so3CLM p.outerRot⁻¹ - so3CLM q.outerRot⁻¹).le_opNorm
    (inject_xy u)).trans_eq
  rw [norm_so3CLM_inv_sub_inv, norm_inject_xy]

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

theorem outerLift_matrixPoseWithOffset_eq_adjoint
    (p : Pose ℝ) (offset : ℝ²) (u : ℝ²) :
    outerLift (p.matrixPoseWithOffset offset) u = (rotM p.θ₂ p.φ₂).adjoint u := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [← inner_outerProjection_eq_outerLift]
  rw [outerProjectionLinear, ContinuousLinearMap.comp_apply]
  change ⟪u, proj_xyL
    ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin x)⟫ = _
  rw [matrixPoseWithOffset_outer_rotation_project]
  rw [Pose.outer_eq_M]
  rfl

private theorem pose_mem_four_outer (p : Pose ℚ) (hp : p ∈ fourInterval ℚ) :
    p.θ₂ ∈ Set.Icc (-4 : ℚ) 4 ∧ p.φ₂ ∈ Set.Icc (-4 : ℚ) 4 := by
  rw [NonemptyInterval.mem_def] at hp
  change (fourInterval ℚ).min ≤ p ∧ p ≤ (fourInterval ℚ).max at hp
  simp only [fourInterval_min, fourInterval_max] at hp
  rw [Pose.le_iff, Pose.le_iff] at hp
  exact ⟨⟨hp.1.2.1, hp.2.2.1⟩, ⟨hp.1.2.2.2.1, hp.2.2.2.2.1⟩⟩

theorem norm_outerLift_rationalApprox_sub_le
    (p : Pose ℚ) (hp : p ∈ fourInterval ℚ) (offset : ℝ²)
    (u : ℝ²) (hu : ‖u‖ = 1) :
    ‖outerLift (p.toReal.matrixPoseWithOffset offset) u -
        (RationalApprox.rotMℚℝ (p.θ₂ : ℝ) (p.φ₂ : ℝ)).adjoint u‖ ≤
      RationalApprox.κ := by
  rw [outerLift_matrixPoseWithOffset_eq_adjoint]
  rw [← sub_apply, ← map_sub]
  calc
    ‖((rotM (p.θ₂ : ℝ) (p.φ₂ : ℝ) -
        RationalApprox.rotMℚℝ (p.θ₂ : ℝ) (p.φ₂ : ℝ)).adjoint) u‖ ≤
        ‖(rotM (p.θ₂ : ℝ) (p.φ₂ : ℝ) -
          RationalApprox.rotMℚℝ (p.θ₂ : ℝ) (p.φ₂ : ℝ)).adjoint‖ * ‖u‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖rotM (p.θ₂ : ℝ) (p.φ₂ : ℝ) -
          RationalApprox.rotMℚℝ (p.θ₂ : ℝ) (p.φ₂ : ℝ)‖ := by
      rw [LinearIsometryEquiv.norm_map, hu, mul_one]
    _ ≤ RationalApprox.κ := by
      apply RationalApprox.M_difference_norm_bounded
      · exact RationalApprox.cast_Icc4_mem ⟨p.θ₂, (pose_mem_four_outer p hp).1⟩
      · exact RationalApprox.cast_Icc4_mem ⟨p.φ₂, (pose_mem_four_outer p hp).2⟩

theorem norm_rationalApprox_outerLift_le
    (p : Pose ℚ) (hp : p ∈ fourInterval ℚ) (u : ℝ²) (hu : ‖u‖ = 1) :
    ‖(RationalApprox.rotMℚℝ (p.θ₂ : ℝ) (p.φ₂ : ℝ)).adjoint u‖ ≤
      1 + RationalApprox.κ := by
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  rw [LinearIsometryEquiv.norm_map, hu, mul_one]
  apply RationalApprox.Mℚ_norm_bounded
  · exact RationalApprox.cast_Icc4_mem ⟨p.θ₂, (pose_mem_four_outer p hp).1⟩
  · exact RationalApprox.cast_Icc4_mem ⟨p.φ₂, (pose_mem_four_outer p hp).2⟩

/-- Coordinate-free first-variation vector for one balanced certificate. -/
noncomputable def firstVariationVector
    {κ : Type} [Fintype κ] (p : MatrixPose)
    (weight : κ → ℝ) (direction : κ → ℝ²) (vertex : κ → ℝ³) : ℝ³ :=
  ∑ i, weight i • cross3 (vertex i) (outerLift p (direction i))

/-- A balanced certificate's first-variation vector is Lipschitz in the
outer rotation.  Its natural remainder budget is also its Lipschitz scale. -/
theorem norm_firstVariationVector_sub_le
    {κ : Type} [Fintype κ] (p q : MatrixPose)
    (weight : κ → ℝ) (direction : κ → ℝ²) (vertex : κ → ℝ³)
    (hweight : ∀ i, 0 ≤ weight i) :
    ‖firstVariationVector p weight direction vertex -
        firstVariationVector q weight direction vertex‖ ≤
      (∑ i, weight i * (‖direction i‖ * ‖vertex i‖)) *
        ‖so3CLM p.outerRot - so3CLM q.outerRot‖ := by
  have hsum : firstVariationVector p weight direction vertex -
      firstVariationVector q weight direction vertex =
      ∑ i, weight i • cross3 (vertex i)
        (outerLift p (direction i) - outerLift q (direction i)) := by
    simp only [firstVariationVector, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← smul_sub, cross3_sub_right]
  rw [hsum]
  apply (norm_sum_le _ _).trans
  calc
    ∑ i, ‖weight i • cross3 (vertex i)
          (outerLift p (direction i) - outerLift q (direction i))‖
        ≤ ∑ i, weight i * (‖direction i‖ * ‖vertex i‖) *
          ‖so3CLM p.outerRot - so3CLM q.outerRot‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hweight i)]
      have hcross := cross3_norm_le (vertex i)
        (outerLift p (direction i) - outerLift q (direction i))
      have hlift := norm_outerLift_sub_le p q (direction i)
      calc
        weight i *
            ‖cross3 (vertex i)
              (outerLift p (direction i) - outerLift q (direction i))‖
            ≤ weight i *
              (‖vertex i‖ *
                ‖outerLift p (direction i) - outerLift q (direction i)‖) :=
          mul_le_mul_of_nonneg_left hcross (hweight i)
        _ ≤ weight i *
              (‖vertex i‖ *
                (‖so3CLM p.outerRot - so3CLM q.outerRot‖ * ‖direction i‖)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlift (norm_nonneg _)) (hweight i)
        _ = weight i * (‖direction i‖ * ‖vertex i‖) *
              ‖so3CLM p.outerRot - so3CLM q.outerRot‖ := by ring
    _ = (∑ i, weight i * (‖direction i‖ * ‖vertex i‖)) *
          ‖so3CLM p.outerRot - so3CLM q.outerRot‖ := by
      rw [Finset.sum_mul]

/-- Uniform error bound for a weighted family of cross products. -/
theorem norm_weightedCross_approx_sub_le
    {κ : Type} [Fintype κ]
    (weight : κ → ℝ) (vertex approxVertex lift approxLift : κ → ℝ³)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hweight : ∀ i, 0 ≤ weight i)
    (hvertex : ∀ i, ‖vertex i‖ ≤ 1)
    (hvertexError : ∀ i, ‖vertex i - approxVertex i‖ ≤ ε)
    (hliftError : ∀ i, ‖lift i - approxLift i‖ ≤ ε)
    (happroxLift : ∀ i, ‖approxLift i‖ ≤ 1 + ε) :
    ‖(∑ i, weight i • cross3 (vertex i) (lift i)) -
        ∑ i, weight i • cross3 (approxVertex i) (approxLift i)‖ ≤
      (∑ i, weight i) * (2 * ε + ε ^ 2) := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    ∑ i, ‖weight i • cross3 (vertex i) (lift i) -
          weight i • cross3 (approxVertex i) (approxLift i)‖
        ≤ ∑ i, weight i * (2 * ε + ε ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hweight i)]
      have hcross :
          ‖cross3 (vertex i) (lift i) -
              cross3 (approxVertex i) (approxLift i)‖ ≤ 2 * ε + ε ^ 2 := by
        rw [cross3_sub_cross3]
        calc
          ‖cross3 (vertex i) (lift i - approxLift i) +
              cross3 (vertex i - approxVertex i) (approxLift i)‖ ≤
              ‖cross3 (vertex i) (lift i - approxLift i)‖ +
                ‖cross3 (vertex i - approxVertex i) (approxLift i)‖ :=
            norm_add_le _ _
          _ ≤ ‖vertex i‖ * ‖lift i - approxLift i‖ +
                ‖vertex i - approxVertex i‖ * ‖approxLift i‖ :=
            add_le_add (cross3_norm_le _ _) (cross3_norm_le _ _)
          _ ≤ 1 * ε + ε * (1 + ε) := by
            apply add_le_add
            · exact (mul_le_mul_of_nonneg_right (hvertex i) (norm_nonneg _)).trans
                (mul_le_mul_of_nonneg_left (hliftError i) (by norm_num))
            · exact (mul_le_mul_of_nonneg_right (hvertexError i) (norm_nonneg _)).trans
                (mul_le_mul_of_nonneg_left (happroxLift i) hε)
          _ = 2 * ε + ε ^ 2 := by ring
      exact mul_le_mul_of_nonneg_left hcross (hweight i)
    _ = (∑ i, weight i) * (2 * ε + ε ^ 2) := by
      rw [Finset.sum_mul]

/-- Normalizing by the positive total weight removes the size of the
certificate from the approximation error. -/
theorem norm_normalizedWeightedCross_approx_sub_le
    {κ : Type} [Fintype κ]
    (weight : κ → ℝ) (vertex approxVertex lift approxLift : κ → ℝ³)
    (normalized approxNormalized : ℝ³) (B ε : ℝ)
    (hε : 0 ≤ ε) (hweight : ∀ i, 0 ≤ weight i) (hB : 0 < B)
    (hBsum : B = ∑ i, weight i)
    (hvertex : ∀ i, ‖vertex i‖ ≤ 1)
    (hvertexError : ∀ i, ‖vertex i - approxVertex i‖ ≤ ε)
    (hliftError : ∀ i, ‖lift i - approxLift i‖ ≤ ε)
    (happroxLift : ∀ i, ‖approxLift i‖ ≤ 1 + ε)
    (hactual : ∑ i, weight i • cross3 (vertex i) (lift i) = B • normalized)
    (happrox : ∑ i, weight i • cross3 (approxVertex i) (approxLift i) =
      B • approxNormalized) :
    ‖normalized - approxNormalized‖ ≤ 2 * ε + ε ^ 2 := by
  have h := norm_weightedCross_approx_sub_le weight vertex approxVertex lift approxLift
    ε hε hweight hvertex hvertexError hliftError happroxLift
  rw [← hBsum] at h
  have hsub : (∑ i, weight i • cross3 (vertex i) (lift i)) -
      ∑ i, weight i • cross3 (approxVertex i) (approxLift i) =
      B • (normalized - approxNormalized) := by
    rw [hactual, happrox, smul_sub]
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hB] at h
  nlinarith

/-- After division by its positive remainder budget, a first-variation
vector is 1-Lipschitz in the outer rotation. -/
theorem norm_normalizedFirstVariation_sub_le
    {κ : Type} [Fintype κ] (p q : MatrixPose)
    (weight : κ → ℝ) (direction : κ → ℝ²) (vertex : κ → ℝ³)
    (normalized currentCenter : ℝ³) (B : ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hB : 0 < B)
    (hbudget : B = ∑ i, weight i * (‖direction i‖ * ‖vertex i‖))
    (hcurrent : firstVariationVector p weight direction vertex = B • normalized)
    (hcenter : firstVariationVector q weight direction vertex = B • currentCenter) :
    ‖normalized - currentCenter‖ ≤
      ‖so3CLM p.outerRot - so3CLM q.outerRot‖ := by
  have h := norm_firstVariationVector_sub_le p q weight direction vertex hweight
  rw [← hbudget] at h
  have hsub : firstVariationVector p weight direction vertex -
      firstVariationVector q weight direction vertex =
      B • (normalized - currentCenter) := by
    rw [hcurrent, hcenter, smul_sub]
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hB] at h
  nlinarith

/-- Upper-budget variant of normalized first-variation stability.  This is
the form used by rational rows: unit directions and radius-one vertices make
the sum of the weights a convenient rational upper bound, without requiring
exact algebraic vertex norms in the certificate. -/
theorem norm_normalizedFirstVariation_sub_le_of_budget_bound
    {κ : Type} [Fintype κ] (p q : MatrixPose)
    (weight : κ → ℝ) (direction : κ → ℝ²) (vertex : κ → ℝ³)
    (normalized currentCenter : ℝ³) (B : ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hB : 0 < B)
    (hbudget : ∑ i, weight i * (‖direction i‖ * ‖vertex i‖) ≤ B)
    (hcurrent : firstVariationVector p weight direction vertex = B • normalized)
    (hcenter : firstVariationVector q weight direction vertex = B • currentCenter) :
    ‖normalized - currentCenter‖ ≤
      ‖so3CLM p.outerRot - so3CLM q.outerRot‖ := by
  have h := norm_firstVariationVector_sub_le p q weight direction vertex hweight
  have hscale :
      (∑ i, weight i * (‖direction i‖ * ‖vertex i‖)) *
          ‖so3CLM p.outerRot - so3CLM q.outerRot‖ ≤
        B * ‖so3CLM p.outerRot - so3CLM q.outerRot‖ :=
    mul_le_mul_of_nonneg_right hbudget (norm_nonneg _)
  have hsub : firstVariationVector p weight direction vertex -
      firstVariationVector q weight direction vertex =
      B • (normalized - currentCenter) := by
    rw [hcurrent, hcenter, smul_sub]
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hB] at h
  nlinarith

/-- Pose-coordinate form used by local rows: normalized axis-coverage vectors
lose at most the two-coordinate outer Euler distance. -/
theorem norm_normalizedFirstVariation_matrixPoseWithOffset_sub_le
    {κ : Type} [Fintype κ]
    (p center : Pose ℝ) (offset centerOffset : ℝ²)
    (weight : κ → ℝ) (direction : κ → ℝ²) (vertex : κ → ℝ³)
    (normalized centerNormalized : ℝ³) (B : ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hB : 0 < B)
    (hbudget : B = ∑ i, weight i * (‖direction i‖ * ‖vertex i‖))
    (hcurrent : firstVariationVector (p.matrixPoseWithOffset offset)
      weight direction vertex = B • normalized)
    (hcenter : firstVariationVector (center.matrixPoseWithOffset centerOffset)
      weight direction vertex = B • centerNormalized) :
    ‖normalized - centerNormalized‖ ≤
      |p.φ₂ - center.φ₂| + |p.θ₂ - center.θ₂| := by
  exact (norm_normalizedFirstVariation_sub_le
    (p.matrixPoseWithOffset offset) (center.matrixPoseWithOffset centerOffset)
    weight direction vertex normalized centerNormalized B
    hweight hB hbudget hcurrent hcenter).trans
      (norm_outerRot_matrixPoseWithOffset_sub_le p center offset centerOffset)

/-- Pose-coordinate upper-budget form of normalized axis-vector stability. -/
theorem norm_normalizedFirstVariation_matrixPoseWithOffset_sub_le_of_budget_bound
    {κ : Type} [Fintype κ]
    (p center : Pose ℝ) (offset centerOffset : ℝ²)
    (weight : κ → ℝ) (direction : κ → ℝ²) (vertex : κ → ℝ³)
    (normalized centerNormalized : ℝ³) (B : ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hB : 0 < B)
    (hbudget : ∑ i, weight i * (‖direction i‖ * ‖vertex i‖) ≤ B)
    (hcurrent : firstVariationVector (p.matrixPoseWithOffset offset)
      weight direction vertex = B • normalized)
    (hcenter : firstVariationVector (center.matrixPoseWithOffset centerOffset)
      weight direction vertex = B • centerNormalized) :
    ‖normalized - centerNormalized‖ ≤
      |p.φ₂ - center.φ₂| + |p.θ₂ - center.θ₂| := by
  exact (norm_normalizedFirstVariation_sub_le_of_budget_bound
    (p.matrixPoseWithOffset offset) (center.matrixPoseWithOffset centerOffset)
    weight direction vertex normalized centerNormalized B
    hweight hB hbudget hcurrent hcenter).trans
      (norm_outerRot_matrixPoseWithOffset_sub_le p center offset centerOffset)

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

/-- Perturbation-stable geometric axis-free obstruction.  Axis coverage is
certified once at a center configuration with radius `c + δ`; pointwise
movement of each normalized first-variation vector by at most `δ` leaves
the required radius `c` at the current pose. -/
theorem not_rupertPose_of_axisFree_geometric_certificates_of_perturbation
    {J κ : Type} [Fintype J] [Nonempty J] [Fintype κ] [Nonempty κ]
    (p : MatrixPose) (g : VertexIndex)
    (a : AxisAngle
      ((relativeRotationAtSymmetry p g).val.toEuclideanLin.toContinuousLinearMap))
    (index : J → κ → VertexIndex)
    (weight : J → κ → ℝ) (direction : J → κ → ℝ²)
    (A normalizedA centerNormalizedA : J → ℝ³) (B : J → ℝ)
    (c δ : ℝ)
    (hcδ : 0 ≤ c + δ)
    (hB : ∀ j, 0 < B j)
    (hA : ∀ j, A j = B j • normalizedA j)
    (hball : Metric.closedBall (0 : ℝ³) (c + δ) ⊆
      convexHull ℝ {centerNormalizedA j | j})
    (hmove : ∀ j, ‖normalizedA j - centerNormalizedA j‖ ≤ δ)
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
  obtain ⟨j, hj⟩ := exists_axis_certificate_dominating_remainder_of_perturbation
    centerNormalizedA normalizedA A B c δ |Real.sin a.angle| (1 - Real.cos a.angle)
    hcδ (abs_nonneg _) hB hA hball hmove hratio a.signedAxis a.signedAxis_norm
  apply not_rupertPose_of_symmetry_axisAngle_certificate p g a
    (index j) (weight j) (direction j)
    (hdirection j) (hweight j) (hweight_pos j) (hbalance j) (hsupport j)
  rw [← hB_eq j]
  rw [axisAngle_weighted_first_identity a p (weight j) (direction j)
    (fun i => normalizedExactVertex (symmetryAction g (index j i)))]
  rw [← hA_eq j]
  exact hj

/-- Direct-axis-cover form of the perturbation theorem.  In generated
certificates `hcover` can be discharged by six rational barycentric witnesses
and `octahedral_axis_cover`. -/
theorem not_rupertPose_of_axisFree_geometric_certificates_of_cover_perturbation
    {J κ : Type} [Fintype J] [Nonempty J] [Fintype κ] [Nonempty κ]
    (p : MatrixPose) (g : VertexIndex)
    (a : AxisAngle
      ((relativeRotationAtSymmetry p g).val.toEuclideanLin.toContinuousLinearMap))
    (index : J → κ → VertexIndex)
    (weight : J → κ → ℝ) (direction : J → κ → ℝ²)
    (A normalizedA centerNormalizedA : J → ℝ³) (B : J → ℝ)
    (c δ : ℝ)
    (hB : ∀ j, 0 < B j)
    (hA : ∀ j, A j = B j • normalizedA j)
    (hcover : ∀ axis : ℝ³, ‖axis‖ = 1 →
      ∃ j, c + δ ≤ ⟪axis, centerNormalizedA j⟫)
    (hmove : ∀ j, ‖normalizedA j - centerNormalizedA j‖ ≤ δ)
    (hA_eq : ∀ j, A j = firstVariationVector p (weight j) (direction j)
      (fun i => normalizedExactVertex (symmetryAction g (index j i))))
    (hB_bound : ∀ j, ∑ i, weight j i *
      (‖direction j i‖ *
        ‖normalizedExactVertex (symmetryAction g (index j i))‖) ≤ B j)
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
  obtain ⟨j, hj⟩ := exists_axis_certificate_dominating_remainder_of_cover_perturbation
    centerNormalizedA normalizedA A B c δ |Real.sin a.angle| (1 - Real.cos a.angle)
    (abs_nonneg _) hB hA hcover hmove hratio a.signedAxis a.signedAxis_norm
  apply not_rupertPose_of_symmetry_axisAngle_certificate p g a
    (index j) (weight j) (direction j)
    (hdirection j) (hweight j) (hweight_pos j) (hbalance j) (hsupport j)
  have hremainder :
      (1 - Real.cos a.angle) *
          (∑ i, weight j i *
            (‖direction j i‖ *
              ‖normalizedExactVertex (symmetryAction g (index j i))‖)) ≤
        (1 - Real.cos a.angle) * B j :=
    mul_le_mul_of_nonneg_left (hB_bound j)
      (sub_nonneg.mpr (Real.cos_le_one a.angle))
  rw [axisAngle_weighted_first_identity a p (weight j) (direction j)
    (fun i => normalizedExactVertex (symmetryAction g (index j i)))]
  rw [← hA_eq j]
  exact hremainder.trans hj

end Noperthedron.SnubCube

end
