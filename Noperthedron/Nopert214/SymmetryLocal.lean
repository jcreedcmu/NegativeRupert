module

public import Noperthedron.Nopert214.Symmetry
public import Noperthedron.SnubCube.LocalRigidity

@[expose] public section

/-!
# Local rigidity at the five symmetry strata of Nopert #214

This specializes the reindexed balanced-support theorem to the exact
fivefold action.  It is the mathematical layer needed to cover the
Euler-pole equality strata, where equal shadows need not have equal Euler
coordinates.
-/

namespace Noperthedron.Nopert214

open scoped Matrix RealInnerProductSpace
open Noperthedron.BalancedSupport Real

noncomputable def symmetry (g : OrbitIndex) : SO3 :=
  ⟨Rz_mat (2 * π * (g : ℝ) / 5), MatrixPose.Rz_mat_mem_SO3 _⟩

def symmetryAction (g : OrbitIndex) (i : VertexIndex) : VertexIndex :=
  vertexIndex
    ⟨((orbitIndex i).val + g.val) % 5, Nat.mod_lt _ (by omega)⟩
    (seedIndex i)

noncomputable def relativeRotationAtSymmetry
    (p : MatrixPose) (g : OrbitIndex) : SO3 :=
  relativeRotation p * (symmetry g)⁻¹

noncomputable def equalityPose (outer : SO3) (g : OrbitIndex) : MatrixPose where
  innerRot := outer * symmetry g
  outerRot := outer
  innerOffset := 0

@[simp] theorem relativeRotationAtSymmetry_equalityPose
    (outer : SO3) (g : OrbitIndex) :
    relativeRotationAtSymmetry (equalityPose outer g) g = 1 := by
  simp [relativeRotationAtSymmetry, relativeRotation, equalityPose, ← mul_assoc]

/-- Matrix distance to a fivefold equality stratum is bounded by the direct
inner-versus-symmetry mismatch.  This formulation is independent of Euler
coordinates and therefore remains well behaved at their poles. -/
theorem norm_relativeRotationAtSymmetry_one_le_inner_mismatch
    (p : MatrixPose) (g : OrbitIndex) :
    ‖Noperthedron.SnubCube.so3CLM (relativeRotationAtSymmetry p g) - 1‖ ≤
      ‖Noperthedron.SnubCube.so3CLM p.innerRot -
        Noperthedron.SnubCube.so3CLM (p.outerRot * symmetry g)‖ := by
  let q := equalityPose p.outerRot g
  have hrelative := Noperthedron.SnubCube.norm_relativeRotation_sub_le p q
  have hadjusted :
      ‖Noperthedron.SnubCube.so3CLM (relativeRotationAtSymmetry p g) -
          Noperthedron.SnubCube.so3CLM (relativeRotationAtSymmetry q g)‖ ≤
        ‖Noperthedron.SnubCube.so3CLM (relativeRotation p) -
          Noperthedron.SnubCube.so3CLM (relativeRotation q)‖ := by
    rw [relativeRotationAtSymmetry, relativeRotationAtSymmetry,
      Noperthedron.SnubCube.so3CLM_mul,
      Noperthedron.SnubCube.so3CLM_mul,
      ← ContinuousLinearMap.sub_comp]
    calc
      ‖(Noperthedron.SnubCube.so3CLM (relativeRotation p) -
          Noperthedron.SnubCube.so3CLM (relativeRotation q)) ∘L
            Noperthedron.SnubCube.so3CLM (symmetry g)⁻¹‖ ≤
        ‖Noperthedron.SnubCube.so3CLM (relativeRotation p) -
          Noperthedron.SnubCube.so3CLM (relativeRotation q)‖ *
            ‖Noperthedron.SnubCube.so3CLM (symmetry g)⁻¹‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ = _ := by rw [Noperthedron.SnubCube.so3CLM_norm, mul_one]
  have hone : Noperthedron.SnubCube.so3CLM (1 : SO3) = 1 := by
    ext v
    simp [Noperthedron.SnubCube.so3CLM]
  calc
    ‖Noperthedron.SnubCube.so3CLM (relativeRotationAtSymmetry p g) - 1‖ =
        ‖Noperthedron.SnubCube.so3CLM (relativeRotationAtSymmetry p g) -
          Noperthedron.SnubCube.so3CLM (relativeRotationAtSymmetry q g)‖ := by
      rw [relativeRotationAtSymmetry_equalityPose, hone]
    _ ≤ ‖Noperthedron.SnubCube.so3CLM (relativeRotation p) -
          Noperthedron.SnubCube.so3CLM (relativeRotation q)‖ := hadjusted
    _ ≤ ‖Noperthedron.SnubCube.so3CLM p.innerRot -
          Noperthedron.SnubCube.so3CLM q.innerRot‖ +
        ‖Noperthedron.SnubCube.so3CLM p.outerRot -
          Noperthedron.SnubCube.so3CLM q.outerRot‖ := hrelative
    _ = _ := by simp [q, equalityPose]

/-- Division-free local-angle test from a certified matrix mismatch to one
of the exact fivefold equality strata. -/
theorem AxisAngle.ratio_of_inner_mismatch_bound
    (p : MatrixPose) (g : OrbitIndex)
    (a : AxisAngle
      (Noperthedron.SnubCube.so3CLM (relativeRotationAtSymmetry p g)))
    (c r : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hmismatch : ‖Noperthedron.SnubCube.so3CLM p.innerRot -
      Noperthedron.SnubCube.so3CLM (p.outerRot * symmetry g)‖ ≤ r)
    (hsmall : r ^ 2 * (1 + c ^ 2) ≤ 4 * c ^ 2) :
    1 - Real.cos a.angle ≤ |Real.sin a.angle| * c := by
  apply a.ratio_of_norm_bound c r hc hr
  · exact (norm_relativeRotationAtSymmetry_one_le_inner_mismatch p g).trans
      hmismatch
  · exact hsmall

private lemma RzL_apply_add (α β : ℝ) (v : ℝ³) :
    RzL (α + β) v = RzL α (RzL β v) := by
  have h := RzC.map_add_eq_mul α β
  simp only [RzC_coe] at h
  rw [h]
  rfl

private lemma RzL_periodic (x : ℝ) (z : ℤ) :
    RzL (x + z * (2 * π)) = RzL x := by
  simp only [RzL, Rz_mat_add_int_mul_two_pi]

private lemma RzL_nat_mod_five (x : ℕ) :
    RzL (2 * π * ((x % 5 : ℕ) : ℝ) / 5) =
      RzL (2 * π * (x : ℝ) / 5) := by
  have hreal : ((x % 5 : ℕ) : ℝ) + 5 * ((x / 5 : ℕ) : ℝ) = (x : ℝ) := by
    exact_mod_cast Nat.mod_add_div x 5
  have hcast : ((-((x / 5 : ℕ) : ℤ) : ℤ) : ℝ) =
      -((x / 5 : ℕ) : ℝ) := by
    push_cast
    rfl
  rw [show 2 * π * ((x % 5 : ℕ) : ℝ) / 5 =
      2 * π * (x : ℝ) / 5 +
        ((-((x / 5 : ℕ) : ℤ) : ℤ) : ℝ) * (2 * π) by
    rw [hcast]
    linear_combination (2 * π / 5) * hreal,
    RzL_periodic]

theorem symmetry_apply_exactVertex (g : OrbitIndex) (i : VertexIndex) :
    Noperthedron.SnubCube.so3CLM (symmetry g) (exactVertex i) =
      exactVertex (symmetryAction g i) := by
  let k := orbitIndex i
  let s := seedIndex i
  have hi : vertexIndex k s = i := indexEquiv.symm_apply_apply i
  rw [← hi]
  simp only [exactVertex, orbitIndex_vertexIndex, seedIndex_vertexIndex,
    symmetryAction]
  change RzL (2 * π * (g : ℝ) / 5)
      (RzL (2 * π * (k : ℝ) / 5) (toR3 (seedVertex s))) = _
  rw [← RzL_apply_add]
  rw [show 2 * π * (g : ℝ) / 5 + 2 * π * (k : ℝ) / 5 =
      2 * π * ((g.val + k.val : ℕ) : ℝ) / 5 by push_cast; ring]
  rw [← RzL_nat_mod_five (g.val + k.val)]
  simp [Nat.add_comm]

/-- The inner vertex `i` tracks the outer vertex obtained by the exact
fivefold action after the chosen symmetry is removed. -/
theorem outer_relative_at_symmetry_apply
    (p : MatrixPose) (g : OrbitIndex) (i : VertexIndex) :
    outerProjectionLinear p
        ((relativeRotationAtSymmetry p g).val.toEuclideanLin.toContinuousLinearMap
          (exactVertex (symmetryAction g i))) =
      proj_xyL (p.innerRot.val.toEuclideanLin (exactVertex i)) := by
  rw [← symmetry_apply_exactVertex g i]
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
          ((symmetry g).val *ᵥ (exactVertex i).ofLp))) =
    WithLp.toLp 2 (p.innerRot.val *ᵥ (exactVertex i).ofLp)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat]

theorem not_rupertPose_of_symmetry_axisAngle_certificate
    {κ : Type} [Fintype κ] [Nonempty κ]
    (p : MatrixPose) (g : OrbitIndex)
    (a : AxisAngle
      ((relativeRotationAtSymmetry p g).val.toEuclideanLin.toContinuousLinearMap))
    (index : κ → VertexIndex) (weight : κ → ℝ) (direction : κ → ℝ²)
    (hdirection : ∀ i, direction i ≠ 0)
    (hweight : ∀ i, 0 ≤ weight i) (hweight_pos : ∃ i, 0 < weight i)
    (hbalance : ∑ i, weight i • direction i = 0)
    (hsupport : ∀ i j,
      ⟪direction i, outerProjectionLinear p (exactVertex j)⟫ ≤
        ⟪direction i, outerProjectionLinear p
          (exactVertex (symmetryAction g (index i)))⟫)
    (hdominates :
      (1 - Real.cos a.angle) *
          (∑ i, weight i *
            (‖direction i‖ * ‖exactVertex (symmetryAction g (index i))‖)) ≤
        Real.sin a.angle *
          (∑ i, weight i *
            ⟪direction i, outerProjectionLinear p
              (a.first (exactVertex (symmetryAction g (index i))))⟫)) :
    ¬ RupertPose p exactPolyhedron.hull := by
  apply not_rupertPose_of_reindexed_axisAngle_certificate
    exactPolyhedron p a index (fun i => symmetryAction g (index i))
    weight direction hdirection hweight hweight_pos hbalance
  · intro i
    exact (outer_relative_at_symmetry_apply p g (index i)).symm
  · simpa [exactPolyhedron] using hsupport
  · simpa [exactPolyhedron] using hdominates

/-- Four perturbation-stable balanced triples eliminate the unknown local
rotation axis around any of the five symmetry strata. -/
theorem not_rupertPose_of_axisFree_symmetry_certificates_of_cover_perturbation
    {J κ : Type} [Fintype J] [Nonempty J] [Fintype κ] [Nonempty κ]
    (p : MatrixPose) (g : OrbitIndex)
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
    (hA_eq : ∀ j, A j = Noperthedron.SnubCube.firstVariationVector p
      (weight j) (direction j)
      (fun i => exactVertex (symmetryAction g (index j i))))
    (hB_bound : ∀ j, ∑ i, weight j i *
      (‖direction j i‖ * ‖exactVertex (symmetryAction g (index j i))‖) ≤ B j)
    (hratio : 1 - Real.cos a.angle ≤ |Real.sin a.angle| * c)
    (hdirection : ∀ j i, direction j i ≠ 0)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hweight_pos : ∀ j, ∃ i, 0 < weight j i)
    (hbalance : ∀ j, ∑ i, weight j i • direction j i = 0)
    (hsupport : ∀ j i k,
      ⟪direction j i, outerProjectionLinear p (exactVertex k)⟫ ≤
        ⟪direction j i, outerProjectionLinear p
          (exactVertex (symmetryAction g (index j i)))⟫) :
    ¬ RupertPose p exactPolyhedron.hull := by
  obtain ⟨j, hj⟩ :=
    exists_axis_certificate_dominating_remainder_of_cover_perturbation
      centerNormalizedA normalizedA A B c δ |Real.sin a.angle|
      (1 - Real.cos a.angle) (abs_nonneg _) hB hA hcover hmove hratio
      a.signedAxis a.signedAxis_norm
  apply not_rupertPose_of_symmetry_axisAngle_certificate p g a
    (index j) (weight j) (direction j)
    (hdirection j) (hweight j) (hweight_pos j) (hbalance j) (hsupport j)
  have hremainder :
      (1 - Real.cos a.angle) *
          (∑ i, weight j i *
            (‖direction j i‖ * ‖exactVertex (symmetryAction g (index j i))‖)) ≤
        (1 - Real.cos a.angle) * B j :=
    mul_le_mul_of_nonneg_left (hB_bound j)
      (sub_nonneg.mpr (Real.cos_le_one a.angle))
  rw [Noperthedron.SnubCube.axisAngle_weighted_first_identity a p
    (weight j) (direction j)
    (fun i => exactVertex (symmetryAction g (index j i)))]
  rw [← hA_eq j]
  exact hremainder.trans hj

end Noperthedron.Nopert214

end
