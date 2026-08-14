module

public import Noperthedron.Basic
public import Noperthedron.Rupert.Basic
public import Noperthedron.PoseClasses
public import Noperthedron.Util
public import Noperthedron.Bounding.OrthEquivRotz

@[expose] public section


open scoped Matrix

structure MatrixPose : Type where
  innerRot : SO3
  outerRot : SO3
  innerOffset : ℝ²

namespace MatrixPose

def zeroOffset (p : MatrixPose) : MatrixPose :=
  { p with innerOffset := 0 }

/-- Helper: Rz_mat is in SO3 -/
lemma Rz_mat_mem_SO3 (δ : ℝ) : Rz_mat δ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  Bounding.rot3_mat_mem_SO3 2 δ

/-- Rotate a MatrixPose by applying Rz(δ) to both rotations and the offset. -/
noncomputable def rotateBy (p : MatrixPose) (δ : ℝ) : MatrixPose where
  innerRot := ⟨Rz_mat δ * p.innerRot.val, Submonoid.mul_mem _ (Rz_mat_mem_SO3 δ) p.innerRot.property⟩
  outerRot := ⟨Rz_mat δ * p.outerRot.val, Submonoid.mul_mem _ (Rz_mat_mem_SO3 δ) p.outerRot.property⟩
  innerOffset := rotR δ p.innerOffset

noncomputable def innerOffsetPart (p : MatrixPose) : ℝ³ → ℝ³ :=
  AffineEquiv.vaddConst ℝ (inject_xy p.innerOffset)
noncomputable def innerRotPart (p : MatrixPose) : ℝ³ → ℝ³ := p.innerRot.val.toEuclideanLin

end MatrixPose

noncomputable
instance : PoseLike MatrixPose where
  inner p := (AffineEquiv.vaddConst ℝ (inject_xy p.innerOffset)).toAffineMap.comp
      (p.innerRot.val.toEuclideanLin.toAffineMap)
  outer p := p.outerRot.val.toEuclideanLin.toAffineMap

namespace MatrixPose

/--
If we zero out the offset, then the offset part of the inner
action is the identity.
-/
theorem zero_offset_id (p : MatrixPose) (v : ℝ³) : p.zeroOffset.innerOffsetPart v = v := by
  ext i
  fin_cases i <;>
    simp [MatrixPose.innerOffsetPart, inject_xy, MatrixPose.zeroOffset]

@[simp]
theorem zero_offset_elim (p : MatrixPose) :
    ↑(PoseLike.inner p.zeroOffset) = (fun (v : ℝ³) => p.innerRot.val.toEuclideanLin v) := by
  ext1 v
  change p.zeroOffset.innerOffsetPart (p.innerRot.val.toEuclideanLin v) = _
  rw [zero_offset_id]

noncomputable def shift (p : MatrixPose) : ℝ² ≃ₜ ℝ² := Homeomorph.addRight p.innerOffset

/--
We can massage innerShadow p S into the form of the standard Rupert definition
-/
theorem inner_shadow_lemma (p : MatrixPose) (S : Set ℝ³) :
    innerShadow p S = {x | ∃ v ∈ S, p.innerOffset + proj_xyL (p.innerRot.val.toEuclideanLin v) = x} := by
  change ((proj_xyL ∘ (· + inject_xy p.innerOffset)) ∘ p.innerRotPart) '' S =
         (((p.innerOffset + ·) ∘ proj_xyL) ∘ p.innerRotPart) '' S
  suffices h : proj_xyL ∘ (· + inject_xy p.innerOffset) = (p.innerOffset + ·) ∘ proj_xyL by
    rw[h]
  ext1 v
  simp only [Function.comp_apply]
  nth_rw 2 [add_comm]
  rw [proj_xyL_offset_commute p.innerOffset v]

/-- Matrix multiplication yields RzL composition. -/
lemma Rz_mul_toEuclideanLin (δ : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (v : ℝ³) :
    (Rz_mat δ * M).toEuclideanLin v = RzL δ (M.toEuclideanLin v) := by
  simp [Matrix.toLpLin_apply, RzL, Matrix.mulVec_mulVec]

/-- Outer shadow of rotated pose equals rotated outer shadow. -/
theorem outerShadow_rotateBy (p : MatrixPose) (δ : ℝ) (S : Set ℝ³) :
    outerShadow (p.rotateBy δ) S = rotR δ '' outerShadow p S := by
  ext w
  simp only [outerShadow, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨proj_xyL (p.outerRot.val.toEuclideanLin v), ⟨v, hv, rfl⟩, ?_⟩
    simp only [rotateBy, PoseLike.outer, LinearMap.coe_toAffineMap, Rz_mul_toEuclideanLin]
    rw [← ContinuousLinearMap.comp_apply proj_xyL (RzL δ), proj_xyL_comp_RzL]
    rfl
  · rintro ⟨w', ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨v, hv, ?_⟩
    simp only [rotateBy, PoseLike.outer, LinearMap.coe_toAffineMap, Rz_mul_toEuclideanLin]
    rw [← ContinuousLinearMap.comp_apply proj_xyL (RzL δ), proj_xyL_comp_RzL]
    rfl

/-- inject_xy of rotR is RzL of inject_xy. -/
lemma inject_xy_rotR (δ : ℝ) (v : ℝ²) : inject_xy (rotR δ v) = RzL δ (inject_xy v) := by
  ext i
  fin_cases i <;> simp [inject_xy, rotR, rotR_mat, RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Helper to show the inner action of a MatrixPose. -/
lemma inner_apply (p : MatrixPose) (v : ℝ³) :
    PoseLike.inner p v = p.innerRot.val.toEuclideanLin v + inject_xy p.innerOffset := by
  simp only [PoseLike.inner, AffineMap.coe_comp, Function.comp_apply,
    LinearMap.coe_toAffineMap, AffineEquiv.coe_toAffineMap,
    AffineEquiv.vaddConst_apply, vadd_eq_add, add_comm]

/-- Helper to show the inner action of a rotated MatrixPose. -/
lemma rotateBy_inner_apply (p : MatrixPose) (δ : ℝ) (v : ℝ³) :
    PoseLike.inner (p.rotateBy δ) v =
    RzL δ (p.innerRot.val.toEuclideanLin v) + inject_xy (rotR δ p.innerOffset) := by
  simp only [rotateBy, PoseLike.inner, AffineMap.coe_comp, Function.comp_apply,
    LinearMap.coe_toAffineMap, AffineEquiv.coe_toAffineMap,
    AffineEquiv.vaddConst_apply, vadd_eq_add, add_comm]
  congr 1
  exact Rz_mul_toEuclideanLin δ p.innerRot.val v

/-- Inner shadow of rotated pose equals rotated inner shadow. -/
theorem innerShadow_rotateBy (p : MatrixPose) (δ : ℝ) (S : Set ℝ³) :
    innerShadow (p.rotateBy δ) S = rotR δ '' innerShadow p S := by
  ext w
  simp only [innerShadow, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    use proj_xyL (PoseLike.inner p v)
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    rw [rotateBy_inner_apply, inject_xy_rotR, ← map_add (RzL δ)]
    rw [← ContinuousLinearMap.comp_apply proj_xyL (RzL δ), proj_xyL_comp_RzL δ,
        ContinuousLinearMap.comp_apply, inner_apply]
  · rintro ⟨w', ⟨v, hv, rfl⟩, rfl⟩
    use v, hv
    rw [rotateBy_inner_apply, inject_xy_rotR, ← map_add (RzL δ)]
    rw [← ContinuousLinearMap.comp_apply proj_xyL (RzL δ), proj_xyL_comp_RzL δ,
        ContinuousLinearMap.comp_apply, inner_apply]

/-- rotR composition is addition of angles. -/
lemma rotR_comp (α β : ℝ) : (rotR α).comp (rotR β) = rotR (α + β) :=
  (AddChar.map_add_eq_mul rotR α β).symm

/-- rotR as a continuous linear equiv. -/
noncomputable def rotR_equiv (δ : ℝ) : ℝ² ≃L[ℝ] ℝ² where
  toLinearEquiv := {
    toFun := rotR δ
    invFun := rotR (-δ)
    left_inv := fun v => by
      rw [← ContinuousLinearMap.comp_apply, rotR_comp, neg_add_cancel, AddChar.map_zero_eq_one,
          one_apply_eq_self]
    right_inv := fun v => by
      rw [← ContinuousLinearMap.comp_apply, rotR_comp, add_neg_cancel, AddChar.map_zero_eq_one,
          one_apply_eq_self]
    map_add' := fun x y => by simp only [map_add]
    map_smul' := fun r x => by simp only [map_smul, RingHom.id_apply]
  }
  continuous_toFun := (rotR δ).cont
  continuous_invFun := (rotR (-δ)).cont

/-- rotR as a homeomorphism. -/
noncomputable def rotR_homeomorph (δ : ℝ) : ℝ² ≃ₜ ℝ² := (rotR_equiv δ).toHomeomorph

theorem rotR_homeomorph_apply (δ : ℝ) (v : ℝ²) : rotR_homeomorph δ v = rotR δ v := rfl

/-- RupertPose is invariant under rotation by Rz(δ). -/
theorem RupertPose_rotateBy_iff (p : MatrixPose) (δ : ℝ) (S : Set ℝ³) :
    RupertPose (p.rotateBy δ) S ↔ RupertPose p S := by
  simp only [RupertPose, innerShadow_rotateBy, outerShadow_rotateBy,
    show (fun a => rotR δ a) = rotR_homeomorph δ from rfl]
  rw [← Homeomorph.image_closure (rotR_homeomorph δ), ← Homeomorph.image_interior (rotR_homeomorph δ)]
  exact Set.image_subset_image_iff (rotR_homeomorph δ).injective

end MatrixPose

end
