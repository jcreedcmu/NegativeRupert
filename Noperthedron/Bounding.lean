module

public import Noperthedron.Basic
public import Noperthedron.Bounding.SmallConsecutiveRotations
public import Noperthedron.Bounding.OpNorm

public section


open scoped RealInnerProductSpace Real

namespace Bounding

/-- Cancel the common rotations before comparing the two angle changes. -/
lemma norm_rot3_comp_sub_eq {d d' : Fin 3} {α β α_ β_ : ℝ} :
    ‖rot3 d α ∘L rot3 d' β - rot3 d α_ ∘L rot3 d' β_‖ =
      ‖rot3 d (α - α_) ∘L rot3 d' (β - β_) - 1‖ := by
  rw [← rot3_preserves_op_norm (d := d) (-α_), ContinuousLinearMap.comp_sub]
  rw [← rot3_comp_right_preserves_op_norm (d := d') (-β_), ContinuousLinearMap.sub_comp]
  simp only [ContinuousLinearMap.comp_assoc]
  simp only [← ContinuousLinearMap.mul_def, ← AddChar.map_add_eq_mul]
  simp only [← mul_assoc, ← AddChar.map_add_eq_mul]
  simp [sub_eq_add_neg, add_comm]

/-- Two rotations about distinct axes vary by less than the Euclidean norm of
the positive bounds on their angle changes. -/
lemma norm_rot3_comp_sub_lt {d d' : Fin 3} {α β α_ β_ εα εβ : ℝ}
    (hdd : d ≠ d') (hεα : 0 < εα) (hεβ : 0 < εβ)
    (hα : |α - α_| ≤ εα) (hβ : |β - β_| ≤ εβ) :
    ‖rot3 d α ∘L rot3 d' β - rot3 d α_ ∘L rot3 d' β_‖ < √(εα^2 + εβ^2) := by
  rw [norm_rot3_comp_sub_eq]
  by_cases hzero : α - α_ = 0 ∧ β - β_ = 0
  · simp only [hzero.1, hzero.2, AddChar.map_zero_eq_one,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, sub_self, norm_zero]
    positivity
  · have hstrict := lt_of_le_of_ne (lemma12 hdd) ((lemma12_equality_iff hdd).not.mpr hzero)
    refine hstrict.trans_le ?_
    apply Real.sqrt_le_sqrt
    rw [← sq_abs (α - α_), ← sq_abs (β - β_)]
    gcongr

/-- First half of [SY25] Lemma 13. -/
theorem norm_M_sub_lt {ε θ θ_ φ φ_ : ℝ} (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    ‖rotM θ φ - rotM θ_ φ_‖ < √2 * ε := by
  simp only [rotM_identity, ← ContinuousLinearMap.comp_sub]
  grw [ContinuousLinearMap.opNorm_comp_le, reduceL_norm, one_mul]
  have h := norm_rot3_comp_sub_lt (d := 1) (d' := 2) (α := φ) (β := -θ)
    (α_ := φ_) (β_ := -θ_) (by decide) hε hε hφ (by rw [neg_sub_neg, abs_sub_comm]; exact hθ)
  simpa [rot3, RyC_coe, RzC_coe, show ε^2 + ε^2 = 2 * ε^2 by ring,
    Real.sqrt_mul, Real.sqrt_sq hε.le] using h

/-- Second half of [SY25] Lemma 13. -/
theorem norm_X_sub_lt {ε θ θ_ φ φ_ : ℝ} (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    ‖vecX θ φ - vecX θ_ φ_‖ < √2 * ε := by
  simp only [vecX_identity, ← sub_apply]
  grw [ContinuousLinearMap.le_opNorm]
  have he : ‖!₂[0, 0, (1 : ℝ)]‖ = 1 := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  rw [he, mul_one]
  have h := norm_rot3_comp_sub_lt (d := 2) (d' := 1) (α := θ) (β := -φ)
    (α_ := θ_) (β_ := -φ_) (by decide) hε hε hθ (by rw [neg_sub_neg, abs_sub_comm]; exact hφ)
  simpa [rot3, RyC_coe, RzC_coe, show ε^2 + ε^2 = 2 * ε^2 by ring,
    Real.sqrt_mul, Real.sqrt_sq hε.le] using h

/--
[SY25] Lemma 14
-/
theorem XPgt0 {P : ℝ³} {ε θ θ_ φ φ_ : ℝ} (hP : ‖P‖ ≤ 1)
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hX : √2 * ε < ⟪vecX θ_ φ_, P⟫) :
    0 < ⟪vecX θ φ, P⟫ := by
  have h₁ : ‖⟪vecX θ_ φ_ - vecX θ φ, P⟫‖ ≤ ‖vecX θ_ φ_ - vecX θ φ‖ * ‖P‖ := by
    exact norm_inner_le_norm (vecX θ_ φ_ - vecX θ φ) P
  grw [inner_sub_left, ←Real.le_norm_self] at h₁
  rw [tsub_le_iff_tsub_le] at h₁
  have h₂ := norm_X_sub_lt hε hθ hφ
  grw [← h₁]
  rw [norm_sub_rev] at h₂
  have h₃ : ‖vecX θ_ φ_ - vecX θ φ‖ * ‖P‖ ≤ ‖vecX θ_ φ_ - vecX θ φ‖ * 1 :=
     mul_le_mul_of_nonneg_left hP (norm_nonneg _)
  linarith

/--
[SY25] Lemma 15
-/
theorem norm_M_apply_gt {ε r θ θ_ φ φ_ : ℝ} {P : ℝ³}
    (hP : ‖P‖ ≤ 1) (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hM : r + √2 * ε < ‖rotM θ_ φ_ P‖) : r < ‖rotM θ φ P‖ := by
  have h₁ : ‖rotM θ_ φ_ P‖ - ‖rotM θ φ - rotM θ_ φ_‖ * ‖P‖ ≤ ‖rotM θ φ P‖ := by
    grw [←ContinuousLinearMap.le_opNorm, sub_apply]
    suffices ‖(rotM θ_ φ_) P‖ ≤ ‖(rotM θ φ) P‖ + ‖(rotM θ φ) P - (rotM θ_ φ_) P‖ by linarith
    exact norm_le_insert ((rotM θ φ) P) ((rotM θ_ φ_) P)
  have h₂ := norm_M_sub_lt hε hθ hφ
  grw [hP, mul_one] at h₁
  linarith

/--
[SY25] Lemma 16
-/
theorem norm_RM_sub_RM_le {ε θ θ_ φ φ_ α α_}
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) (hα : |α - α_| ≤ ε) :
    ‖rotprojRM θ φ α - rotprojRM θ_ φ_ α_‖ < √5 * ε := by
  simp only [rotprojRM_identity, ←ContinuousLinearMap.comp_sub]
  grw [ContinuousLinearMap.opNorm_comp_le, reduceL_norm, one_mul]
  rw [←Rz_preserves_op_norm (-α_), ContinuousLinearMap.comp_sub]
  rw [←Rz_comp_right_preserves_op_norm θ, ContinuousLinearMap.sub_comp]
  simp only [← RzC_coe, ← RyC_coe, ← ContinuousLinearMap.mul_def, mul_assoc,
    ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, mul_one]
  simp only [← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
    AddChar.map_zero_eq_one, one_mul, neg_add_eq_sub]
  change ‖RzL (α - α_) ∘L RyL φ - RyL φ_ ∘L RzL (θ - θ_)‖ < √5 * ε
  -- Split the middle angle at its ordinary midpoint. Each half has angle
  -- changes bounded by ε and ε/2, so their bounds add to √5 * ε.
  let Φ := (φ + φ_) / 2
  have hφΦ : |φ - Φ| ≤ ε / 2 := by
    rw [show φ - Φ = (φ - φ_) / 2 by dsimp [Φ]; ring, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right hφ (by positivity)
  have hφ_Φ : |φ_ - Φ| ≤ ε / 2 := by
    rw [show φ_ - Φ = -(φ - φ_) / 2 by dsimp [Φ]; ring, abs_div, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right hφ (by positivity)
  have hroot : √(ε^2 + (ε / 2)^2) = √5 * ε / 2 := by
    rw [show ε^2 + (ε / 2)^2 = 5 * (ε / 2)^2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    ring
  have hleft : ‖RzL (α - α_) ∘L RyL φ - RyL Φ‖ < √5 * ε / 2 := by
    have h := norm_rot3_comp_sub_lt (d := 2) (d' := 1)
      (α := α - α_) (β := φ) (α_ := 0) (β_ := Φ)
      (by decide) hε (show 0 < ε / 2 by positivity) (by simpa using hα) hφΦ
    simpa [rot3, RyC_coe, RzC_coe, ContinuousLinearMap.one_def, hroot] using h
  have hright : ‖RyL Φ - RyL φ_ ∘L RzL (θ - θ_)‖ < √5 * ε / 2 := by
    have h := norm_rot3_comp_sub_lt (d := 1) (d' := 2)
      (α := φ_) (β := θ - θ_) (α_ := Φ) (β_ := 0)
      (by decide) (show 0 < ε / 2 by positivity) hε hφ_Φ (by simpa using hθ)
    simpa [rot3, RyC_coe, RzC_coe, ContinuousLinearMap.one_def, norm_sub_rev,
      add_comm ((ε / 2)^2), hroot] using h
  calc
    _ ≤ ‖RzL (α - α_) ∘L RyL φ - RyL Φ‖ + ‖RyL Φ - RyL φ_ ∘L RzL (θ - θ_)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < √5 * ε / 2 + √5 * ε / 2 := add_lt_add hleft hright
    _ = √5 * ε := by ring

end Bounding
end
