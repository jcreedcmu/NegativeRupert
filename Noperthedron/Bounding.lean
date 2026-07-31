module

public import Noperthedron.Basic
public import Noperthedron.Bounding.SmallConsecutiveRotations
public import Noperthedron.Bounding.OpNorm

public section


open scoped RealInnerProductSpace Real

namespace Bounding

lemma RyL_neg_compose_RyL {α : ℝ} : RyL (-α) ∘L RyL α = ContinuousLinearMap.id _ _ := by
  have h₄ : (RyL (-α)).comp (RyL α) = RyC (-α + α) := by
    simp only [← RyC_coe]
    rw [←ContinuousLinearMap.mul_def, ←AddChar.map_add_eq_mul]
  rw [h₄]
  simp [ContinuousLinearMap.one_def]

lemma RzL_neg_compose_RzL {α : ℝ} : RzL (-α) ∘L RzL α = ContinuousLinearMap.id _ _ := by
  have h₄ : (RzL (-α)).comp (RzL α) = RzC (-α + α) := by
    simp only [← RzC_coe]
    rw [←ContinuousLinearMap.mul_def, ←AddChar.map_add_eq_mul]
  rw [h₄]
  simp [ContinuousLinearMap.one_def]

/--
First half of [SY25] Lemma 13.
-/
theorem norm_M_sub_lt {ε θ θ_ φ φ_ : ℝ} (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    ‖rotM θ φ - rotM θ_ φ_‖ < √2 * ε := by
  by_cases h₁ : θ = θ_ ∧ φ = φ_
  · obtain ⟨hθ₁, hφ₁⟩ := h₁
    simp [hθ₁, hφ₁, hε]
  simp only [rotM_identity, ←ContinuousLinearMap.comp_sub]
  grw [ContinuousLinearMap.opNorm_comp_le, reduceL_norm, one_mul]
  rw [←Ry_preserves_op_norm (-φ), ContinuousLinearMap.comp_sub]
  rw [←Rz_comp_right_preserves_op_norm θ, ContinuousLinearMap.sub_comp]
  have h₂ : ((RyL (-φ)).comp ((RyL φ).comp (RzL (-θ)))).comp (RzL θ) =
      (RyL (-φ) ∘L (RyL φ)) ∘L (RzL (-θ) ∘L (RzL θ)) := by
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
  rw [h₂, RyL_neg_compose_RyL, RzL_neg_compose_RzL, ContinuousLinearMap.id_comp,
      ←ContinuousLinearMap.one_def]
  have h₆ : ((RyL (-φ)).comp ((RyL φ_).comp (RzL (-θ_)))).comp (RzL θ) =
      (RyL (-φ) ∘L (RyL φ_)) ∘L (RzL (-θ_) ∘L (RzL θ)) := by
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
  rw [h₆]
  clear h₂ h₆
  simp only [←RyC_coe, ←RzC_coe]
  rw [← ContinuousLinearMap.mul_def (RzC (-θ_)) (RzC θ)]
  rw [← ContinuousLinearMap.mul_def (RyC (-φ)) (RyC φ_)]
  simp only [← AddChar.map_add_eq_mul]
  rw [norm_sub_rev]
  have h₇ := lemma12 (d := 1) (d' := 2) (α := -φ + φ_) (β := -θ_ + θ) (by decide)
  have h₇' := lemma12_equality_iff (d := 1) (d' := 2) (α := -φ + φ_) (β := -θ_ + θ) (by decide)
  have h11 : ¬ (-φ + φ_ = 0 ∧ -θ_ + θ = 0) := by grind
  replace h₇' := h₇'.not.mpr h11
  replace h₇ := lt_of_le_of_ne h₇ h₇'
  simp only [rot3] at h₇
  suffices √((-φ + φ_) ^ 2 + (-θ_ + θ) ^ 2) ≤ √2 * ε by linarith
  rw [←sq_abs (-φ + _), ←sq_abs (-θ_ + _)]
  suffices (√(|-φ + φ_| ^ 2 + |-θ_ + θ| ^ 2)) ^ 2 ≤ (√2 * ε) ^ 2 by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp this
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity), two_mul]
  rw [show |-θ_ + θ| = |θ - θ_| by grind, show |-φ + φ_| = |φ - φ_| by grind]
  gcongr

/--
Second half of [SY25] Lemma 13.
-/
theorem norm_X_sub_lt {ε θ θ_ φ φ_ : ℝ} (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    ‖vecX θ φ - vecX θ_ φ_‖ < √2 * ε := by
  by_cases h₁ : θ = θ_ ∧ φ = φ_
  · have h₂ : ‖vecX θ φ - vecX θ_ φ_‖ = 0 := by
      obtain ⟨hθ₁, hφ₁⟩ := h₁
      simp [hθ₁, hφ₁]
    rw [h₂]
    positivity
  simp only [vecX_identity, ← sub_apply]
  grw [ContinuousLinearMap.le_opNorm]
  have h₉₉ : ‖!₂[0, 0, (1:ℝ)]‖ = 1 := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  rw [h₉₉, mul_one]; clear h₉₉
  rw [←Rz_preserves_op_norm (-θ), ContinuousLinearMap.comp_sub]
  rw [←Ry_comp_right_preserves_op_norm φ, ContinuousLinearMap.sub_comp]
  have h₂ : ((RzL (-θ)).comp ((RzL θ).comp (RyL (-φ)))).comp (RyL φ) =
      (RzL (-θ) ∘L (RzL θ)) ∘L (RyL (-φ) ∘L (RyL φ)) := by
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
  rw [h₂, RyL_neg_compose_RyL, RzL_neg_compose_RzL, ContinuousLinearMap.id_comp,
      ←ContinuousLinearMap.one_def]
  have h₆ : ((RzL (-θ)).comp ((RzL θ_).comp (RyL (-φ_)))).comp (RyL φ) =
      (RzL (-θ) ∘L (RzL θ_)) ∘L (RyL (-φ_) ∘L (RyL φ)) := by
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
  rw [h₆]
  clear h₂ h₆
  simp only [←RyC_coe, ← RzC_coe]
  rw [show (RyC (-φ_)).comp (RyC φ) = (RyC (-φ_)) * (RyC φ) from rfl]
  rw [show (RzC (-θ)).comp (RzC θ_) = (RzC (-θ)) * (RzC θ_) from rfl]
  simp only [←AddChar.map_add_eq_mul]
  rw [norm_sub_rev]
  have h₇ := lemma12 (d := 2) (d' := 1) (α := -θ + θ_) (β := -φ_ + φ) (by decide)
  have h₇' := lemma12_equality_iff (d := 2) (d' := 1) (α := -θ + θ_) (β := -φ_ + φ) (by decide)
  have h11 : ¬ (-θ + θ_ = 0 ∧ -φ_ + φ = 0) := by grind
  replace h₇' := h₇'.not.mpr h11
  replace h₇ := lt_of_le_of_ne h₇ h₇'
  simp only [rot3] at h₇
  suffices √((-θ + θ_) ^ 2 + (-φ_ + φ) ^ 2) ≤ √2 * ε by linarith
  rw [←sq_abs (-θ + _), ←sq_abs (-φ_ + _)]
  suffices (√(|-θ + θ_| ^ 2 + |-φ_ + φ| ^ 2)) ^ 2 ≤ (√2 * ε) ^ 2 by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp this
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity), two_mul]
  rw [show |-φ_ + φ| = |φ - φ_| by grind, show |-θ + θ_| = |θ - θ_| by grind]
  gcongr

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
  have h₃ : ((RzL (-α_)).comp ((RzL α).comp ((RyL φ).comp (RzL (-θ))))).comp (RzL θ) =
      RzL (-α_) ∘L RzL α ∘L RyL φ ∘L RzL (-θ) ∘L RzL θ := by
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
    rw [←ContinuousLinearMap.comp_assoc]
  have h₄ : ((RzL (-α_)).comp ((RzL α_).comp ((RyL φ_).comp (RzL (-θ_))))).comp (RzL θ) =
        (RzL (-α_) ∘L RzL α_) ∘L RyL φ_ ∘L RzL (-θ_) ∘L RzL θ
       := by
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
    rw [←ContinuousLinearMap.comp_assoc, ←ContinuousLinearMap.comp_assoc]
  rw [h₃, h₄, RzL_neg_compose_RzL, RzL_neg_compose_RzL]
  clear h₃ h₄
  simp only [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
  have h₅ : ((RzL (-θ_)).comp (RzL θ)) = RzL (θ - θ_) := by
    rw [←RzC_coe]
    rw [←ContinuousLinearMap.mul_def, ←AddChar.map_add_eq_mul]
    rw [show -θ_ + θ = θ - θ_ by ring]
  rw [h₅]; clear h₅
  rw [←ContinuousLinearMap.comp_assoc]
  have h₅ : ((RzL (-α_)).comp (RzL α)) = RzL (α - α_) := by
    rw [show RzL = RzC from rfl]
    rw [←ContinuousLinearMap.mul_def, ←AddChar.map_add_eq_mul]
    ring_nf
  rw [h₅]; clear h₅
  by_cases h₁ : θ = θ_ ∧ α = α_
  · rw [←RzC_coe]
    simp only [h₁, sub_self, AddChar.map_zero_eq_one]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    rw [norm_RyL_sub_RyL_eq]
    have := norm_rotR_sub_rotR_lt hε hφ
    have h₅ : (1:ℝ) ≤ √5 := by norm_num
    grw [←h₅]
    rw [one_mul]
    exact this
  let Φ := (φ * |θ - θ_| + φ_ * |α - α_|) / (|α - α_| + |θ - θ_|)
  have h₆ : ‖(RzL (α - α_)).comp (RyL φ) - RyL Φ‖ + ‖ RyL Φ - (RyL φ_).comp (RzL (θ - θ_))‖
      ≥ ‖(RzL (α - α_)).comp (RyL φ) - (RyL φ_).comp (RzL (θ - θ_))‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  grw [←h₆]; clear h₆
  nth_rw 1 [←Ry_comp_right_preserves_op_norm (-Φ)]
  nth_rw 2 [←Ry_preserves_op_norm (-Φ)]
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, RyL_neg_compose_RyL]
  have h₇ := RyL_neg_compose_RyL (α := -Φ)
  rw [neg_neg] at h₇
  rw [h₇]; clear h₇
  simp only [←ContinuousLinearMap.one_def]
  rw [norm_sub_rev 1]
  rw [ContinuousLinearMap.comp_assoc]
  have h₉ : ((RyL φ).comp (RyL (-Φ))) = RyL (φ - Φ) := by
    rw [←RyC_coe]
    rw [←ContinuousLinearMap.mul_def, ←AddChar.map_add_eq_mul, ←Ring.sub_eq_add_neg]
  rw [h₉]; clear h₉
  rw [←ContinuousLinearMap.comp_assoc]
  have h₉ : ((RyL (-Φ)).comp (RyL φ_)) = RyL (φ_ - Φ) := by
    rw [←RyC_coe]
    rw [←ContinuousLinearMap.mul_def, ←AddChar.map_add_eq_mul]
    ring_nf
  rw [h₉]; clear h₉
  rw [←RyC_coe, ←RzC_coe]
  have h₁₀ : ‖(RzC (α - α_)).comp (RyC (φ - Φ)) - 1‖ + ‖(RyC (φ_ - Φ)).comp (RzC (θ - θ_)) - 1‖
      < √((α - α_) ^ 2 + (φ - Φ) ^ 2) + √((φ_ - Φ) ^ 2 + (θ - θ_) ^ 2) := by
    have h₈ := lemma12 (d := 2) (d' := 1) (α := α - α_) (β := φ - Φ) (by decide)
    have h₉ := lemma12 (d := 1) (d' := 2) (α := φ_ - Φ) (β := θ - θ_) (by decide)
    have h₈' := lemma12_equality_iff (d := 2) (d' := 1) (α := α - α_) (β := φ - Φ) (by decide)
    have h₉':= lemma12_equality_iff (d := 1) (d' := 2) (α := φ_ - Φ) (β := θ - θ_) (by decide)
    simp only [rot3] at h₈ h₉ h₈' h₉'
    obtain h₁ | h₁ : θ ≠ θ_ ∨ α ≠ α_ := Decidable.not_and_iff_or_not.mp h₁
    · have h₁₂ : ¬ (φ_ - Φ = 0 ∧ θ - θ_ = 0) := by
        push Not
        intro _
        exact sub_ne_zero_of_ne h₁
      have := lt_of_le_of_ne h₉ (h₉'.not.mpr h₁₂)
      linarith
    · have h₁₂ : ¬(α - α_ = 0 ∧ φ - Φ = 0) := by
        push Not
        intro H
        have : α = α_ := by linarith only [H]
        contradiction
      have := lt_of_le_of_ne h₈ (h₈'.not.mpr h₁₂)
      linarith
  suffices √((α - α_) ^ 2 + (φ - Φ) ^ 2) + √((φ_ - Φ) ^ 2 + (θ - θ_) ^ 2) ≤ √5 * ε by
    linarith only [this, h₁₀]
  have h₁₁ : √((α - α_) ^ 2 + (φ - Φ) ^ 2) + √((φ_ - Φ) ^ 2 + (θ - θ_) ^ 2) =
      √((|α - α_| + |θ - θ_|)^2 + |φ - φ_|^2) := by
    have h₁₄ : 0 < |α - α_| + |θ - θ_| := by
      obtain h₁ | h₁ : θ ≠ θ_ ∨ α ≠ α_ := Decidable.not_and_iff_or_not.mp h₁ <;>
        have := abs_sub_pos.mpr h₁ <;> positivity
    have h_subst : φ - Φ = (φ - φ_) * |α - α_| / (|α - α_| + |θ - θ_|) ∧
                   φ_ - Φ = (φ_ - φ) * |θ - θ_| / (|α - α_| + |θ - θ_|) := by grind
    rw [h_subst.1, h_subst.2]; clear h_subst
    have h₁₅ : (α - α_) ^ 2 + ((φ - φ_) * |α - α_| / (|α - α_| + |θ - θ_|)) ^ 2 =
               ((α - α_) ^ 2 * (|α - α_| + |θ - θ_|) ^ 2 + (φ - φ_) ^ 2 * |α - α_| ^ 2) /
                (|α - α_| + |θ - θ_|) ^ 2 := by field_simp
    have h₁₆: ((φ_ - φ) * |θ - θ_| / (|α - α_| + |θ - θ_|)) ^ 2 + (θ - θ_) ^ 2 =
              (|θ - θ_| ^ 2 * (φ_ - φ) ^ 2 + (θ - θ_) ^ 2 * (|α - α_| + |θ - θ_|) ^ 2) /
               (|α - α_| + |θ - θ_|) ^ 2 := by field_simp
    rw [h₁₅, h₁₆]; clear h₁₅ h₁₆
    rw [Real.sqrt_div (by positivity), Real.sqrt_div (by positivity)]
    rw [← add_div, div_eq_iff (by simp [h₁₄.le, h₁₄.ne'])]
    simp only [sq_abs, h₁₄.le, Real.sqrt_sq]
    rw [show (α - α_) ^ 2 * (|α - α_| + |θ - θ_|) ^ 2 + (φ - φ_) ^ 2 * (α - α_) ^ 2 =
             ((|α - α_| + |θ - θ_|) ^ 2 + (φ - φ_) ^ 2) * (α - α_) ^ 2 by ring,
        show (θ - θ_) ^ 2 * (φ_ - φ) ^ 2 + (θ - θ_) ^ 2 * (|α - α_| + |θ - θ_|) ^ 2 =
             ((|α - α_| + |θ - θ_|) ^ 2 + (φ - φ_) ^ 2 ) * (θ - θ_) ^ 2 by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
    ring_nf
  rw [h₁₁]; clear h₁₁
  grw [hθ, hφ, hα]
  rw [show (ε + ε) ^ 2 + ε ^ 2 = 5 * ε ^ 2 by ring]
  simp [Real.sqrt_sq hε.le]

end Bounding
end
