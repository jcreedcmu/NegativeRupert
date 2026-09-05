module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.InnerProductSpace.PiL2

public import Noperthedron.Basic
public import Noperthedron.Bounding.OpNorm
public import Noperthedron.PoseInterval

public section


namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

/-- [SY25] Lemma 21.

`rotM θ φ` consists of the first two rows of a rotation whose third row is
`vecX θ φ`, so this is Parseval for that rotated orthonormal basis. -/
theorem pythagoras {θ φ : ℝ} (P : Euc(3)) :
    ‖rotM θ φ P‖ ^ 2 = ‖P‖ ^ 2 - ⟪vecX θ φ, P⟫ ^ 2 := by
  set w : ℝ³ := RyL φ (RzL (-θ) P) with hw
  have h1 : rotM θ φ P = reduceL w := by rw [rotM_identity]; rfl
  have h2 : ⟪vecX θ φ, P⟫ = w 2 := by
    rw [vecX_identity,
      show ((RzL θ ∘L RyL (-φ)) !₂[0, 0, 1] : ℝ³) = rot3 2 θ (rot3 1 (-φ) !₂[0, 0, 1]) from rfl,
      Bounding.inner_rot3_left, Bounding.inner_rot3_left, neg_neg,
      show (rot3 1 φ (rot3 2 (-θ) P) : ℝ³) = w from rfl]
    simp [PiLp.inner_apply, Fin.sum_univ_three]
  have h3 : ‖w‖ = ‖P‖ := by rw [hw, Bounding.Ry_preserves_norm, Bounding.Rz_preserves_norm]
  have h4 : ‖reduceL w‖ ^ 2 + w 2 ^ 2 = ‖w‖ ^ 2 := by
    have e : reduceL w = !₂[w 1, -(w 0)] := by
      ext i; fin_cases i <;> simp [reduceL, Matrix.vecHead, Matrix.vecTail]
    rw [e, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Real.norm_eq_abs, sq_abs]
    ring
  rw [h1, h2, ← h3]
  linarith [h4]

/-- A vector killed by the projection is its component along the viewing direction. -/
theorem eq_smul_vecX_of_rotM_eq_zero {θ φ : ℝ} {P : Euc(3)} (hP : rotM θ φ P = 0) :
    P = ⟪vecX θ φ, P⟫ • vecX θ φ := by
  have hnorm := pythagoras (θ := θ) (φ := φ) P
  rw [hP, norm_zero, zero_pow (by norm_num)] at hnorm
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hsq := norm_sub_sq_real P (⟪vecX θ φ, P⟫ • vecX θ φ)
  rw [norm_smul, Bounding.vecX_norm_one, mul_one, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right, real_inner_comm (vecX θ φ) P] at hsq
  apply sq_eq_zero_iff.mp
  calc
    ‖P - ⟪vecX θ φ, P⟫ • vecX θ φ‖ ^ 2 =
        ‖P‖ ^ 2 - 2 * (⟪vecX θ φ, P⟫ * ⟪vecX θ φ, P⟫) + ⟪vecX θ φ, P⟫ ^ 2 := hsq
    _ = ‖P‖ ^ 2 - ⟪vecX θ φ, P⟫ ^ 2 := by ring
    _ = 0 := hnorm.symm

/-- [SY25] Lemma 24 -/
theorem abs_sub_inner_bars_le {m n : ℕ} (A B A_ B_ : Euc(m) →L[ℝ] Euc(n)) (P₁ P₂ : Euc(m)) :
    |⟪A P₁, B P₂⟫ - ⟪A_ P₁, B_ P₂⟫| ≤
    ‖P₁‖ * ‖P₂‖ * (‖A - A_‖ * ‖B_‖ + ‖A_‖ * ‖B - B_‖ + ‖A - A_‖ * ‖B - B_‖) := by
  have h₁ := calc
    ⟪A P₁, B P₂⟫ = ⟪(A - A_) P₁ + A_ P₁, (B - B_) P₂ + B_ P₂⟫ := by simp
               _ = ⟪(A - A_) P₁, B_ P₂⟫ + ⟪A_ P₁, (B - B_) P₂⟫ +
                   ⟪(A - A_) P₁, (B - B_) P₂⟫ + ⟪A_ P₁, B_ P₂⟫ :=
                 by simp only [inner_add_left, inner_add_right]
                    ring
  -- Then the inequality follows from the triangle inequality,
  -- the Cauchy-Schwarz inequality and the submultiplicativity of ‖.‖:
  calc
    _ ≤ |⟪(A - A_) P₁, B_ P₂⟫| + |⟪A_ P₁, (B - B_) P₂⟫| + |⟪(A - A_) P₁, (B - B_) P₂⟫| :=
      by rw [h₁]; ring_nf; exact abs_add_three _ _ _
    _ ≤ ‖(A - A_) P₁‖ * ‖B_ P₂‖ + ‖A_ P₁‖ * ‖(B - B_) P₂‖ + ‖(A - A_) P₁‖ * ‖(B - B_) P₂‖ :=
      by simp only [←Real.norm_eq_abs]
         grw [norm_inner_le_norm, norm_inner_le_norm, norm_inner_le_norm]
    _ ≤ _ :=
      by grw [ContinuousLinearMap.le_opNorm, ContinuousLinearMap.le_opNorm,
              ContinuousLinearMap.le_opNorm, ContinuousLinearMap.le_opNorm]
         linarith only

/-- [SY25] Lemma 25 -/
theorem abs_sub_inner_le {m n : ℕ} (A B : Euc(m) →L[ℝ] Euc(n)) (P₁ P₂ : Euc(m)) :
    |⟪A P₁, A P₂⟫ - ⟪B P₁, B P₂⟫| ≤ ‖P₁‖ * ‖P₂‖ * ‖A - B‖ * (‖A‖ + ‖B‖ + ‖A - B‖) := by
  -- Add and subtract the mixed inner product. This already gives the sharper
  -- bound with `‖A‖ + ‖B‖`; the final step recovers the stated bound.
  have hsplit : ⟪A P₁, A P₂⟫ - ⟪B P₁, B P₂⟫ =
      ⟪(A - B) P₁, A P₂⟫ + ⟪B P₁, (A - B) P₂⟫ := by
    simp only [sub_apply, inner_sub_left, inner_sub_right]
    ring
  calc
    _ ≤ |⟪(A - B) P₁, A P₂⟫| + |⟪B P₁, (A - B) P₂⟫| := by
      rw [hsplit]; exact abs_add_le _ _
    _ ≤ ‖(A - B) P₁‖ * ‖A P₂‖ + ‖B P₁‖ * ‖(A - B) P₂‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (‖A - B‖ * ‖P₁‖) * (‖A‖ * ‖P₂‖) +
        (‖B‖ * ‖P₁‖) * (‖A - B‖ * ‖P₂‖) := by
      gcongr <;> exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖P₁‖ * ‖P₂‖ * ‖A - B‖ * (‖A‖ + ‖B‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _))
      (by positivity)

end Local
end
