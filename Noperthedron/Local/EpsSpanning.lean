module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.InnerProductSpace.PiL2

public import Noperthedron.Basic
public import Noperthedron.PoseInterval
public import Noperthedron.Bounding
public import Noperthedron.Local.Prelims
public import Noperthedron.Local.OriginInTriangle
public import Noperthedron.Local.Spanp
public import Noperthedron.Global.SpanProducts

@[expose] public section


namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

def Triangle : Type := Fin 3 → ℝ³

/--
[SY25] Definition 34.
We define "congruent" to mean "there exists a linear isometry". Note that this is
stronger than "there exists an *affine* isometry", which might be the definition
you usually think of.
-/
def Triangle.Congruent (P Q : Triangle) : Prop :=
  ∃ L : Euc(3) →ₗᵢ[ℝ] Euc(3), ∀ i, P i = L (Q i)

/-- [SY25] Definition 27. Note that the "+ 1" at the type Fin 3 wraps. -/
structure Triangle.Spanning (P : Triangle) (θ φ ε : ℝ) : Prop where
  pos : 0 < ε
  lt : ∀ i : Fin 3, 2 * ε * (√2 + ε) < ⟪rotR (π / 2) (rotM θ φ (P i)), rotM θ φ (P (i + 1))⟫

lemma spanning_neg {P : Triangle} {θ φ ε : ℝ} (e : ℕ) (h : P.Spanning θ φ ε) :
    Triangle.Spanning (fun i ↦ (-1:ℝ)^e • P i) θ φ ε := by
  obtain ⟨pos, lt⟩ := h
  refine ⟨pos, ?_⟩
  intro i
  specialize lt i
  simp only [map_smul]
  rw [real_inner_smul_right, real_inner_smul_left, ←mul_assoc ((-1:ℝ)^e)]
  have h₁ : (-1:ℝ) ^ e * (-1:ℝ) ^ e = 1 := by
    rw [←pow_add, ←mul_two, mul_comm]
    rw [pow_mul]
    norm_num
  rw [h₁, one_mul]
  exact lt

lemma triangle_ineq_aux
    {d x y : ℝ} (hd : 0 < d) (hy : d < y) (hx : |x - y| ≤ d) : 0 < x := by
  grind

/-- The core of [SY25] Lemma 28: once the three consecutive spanning products
are positive at the pose itself, `vecX` lies in the positive span of the
triangle (via [SY25] Lemma 26). -/
theorem spanp_of_pos {θ φ : ℝ} (P : Triangle)
    (h₁ : ∀ i : Fin 3, 0 < ⟪rotR (π/2) (rotM θ φ (P i)), rotM θ φ (P (i + 1))⟫)
    (hX : ∀ i, 0 < ⟪vecX θ φ, P i⟫) :
    vecX θ φ ∈ Spanp P := by
  -- apply lemma 26
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ := Local.origin_in_triangle (h₁ 0) (h₁ 1) (h₁ 2)
  let S := a • (P 0) + b • (P 1) + c • (P 2)
  -- The positive combination has zero projection, hence equals its component along vecX.
  have hS : rotM θ φ S = 0 := by simpa [S]
  let lam := ⟪vecX θ φ, S⟫
  have hlam : S = lam • vecX θ φ := eq_smul_vecX_of_rotM_eq_zero hS
  have h₄ : 0 < lam := by
    dsimp [lam, S]
    simp only [inner_add_right, real_inner_smul_right]
    positivity [hX 0, hX 1, hX 2]
  have h₅ : vecX θ φ = lam⁻¹ • S := by
    rw [hlam, smul_smul, inv_eq_one_div, one_div_mul_cancel h₄.ne.symm]
    simp
  simp only [Spanp, Set.mem_ofPred_eq]
  use ![lam⁻¹ * a, lam⁻¹ * b, lam⁻¹ * c]
  constructor
  · intro i
    fin_cases i <;> simp <;> positivity
  · simp [Fin.sum_univ_three, h₅, S, smul_smul]

/-- [SY25] Lemma 28 -/
theorem vecX_spanning {ε θ θ_ φ φ_ : ℝ} (P : Triangle)
    (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε)
    (hSpanning: P.Spanning θ_ φ_ ε)
    (hP : ∀ i, ‖P i‖ ≤ 1)
    (hX : ∀ i, 0 < ⟪vecX θ φ, P i⟫) :
    vecX θ φ ∈ Spanp P := by
  obtain ⟨hε, hlt⟩ := hSpanning
  refine spanp_of_pos P ?_ hX
  intro i
  -- lemma 24 -> Local.abs_sub_inner_bars_le
  have h₂ :=
    Local.abs_sub_inner_bars_le
      (rotR (π/2) ∘L rotM θ φ) (rotM θ φ)
      (rotR (π/2) ∘L rotM θ_ φ_) (rotM θ_ φ_)
      (P i) (P (i + 1))

  specialize hlt i

  rw [←ContinuousLinearMap.comp_sub] at h₂
  grw [hP, hP] at h₂
  grw [ContinuousLinearMap.opNorm_comp_le (rotR (π / 2)) (rotM θ_ φ_)] at h₂
  grw [ContinuousLinearMap.opNorm_comp_le] at h₂
  simp only [Bounding.rotR_norm_one, Bounding.rotM_norm_one, mul_one, one_mul] at h₂

  -- lemma 13 -> Bounding.norm_M_sub_lt
  have h₃ := Bounding.norm_M_sub_lt hε hθ hφ
  grw [h₃.le, h₃.le] at h₂
  have h₄ : √2 * ε + √2 * ε + √2 * ε * (√2 * ε) = 2 * ε * (√2 + ε) := by
    rw [show √2 * ε * (√2 * ε) = √2^2 * ε^2 by ring]
    simp only [Nat.ofNat_nonneg, Real.sq_sqrt]
    ring
  rw [h₄] at h₂
  clear h₃ h₄
  have hd : 0 < 2 * ε * (√2 + ε) := by positivity
  exact triangle_ineq_aux hd hlt h₂

/-- **Second-order spanning condition**: each consecutive spanning product at
the center exceeds its own second-order variation budget over the per-axis
box `(εθ, εφ)`. Replaces the Lipschitz margin `2ε(√2+ε)` of
`Triangle.Spanning`. -/
def Triangle.Spanning₂ (P : Triangle) (θ_ φ_ εθ εφ : ℝ) : Prop :=
  ∀ i : Fin 3, GlobalTheorem.ΔprodMM (rotR (π/2)) (P i) (P (i + 1)) εθ εφ θ_ φ_
    < ⟪rotR (π/2) (rotM θ_ φ_ (P i)), rotM θ_ φ_ (P (i + 1))⟫

lemma spanning₂_neg {P : Triangle} {θ_ φ_ εθ εφ : ℝ} (e : ℕ)
    (h : P.Spanning₂ θ_ φ_ εθ εφ) :
    Triangle.Spanning₂ (fun i ↦ (-1 : ℝ)^e • P i) θ_ φ_ εθ εφ := by
  intro i
  have hlt := h i
  simpa [Triangle.Spanning₂, GlobalTheorem.ΔprodMM_neg_one_pow_smul, map_smul,
    GlobalTheorem.inner_neg_one_pow_smul_smul] using hlt

/-- [SY25] Lemma 28, second-order version: no norm hypothesis on `P` is
needed since the budget carries `‖P i‖` explicitly. -/
theorem vecX_spanning₂ {εθ εφ θ θ_ φ φ_ : ℝ} (P : Triangle)
    (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    (hθ : |θ - θ_| ≤ εθ) (hφ : |φ - φ_| ≤ εφ)
    (hSpanning : P.Spanning₂ θ_ φ_ εθ εφ)
    (hX : ∀ i, 0 < ⟪vecX θ φ, P i⟫) :
    vecX θ φ ∈ Spanp P := by
  refine spanp_of_pos P ?_ hX
  intro i
  have h₂ := GlobalTheorem.inner_prod_MM_sub_le (rotR (π/2))
    (le_of_eq (Bounding.rotR_norm_one _)) (v := P i) (w := P (i + 1)) hεθ hεφ hθ hφ
  have hlt := hSpanning i
  have := abs_le.mp h₂
  linarith [this.1]

end Local
end
