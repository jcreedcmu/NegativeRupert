module

public import Noperthedron.Global.SecondOrderBounds

@[expose] public section


/-!
# Second-order bounds for product quantities `⟪T (M v), M w⟫`

The spanning condition (`T = rotR (π/2)`) and the LMD numerator (`T = id`)
of the local theorem are quadratic in the rotation family.  Their partials
follow the Leibniz rule over the `rotMFam` grid: each derivative of a base
product `⟪T (∂ᵃM v), ∂ᵇM w⟫` is a **sum of two** signed base products, so
iterated partials live in the weighted ∂-closed family `IsProdDerivFam`
(weight = number of leaves, doubling per derivative), giving `|∂³| ≤ 8‖v‖‖w‖`.
Below order 3 no grid fold occurs starting from `(M, M)`, so the first and
second partials are identified sign-free (`ΔprodMM`'s exact charges).
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private lemma coordP_same (i : Fin 2) (y : E 2) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E 2)).ofLp i = y.ofLp i + t := by simp

private lemma coordP_other {i j : Fin 2} (hij : j ≠ i) (y : E 2) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E 2)).ofLp j = y.ofLp j := by simp [hij]

/-- The grid member applied to a fixed vector, as an `E 2`-indexed map. -/
noncomputable def famApp (a b : Fin 3) (P : ℝ³) : E 2 → ℝ² :=
  fun z => rotMFam a b (z.ofLp 0) (z.ofLp 1) P

private lemma differentiable_famApp (a b : Fin 3) (P : ℝ³) :
    Differentiable ℝ (famApp a b P) := fun y => differentiableAt_rotMFam_outer a b P y

/-- Applied fderiv of a grid member in the θ-direction: the `famStep`-indexed
member, negated at the fold. -/
private lemma fderiv_famApp_e0 (a b : Fin 3) (P : ℝ³) (y : E 2) :
    (fderiv ℝ (famApp a b P) y) (EuclideanSpace.single 0 1)
    = cond (famStep a).1 (-(famApp (famStep a).2 b P y)) (famApp (famStep a).2 b P y) := by
  refine fderiv_single_eq (differentiable_famApp a b P y) ?_
  show HasDerivAt (fun t => famApp a b P (y + t • EuclideanSpace.single 0 1)) _ 0
  unfold famApp
  simp only [coordP_same, coordP_other (by decide : (1 : Fin 2) ≠ 0)]
  exact hasDerivAt_comp_add _ _ _ (rotMFam_hasDerivAt_θ a b (y.ofLp 0) (y.ofLp 1) P)

/-- Applied fderiv of a grid member in the φ-direction. -/
private lemma fderiv_famApp_e1 (a b : Fin 3) (P : ℝ³) (y : E 2) :
    (fderiv ℝ (famApp a b P) y) (EuclideanSpace.single 1 1)
    = cond (famStep b).1 (-(famApp a (famStep b).2 P y)) (famApp a (famStep b).2 P y) := by
  refine fderiv_single_eq (differentiable_famApp a b P y) ?_
  show HasDerivAt (fun t => famApp a b P (y + t • EuclideanSpace.single 1 1)) _ 0
  unfold famApp
  simp only [coordP_same, coordP_other (by decide : (0 : Fin 2) ≠ 1)]
  exact hasDerivAt_comp_add _ _ _ (rotMFam_hasDerivAt_φ a b (y.ofLp 0) (y.ofLp 1) P)

/-- Leibniz rule for `nth_partial` of an inner product of two differentiable
vector maps. -/
private lemma nth_partial_inner_prod {F G : E 2 → ℝ²}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (i : Fin 2) (y : E 2) :
    nth_partial i (fun z => ⟪F z, G z⟫) y
    = ⟪(fderiv ℝ F y) (EuclideanSpace.single i 1), G y⟫
      + ⟪F y, (fderiv ℝ G y) (EuclideanSpace.single i 1)⟫ := by
  unfold nth_partial
  rw [fderiv_inner_apply ℝ (hF y) (hG y)]
  ring

/-- The base product function. -/
noncomputable def prodFn (T : ℝ² →L[ℝ] ℝ²) (v w : ℝ³) (a₁ b₁ a₂ b₂ : Fin 3) : E 2 → ℝ :=
  fun y => ⟪T (famApp a₁ b₁ v y), famApp a₂ b₂ w y⟫

private lemma differentiable_T_famApp (T : ℝ² →L[ℝ] ℝ²) (a b : Fin 3) (P : ℝ³) :
    Differentiable ℝ (fun y => T (famApp a b P y)) :=
  T.differentiable.comp (differentiable_famApp a b P)

private lemma fderiv_T_famApp (T : ℝ² →L[ℝ] ℝ²) (a b : Fin 3) (P : ℝ³) (y : E 2)
    (d : E 2) :
    (fderiv ℝ (fun z => T (famApp a b P z)) y) d = T ((fderiv ℝ (famApp a b P) y) d) := by
  rw [show (fun z => T (famApp a b P z)) = T ∘ famApp a b P from rfl,
    fderiv_comp y T.differentiableAt (differentiable_famApp a b P y),
    T.fderiv]
  rfl

/-- Leibniz step of the base product in the θ-direction, with the two signed
`famStep` results. -/
private lemma nth_partial_prodFn_e0 (T : ℝ² →L[ℝ] ℝ²) (v w : ℝ³) (a₁ b₁ a₂ b₂ : Fin 3) :
    nth_partial 0 (prodFn T v w a₁ b₁ a₂ b₂)
    = fun y =>
        (cond (famStep a₁).1 (-(prodFn T v w (famStep a₁).2 b₁ a₂ b₂ y))
          (prodFn T v w (famStep a₁).2 b₁ a₂ b₂ y))
        + (cond (famStep a₂).1 (-(prodFn T v w a₁ b₁ (famStep a₂).2 b₂ y))
          (prodFn T v w a₁ b₁ (famStep a₂).2 b₂ y)) := by
  funext y
  rw [show prodFn T v w a₁ b₁ a₂ b₂ = fun z => ⟪(fun z' => T (famApp a₁ b₁ v z')) z,
      famApp a₂ b₂ w z⟫ from rfl,
    nth_partial_inner_prod (differentiable_T_famApp T a₁ b₁ v)
      (differentiable_famApp a₂ b₂ w) 0 y,
    fderiv_T_famApp, fderiv_famApp_e0, fderiv_famApp_e0]
  rcases famStep a₁ with ⟨c₁, a₁'⟩
  rcases famStep a₂ with ⟨c₂, a₂'⟩
  cases c₁ <;> cases c₂ <;>
    simp [prodFn, inner_neg_left, inner_neg_right, map_neg]

/-- Leibniz step of the base product in the φ-direction. -/
private lemma nth_partial_prodFn_e1 (T : ℝ² →L[ℝ] ℝ²) (v w : ℝ³) (a₁ b₁ a₂ b₂ : Fin 3) :
    nth_partial 1 (prodFn T v w a₁ b₁ a₂ b₂)
    = fun y =>
        (cond (famStep b₁).1 (-(prodFn T v w a₁ (famStep b₁).2 a₂ b₂ y))
          (prodFn T v w a₁ (famStep b₁).2 a₂ b₂ y))
        + (cond (famStep b₂).1 (-(prodFn T v w a₁ b₁ a₂ (famStep b₂).2 y))
          (prodFn T v w a₁ b₁ a₂ (famStep b₂).2 y)) := by
  funext y
  rw [show prodFn T v w a₁ b₁ a₂ b₂ = fun z => ⟪(fun z' => T (famApp a₁ b₁ v z')) z,
      famApp a₂ b₂ w z⟫ from rfl,
    nth_partial_inner_prod (differentiable_T_famApp T a₁ b₁ v)
      (differentiable_famApp a₂ b₂ w) 1 y,
    fderiv_T_famApp, fderiv_famApp_e1, fderiv_famApp_e1]
  rcases famStep b₁ with ⟨c₁, b₁'⟩
  rcases famStep b₂ with ⟨c₂, b₂'⟩
  cases c₁ <;> cases c₂ <;>
    simp [prodFn, inner_neg_left, inner_neg_right, map_neg]

/-- Weighted ∂-closed family of sums of signed base products; the weight
counts the leaves. -/
inductive IsProdDerivFam (T : ℝ² →L[ℝ] ℝ²) (v w : ℝ³) : (E 2 → ℝ) → ℕ → Prop where
  | base (a₁ b₁ a₂ b₂ : Fin 3) : IsProdDerivFam T v w (prodFn T v w a₁ b₁ a₂ b₂) 1
  | neg {f k} : IsProdDerivFam T v w f k → IsProdDerivFam T v w (fun y => -(f y)) k
  | add {f g k l} : IsProdDerivFam T v w f k → IsProdDerivFam T v w g l →
      IsProdDerivFam T v w (fun y => f y + g y) (k + l)

lemma IsProdDerivFam.differentiable {T : ℝ² →L[ℝ] ℝ²} {v w : ℝ³} {f : E 2 → ℝ} {k : ℕ}
    (hf : IsProdDerivFam T v w f k) : Differentiable ℝ f := by
  induction hf with
  | base a₁ b₁ a₂ b₂ =>
    exact Differentiable.inner ℝ (differentiable_T_famApp T a₁ b₁ v)
      (differentiable_famApp a₂ b₂ w)
  | neg _ ih => exact ih.neg
  | add _ _ ihf ihg => exact ihf.add ihg

private lemma nth_partial_add {n : ℕ} {f g : E n → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin n) :
    nth_partial i (fun y => f y + g y)
    = fun y => nth_partial i f y + nth_partial i g y := by
  funext y
  simp only [nth_partial]
  rw [fderiv_fun_add (hf y) (hg y)]
  simp

/-- One derivative doubles the weight. -/
lemma IsProdDerivFam.nth_partial {T : ℝ² →L[ℝ] ℝ²} {v w : ℝ³} {f : E 2 → ℝ} {k : ℕ}
    (hf : IsProdDerivFam T v w f k) (i : Fin 2) :
    IsProdDerivFam T v w (nth_partial i f) (2 * k) := by
  induction hf with
  | base a₁ b₁ a₂ b₂ =>
    fin_cases i
    · show IsProdDerivFam T v w (GlobalTheorem.nth_partial 0 (prodFn T v w a₁ b₁ a₂ b₂)) _
      rw [nth_partial_prodFn_e0]
      have h1 : IsProdDerivFam T v w
          (fun y => cond (famStep a₁).1 (-(prodFn T v w (famStep a₁).2 b₁ a₂ b₂ y))
            (prodFn T v w (famStep a₁).2 b₁ a₂ b₂ y)) 1 := by
        cases hc : (famStep a₁).1
        · simpa [hc] using IsProdDerivFam.base (T := T) (v := v) (w := w) (famStep a₁).2 b₁ a₂ b₂
        · simpa [hc] using (IsProdDerivFam.base (T := T) (v := v) (w := w)
            (famStep a₁).2 b₁ a₂ b₂).neg
      have h2 : IsProdDerivFam T v w
          (fun y => cond (famStep a₂).1 (-(prodFn T v w a₁ b₁ (famStep a₂).2 b₂ y))
            (prodFn T v w a₁ b₁ (famStep a₂).2 b₂ y)) 1 := by
        cases hc : (famStep a₂).1
        · simpa [hc] using IsProdDerivFam.base (T := T) (v := v) (w := w) a₁ b₁ (famStep a₂).2 b₂
        · simpa [hc] using (IsProdDerivFam.base (T := T) (v := v) (w := w)
            a₁ b₁ (famStep a₂).2 b₂).neg
      exact h1.add h2
    · show IsProdDerivFam T v w (GlobalTheorem.nth_partial 1 (prodFn T v w a₁ b₁ a₂ b₂)) _
      rw [nth_partial_prodFn_e1]
      have h1 : IsProdDerivFam T v w
          (fun y => cond (famStep b₁).1 (-(prodFn T v w a₁ (famStep b₁).2 a₂ b₂ y))
            (prodFn T v w a₁ (famStep b₁).2 a₂ b₂ y)) 1 := by
        cases hc : (famStep b₁).1
        · simpa [hc] using IsProdDerivFam.base (T := T) (v := v) (w := w) a₁ (famStep b₁).2 a₂ b₂
        · simpa [hc] using (IsProdDerivFam.base (T := T) (v := v) (w := w)
            a₁ (famStep b₁).2 a₂ b₂).neg
      have h2 : IsProdDerivFam T v w
          (fun y => cond (famStep b₂).1 (-(prodFn T v w a₁ b₁ a₂ (famStep b₂).2 y))
            (prodFn T v w a₁ b₁ a₂ (famStep b₂).2 y)) 1 := by
        cases hc : (famStep b₂).1
        · simpa [hc] using IsProdDerivFam.base (T := T) (v := v) (w := w) a₁ b₁ a₂ (famStep b₂).2
        · simpa [hc] using (IsProdDerivFam.base (T := T) (v := v) (w := w)
            a₁ b₁ a₂ (famStep b₂).2).neg
      exact h1.add h2
  | neg hf ih =>
    rw [nth_partial_neg]
    exact ih.neg
  | @add f g k l hf hg ihf ihg =>
    rw [nth_partial_add hf.differentiable hg.differentiable]
    rw [show 2 * (k + l) = 2 * k + 2 * l by ring]
    exact ihf.add ihg

/-- Every weight-`k` family member is bounded by `k·‖v‖·‖w‖` (for `‖T‖ ≤ 1`). -/
lemma IsProdDerivFam.abs_le {T : ℝ² →L[ℝ] ℝ²} {v w : ℝ³} {f : E 2 → ℝ} {k : ℕ}
    (hf : IsProdDerivFam T v w f k) (hT : ‖T‖ ≤ 1) (y : E 2) :
    |f y| ≤ k * (‖v‖ * ‖w‖) := by
  induction hf with
  | base a₁ b₁ a₂ b₂ =>
    calc |prodFn T v w a₁ b₁ a₂ b₂ y|
        ≤ ‖T (famApp a₁ b₁ v y)‖ * ‖famApp a₂ b₂ w y‖ := abs_real_inner_le_norm _ _
      _ ≤ (1 * ‖v‖) * (1 * ‖w‖) := by
          have hTv : ‖T (famApp a₁ b₁ v y)‖ ≤ 1 * ‖v‖ := by
            calc ‖T (famApp a₁ b₁ v y)‖ ≤ ‖T‖ * ‖famApp a₁ b₁ v y‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ 1 * (1 * ‖v‖) := by
                  have hfam : ‖famApp a₁ b₁ v y‖ ≤ 1 * ‖v‖ := by
                    calc ‖famApp a₁ b₁ v y‖
                        ≤ ‖rotMFam a₁ b₁ (y.ofLp 0) (y.ofLp 1)‖ * ‖v‖ :=
                          ContinuousLinearMap.le_opNorm _ _
                      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right
                          (rotMFam_norm_le_one a₁ b₁ _ _) (norm_nonneg _)
                  exact mul_le_mul hT hfam (norm_nonneg _) zero_le_one
              _ = 1 * ‖v‖ := by ring
          have hW : ‖famApp a₂ b₂ w y‖ ≤ 1 * ‖w‖ := by
            calc ‖famApp a₂ b₂ w y‖
                ≤ ‖rotMFam a₂ b₂ (y.ofLp 0) (y.ofLp 1)‖ * ‖w‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right
                  (rotMFam_norm_le_one a₂ b₂ _ _) (norm_nonneg _)
          exact mul_le_mul hTv hW (norm_nonneg _) (by positivity)
      _ = 1 * (‖v‖ * ‖w‖) := by ring
      _ = (1 : ℕ) * (‖v‖ * ‖w‖) := by norm_num
  | neg _ ih => simpa using ih
  | @add f g k l _ _ ihf ihg =>
    calc |f y + g y| ≤ |f y| + |g y| := abs_add_le _ _
      _ ≤ k * (‖v‖ * ‖w‖) + l * (‖v‖ * ‖w‖) := add_le_add ihf ihg
      _ = ((k + l : ℕ) : ℝ) * (‖v‖ * ‖w‖) := by push_cast; ring

/-! ## The span-type product: smoothness, third bound, explicit partials -/

private lemma contDiff_rotM_apply (P : ℝ³) :
    ContDiff ℝ 3 (fun z : E 2 => rotM (z.ofLp 0) (z.ofLp 1) P) := by
  rw [contDiff_piLp]
  intro i
  simp only [rotM, rotM_mat, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply]
  fin_cases i <;> (simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop)

lemma prodMM_contDiff (T : ℝ² →L[ℝ] ℝ²) (v w : ℝ³) :
    ContDiff ℝ 3 (prodFn T v w 0 0 0 0) := by
  refine ContDiff.inner ℝ ?_ ?_
  · exact (T.contDiff).comp (contDiff_rotM_apply v)
  · exact contDiff_rotM_apply w

lemma prodMM_third_partials_bounded (T : ℝ² →L[ℝ] ℝ²) (hT : ‖T‖ ≤ 1) (v w : ℝ³) :
    third_partials_bounded (prodFn T v w 0 0 0 0) (8 * (‖v‖ * ‖w‖)) := by
  intro x i j k
  have h := ((((IsProdDerivFam.base (T := T) (v := v) (w := w)
    0 0 0 0).nth_partial k).nth_partial j).nth_partial i).abs_le hT x
  have : ((2 * (2 * (2 * 1)) : ℕ) : ℝ) = 8 := by norm_num
  rw [this] at h
  linarith [h]

/-- First partials of the span-type product (fold-free from `(M, M)`). -/
private lemma prodFn00_d0 (T : ℝ² →L[ℝ] ℝ²) (v w : ℝ³) :
    nth_partial 0 (prodFn T v w 0 0 0 0)
    = fun y => prodFn T v w 1 0 0 0 y + prodFn T v w 0 0 1 0 y := by
  rw [nth_partial_prodFn_e0]
  simp [famStep]

private lemma prodFn00_d1 (T : ℝ² →L[ℝ] ℝ²) (v w : ℝ³) :
    nth_partial 1 (prodFn T v w 0 0 0 0)
    = fun y => prodFn T v w 0 1 0 0 y + prodFn T v w 0 0 0 1 y := by
  rw [nth_partial_prodFn_e1]
  simp [famStep]

private lemma prodFn00_d00 (T : ℝ² →L[ℝ] ℝ²) (v w : ℝ³) :
    nth_partial 0 (nth_partial 0 (prodFn T v w 0 0 0 0))
    = fun y => (prodFn T v w 2 0 0 0 y + prodFn T v w 1 0 1 0 y)
      + (prodFn T v w 1 0 1 0 y + prodFn T v w 0 0 2 0 y) := by
  rw [prodFn00_d0,
    nth_partial_add (IsProdDerivFam.base (T := T) (v := v) (w := w) 1 0 0 0).differentiable
      (IsProdDerivFam.base (T := T) (v := v) (w := w) 0 0 1 0).differentiable,
    nth_partial_prodFn_e0, nth_partial_prodFn_e0]
  simp [famStep]

private lemma prodFn00_d10 (T : ℝ² →L[ℝ] ℝ²) (v w : ℝ³) :
    nth_partial 1 (nth_partial 0 (prodFn T v w 0 0 0 0))
    = fun y => (prodFn T v w 1 1 0 0 y + prodFn T v w 1 0 0 1 y)
      + (prodFn T v w 0 1 1 0 y + prodFn T v w 0 0 1 1 y) := by
  rw [prodFn00_d0,
    nth_partial_add (IsProdDerivFam.base (T := T) (v := v) (w := w) 1 0 0 0).differentiable
      (IsProdDerivFam.base (T := T) (v := v) (w := w) 0 0 1 0).differentiable,
    nth_partial_prodFn_e1, nth_partial_prodFn_e1]
  simp [famStep]

private lemma prodFn00_d01 (T : ℝ² →L[ℝ] ℝ²) (v w : ℝ³) :
    nth_partial 0 (nth_partial 1 (prodFn T v w 0 0 0 0))
    = fun y => (prodFn T v w 1 1 0 0 y + prodFn T v w 0 1 1 0 y)
      + (prodFn T v w 1 0 0 1 y + prodFn T v w 0 0 1 1 y) := by
  rw [prodFn00_d1,
    nth_partial_add (IsProdDerivFam.base (T := T) (v := v) (w := w) 0 1 0 0).differentiable
      (IsProdDerivFam.base (T := T) (v := v) (w := w) 0 0 0 1).differentiable,
    nth_partial_prodFn_e0, nth_partial_prodFn_e0]
  simp [famStep]

private lemma prodFn00_d11 (T : ℝ² →L[ℝ] ℝ²) (v w : ℝ³) :
    nth_partial 1 (nth_partial 1 (prodFn T v w 0 0 0 0))
    = fun y => (prodFn T v w 0 2 0 0 y + prodFn T v w 0 1 0 1 y)
      + (prodFn T v w 0 1 0 1 y + prodFn T v w 0 0 0 2 y) := by
  rw [prodFn00_d1,
    nth_partial_add (IsProdDerivFam.base (T := T) (v := v) (w := w) 0 1 0 0).differentiable
      (IsProdDerivFam.base (T := T) (v := v) (w := w) 0 0 0 1).differentiable,
    nth_partial_prodFn_e1, nth_partial_prodFn_e1]
  simp [famStep]

/-! ## The variation budget and transfer theorems -/

/-- The second-order variation budget of `⟪T (M(θ,φ)v), M(θ,φ)w⟫` over a
per-axis box of radii `(εθ, εφ)`: exact first and second partials at the
center, cubic remainder `8‖v‖‖w‖·E³/6`. -/
noncomputable def ΔprodMM (T : ℝ² →L[ℝ] ℝ²) (v w : ℝ³) (εθ εφ θ_ φ_ : ℝ) : ℝ :=
  εθ * |⟪T (rotMθ θ_ φ_ v), rotM θ_ φ_ w⟫ + ⟪T (rotM θ_ φ_ v), rotMθ θ_ φ_ w⟫|
  + εφ * |⟪T (rotMφ θ_ φ_ v), rotM θ_ φ_ w⟫ + ⟪T (rotM θ_ φ_ v), rotMφ θ_ φ_ w⟫|
  + (1/2) * (
      εθ^2 * |⟪T (rotMθθ θ_ φ_ v), rotM θ_ φ_ w⟫
              + 2*⟪T (rotMθ θ_ φ_ v), rotMθ θ_ φ_ w⟫
              + ⟪T (rotM θ_ φ_ v), rotMθθ θ_ φ_ w⟫|
      + 2*(εθ*εφ) * |⟪T (rotMθφ θ_ φ_ v), rotM θ_ φ_ w⟫
              + ⟪T (rotMθ θ_ φ_ v), rotMφ θ_ φ_ w⟫
              + ⟪T (rotMφ θ_ φ_ v), rotMθ θ_ φ_ w⟫
              + ⟪T (rotM θ_ φ_ v), rotMθφ θ_ φ_ w⟫|
      + εφ^2 * |⟪T (rotMφφ θ_ φ_ v), rotM θ_ φ_ w⟫
              + 2*⟪T (rotMφ θ_ φ_ v), rotMφ θ_ φ_ w⟫
              + ⟪T (rotM θ_ φ_ v), rotMφφ θ_ φ_ w⟫|)
  + 8 * ‖v‖ * ‖w‖ * (εθ + εφ)^3 / 6

/-- **Second-order variation of the product quantity** `⟪T (M v), M w⟫`.
Powers the spanning condition (`T = rotR (π/2)`) and the LMD numerator
(`T = id`) of the second-order local certificate. -/
theorem inner_prod_MM_sub_le (T : ℝ² →L[ℝ] ℝ²) (hT : ‖T‖ ≤ 1) {v w : ℝ³}
    {εθ εφ θ θ_ φ φ_ : ℝ}
    (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ) (hθ : |θ - θ_| ≤ εθ) (hφ : |φ - φ_| ≤ εφ) :
    |⟪T (rotM θ φ v), rotM θ φ w⟫ - ⟪T (rotM θ_ φ_ v), rotM θ_ φ_ w⟫|
      ≤ ΔprodMM T v w εθ εφ θ_ φ_ := by
  have hεv : ∀ i, 0 ≤ (![εθ, εφ] : Fin 2 → ℝ) i := by
    intro i; fin_cases i
    · exact hεθ
    · exact hεφ
  have hdiffv : ∀ i : Fin 2,
      |(!₂[θ_, φ_] : E 2) i - (!₂[θ, φ] : E 2) i| ≤ ![εθ, εφ] i := by
    intro i; fin_cases i
    · simpa [abs_sub_comm] using hθ
    · simpa [abs_sub_comm] using hφ
  have key := bounded_partials_control_difference2 (prodFn T v w 0 0 0 0)
    (prodMM_contDiff T v w) !₂[θ_, φ_] !₂[θ, φ] ![εθ, εφ] hεv hdiffv
    (prodMM_third_partials_bounded T hT v w)
  rw [show ∑ i, (![εθ, εφ] : Fin 2 → ℝ) i = εθ + εφ by simp [Fin.sum_univ_two]] at key
  have hsum1 : ∑ i, (![εθ, εφ] : Fin 2 → ℝ) i *
        |GlobalTheorem.nth_partial i (prodFn T v w 0 0 0 0) !₂[θ_, φ_]|
      = εθ * |⟪T (rotMθ θ_ φ_ v), rotM θ_ φ_ w⟫ + ⟪T (rotM θ_ φ_ v), rotMθ θ_ φ_ w⟫|
        + εφ * |⟪T (rotMφ θ_ φ_ v), rotM θ_ φ_ w⟫ + ⟪T (rotM θ_ φ_ v), rotMφ θ_ φ_ w⟫| := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, prodFn00_d0, prodFn00_d1]
    rfl
  have hsum2 : ∑ i, ∑ j, (![εθ, εφ] : Fin 2 → ℝ) i * (![εθ, εφ] : Fin 2 → ℝ) j *
        |GlobalTheorem.nth_partial i (GlobalTheorem.nth_partial j
          (prodFn T v w 0 0 0 0)) !₂[θ_, φ_]|
      = εθ^2 * |⟪T (rotMθθ θ_ φ_ v), rotM θ_ φ_ w⟫
              + 2*⟪T (rotMθ θ_ φ_ v), rotMθ θ_ φ_ w⟫
              + ⟪T (rotM θ_ φ_ v), rotMθθ θ_ φ_ w⟫|
        + 2*(εθ*εφ) * |⟪T (rotMθφ θ_ φ_ v), rotM θ_ φ_ w⟫
              + ⟪T (rotMθ θ_ φ_ v), rotMφ θ_ φ_ w⟫
              + ⟪T (rotMφ θ_ φ_ v), rotMθ θ_ φ_ w⟫
              + ⟪T (rotM θ_ φ_ v), rotMθφ θ_ φ_ w⟫|
        + εφ^2 * |⟪T (rotMφφ θ_ φ_ v), rotM θ_ φ_ w⟫
              + 2*⟪T (rotMφ θ_ φ_ v), rotMφ θ_ φ_ w⟫
              + ⟪T (rotM θ_ φ_ v), rotMφφ θ_ φ_ w⟫| := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      prodFn00_d00, prodFn00_d10, prodFn00_d01, prodFn00_d11]
    rw [show |(prodFn T v w 2 0 0 0 !₂[θ_, φ_] + prodFn T v w 1 0 1 0 !₂[θ_, φ_])
          + (prodFn T v w 1 0 1 0 !₂[θ_, φ_] + prodFn T v w 0 0 2 0 !₂[θ_, φ_])|
        = |⟪T (rotMθθ θ_ φ_ v), rotM θ_ φ_ w⟫
            + 2*⟪T (rotMθ θ_ φ_ v), rotMθ θ_ φ_ w⟫
            + ⟪T (rotM θ_ φ_ v), rotMθθ θ_ φ_ w⟫| from congrArg abs (by
          show ⟪T (rotMθθ θ_ φ_ v), rotM θ_ φ_ w⟫
              + ⟪T (rotMθ θ_ φ_ v), rotMθ θ_ φ_ w⟫
              + (⟪T (rotMθ θ_ φ_ v), rotMθ θ_ φ_ w⟫
                + ⟪T (rotM θ_ φ_ v), rotMθθ θ_ φ_ w⟫) = _
          ring)]
    rw [show |(prodFn T v w 1 1 0 0 !₂[θ_, φ_] + prodFn T v w 1 0 0 1 !₂[θ_, φ_])
          + (prodFn T v w 0 1 1 0 !₂[θ_, φ_] + prodFn T v w 0 0 1 1 !₂[θ_, φ_])|
        = |⟪T (rotMθφ θ_ φ_ v), rotM θ_ φ_ w⟫
            + ⟪T (rotMθ θ_ φ_ v), rotMφ θ_ φ_ w⟫
            + ⟪T (rotMφ θ_ φ_ v), rotMθ θ_ φ_ w⟫
            + ⟪T (rotM θ_ φ_ v), rotMθφ θ_ φ_ w⟫| from congrArg abs (by
          show ⟪T (rotMθφ θ_ φ_ v), rotM θ_ φ_ w⟫
              + ⟪T (rotMθ θ_ φ_ v), rotMφ θ_ φ_ w⟫
              + (⟪T (rotMφ θ_ φ_ v), rotMθ θ_ φ_ w⟫
                + ⟪T (rotM θ_ φ_ v), rotMθφ θ_ φ_ w⟫) = _
          ring)]
    rw [show |(prodFn T v w 1 1 0 0 !₂[θ_, φ_] + prodFn T v w 0 1 1 0 !₂[θ_, φ_])
          + (prodFn T v w 1 0 0 1 !₂[θ_, φ_] + prodFn T v w 0 0 1 1 !₂[θ_, φ_])|
        = |⟪T (rotMθφ θ_ φ_ v), rotM θ_ φ_ w⟫
            + ⟪T (rotMθ θ_ φ_ v), rotMφ θ_ φ_ w⟫
            + ⟪T (rotMφ θ_ φ_ v), rotMθ θ_ φ_ w⟫
            + ⟪T (rotM θ_ φ_ v), rotMθφ θ_ φ_ w⟫| from congrArg abs (by
          show ⟪T (rotMθφ θ_ φ_ v), rotM θ_ φ_ w⟫
              + ⟪T (rotMφ θ_ φ_ v), rotMθ θ_ φ_ w⟫
              + (⟪T (rotMθ θ_ φ_ v), rotMφ θ_ φ_ w⟫
                + ⟪T (rotM θ_ φ_ v), rotMθφ θ_ φ_ w⟫) = _
          ring)]
    rw [show |(prodFn T v w 0 2 0 0 !₂[θ_, φ_] + prodFn T v w 0 1 0 1 !₂[θ_, φ_])
          + (prodFn T v w 0 1 0 1 !₂[θ_, φ_] + prodFn T v w 0 0 0 2 !₂[θ_, φ_])|
        = |⟪T (rotMφφ θ_ φ_ v), rotM θ_ φ_ w⟫
            + 2*⟪T (rotMφ θ_ φ_ v), rotMφ θ_ φ_ w⟫
            + ⟪T (rotM θ_ φ_ v), rotMφφ θ_ φ_ w⟫| from congrArg abs (by
          show ⟪T (rotMφφ θ_ φ_ v), rotM θ_ φ_ w⟫
              + ⟪T (rotMφ θ_ φ_ v), rotMφ θ_ φ_ w⟫
              + (⟪T (rotMφ θ_ φ_ v), rotMφ θ_ φ_ w⟫
                + ⟪T (rotM θ_ φ_ v), rotMφφ θ_ φ_ w⟫) = _
          ring)]
    ring
  rw [hsum1, hsum2] at key
  unfold ΔprodMM
  rw [abs_sub_comm]
  refine key.trans (le_of_eq ?_)
  ring

end GlobalTheorem

end
