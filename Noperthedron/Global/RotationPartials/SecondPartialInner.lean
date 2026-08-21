/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Noperthedron.Global.RotationPartials.SecondPartialOuter
public import Noperthedron.Global.RotationPartials.Rotproj
public import Noperthedron.Global.FDerivHelpers

@[expose] public section


/-!
# Second Partial Inner Lemmas

This file contains:
- **`third_partial_inner_rotM_inner`** (27 cases)
- **`rotation_third_partials_bounded`** (the main theorem from [SY25] Lemma 19)

Helper lemmas `comp_norm_le_one`, `neg_comp_norm_le_one`, `inner_bound_helper`, `fderiv_inner_const`
are imported from SecondPartialHelpers.
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-!
## Private lemma: second partials as inner products (inner case, 9 cases)

The second partial derivatives of rotproj_inner S w equal ⟪A S, w⟫
where A is a composition of rotR/rotR' with rotM/rotMθ/rotMφ/rotMθθ/rotMθφ/rotMφφ,
all with ‖A‖ ≤ 1.

Variables: x 0 = α, x 1 = θ, x 2 = φ (note: rotprojRM takes θ φ α)
rotproj_inner S w x = ⟪rotprojRM (x 1) (x 2) (x 0) S, w⟫
                    = ⟪rotR (x 0) (rotM (x 1) (x 2) S), w⟫

The A[i,j] table:
| i\j |    0                    |    1                  |    2                  |
|-----|-------------------------|-----------------------|-----------------------|
|  0  | -(rotR α ∘L rotM θ φ)   | rotR' α ∘L rotMθ θ φ  | rotR' α ∘L rotMφ θ φ  |
|  1  | rotR' α ∘L rotMθ θ φ    | rotR α ∘L rotMθθ θ φ  | rotR α ∘L rotMθφ θ φ  |
|  2  | rotR' α ∘L rotMφ θ φ    | rotR α ∘L rotMθφ θ φ  | rotR α ∘L rotMφφ θ φ  |
-/

private lemma second_partial_col0 (S : ℝ³) (w : ℝ²) (x : E 3) (i : Fin 3) :
    nth_partial i (nth_partial 0 (rotproj_inner S w)) x =
    ⟪(fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) x)
      (EuclideanSpace.single i 1), w⟫ := by
  rw [nth_partial_rotproj_inner_e0 S w]; unfold nth_partial
  exact fderiv_inner_const _ w x _ (differentiableAt_rotR'_rotM S x)

private lemma second_partial_col1 (S : ℝ³) (w : ℝ²) (x : E 3) (i : Fin 3) :
    nth_partial i (nth_partial 1 (rotproj_inner S w)) x =
    ⟪(fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S)) x)
      (EuclideanSpace.single i 1), w⟫ := by
  rw [nth_partial_rotproj_inner_e1 S w]; unfold nth_partial
  exact fderiv_inner_const _ w x _ (differentiableAt_rotR_rotMθ S x)

private lemma second_partial_col2 (S : ℝ³) (w : ℝ²) (x : E 3) (i : Fin 3) :
    nth_partial i (nth_partial 2 (rotproj_inner S w)) x =
    ⟪(fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S)) x)
      (EuclideanSpace.single i 1), w⟫ := by
  rw [nth_partial_rotproj_inner_e2 S w]; unfold nth_partial
  exact fderiv_inner_const _ w x _ (differentiableAt_rotR_rotMφ S x)

/-- The second partials of `rotproj_inner` are given pointwise by the
`inner_second_partial_A` table. -/
theorem second_partial_rotproj_inner_eq (S : ℝ³) (w : ℝ²) (x : E 3) (i j : Fin 3) :
    nth_partial i (nth_partial j (rotproj_inner S w)) x =
      ⟪inner_second_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i j S, w⟫ := by
  fin_cases i <;> fin_cases j
  · -- (0, 0): -(rotR α ∘L rotM θ φ)
    show nth_partial 0 (nth_partial 0 _) x = _
    rw [second_partial_col0 S w x,
      fderiv_rotR'_rotM_in_e0 S x _ _ _ rfl rfl rfl (differentiableAt_rotR'_rotM S x)]
    simp only [inner_second_partial_A, neg_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, inner_neg_left]
  · -- (0, 1): rotR' α ∘L rotMθ θ φ
    show nth_partial 0 (nth_partial 1 _) x = _
    rw [second_partial_col1 S w x,
      fderiv_rotR_any_M_in_e0 S x rotMθ (differentiableAt_rotR_rotMθ S x)]; rfl
  · -- (0, 2): rotR' α ∘L rotMφ θ φ
    show nth_partial 0 (nth_partial 2 _) x = _
    rw [second_partial_col2 S w x,
      fderiv_rotR_any_M_in_e0 S x rotMφ (differentiableAt_rotR_rotMφ S x)]; rfl
  · -- (1, 0): rotR' α ∘L rotMθ θ φ
    show nth_partial 1 (nth_partial 0 _) x = _
    rw [second_partial_col0 S w x,
      fderiv_rotR'_rotM_in_e1 S x _ _ _ rfl rfl rfl (differentiableAt_rotR'_rotM S x)]
    simp only [inner_second_partial_A, ContinuousLinearMap.coe_comp, Function.comp_apply]
  · -- (1, 1): rotR α ∘L rotMθθ θ φ
    show nth_partial 1 (nth_partial 1 _) x = _
    rw [second_partial_col1 S w x, fderiv_rotR_rotMθ_in_e1 S x]; rfl
  · -- (1, 2): rotR α ∘L rotMθφ θ φ
    show nth_partial 1 (nth_partial 2 _) x = _
    rw [second_partial_col2 S w x, fderiv_rotR_rotMφ_in_e1 S x]; rfl
  · -- (2, 0): rotR' α ∘L rotMφ θ φ
    show nth_partial 2 (nth_partial 0 _) x = _
    rw [second_partial_col0 S w x,
      fderiv_rotR'_rotM_in_e2 S x _ _ _ rfl rfl rfl (differentiableAt_rotR'_rotM S x)]
    simp only [inner_second_partial_A, ContinuousLinearMap.coe_comp, Function.comp_apply]
  · -- (2, 1): rotR α ∘L rotMθφ θ φ
    show nth_partial 2 (nth_partial 1 _) x = _
    rw [second_partial_col1 S w x, fderiv_rotR_rotMθ_in_e2 S x]; rfl
  · -- (2, 2): rotR α ∘L rotMφφ θ φ
    show nth_partial 2 (nth_partial 2 _) x = _
    rw [second_partial_col2 S w x, fderiv_rotR_rotMφ_in_e2 S x]; rfl

/-- Function-level form of `second_partial_rotproj_inner_eq`. -/
theorem nth_partial_nth_partial_rotproj_inner (S : ℝ³) (w : ℝ²) (i j : Fin 3) :
    nth_partial i (nth_partial j (rotproj_inner S w)) =
      fun y => ⟪inner_second_partial_A (y.ofLp 0) (y.ofLp 1) (y.ofLp 2) i j S, w⟫ :=
  funext fun y => second_partial_rotproj_inner_eq S w y i j

/-!
## Third partials as inner products (27 cases)

Differentiating the `inner_second_partial_A` table once more: each column of the
table is `y ↦ (±) X (y 0) (N (y 1) (y 2) S)` with `X ∈ {rotR, rotR'}` and `N` in the
M-family, so the generic direction lemmas `fderiv_rotR_any_M_in_e0`,
`fderiv_rotR'_any_M_in_e0`, `fderiv_head_family_in_e1/e2` cover every case.
-/

private lemma nth_partial_neg (f : E 3 → ℝ) (i : Fin 3) (x : E 3) :
    nth_partial i (fun y => -(f y)) x = -(nth_partial i f x) := by
  show fderiv ℝ (-f) x (EuclideanSpace.single i 1) = -(fderiv ℝ f x (EuclideanSpace.single i 1))
  rw [fderiv_neg]
  simp only [neg_apply]

/-- All three partials of one column `y ↦ ⟪X (y 0) (N (y 1) (y 2) S), w⟫` of the
second-partial table, given the head derivative in the `e₀` direction (`h0`) and
the two matrix-family derivatives (`hθ`, `hφ`). -/
private lemma nth_partial_inner_col (S : ℝ³) (w : ℝ²) (x : E 3)
    (X : ℝ → ℝ² →L[ℝ] ℝ²) (N : ℝ → ℝ → ℝ³ →L[ℝ] ℝ²) {D0 Nθ' Nφ' : ℝ²} (i : Fin 3)
    (hdiff : DifferentiableAt ℝ (fun z : E 3 => X (z.ofLp 0) (N (z.ofLp 1) (z.ofLp 2) S)) x)
    (h0 : (fderiv ℝ (fun z : E 3 => X (z.ofLp 0) (N (z.ofLp 1) (z.ofLp 2) S)) x)
      (EuclideanSpace.single 0 1) = D0)
    (hθ : HasDerivAt (fun t => N t (x.ofLp 2) S) Nθ' (x.ofLp 1))
    (hφ : HasDerivAt (fun t => N (x.ofLp 1) t S) Nφ' (x.ofLp 2)) :
    nth_partial i (fun y : E 3 => ⟪X (y.ofLp 0) (N (y.ofLp 1) (y.ofLp 2) S), w⟫) x =
      ⟪![D0, X (x.ofLp 0) Nθ', X (x.ofLp 0) Nφ'] i, w⟫ := by
  unfold nth_partial
  rw [fderiv_inner_const _ w x _ hdiff]
  congr 1
  fin_cases i
  · exact h0
  · exact fderiv_head_family_in_e1 S x X N Nθ' hdiff hθ
  · exact fderiv_head_family_in_e2 S x X N Nφ' hdiff hφ

/-- Match one entry of the `nth_partial_inner_col` vector against the
`inner_third_partial_A` table (normalizing signs and `∘L` applications). -/
local macro "third_partial_match" : tactic =>
  `(tactic| simp only [inner_third_partial_A, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, map_neg, neg_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, inner_neg_left])

theorem third_partial_rotproj_inner_eq (S : ℝ³) (w : ℝ²) (x : E 3) (i j k : Fin 3) :
    nth_partial i (nth_partial j (nth_partial k (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i j k S, w⟫ := by
  have hneg00 : (fun y : E 3 =>
        ⟪inner_second_partial_A (y.ofLp 0) (y.ofLp 1) (y.ofLp 2) 0 0 S, w⟫)
      = fun y => -⟪rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
    funext y
    simp only [inner_second_partial_A, neg_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, inner_neg_left]
  fin_cases j <;> fin_cases k
  · -- column (0,0): A₂ = -(rotR ∘L rotM)
    show nth_partial i (nth_partial 0 (nth_partial 0 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 0 0 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 0 0, hneg00, nth_partial_neg,
      nth_partial_inner_col S w x rotR rotM i (differentiableAt_rotR_rotM S x)
        (fderiv_rotR_any_M_in_e0 S x rotM (differentiableAt_rotR_rotM S x))
        (hasDerivAt_rotM_θ (x.ofLp 1) (x.ofLp 2) S) (hasDerivAt_rotM_φ (x.ofLp 1) (x.ofLp 2) S)]
    fin_cases i <;> third_partial_match
  · -- column (0,1): A₂ = rotR' ∘L rotMθ
    show nth_partial i (nth_partial 0 (nth_partial 1 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 0 1 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 0 1]
    show nth_partial i (fun y => ⟪rotR' (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    rw [nth_partial_inner_col S w x rotR' rotMθ i (differentiableAt_rotR'_rotMθ S x)
      (fderiv_rotR'_any_M_in_e0 S x rotMθ (differentiableAt_rotR'_rotMθ S x))
      (hasDerivAt_rotMθ_θ (x.ofLp 1) (x.ofLp 2) S) (hasDerivAt_rotMθ_φ (x.ofLp 1) (x.ofLp 2) S)]
    fin_cases i <;> third_partial_match
  · -- column (0,2): A₂ = rotR' ∘L rotMφ
    show nth_partial i (nth_partial 0 (nth_partial 2 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 0 2 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 0 2]
    show nth_partial i (fun y => ⟪rotR' (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    rw [nth_partial_inner_col S w x rotR' rotMφ i (differentiableAt_rotR'_rotMφ S x)
      (fderiv_rotR'_any_M_in_e0 S x rotMφ (differentiableAt_rotR'_rotMφ S x))
      (hasDerivAt_rotMφ_θ (x.ofLp 1) (x.ofLp 2) S) (hasDerivAt_rotMφ_φ (x.ofLp 1) (x.ofLp 2) S)]
    fin_cases i <;> third_partial_match
  · -- column (1,0): A₂ = rotR' ∘L rotMθ (mixed-partial symmetry)
    show nth_partial i (nth_partial 1 (nth_partial 0 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 1 0 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 1 0]
    show nth_partial i (fun y => ⟪rotR' (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    rw [nth_partial_inner_col S w x rotR' rotMθ i (differentiableAt_rotR'_rotMθ S x)
      (fderiv_rotR'_any_M_in_e0 S x rotMθ (differentiableAt_rotR'_rotMθ S x))
      (hasDerivAt_rotMθ_θ (x.ofLp 1) (x.ofLp 2) S) (hasDerivAt_rotMθ_φ (x.ofLp 1) (x.ofLp 2) S)]
    fin_cases i <;> third_partial_match
  · -- column (1,1): A₂ = rotR ∘L rotMθθ
    show nth_partial i (nth_partial 1 (nth_partial 1 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 1 1 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 1 1]
    show nth_partial i (fun y => ⟪rotR (y.ofLp 0) (rotMθθ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    rw [nth_partial_inner_col S w x rotR rotMθθ i (differentiableAt_rotR_rotMθθ S x)
      (fderiv_rotR_any_M_in_e0 S x rotMθθ (differentiableAt_rotR_rotMθθ S x))
      (hasDerivAt_rotMθθ_θ (x.ofLp 1) (x.ofLp 2) S) (hasDerivAt_rotMθθ_φ (x.ofLp 1) (x.ofLp 2) S)]
    fin_cases i <;> third_partial_match
  · -- column (1,2): A₂ = rotR ∘L rotMθφ
    show nth_partial i (nth_partial 1 (nth_partial 2 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 1 2 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 1 2]
    show nth_partial i (fun y => ⟪rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    rw [nth_partial_inner_col S w x rotR rotMθφ i (differentiableAt_rotR_rotMθφ S x)
      (fderiv_rotR_any_M_in_e0 S x rotMθφ (differentiableAt_rotR_rotMθφ S x))
      (hasDerivAt_rotMθφ_θ (x.ofLp 1) (x.ofLp 2) S) (hasDerivAt_rotMθφ_φ (x.ofLp 1) (x.ofLp 2) S)]
    fin_cases i <;> third_partial_match
  · -- column (2,0): A₂ = rotR' ∘L rotMφ (mixed-partial symmetry)
    show nth_partial i (nth_partial 2 (nth_partial 0 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 2 0 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 2 0]
    show nth_partial i (fun y => ⟪rotR' (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    rw [nth_partial_inner_col S w x rotR' rotMφ i (differentiableAt_rotR'_rotMφ S x)
      (fderiv_rotR'_any_M_in_e0 S x rotMφ (differentiableAt_rotR'_rotMφ S x))
      (hasDerivAt_rotMφ_θ (x.ofLp 1) (x.ofLp 2) S) (hasDerivAt_rotMφ_φ (x.ofLp 1) (x.ofLp 2) S)]
    fin_cases i <;> third_partial_match
  · -- column (2,1): A₂ = rotR ∘L rotMθφ (mixed-partial symmetry)
    show nth_partial i (nth_partial 2 (nth_partial 1 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 2 1 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 2 1]
    show nth_partial i (fun y => ⟪rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    rw [nth_partial_inner_col S w x rotR rotMθφ i (differentiableAt_rotR_rotMθφ S x)
      (fderiv_rotR_any_M_in_e0 S x rotMθφ (differentiableAt_rotR_rotMθφ S x))
      (hasDerivAt_rotMθφ_θ (x.ofLp 1) (x.ofLp 2) S) (hasDerivAt_rotMθφ_φ (x.ofLp 1) (x.ofLp 2) S)]
    fin_cases i <;> third_partial_match
  · -- column (2,2): A₂ = rotR ∘L rotMφφ
    show nth_partial i (nth_partial 2 (nth_partial 2 (rotproj_inner S w))) x =
      ⟪inner_third_partial_A (x.ofLp 0) (x.ofLp 1) (x.ofLp 2) i 2 2 S, w⟫
    rw [nth_partial_nth_partial_rotproj_inner S w 2 2]
    show nth_partial i (fun y => ⟪rotR (y.ofLp 0) (rotMφφ (y.ofLp 1) (y.ofLp 2) S), w⟫) x = _
    rw [nth_partial_inner_col S w x rotR rotMφφ i (differentiableAt_rotR_rotMφφ S x)
      (fderiv_rotR_any_M_in_e0 S x rotMφφ (differentiableAt_rotR_rotMφφ S x))
      (hasDerivAt_rotMφφ_θ (x.ofLp 1) (x.ofLp 2) S) (hasDerivAt_rotMφφ_φ (x.ofLp 1) (x.ofLp 2) S)]
    fin_cases i <;> third_partial_match

/- [SY25] Lemma 19 (inner part) -/
theorem third_partial_inner_rotM_inner (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1)
    (i j k : Fin 3) (y : ℝ³) :
    |nth_partial i (nth_partial j (nth_partial k (rotproj_inner S w))) y| ≤ ‖S‖ := by
  rw [third_partial_rotproj_inner_eq S w y i j k]
  exact inner_bound_helper _ S w w_unit (inner_third_partial_A_norm_le _ _ _ i j k)

/- [SY25] Lemma 19 -/
theorem rotation_third_partials_bounded (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    third_partials_bounded (rotproj_inner S w) ‖S‖ := fun x i j k =>
  third_partial_inner_rotM_inner S w_unit i j k x

end GlobalTheorem

end
