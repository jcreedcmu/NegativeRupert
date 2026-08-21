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
- the second-partial operator table `second_partial_rotproj_inner_eq` (9 cases)
- **`IsRotDerivFam`**, the ∂-closed family of signed
  `⟪(rotR/rotR') (α) (rotMFam a b (θ,φ) S), w⟫` functions, closed under
  `nth_partial` one identified step at a time
- **`rotation_third_partials_bounded`** ([SY25] Lemma 19) and the any-order
  bound `rotproj_inner_iterated_partials_bounded`, both by iterating the
  closure

Helper lemmas `comp_norm_le_one`, `inner_bound_helper`, `fderiv_inner_const`,
`rotMFam` and its step lemmas are imported from SecondPartialHelpers.
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
## Third and higher partials: the ∂-closed family

Instead of enumerating the third-partial operators, we close the family
`± ⟪(rotR/rotR') (α) (rotMFam a b (θ, φ) S), w⟫` under `nth_partial`: an
α-derivative steps the head around its four-cycle
(`rotR → rotR' → -rotR → -rotR'`), while a θ/φ-derivative moves one grid
coordinate of `rotMFam` (with a sign at the fold).  Iterating the single-step
closure bounds the partials of `rotproj_inner` at *every* order.
-/

/-- The ∂-closed family of inner scalar functions: signed
`⟪(rotR/rotR') (α) (∂θᵃ∂φᵇ M(θ,φ) S), w⟫`. -/
inductive IsRotDerivFam (S : ℝ³) (w : ℝ²) : (E 3 → ℝ) → Prop where
  | base (h' : Bool) (a b : Fin 3) :
      IsRotDerivFam S w
        (fun y => ⟪(cond h' rotR' rotR) (y.ofLp 0) (rotMFam a b (y.ofLp 1) (y.ofLp 2) S), w⟫)
  | neg {f} : IsRotDerivFam S w f → IsRotDerivFam S w (fun y => -(f y))

/-- The family is closed under partial derivatives. -/
lemma IsRotDerivFam.nth_partial {S : ℝ³} {w : ℝ²} {f : E 3 → ℝ}
    (hf : IsRotDerivFam S w f) (i : Fin 3) :
    IsRotDerivFam S w (nth_partial i f) := by
  induction hf with
  | neg _ ih => rw [nth_partial_neg]; exact ih.neg
  | base h' a b =>
    fin_cases i
    · -- α-direction: step the head around its four-cycle
      show IsRotDerivFam S w (GlobalTheorem.nth_partial 0
        (fun y : E 3 => ⟪(cond h' rotR' rotR) (y.ofLp 0)
          (rotMFam a b (y.ofLp 1) (y.ofLp 2) S), w⟫))
      cases h'
      · simp only [Bool.cond_false]
        rw [show GlobalTheorem.nth_partial 0
              (fun y : E 3 => ⟪rotR (y.ofLp 0) (rotMFam a b (y.ofLp 1) (y.ofLp 2) S), w⟫)
            = fun y : E 3 => ⟪rotR' (y.ofLp 0) (rotMFam a b (y.ofLp 1) (y.ofLp 2) S), w⟫ from
          funext fun y => by
            have hdiff : DifferentiableAt ℝ
                (fun z : E 3 => rotR (z.ofLp 0) (rotMFam a b (z.ofLp 1) (z.ofLp 2) S)) y :=
              differentiableAt_head_rotMFam false a b S y
            show (fderiv ℝ _ y) (EuclideanSpace.single 0 1) = _
            rw [fderiv_inner_const _ w y _ hdiff,
              fderiv_rotR_any_M_in_e0 S y (rotMFam a b) hdiff]]
        exact .base true a b
      · simp only [Bool.cond_true]
        rw [show GlobalTheorem.nth_partial 0
              (fun y : E 3 => ⟪rotR' (y.ofLp 0) (rotMFam a b (y.ofLp 1) (y.ofLp 2) S), w⟫)
            = fun y : E 3 =>
                -(⟪rotR (y.ofLp 0) (rotMFam a b (y.ofLp 1) (y.ofLp 2) S), w⟫ : ℝ) from
          funext fun y => by
            have hdiff : DifferentiableAt ℝ
                (fun z : E 3 => rotR' (z.ofLp 0) (rotMFam a b (z.ofLp 1) (z.ofLp 2) S)) y :=
              differentiableAt_head_rotMFam true a b S y
            show (fderiv ℝ _ y) (EuclideanSpace.single 0 1) = _
            rw [fderiv_inner_const _ w y _ hdiff,
              fderiv_rotR'_any_M_in_e0 S y (rotMFam a b) hdiff]
            exact inner_neg_left _ _]
        exact (IsRotDerivFam.base false a b).neg
    · -- θ-direction
      show IsRotDerivFam S w (GlobalTheorem.nth_partial 1
        (fun y : E 3 => ⟪(cond h' rotR' rotR) (y.ofLp 0)
          (rotMFam a b (y.ofLp 1) (y.ofLp 2) S), w⟫))
      rcases hs : famStep a with ⟨c, a'⟩
      cases c
      · rw [show GlobalTheorem.nth_partial 1
              (fun y : E 3 => ⟪(cond h' rotR' rotR) (y.ofLp 0)
                (rotMFam a b (y.ofLp 1) (y.ofLp 2) S), w⟫)
            = fun y : E 3 => ⟪(cond h' rotR' rotR) (y.ofLp 0)
                (rotMFam a' b (y.ofLp 1) (y.ofLp 2) S), w⟫ from
          funext fun y => by
            show (fderiv ℝ _ y) (EuclideanSpace.single 1 1) = _
            rw [fderiv_inner_const _ w y _ (differentiableAt_head_rotMFam h' a b S y),
              fderiv_head_family_in_e1 S y (cond h' rotR' rotR) (rotMFam a b) _
                (differentiableAt_head_rotMFam h' a b S y)
                (by simpa [hs] using rotMFam_hasDerivAt_θ a b (y.ofLp 1) (y.ofLp 2) S)]]
        exact .base h' a' b
      · rw [show GlobalTheorem.nth_partial 1
              (fun y : E 3 => ⟪(cond h' rotR' rotR) (y.ofLp 0)
                (rotMFam a b (y.ofLp 1) (y.ofLp 2) S), w⟫)
            = fun y : E 3 => -(⟪(cond h' rotR' rotR) (y.ofLp 0)
                (rotMFam a' b (y.ofLp 1) (y.ofLp 2) S), w⟫ : ℝ) from
          funext fun y => by
            show (fderiv ℝ _ y) (EuclideanSpace.single 1 1) = _
            rw [fderiv_inner_const _ w y _ (differentiableAt_head_rotMFam h' a b S y),
              fderiv_head_family_in_e1 S y (cond h' rotR' rotR) (rotMFam a b) _
                (differentiableAt_head_rotMFam h' a b S y)
                (by simpa [hs] using rotMFam_hasDerivAt_θ a b (y.ofLp 1) (y.ofLp 2) S),
              map_neg, inner_neg_left]]
        exact (IsRotDerivFam.base h' a' b).neg
    · -- φ-direction
      show IsRotDerivFam S w (GlobalTheorem.nth_partial 2
        (fun y : E 3 => ⟪(cond h' rotR' rotR) (y.ofLp 0)
          (rotMFam a b (y.ofLp 1) (y.ofLp 2) S), w⟫))
      rcases hs : famStep b with ⟨c, b'⟩
      cases c
      · rw [show GlobalTheorem.nth_partial 2
              (fun y : E 3 => ⟪(cond h' rotR' rotR) (y.ofLp 0)
                (rotMFam a b (y.ofLp 1) (y.ofLp 2) S), w⟫)
            = fun y : E 3 => ⟪(cond h' rotR' rotR) (y.ofLp 0)
                (rotMFam a b' (y.ofLp 1) (y.ofLp 2) S), w⟫ from
          funext fun y => by
            show (fderiv ℝ _ y) (EuclideanSpace.single 2 1) = _
            rw [fderiv_inner_const _ w y _ (differentiableAt_head_rotMFam h' a b S y),
              fderiv_head_family_in_e2 S y (cond h' rotR' rotR) (rotMFam a b) _
                (differentiableAt_head_rotMFam h' a b S y)
                (by simpa [hs] using rotMFam_hasDerivAt_φ a b (y.ofLp 1) (y.ofLp 2) S)]]
        exact .base h' a b'
      · rw [show GlobalTheorem.nth_partial 2
              (fun y : E 3 => ⟪(cond h' rotR' rotR) (y.ofLp 0)
                (rotMFam a b (y.ofLp 1) (y.ofLp 2) S), w⟫)
            = fun y : E 3 => -(⟪(cond h' rotR' rotR) (y.ofLp 0)
                (rotMFam a b' (y.ofLp 1) (y.ofLp 2) S), w⟫ : ℝ) from
          funext fun y => by
            show (fderiv ℝ _ y) (EuclideanSpace.single 2 1) = _
            rw [fderiv_inner_const _ w y _ (differentiableAt_head_rotMFam h' a b S y),
              fderiv_head_family_in_e2 S y (cond h' rotR' rotR) (rotMFam a b) _
                (differentiableAt_head_rotMFam h' a b S y)
                (by simpa [hs] using rotMFam_hasDerivAt_φ a b (y.ofLp 1) (y.ofLp 2) S),
              map_neg, inner_neg_left]]
        exact (IsRotDerivFam.base h' a b').neg

/-- `rotproj_inner` is the `(rotR, 0, 0)` member of the family. -/
lemma isRotDerivFam_rotproj_inner (S : ℝ³) (w : ℝ²) :
    IsRotDerivFam S w (rotproj_inner S w) := by
  rw [show rotproj_inner S w = fun y : E 3 =>
      ⟪(cond false rotR' rotR) (y.ofLp 0) (rotMFam 0 0 (y.ofLp 1) (y.ofLp 2) S), w⟫ from
    funext fun y => rotproj_inner_eq S w y]
  exact .base false 0 0

/-- Every family member is pointwise bounded by `‖S‖` (for unit `w`). -/
lemma IsRotDerivFam.abs_le {S : ℝ³} {w : ℝ²} {f : E 3 → ℝ}
    (hf : IsRotDerivFam S w f) (hw : ‖w‖ = 1) (y : E 3) : |f y| ≤ ‖S‖ := by
  induction hf with
  | base h' a b =>
    have hhead : ‖(cond h' rotR' rotR) (y.ofLp 0)‖ ≤ 1 := by
      cases h'
      · exact le_of_eq (Bounding.rotR_norm_one _)
      · exact le_of_eq (Bounding.rotR'_norm_one _)
    exact inner_bound_helper
      ((cond h' rotR' rotR) (y.ofLp 0) ∘L rotMFam a b (y.ofLp 1) (y.ofLp 2)) S w hw
      (comp_norm_le_one hhead (rotMFam_norm_le_one a b _ _))
  | neg _ ih => simpa using ih

/-- Family membership of every iterated partial of `rotproj_inner`. -/
lemma isRotDerivFam_foldr (S : ℝ³) (w : ℝ²) (ds : List (Fin 3)) :
    IsRotDerivFam S w (ds.foldr (fun i f => nth_partial i f) (rotproj_inner S w)) := by
  induction ds with
  | nil => exact isRotDerivFam_rotproj_inner S w
  | cons i ds ih => exact ih.nth_partial i

/-- Any-order bound: every iterated partial of `rotproj_inner` is bounded by
`‖S‖` (for unit `w`). -/
theorem rotproj_inner_iterated_partials_bounded (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1)
    (ds : List (Fin 3)) (y : ℝ³) :
    |(ds.foldr (fun i f => nth_partial i f) (rotproj_inner S w)) y| ≤ ‖S‖ :=
  (isRotDerivFam_foldr S w ds).abs_le w_unit y

/- [SY25] Lemma 19 (inner part) -/
theorem third_partial_inner_rotM_inner (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1)
    (i j k : Fin 3) (y : ℝ³) :
    |nth_partial i (nth_partial j (nth_partial k (rotproj_inner S w))) y| ≤ ‖S‖ :=
  ((((isRotDerivFam_rotproj_inner S w).nth_partial k).nth_partial j).nth_partial i).abs_le
    w_unit y

/- [SY25] Lemma 19 -/
theorem rotation_third_partials_bounded (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    third_partials_bounded (rotproj_inner S w) ‖S‖ := fun x i j k =>
  third_partial_inner_rotM_inner S w_unit i j k x

end GlobalTheorem

end
