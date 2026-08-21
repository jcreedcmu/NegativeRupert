/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Noperthedron.Global.RotationPartials.RotMOuter
public import Noperthedron.Global.Basic
public import Noperthedron.Global.SecondPartialHelpers

@[expose] public section


/-!
# Second Partial Outer Lemmas

This file contains:
- `outer_second_partial_A` definition and norm bound
- **`IsRotDerivFamOuter`**, the ∂-closed family of signed
  `⟪rotMFam a b (θ,φ) P, w⟫` functions
- **`rotation_third_partials_bounded_outer`** and the any-order bound
  `rotproj_outer_iterated_partials_bounded`, by iterating the closure
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-!
## The A[i,j] table for outer second partials

For the outer function (2 variables: θ, φ), we have:
| i\j |    0 (θ)        |    1 (φ)        |
|-----|-----------------|-----------------|
|  0  | rotMθθ θ φ      | rotMθφ θ φ      |
|  1  | rotMθφ θ φ      | rotMφφ θ φ      |

All have operator norm ≤ 1.
-/

/-- The operator A[i,j] for second partials of the outer rotation projection. -/
noncomputable def outer_second_partial_A (θ φ : ℝ) (i j : Fin 2) : ℝ³ →L[ℝ] ℝ² :=
  match i, j with
  | 0, 0 => rotMθθ θ φ
  | 0, 1 => rotMθφ θ φ
  | 1, 0 => rotMθφ θ φ
  | 1, 1 => rotMφφ θ φ

/-- All A[i,j] have operator norm ≤ 1 for outer partials. -/
lemma outer_second_partial_A_norm_le (θ φ : ℝ) (i j : Fin 2) :
    ‖outer_second_partial_A θ φ i j‖ ≤ 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [outer_second_partial_A, Bounding.rotMθθ_norm_le_one,
      Bounding.rotMθφ_norm_le_one, Bounding.rotMφφ_norm_le_one]

/-!
## Helper lemmas: partials of ⟪rotM S, w⟫ in coordinate directions
-/

private lemma outerPbar (x : E 2) : (⟨0, x.ofLp 0, 0, x.ofLp 1, 0⟩ : Pose ℝ).outerParams = x := by
  ext i; fin_cases i <;> simp [Pose.outerParams]

private lemma fderiv_rotM_outer_eq (S : ℝ³) (x : E 2) :
    fderiv ℝ (fun z => rotM (z.ofLp 0) (z.ofLp 1) S) x = rotM' ⟨0, x.ofLp 0, 0, x.ofLp 1, 0⟩ S :=
  (outerPbar x ▸ HasFDerivAt.rotM_outer _ S).fderiv

private lemma fderiv_rotMθ_outer_eq (S : ℝ³) (x : E 2) :
    fderiv ℝ (fun y => rotMθ (y.ofLp 0) (y.ofLp 1) S) x = rotMθ' ⟨0, x.ofLp 0, 0, x.ofLp 1, 0⟩ S :=
  (outerPbar x ▸ HasFDerivAt.rotMθ_outer _ S).fderiv

private lemma fderiv_rotMφ_outer_eq (S : ℝ³) (x : E 2) :
    fderiv ℝ (fun y => rotMφ (y.ofLp 0) (y.ofLp 1) S) x = rotMφ' ⟨0, x.ofLp 0, 0, x.ofLp 1, 0⟩ S :=
  (outerPbar x ▸ HasFDerivAt.rotMφ_outer _ S).fderiv

private lemma fderiv_rotM_inner_e0 (S : ℝ³) (w : ℝ²) (y : E 2) :
    (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
      (EuclideanSpace.single 0 1) = ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w y _ (Differentiable.rotM_outer S y), fderiv_rotM_outer_eq S y]
  congr 1; ext i; simp

private lemma fderiv_rotM_inner_e1 (S : ℝ³) (w : ℝ²) (y : E 2) :
    (fderiv ℝ (fun z => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫) y)
      (EuclideanSpace.single 1 1) = ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w y _ (Differentiable.rotM_outer S y), fderiv_rotM_outer_eq S y]
  congr 1; ext i; simp

private lemma fderiv_rotMθ_inner_e0 (S : ℝ³) (w : ℝ²) (x : E 2) :
    (fderiv ℝ (fun y => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
      (EuclideanSpace.single 0 1) = ⟪rotMθθ (x.ofLp 0) (x.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w x _ (differentiableAt_rotMθ_outer S x), fderiv_rotMθ_outer_eq S x]
  congr 1; ext i; simp

private lemma fderiv_rotMθ_inner_e1 (S : ℝ³) (w : ℝ²) (x : E 2) :
    (fderiv ℝ (fun y => ⟪rotMθ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
      (EuclideanSpace.single 1 1) = ⟪rotMθφ (x.ofLp 0) (x.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w x _ (differentiableAt_rotMθ_outer S x), fderiv_rotMθ_outer_eq S x]
  congr 1; ext i; simp

private lemma fderiv_rotMφ_inner_e0 (S : ℝ³) (w : ℝ²) (x : E 2) :
    (fderiv ℝ (fun y => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
      (EuclideanSpace.single 0 1) = ⟪rotMθφ (x.ofLp 0) (x.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w x _ (differentiableAt_rotMφ_outer S x), fderiv_rotMφ_outer_eq S x]
  congr 1; ext i; simp

private lemma fderiv_rotMφ_inner_e1 (S : ℝ³) (w : ℝ²) (x : E 2) :
    (fderiv ℝ (fun y => ⟪rotMφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
      (EuclideanSpace.single 1 1) = ⟪rotMφφ (x.ofLp 0) (x.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w x _ (differentiableAt_rotMφ_outer S x), fderiv_rotMφ_outer_eq S x]
  congr 1; ext i; simp

/-!
## Private lemma: second partials as inner products
-/

/-- The second partials of the outer projection are given pointwise by the
`outer_second_partial_A` table. -/
theorem second_partial_rotproj_outer_eq (S : ℝ³) (w : ℝ²) (x : E 2) (i j : Fin 2) :
    nth_partial i (nth_partial j (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫)) x =
      ⟪outer_second_partial_A (x.ofLp 0) (x.ofLp 1) i j S, w⟫ := by
  fin_cases i <;> fin_cases j <;> unfold nth_partial <;>
    simp [outer_second_partial_A, fderiv_rotM_inner_e0, fderiv_rotM_inner_e1,
      fderiv_rotMθ_inner_e0, fderiv_rotMθ_inner_e1, fderiv_rotMφ_inner_e0, fderiv_rotMφ_inner_e1]

/-- Function-level form of `second_partial_rotproj_outer_eq`. -/
theorem nth_partial_nth_partial_rotproj_outer (S : ℝ³) (w : ℝ²) (i j : Fin 2) :
    nth_partial i (nth_partial j (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫)) =
      fun y => ⟪outer_second_partial_A (y.ofLp 0) (y.ofLp 1) i j S, w⟫ :=
  funext fun y => second_partial_rotproj_outer_eq S w y i j

/-!
## Third and higher partials (outer): the ∂-closed family

Instead of enumerating the third-partial operators, we close the family
`± ⟪rotMFam a b (θ, φ) P, w⟫` under `nth_partial`: one derivative moves one
grid coordinate (`rotMFam_hasDerivAt_θ/φ`), folding back with a sign at the
edge.  Iterating gives the `≤ ‖P‖` bound at every order.
-/

/-- `nth_partial` commutes with pointwise negation (unconditionally, since
`fderiv` of a non-differentiable function is `0`). -/
lemma nth_partial_neg {n : ℕ} (f : E n → ℝ) (i : Fin n) :
    nth_partial i (fun y => -(f y)) = fun y => -(nth_partial i f y) := by
  funext y
  show fderiv ℝ (-f) y (EuclideanSpace.single i 1) = -(fderiv ℝ f y (EuclideanSpace.single i 1))
  rw [fderiv_neg]
  simp only [ContinuousLinearMap.neg_apply]

/-- Coordinate extraction in `E 2`: direction `e_i`, same coordinate (moves). -/
private lemma coord2_same (i : Fin 2) (y : E 2) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E 2)).ofLp i = y.ofLp i + t := by simp

/-- Coordinate extraction in `E 2`: direction `e_i`, different coordinate (fixed). -/
private lemma coord2_other {i j : Fin 2} (hij : j ≠ i) (y : E 2) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E 2)).ofLp j = y.ofLp j := by simp [hij]

/-- Joint differentiability of a grid member in the outer variables. -/
lemma differentiableAt_rotMFam_outer (a b : Fin 3) (S : ℝ³) (y : E 2) :
    DifferentiableAt ℝ (fun z : E 2 => rotMFam a b (z.ofLp 0) (z.ofLp 1) S) y := by
  fin_cases a <;> fin_cases b
  · exact (Differentiable.rotM_outer S).differentiableAt
  · exact differentiableAt_rotMφ_outer S y
  · exact differentiableAt_rotMφφ_outer S y
  · exact differentiableAt_rotMθ_outer S y
  · exact differentiableAt_rotMθφ_outer S y
  · exact differentiableAt_rotMθφφ_outer S y
  · exact differentiableAt_rotMθθ_outer S y
  · exact differentiableAt_rotMθθφ_outer S y
  · exact differentiableAt_rotMθθφφ_outer S y

/-- `nth_partial 0` (the θ-direction) of `⟪N (θ, φ) P, w⟫`, given the
θ-derivative of the two-parameter family `N`. -/
private lemma nth_partial_outer_e0 {P : ℝ³} {w : ℝ²} {N : ℝ → ℝ → ℝ³ →L[ℝ] ℝ²}
    {N' : ℝ²} {y : E 2}
    (hdiff : DifferentiableAt ℝ (fun z : E 2 => N (z.ofLp 0) (z.ofLp 1) P) y)
    (hN : HasDerivAt (fun t => N t (y.ofLp 1) P) N' (y.ofLp 0)) :
    nth_partial 0 (fun z : E 2 => ⟪N (z.ofLp 0) (z.ofLp 1) P, w⟫) y = ⟪N', w⟫ := by
  show (fderiv ℝ _ y) (EuclideanSpace.single 0 1) = _
  rw [fderiv_inner_const _ w y _ hdiff]
  congr 1
  refine fderiv_single_eq hdiff ?_
  simp only [coord2_same, coord2_other (by decide : (1 : Fin 2) ≠ 0)]
  exact hasDerivAt_comp_add _ _ _ hN

/-- `nth_partial 1` (the φ-direction) of `⟪N (θ, φ) P, w⟫`. -/
private lemma nth_partial_outer_e1 {P : ℝ³} {w : ℝ²} {N : ℝ → ℝ → ℝ³ →L[ℝ] ℝ²}
    {N' : ℝ²} {y : E 2}
    (hdiff : DifferentiableAt ℝ (fun z : E 2 => N (z.ofLp 0) (z.ofLp 1) P) y)
    (hN : HasDerivAt (fun t => N (y.ofLp 0) t P) N' (y.ofLp 1)) :
    nth_partial 1 (fun z : E 2 => ⟪N (z.ofLp 0) (z.ofLp 1) P, w⟫) y = ⟪N', w⟫ := by
  show (fderiv ℝ _ y) (EuclideanSpace.single 1 1) = _
  rw [fderiv_inner_const _ w y _ hdiff]
  congr 1
  refine fderiv_single_eq hdiff ?_
  simp only [coord2_same, coord2_other (by decide : (0 : Fin 2) ≠ 1)]
  exact hasDerivAt_comp_add _ _ _ hN

/-- The ∂-closed family of outer scalar functions: `⟪∂θᵃ∂φᵇ M(θ,φ) P, w⟫` up
to sign. -/
inductive IsRotDerivFamOuter (P : ℝ³) (w : ℝ²) : (E 2 → ℝ) → Prop where
  | base (a b : Fin 3) :
      IsRotDerivFamOuter P w (fun y => ⟪rotMFam a b (y.ofLp 0) (y.ofLp 1) P, w⟫)
  | neg {f} : IsRotDerivFamOuter P w f → IsRotDerivFamOuter P w (fun y => -(f y))

/-- The outer family is closed under partial derivatives: one `nth_partial`
moves one grid coordinate (with a sign at the fold). -/
lemma IsRotDerivFamOuter.nth_partial {P : ℝ³} {w : ℝ²} {f : E 2 → ℝ}
    (hf : IsRotDerivFamOuter P w f) (i : Fin 2) :
    IsRotDerivFamOuter P w (nth_partial i f) := by
  induction hf with
  | neg _ ih => rw [nth_partial_neg]; exact ih.neg
  | base a b =>
    fin_cases i
    · -- θ-direction
      show IsRotDerivFamOuter P w
        (GlobalTheorem.nth_partial 0 (fun y : E 2 => ⟪rotMFam a b (y.ofLp 0) (y.ofLp 1) P, w⟫))
      rcases hs : famStep a with ⟨c, a'⟩
      cases c
      · rw [show GlobalTheorem.nth_partial 0 (fun y : E 2 => ⟪rotMFam a b (y.ofLp 0) (y.ofLp 1) P, w⟫)
              = fun y : E 2 => ⟪rotMFam a' b (y.ofLp 0) (y.ofLp 1) P, w⟫ from funext fun y =>
            nth_partial_outer_e0 (differentiableAt_rotMFam_outer a b P y)
              (by simpa [hs] using rotMFam_hasDerivAt_θ a b (y.ofLp 0) (y.ofLp 1) P)]
        exact .base a' b
      · rw [show GlobalTheorem.nth_partial 0 (fun y : E 2 => ⟪rotMFam a b (y.ofLp 0) (y.ofLp 1) P, w⟫)
              = fun y : E 2 => -(⟪rotMFam a' b (y.ofLp 0) (y.ofLp 1) P, w⟫ : ℝ) from
            funext fun y => by
              rw [nth_partial_outer_e0 (differentiableAt_rotMFam_outer a b P y)
                (by simpa [hs] using rotMFam_hasDerivAt_θ a b (y.ofLp 0) (y.ofLp 1) P)]
              exact inner_neg_left _ _]
        exact (IsRotDerivFamOuter.base a' b).neg
    · -- φ-direction
      show IsRotDerivFamOuter P w
        (GlobalTheorem.nth_partial 1 (fun y : E 2 => ⟪rotMFam a b (y.ofLp 0) (y.ofLp 1) P, w⟫))
      rcases hs : famStep b with ⟨c, b'⟩
      cases c
      · rw [show GlobalTheorem.nth_partial 1 (fun y : E 2 => ⟪rotMFam a b (y.ofLp 0) (y.ofLp 1) P, w⟫)
              = fun y : E 2 => ⟪rotMFam a b' (y.ofLp 0) (y.ofLp 1) P, w⟫ from funext fun y =>
            nth_partial_outer_e1 (differentiableAt_rotMFam_outer a b P y)
              (by simpa [hs] using rotMFam_hasDerivAt_φ a b (y.ofLp 0) (y.ofLp 1) P)]
        exact .base a b'
      · rw [show GlobalTheorem.nth_partial 1 (fun y : E 2 => ⟪rotMFam a b (y.ofLp 0) (y.ofLp 1) P, w⟫)
              = fun y : E 2 => -(⟪rotMFam a b' (y.ofLp 0) (y.ofLp 1) P, w⟫ : ℝ) from
            funext fun y => by
              rw [nth_partial_outer_e1 (differentiableAt_rotMFam_outer a b P y)
                (by simpa [hs] using rotMFam_hasDerivAt_φ a b (y.ofLp 0) (y.ofLp 1) P)]
              exact inner_neg_left _ _]
        exact (IsRotDerivFamOuter.base a b').neg

/-- Every member of the outer family is bounded by `‖P‖` (for unit `w`). -/
lemma IsRotDerivFamOuter.abs_le {P : ℝ³} {w : ℝ²} {f : E 2 → ℝ}
    (hf : IsRotDerivFamOuter P w f) (hw : ‖w‖ = 1) (y : E 2) : |f y| ≤ ‖P‖ := by
  induction hf with
  | base a b =>
    exact inner_bound_helper _ P w hw (rotMFam_norm_le_one a b _ _)
  | neg _ ih => simpa using ih

/-- `rotproj_outer` is the `(0,0)` member of the outer family. -/
lemma isRotDerivFamOuter_rotproj_outer (S : ℝ³) (w : ℝ²) :
    IsRotDerivFamOuter S w (rotproj_outer S w) :=
  IsRotDerivFamOuter.base 0 0

/-- The outer family membership of every iterated partial of `rotproj_outer`. -/
lemma isRotDerivFamOuter_foldr (S : ℝ³) (w : ℝ²) (ds : List (Fin 2)) :
    IsRotDerivFamOuter S w (ds.foldr (fun i f => nth_partial i f) (rotproj_outer S w)) := by
  induction ds with
  | nil => exact isRotDerivFamOuter_rotproj_outer S w
  | cons i ds ih => exact ih.nth_partial i

/-- Any-order bound: every iterated partial of `rotproj_outer` is bounded by
`‖S‖` (for unit `w`). -/
theorem rotproj_outer_iterated_partials_bounded (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1)
    (ds : List (Fin 2)) (y : E 2) :
    |(ds.foldr (fun i f => nth_partial i f) (rotproj_outer S w)) y| ≤ ‖S‖ :=
  (isRotDerivFamOuter_foldr S w ds).abs_le w_unit y

theorem third_partial_inner_rotM_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1)
    (i j k : Fin 2) (y : ℝ²) :
    |nth_partial i (nth_partial j (nth_partial k (rotproj_outer S w))) y| ≤ ‖S‖ :=
  ((((isRotDerivFamOuter_rotproj_outer S w).nth_partial k).nth_partial j).nth_partial i).abs_le
    w_unit y

theorem rotation_third_partials_bounded_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    third_partials_bounded (rotproj_outer S w) ‖S‖ := fun x i j k =>
  third_partial_inner_rotM_outer S w_unit i j k x

end GlobalTheorem

end
