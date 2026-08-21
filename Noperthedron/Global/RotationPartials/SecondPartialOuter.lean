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
- **`third_partial_inner_rotM_outer`** (8 cases)
- **`rotation_third_partials_bounded_outer`**
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
## Third partials (outer)

Differentiating the `outer_second_partial_A` table once more.  Only 4 distinct
values occur: -rotMθ, rotMθθφ, rotMθφφ, -rotMφ (using Mθθθ = -Mθ, Mφφφ = -Mφ).
-/

private lemma fderiv_rotMθθ_outer_eq (S : ℝ³) (x : E 2) :
    fderiv ℝ (fun y => rotMθθ (y.ofLp 0) (y.ofLp 1) S) x = rotMθθ' ⟨0, x.ofLp 0, 0, x.ofLp 1, 0⟩ S :=
  (outerPbar x ▸ HasFDerivAt.rotMθθ_outer _ S).fderiv

private lemma fderiv_rotMθφ_outer_eq (S : ℝ³) (x : E 2) :
    fderiv ℝ (fun y => rotMθφ (y.ofLp 0) (y.ofLp 1) S) x = rotMθφ' ⟨0, x.ofLp 0, 0, x.ofLp 1, 0⟩ S :=
  (outerPbar x ▸ HasFDerivAt.rotMθφ_outer _ S).fderiv

private lemma fderiv_rotMφφ_outer_eq (S : ℝ³) (x : E 2) :
    fderiv ℝ (fun y => rotMφφ (y.ofLp 0) (y.ofLp 1) S) x = rotMφφ' ⟨0, x.ofLp 0, 0, x.ofLp 1, 0⟩ S :=
  (outerPbar x ▸ HasFDerivAt.rotMφφ_outer _ S).fderiv

private lemma fderiv_rotMθθ_inner_e0 (S : ℝ³) (w : ℝ²) (x : E 2) :
    (fderiv ℝ (fun y => ⟪rotMθθ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
      (EuclideanSpace.single 0 1) = ⟪-(rotMθ (x.ofLp 0) (x.ofLp 1) S), w⟫ := by
  rw [fderiv_inner_const _ w x _ (differentiableAt_rotMθθ_outer S x), fderiv_rotMθθ_outer_eq S x]
  congr 1; ext i; simp

private lemma fderiv_rotMθθ_inner_e1 (S : ℝ³) (w : ℝ²) (x : E 2) :
    (fderiv ℝ (fun y => ⟪rotMθθ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
      (EuclideanSpace.single 1 1) = ⟪rotMθθφ (x.ofLp 0) (x.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w x _ (differentiableAt_rotMθθ_outer S x), fderiv_rotMθθ_outer_eq S x]
  congr 1; ext i; simp

private lemma fderiv_rotMθφ_inner_e0 (S : ℝ³) (w : ℝ²) (x : E 2) :
    (fderiv ℝ (fun y => ⟪rotMθφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
      (EuclideanSpace.single 0 1) = ⟪rotMθθφ (x.ofLp 0) (x.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w x _ (differentiableAt_rotMθφ_outer S x), fderiv_rotMθφ_outer_eq S x]
  congr 1; ext i; simp

private lemma fderiv_rotMθφ_inner_e1 (S : ℝ³) (w : ℝ²) (x : E 2) :
    (fderiv ℝ (fun y => ⟪rotMθφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
      (EuclideanSpace.single 1 1) = ⟪rotMθφφ (x.ofLp 0) (x.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w x _ (differentiableAt_rotMθφ_outer S x), fderiv_rotMθφ_outer_eq S x]
  congr 1; ext i; simp

private lemma fderiv_rotMφφ_inner_e0 (S : ℝ³) (w : ℝ²) (x : E 2) :
    (fderiv ℝ (fun y => ⟪rotMφφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
      (EuclideanSpace.single 0 1) = ⟪rotMθφφ (x.ofLp 0) (x.ofLp 1) S, w⟫ := by
  rw [fderiv_inner_const _ w x _ (differentiableAt_rotMφφ_outer S x), fderiv_rotMφφ_outer_eq S x]
  congr 1; ext i; simp

private lemma fderiv_rotMφφ_inner_e1 (S : ℝ³) (w : ℝ²) (x : E 2) :
    (fderiv ℝ (fun y => ⟪rotMφφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x)
      (EuclideanSpace.single 1 1) = ⟪-(rotMφ (x.ofLp 0) (x.ofLp 1) S), w⟫ := by
  rw [fderiv_inner_const _ w x _ (differentiableAt_rotMφφ_outer S x), fderiv_rotMφφ_outer_eq S x]
  congr 1; ext i; simp

/-- The operator A₃[i,j,k] for third partials of the outer rotation projection:
the ∂ᵢ-derivative of `outer_second_partial_A · · j k`. -/
noncomputable def outer_third_partial_A (θ φ : ℝ) (i j k : Fin 2) : ℝ³ →L[ℝ] ℝ² :=
  match i, j, k with
  | 0, 0, 0 => -(rotMθ θ φ)
  | 1, 0, 0 => rotMθθφ θ φ
  | 0, 0, 1 => rotMθθφ θ φ
  | 1, 0, 1 => rotMθφφ θ φ
  | 0, 1, 0 => rotMθθφ θ φ
  | 1, 1, 0 => rotMθφφ θ φ
  | 0, 1, 1 => rotMθφφ θ φ
  | 1, 1, 1 => -(rotMφ θ φ)

/-- All outer A₃[i,j,k] have operator norm ≤ 1. -/
lemma outer_third_partial_A_norm_le (θ φ : ℝ) (i j k : Fin 2) :
    ‖outer_third_partial_A θ φ i j k‖ ≤ 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [outer_third_partial_A, norm_neg, Bounding.rotMθ_norm_le_one,
      Bounding.rotMφ_norm_le_one, Bounding.rotMθθφ_norm_le_one, Bounding.rotMθφφ_norm_le_one]

theorem third_partial_rotproj_outer_eq (S : ℝ³) (w : ℝ²) (x : E 2) (i j k : Fin 2) :
    nth_partial i (nth_partial j (nth_partial k
        (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫))) x =
      ⟪outer_third_partial_A (x.ofLp 0) (x.ofLp 1) i j k S, w⟫ := by
  fin_cases j <;> fin_cases k
  · -- column (0,0): A₂ = rotMθθ
    show nth_partial i (nth_partial 0 (nth_partial 0
      (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫))) x =
      ⟪outer_third_partial_A (x.ofLp 0) (x.ofLp 1) i 0 0 S, w⟫
    rw [nth_partial_nth_partial_rotproj_outer S w 0 0]
    show nth_partial i (fun y => ⟪rotMθθ (y.ofLp 0) (y.ofLp 1) S, w⟫) x = _
    unfold nth_partial
    fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
    · rw [fderiv_rotMθθ_inner_e0 S w x]
      simp only [outer_third_partial_A, neg_apply, inner_neg_left]
    · rw [fderiv_rotMθθ_inner_e1 S w x]; rfl
  · -- column (0,1): A₂ = rotMθφ
    show nth_partial i (nth_partial 0 (nth_partial 1
      (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫))) x =
      ⟪outer_third_partial_A (x.ofLp 0) (x.ofLp 1) i 0 1 S, w⟫
    rw [nth_partial_nth_partial_rotproj_outer S w 0 1]
    show nth_partial i (fun y => ⟪rotMθφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x = _
    unfold nth_partial
    fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
    · rw [fderiv_rotMθφ_inner_e0 S w x]; rfl
    · rw [fderiv_rotMθφ_inner_e1 S w x]; rfl
  · -- column (1,0): A₂ = rotMθφ (mixed-partial symmetry)
    show nth_partial i (nth_partial 1 (nth_partial 0
      (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫))) x =
      ⟪outer_third_partial_A (x.ofLp 0) (x.ofLp 1) i 1 0 S, w⟫
    rw [nth_partial_nth_partial_rotproj_outer S w 1 0]
    show nth_partial i (fun y => ⟪rotMθφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x = _
    unfold nth_partial
    fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
    · rw [fderiv_rotMθφ_inner_e0 S w x]; rfl
    · rw [fderiv_rotMθφ_inner_e1 S w x]; rfl
  · -- column (1,1): A₂ = rotMφφ
    show nth_partial i (nth_partial 1 (nth_partial 1
      (fun y : E 2 => ⟪rotM (y.ofLp 0) (y.ofLp 1) S, w⟫))) x =
      ⟪outer_third_partial_A (x.ofLp 0) (x.ofLp 1) i 1 1 S, w⟫
    rw [nth_partial_nth_partial_rotproj_outer S w 1 1]
    show nth_partial i (fun y => ⟪rotMφφ (y.ofLp 0) (y.ofLp 1) S, w⟫) x = _
    unfold nth_partial
    fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
    · rw [fderiv_rotMφφ_inner_e0 S w x]; rfl
    · rw [fderiv_rotMφφ_inner_e1 S w x]
      simp only [outer_third_partial_A, neg_apply, inner_neg_left]

theorem third_partial_inner_rotM_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1)
    (i j k : Fin 2) (y : ℝ²) :
    |nth_partial i (nth_partial j (nth_partial k (rotproj_outer S w))) y| ≤ ‖S‖ := by
  rw [show rotproj_outer S w = fun z : E 2 => ⟪rotM (z.ofLp 0) (z.ofLp 1) S, w⟫ from rfl,
    third_partial_rotproj_outer_eq S w y i j k]
  exact inner_bound_helper _ S w w_unit (outer_third_partial_A_norm_le _ _ i j k)

theorem rotation_third_partials_bounded_outer (S : ℝ³) {w : ℝ²} (w_unit : ‖w‖ = 1) :
    third_partials_bounded (rotproj_outer S w) ‖S‖ := fun x i j k =>
  third_partial_inner_rotM_outer S w_unit i j k x

end GlobalTheorem

end
