/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Noperthedron.Global.RotationDerivs
public import Noperthedron.Bounding.OpNorm

@[expose] public section


/-!
# Second Partial Helper Lemmas

Helper lemmas for second partial derivative computations in Global.lean.

These lemmas factor out repeated DifferentiableAt proofs and first partial
computations to reduce heartbeat usage in third_partial_inner_rotM_inner.
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-!
## DifferentiableAt lemmas for rotation compositions

These lemmas eliminate the repeated `rw [differentiableAt_piLp]; intro i; fin_cases i ...`
pattern that appears ~30+ times in third_partial_inner_rotM_inner.
-/

/-- DifferentiableAt for rotMθ (outer, E 2) -/
lemma differentiableAt_rotMθ_outer (S : ℝ³) (y : E 2) :
    DifferentiableAt ℝ (fun z : E 2 => rotMθ (z.ofLp 0) (z.ofLp 1) S) y := by
  rw [differentiableAt_piLp]; intro i
  simp only [rotMθ, rotMθ_mat, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply]
  fin_cases i <;> (simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotMφ (outer, E 2) -/
lemma differentiableAt_rotMφ_outer (S : ℝ³) (y : E 2) :
    DifferentiableAt ℝ (fun z : E 2 => rotMφ (z.ofLp 0) (z.ofLp 1) S) y := by
  rw [differentiableAt_piLp]; intro i
  simp only [rotMφ, rotMφ_mat, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply]
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop

/-- DifferentiableAt for rotMθθ (outer, E 2) -/
lemma differentiableAt_rotMθθ_outer (S : ℝ³) (y : E 2) :
    DifferentiableAt ℝ (fun z : E 2 => rotMθθ (z.ofLp 0) (z.ofLp 1) S) y := by
  rw [differentiableAt_piLp]; intro i
  simp only [rotMθθ, rotMθθ_mat, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply]
  fin_cases i <;> (simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotMθφ (outer, E 2) -/
lemma differentiableAt_rotMθφ_outer (S : ℝ³) (y : E 2) :
    DifferentiableAt ℝ (fun z : E 2 => rotMθφ (z.ofLp 0) (z.ofLp 1) S) y := by
  rw [differentiableAt_piLp]; intro i
  simp only [rotMθφ, rotMθφ_mat, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply]
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop

/-- DifferentiableAt for rotMφφ (outer, E 2) -/
lemma differentiableAt_rotMφφ_outer (S : ℝ³) (y : E 2) :
    DifferentiableAt ℝ (fun z : E 2 => rotMφφ (z.ofLp 0) (z.ofLp 1) S) y := by
  rw [differentiableAt_piLp]; intro i
  simp only [rotMφφ, rotMφφ_mat, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply]
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; fun_prop

/-- DifferentiableAt for rotR ∘ rotM -/
lemma differentiableAt_rotR_rotM (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR, rotR_mat, rotM, rotM_mat, Matrix.toLpLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR' ∘ rotM -/
lemma differentiableAt_rotR'_rotM (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR', rotR'_mat, rotM, rotM_mat, Matrix.toLpLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR ∘ rotMθ -/
lemma differentiableAt_rotR_rotMθ (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR, rotR_mat, rotMθ, rotMθ_mat, Matrix.toLpLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR ∘ rotMφ -/
lemma differentiableAt_rotR_rotMφ (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR, rotR_mat, rotMφ, rotMφ_mat, Matrix.toLpLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR' ∘ rotMθ -/
lemma differentiableAt_rotR'_rotMθ (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR', rotR'_mat, rotMθ, rotMθ_mat, Matrix.toLpLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR' ∘ rotMφ -/
lemma differentiableAt_rotR'_rotMφ (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR', rotR'_mat, rotMφ, rotMφ_mat, Matrix.toLpLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR ∘ rotMθθ -/
lemma differentiableAt_rotR_rotMθθ (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMθθ (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR, rotR_mat, rotMθθ, rotMθθ_mat, Matrix.toLpLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR ∘ rotMθφ -/
lemma differentiableAt_rotR_rotMθφ (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMθφ (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR, rotR_mat, rotMθφ, rotMθφ_mat, Matrix.toLpLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-- DifferentiableAt for rotR ∘ rotMφφ -/
lemma differentiableAt_rotR_rotMφφ (S : ℝ³) (y : E 3) :
    DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφφ (z.ofLp 1) (z.ofLp 2) S)) y := by
  rw [differentiableAt_piLp]; intro i
  fin_cases i <;> (simp [rotR, rotR_mat, rotMφφ, rotMφφ_mat, Matrix.toLpLin_apply,
    Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_three]; fun_prop)

/-!
## Inner product fderiv helper

This lemma factors out the repeated pattern:
```
have hInner := fderiv_inner_apply ℝ hf_diff (differentiableAt_const w) (e_i)
have hw := hasFDerivAt_const w y
rw [hw.fderiv] at hInner
simp only [ContinuousLinearMap.zero_apply, inner_zero_right, zero_add] at hInner
```

The result is: `fderiv (⟪f·, w⟫) y d = ⟪fderiv f y d, w⟫` when `w` is constant.
-/

/-- fderiv of inner product with constant second argument equals inner product of fderiv -/
lemma fderiv_inner_const {n : ℕ} (f : E n → ℝ²) (w : ℝ²) (y : E n) (d : E n)
    (hf : DifferentiableAt ℝ f y) :
    (fderiv ℝ (fun z => ⟪f z, w⟫) y) d = ⟪(fderiv ℝ f y) d, w⟫ := by
  simpa [(hasFDerivAt_const w y).fderiv] using fderiv_inner_apply ℝ hf (differentiableAt_const w) d

/-- |⟪A S, w⟫ / ‖S‖| ≤ 1 when ‖A‖ ≤ 1 and ‖w‖ = 1 -/
lemma inner_bound_helper (A : ℝ³ →L[ℝ] ℝ²) (S : ℝ³) (w : ℝ²)
    (hw : ‖w‖ = 1) (hA : ‖A‖ ≤ 1) : |⟪A S, w⟫| ≤ ‖S‖ := by
  calc |⟪A S, w⟫|
    _ ≤ ‖A S‖ * ‖w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖A‖ * ‖S‖ * ‖w‖ := by
        apply mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ 1 * ‖S‖ * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hA (norm_nonneg _)) (le_of_eq hw)
          (norm_nonneg _)
        positivity
    _ = ‖S‖ := by ring

/-!
## Coordinate extraction lemmas

These factor out the repeated `(y + t • EuclideanSpace.single k 1).ofLp j` simplifications.
-/

/-- Coordinate extraction: direction e_i, same coordinate (moves) -/
lemma coord_ei_same (i : Fin 3) (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E 3)).ofLp i = y.ofLp i + t := by
  simp

/-- Coordinate extraction: direction e_i, different coordinate j (fixed) -/
@[simp]
lemma coord_ei_at_other (i j : Fin 3) (hij : j ≠ i) (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E 3)).ofLp j = y.ofLp j := by
  simp [hij]

/-- Shorthand for coord_ei_same 0 -/
abbrev coord_e0_same := coord_ei_same 0
/-- Shorthand for coord_ei_same 1 -/
abbrev coord_e1_same := coord_ei_same 1
/-- Shorthand for coord_ei_same 2 -/
abbrev coord_e2_same := coord_ei_same 2

@[simp]
lemma coord_e0_at1 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (0 : Fin 3) 1 : E 3)).ofLp 1 = y.ofLp 1 :=
  coord_ei_at_other 0 1 (by decide) y t

@[simp]
lemma coord_e0_at2 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (0 : Fin 3) 1 : E 3)).ofLp 2 = y.ofLp 2 :=
  coord_ei_at_other 0 2 (by decide) y t

@[simp]
lemma coord_e1_at0 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (1 : Fin 3) 1 : E 3)).ofLp 0 = y.ofLp 0 :=
  coord_ei_at_other 1 0 (by decide) y t

@[simp]
lemma coord_e1_at2 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (1 : Fin 3) 1 : E 3)).ofLp 2 = y.ofLp 2 :=
  coord_ei_at_other 1 2 (by decide) y t

@[simp]
lemma coord_e2_at0 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (2 : Fin 3) 1 : E 3)).ofLp 0 = y.ofLp 0 :=
  coord_ei_at_other 2 0 (by decide) y t

@[simp]
lemma coord_e2_at1 (y : E 3) (t : ℝ) :
    (y + t • (EuclideanSpace.single (2 : Fin 3) 1 : E 3)).ofLp 1 = y.ofLp 1 :=
  coord_ei_at_other 2 1 (by decide) y t

/-!
## Directional fderiv lemmas for second partials

These factor out the lineDeriv_eq_fderiv + HasLineDerivAt pattern.
-/

/-- Helper for deriv → fderiv composition pattern -/
lemma hasDerivAt_comp_add (f : ℝ → ℝ²) (f' : ℝ²) (a : ℝ) (hf : HasDerivAt f f' a) :
    HasDerivAt (fun t => f (a + t)) f' 0 :=
  HasDerivAt.comp_const_add a 0 (by simpa using hf)

/-- For a differentiable function, the `fderiv` along a basis direction can be computed
as the one-variable derivative along the line through that direction. -/
lemma fderiv_single_eq {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E n → F} {y : E n} {i : Fin n} {d : F}
    (hdiff : DifferentiableAt ℝ f y)
    (hline : HasDerivAt (fun t : ℝ => f (y + t • EuclideanSpace.single i 1)) d 0) :
    fderiv ℝ f y (EuclideanSpace.single i 1) = d := by
  rw [← hdiff.lineDeriv_eq_fderiv]
  exact HasLineDerivAt.lineDeriv hline

/-- The continuous linear map `E n →L[ℝ] ℝ²` with prescribed values on the standard basis. -/
noncomputable def columnsCLM {n : ℕ} (cols : Fin n → ℝ²) : E n →L[ℝ] ℝ² :=
  (Matrix.of fun i j => (cols j) i).toEuclideanLin.toContinuousLinearMap

@[simp]
lemma columnsCLM_single {n : ℕ} (cols : Fin n → ℝ²) (i : Fin n) :
    columnsCLM cols (EuclideanSpace.single i 1) = cols i := by
  ext k
  simp [columnsCLM]

/-- A differentiable map whose directional derivatives along the standard basis are
`cols i` has Fréchet derivative `columnsCLM cols`. -/
lemma hasFDerivAt_of_partials {n : ℕ} {f : E n → ℝ²} {y : E n} (cols : Fin n → ℝ²)
    (hdiff : DifferentiableAt ℝ f y)
    (h : ∀ i, HasDerivAt (fun t : ℝ => f (y + t • EuclideanSpace.single i 1)) (cols i) 0) :
    HasFDerivAt f (columnsCLM cols) y := by
  have hfd : fderiv ℝ f y = columnsCLM cols := by
    refine ContinuousLinearMap.coe_injective
      ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext fun i => ?_)
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      ContinuousLinearMap.coe_coe, columnsCLM_single]
    exact fderiv_single_eq hdiff (h i)
  exact hfd ▸ hdiff.hasFDerivAt

/-- fderiv of a composition `z ↦ X (z 0) (N (z 1) (z 2) S)` in direction e₁,
given the derivative of the matrix family `N` in its first (θ) argument.
The head `X` is arbitrary since e₁ does not move the `z 0` coordinate. -/
lemma fderiv_head_family_in_e1 (S : ℝ³) (y : E 3) (X : ℝ → ℝ² →L[ℝ] ℝ²)
    (N : ℝ → ℝ → ℝ³ →L[ℝ] ℝ²) (N' : ℝ²)
    (hdiff : DifferentiableAt ℝ (fun z : E 3 => X (z.ofLp 0) (N (z.ofLp 1) (z.ofLp 2) S)) y)
    (hN : HasDerivAt (fun t => N t (y.ofLp 2) S) N' (y.ofLp 1)) :
    (fderiv ℝ (fun z : E 3 => X (z.ofLp 0) (N (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) = X (y.ofLp 0) N' := by
  refine fderiv_single_eq hdiff ?_
  simp only [coord_e1_at0, coord_e1_same, coord_e1_at2]
  exact hasDerivAt_comp_add _ _ _
    ((ContinuousLinearMap.hasFDerivAt (X (y.ofLp 0))).comp_hasDerivAt _ hN)

/-- fderiv of a composition `z ↦ X (z 0) (N (z 1) (z 2) S)` in direction e₂,
given the derivative of the matrix family `N` in its second (φ) argument. -/
lemma fderiv_head_family_in_e2 (S : ℝ³) (y : E 3) (X : ℝ → ℝ² →L[ℝ] ℝ²)
    (N : ℝ → ℝ → ℝ³ →L[ℝ] ℝ²) (N' : ℝ²)
    (hdiff : DifferentiableAt ℝ (fun z : E 3 => X (z.ofLp 0) (N (z.ofLp 1) (z.ofLp 2) S)) y)
    (hN : HasDerivAt (fun t => N (y.ofLp 1) t S) N' (y.ofLp 2)) :
    (fderiv ℝ (fun z : E 3 => X (z.ofLp 0) (N (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 2 1) = X (y.ofLp 0) N' := by
  refine fderiv_single_eq hdiff ?_
  simp only [coord_e2_at0, coord_e2_at1, coord_e2_same]
  exact hasDerivAt_comp_add _ _ _
    ((ContinuousLinearMap.hasFDerivAt (X (y.ofLp 0))).comp_hasDerivAt _ hN)

/-- fderiv of rotR ∘ rotMθ in direction e1 gives rotR ∘ rotMθθ -/
lemma fderiv_rotR_rotMθ_in_e1 (S : ℝ³) (y : E 3) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) =
    rotR (y.ofLp 0) (rotMθθ (y.ofLp 1) (y.ofLp 2) S) := by
  refine fderiv_single_eq (differentiableAt_rotR_rotMθ S y) ?_
  simp only [coord_e1_at0, coord_e1_same, coord_e1_at2]
  exact hasDerivAt_comp_add _ _ _
    ((ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))).comp_hasDerivAt _
      (hasDerivAt_rotMθ_θ (y.ofLp 1) (y.ofLp 2) S))

/-- fderiv of rotR ∘ rotMθ in direction e2 gives rotR ∘ rotMθφ -/
lemma fderiv_rotR_rotMθ_in_e2 (S : ℝ³) (y : E 3) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMθ (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 2 1) =
    rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S) := by
  refine fderiv_single_eq (differentiableAt_rotR_rotMθ S y) ?_
  simp only [coord_e2_at0, coord_e2_at1, coord_e2_same]
  exact hasDerivAt_comp_add _ _ _
    ((ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))).comp_hasDerivAt _
      (hasDerivAt_rotMθ_φ (y.ofLp 1) (y.ofLp 2) S))

/-- fderiv of rotR ∘ rotMφ in direction e1 gives rotR ∘ rotMθφ -/
lemma fderiv_rotR_rotMφ_in_e1 (S : ℝ³) (y : E 3) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) =
    rotR (y.ofLp 0) (rotMθφ (y.ofLp 1) (y.ofLp 2) S) := by
  refine fderiv_single_eq (differentiableAt_rotR_rotMφ S y) ?_
  simp only [coord_e1_at0, coord_e1_same, coord_e1_at2]
  exact hasDerivAt_comp_add _ _ _
    ((ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))).comp_hasDerivAt _
      (hasDerivAt_rotMφ_θ (y.ofLp 1) (y.ofLp 2) S))

/-- fderiv of rotR ∘ rotMφ in direction e2 gives rotR ∘ rotMφφ -/
lemma fderiv_rotR_rotMφ_in_e2 (S : ℝ³) (y : E 3) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotMφ (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 2 1) =
    rotR (y.ofLp 0) (rotMφφ (y.ofLp 1) (y.ofLp 2) S) := by
  refine fderiv_single_eq (differentiableAt_rotR_rotMφ S y) ?_
  simp only [coord_e2_at0, coord_e2_at1, coord_e2_same]
  exact hasDerivAt_comp_add _ _ _
    ((ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))).comp_hasDerivAt _
      (hasDerivAt_rotMφ_φ (y.ofLp 1) (y.ofLp 2) S))

/-!
## A[i,j] Table for Second Partials

This defines the operator A_{i,j}(α, θ, φ) such that
  ∂²(rotproj_inner S w)/∂x_i∂x_j = ⟪A_{i,j} S, w⟫

where x₀ = α, x₁ = θ, x₂ = φ.

The table is:
| i\j |    0                    |    1                  |    2                  |
|-----|-------------------------|-----------------------|-----------------------|
|  0  | -(rotR α ∘L rotM θ φ)   | rotR' α ∘L rotMθ θ φ  | rotR' α ∘L rotMφ θ φ  |
|  1  | rotR' α ∘L rotMθ θ φ    | rotR α ∘L rotMθθ θ φ  | rotR α ∘L rotMθφ θ φ  |
|  2  | rotR' α ∘L rotMφ θ φ    | rotR α ∘L rotMθφ θ φ  | rotR α ∘L rotMφφ θ φ  |

All have operator norm ≤ 1 since ‖rotR‖ = ‖rotR'‖ = 1 and ‖rotM*‖ ≤ 1.
-/

/-- The operator A[i,j] for second partials of the inner rotation projection.
    Returns the composition that appears in ⟪A S, w⟫. -/
noncomputable def inner_second_partial_A (α θ φ : ℝ) (i j : Fin 3) : ℝ³ →L[ℝ] ℝ² :=
  match i, j with
  | 0, 0 => -(rotR α ∘L rotM θ φ)
  | 0, 1 => rotR' α ∘L rotMθ θ φ
  | 0, 2 => rotR' α ∘L rotMφ θ φ
  | 1, 0 => rotR' α ∘L rotMθ θ φ   -- = A[0,1] by mixed partial symmetry
  | 1, 1 => rotR α ∘L rotMθθ θ φ
  | 1, 2 => rotR α ∘L rotMθφ θ φ
  | 2, 0 => rotR' α ∘L rotMφ θ φ   -- = A[0,2] by mixed partial symmetry
  | 2, 1 => rotR α ∘L rotMθφ θ φ   -- = A[1,2] by mixed partial symmetry
  | 2, 2 => rotR α ∘L rotMφφ θ φ

/-- Composition norm bound: ‖A ∘L B‖ ≤ 1 when ‖A‖ ≤ 1 and ‖B‖ ≤ 1 -/
lemma comp_norm_le_one {A : ℝ² →L[ℝ] ℝ²} {B : ℝ³ →L[ℝ] ℝ²} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖A ∘L B‖ ≤ 1 :=
  calc ‖A ∘L B‖ ≤ ‖A‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le A B
    _ ≤ 1 * 1 := mul_le_mul hA hB (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Negated composition norm bound: ‖-(A ∘L B)‖ ≤ 1 when ‖A‖ ≤ 1 and ‖B‖ ≤ 1 -/
lemma neg_comp_norm_le_one {A : ℝ² →L[ℝ] ℝ²} {B : ℝ³ →L[ℝ] ℝ²} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖-(A ∘L B)‖ ≤ 1 := by
  rw [norm_neg]; exact comp_norm_le_one hA hB

/-- All A[i,j] have operator norm ≤ 1. -/
lemma inner_second_partial_A_norm_le (α θ φ : ℝ) (i j : Fin 3) :
    ‖inner_second_partial_A α θ φ i j‖ ≤ 1 := by
  fin_cases i <;> fin_cases j
  · exact neg_comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one _)) (le_of_eq (Bounding.rotM_norm_one _ _))
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one _)) (Bounding.rotMθ_norm_le_one _ _)
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one _)) (Bounding.rotMφ_norm_le_one _ _)
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one _)) (Bounding.rotMθ_norm_le_one _ _)
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one _)) (Bounding.rotMθθ_norm_le_one _ _)
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one _)) (Bounding.rotMθφ_norm_le_one _ _)
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR'_norm_one _)) (Bounding.rotMφ_norm_le_one _ _)
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one _)) (Bounding.rotMθφ_norm_le_one _ _)
  · exact comp_norm_le_one (le_of_eq (Bounding.rotR_norm_one _)) (Bounding.rotMφφ_norm_le_one _ _)

/-!
## A[i,j,k] Table for Third Partials

This defines the operator A₃[i,j,k](α, θ, φ) such that
  ∂³(rotproj_inner S w)/∂x_i∂x_j∂x_k = ⟪A₃[i,j,k] S, w⟫,
i.e. A₃[i,j,k] = ∂_i (inner_second_partial_A · · · j k), where x₀ = α, x₁ = θ, x₂ = φ.

Differentiation rules: ∂α sends head rotR ↦ rotR', rotR' ↦ -rotR, -(rotR ∘ ·) ↦ -(rotR' ∘ ·);
∂θ/∂φ act on the matrix family (Mθθθ = -Mθ and Mφφφ = -Mφ collapse, so only the two mixed
matrices rotMθθφ, rotMθφφ are new).  Only 8 distinct compositions occur.
-/

/-- The operator A₃[i,j,k] for third partials of the inner rotation projection:
the ∂ᵢ-derivative of `inner_second_partial_A · · · j k`. -/
noncomputable def inner_third_partial_A (α θ φ : ℝ) (i j k : Fin 3) : ℝ³ →L[ℝ] ℝ² :=
  match i, j, k with
  -- column (j,k) = (0,0): A₂ = -(rotR ∘L rotM)
  | 0, 0, 0 => -(rotR' α ∘L rotM θ φ)
  | 1, 0, 0 => -(rotR α ∘L rotMθ θ φ)
  | 2, 0, 0 => -(rotR α ∘L rotMφ θ φ)
  -- columns (0,1) and (1,0): A₂ = rotR' ∘L rotMθ
  | 0, 0, 1 => -(rotR α ∘L rotMθ θ φ)
  | 1, 0, 1 => rotR' α ∘L rotMθθ θ φ
  | 2, 0, 1 => rotR' α ∘L rotMθφ θ φ
  | 0, 1, 0 => -(rotR α ∘L rotMθ θ φ)
  | 1, 1, 0 => rotR' α ∘L rotMθθ θ φ
  | 2, 1, 0 => rotR' α ∘L rotMθφ θ φ
  -- columns (0,2) and (2,0): A₂ = rotR' ∘L rotMφ
  | 0, 0, 2 => -(rotR α ∘L rotMφ θ φ)
  | 1, 0, 2 => rotR' α ∘L rotMθφ θ φ
  | 2, 0, 2 => rotR' α ∘L rotMφφ θ φ
  | 0, 2, 0 => -(rotR α ∘L rotMφ θ φ)
  | 1, 2, 0 => rotR' α ∘L rotMθφ θ φ
  | 2, 2, 0 => rotR' α ∘L rotMφφ θ φ
  -- column (1,1): A₂ = rotR ∘L rotMθθ  (∂θ collapses via Mθθθ = -Mθ)
  | 0, 1, 1 => rotR' α ∘L rotMθθ θ φ
  | 1, 1, 1 => -(rotR α ∘L rotMθ θ φ)
  | 2, 1, 1 => rotR α ∘L rotMθθφ θ φ
  -- columns (1,2) and (2,1): A₂ = rotR ∘L rotMθφ
  | 0, 1, 2 => rotR' α ∘L rotMθφ θ φ
  | 1, 1, 2 => rotR α ∘L rotMθθφ θ φ
  | 2, 1, 2 => rotR α ∘L rotMθφφ θ φ
  | 0, 2, 1 => rotR' α ∘L rotMθφ θ φ
  | 1, 2, 1 => rotR α ∘L rotMθθφ θ φ
  | 2, 2, 1 => rotR α ∘L rotMθφφ θ φ
  -- column (2,2): A₂ = rotR ∘L rotMφφ  (∂φ collapses via Mφφφ = -Mφ)
  | 0, 2, 2 => rotR' α ∘L rotMφφ θ φ
  | 1, 2, 2 => rotR α ∘L rotMθφφ θ φ
  | 2, 2, 2 => -(rotR α ∘L rotMφ θ φ)

/-- All A₃[i,j,k] have operator norm ≤ 1. -/
lemma inner_third_partial_A_norm_le (α θ φ : ℝ) (i j k : Fin 3) :
    ‖inner_third_partial_A α θ φ i j k‖ ≤ 1 := by
  have hR := le_of_eq (Bounding.rotR_norm_one α)
  have hR' := le_of_eq (Bounding.rotR'_norm_one α)
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact neg_comp_norm_le_one hR' (le_of_eq (Bounding.rotM_norm_one _ _))
  · exact neg_comp_norm_le_one hR (Bounding.rotMθ_norm_le_one _ _)
  · exact neg_comp_norm_le_one hR (Bounding.rotMφ_norm_le_one _ _)
  · exact neg_comp_norm_le_one hR (Bounding.rotMθ_norm_le_one _ _)
  · exact comp_norm_le_one hR' (Bounding.rotMθθ_norm_le_one _ _)
  · exact comp_norm_le_one hR' (Bounding.rotMθφ_norm_le_one _ _)
  · exact neg_comp_norm_le_one hR (Bounding.rotMφ_norm_le_one _ _)
  · exact comp_norm_le_one hR' (Bounding.rotMθφ_norm_le_one _ _)
  · exact comp_norm_le_one hR' (Bounding.rotMφφ_norm_le_one _ _)
  · exact neg_comp_norm_le_one hR (Bounding.rotMθ_norm_le_one _ _)
  · exact comp_norm_le_one hR' (Bounding.rotMθθ_norm_le_one _ _)
  · exact comp_norm_le_one hR' (Bounding.rotMθφ_norm_le_one _ _)
  · exact comp_norm_le_one hR' (Bounding.rotMθθ_norm_le_one _ _)
  · exact neg_comp_norm_le_one hR (Bounding.rotMθ_norm_le_one _ _)
  · exact comp_norm_le_one hR (Bounding.rotMθθφ_norm_le_one _ _)
  · exact comp_norm_le_one hR' (Bounding.rotMθφ_norm_le_one _ _)
  · exact comp_norm_le_one hR (Bounding.rotMθθφ_norm_le_one _ _)
  · exact comp_norm_le_one hR (Bounding.rotMθφφ_norm_le_one _ _)
  · exact neg_comp_norm_le_one hR (Bounding.rotMφ_norm_le_one _ _)
  · exact comp_norm_le_one hR' (Bounding.rotMθφ_norm_le_one _ _)
  · exact comp_norm_le_one hR' (Bounding.rotMφφ_norm_le_one _ _)
  · exact comp_norm_le_one hR' (Bounding.rotMθφ_norm_le_one _ _)
  · exact comp_norm_le_one hR (Bounding.rotMθθφ_norm_le_one _ _)
  · exact comp_norm_le_one hR (Bounding.rotMθφφ_norm_le_one _ _)
  · exact comp_norm_le_one hR' (Bounding.rotMφφ_norm_le_one _ _)
  · exact comp_norm_le_one hR (Bounding.rotMθφφ_norm_le_one _ _)
  · exact neg_comp_norm_le_one hR (Bounding.rotMφ_norm_le_one _ _)

end GlobalTheorem

end
