/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Noperthedron.Global.RotationDerivs
public import Noperthedron.Global.SecondPartialHelpers
public import Noperthedron.Global.Definitions
public import Noperthedron.Global.Basic

@[expose] public section


/-!
# FDeriv Helper Lemmas for Global Theorem

This file contains helper lemmas for computing fderiv in coordinate directions.
These show that fderiv f y (e_i) equals the partial derivative in direction i.

## Main Results

* `fderiv_rotR_rotM_in_e0` - fderiv of rotR ∘ rotM in direction e₀ gives rotR'
* `fderiv_rotR_rotM_in_e1` - fderiv of rotR ∘ rotM in direction e₁ gives rotR ∘ rotMθ
* `fderiv_rotR_rotM_in_e2` - fderiv of rotR ∘ rotM in direction e₂ gives rotR ∘ rotMφ
* `fderiv_rotR'_rotM_in_e0` - fderiv of rotR' ∘ rotM in direction e₀ gives -rotR
* `fderiv_rotR'_rotM_in_e1` - fderiv of rotR' ∘ rotM in direction e₁ gives rotR' ∘ rotMθ
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

-- Derivative of rotR' with respect to α: d/dα(rotR' α v) = -rotR α v
-- This is needed for the second derivative ∂²/∂α² of rotproj_inner
lemma HasDerivAt_rotR' (α : ℝ) (v : ℝ²) :
    HasDerivAt (rotR' · v) (-(rotR α v)) α := by
  have h := HasDerivAt.comp_add_const α (Real.pi / 2) (HasDerivAt_rotR (α + Real.pi / 2) v)
  rw [rotR'_eq_rotR_add_pi_div_two,
    show α + Real.pi / 2 + Real.pi / 2 = α + Real.pi by ring,
    rotR_add_pi_eq_neg_rotR] at h
  simpa only [neg_apply, ← rotR'_eq_rotR_add_pi_div_two] using h

/-- fderiv of rotR with any M in direction e₀ gives rotR' -/
lemma fderiv_rotR_any_M_in_e0 (S : Euc(3)) (y : E 3) (M : ℝ → ℝ → ℝ³ →L[ℝ] ℝ²)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (M (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (M (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 0 1) =
    rotR' (y.ofLp 0) (M (y.ofLp 1) (y.ofLp 2) S) := by
  refine fderiv_single_eq hf_diff ?_
  simp only [coord_e0_same, coord_e0_at1, coord_e0_at2]
  exact hasDerivAt_comp_add _ _ _ (HasDerivAt_rotR (y.ofLp 0) (M (y.ofLp 1) (y.ofLp 2) S))

/-- fderiv of rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₀ gives rotR' -/
lemma fderiv_rotR_rotM_in_e0 (S : Euc(3)) (y : E 3)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 0 1) =
    rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) :=
  fderiv_rotR_any_M_in_e0 S y rotM hf_diff

/-- fderiv of rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₂ gives rotR ∘ rotMφ -/
lemma fderiv_rotR_rotM_in_e2 (S : Euc(3)) (y : E 3)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 2 1) =
    rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S) := by
  refine fderiv_single_eq hf_diff ?_
  simp only [coord_e2_at0, coord_e2_at1, coord_e2_same]
  exact hasDerivAt_comp_add _ _ _
    ((ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))).comp_hasDerivAt _
      (hasDerivAt_rotM_φ (y.ofLp 1) (y.ofLp 2) S))

/-- fderiv of rotR (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₁ gives rotR ∘ rotMθ -/
lemma fderiv_rotR_rotM_in_e1 (S : Euc(3)) (y : E 3)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) =
    rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S) := by
  refine fderiv_single_eq hf_diff ?_
  simp only [coord_e1_at0, coord_e1_same, coord_e1_at2]
  exact hasDerivAt_comp_add _ _ _
    ((ContinuousLinearMap.hasFDerivAt (rotR (y.ofLp 0))).comp_hasDerivAt _
      (hasDerivAt_rotM_θ (y.ofLp 1) (y.ofLp 2) S))

/-- fderiv of rotR' with any M in direction e₀ gives -rotR -/
lemma fderiv_rotR'_any_M_in_e0 (S : Euc(3)) (y : E 3) (M : ℝ → ℝ → ℝ³ →L[ℝ] ℝ²)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (M (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (M (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 0 1) =
    -(rotR (y.ofLp 0) (M (y.ofLp 1) (y.ofLp 2) S)) := by
  refine fderiv_single_eq hf_diff ?_
  simp only [coord_e0_same, coord_e0_at1, coord_e0_at2]
  exact hasDerivAt_comp_add _ _ _ (HasDerivAt_rotR' (y.ofLp 0) (M (y.ofLp 1) (y.ofLp 2) S))

/-- fderiv of rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₀ gives -rotR -/
lemma fderiv_rotR'_rotM_in_e0 (S : Euc(3)) (y : E 3) (α θ φ : ℝ)
    (hα : y.ofLp 0 = α) (hθ : y.ofLp 1 = θ) (hφ : y.ofLp 2 = φ)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 0 1) =
    -(rotR α (rotM θ φ S)) := by
  subst hα hθ hφ
  exact fderiv_rotR'_any_M_in_e0 S y rotM hf_diff

/-- fderiv of rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₁ gives rotR' α (rotMθ θ φ S) -/
lemma fderiv_rotR'_rotM_in_e1 (S : Euc(3)) (y : E 3) (α θ φ : ℝ)
    (hα : y.ofLp 0 = α) (hθ : y.ofLp 1 = θ) (hφ : y.ofLp 2 = φ)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 1 1) =
    rotR' α (rotMθ θ φ S) := by
  refine fderiv_single_eq hf_diff ?_
  simp only [coord_e1_at0, coord_e1_same, coord_e1_at2, hα, hθ, hφ]
  exact hasDerivAt_comp_add _ _ _
    ((ContinuousLinearMap.hasFDerivAt (rotR' α)).comp_hasDerivAt _ (hasDerivAt_rotM_θ θ φ S))

/-- fderiv of rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S) in direction e₂ gives rotR' α (rotMφ θ φ S) -/
lemma fderiv_rotR'_rotM_in_e2 (S : Euc(3)) (y : E 3) (α θ φ : ℝ)
    (hα : y.ofLp 0 = α) (hθ : y.ofLp 1 = θ) (hφ : y.ofLp 2 = φ)
    (hf_diff : DifferentiableAt ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y) :
    (fderiv ℝ (fun z : E 3 => rotR' (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S)) y)
      (EuclideanSpace.single 2 1) =
    rotR' α (rotMφ θ φ S) := by
  refine fderiv_single_eq hf_diff ?_
  simp only [coord_e2_at0, coord_e2_at1, coord_e2_same, hα, hθ, hφ]
  exact hasDerivAt_comp_add _ _ _
    ((ContinuousLinearMap.hasFDerivAt (rotR' α)).comp_hasDerivAt _ (hasDerivAt_rotM_φ θ φ S))

/-!
## nth_partial of rotproj_inner in coordinate directions

These combine `fderiv_inner_const` with `fderiv_rotR_rotM_in_e*` to give
function-level formulas for the partial derivatives of `rotproj_inner`,
eliminating the `funext`/`congrArg` boilerplate at each use site.
-/

/-- Function-level form of `rotproj_inner_eq`. -/
private lemma rotproj_inner_funext (S : ℝ³) (w : ℝ²) :
    rotproj_inner S w = fun z : E 3 => ⟪rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) S), w⟫ :=
  funext fun z => rotproj_inner_eq S w z

lemma nth_partial_rotproj_inner_e0 (S : ℝ³) (w : ℝ²) :
    nth_partial 0 (rotproj_inner S w) =
      fun (y : ℝ³) => ⟪rotR' (y.ofLp 0) (rotM (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
  funext y
  have hd := differentiableAt_rotR_rotM S y
  show (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 0 1) = _
  rw [rotproj_inner_funext, fderiv_inner_const _ w y _ hd, fderiv_rotR_rotM_in_e0 S y hd]

lemma nth_partial_rotproj_inner_e1 (S : ℝ³) (w : ℝ²) :
    nth_partial 1 (rotproj_inner S w) =
      fun (y : ℝ³) => ⟪rotR (y.ofLp 0) (rotMθ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
  funext y
  have hd := differentiableAt_rotR_rotM S y
  show (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 1 1) = _
  rw [rotproj_inner_funext, fderiv_inner_const _ w y _ hd, fderiv_rotR_rotM_in_e1 S y hd]

lemma nth_partial_rotproj_inner_e2 (S : ℝ³) (w : ℝ²) :
    nth_partial 2 (rotproj_inner S w) =
      fun (y : ℝ³) => ⟪rotR (y.ofLp 0) (rotMφ (y.ofLp 1) (y.ofLp 2) S), w⟫ := by
  funext y
  have hd := differentiableAt_rotR_rotM S y
  show (fderiv ℝ (rotproj_inner S w) y) (EuclideanSpace.single 2 1) = _
  rw [rotproj_inner_funext, fderiv_inner_const _ w y _ hd, fderiv_rotR_rotM_in_e2 S y hd]

end GlobalTheorem

end
