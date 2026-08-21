/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Noperthedron.Global.Definitions
public import Noperthedron.Global.SecondPartialHelpers

@[expose] public section


/-!
# RotM Outer HasFDerivAt Lemmas

This file contains:
- `rotM'` definition
- `Differentiable.rotM_outer`
- **`HasFDerivAt.rotM_outer`**
- `rotMθ'`, **`HasFDerivAt.rotMθ_outer`**
- `rotMφ'`, **`HasFDerivAt.rotMφ_outer`**
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private lemma outerParams_0 (pbar : Pose ℝ) : pbar.outerParams.ofLp 0 = pbar.θ₂ := by simp [Pose.outerParams]
private lemma outerParams_1 (pbar : Pose ℝ) : pbar.outerParams.ofLp 1 = pbar.φ₂ := by simp [Pose.outerParams]

/-- Coordinate extraction in `E 2`: direction `e_i`, same coordinate (moves). -/
private lemma coord2_same (i : Fin 2) (y : E 2) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E 2)).ofLp i = y.ofLp i + t := by simp

/-- Coordinate extraction in `E 2`: direction `e_i`, different coordinate (fixed). -/
private lemma coord2_other {i j : Fin 2} (hij : j ≠ i) (y : E 2) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E 2)).ofLp j = y.ofLp j := by simp [hij]

/-- The fderiv of rotM applied to a fixed vector P, as a function of (θ, φ).
Columns: [rotMθ, rotMφ]. -/
noncomputable
def rotM' (pbar : Pose ℝ) (P : ℝ³) : ℝ² →L[ℝ] ℝ² :=
  columnsCLM ![rotMθ pbar.θ₂ pbar.φ₂ P, rotMφ pbar.θ₂ pbar.φ₂ P]

lemma Differentiable.rotM_outer (P : ℝ³) :
    Differentiable ℝ fun (x : ℝ²) => (rotM (x 0) (x 1)) P := by
  rw [differentiable_piLp]
  intro i
  fin_cases i <;> simp [rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail] <;> fun_prop

@[simp]
lemma rotM'_single_0 (pbar : Pose ℝ) (P : ℝ³) :
    rotM' pbar P (EuclideanSpace.single 0 1) = rotMθ pbar.θ₂ pbar.φ₂ P := by
  simp [rotM']

@[simp]
lemma rotM'_single_1 (pbar : Pose ℝ) (P : ℝ³) :
    rotM' pbar P (EuclideanSpace.single 1 1) = rotMφ pbar.θ₂ pbar.φ₂ P := by
  simp [rotM']

lemma HasFDerivAt.rotM_outer (pbar : Pose ℝ) (P : ℝ³) :
    HasFDerivAt (fun x => (rotM (x.ofLp 0) (x.ofLp 1)) P) (rotM' pbar P) pbar.outerParams := by
  refine hasFDerivAt_of_partials _ (Differentiable.rotM_outer P pbar.outerParams) fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, coord2_same,
      coord2_other (by decide : (1 : Fin 2) ≠ 0), outerParams_0, outerParams_1]
    exact hasDerivAt_comp_add _ _ _ (hasDerivAt_rotM_θ pbar.θ₂ pbar.φ₂ P)
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      coord2_same, coord2_other (by decide : (0 : Fin 2) ≠ 1), outerParams_0, outerParams_1]
    exact hasDerivAt_comp_add _ _ _ (hasDerivAt_rotM_φ pbar.θ₂ pbar.φ₂ P)

/-- Fréchet derivative of rotMθ: columns are [rotMθθ, rotMθφ]. -/
noncomputable def rotMθ' (pbar : Pose ℝ) (P : ℝ³) : E 2 →L[ℝ] ℝ² :=
  columnsCLM ![rotMθθ pbar.θ₂ pbar.φ₂ P, rotMθφ pbar.θ₂ pbar.φ₂ P]

@[simp]
lemma rotMθ'_single_0 (pbar : Pose ℝ) (P : ℝ³) :
    rotMθ' pbar P (EuclideanSpace.single 0 1) = rotMθθ pbar.θ₂ pbar.φ₂ P := by
  simp [rotMθ']

@[simp]
lemma rotMθ'_single_1 (pbar : Pose ℝ) (P : ℝ³) :
    rotMθ' pbar P (EuclideanSpace.single 1 1) = rotMθφ pbar.θ₂ pbar.φ₂ P := by
  simp [rotMθ']

lemma HasFDerivAt.rotMθ_outer (pbar : Pose ℝ) (P : ℝ³) :
    HasFDerivAt (fun x => (rotMθ (x.ofLp 0) (x.ofLp 1)) P) (rotMθ' pbar P) pbar.outerParams := by
  refine hasFDerivAt_of_partials _ (differentiableAt_rotMθ_outer P pbar.outerParams) fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, coord2_same,
      coord2_other (by decide : (1 : Fin 2) ≠ 0), outerParams_0, outerParams_1]
    exact hasDerivAt_comp_add _ _ _ (hasDerivAt_rotMθ_θ pbar.θ₂ pbar.φ₂ P)
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      coord2_same, coord2_other (by decide : (0 : Fin 2) ≠ 1), outerParams_0, outerParams_1]
    exact hasDerivAt_comp_add _ _ _ (hasDerivAt_rotMθ_φ pbar.θ₂ pbar.φ₂ P)

/-- Fréchet derivative of rotMφ: columns are [rotMθφ, rotMφφ]. -/
noncomputable def rotMφ' (pbar : Pose ℝ) (P : ℝ³) : E 2 →L[ℝ] ℝ² :=
  columnsCLM ![rotMθφ pbar.θ₂ pbar.φ₂ P, rotMφφ pbar.θ₂ pbar.φ₂ P]

@[simp]
lemma rotMφ'_single_0 (pbar : Pose ℝ) (P : ℝ³) :
    rotMφ' pbar P (EuclideanSpace.single 0 1) = rotMθφ pbar.θ₂ pbar.φ₂ P := by
  simp [rotMφ']

@[simp]
lemma rotMφ'_single_1 (pbar : Pose ℝ) (P : ℝ³) :
    rotMφ' pbar P (EuclideanSpace.single 1 1) = rotMφφ pbar.θ₂ pbar.φ₂ P := by
  simp [rotMφ']

lemma HasFDerivAt.rotMφ_outer (pbar : Pose ℝ) (P : ℝ³) :
    HasFDerivAt (fun x => (rotMφ (x.ofLp 0) (x.ofLp 1)) P) (rotMφ' pbar P) pbar.outerParams := by
  refine hasFDerivAt_of_partials _ (differentiableAt_rotMφ_outer P pbar.outerParams) fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, coord2_same,
      coord2_other (by decide : (1 : Fin 2) ≠ 0), outerParams_0, outerParams_1]
    exact hasDerivAt_comp_add _ _ _ (hasDerivAt_rotMφ_θ pbar.θ₂ pbar.φ₂ P)
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      coord2_same, coord2_other (by decide : (0 : Fin 2) ≠ 1), outerParams_0, outerParams_1]
    exact hasDerivAt_comp_add _ _ _ (hasDerivAt_rotMφ_φ pbar.θ₂ pbar.φ₂ P)

end GlobalTheorem

end
