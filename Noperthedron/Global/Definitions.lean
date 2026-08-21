/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Noperthedron.PoseInterval
public import Noperthedron.Vertices.Exact

@[expose] public section


/-!
# Global Theorem Definitions

Shared definitions for the global theorem.
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

noncomputable
def rotproj_inner (S : ℝ³) (w : ℝ²) (x : ℝ³) : ℝ :=
  ⟪rotprojRM (x 1) (x 2) (x 0) S, w⟫

noncomputable
def rotproj_outer (S : ℝ³) (w : ℝ²) (x : ℝ²) : ℝ :=
  ⟪rotM (x 0) (x 1) S, w⟫

/-- Expand rotproj_inner in terms of rotR and rotM -/
@[simp]
lemma rotproj_inner_eq (S : ℝ³) (w : ℝ²) (x : ℝ³) :
    rotproj_inner S w x = ⟪rotR (x 0) (rotM (x 1) (x 2) S), w⟫ := by
  simp [rotproj_inner, rotprojRM]

/-- Expand rotproj_outer in terms of rotM -/
@[simp]
lemma rotproj_outer_eq (S : ℝ³) (w : ℝ²) (x : ℝ²) :
    rotproj_outer S w x = ⟪rotM (x 0) (x 1) S, w⟫ := rfl

lemma rotation_partials_exist {S : ℝ³} {w : ℝ²} :
    ContDiff ℝ 3 (rotproj_inner S w) := by
  unfold rotproj_inner
  simp [inner, rotprojRM, rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
  fun_prop

lemma rotation_partials_exist_outer {S : ℝ³} {w : ℝ²} :
    ContDiff ℝ 3 (rotproj_outer S w) := by
  unfold rotproj_outer
  simp [inner, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
  fun_prop

end GlobalTheorem

end
