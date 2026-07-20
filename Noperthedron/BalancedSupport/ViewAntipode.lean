module

public import Noperthedron.MatrixPose

@[expose] public section

/-!
# Reversing the oriented viewing normal

Orthogonal projection remembers the viewing plane but not an orientation of
its normal.  Left multiplication of both rotations by the half-turn about
the screen x-axis reverses that normal and reflects both planar shadows in
the y-axis.  Rupert containment is therefore unchanged, and the relative
rotation is unchanged as well.
-/

open scoped Matrix

namespace MatrixPose

noncomputable def viewAntipodeRotation : SO3 :=
  ⟨Rx_mat Real.pi, Bounding.rot3_mat_mem_SO3 0 Real.pi⟩

/-- Reverse the oriented viewing normal, reflecting the screen y-coordinate. -/
noncomputable def viewAntipode (p : MatrixPose) : MatrixPose where
  innerRot := viewAntipodeRotation * p.innerRot
  outerRot := viewAntipodeRotation * p.outerRot
  innerOffset := flip_y p.innerOffset

private theorem project_viewAntipodeRotation (v : ℝ³) :
    proj_xyL (viewAntipodeRotation.val.toEuclideanLin v) =
      flip_y (proj_xyL v) := by
  ext i
  fin_cases i <;>
    simp [viewAntipodeRotation, flip_y, flip_y_mat, proj_xyL, proj_xy_mat,
      Rx_mat, Matrix.vecHead, Matrix.vecTail]

private theorem viewAntipodeRotation_mul_apply
    (M : SO3) (v : ℝ³) :
    (viewAntipodeRotation * M).val.toEuclideanLin v =
      viewAntipodeRotation.val.toEuclideanLin (M.val.toEuclideanLin v) := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

theorem outerShadow_viewAntipode (p : MatrixPose) (S : Set ℝ³) :
    outerShadow p.viewAntipode S = flip_y '' outerShadow p S := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨proj_xyL (p.outerRot.val.toEuclideanLin v), ⟨v, hv, rfl⟩, ?_⟩
    simp only [viewAntipode, PoseLike.outer, LinearMap.coe_toAffineMap]
    rw [viewAntipodeRotation_mul_apply, project_viewAntipodeRotation]
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨v, hv, ?_⟩
    simp only [viewAntipode, PoseLike.outer, LinearMap.coe_toAffineMap]
    rw [viewAntipodeRotation_mul_apply, project_viewAntipodeRotation]

theorem innerShadow_viewAntipode (p : MatrixPose) (S : Set ℝ³) :
    innerShadow p.viewAntipode S = flip_y '' innerShadow p S := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨proj_xyL (PoseLike.inner p v), ⟨v, hv, rfl⟩, ?_⟩
    rw [inner_apply, inner_apply]
    simp only [viewAntipode]
    rw [viewAntipodeRotation_mul_apply, map_add, map_add, map_add,
      project_viewAntipodeRotation]
    ext i
    fin_cases i <;>
      simp [flip_y, flip_y_mat, proj_xyL, proj_xy_mat, inject_xy,
        Matrix.vecHead, Matrix.vecTail]
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨v, hv, ?_⟩
    rw [inner_apply, inner_apply]
    simp only [viewAntipode]
    rw [viewAntipodeRotation_mul_apply, map_add, map_add, map_add,
      project_viewAntipodeRotation]
    ext i
    fin_cases i <;>
      simp [flip_y, flip_y_mat, proj_xyL, proj_xy_mat, inject_xy,
        Matrix.vecHead, Matrix.vecTail]

/-- Reversing the oriented normal preserves strict shadow containment. -/
theorem RupertPose_viewAntipode_iff (p : MatrixPose) (S : Set ℝ³) :
    RupertPose p.viewAntipode S ↔ RupertPose p S := by
  simp only [RupertPose, innerShadow_viewAntipode,
    outerShadow_viewAntipode]
  let fh := flip_y_equiv.toHomeomorph
  change closure (fh '' innerShadow p S) ⊆
      interior (fh '' outerShadow p S) ↔ _
  rw [← fh.image_closure, ← fh.image_interior]
  exact Set.image_subset_image_iff fh.injective

@[simp] theorem viewAntipode_outer_22 (p : MatrixPose) :
    p.viewAntipode.outerRot.val 2 2 = -p.outerRot.val 2 2 := by
  simp [viewAntipode, viewAntipodeRotation, Matrix.mul_apply,
    Rx_mat, Fin.sum_univ_three]

/-- Choose the orientation of the viewing normal whose z-coordinate is
nonnegative. -/
noncomputable def upperViewRepresentative (p : MatrixPose) : MatrixPose :=
  if 0 ≤ p.outerRot.val 2 2 then p else p.viewAntipode

theorem upperViewRepresentative_outer_22_nonneg (p : MatrixPose) :
    0 ≤ p.upperViewRepresentative.outerRot.val 2 2 := by
  by_cases h : 0 ≤ p.outerRot.val 2 2
  · simp [upperViewRepresentative, h]
  · simp [upperViewRepresentative, h]
    exact le_of_not_ge h

theorem RupertPose_upperViewRepresentative_iff
    (p : MatrixPose) (S : Set ℝ³) :
    RupertPose p.upperViewRepresentative S ↔ RupertPose p S := by
  by_cases h : 0 ≤ p.outerRot.val 2 2
  · simp [upperViewRepresentative, h]
  · simpa [upperViewRepresentative, h] using
      RupertPose_viewAntipode_iff p S

end MatrixPose

end
