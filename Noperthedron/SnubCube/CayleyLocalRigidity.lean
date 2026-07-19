module

public import Noperthedron.SnubCube.CayleyPose
public import Noperthedron.SnubCube.LocalRigidity

@[expose] public section


/-!
# Exact local-angle control for Cayley poses

At symmetry index zero the relative rotation is definitionally the Cayley
rotation, independent of the outer viewing angles and planar translation.
The general Cayley ratio identity therefore supplies the local theorem's
finite-rotation bound without a matrix-mismatch approximation.
-/

namespace Noperthedron.SnubCube

open Noperthedron.BalancedSupport

theorem CayleyPose.matrixPoseWithOffset_innerRot_eq
    (p : CayleyPose ℝ) (offset : ℝ²) :
    (p.matrixPoseWithOffset offset).innerRot =
      (p.matrixPoseWithOffset offset).outerRot * cayleySO3 p.x p.y p.z := by
  apply Subtype.ext
  rfl

@[simp]
theorem CayleyPose.relativeRotationAtSymmetry_zero
    (p : CayleyPose ℝ) (offset : ℝ²) :
    relativeRotationAtSymmetry (p.matrixPoseWithOffset offset)
        (VertexIndex.ofFin24 0) = cayleySO3 p.x p.y p.z := by
  unfold relativeRotationAtSymmetry
  unfold Noperthedron.BalancedSupport.relativeRotation
  rw [p.matrixPoseWithOffset_innerRot_eq, symmetry_zero]
  simp [← mul_assoc]

theorem CayleyPose.axisAngle_ratio_eq
    (p : CayleyPose ℝ) (offset : ℝ²)
    (a : AxisAngle
      ((relativeRotationAtSymmetry (p.matrixPoseWithOffset offset)
        (VertexIndex.ofFin24 0)).val.toEuclideanLin.toContinuousLinearMap)) :
    1 - Real.cos a.angle = |Real.sin a.angle| *
      Real.sqrt (p.x ^ 2 + p.y ^ 2 + p.z ^ 2) := by
  have hrelative := p.relativeRotationAtSymmetry_zero offset
  have hQ :
      (relativeRotationAtSymmetry (p.matrixPoseWithOffset offset)
          (VertexIndex.ofFin24 0)).val.toEuclideanLin.toContinuousLinearMap =
        (cayleyMatrix p.x p.y p.z).toEuclideanLin.toContinuousLinearMap := by
    rw [hrelative]
    rfl
  exact a.cayley_ratio_eq_of_rotation_eq p.x p.y p.z hQ

theorem CayleyPose.axisAngle_ratio_le
    (p : CayleyPose ℝ) (offset : ℝ²)
    (a : AxisAngle
      ((relativeRotationAtSymmetry (p.matrixPoseWithOffset offset)
        (VertexIndex.ofFin24 0)).val.toEuclideanLin.toContinuousLinearMap))
    (c : ℝ) (hradius : Real.sqrt (p.x ^ 2 + p.y ^ 2 + p.z ^ 2) ≤ c) :
    1 - Real.cos a.angle ≤ |Real.sin a.angle| * c := by
  rw [p.axisAngle_ratio_eq offset a]
  exact mul_le_mul_of_nonneg_left hradius (abs_nonneg _)

end Noperthedron.SnubCube

end
