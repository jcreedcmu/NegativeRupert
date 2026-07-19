module

public import Noperthedron.BalancedSupport.LocalRigidity
public import Noperthedron.SnubCube.Symmetry

@[expose] public section


/-!
# Local rigidity around every snub-cube symmetry

The relative rotation at an equality pose is one of the 24 rotations in
`Symmetry.lean`.  Removing that rotation turns the motion into a small
axis-angle rotation, while the checked symmetry action supplies the required
inner/outer vertex reindexing.
-/

namespace Noperthedron.SnubCube

open scoped Matrix RealInnerProductSpace
open Noperthedron.BalancedSupport

/-- Relative inner/outer rotation after removing symmetry `g`. -/
def relativeRotationAtSymmetry (p : MatrixPose) (g : VertexIndex) : SO3 :=
  relativeRotation p * (symmetry g)⁻¹

/-- The vertex indexed by `i` on the inner copy tracks the vertex indexed by
`symmetryAction g i` on the outer copy after symmetry `g` is removed. -/
theorem outer_relative_at_symmetry_apply
    (p : MatrixPose) (g i : VertexIndex) :
    outerProjectionLinear p
        ((relativeRotationAtSymmetry p g).val.toEuclideanLin.toContinuousLinearMap
          (normalizedExactVertex (symmetryAction g i))) =
      proj_xyL (p.innerRot.val.toEuclideanLin (normalizedExactVertex i)) := by
  rw [← symmetry_apply_normalizedExactVertex g i]
  have hgroup :
      p.outerRot * relativeRotationAtSymmetry p g * symmetry g = p.innerRot := by
    simp [relativeRotationAtSymmetry, relativeRotation, ← mul_assoc]
  have hmat := congrArg Subtype.val hgroup
  simp only [MulMemClass.coe_mul] at hmat
  simp only [outerProjectionLinear, ContinuousLinearMap.comp_apply]
  apply congrArg proj_xyL
  change WithLp.toLp 2
      (p.outerRot.val *ᵥ
        ((relativeRotationAtSymmetry p g).val *ᵥ
          ((symmetry g).val *ᵥ (normalizedExactVertex i).ofLp))) =
    WithLp.toLp 2
      (p.innerRot.val *ᵥ (normalizedExactVertex i).ofLp)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hmat]

/-- Exact finite-rotation local obstruction around any of the 24 snub-cube
symmetry strata.  A row supplies supporting outer vertices after the checked
symmetry reindexing; balance cancels every planar translation. -/
theorem not_rupertPose_of_symmetry_axisAngle_certificate
    {κ : Type} [Fintype κ] [Nonempty κ]
    (p : MatrixPose) (g : VertexIndex)
    (a : AxisAngle
      ((relativeRotationAtSymmetry p g).val.toEuclideanLin.toContinuousLinearMap))
    (index : κ → VertexIndex) (weight : κ → ℝ) (direction : κ → ℝ²)
    (hdirection : ∀ i, direction i ≠ 0)
    (hweight : ∀ i, 0 ≤ weight i) (hweight_pos : ∃ i, 0 < weight i)
    (hbalance : ∑ i, weight i • direction i = 0)
    (hsupport : ∀ i j,
      ⟪direction i, outerProjectionLinear p (normalizedExactVertex j)⟫ ≤
        ⟪direction i, outerProjectionLinear p
          (normalizedExactVertex (symmetryAction g (index i)))⟫)
    (hdominates :
      (1 - Real.cos a.angle) *
          (∑ i, weight i *
            (‖direction i‖ *
              ‖normalizedExactVertex (symmetryAction g (index i))‖)) ≤
        Real.sin a.angle *
          (∑ i, weight i *
            ⟪direction i, outerProjectionLinear p
              (a.first
                (normalizedExactVertex (symmetryAction g (index i))))⟫)) :
    ¬ RupertPose p normalizedExactPolyhedron.hull := by
  apply not_rupertPose_of_reindexed_axisAngle_certificate
    normalizedExactPolyhedron p a index
    (fun i => symmetryAction g (index i)) weight direction
    hdirection hweight hweight_pos hbalance
  · intro i
    exact (outer_relative_at_symmetry_apply p g (index i)).symm
  · simpa [normalizedExactPolyhedron] using hsupport
  · simpa [normalizedExactPolyhedron] using hdominates

end Noperthedron.SnubCube

end
