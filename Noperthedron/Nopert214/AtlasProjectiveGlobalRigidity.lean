module

public import Noperthedron.Nopert214.AtlasProjectiveLocalRigidity

@[expose] public section

/-!
# Projective moving-direction global obstruction for Nopert #214

A single determinant-balanced triple of moving outer support directions rules
out a translated Rupert pose whenever its weighted inner-minus-outer
displacement is nonnegative.  Unlike the local theorem, this statement makes
no reference to a nearby symmetry or to an axis-angle decomposition.
-/

namespace Noperthedron.Nopert214.AtlasProjectiveGlobalRigidity

open scoped RealInnerProductSpace
open Noperthedron.BalancedSupport
open AtlasProjectiveLocalRigidity
open AtlasProjectiveView

theorem not_rupertPose_of_projective_global_certificate
    (root : Fin 8) (p : AtlasPose ℝ) (chart : CayleyAtlas.ChartIndex)
    (offset : ℝ²) (edge : EdgeTriple)
    (innerIndex outerIndex : Fin 3 → VertexIndex)
    (hscale : viewScale root p ≠ 0)
    (hdirection : ∀ i, direction root p (edge i) ≠ 0)
    (hweight : ∀ i, 0 ≤ weight root p edge i)
    (hweight_pos : ∃ i, 0 < weight root p edge i)
    (hsupport : ∀ i k,
      ⟪direction root p (edge i),
          outerProjectionLinear (p.matrixPoseWithOffset chart offset)
            (exactVertex k)⟫ ≤
        ⟪direction root p (edge i),
          outerProjectionLinear (p.matrixPoseWithOffset chart offset)
            (exactVertex (outerIndex i))⟫)
    (hdisplacement : 0 ≤ ∑ i, weight root p edge i *
      ⟪direction root p (edge i),
        proj_xyL ((p.matrixPoseWithOffset chart offset).innerRot.val.toEuclideanLin
            (exactVertex (innerIndex i))) -
          outerProjectionLinear (p.matrixPoseWithOffset chart offset)
            (exactVertex (outerIndex i))⟫) :
    ¬ RupertPose (p.matrixPoseWithOffset chart offset)
      exactPolyhedron.hull := by
  let pose := p.matrixPoseWithOffset chart offset
  apply not_rupertPose_of_balanced_support exactPolyhedron pose
    innerIndex outerIndex (weight root p edge)
    (fun i => direction root p (edge i))
  · exact hdirection
  · exact hweight
  · exact hweight_pos
  · exact weight_balance root p edge hscale
  · intro i y hy
    obtain ⟨v, ⟨k, rfl⟩, rfl⟩ := hy
    simpa [pose, outerProjectionLinear, outerProj, PoseLike.outer,
      LinearMap.coe_toAffineMap, ContinuousLinearMap.comp_apply] using
      hsupport i k
  · simpa [pose, outerProjectionLinear,
      ContinuousLinearMap.comp_apply] using hdisplacement

/-- The transition-stable form of the moving balanced-triple obstruction.
Each chosen outer vertex may miss the true support line by `defect i`; the
weighted displacement pays for the resulting total error. -/
theorem not_rupertPose_of_projective_global_certificate_with_defect
    (root : Fin 8) (p : AtlasPose ℝ) (chart : CayleyAtlas.ChartIndex)
    (offset : ℝ²) (edge : EdgeTriple)
    (innerIndex outerIndex : Fin 3 → VertexIndex) (defect : Fin 3 → ℝ)
    (hscale : viewScale root p ≠ 0)
    (hdirection : ∀ i, direction root p (edge i) ≠ 0)
    (hweight : ∀ i, 0 ≤ weight root p edge i)
    (hweight_pos : ∃ i, 0 < weight root p edge i)
    (hsupport : ∀ i k,
      ⟪direction root p (edge i),
          outerProjectionLinear (p.matrixPoseWithOffset chart offset)
            (exactVertex k)⟫ ≤
        ⟪direction root p (edge i),
          outerProjectionLinear (p.matrixPoseWithOffset chart offset)
            (exactVertex (outerIndex i))⟫ + defect i)
    (hdisplacement : ∑ i, weight root p edge i * defect i ≤
      ∑ i, weight root p edge i *
        ⟪direction root p (edge i),
          proj_xyL
              ((p.matrixPoseWithOffset chart offset).innerRot.val.toEuclideanLin
                (exactVertex (innerIndex i))) -
            outerProjectionLinear (p.matrixPoseWithOffset chart offset)
              (exactVertex (outerIndex i))⟫) :
    ¬ RupertPose (p.matrixPoseWithOffset chart offset)
      exactPolyhedron.hull := by
  let pose := p.matrixPoseWithOffset chart offset
  apply not_rupertPose_of_balanced_support_with_defect exactPolyhedron pose
    innerIndex outerIndex (weight root p edge)
    (fun i => direction root p (edge i)) defect
  · exact hdirection
  · exact hweight
  · exact hweight_pos
  · exact weight_balance root p edge hscale
  · intro i y hy
    obtain ⟨v, ⟨k, rfl⟩, rfl⟩ := hy
    simpa [pose, outerProjectionLinear, outerProj, PoseLike.outer,
      LinearMap.coe_toAffineMap, ContinuousLinearMap.comp_apply] using
      hsupport i k
  · simpa [pose, outerProjectionLinear,
      ContinuousLinearMap.comp_apply] using hdisplacement

end Noperthedron.Nopert214.AtlasProjectiveGlobalRigidity

end
