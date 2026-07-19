module

public import Noperthedron.BalancedSupport.Basic
public import Noperthedron.MatrixPose

@[expose] public section


/-!
# Balanced-support certificates for full Rupert poses

The snub cube is not centrally symmetric, so its proof must retain the planar
translation in `MatrixPose`.  The balance equation below cancels that offset;
no common-center reduction is used.
-/

namespace Noperthedron.BalancedSupport

open scoped RealInnerProductSpace

/-- The projected outer vertices of a polyhedron at a matrix pose. -/
noncomputable def outerVertexSet {ι : Type} [Fintype ι]
    (p : MatrixPose) (poly : Polyhedron ι ℝ³) : Set ℝ² :=
  outerProj p '' {poly.v i | i}

/-- Projecting the convex hull is the convex hull of the projected vertices. -/
theorem outerShadow_poly_hull_eq {ι : Type} [Fintype ι]
    (p : MatrixPose) (poly : Polyhedron ι ℝ³) :
    outerShadow p poly.hull = convexHull ℝ (outerVertexSet p poly) := by
  change outerProj p '' convexHull ℝ {poly.v i | i} =
    convexHull ℝ (outerProj p '' {poly.v i | i})
  exact AffineMap.image_convexHull (outerProj p) _

/-- A vertex of the inner copy belongs to the interior of the outer shadow at
any Rupert pose. -/
theorem inner_vertex_mem_outer_interior {ι : Type} [Fintype ι]
    (p : MatrixPose) (poly : Polyhedron ι ℝ³) (i : ι)
    (hrupert : RupertPose p poly.hull) :
    proj_xyL (PoseLike.inner p (poly.v i)) ∈ interior (outerShadow p poly.hull) := by
  apply hrupert
  apply subset_closure
  exact ⟨poly.v i, subset_convexHull ℝ _ ⟨i, rfl⟩, rfl⟩

/-- The projection of the affine inner action is its rotational projection
plus the explicit planar offset. -/
theorem project_inner_apply (p : MatrixPose) (v : ℝ³) :
    proj_xyL (PoseLike.inner p v) =
      proj_xyL (p.innerRot.val.toEuclideanLin v) + p.innerOffset := by
  rw [MatrixPose.inner_apply, proj_xyL_offset_commute]

/-- A balanced-support certificate rules out a full `MatrixPose`, including
an arbitrary planar translation. -/
theorem not_rupertPose_of_balanced_support
    {ι κ : Type} [Fintype ι] [Fintype κ] [Nonempty κ]
    (poly : Polyhedron ι ℝ³) (p : MatrixPose)
    (Pi Qi : κ → ι) (μ : κ → ℝ) (u : κ → ℝ²)
    (hu : ∀ i, u i ≠ 0)
    (hμ : ∀ i, 0 ≤ μ i) (hμpos : ∃ i, 0 < μ i)
    (hbalance : ∑ i, μ i • u i = 0)
    (hsupport : ∀ i y, y ∈ outerVertexSet p poly →
      ⟪u i, y⟫ ≤
        ⟪u i, proj_xyL (p.outerRot.val.toEuclideanLin (poly.v (Qi i)))⟫)
    (hdisplacement : 0 ≤ ∑ i, μ i *
      ⟪u i, proj_xyL (p.innerRot.val.toEuclideanLin (poly.v (Pi i))) -
        proj_xyL (p.outerRot.val.toEuclideanLin (poly.v (Qi i)))⟫) :
    ¬ RupertPose p poly.hull := by
  intro hrupert
  let innerPoint : κ → ℝ² := fun i =>
    proj_xyL (p.innerRot.val.toEuclideanLin (poly.v (Pi i)))
  let outerPoint : κ → ℝ² := fun i =>
    proj_xyL (p.outerRot.val.toEuclideanLin (poly.v (Qi i)))
  refine not_strictly_contained_of_balanced_support
    (outerVertexSet p poly) μ u innerPoint outerPoint p.innerOffset
    hu hμ hμpos hbalance ?_ ?_ ?_
  · simpa [outerPoint] using hsupport
  · intro i
    rw [← project_inner_apply, ← outerShadow_poly_hull_eq]
    exact inner_vertex_mem_outer_interior p poly (Pi i) hrupert
  · simpa [innerPoint, outerPoint] using hdisplacement

end Noperthedron.BalancedSupport

end
