module

public import Noperthedron.Nopert214.AtlasProjectiveSolutionTree
public import Noperthedron.Rupert.Equivalences.RupertEquivRupertSet

@[expose] public section

/-!
# The public non-Rupert conclusion for Nopert #214

This file contains the small, certificate-independent bridge from four valid
Cayley-chart tables to the usual vertex-set formulation of the Rupert
property.
-/

open scoped Matrix

namespace Noperthedron.Nopert214

open CayleyAtlas
open AtlasProjectiveSolutionTree

private lemma rupert_set_implies_matrix_pose {S : Set ℝ³}
    (h : IsRupertSet S) :
    ∃ p : MatrixPose, RupertPose p S := by
  obtain ⟨inner, innerSO3, offset, outer, outerSO3, hshadow⟩ := h
  let p : MatrixPose :=
    MatrixPose.mk ⟨inner, innerSO3⟩ ⟨outer, outerSO3⟩ offset
  refine ⟨p, ?_⟩
  change closure (innerShadow p S) ⊆ interior (outerShadow p S)
  rw [p.inner_shadow_lemma, outerShadow]
  repeat rw [← proj_xy_eq_proj_xyL]
  exact hshadow

/-- Valid exclusion tables for all four Cayley charts prove that the exact
fivefold-symmetric version of Nopert #214 is not Rupert. -/
theorem not_rupert_of_valid_tables
    (table : ChartIndex → AtlasProjectiveSolutionTree.Table)
    (hchart : ∀ chart, (table chart).chart = chart)
    (hvalid : ∀ chart, (table chart).Valid) :
    ¬ IsRupert exactVerts := by
  intro hrupert
  have hset : IsRupertSet (convexHull ℝ exactVerts) :=
    (rupert_iff_rupert_set exactVerts).mp hrupert
  rw [← exactPolyhedron_hull] at hset
  exact no_matrixPose_of_valid_tables table hchart hvalid
    (rupert_set_implies_matrix_pose hset)

end Noperthedron.Nopert214

end
