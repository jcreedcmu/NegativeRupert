module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Noperthedron.Vertices.Exact

@[expose] public section


/-!
This file proves the interior of the Noperthedron is nonempty.
-/

open scoped Matrix

namespace Noperthedron

open Real

/-- Four vertices forming a full-dimensional tetrahedron inside the Noperthedron. -/
noncomputable
def affineIndVertsR : Fin 4 → Euc(3) := ![C1R, C2R, C3R, -C1R]

/-- The three differences from `-C1R` have nonzero determinant. -/
theorem affineIndVertsRAffine : AffineIndependent ℝ affineIndVertsR := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ affineIndVertsR 3]
  rw [← linearIndependent_equiv (finSuccAboveEquiv 3)]
  let M : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
    (affineIndVertsR (Fin.castSucc i) - affineIndVertsR 3) j
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_fin_three]
    dsimp [M, affineIndVertsR, C1R, C2R, C3R, C1, C2, C3]
    norm_num
  have hli := (Matrix.linearIndependent_rows_of_det_ne_zero hdet).map'
    (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap (LinearEquiv.ker _)
  convert! hli using 1
  ext i j
  fin_cases i <;> simp [M, affineIndVertsR, finSuccAboveEquiv, Fin.succAbove]

theorem affineIndVertsR_span_eq_top :
    affineSpan ℝ (Set.range affineIndVertsR) = ⊤ := by
  rw [affineIndVertsRAffine.affineSpan_eq_top_iff_card_eq_finrank_add_one]
  simp [Fintype.card_fin]

/-- RzL at angle 0 is the identity. -/
lemma RzL_zero_eq_one : RzL (0 : ℝ) = 1 :=
  AddChar.map_zero_eq_one RzC

/--
All of the vertices we are showing to be affine independent actually
occur in the Noperthedron.
-/
theorem affineIndVertsR_subset_exactVerts :
    Set.range affineIndVertsR ⊆ (exactVerts : Set Euc(3)) := by
  rintro x ⟨i, rfl⟩
  fin_cases i <;>
    simp only [affineIndVertsR, exactVerts, Finset.coe_image] <;>
    [use ⟨0, 0, 0⟩; use ⟨0, 0, 1⟩; use ⟨0, 0, 2⟩; use ⟨0, 1, 0⟩] <;>
    simp [RzL_zero_eq_one, exactVertex, Cpt]

theorem exactVerts_affineSpan_eq_top :
    affineSpan ℝ (exactVerts : Set Euc(3)) = ⊤ := by
  rw [eq_top_iff, ← affineIndVertsR_span_eq_top]
  exact affineSpan_mono ℝ affineIndVertsR_subset_exactVerts

theorem interior_exactVerts_hull_nonempty :
    (interior ((convexHull ℝ) (exactVerts : Set (Euc(3))))).Nonempty :=
by
  exact interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
    exactVerts_affineSpan_eq_top

end Noperthedron
end
