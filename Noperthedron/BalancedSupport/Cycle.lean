module

public import Mathlib.GroupTheory.Perm.Fin
public import Noperthedron.BalancedSupport.Determinant
public import Noperthedron.BalancedSupport.LocalRigidity
public import Noperthedron.BalancedSupport.Rupert

@[expose] public section


/-!
# Balanced support from a projected polygonal cycle

The clockwise normals of the edges of any closed projected polygon sum to
zero.  This supplies a pose-dependent balanced family with unit weights,
allowing certificate directions to follow the outer silhouette instead of
being frozen at the center of a parameter box.
-/

namespace Noperthedron.BalancedSupport

open scoped RealInnerProductSpace

/-- Cyclic successor on a nonempty finite type. -/
def cycleNext (n : ℕ) : Fin (n + 1) ≃ Fin (n + 1) :=
  Fin.cycleRange (Fin.last n)

theorem sum_comp_cycleNext {M : Type} [AddCommMonoid M]
    (n : ℕ) (f : Fin (n + 1) → M) :
    ∑ i, f (cycleNext n i) = ∑ i, f i := by
  exact Equiv.sum_comp (cycleNext n) f

/-- Clockwise edge normal.  `quarterTurn` is counterclockwise, so the edge
is written from its successor back to its current vertex. -/
noncomputable def cycleDirection {ι : Type} [Fintype ι]
    (p : MatrixPose) (poly : Polyhedron ι ℝ³) {n : ℕ}
    (Q : Fin (n + 1) → ι) (i : Fin (n + 1)) : ℝ² :=
  quarterTurn (outerProjectionLinear p
    (poly.v (Q i) - poly.v (Q (cycleNext n i))))

private theorem sum_quarterTurn {κ : Type} [Fintype κ] (f : κ → ℝ²) :
    ∑ i, quarterTurn (f i) = quarterTurn (∑ i, f i) := by
  ext c
  fin_cases c <;> simp [quarterTurn]

/-- Edge normals around a projected cycle balance identically. -/
theorem cycleDirection_balance {ι : Type} [Fintype ι]
    (p : MatrixPose) (poly : Polyhedron ι ℝ³) {n : ℕ}
    (Q : Fin (n + 1) → ι) :
    ∑ i, cycleDirection p poly Q i = 0 := by
  simp_rw [cycleDirection]
  rw [sum_quarterTurn]
  rw [← map_sum, Finset.sum_sub_distrib]
  have hsum := sum_comp_cycleNext n (fun i => poly.v (Q i))
  rw [hsum, sub_self, map_zero]
  simp [quarterTurn]

/-- A cyclic outer-edge certificate with explicit support defects excludes a
Rupert pose.  All weights are one; translation cancellation is the
telescoping identity above. -/
theorem not_rupertPose_of_cycle_support_with_defect
    {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : Polyhedron ι ℝ³) (p : MatrixPose) {n : ℕ}
    (P Q : Fin (n + 1) → ι) (defect : Fin (n + 1) → ℝ)
    (hdirection : ∀ i, cycleDirection p poly Q i ≠ 0)
    (hsupport : ∀ i k,
      ⟪cycleDirection p poly Q i,
        outerProjectionLinear p (poly.v k - poly.v (Q i))⟫ ≤ defect i)
    (hdisplacement :
      ∑ i, defect i ≤ ∑ i,
        ⟪cycleDirection p poly Q i,
          proj_xyL (p.innerRot.val.toEuclideanLin (poly.v (P i))) -
            proj_xyL (p.outerRot.val.toEuclideanLin (poly.v (Q i)))⟫) :
    ¬ RupertPose p poly.hull := by
  apply not_rupertPose_of_balanced_support_with_defect
    poly p P Q (fun _ => 1) (cycleDirection p poly Q) defect
  · exact hdirection
  · intro i
    norm_num
  · exact ⟨0, by norm_num⟩
  · simpa using cycleDirection_balance p poly Q
  · intro i y hy
    rcases hy with ⟨v, ⟨k, rfl⟩, rfl⟩
    simpa [outerProjectionLinear, outerProj, PoseLike.outer,
      map_sub, inner_sub_right, add_comm] using
      hsupport i k
  · simpa using hdisplacement

end Noperthedron.BalancedSupport

end
