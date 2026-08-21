module

public import Noperthedron.Checker.Local
public import Noperthedron.RationalApprox.RationalLocal2
public import Noperthedron.Checker.Local2Fast

@[expose] public section


/-!
# The second-order local row check

`Row.ValidLocal₂` asserts that a row certifies the second-order rational
local theorem (`rational_local₂`) at the row's per-axis half-widths.  It is
an alternative to the first-order `Row.ValidLocal` — the table checker tries
the first-order (cheaper) predicate first, so only rows produced with
second-order certificates pay for the extra partial-derivative atoms.

The `δ` of the second-order theorem is not stored in the row: `Row.δ₂`
derives it from the center pose as half the largest `BoundDelta₂ℚ`
left-hand side plus a `κℚ` bump (for the strict inequality).
-/

namespace Noperthedron.Solution

open RationalApprox (sqrtApprox16 κℚ ΔrotMℚ ΔrotRMℚ)
open RationalApprox.LocalTheorem (BoundR₂ℚ BoundDelta₂ℚ)

/-- The `i`-th left-hand side of the row's `BoundDelta₂ℚ` condition. -/
def Row.BoundDelta₂ℚi (row : Row) (i : Fin 3) : ℚ :=
  let p := row.interval.centerPose
  let P_ : Local.TriangleQ := pythonVertexA ∘ row.Pi
  let Q_ : Local.TriangleQ := pythonVertexA ∘ row.Qi
  sqrtApprox16.upper_sqrt.norm (p.rotRℚ (p.rotM₁ℚ (P_ i)) - p.rotM₂ℚ (Q_ i)) + 6 * κℚ
    + ΔrotRMℚ sqrtApprox16.upper_sqrt p.θ₁ p.φ₁ (P_ i) row.εα row.εθ₁ row.εφ₁
    + ΔrotMℚ sqrtApprox16.upper_sqrt p.θ₂ p.φ₂ (Q_ i) row.εθ₂ row.εφ₂

/-- The derived second-order `δ`: half the largest `BoundDelta₂ℚ` left-hand
side, bumped by `κℚ` so the strict inequality holds by construction. -/
def Row.δ₂ (row : Row) : ℚ :=
  Finset.max' (Finset.image row.BoundDelta₂ℚi Finset.univ)
    (Finset.image_nonempty.mpr ⟨0, Finset.mem_univ 0⟩) / 2 + κℚ

/-- `BoundDelta₂ℚ` holds at `Row.δ₂` by construction. -/
lemma Row.boundDelta₂_δ₂ (row : Row) :
    BoundDelta₂ℚ row.δ₂ row.interval.centerPose
      (pythonVertexA ∘ row.Pi) (pythonVertexA ∘ row.Qi)
      row.εα row.εθ₁ row.εφ₁ row.εθ₂ row.εφ₂ sqrtApprox16 := by
  intro i
  have hle := Finset.le_max' (Finset.image row.BoundDelta₂ℚi Finset.univ)
    (row.BoundDelta₂ℚi i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hκ : (0 : ℚ) < κℚ := by norm_num [κℚ]
  show row.BoundDelta₂ℚi i < 2 * row.δ₂
  unfold Row.δ₂
  linarith

/-- Assertion that a row constitutes a valid application of the second-order
rational local theorem at the row's per-axis half-widths. -/
@[mk_iff]
structure Row.ValidLocal₂ (row : Row) : Prop where
  nodeType_eq : row.nodeType = 2
  center_in_fourQ : row.interval.centerPose ∈ fourInterval ℚ
  exists_symmetry : ∃ s : TriangleSymmetry,
    s.applicable row.Qi ∧ ∀ i, row.Pi i = s.apply (row.Qi i)
  X₁_inner_gt : Local.TriangleQ.Aε₂ℚσ row.θ₁ row.φ₁ (pythonVertexA ∘ row.Pi)
    row.εθ₁ row.εφ₁ 0
  X₂_inner_gt : Local.TriangleQ.Aε₂ℚσ row.θ₂ row.φ₂ (pythonVertexA ∘ row.Qi)
    row.εθ₂ row.εφ₂ row.sigma_Q.val
  P_spanning : Local.TriangleQ.Spanning₂ℚ row.θ₁ row.φ₁ (pythonVertexA ∘ row.Pi)
    row.εθ₁ row.εφ₁
  Q_spanning : Local.TriangleQ.Spanning₂ℚ row.θ₂ row.φ₂ (pythonVertexA ∘ row.Qi)
    row.εθ₂ row.εφ₂
  rpos : 0 < row.r
  r_valid : BoundR₂ℚ row.r row.interval.centerPose (pythonVertexA ∘ row.Qi)
    row.εθ₂ row.εφ₂ sqrtApprox16
  Bε₂ℚ : Local.TriangleQ.Bε₂ℚ row.Qi pythonVertexA row.interval.centerPose
    row.εθ₂ row.εφ₂ row.δ₂ row.r sqrtApprox16.upper_sqrt

instance (row : Row) : Decidable (Row.ValidLocal₂ row) :=
  decidable_of_iff _ (Row.validLocal₂_iff row).symm

end Noperthedron.Solution
end
