module

public import Noperthedron.BalancedSupport.Basic

@[expose] public section


/-!
# Determinant-generated balance certificates

Three planar directions have canonical balancing weights given by their
pairwise determinants.  Keeping these weights symbolic makes the balance
equation an identity, rather than an interval condition checked numerically.
-/

namespace Noperthedron.BalancedSupport

/-- The standard determinant of two planar vectors. -/
def det2 (a b : ℝ²) : ℝ := a 0 * b 1 - a 1 * b 0

/-- Counterclockwise rotation through a right angle. -/
def quarterTurn (a : ℝ²) : ℝ² := !₂[-a 1, a 0]

@[simp] theorem quarterTurn_apply_zero (a : ℝ²) : quarterTurn a 0 = -a 1 := rfl
@[simp] theorem quarterTurn_apply_one (a : ℝ²) : quarterTurn a 1 = a 0 := rfl

theorem det2_quarterTurn (a b : ℝ²) :
    det2 (quarterTurn a) (quarterTurn b) = det2 a b := by
  simp [det2, quarterTurn]
  ring

/-- The two-dimensional Grassmann identity. -/
theorem det2_balance (u₀ u₁ u₂ : ℝ²) :
    det2 u₁ u₂ • u₀ + det2 u₂ u₀ • u₁ + det2 u₀ u₁ • u₂ = 0 := by
  ext i
  fin_cases i <;> simp [det2] <;> ring

/-- Canonical balancing weights for an ordered triple of directions. -/
def determinantWeights (u : Fin 3 → ℝ²) : Fin 3 → ℝ :=
  ![det2 (u 1) (u 2), det2 (u 2) (u 0), det2 (u 0) (u 1)]

@[simp] theorem determinantWeights_zero (u : Fin 3 → ℝ²) :
    determinantWeights u 0 = det2 (u 1) (u 2) := rfl

@[simp] theorem determinantWeights_one (u : Fin 3 → ℝ²) :
    determinantWeights u 1 = det2 (u 2) (u 0) := rfl

@[simp] theorem determinantWeights_two (u : Fin 3 → ℝ²) :
    determinantWeights u 2 = det2 (u 0) (u 1) := rfl

/-- Determinant weights balance exactly for every triple of directions. -/
theorem determinantWeights_balance (u : Fin 3 → ℝ²) :
    ∑ i, determinantWeights u i • u i = 0 := by
  simpa [Fin.sum_univ_succ, add_assoc] using det2_balance (u 0) (u 1) (u 2)

end Noperthedron.BalancedSupport

end
