module

public import Noperthedron.SnubCube.BernsteinCertificate
public import Noperthedron.SnubCube.ProjectiveTransitionBlowup

@[expose] public section


/-!
# Guarded transition parameterizations

The difficult transition band is split by the affine leading obstruction of
`family89`.  This file records the exact polynomial substitutions used by the
generator and the positive transverse/nested combination which cancels both
wild Cayley coordinates.
-/

namespace Noperthedron.SnubCube.ProjectiveTransitionGuarded

open ProjectiveTransitionBlowup
open SparseTribonacciPolynomial
open TribonacciExpr

abbrev Polynomial := SparseTribonacciPolynomial.Polynomial 5

def exact (c0 c1 c2 : ℚ) : TribonacciExpr := ⟨c0, c1, c2⟩

def tUpper : Polynomial :=
  const (exact (-1775 / 112) (-1025 / 112) (1325 / 112)) +
    const (exact (-3) (-2) 1) * var 1 +
    const (exact (75 / 28) (-75 / 28) (15 / 28)) * var 2

def tMiddle : Polynomial :=
  const (exact (-1475 / 112) (-1325 / 112) (1385 / 112)) +
    const (exact (-3) (-2) 1) * var 1 +
    const (exact (75 / 112) (-75 / 112) (15 / 112)) * var 2

def tLower : Polynomial :=
  const (exact (-25 / 2) (-25 / 2) (25 / 2)) +
    const (exact (-3) (-2) 1) * var 1 +
    const (exact (131 / 10) (25 / 2) (-25 / 2)) * var 2 +
    const (exact 3 2 (-1)) * var 1 * var 2

def substitutions (t : Polynomial) : Fin 5 → Polynomial :=
  ![var 0, var 1, var 3, var 4, t]

def guardedQuotient (family : Family) (t : Polynomial) : Polynomial :=
  compose family.quotient (substitutions t)

def upper89 : Polynomial := guardedQuotient family89 tUpper
def middle89 : Polynomial := guardedQuotient family89 tMiddle
def middleTransverse : Polynomial :=
  guardedQuotient familyTransverse tMiddle
def middleNested : Polynomial := guardedQuotient familyNested tMiddle
def middleWidth : Polynomial := guardedQuotient familyWidth tMiddle
def lowerTransverse : Polynomial :=
  guardedQuotient familyTransverse tLower
def lowerNested : Polynomial := guardedQuotient familyNested tLower

def transverseWeight : TribonacciExpr := exact 0 (8 / 625) (24 / 625)
def nestedWeight : TribonacciExpr := exact (8 / 625) 0 (16 / 625)

def weightedCombination (left right : Polynomial) : Polynomial :=
  const transverseWeight * left + const nestedWeight * right

def middleCombination : Polynomial :=
  weightedCombination middleTransverse middleNested

def lowerCombination : Polynomial :=
  weightedCombination lowerTransverse lowerNested

theorem transverseWeight_positive : 0 < transverseWeight.eval := by
  simp [transverseWeight, exact, TribonacciExpr.eval]
  nlinarith [tribonacci_pos, sq_nonneg tribonacci]

theorem nestedWeight_positive : 0 < nestedWeight.eval := by
  simp [nestedWeight, exact, TribonacciExpr.eval]
  nlinarith [tribonacci_pos, sq_nonneg tribonacci]

theorem eval_guardedQuotient (family : Family) (t : Polynomial)
    (values : Fin 5 → ℝ) :
    evalReal values (guardedQuotient family t) =
      evalReal ![values 0, values 1, values 3, values 4,
        evalReal values t] family.quotient := by
  rw [guardedQuotient, evalReal_compose]
  congr 1
  funext i
  fin_cases i <;> simp [substitutions]

theorem eval_weightedCombination (left right : Polynomial)
    (values : Fin 5 → ℝ) :
    evalReal values (weightedCombination left right) =
      transverseWeight.eval * evalReal values left +
        nestedWeight.eval * evalReal values right := by
  simp [weightedCombination]

/-- A nonnegative positive-weight combination proves that at least one of
the two constituent obstruction quotients is nonnegative. -/
theorem exists_nonnegative_of_weightedCombination
    (left right : Polynomial) (values : Fin 5 → ℝ)
    (hcombination : 0 ≤ evalReal values (weightedCombination left right)) :
    0 ≤ evalReal values left ∨ 0 ≤ evalReal values right := by
  rw [eval_weightedCombination] at hcombination
  by_contra h
  simp only [not_or, not_le] at h
  have hleft := mul_neg_of_pos_of_neg transverseWeight_positive h.1
  have hright := mul_neg_of_pos_of_neg nestedWeight_positive h.2
  linarith

end Noperthedron.SnubCube.ProjectiveTransitionGuarded

end
