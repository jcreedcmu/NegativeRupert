module

public import Noperthedron.SnubCube.ProjectiveTransitionBlowup

@[expose] public section


/-!
# Exact interval leaves for the blown-up transition chart

A leaf chooses one of the three exact contact families and a rational box in
the five chart variables `(d,e,a,b,t)`.  Its decidable validity predicate
checks every pointwise inequality needed later by the balanced-support
argument: strictly positive determinant weights, exact
support dominance over all 24 vertices, and positivity of the obstruction
quotient after its structural seam factor has been removed.
-/

namespace Noperthedron.SnubCube.ProjectiveTransitionBox

open Noperthedron.Checker
open ProjectiveTransitionBlowup
open SparseTribonacciPolynomial

def familyBank : Fin 5 → Family :=
  ![family2, family89, family192, familyTransverse, familyNested]

structure Box where
  familyIndex : Fin 5
  variableBalls : Fin 5 → RatBall
deriving DecidableEq, Repr

def Box.family (box : Box) : Family := familyBank box.familyIndex

def lower (ball : RatBall) : ℚ := ball.center - ball.radius
def upper (ball : RatBall) : ℚ := ball.center + ball.radius

def Box.polynomialBall (box : Box) (polynomial : Polynomial) : RatBall :=
  evalBall box.variableBalls polynomial

def Box.weightBall (box : Box) (i : Fin 3) : RatBall :=
  box.polynomialBall (box.family.weightPolynomial i)

def Box.supportBall (box : Box) (i : Fin 3) (vertex : Fin 24) : RatBall :=
  box.polynomialBall (box.family.supportPolynomial i vertex)

def Box.defectBall (box : Box) (i : Fin 3) : RatBall :=
  box.polynomialBall (box.family.defectPolynomial i)

def Box.supportSlackBall (box : Box) (i : Fin 3)
    (vertex : Fin 24) : RatBall :=
  box.polynomialBall (box.family.supportQuotient i vertex)

def Box.quotientBall (box : Box) : RatBall :=
  recenteredEvalBall box.variableBalls box.family.quotient

@[mk_iff]
structure Box.Valid (box : Box) : Prop where
  factor : box.family.FactorValid
  seam_nonnegative : 0 ≤ lower (box.variableBalls 0)
  tangential_nonnegative : 0 ≤ lower (box.variableBalls 1)
  weights_positive : ∀ i, 0 < lower (box.weightBall i)
  support_dominance : ∀ i vertex,
    0 ≤ lower (box.supportSlackBall i vertex)
  quotient_positive : 0 < lower box.quotientBall

instance (box : Box) : Decidable box.Valid :=
  decidable_of_iff _ (Box.valid_iff box).symm

theorem Box.polynomialBall_holds (box : Box) {values : Fin 5 → ℝ}
    (hvalues : ∀ i, (box.variableBalls i).Holds (values i))
    (polynomial : Polynomial) :
    (box.polynomialBall polynomial).Holds (evalReal values polynomial) := by
  exact evalBall_holds hvalues polynomial

theorem Box.quotientBall_holds (box : Box) {values : Fin 5 → ℝ}
    (hvalues : ∀ i, (box.variableBalls i).Holds (values i)) :
    box.quotientBall.Holds (evalReal values box.family.quotient) := by
  exact recenteredEvalBall_holds hvalues box.family.quotient

theorem Box.seam_nonnegative (box : Box) (h : box.Valid)
    {values : Fin 5 → ℝ}
    (hvalues : ∀ i, (box.variableBalls i).Holds (values i)) :
    0 ≤ values 0 := by
  exact RatBall.nonneg_of_holds_of_lower_nonneg (hvalues 0)
    h.seam_nonnegative

theorem Box.weight_nonnegative (box : Box) (h : box.Valid)
    {values : Fin 5 → ℝ}
    (hvalues : ∀ i, (box.variableBalls i).Holds (values i)) (i : Fin 3) :
    0 ≤ evalReal values (box.family.weightPolynomial i) := by
  exact RatBall.nonneg_of_holds_of_lower_nonneg
    (box.polynomialBall_holds hvalues _) (h.weights_positive i).le

theorem Box.weight_positive (box : Box) (h : box.Valid)
    {values : Fin 5 → ℝ}
    (hvalues : ∀ i, (box.variableBalls i).Holds (values i)) (i : Fin 3) :
    0 < evalReal values (box.family.weightPolynomial i) := by
  exact RatBall.pos_of_holds_of_lower_pos
    (box.polynomialBall_holds hvalues _) (h.weights_positive i)

theorem Box.tangential_nonnegative (box : Box) (h : box.Valid)
    {values : Fin 5 → ℝ}
    (hvalues : ∀ i, (box.variableBalls i).Holds (values i)) :
    0 ≤ values 1 := by
  exact RatBall.nonneg_of_holds_of_lower_nonneg (hvalues 1)
    h.tangential_nonnegative

theorem Box.exists_weight_positive (box : Box) (h : box.Valid)
    {values : Fin 5 → ℝ}
    (hvalues : ∀ i, (box.variableBalls i).Holds (values i)) :
    ∃ i, 0 < evalReal values (box.family.weightPolynomial i) := by
  exact ⟨0, box.weight_positive h hvalues 0⟩

theorem Box.support_le_defect (box : Box) (h : box.Valid)
    {values : Fin 5 → ℝ}
    (hvalues : ∀ i, (box.variableBalls i).Holds (values i))
    (i : Fin 3) (vertex : Fin 24) :
    evalReal values (box.family.supportPolynomial i vertex) ≤
      evalReal values (box.family.defectPolynomial i) := by
  have hslack := RatBall.nonneg_of_holds_of_lower_nonneg
    (box.polynomialBall_holds hvalues (box.family.supportQuotient i vertex))
    (h.support_dominance i vertex)
  have hfactor := box.family.eval_supportSlack_factor i vertex values
  have hseamPower : 0 ≤ values 0 ^
      box.family.supportFactorPower i vertex :=
    pow_nonneg (box.seam_nonnegative h hvalues) _
  have htangentialPower : 0 ≤ values 1 ^
      box.family.supportTangentialFactorPower i vertex :=
    pow_nonneg (box.tangential_nonnegative h hvalues) _
  have hfull : 0 ≤ evalReal values
      (box.family.supportSlackPolynomial i vertex) := by
    rw [hfactor]
    exact mul_nonneg hseamPower (mul_nonneg htangentialPower hslack)
  rw [Family.supportSlackPolynomial, evalReal_sub_op] at hfull
  linarith

theorem Box.quotient_positive (box : Box) (h : box.Valid)
    {values : Fin 5 → ℝ}
    (hvalues : ∀ i, (box.variableBalls i).Holds (values i)) :
    0 < evalReal values box.family.quotient := by
  exact RatBall.pos_of_holds_of_lower_pos
    (box.quotientBall_holds hvalues) h.quotient_positive

/-- Every valid rational leaf proves the complete denominator-cleared
transition obstruction nonnegative throughout its five-dimensional box. -/
theorem Box.obstruction_nonnegative (box : Box) (h : box.Valid)
    {values : Fin 5 → ℝ}
    (hvalues : ∀ i, (box.variableBalls i).Holds (values i)) :
    0 ≤ evalReal values box.family.obstruction := by
  rw [box.family.eval_obstruction_factor h.factor]
  exact mul_nonneg (pow_nonneg (box.seam_nonnegative h hvalues) _)
    (le_of_lt (box.quotient_positive h hvalues))

end Noperthedron.SnubCube.ProjectiveTransitionBox

end
