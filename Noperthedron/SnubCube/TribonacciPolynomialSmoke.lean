module

public import Noperthedron.SnubCube.TribonacciPolynomial
public meta import Noperthedron.SnubCube.TribonacciPolynomial

@[expose] public section


/-!
# Smoke test for exact cubic-field polynomial cancellation
-/

namespace Noperthedron.SnubCube.TribonacciPolynomialSmoke

open Noperthedron.Checker
open TribonacciExpr TribonacciPolynomial

def x : Polynomial 2 := .var 0
def y : Polynomial 2 := .var 1

def seam : Polynomial 2 :=
  .const root * x + .const rootSq * y

def reducedConstant : TribonacciExpr :=
  root * rootSq - rootSq * root + ofRat 2

def quotient : Polynomial 2 :=
  .const reducedConstant + x * x + y * y

/-- Written in the association pattern produced by contact expansion. -/
def expanded : Polynomial 2 := seam * (seam * quotient)

/-- Written in the factored association pattern stored by a certificate. -/
def factored : Polynomial 2 := seam * seam * quotient

def smokeVars : Fin 2 → RatBall := ![
  RatBall.ofEndpoints (-1 / 10) (1 / 10),
  RatBall.ofEndpoints (-1 / 10) (1 / 10)]

def SmokeValid : Prop :=
  reducedConstant = ofRat 2 ∧
    0 < (evalBall smokeVars quotient).center -
      (evalBall smokeVars quotient).radius

instance : Decidable SmokeValid := by
  unfold SmokeValid
  infer_instance

theorem smoke_valid_kernel : SmokeValid := by
  decide +kernel

theorem smoke_valid_native : SmokeValid := by
  native_decide

theorem expanded_eval_eq_factored (values : Fin 2 → ℝ) :
    evalReal values expanded = evalReal values factored := by
  simp [expanded, factored]
  ring

theorem quotient_positive {values : Fin 2 → ℝ}
    (hvalues : ∀ i, (smokeVars i).Holds (values i)) :
    0 < evalReal values quotient :=
  evalReal_pos_of_lower_pos hvalues quotient smoke_valid_kernel.2

end Noperthedron.SnubCube.TribonacciPolynomialSmoke

end
