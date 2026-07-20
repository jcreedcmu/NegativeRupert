module

public import Noperthedron.SnubCube.SparseTribonacciPolynomial
public meta import Noperthedron.SnubCube.SparseTribonacciPolynomial

@[expose] public section


namespace Noperthedron.SnubCube.SparseTribonacciPolynomialSmoke

open Noperthedron.Checker TribonacciExpr
open SparseTribonacciPolynomial

def cancelledSquare : Polynomial 2 :=
  let d : Polynomial 2 := var 0
  d * (1 + d) - d

def cancelledSquareQuotient : Polynomial 2 :=
  factorOut 0 2 cancelledSquare

theorem cancelledSquare_hasFactor_kernel :
    HasFactor 0 2 cancelledSquare := by
  decide +kernel

theorem cancelledSquare_hasFactor_native :
    HasFactor 0 2 cancelledSquare := by
  native_decide

theorem cancelledSquare_quotient_native :
    cancelledSquareQuotient = (1 : Polynomial 2) := by
  native_decide

theorem cancelledSquare_factor_semantic (d x : ℝ) :
    evalReal ![d, x] cancelledSquare = d ^ 2 *
      evalReal ![d, x] cancelledSquareQuotient := by
  exact evalReal_factorOut ![d, x] 0 2 cancelledSquare
    cancelledSquare_hasFactor_kernel

theorem cancelledSquare_eval (d x : ℝ) :
    evalReal ![d, x] cancelledSquare = d ^ 2 := by
  simp [cancelledSquare]
  ring

def composedCancelledSquare : Polynomial 1 :=
  compose cancelledSquare ![var 0, 1 + var 0]

theorem composedCancelledSquare_eval (x : ℝ) :
    evalReal ![x] composedCancelledSquare = x ^ 2 := by
  rw [composedCancelledSquare, evalReal_compose]
  simp [cancelledSquare]
  ring

def quotientBox : Fin 2 → RatBall := ![
  RatBall.ofEndpoints (-1 / 1000) (1 / 1000),
  RatBall.ofEndpoints (-10) 10]

def QuotientPositive : Prop :=
  0 < (evalBall quotientBox cancelledSquareQuotient).center -
    (evalBall quotientBox cancelledSquareQuotient).radius

instance : Decidable QuotientPositive := by
  unfold QuotientPositive
  infer_instance

theorem quotient_positive_kernel : QuotientPositive := by
  decide +kernel

theorem quotient_positive_native : QuotientPositive := by
  native_decide

end Noperthedron.SnubCube.SparseTribonacciPolynomialSmoke

end
