module

public import Noperthedron.SnubCube.ExactArithmetic

@[expose] public section


/-!
# Kernel-checkable polynomials over the snub-cube coordinate field

Transition quotients are generated with coefficients in
`ℚ[t]/(t³-t²-t-1)`.  Exact coefficient cancellations happen before the
result is interval-enclosed.  The deliberately small expression language is
fully executable, so the same certificate can be checked both by the kernel
evaluator and by `native_decide`.
-/

namespace Noperthedron.SnubCube.TribonacciPolynomial

open Noperthedron.Checker
open TribonacciExpr

inductive Polynomial (n : ℕ) where
  | const (value : TribonacciExpr)
  | var (index : Fin n)
  | add (left right : Polynomial n)
  | neg (value : Polynomial n)
  | mul (left right : Polynomial n)
deriving DecidableEq, Repr

instance {n : ℕ} : Zero (Polynomial n) := ⟨.const 0⟩
instance {n : ℕ} : One (Polynomial n) := ⟨.const 1⟩
instance {n : ℕ} : Add (Polynomial n) := ⟨.add⟩
instance {n : ℕ} : Neg (Polynomial n) := ⟨.neg⟩
instance {n : ℕ} : Sub (Polynomial n) :=
  ⟨fun left right => .add left (.neg right)⟩
instance {n : ℕ} : Mul (Polynomial n) := ⟨.mul⟩

/-- Exact real evaluation, through the certified cubic-field homomorphism. -/
noncomputable def evalReal {n : ℕ} (vars : Fin n → ℝ)
    : Polynomial n → ℝ
  | .const value => value.eval
  | .var index => vars index
  | .add left right => evalReal vars left + evalReal vars right
  | .neg value => -evalReal vars value
  | .mul left right => evalReal vars left * evalReal vars right

/-- Interval evaluation after exact polynomial normalization. -/
def evalBall {n : ℕ} (vars : Fin n → RatBall)
    : Polynomial n → RatBall
  | .const value => value.evalBall
  | .var index => vars index
  | .add left right => RatBall.add (evalBall vars left) (evalBall vars right)
  | .neg value => RatBall.neg (evalBall vars value)
  | .mul left right => RatBall.mul (evalBall vars left) (evalBall vars right)

/-- Soundness of the executable algebraic-polynomial enclosure. -/
theorem evalBall_holds {n : ℕ} {vars : Fin n → RatBall}
    {values : Fin n → ℝ} (hvars : ∀ i, (vars i).Holds (values i))
    : ∀ p : Polynomial n,
      (evalBall vars p).Holds (evalReal values p)
  | .const value => TribonacciExpr.evalBall_holds value
  | .var index => hvars index
  | .add left right =>
      RatBall.holds_add (evalBall_holds hvars left)
        (evalBall_holds hvars right)
  | .neg value => RatBall.holds_neg (evalBall_holds hvars value)
  | .mul left right =>
      RatBall.holds_mul (evalBall_holds hvars left)
        (evalBall_holds hvars right)

@[simp] theorem evalReal_const {n : ℕ} (vars : Fin n → ℝ)
    (value : TribonacciExpr) :
    evalReal vars (.const value) = value.eval := rfl

@[simp] theorem evalReal_zero {n : ℕ} (vars : Fin n → ℝ) :
    evalReal vars (0 : Polynomial n) = 0 := by simp [evalReal]

@[simp] theorem evalReal_one {n : ℕ} (vars : Fin n → ℝ) :
    evalReal vars (1 : Polynomial n) = 1 := by simp [evalReal]

@[simp] theorem evalReal_var {n : ℕ} (vars : Fin n → ℝ) (index : Fin n) :
    evalReal vars (.var index) = vars index := rfl

@[simp] theorem evalReal_add {n : ℕ} (vars : Fin n → ℝ)
    (left right : Polynomial n) :
    evalReal vars (left + right) =
      evalReal vars left + evalReal vars right := rfl

@[simp] theorem evalReal_neg {n : ℕ} (vars : Fin n → ℝ)
    (value : Polynomial n) :
    evalReal vars (-value) = -evalReal vars value := rfl

@[simp] theorem evalReal_sub {n : ℕ} (vars : Fin n → ℝ)
    (left right : Polynomial n) :
    evalReal vars (left - right) =
      evalReal vars left - evalReal vars right := by rfl

@[simp] theorem evalReal_mul {n : ℕ} (vars : Fin n → ℝ)
    (left right : Polynomial n) :
    evalReal vars (left * right) =
      evalReal vars left * evalReal vars right := rfl

/-- A strictly positive lower endpoint proves positivity of the exact
polynomial throughout the variable box. -/
theorem evalReal_pos_of_lower_pos {n : ℕ} {vars : Fin n → RatBall}
    {values : Fin n → ℝ} (hvars : ∀ i, (vars i).Holds (values i))
    (p : Polynomial n)
    (hpos : 0 < (evalBall vars p).center - (evalBall vars p).radius) :
    0 < evalReal values p :=
  RatBall.pos_of_holds_of_lower_pos (evalBall_holds hvars p) hpos

end Noperthedron.SnubCube.TribonacciPolynomial

end
