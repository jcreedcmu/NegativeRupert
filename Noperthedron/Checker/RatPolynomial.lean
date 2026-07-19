module

public import Noperthedron.Checker.RatBall

@[expose] public section


/-!
# Kernel-checkable multivariate rational polynomials

The syntax is intentionally tiny.  A fixed polynomial can be evaluated in
rational center-radius arithmetic by the executable checker, while
`evalBall_holds` supplies its once-for-all real soundness proof.
-/

namespace Noperthedron.Checker

inductive RatPolynomial (n : ℕ) where
  | const (q : ℚ)
  | var (i : Fin n)
  | add (p q : RatPolynomial n)
  | neg (p : RatPolynomial n)
  | mul (p q : RatPolynomial n)
deriving DecidableEq, Repr

namespace RatPolynomial

instance {n : ℕ} : Add (RatPolynomial n) := ⟨.add⟩
instance {n : ℕ} : Neg (RatPolynomial n) := ⟨.neg⟩
instance {n : ℕ} : Sub (RatPolynomial n) :=
  ⟨fun p q => .add p (.neg q)⟩
instance {n : ℕ} : Mul (RatPolynomial n) := ⟨.mul⟩
instance {n k : ℕ} : OfNat (RatPolynomial n) k := ⟨.const k⟩

def sub {n : ℕ} (p q : RatPolynomial n) : RatPolynomial n :=
  .add p (.neg q)

def scale {n : ℕ} (q : ℚ) (p : RatPolynomial n) : RatPolynomial n :=
  .mul (.const q) p

def evalReal {n : ℕ} (v : Fin n → ℝ) : RatPolynomial n → ℝ
  | .const q => q
  | .var i => v i
  | .add p q => evalReal v p + evalReal v q
  | .neg p => -evalReal v p
  | .mul p q => evalReal v p * evalReal v q

def evalBall {n : ℕ} (v : Fin n → RatBall) : RatPolynomial n → RatBall
  | .const q => RatBall.const q
  | .var i => v i
  | .add p q => RatBall.add (evalBall v p) (evalBall v q)
  | .neg p => RatBall.neg (evalBall v p)
  | .mul p q => RatBall.mul (evalBall v p) (evalBall v q)

theorem evalBall_holds {n : ℕ} {vb : Fin n → RatBall} {vr : Fin n → ℝ}
    (hvar : ∀ i, (vb i).Holds (vr i)) :
    ∀ p : RatPolynomial n, (evalBall vb p).Holds (evalReal vr p)
  | .const q => RatBall.holds_const q
  | .var i => hvar i
  | .add p q => RatBall.holds_add
      (evalBall_holds hvar p) (evalBall_holds hvar q)
  | .neg p => RatBall.holds_neg (evalBall_holds hvar p)
  | .mul p q => RatBall.holds_mul
      (evalBall_holds hvar p) (evalBall_holds hvar q)

@[simp] theorem evalReal_add {n : ℕ} (v : Fin n → ℝ)
    (p q : RatPolynomial n) :
    evalReal v (p + q) = evalReal v p + evalReal v q := rfl

@[simp] theorem evalReal_neg {n : ℕ} (v : Fin n → ℝ)
    (p : RatPolynomial n) :
    evalReal v (-p) = -evalReal v p := rfl

@[simp] theorem evalReal_mul {n : ℕ} (v : Fin n → ℝ)
    (p q : RatPolynomial n) :
    evalReal v (p * q) = evalReal v p * evalReal v q := rfl

@[simp] theorem evalReal_sub {n : ℕ} (v : Fin n → ℝ)
    (p q : RatPolynomial n) :
    evalReal v (p - q) = evalReal v p - evalReal v q := by
  rfl

@[simp] theorem evalReal_scale {n : ℕ} (v : Fin n → ℝ)
    (q : ℚ) (p : RatPolynomial n) :
    evalReal v (scale q p) = (q : ℝ) * evalReal v p := by
  rfl

end RatPolynomial

end Noperthedron.Checker

end
