module

public import Noperthedron.SnubCube.ProjectiveView
public import Noperthedron.BalancedSupport.Rodrigues
public import Noperthedron.Checker.RatBall

@[expose] public section


/-!
# Executable exact arithmetic in the tribonacci coordinate field

Snub-cube coordinates are quadratic expressions in the tribonacci root.
For the exact-zero tests needed at silhouette transitions it suffices to use
the three-dimensional quotient basis `1,t,t²`, reducing with
`t³ = t²+t+1` and `t⁴ = 2t²+2t+1`.
-/

namespace Noperthedron.SnubCube

open Noperthedron.BalancedSupport
open Noperthedron.Checker

/-- The certified decimal enclosure of the tribonacci root, packaged for
executable interval arithmetic. -/
def tribonacciBall : RatBall := RatBall.ofEndpoints
  (1839286755214161 / 10 ^ 15) (1839286755214162 / 10 ^ 15)

theorem tribonacciBall_holds : tribonacciBall.Holds tribonacci := by
  apply RatBall.holds_of_mem_Icc
  convert tribonacci_enclosure using 1
  all_goals norm_num

/-- A rational representative of an element of `ℚ[t]/(t³-t²-t-1)`. -/
structure TribonacciExpr where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
deriving DecidableEq, Repr

namespace TribonacciExpr

def zero : TribonacciExpr := ⟨0, 0, 0⟩
def one : TribonacciExpr := ⟨1, 0, 0⟩
def root : TribonacciExpr := ⟨0, 1, 0⟩
def rootSq : TribonacciExpr := ⟨0, 0, 1⟩
def ofRat (q : ℚ) : TribonacciExpr := ⟨q, 0, 0⟩

def add (a b : TribonacciExpr) : TribonacciExpr :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩

def neg (a : TribonacciExpr) : TribonacciExpr :=
  ⟨-a.c0, -a.c1, -a.c2⟩

def sub (a b : TribonacciExpr) : TribonacciExpr := add a (neg b)

/-- Multiplication reduced to the basis `1,t,t²`. -/
def mul (a b : TribonacciExpr) : TribonacciExpr :=
  let d0 := a.c0 * b.c0
  let d1 := a.c0 * b.c1 + a.c1 * b.c0
  let d2 := a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0
  let d3 := a.c1 * b.c2 + a.c2 * b.c1
  let d4 := a.c2 * b.c2
  ⟨d0 + d3 + d4, d1 + d3 + 2 * d4, d2 + d3 + 2 * d4⟩

instance instZero : Zero TribonacciExpr := ⟨zero⟩
instance instOne : One TribonacciExpr := ⟨one⟩
instance instAdd : Add TribonacciExpr := ⟨add⟩
instance instNeg : Neg TribonacciExpr := ⟨neg⟩
instance instSub : Sub TribonacciExpr := ⟨sub⟩
instance instMul : Mul TribonacciExpr := ⟨mul⟩

noncomputable def eval (a : TribonacciExpr) : ℝ :=
  a.c0 + a.c1 * tribonacci + a.c2 * tribonacci ^ 2

/-- Enclose an exact cubic-field coefficient only after reducing it to the
basis `1,t,t²`.  In particular, coefficients that cancel symbolically incur
no floating-point or vertex-approximation error. -/
def evalBall (a : TribonacciExpr) : RatBall :=
  RatBall.add
    (RatBall.add (RatBall.const a.c0)
      (RatBall.scale a.c1 tribonacciBall))
    (RatBall.scale a.c2 (RatBall.mul tribonacciBall tribonacciBall))

theorem evalBall_holds (a : TribonacciExpr) :
    a.evalBall.Holds a.eval := by
  have ht := tribonacciBall_holds
  have ht2 := RatBall.holds_mul ht ht
  have h0 := RatBall.holds_const a.c0
  have h1 := RatBall.holds_scale a.c1 ht
  have h2 := RatBall.holds_scale a.c2 ht2
  simpa [evalBall, eval, pow_two] using
    RatBall.holds_add (RatBall.holds_add h0 h1) h2

@[simp] theorem eval_zero : eval 0 = 0 := by
  change eval zero = 0
  norm_num [eval, zero]

@[simp] theorem eval_one : eval 1 = 1 := by
  change eval one = 1
  norm_num [eval, one]

@[simp] theorem eval_root : eval root = tribonacci := by
  simp [eval, root]

@[simp] theorem eval_rootSq : eval rootSq = tribonacci ^ 2 := by
  simp [eval, rootSq]

@[simp] theorem eval_ofRat (q : ℚ) : eval (ofRat q) = q := by
  simp [eval, ofRat]

@[simp] theorem eval_add (a b : TribonacciExpr) :
    eval (a + b) = eval a + eval b := by
  change eval (add a b) = eval a + eval b
  simp only [eval, add]
  push_cast
  ring

@[simp] theorem eval_neg (a : TribonacciExpr) : eval (-a) = -eval a := by
  change eval (neg a) = -eval a
  simp only [eval, neg]
  push_cast
  ring

@[simp] theorem eval_sub (a b : TribonacciExpr) :
    eval (a - b) = eval a - eval b := by
  change eval (sub a b) = eval a - eval b
  have hadd := eval_add a (neg b)
  change eval (add a (neg b)) = eval a + eval (neg b) at hadd
  rw [sub, hadd]
  have hneg := eval_neg b
  change eval (neg b) = -eval b at hneg
  rw [hneg]
  ring

theorem tribonacci_cubic :
    tribonacci ^ 3 = tribonacci ^ 2 + tribonacci + 1 := by
  have h := tribonacci_root
  simp only [tribonacciPolynomial] at h
  linarith

theorem tribonacci_fourth :
    tribonacci ^ 4 = 2 * tribonacci ^ 2 + 2 * tribonacci + 1 := by
  calc
    tribonacci ^ 4 = tribonacci * tribonacci ^ 3 := by ring
    _ = tribonacci * (tribonacci ^ 2 + tribonacci + 1) := by
      rw [tribonacci_cubic]
    _ = tribonacci ^ 3 + tribonacci ^ 2 + tribonacci := by ring
    _ = 2 * tribonacci ^ 2 + 2 * tribonacci + 1 := by
      rw [tribonacci_cubic]
      ring

theorem tribonacci_fifth :
    tribonacci ^ 5 = 4 * tribonacci ^ 2 + 3 * tribonacci + 2 := by
  calc
    tribonacci ^ 5 = tribonacci * tribonacci ^ 4 := by ring
    _ = tribonacci * (2 * tribonacci ^ 2 + 2 * tribonacci + 1) := by
      rw [tribonacci_fourth]
    _ = 2 * tribonacci ^ 3 + 2 * tribonacci ^ 2 + tribonacci := by ring
    _ = 4 * tribonacci ^ 2 + 3 * tribonacci + 2 := by
      rw [tribonacci_cubic]
      ring

@[simp] theorem eval_mul (a b : TribonacciExpr) :
    eval (a * b) = eval a * eval b := by
  change eval (mul a b) = eval a * eval b
  simp only [eval, mul]
  push_cast
  calc
    _ = (a.c0 : ℝ) * b.c0 +
        ((a.c0 : ℝ) * b.c1 + a.c1 * b.c0) * tribonacci +
        ((a.c0 : ℝ) * b.c2 + a.c1 * b.c1 + a.c2 * b.c0) *
          tribonacci ^ 2 +
        ((a.c1 : ℝ) * b.c2 + a.c2 * b.c1) * tribonacci ^ 3 +
        (a.c2 : ℝ) * b.c2 * tribonacci ^ 4 := by
          rw [tribonacci_cubic, tribonacci_fourth]
          ring
    _ = _ := by ring

/-! ## Canonical polynomial arithmetic

The executable representation is not merely a collection of exact-zero
tests: it is the cubic quotient ring itself.  Exposing the ring structure
allows `MvPolynomial` to collect transition expressions canonically before
we enclose the real root. -/

theorem ext {a b : TribonacciExpr} (h0 : a.c0 = b.c0)
    (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2) : a = b := by
  cases a
  cases b
  simp_all

@[simp] theorem add_c0 (a b : TribonacciExpr) :
    (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : TribonacciExpr) :
    (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : TribonacciExpr) :
    (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem neg_c0 (a : TribonacciExpr) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : TribonacciExpr) : (-a).c1 = -a.c1 := rfl
@[simp] theorem neg_c2 (a : TribonacciExpr) : (-a).c2 = -a.c2 := rfl
@[simp] theorem zero_c0 : (0 : TribonacciExpr).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : TribonacciExpr).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : TribonacciExpr).c2 = 0 := rfl
@[simp] theorem one_c0 : (1 : TribonacciExpr).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : TribonacciExpr).c1 = 0 := rfl
@[simp] theorem one_c2 : (1 : TribonacciExpr).c2 = 0 := rfl
@[simp] theorem ofRat_c0 (q : ℚ) : (ofRat q).c0 = q := rfl
@[simp] theorem ofRat_c1 (q : ℚ) : (ofRat q).c1 = 0 := rfl
@[simp] theorem ofRat_c2 (q : ℚ) : (ofRat q).c2 = 0 := rfl
@[simp] theorem mul_c0 (a b : TribonacciExpr) :
    (a * b).c0 =
      a.c0*b.c0 + (a.c1*b.c2+a.c2*b.c1) + a.c2*b.c2 := rfl
@[simp] theorem mul_c1 (a b : TribonacciExpr) :
    (a * b).c1 =
      a.c0*b.c1+a.c1*b.c0 + (a.c1*b.c2+a.c2*b.c1) +
        2*(a.c2*b.c2) := rfl
@[simp] theorem mul_c2 (a b : TribonacciExpr) :
    (a * b).c2 =
      a.c0*b.c2+a.c1*b.c1+a.c2*b.c0 +
        (a.c1*b.c2+a.c2*b.c1) + 2*(a.c2*b.c2) := rfl

instance instAddCommGroup : AddCommGroup TribonacciExpr where
  add := add
  add_assoc := by intro a b c; apply ext <;> simp <;> ring
  zero := zero
  zero_add := by intro a; apply ext <;> simp
  add_zero := by intro a; apply ext <;> simp
  nsmul := nsmulRec
  nsmul_zero := by intro; rfl
  nsmul_succ := by intro n a; rfl
  neg := neg
  neg_add_cancel := by
    intro a
    apply ext
    · change -a.c0 + a.c0 = 0; ring
    · change -a.c1 + a.c1 = 0; ring
    · change -a.c2 + a.c2 = 0; ring
  zsmul := zsmulRec
  add_comm := by intro a b; apply ext <;> simp <;> ring

instance instCommMonoid : CommMonoid TribonacciExpr where
  mul := mul
  mul_assoc := by intro a b c; apply ext <;> simp <;> ring
  one := one
  one_mul := by intro a; apply ext <;> simp
  mul_one := by intro a; apply ext <;> simp
  npow := npowRec
  npow_zero := by intro; rfl
  npow_succ := by intro n a; rfl
  mul_comm := by intro a b; apply ext <;> simp <;> ring

instance instCommRing : CommRing TribonacciExpr where
  __ := instAddCommGroup
  __ := instCommMonoid
  zero_mul := by intro a; apply ext <;> simp
  mul_zero := by intro a; apply ext <;> simp
  left_distrib := by intro a b c; apply ext <;> simp <;> ring
  right_distrib := by intro a b c; apply ext <;> simp <;> ring
  natCast := fun n => ofRat n
  natCast_zero := by apply ext <;> simp [ofRat]
  natCast_succ := by intro n; apply ext <;> simp [ofRat]
  intCast := fun z => ofRat z
  intCast_ofNat := by intro; rfl
  intCast_negSucc := by
    intro n
    apply ext
    · change ((Int.negSucc n : ℤ) : ℚ) = -((n + 1 : ℕ) : ℚ)
      norm_num
    · change (0 : ℚ) = 0
      rfl
    · change (0 : ℚ) = 0
      rfl

/-- Evaluation at the real tribonacci root as a ring homomorphism. -/
noncomputable def evalRingHom : TribonacciExpr →+* ℝ where
  toFun := eval
  map_zero' := eval_zero
  map_one' := eval_one
  map_add' := eval_add
  map_mul' := eval_mul

@[simp] theorem eval_eq_zero_of_eq_zero {a : TribonacciExpr} (h : a = 0) :
    eval a = 0 := by simp [h]

end TribonacciExpr

open TribonacciExpr

/-- Exact normalized snub-cube coordinates in the quotient basis. -/
def normalizedSymbolicVertex (i : VertexIndex) : Fin 3 → TribonacciExpr :=
  let base : Fin 3 → TribonacciExpr := ![root, 1, rootSq]
  fun c => ofRat ((signPattern i.permutation i.signs c : ℚ) / 5) *
    permute3 i.permutation base c

theorem eval_normalizedSymbolicVertex (i : VertexIndex) (c : Fin 3) :
    eval (normalizedSymbolicVertex i c) = normalizedExactVertex i c := by
  obtain ⟨p, s⟩ := i
  fin_cases p <;> fin_cases s <;> fin_cases c <;>
    simp [normalizedSymbolicVertex, normalizedExactVertex, exactVertex,
      vertexAt, signPattern, permutationOdd, oddSignPattern, evenSignPattern,
      permute3, PiLp.smul_apply, TribonacciExpr.eval_ofRat] <;> ring

def symbolicCross (a b : Fin 3 → TribonacciExpr) :
    Fin 3 → TribonacciExpr := ![
  a 1 * b 2 - a 2 * b 1,
  a 2 * b 0 - a 0 * b 2,
  a 0 * b 1 - a 1 * b 0]

theorem eval_symbolicCross (a b : Fin 3 → TribonacciExpr)
    (c : Fin 3) :
    eval (symbolicCross a b c) =
      (![eval (a 1) * eval (b 2) - eval (a 2) * eval (b 1),
        eval (a 2) * eval (b 0) - eval (a 0) * eval (b 2),
        eval (a 0) * eval (b 1) - eval (a 1) * eval (b 0)] c) := by
  fin_cases c <;> simp [symbolicCross]

def symbolicVertexDifference (a b : VertexIndex) :
    Fin 3 → TribonacciExpr :=
  fun c => normalizedSymbolicVertex a c - normalizedSymbolicVertex b c

/-- Exact algebraic coefficient of one projective support comparison. -/
def symbolicSupportCross (edgeStart edgeFinish support k : VertexIndex) :
    Fin 3 → TribonacciExpr :=
  symbolicCross (symbolicVertexDifference edgeStart edgeFinish)
    (symbolicVertexDifference k support)

theorem eval_symbolicSupportCross
    (edgeStart edgeFinish support k : VertexIndex) (c : Fin 3) :
    eval (symbolicSupportCross edgeStart edgeFinish support k c) =
      cross3 (normalizedExactVertex edgeStart -
          normalizedExactVertex edgeFinish)
        (normalizedExactVertex k - normalizedExactVertex support) c := by
  rw [symbolicSupportCross, eval_symbolicCross]
  fin_cases c <;>
    simp [symbolicVertexDifference, eval_normalizedSymbolicVertex,
      cross3, cross_apply] <;> ring

def symbolicDotRat (a : Fin 3 → ℚ) (b : Fin 3 → TribonacciExpr) :
    TribonacciExpr :=
  ofRat (a 0) * b 0 + ofRat (a 1) * b 1 + ofRat (a 2) * b 2

theorem eval_symbolicDotRat (a : Fin 3 → ℚ)
    (b : Fin 3 → TribonacciExpr) :
    eval (symbolicDotRat a b) =
      ProjectiveView.linearValue (fun i => (a i : ℝ))
        (fun i => eval (b i)) := by
  simp [symbolicDotRat, ProjectiveView.linearValue]

end Noperthedron.SnubCube

end
