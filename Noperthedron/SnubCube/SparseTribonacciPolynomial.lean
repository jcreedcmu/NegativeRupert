module

public import Noperthedron.SnubCube.TribonacciPolynomial

@[expose] public section


/-!
# Canonical sparse polynomials over the snub-cube coordinate field

The transition charts contain exact cancellations before a structural seam
factor can be removed.  This representation keeps a sorted sparse list of
monomials, combines equal powers in the executable normalizer, and retains a
small kernel- and native-decidable checker.
-/

namespace Noperthedron.SnubCube.SparseTribonacciPolynomial

open Noperthedron.Checker
open TribonacciExpr

structure Term (n : ℕ) where
  powers : Fin n → ℕ
  coefficient : TribonacciExpr
deriving DecidableEq, Repr

abbrev Polynomial (n : ℕ) := List (Term n)

def Term.monomialKey {n : ℕ} (term : Term n) : List ℕ :=
  List.ofFn term.powers

noncomputable def Term.evalReal {n : ℕ} (vars : Fin n → ℝ)
    (term : Term n) : ℝ :=
  term.coefficient.eval * ∏ i, vars i ^ term.powers i

def Term.evalBall {n : ℕ} (vars : Fin n → RatBall)
    (term : Term n) : RatBall :=
  term.coefficient.evalBall * ∏ i, vars i ^ term.powers i

noncomputable def evalReal {n : ℕ} (vars : Fin n → ℝ)
    (polynomial : Polynomial n) : ℝ :=
  (polynomial.map (Term.evalReal vars)).sum

def evalBall {n : ℕ} (vars : Fin n → RatBall)
    (polynomial : Polynomial n) : RatBall :=
  (polynomial.map (Term.evalBall vars)).sum

theorem Term.evalBall_holds {n : ℕ} {vars : Fin n → RatBall}
    {values : Fin n → ℝ} (hvars : ∀ i, (vars i).Holds (values i))
    (term : Term n) :
    (term.evalBall vars).Holds (term.evalReal values) := by
  apply RatBall.holds_mul (TribonacciExpr.evalBall_holds term.coefficient)
  apply RatBall.holds_finset_prod
  intro i _
  exact RatBall.holds_pow (hvars i) (term.powers i)

theorem evalBall_holds {n : ℕ} {vars : Fin n → RatBall}
    {values : Fin n → ℝ} (hvars : ∀ i, (vars i).Holds (values i))
    (polynomial : Polynomial n) :
    (evalBall vars polynomial).Holds (evalReal values polynomial) := by
  induction polynomial with
  | nil => simp [evalBall, evalReal, RatBall.Holds]
  | cons head tail ih =>
      simp only [evalBall, evalReal, List.map_cons, List.sum_cons]
      exact RatBall.holds_add (Term.evalBall_holds hvars head) ih

/-- Insert one monomial into a normalized polynomial, combining its exact
coefficient with an existing equal monomial and deleting exact zeroes. -/
def insertTerm {n : ℕ} (term : Term n) : Polynomial n → Polynomial n
  | [] => if term.coefficient = 0 then [] else [term]
  | head :: tail =>
      if term.coefficient = 0 then head :: tail
      else if term.powers = head.powers then
        let coefficient := term.coefficient + head.coefficient
        if coefficient = 0 then tail else
          { powers := head.powers, coefficient := coefficient } :: tail
      else if term.monomialKey < head.monomialKey then
        term :: head :: tail
      else head :: insertTerm term tail

def normalize {n : ℕ} : Polynomial n → Polynomial n
  | [] => []
  | head :: tail => insertTerm head (normalize tail)

@[simp] theorem evalReal_nil {n : ℕ} (vars : Fin n → ℝ) :
    evalReal vars ([] : Polynomial n) = 0 := by
  simp [evalReal]

@[simp] theorem evalReal_cons {n : ℕ} (vars : Fin n → ℝ)
    (head : Term n) (tail : Polynomial n) :
    evalReal vars (head :: tail) =
      head.evalReal vars + evalReal vars tail := by
  simp [evalReal]

theorem evalReal_insertTerm {n : ℕ} (vars : Fin n → ℝ)
    (term : Term n) (polynomial : Polynomial n) :
    evalReal vars (insertTerm term polynomial) =
      term.evalReal vars + evalReal vars polynomial := by
  induction polynomial with
  | nil =>
      simp only [insertTerm]
      split <;> simp_all [Term.evalReal]
  | cons head tail ih =>
      simp only [insertTerm]
      split
      · rename_i hzero
        simp [hzero, Term.evalReal]
      split
      · rename_i hpowers
        split
        · rename_i hcoefficient
          simp only [evalReal_cons]
          have hcancel : term.evalReal vars + head.evalReal vars = 0 := by
            simp only [Term.evalReal, hpowers, ← add_mul, ← eval_add,
              hcoefficient, eval_zero, zero_mul]
          rw [show term.evalReal vars + (head.evalReal vars +
              evalReal vars tail) =
              (term.evalReal vars + head.evalReal vars) +
                evalReal vars tail by ring, hcancel, zero_add]
        · simp [Term.evalReal, hpowers]
          ring
      split
      · simp
      · rw [evalReal_cons, ih, evalReal_cons]
        ring

theorem evalReal_normalize {n : ℕ} (vars : Fin n → ℝ)
    (polynomial : Polynomial n) :
    evalReal vars (normalize polynomial) = evalReal vars polynomial := by
  induction polynomial with
  | nil => rfl
  | cons head tail ih =>
      rw [normalize, evalReal_insertTerm, ih, evalReal_cons]

def const {n : ℕ} (coefficient : TribonacciExpr) : Polynomial n :=
  normalize [{ powers := fun _ => 0, coefficient := coefficient }]

def var {n : ℕ} (index : Fin n) : Polynomial n :=
  [{ powers := fun i => if i = index then 1 else 0, coefficient := 1 }]

def add {n : ℕ} (left right : Polynomial n) : Polynomial n :=
  normalize (left ++ right)

def neg {n : ℕ} (value : Polynomial n) : Polynomial n :=
  normalize (value.map fun term => { term with
    coefficient := -term.coefficient })

def sub {n : ℕ} (left right : Polynomial n) : Polynomial n :=
  add left (neg right)

def Term.mul {n : ℕ} (left right : Term n) : Term n where
  powers := fun i => left.powers i + right.powers i
  coefficient := left.coefficient * right.coefficient

def mul {n : ℕ} (left right : Polynomial n) : Polynomial n :=
  normalize (left.flatMap fun a => right.map fun b => a.mul b)

def Term.factorOut {n : ℕ} (coordinate : Fin n) (power : ℕ)
    (term : Term n) : Term n where
  powers := fun i => if i = coordinate then term.powers i - power
    else term.powers i
  coefficient := term.coefficient

def HasFactor {n : ℕ} (coordinate : Fin n) (power : ℕ)
    (polynomial : Polynomial n) : Prop :=
  ∀ term ∈ normalize polynomial, power ≤ term.powers coordinate

instance {n : ℕ} (coordinate : Fin n) (power : ℕ)
    (polynomial : Polynomial n) :
    Decidable (HasFactor coordinate power polynomial) := by
  unfold HasFactor
  infer_instance

def factorOut {n : ℕ} (coordinate : Fin n) (power : ℕ)
    (polynomial : Polynomial n) : Polynomial n :=
  (normalize polynomial).map (Term.factorOut coordinate power)

theorem Term.evalReal_factorOut {n : ℕ} (vars : Fin n → ℝ)
    (coordinate : Fin n) (power : ℕ) (term : Term n)
    (hpower : power ≤ term.powers coordinate) :
    term.evalReal vars = vars coordinate ^ power *
      (term.factorOut coordinate power).evalReal vars := by
  classical
  let oldPower : Fin n → ℕ := term.powers
  let newPower : Fin n → ℕ :=
    (term.factorOut coordinate power).powers
  have hother :
      (∏ i ∈ Finset.univ.erase coordinate, vars i ^ oldPower i) =
        ∏ i ∈ Finset.univ.erase coordinate, vars i ^ newPower i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hine : i ≠ coordinate := Finset.ne_of_mem_erase hi
    simp [oldPower, newPower, Term.factorOut, hine]
  have hcoordinate : oldPower coordinate =
      power + newPower coordinate := by
    change term.powers coordinate = power +
      (term.factorOut coordinate power).powers coordinate
    rw [show (term.factorOut coordinate power).powers coordinate =
      term.powers coordinate - power by simp [Term.factorOut]]
    exact (Nat.add_sub_of_le hpower).symm
  have hold := Finset.prod_erase_mul
    (Finset.univ : Finset (Fin n))
    (fun i => vars i ^ oldPower i) (Finset.mem_univ coordinate)
  have hnew := Finset.prod_erase_mul
    (Finset.univ : Finset (Fin n))
    (fun i => vars i ^ newPower i) (Finset.mem_univ coordinate)
  simp only [Term.evalReal]
  change term.coefficient.eval * (∏ i, vars i ^ oldPower i) =
    vars coordinate ^ power *
      (term.coefficient.eval * ∏ i, vars i ^ newPower i)
  rw [← hold, ← hnew, hother, hcoordinate, pow_add]
  ring

theorem evalReal_factorOut {n : ℕ} (vars : Fin n → ℝ)
    (coordinate : Fin n) (power : ℕ) (polynomial : Polynomial n)
    (hfactor : HasFactor coordinate power polynomial) :
    evalReal vars polynomial = vars coordinate ^ power *
      evalReal vars (factorOut coordinate power polynomial) := by
  rw [← evalReal_normalize vars polynomial]
  unfold factorOut
  generalize hnormalized : normalize polynomial = normalized
  unfold HasFactor at hfactor
  rw [hnormalized] at hfactor
  clear hnormalized
  induction normalized with
  | nil => simp
  | cons head tail ih =>
      have hhead := hfactor head (by simp)
      have htail : ∀ term ∈ tail, power ≤ term.powers coordinate := by
        intro term hterm
        exact hfactor term (by simp [hterm])
      simp only [List.map_cons, evalReal_cons]
      rw [head.evalReal_factorOut vars coordinate power hhead,
        ih htail]
      ring

instance {n : ℕ} : Zero (Polynomial n) := ⟨const 0⟩
instance {n : ℕ} : One (Polynomial n) := ⟨const 1⟩
instance {n : ℕ} : Add (Polynomial n) := ⟨add⟩
instance {n : ℕ} : Neg (Polynomial n) := ⟨neg⟩
instance {n : ℕ} : Sub (Polynomial n) := ⟨sub⟩
instance {n : ℕ} : Mul (Polynomial n) := ⟨mul⟩

@[simp] theorem evalReal_const {n : ℕ} (vars : Fin n → ℝ)
    (coefficient : TribonacciExpr) :
    evalReal vars (const coefficient) = coefficient.eval := by
  unfold const
  rw [evalReal_normalize]
  simp [Term.evalReal]

@[simp] theorem evalReal_var {n : ℕ} (vars : Fin n → ℝ)
    (index : Fin n) : evalReal vars (var index) = vars index := by
  classical
  simp [var, evalReal, Term.evalReal]

@[simp] theorem evalReal_add {n : ℕ} (vars : Fin n → ℝ)
    (left right : Polynomial n) :
    evalReal vars (add left right) =
      evalReal vars left + evalReal vars right := by
  unfold add
  rw [evalReal_normalize]
  simp [evalReal]

@[simp] theorem evalReal_neg {n : ℕ} (vars : Fin n → ℝ)
    (value : Polynomial n) :
    evalReal vars (neg value) = -evalReal vars value := by
  unfold neg
  rw [evalReal_normalize]
  induction value with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, evalReal_cons] at ih ⊢
      simp [Term.evalReal, ih]
      ring

@[simp] theorem evalReal_sub {n : ℕ} (vars : Fin n → ℝ)
    (left right : Polynomial n) :
    evalReal vars (sub left right) =
      evalReal vars left - evalReal vars right := by
  simp [sub, sub_eq_add_neg]

theorem Term.evalReal_mul {n : ℕ} (vars : Fin n → ℝ)
    (left right : Term n) :
    (left.mul right).evalReal vars =
      left.evalReal vars * right.evalReal vars := by
  classical
  simp only [Term.evalReal, Term.mul, eval_mul]
  simp_rw [pow_add]
  rw [Finset.prod_mul_distrib]
  ring

theorem evalReal_map_term_mul {n : ℕ} (vars : Fin n → ℝ)
    (left : Term n) (right : Polynomial n) :
    evalReal vars (right.map (left.mul ·)) =
      left.evalReal vars * evalReal vars right := by
  induction right with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, evalReal_cons, Term.evalReal_mul, ih]
      ring

theorem evalReal_flatMap_mul {n : ℕ} (vars : Fin n → ℝ)
    (left right : Polynomial n) :
    evalReal vars (left.flatMap fun a => right.map (a.mul ·)) =
      evalReal vars left * evalReal vars right := by
  induction left with
  | nil => simp
  | cons head tail ih =>
      rw [List.flatMap_cons]
      rw [show evalReal vars
          (right.map (head.mul ·) ++
            tail.flatMap fun a => right.map (a.mul ·)) =
          evalReal vars (right.map (head.mul ·)) +
            evalReal vars (tail.flatMap fun a => right.map (a.mul ·)) by
              simp [evalReal]]
      rw [evalReal_map_term_mul, ih, evalReal_cons]
      ring

@[simp] theorem evalReal_mul {n : ℕ} (vars : Fin n → ℝ)
    (left right : Polynomial n) :
    evalReal vars (mul left right) =
      evalReal vars left * evalReal vars right := by
  unfold mul
  rw [evalReal_normalize, evalReal_flatMap_mul]

@[simp] theorem evalReal_zero {n : ℕ} (vars : Fin n → ℝ) :
    evalReal vars (0 : Polynomial n) = 0 := by
  change evalReal vars (const 0) = 0
  simp

@[simp] theorem evalReal_one {n : ℕ} (vars : Fin n → ℝ) :
    evalReal vars (1 : Polynomial n) = 1 := by
  change evalReal vars (const 1) = 1
  simp

@[simp] theorem evalReal_add_op {n : ℕ} (vars : Fin n → ℝ)
    (left right : Polynomial n) :
    evalReal vars (left + right) =
      evalReal vars left + evalReal vars right := by
  change evalReal vars (add left right) = _
  exact evalReal_add vars left right

@[simp] theorem evalReal_neg_op {n : ℕ} (vars : Fin n → ℝ)
    (value : Polynomial n) :
    evalReal vars (-value) = -evalReal vars value := by
  change evalReal vars (neg value) = _
  exact evalReal_neg vars value

@[simp] theorem evalReal_sub_op {n : ℕ} (vars : Fin n → ℝ)
    (left right : Polynomial n) :
    evalReal vars (left - right) =
      evalReal vars left - evalReal vars right := by
  change evalReal vars (sub left right) = _
  exact evalReal_sub vars left right

@[simp] theorem evalReal_mul_op {n : ℕ} (vars : Fin n → ℝ)
    (left right : Polynomial n) :
    evalReal vars (left * right) =
      evalReal vars left * evalReal vars right := by
  change evalReal vars (mul left right) = _
  exact evalReal_mul vars left right

/-- A positive lower endpoint proves positivity of the exact sparse
polynomial throughout the variable box. -/
theorem evalReal_pos_of_lower_pos {n : ℕ} {vars : Fin n → RatBall}
    {values : Fin n → ℝ} (hvars : ∀ i, (vars i).Holds (values i))
    (polynomial : Polynomial n)
    (hpos : 0 < (evalBall vars polynomial).center -
      (evalBall vars polynomial).radius) :
    0 < evalReal values polynomial :=
  RatBall.pos_of_holds_of_lower_pos (evalBall_holds hvars polynomial) hpos

/-! ## Exact affine recentering

Expanding around a rational box center before interval evaluation retains
the cancellations between large monomials that direct natural-interval
evaluation loses.  The expansion remains an exact sparse polynomial over the
same cubic field, so both the transformation and its final sign check are
kernel executable.
-/

def polynomialPower {n : ℕ} (value : Polynomial n) : ℕ → Polynomial n
  | 0 => 1
  | power + 1 => polynomialPower value power * value

def polynomialProduct {n : ℕ} : List (Polynomial n) → Polynomial n
  | [] => 1
  | head :: tail => head * polynomialProduct tail

def affineVariable {n : ℕ} (centers radii : Fin n → ℚ)
    (index : Fin n) : Polynomial n :=
  const (ofRat (centers index)) +
    const (ofRat (radii index)) * var index

def Term.recenter {n : ℕ} (term : Term n)
    (centers radii : Fin n → ℚ) : Polynomial n :=
  const term.coefficient * polynomialProduct
    (List.ofFn fun i =>
      polynomialPower (affineVariable centers radii i) (term.powers i))

def recenter {n : ℕ} (centers radii : Fin n → ℚ)
    (polynomial : Polynomial n) : Polynomial n :=
  polynomial.foldr (fun term answer => term.recenter centers radii + answer) 0

theorem evalReal_polynomialPower {n : ℕ} (vars : Fin n → ℝ)
    (value : Polynomial n) (power : ℕ) :
    evalReal vars (polynomialPower value power) =
      evalReal vars value ^ power := by
  induction power with
  | zero => simp [polynomialPower]
  | succ power ih => simp [polynomialPower, ih, pow_succ]

theorem evalReal_polynomialProduct {n : ℕ} (vars : Fin n → ℝ)
    (values : List (Polynomial n)) :
    evalReal vars (polynomialProduct values) =
      (values.map (evalReal vars)).prod := by
  induction values with
  | nil => simp [polynomialProduct]
  | cons head tail ih => simp [polynomialProduct, ih]

theorem evalReal_affineVariable {n : ℕ} (vars : Fin n → ℝ)
    (centers radii : Fin n → ℚ) (index : Fin n) :
    evalReal vars (affineVariable centers radii index) =
      (centers index : ℝ) + (radii index : ℝ) * vars index := by
  simp [affineVariable]

theorem evalReal_term_recenter {n : ℕ} (vars : Fin n → ℝ)
    (centers radii : Fin n → ℚ) (term : Term n) :
    evalReal vars (term.recenter centers radii) =
      term.evalReal (fun i =>
        (centers i : ℝ) + (radii i : ℝ) * vars i) := by
  simp only [Term.recenter, evalReal_mul_op, evalReal_const,
    evalReal_polynomialProduct, List.map_ofFn,
    List.prod_ofFn, Term.evalReal, Function.comp_apply]
  simp_rw [evalReal_polynomialPower, evalReal_affineVariable]

theorem evalReal_recenter {n : ℕ} (vars : Fin n → ℝ)
    (centers radii : Fin n → ℚ) (polynomial : Polynomial n) :
    evalReal vars (recenter centers radii polynomial) =
      evalReal (fun i =>
        (centers i : ℝ) + (radii i : ℝ) * vars i) polynomial := by
  induction polynomial with
  | nil => simp [recenter]
  | cons head tail ih =>
      change evalReal vars (head.recenter centers radii +
          recenter centers radii tail) = _
      rw [evalReal_add_op, evalReal_term_recenter vars centers radii head, ih,
        evalReal_cons]

def recenteredEvalBall {n : ℕ} (vars : Fin n → RatBall)
    (polynomial : Polynomial n) : RatBall :=
  evalBall (fun _ => RatBall.unit)
    (recenter (fun i => (vars i).center) (fun i => (vars i).radius)
      polynomial)

theorem recenteredEvalBall_holds {n : ℕ} {vars : Fin n → RatBall}
    {values : Fin n → ℝ} (hvars : ∀ i, (vars i).Holds (values i))
    (polynomial : Polynomial n) :
    (recenteredEvalBall vars polynomial).Holds
      (evalReal values polynomial) := by
  classical
  choose normalized hnormalized hvalue using fun i =>
    RatBall.exists_normalized_of_holds (hvars i)
  have henclose := evalBall_holds hnormalized
    (recenter (fun i => (vars i).center) (fun i => (vars i).radius)
      polynomial)
  rw [evalReal_recenter] at henclose
  have hfunctions :
      (fun i => ((vars i).center : ℝ) +
        ((vars i).radius : ℝ) * normalized i) = values := by
    funext i
    exact (hvalue i).symm
  rw [hfunctions] at henclose
  exact henclose

end Noperthedron.SnubCube.SparseTribonacciPolynomial

end
