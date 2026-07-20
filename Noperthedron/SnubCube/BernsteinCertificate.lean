module

public import Noperthedron.SnubCube.SparseTribonacciPolynomial

@[expose] public section


/-!
# Tensor Bernstein range certificates

Bernstein control coefficients give tighter polynomial range bounds than
ordinary interval evaluation.  This file contains the representation-free
mathematics used by the snub-cube guarded transition checker: the univariate
Bernstein basis is nonnegative on the unit interval, sums to one, and tensor
products therefore form convex weights.
-/

namespace Noperthedron.SnubCube.BernsteinCertificate

open scoped BigOperators
open SparseTribonacciPolynomial

def basis (degree index : ℕ) (x : ℝ) : ℝ :=
  degree.choose index * x ^ index * (1 - x) ^ (degree - index)

theorem basis_nonnegative {degree index : ℕ} {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ basis degree index x := by
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 _))
    (pow_nonneg (sub_nonneg.mpr hx1) _)

theorem sum_basis (degree : ℕ) (x : ℝ) :
    ∑ index ∈ Finset.range (degree + 1), basis degree index x = 1 := by
  rw [show (1 : ℝ) = (x + (1 - x)) ^ degree by ring]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro index hindex
  simp only [basis]
  ring

def tensorBasis {n : ℕ} (degrees : Fin n → ℕ) (values : Fin n → ℝ)
    (index : Fin n → ℕ) : ℝ :=
  ∏ i, basis (degrees i) (index i) (values i)

def indexFinset {n : ℕ} (degrees : Fin n → ℕ) :
    Finset (Fin n → ℕ) :=
  Fintype.piFinset fun i => Finset.range (degrees i + 1)

theorem tensorBasis_nonnegative {n : ℕ} (degrees : Fin n → ℕ)
    {values : Fin n → ℝ} (hvalues : ∀ i, 0 ≤ values i ∧ values i ≤ 1)
    (index : Fin n → ℕ) :
    0 ≤ tensorBasis degrees values index := by
  exact Finset.prod_nonneg fun i _ =>
    basis_nonnegative (hvalues i).1 (hvalues i).2

theorem sum_tensorBasis {n : ℕ} (degrees : Fin n → ℕ)
    (values : Fin n → ℝ) :
    ∑ index ∈ indexFinset degrees, tensorBasis degrees values index = 1 := by
  change (∑ index ∈ Fintype.piFinset
      (fun i => Finset.range (degrees i + 1)),
        ∏ i, basis (degrees i) (index i) (values i)) = 1
  calc
    _ = ∏ i, ∑ j ∈ Finset.range (degrees i + 1),
          basis (degrees i) j (values i) :=
      (Finset.prod_univ_sum
        (fun i => Finset.range (degrees i + 1))
        (fun i j => basis (degrees i) j (values i))).symm
    _ = 1 := by simp only [sum_basis, Finset.prod_const_one]

/-- Tensor Bernstein evaluation is a convex combination of its control
coefficients, so a common lower bound on those coefficients bounds the
polynomial value. -/
theorem lower_le_sum_coeff_mul_tensorBasis {n : ℕ}
    (degrees : Fin n → ℕ) (coefficients : (Fin n → ℕ) → ℝ)
    {values : Fin n → ℝ} (hvalues : ∀ i, 0 ≤ values i ∧ values i ≤ 1)
    (lower : ℝ)
    (hlower : ∀ index ∈ indexFinset degrees, lower ≤ coefficients index) :
    lower ≤ ∑ index ∈ indexFinset degrees,
      coefficients index * tensorBasis degrees values index := by
  have hsum := sum_tensorBasis degrees values
  calc
    lower = ∑ index ∈ indexFinset degrees,
        lower * tensorBasis degrees values index := by
      rw [← Finset.mul_sum, hsum, mul_one]
    _ ≤ ∑ index ∈ indexFinset degrees,
        coefficients index * tensorBasis degrees values index := by
      apply Finset.sum_le_sum
      intro index hindex
      exact mul_le_mul_of_nonneg_right (hlower index hindex)
        (tensorBasis_nonnegative degrees hvalues index)

structure Table (n : ℕ) where
  degrees : Fin n → ℕ
  coefficient : (Fin n → ℕ) → TribonacciExpr
  indices : List (Fin n → ℕ)

noncomputable def Table.evalReal {n : ℕ} (table : Table n)
    (values : Fin n → ℝ) : ℝ :=
  ∑ index ∈ indexFinset table.degrees,
    (table.coefficient index).eval *
      tensorBasis table.degrees values index

def polynomialPow {n : ℕ} (polynomial : Polynomial n) : ℕ → Polynomial n
  | 0 => 1
  | power + 1 => polynomial * polynomialPow polynomial power

def basisPolynomial {n : ℕ} (degree index : ℕ) (coordinate : Fin n) :
    Polynomial n :=
  SparseTribonacciPolynomial.const (TribonacciExpr.ofRat (degree.choose index)) *
    polynomialPow (SparseTribonacciPolynomial.var coordinate) index *
      polynomialPow (1 - SparseTribonacciPolynomial.var coordinate)
        (degree - index)

def Table.tensorBasisPolynomial {n : ℕ} (table : Table n)
    (index : Fin n → ℕ) : Polynomial n :=
  (List.ofFn fun i => basisPolynomial (table.degrees i) (index i) i).foldr
    (· * ·) 1

def Table.toPolynomial {n : ℕ} (table : Table n) : Polynomial n :=
  table.indices.foldr
    (fun index answer =>
      SparseTribonacciPolynomial.const (table.coefficient index) *
        table.tensorBasisPolynomial index + answer)
    0

def Table.Complete {n : ℕ} (table : Table n) : Prop :=
  table.indices.Nodup ∧ table.indices.toFinset = indexFinset table.degrees

instance {n : ℕ} (table : Table n) : Decidable table.Complete := by
  unfold Table.Complete
  infer_instance

def termSignature {n : ℕ} (term : Term n) : List ℕ × TribonacciExpr :=
  (term.monomialKey, term.coefficient)

def polynomialSignature {n : ℕ} (polynomial : Polynomial n) :
    List (List ℕ × TribonacciExpr) :=
  (SparseTribonacciPolynomial.normalize polynomial).map termSignature

/-- An executable canonical equality test which compares exponent vectors as
lists.  Unlike the derived equality on `Fin n → ℕ`, this reduces in both the
kernel evaluator and native code. -/
def Table.Represents {n : ℕ} (table : Table n)
    (polynomial : Polynomial n) : Prop :=
  polynomialSignature table.toPolynomial = polynomialSignature polynomial

instance {n : ℕ} (table : Table n) (polynomial : Polynomial n) :
    Decidable (table.Represents polynomial) := by
  unfold Table.Represents
  infer_instance

theorem termSignature_injective {n : ℕ} :
    Function.Injective (termSignature : Term n → List ℕ × TribonacciExpr) := by
  intro left right h
  cases left with
  | mk leftPowers leftCoefficient =>
      cases right with
      | mk rightPowers rightCoefficient =>
          have hpowers : leftPowers = rightPowers :=
            List.ofFn_injective (congrArg Prod.fst h)
          have hcoefficient : leftCoefficient = rightCoefficient :=
            congrArg Prod.snd h
          cases hpowers
          cases hcoefficient
          rfl

theorem evalReal_eq_of_map_termSignature {n : ℕ} (values : Fin n → ℝ)
    {left right : Polynomial n}
    (h : left.map termSignature = right.map termSignature) :
    SparseTribonacciPolynomial.evalReal values left =
      SparseTribonacciPolynomial.evalReal values right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
      cases right with
      | nil => simp at h
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at h
          have hhead := termSignature_injective h.1
          subst other
          rw [SparseTribonacciPolynomial.evalReal_cons,
            SparseTribonacciPolynomial.evalReal_cons, ih h.2]

theorem evalReal_polynomialPow {n : ℕ} (values : Fin n → ℝ)
    (polynomial : Polynomial n) (power : ℕ) :
    SparseTribonacciPolynomial.evalReal values
        (polynomialPow polynomial power) =
      SparseTribonacciPolynomial.evalReal values polynomial ^ power := by
  induction power with
  | zero => simp [polynomialPow]
  | succ power ih => simp [polynomialPow, ih, pow_succ, mul_comm]

theorem evalReal_basisPolynomial {n : ℕ} (values : Fin n → ℝ)
    (degree index : ℕ) (coordinate : Fin n) :
    SparseTribonacciPolynomial.evalReal values
        (basisPolynomial degree index coordinate) =
      basis degree index (values coordinate) := by
  simp [basisPolynomial, basis, evalReal_polynomialPow]

theorem evalReal_foldr_mul {n : ℕ} (values : Fin n → ℝ)
    (polynomials : List (Polynomial n)) :
    SparseTribonacciPolynomial.evalReal values
        (polynomials.foldr (· * ·) 1) =
      (polynomials.map (SparseTribonacciPolynomial.evalReal values)).prod := by
  induction polynomials with
  | nil => simp
  | cons head tail ih => simp [ih]

theorem Table.evalReal_tensorBasisPolynomial {n : ℕ} (table : Table n)
    (values : Fin n → ℝ) (index : Fin n → ℕ) :
    SparseTribonacciPolynomial.evalReal values
        (table.tensorBasisPolynomial index) =
      tensorBasis table.degrees values index := by
  rw [Table.tensorBasisPolynomial, evalReal_foldr_mul]
  simp only [List.map_ofFn, Function.comp_apply, evalReal_basisPolynomial,
    List.prod_ofFn, tensorBasis]

theorem sum_map_eq_sum_toFinset {α : Type} [DecidableEq α]
    (items : List α) (hitems : items.Nodup) (f : α → ℝ) :
    (items.map f).sum = ∑ item ∈ items.toFinset, f item := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.nodup_cons] at hitems
      simp [ih hitems.2, hitems.1]

theorem Table.evalReal_toPolynomial {n : ℕ} (table : Table n)
    (hcomplete : table.Complete) (values : Fin n → ℝ) :
    SparseTribonacciPolynomial.evalReal values table.toPolynomial =
      table.evalReal values := by
  have hfold :
      SparseTribonacciPolynomial.evalReal values table.toPolynomial =
        (table.indices.map fun index =>
          (table.coefficient index).eval *
            tensorBasis table.degrees values index).sum := by
    unfold Table.toPolynomial
    induction table.indices with
    | nil => simp
    | cons head tail ih => simp [ih, table.evalReal_tensorBasisPolynomial]
  have hlist := sum_map_eq_sum_toFinset table.indices hcomplete.1
    (fun index => (table.coefficient index).eval *
      tensorBasis table.degrees values index)
  rw [hfold, hlist, hcomplete.2]
  rfl

theorem Table.evalReal_eq_of_represents {n : ℕ} (table : Table n)
    (polynomial : Polynomial n) (hcomplete : table.Complete)
    (h : table.Represents polynomial)
    (values : Fin n → ℝ) :
    SparseTribonacciPolynomial.evalReal values polynomial =
      table.evalReal values := by
  rw [← table.evalReal_toPolynomial hcomplete values,
    ← SparseTribonacciPolynomial.evalReal_normalize values table.toPolynomial,
    ← SparseTribonacciPolynomial.evalReal_normalize values polynomial]
  exact (evalReal_eq_of_map_termSignature values h).symm

def Table.LowerValid {n : ℕ} (table : Table n) (lower : ℚ) : Prop :=
  ∀ index ∈ indexFinset table.degrees,
    lower ≤ (table.coefficient index).evalBall.center -
      (table.coefficient index).evalBall.radius

instance {n : ℕ} (table : Table n) (lower : ℚ) :
    Decidable (table.LowerValid lower) := by
  unfold Table.LowerValid
  infer_instance

theorem Table.lower_le_evalReal {n : ℕ} (table : Table n) (lower : ℚ)
    {values : Fin n → ℝ} (hvalues : ∀ i, 0 ≤ values i ∧ values i ≤ 1)
    (hvalid : table.LowerValid lower) :
    (lower : ℝ) ≤ table.evalReal values := by
  apply lower_le_sum_coeff_mul_tensorBasis table.degrees
    (fun index => (table.coefficient index).eval) hvalues
  intro index hindex
  have hlower : (lower : ℝ) ≤
      ((table.coefficient index).evalBall.center -
        (table.coefficient index).evalBall.radius : ℚ) := by
    exact_mod_cast hvalid index hindex
  exact hlower.trans (Noperthedron.Checker.RatBall.lower_le_of_holds
    (TribonacciExpr.evalBall_holds (table.coefficient index)))

theorem Table.lower_le_polynomial {n : ℕ} (table : Table n)
    (polynomial : Polynomial n) (lower : ℚ)
    (hcomplete : table.Complete) (hrepresents : table.Represents polynomial)
    {values : Fin n → ℝ} (hvalues : ∀ i, 0 ≤ values i ∧ values i ≤ 1)
    (hvalid : table.LowerValid lower) :
    (lower : ℝ) ≤ SparseTribonacciPolynomial.evalReal values polynomial := by
  rw [table.evalReal_eq_of_represents polynomial hcomplete hrepresents values]
  exact table.lower_le_evalReal lower hvalues hvalid

end Noperthedron.SnubCube.BernsteinCertificate

end
