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

noncomputable def Table.evalReal {n : ℕ} (table : Table n)
    (values : Fin n → ℝ) : ℝ :=
  ∑ index ∈ indexFinset table.degrees,
    (table.coefficient index).eval *
      tensorBasis table.degrees values index

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

end Noperthedron.SnubCube.BernsteinCertificate

end
