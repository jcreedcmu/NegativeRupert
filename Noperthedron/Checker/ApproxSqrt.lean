module

public import Mathlib.Analysis.Real.Sqrt

public import Noperthedron.RationalApprox.Basic
-- Mirror the imports at the meta phase so the test `#eval`s below can
-- interpret cross-module code under the module system.
public meta import Mathlib.Analysis.Real.Sqrt
public meta import Noperthedron.RationalApprox.Basic

@[expose] public section


/-!
# Lower rational square root (§7.2.2 of [SY25])

We define a computable lower rational square-root function, following
Definition 47 and §7.2.2 of SY25:

  `sqrtℚLow x ≤ √(x : ℝ)` for `0 ≤ x`,

returning `0` on negative input (matching the convention used by
`Real.sqrt`). The companion *upper* square root of the checkers is the
fixed-point `sqrtℚUp16` in `Checker/SqrtFixed.lean` (which superseded the
`1 / sqrtℚLow (1/x)` construction this file originally carried).

## Construction

* `x = 0` ↦ `0`.
* `x > 0`: write `x = p/q` (in lowest terms, `p, q > 0`). We find the unique
  integer `a` such that `p · 100^a / q ∈ [10^20, 10^22)`, then compute
    `m := ⌊p · 100^a / q⌋`,
    `b := ⌊√m⌋`,
    `sqrtℚLow x := b · 10^(-a)`.
  This guarantees ten decimal digits of accuracy.

The implementation works in pure ℕ-arithmetic for the scale search, avoiding
the gcd cost of repeated rational multiplication. We maintain a state pair
`(num, den)` with the invariant `num/den = x · 100^a`. An "up" step multiplies
`num` by 100 (incrementing `a`); a "down" step multiplies `den` by 100
(decrementing `a`). Once in the window, `m = num / den` (integer division).
-/

namespace RationalApprox

open scoped BigOperators

/-! ## Constants and search loops -/

def lo : ℕ := 10 ^ 20
def hi : ℕ := 10 ^ 22

/-- **Up-search**: starting from `num`, multiply by 100 each step (incrementing
`k`) until either `num ≥ threshold` or fuel is exhausted. Returns `(k, num)`. -/
def shiftUpAux (threshold : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | num, k, 0          => (k, num)
  | num, k, fuel + 1   =>
      if num ≥ threshold then (k, num)
      else shiftUpAux threshold (num * 100) (k + 1) fuel

/-- **Down-search**: starting from `den`, multiply by 100 each step (incrementing
`k`) until either `numDivHi < den` or fuel is exhausted. Returns `(k, den)`.
The condition `numDivHi < den` is equivalent to `num < hi · den` when
`numDivHi = num / hi` (integer division). -/
def shiftDownAux (numDivHi : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | den, k, 0          => (k, den)
  | den, k, fuel + 1   =>
      if numDivHi < den then (k, den)
      else shiftDownAux numDivHi (den * 100) (k + 1) fuel

/-! ## The square-root functions -/

/-- Implementation of the lower rational square-root for `x = p/q > 0`,
parametrised by `fuel`. Returns the rational `(b : ℚ) · 10^(-a)` where
`a` is the chosen scale exponent and `b = ⌊√⌊p · 100^a / q⌋⌋`. -/
def sqrtℚLowImpl (p q fuel : ℕ) : ℚ :=
  if p < lo * q then
    let res := shiftUpAux (lo * q) p 0 fuel
    ((Nat.sqrt (res.2 / q) : ℚ)) * (10 : ℚ) ^ (-(res.1 : ℤ))
  else if p < hi * q then
    ((Nat.sqrt (p / q) : ℚ))
  else
    let res := shiftDownAux (p / hi) q 0 fuel
    ((Nat.sqrt (p / res.2) : ℚ)) * (10 : ℚ) ^ (res.1 : ℤ)

/-- **Lower rational square-root** (`√⁻`): returns `0` on `x ≤ 0`; otherwise
returns a rational `r` with `r ≤ √x`. -/
def sqrtℚLow (x : ℚ) : ℚ :=
  if x ≤ 0 then 0
  else
    let p : ℕ := x.num.toNat
    let q : ℕ := x.den
    let fuel : ℕ := Nat.log 10 p + Nat.log 10 q + 100
    sqrtℚLowImpl p q fuel

/-! ## Search-loop invariants -/

/-- Each step of `shiftUpAux` multiplies `num` by 100 and increments `k` by 1.
Hence the loop output `(k', num')` satisfies `k' = k + s` and `num' = num · 100^s`
for some step count `s ≤ fuel`. -/
private lemma shiftUpAux_invariant (threshold : ℕ) :
    ∀ (num k fuel : ℕ),
      ∃ s : ℕ, s ≤ fuel ∧
        (shiftUpAux threshold num k fuel).1 = k + s ∧
        (shiftUpAux threshold num k fuel).2 = num * 100 ^ s := by
  intro num k fuel
  induction fuel generalizing num k with
  | zero =>
    refine ⟨0, le_refl 0, ?_, ?_⟩ <;> simp [shiftUpAux]
  | succ f ih =>
    by_cases h : num ≥ threshold
    · refine ⟨0, Nat.zero_le _, ?_, ?_⟩ <;> simp [shiftUpAux, h]
    · obtain ⟨s, hs_le, hs_k, hs_num⟩ := ih (num := num * 100) (k := k + 1)
      refine ⟨s + 1, Nat.succ_le_succ hs_le, ?_, ?_⟩
      · simp only [shiftUpAux, if_neg h]
        rw [hs_k]; ring
      · simp only [shiftUpAux, if_neg h]
        rw [hs_num, pow_succ]; ring

/-- Each step of `shiftDownAux` multiplies `den` by 100 and increments `k` by 1. -/
private lemma shiftDownAux_invariant (numDivHi : ℕ) :
    ∀ (den k fuel : ℕ),
      ∃ s : ℕ, s ≤ fuel ∧
        (shiftDownAux numDivHi den k fuel).1 = k + s ∧
        (shiftDownAux numDivHi den k fuel).2 = den * 100 ^ s := by
  intro den k fuel
  induction fuel generalizing den k with
  | zero =>
    refine ⟨0, le_refl 0, ?_, ?_⟩ <;> simp [shiftDownAux]
  | succ f ih =>
    by_cases h : numDivHi < den
    · refine ⟨0, Nat.zero_le _, ?_, ?_⟩ <;> simp [shiftDownAux, h]
    · obtain ⟨s, hs_le, hs_k, hs_den⟩ := ih (den := den * 100) (k := k + 1)
      refine ⟨s + 1, Nat.succ_le_succ hs_le, ?_, ?_⟩
      · simp only [shiftDownAux, if_neg h]
        rw [hs_k]; ring
      · simp only [shiftDownAux, if_neg h]
        rw [hs_den, pow_succ]; ring

/-! ## Squared lower bound

The bound `(sqrtℚLow x)^2 ≤ x` follows uniformly from a single algebraic fact:
in each branch we maintain a positive `(num, den) : ℕ × ℕ` with
`(num : ℝ) / den = (x : ℝ) * 100^a`, and set `b = ⌊√⌊num/den⌋⌋`. Then
`(b : ℝ)^2 ≤ (num : ℝ) / den = x · 100^a`, from which
`((b : ℝ) · 10^(-a))^2 ≤ x` follows by multiplying by `100^(-a)`. -/

private lemma rat_pos_eq (x : ℚ) (hx : 0 < x) :
    ((x.num.toNat : ℕ) : ℝ) / ((x.den : ℕ) : ℝ) = (x : ℝ) := by
  have hnum_pos : 0 < x.num := Rat.num_pos.mpr hx
  have hcast : ((x.num.toNat : ℕ) : ℝ) = (x.num : ℝ) := by
    have : (x.num.toNat : ℤ) = x.num := Int.toNat_of_nonneg (le_of_lt hnum_pos)
    exact_mod_cast this
  rw [hcast]
  rw [Field.ratCast_def x]

/-- Core algebraic fact: from `b² · den ≤ num` (in ℕ) and `(num : ℝ) = xR · 100^a · den`,
deduce `(b · 10^(-a))² ≤ xR` in ℝ. -/
private lemma sq_bound_aux (xR : ℝ) (a : ℤ) (numN denN b : ℕ)
    (hden : 0 < denN)
    (hscaled : (numN : ℝ) = xR * (100 : ℝ) ^ a * (denN : ℝ))
    (hb : b * b * denN ≤ numN) :
    ((b : ℝ) * (10 : ℝ) ^ (-a)) ^ 2 ≤ xR := by
  have hdenR : (0 : ℝ) < (denN : ℝ) := mod_cast hden
  have hbR : (b : ℝ) * b * (denN : ℝ) ≤ (numN : ℝ) := mod_cast hb
  -- numN = xR · 100^a · denN, so divide by denN > 0
  have hbR' : (b : ℝ) * b ≤ xR * (100 : ℝ) ^ a := by
    rw [hscaled] at hbR
    exact le_of_mul_le_mul_right hbR hdenR
  -- ((b) * 10^(-a))² = b² * 100^(-a)
  have hLHS : ((b : ℝ) * (10 : ℝ) ^ (-a)) ^ 2 = (b : ℝ) * b * (100 : ℝ) ^ (-a) := by
    have h10sq : ((10 : ℝ) ^ (-a)) ^ 2 = (100 : ℝ) ^ (-a) := by
      rw [show ((10 : ℝ) ^ (-a)) ^ 2 = (10 : ℝ) ^ (2 * -a) from by
        rw [show (2 * -a : ℤ) = -a + -a from by ring,
            zpow_add₀ (by norm_num : (10 : ℝ) ≠ 0), pow_two]]
      rw [show (100 : ℝ) = 10 ^ 2 from by norm_num]
      rw [← zpow_natCast (10 : ℝ) 2, ← zpow_mul]
      ring_nf
    rw [mul_pow, pow_two (b : ℝ), h10sq]
  rw [hLHS]
  -- b² * 100^(-a) ≤ xR
  have h100neg_pos : (0 : ℝ) < (100 : ℝ) ^ (-a) := zpow_pos (by norm_num) _
  calc (b : ℝ) * b * (100 : ℝ) ^ (-a)
      ≤ xR * (100 : ℝ) ^ a * (100 : ℝ) ^ (-a) :=
        mul_le_mul_of_nonneg_right hbR' (le_of_lt h100neg_pos)
    _ = xR := by
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (100 : ℝ) ≠ 0)]; simp

/-- Squared lower bound for the implementation: if `xR = (p : ℝ)/q` with `q > 0`,
then `(sqrtℚLowImpl p q fuel)² ≤ xR`. -/
private lemma sqrtℚLowImpl_sq_le (p q fuel : ℕ) (hq : 0 < q) :
    ((sqrtℚLowImpl p q fuel : ℚ) : ℝ) ^ 2 ≤ ((p : ℝ) / q) := by
  unfold sqrtℚLowImpl
  split_ifs with hbr1 hbr2
  · -- Branch 1: p < lo * q (up-search)
    obtain ⟨s, _, hk_eq, hnum_eq⟩ := shiftUpAux_invariant (lo * q) p 0 fuel
    set res := shiftUpAux (lo * q) p 0 fuel
    have hk : res.1 = s := by simp [hk_eq]
    have hnum : res.2 = p * 100 ^ s := by simp [hnum_eq]
    have hcast :
        (((Nat.sqrt (res.2 / q) : ℚ) * (10 : ℚ) ^ (-(res.1 : ℤ)) : ℚ) : ℝ)
        = ((Nat.sqrt (res.2 / q) : ℝ)) * (10 : ℝ) ^ (-(res.1 : ℤ)) := by
      push_cast; rfl
    rw [hcast]
    apply sq_bound_aux ((p : ℝ) / q) (res.1 : ℤ) res.2 q (Nat.sqrt (res.2 / q)) hq
    · -- (res.2 : ℝ) = (p/q) · 100^res.1 · q
      rw [hnum, hk]
      push_cast
      rw [zpow_natCast]
      have hqne : (q : ℝ) ≠ 0 := ne_of_gt (mod_cast hq)
      field_simp
    · calc Nat.sqrt (res.2 / q) * Nat.sqrt (res.2 / q) * q
          ≤ (res.2 / q) * q := Nat.mul_le_mul_right _ (Nat.sqrt_le _)
        _ ≤ res.2 := Nat.div_mul_le_self _ _
  · -- Branch 2: lo*q ≤ p < hi*q (a = 0)
    have hcast : ((Nat.sqrt (p / q) : ℚ) : ℝ) = (Nat.sqrt (p / q) : ℝ) := by push_cast; rfl
    rw [hcast]
    rw [show ((Nat.sqrt (p / q) : ℝ))
        = ((Nat.sqrt (p / q) : ℝ)) * (10 : ℝ) ^ (-(0 : ℤ)) from by simp]
    apply sq_bound_aux ((p : ℝ) / q) (0 : ℤ) p q (Nat.sqrt (p / q)) hq
    · have hqne : (q : ℝ) ≠ 0 := ne_of_gt (mod_cast hq)
      field_simp
    · calc Nat.sqrt (p / q) * Nat.sqrt (p / q) * q
          ≤ (p / q) * q := Nat.mul_le_mul_right _ (Nat.sqrt_le _)
        _ ≤ p := Nat.div_mul_le_self _ _
  · -- Branch 3: p ≥ hi * q (down-search; a = -k)
    obtain ⟨s, _, hk_eq, hden_eq⟩ := shiftDownAux_invariant (p / hi) q 0 fuel
    set res := shiftDownAux (p / hi) q 0 fuel
    have hk : res.1 = s := by simp [hk_eq]
    have hden : res.2 = q * 100 ^ s := by simp [hden_eq]
    have hden_pos : 0 < res.2 := by rw [hden]; positivity
    have hcast :
        (((Nat.sqrt (p / res.2) : ℚ) * (10 : ℚ) ^ (res.1 : ℤ) : ℚ) : ℝ)
        = ((Nat.sqrt (p / res.2) : ℝ)) * (10 : ℝ) ^ (-(-(res.1 : ℤ))) := by
      push_cast; rw [neg_neg]
    rw [hcast]
    apply sq_bound_aux ((p : ℝ) / q) (-(res.1 : ℤ)) p res.2 (Nat.sqrt (p / res.2)) hden_pos
    · rw [hden, hk]
      push_cast
      rw [zpow_neg, zpow_natCast]
      have hqne : (q : ℝ) ≠ 0 := ne_of_gt (mod_cast hq)
      have h100ne : (100 : ℝ) ≠ 0 := by norm_num
      have h100ne' : (100 : ℝ)^s ≠ 0 := pow_ne_zero _ h100ne
      field_simp
    · calc Nat.sqrt (p / res.2) * Nat.sqrt (p / res.2) * res.2
          ≤ (p / res.2) * res.2 := Nat.mul_le_mul_right _ (Nat.sqrt_le _)
        _ ≤ p := Nat.div_mul_le_self _ _

/-- Squared lower bound: `(sqrtℚLow x)^2 ≤ x` (cast to ℝ) for `0 ≤ x`. -/
private lemma sqrtℚLow_sq_le (x : ℚ) (hx : 0 ≤ x) :
    ((sqrtℚLow x : ℚ) : ℝ) ^ 2 ≤ ((x : ℚ) : ℝ) := by
  rw [sqrtℚLow]
  split_ifs with h0
  · -- x ≤ 0 and 0 ≤ x: x = 0
    have : x = 0 := le_antisymm h0 hx
    simp [this]
  · push Not at h0
    have hxpos : 0 < x := h0
    have hq_pos : 0 < x.den := x.pos
    have hxR_eq : ((x.num.toNat : ℕ) : ℝ) / ((x.den : ℕ) : ℝ) = (x : ℝ) :=
      rat_pos_eq x hxpos
    have h := sqrtℚLowImpl_sq_le x.num.toNat x.den
      (Nat.log 10 x.num.toNat + Nat.log 10 x.den + 100) hq_pos
    rw [hxR_eq] at h
    exact h

/-- `√⁻ x ≤ √x` for `x ≥ 0` (Definition 47). -/
theorem sqrtℚLow_le_sqrt {x : ℚ} (hx : 0 ≤ x) :
    ((sqrtℚLow x : ℚ) : ℝ) ≤ Real.sqrt ((x : ℚ) : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  exact sqrtℚLow_sq_le x hx

def lowerSqrt : LowerSqrt where
  f := sqrtℚLow
  bound _ := sqrtℚLow_le_sqrt

end RationalApprox

/-! ## Sanity checks -/
section Examples
open RationalApprox

/-- info: 14142135623 / 10000000000 -/
#guard_msgs in
#eval sqrtℚLow 2

/-- info: 35355339059 / 50000000000 -/
#guard_msgs in
#eval sqrtℚLow (1/2)

/-- info: 10 -/
#guard_msgs in
#eval sqrtℚLow 100

end Examples

end
