module

public import Noperthedron.Checker.ApproxSqrt

@[expose] public section


/-!
# Fixed-point upper square root

`sqrtℚUp16` is an upper rational square root whose output always has
denominator dividing `10¹⁶`: for `x > 0`,

    sqrtℚUp16 x = (Nat.sqrt ⌈x · 10³²⌉ + 1) / 10¹⁶ ≥ √x.

Compared to the retired ℚ-Newton upper sqrt (accuracy ~10⁻¹⁰, output
denominators arbitrary), this is both *more accurate* (error < 2·10⁻¹⁶
relative to the input scale) and *fixed-point*, which is what lets the
checkers' hot loops run on integer numerators with statically known scales:
every upper-sqrt output is an integer multiple of `10⁻¹⁶`, and for inputs
that are themselves multiples of `10⁻³²` the ceiling is exact. The lower
square root `sqrtℚLow13` (in `Checker/ApproxSqrt.lean`) has the same
fixed-point shape at scale `10⁻¹³`.

`sqrtApprox16` packages it as an `Approx` together with the fixed-point
lower square root `sqrtℚLow13` from `Checker/ApproxSqrt.lean`. Since upper
square roots only ever appear in check-hardening positions, any upper bound
is sound here, and a tighter one only makes it easier for certificate rows
to pass.
-/

namespace RationalApprox

/-- Fixed-point upper square root: `√x ≤ sqrtℚUp16 x`, with output an integer
multiple of `10⁻¹⁶` (and `0` for `x ≤ 0`). -/
def sqrtℚUp16 (x : ℚ) : ℚ :=
  if x ≤ 0 then 0
  else (Nat.sqrt ⌈x * 10 ^ 32⌉.toNat + 1) / 10 ^ 16

theorem sqrtℚUp16_nonneg (x : ℚ) : 0 ≤ sqrtℚUp16 x := by
  unfold sqrtℚUp16
  positivity

/-- The upper-bound property: `√x ≤ sqrtℚUp16 x` for `0 ≤ x`. -/
theorem sqrt_le_sqrtℚUp16 (x : ℚ) (hx : 0 ≤ x) :
    Real.sqrt ((x : ℚ) : ℝ) ≤ ((sqrtℚUp16 x : ℚ) : ℝ) := by
  unfold sqrtℚUp16
  split_ifs with h0
  · -- x ≤ 0 and 0 ≤ x: x = 0
    have : x = 0 := le_antisymm h0 hx
    simp [this]
  · push Not at h0
    set N : ℕ := ⌈x * 10 ^ 32⌉.toNat with hN_def
    -- x · 10³² ≤ N in ℝ
    have hxN : ((x : ℚ) : ℝ) * 10 ^ 32 ≤ (N : ℝ) := by
      have hceil : (x * 10 ^ 32 : ℚ) ≤ (⌈x * 10 ^ 32⌉ : ℚ) := Int.le_ceil _
      have htoNat : (⌈x * 10 ^ 32⌉ : ℤ) ≤ (N : ℤ) := by
        rw [hN_def]
        exact Int.self_le_toNat _
      have h1 : (x * 10 ^ 32 : ℚ) ≤ (N : ℚ) := by
        calc (x * 10 ^ 32 : ℚ) ≤ (⌈x * 10 ^ 32⌉ : ℚ) := hceil
          _ ≤ (N : ℚ) := by exact_mod_cast htoNat
      calc ((x : ℚ) : ℝ) * 10 ^ 32 = ((x * 10 ^ 32 : ℚ) : ℝ) := by push_cast; ring
        _ ≤ ((N : ℚ) : ℝ) := by exact_mod_cast h1
        _ = (N : ℝ) := by push_cast; ring
    -- assemble: √x = √(x·10³²)/10¹⁶ ≤ √N/10¹⁶ < (Nat.sqrt N + 1)/10¹⁶
    have hxR : (0 : ℝ) ≤ ((x : ℚ) : ℝ) := by exact_mod_cast hx
    have hsplit : Real.sqrt ((x : ℚ) : ℝ) * 10 ^ 16 = Real.sqrt (((x : ℚ) : ℝ) * 10 ^ 32) := by
      rw [show ((x : ℚ) : ℝ) * 10 ^ 32 = ((x : ℚ) : ℝ) * (10 ^ 16) ^ 2 from by ring,
        Real.sqrt_mul hxR, Real.sqrt_sq (by positivity)]
    have hmono : Real.sqrt (((x : ℚ) : ℝ) * 10 ^ 32) ≤ Real.sqrt (N : ℝ) :=
      Real.sqrt_le_sqrt hxN
    have hgoal : Real.sqrt ((x : ℚ) : ℝ) * 10 ^ 16 < (Nat.sqrt N : ℝ) + 1 := by
      rw [hsplit]
      exact lt_of_le_of_lt hmono Real.real_sqrt_lt_nat_sqrt_succ
    have hcast : (((Nat.sqrt N + 1 : ℚ) / 10 ^ 16 : ℚ) : ℝ)
        = ((Nat.sqrt N : ℝ) + 1) / 10 ^ 16 := by push_cast; ring
    rw [show ((Nat.sqrt ⌈x * 10 ^ 32⌉.toNat + 1 : ℚ) : ℚ) = (Nat.sqrt N + 1 : ℚ) from by
      rw [hN_def]]
    rw [hcast]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 10 ^ 16)]
    exact le_of_lt hgoal

/-- Rational lower bound on the square of any upper sqrt:
`x ≤ s.f x · s.f x` for `0 ≤ x`. -/
theorem _root_.RationalApprox.UpperSqrt.le_mul_self (s : UpperSqrt) {x : ℚ}
    (hx : 0 ≤ x) : x ≤ s.f x * s.f x := by
  have h : Real.sqrt ((x : ℚ) : ℝ) ≤ ((s.f x : ℚ) : ℝ) := s.bound x hx
  have hxR : (0 : ℝ) ≤ ((x : ℚ) : ℝ) := mod_cast hx
  have hR : ((x : ℚ) : ℝ) ≤ ((s.f x : ℚ) : ℝ) * ((s.f x : ℚ) : ℝ) := by
    calc ((x : ℚ) : ℝ) = Real.sqrt ((x : ℚ) : ℝ) * Real.sqrt ((x : ℚ) : ℝ) :=
          (Real.mul_self_sqrt hxR).symm
      _ ≤ ((s.f x : ℚ) : ℝ) * ((s.f x : ℚ) : ℝ) :=
          mul_le_mul h h (Real.sqrt_nonneg _) (le_trans (Real.sqrt_nonneg _) h)
  exact_mod_cast hR

/-- Rational lower bound on the square of `sqrtℚUp16`. -/
theorem le_mul_self_sqrtℚUp16 {x : ℚ} (hx : 0 ≤ x) :
    x ≤ sqrtℚUp16 x * sqrtℚUp16 x :=
  UpperSqrt.le_mul_self ⟨sqrtℚUp16, fun _ => sqrt_le_sqrtℚUp16 _⟩ hx

/-- Tight computable upper bound on `sqrtℚUp16`: if `x ≤ Y·Y` with `0 ≤ Y`,
then `sqrtℚUp16 x ≤ Y + 2·10⁻¹⁶`. This replaces the crude `√⁺x ≤ 2·Y` bound
used with `sqrtℚUp` — the cheap-test constants shrink accordingly. -/
theorem sqrtℚUp16_le_add_of_le_mul_self {x Y : ℚ} (hY : 0 ≤ Y) (h : x ≤ Y * Y) :
    sqrtℚUp16 x ≤ Y + 2 / 10 ^ 16 := by
  unfold sqrtℚUp16
  split_ifs with h0
  · positivity
  · push Not at h0
    set N : ℕ := ⌈x * 10 ^ 32⌉.toNat with hN
    have hceil_lt : (⌈x * 10 ^ 32⌉ : ℚ) < x * 10 ^ 32 + 1 := Int.ceil_lt_add_one _
    have hpos : (0 : ℤ) ≤ ⌈x * 10 ^ 32⌉ := Int.ceil_nonneg (by positivity)
    have hNle : (N : ℚ) ≤ x * 10 ^ 32 + 1 := by
      have hNval : ((N : ℤ) : ℚ) = (⌈x * 10 ^ 32⌉ : ℚ) := by
        have := Int.toNat_of_nonneg hpos
        exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) this
      calc (N : ℚ) = ((N : ℤ) : ℚ) := by push_cast; ring
        _ = (⌈x * 10 ^ 32⌉ : ℚ) := hNval
        _ ≤ x * 10 ^ 32 + 1 := le_of_lt hceil_lt
    set s : ℕ := Nat.sqrt N with hs
    have hssq : (s : ℚ) * s ≤ (N : ℚ) := by exact_mod_cast Nat.sqrt_le N
    have hkey : (s : ℚ) ≤ Y * 10 ^ 16 + 1 := by
      by_contra hcon
      push Not at hcon
      have h1nn : (0 : ℚ) ≤ Y * 10 ^ 16 := by positivity
      have hs1 : (1 : ℚ) ≤ (s : ℚ) := by linarith
      have hx32 : x * 10 ^ 32 ≤ (Y * 10 ^ 16) * (Y * 10 ^ 16) := by nlinarith
      nlinarith
    have hfinal : ((Nat.sqrt N + 1 : ℕ) : ℚ) / 10 ^ 16 ≤ Y + 2 / 10 ^ 16 := by
      rw [div_le_iff₀ (by positivity : (0 : ℚ) < 10 ^ 16)]
      have : ((Nat.sqrt N + 1 : ℕ) : ℚ) = (s : ℚ) + 1 := by rw [← hs]; push_cast; ring
      rw [this]
      nlinarith
    simpa using hfinal

/-- `sqrtℚUp16` as an `UpperSqrt`. -/
def upperSqrt16 : UpperSqrt where
  f := sqrtℚUp16
  bound _ := sqrt_le_sqrtℚUp16 _

/-- The `Approx` bundle used by all checkers: `sqrtℚLow` below, `sqrtℚUp16`
above, and rational upper bounds for `√2` and `√5`. -/
def sqrtApprox16 : Approx where
  upper_sqrt_two := 1.42
  upper_sqrt_two_gt_sqrt_two := by
    show ((1.42 : ℚ) : ℝ) > Real.sqrt 2
    have h : Real.sqrt 2 < (1.42 : ℝ) :=
      (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    push_cast
    linarith
  upper_sqrt_five := 2.24
  upper_sqrt_five_gt_sqrt_five := by
    show ((2.24 : ℚ) : ℝ) > Real.sqrt 5
    have h : Real.sqrt 5 < (2.24 : ℝ) :=
      (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    push_cast
    linarith
  lower_sqrt := lowerSqrt
  upper_sqrt := upperSqrt16

/-! ## Sanity checks -/

/-- info: 14142135623730951 / 10000000000000000 -/
#guard_msgs in
#eval sqrtℚUp16 2

/-- info: 100000000000000001 / 10000000000000000 -/
#guard_msgs in
#eval sqrtℚUp16 100

end RationalApprox

end
