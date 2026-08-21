module

public import Mathlib.Analysis.Real.Sqrt

public import Noperthedron.RationalApprox.Basic
-- Mirror the imports at the meta phase so the test `#eval`s below can
-- interpret cross-module code under the module system.
public meta import Mathlib.Analysis.Real.Sqrt
public meta import Noperthedron.RationalApprox.Basic

@[expose] public section


/-!
# Fixed-point lower rational square root

`sqrtℚLow13` is a lower rational square root whose output always has
denominator dividing `10¹³`: for `x > 0`,

    sqrtℚLow13 x = Nat.sqrt ⌊x · 10²⁶⌋ / 10¹³ ≤ √x,

returning `0` on nonpositive input (matching the convention used by
`Real.sqrt`). It is the lower companion of the fixed-point upper square
root `sqrtℚUp16` in `Checker/SqrtFixed.lean`, and replaces the retired
scale-search construction of §7.2.2 of [SY25] (window constants, fuel-driven
`×100` shift loops): the fixed-point form is both *more accurate*
(error < 10⁻¹³ relative to the input scale, vs the scale search's ten
decimal digits) and a single `Nat.sqrt` per call. For inputs that are
themselves integer multiples of `10⁻²⁶` — the only inputs the checkers
produce, via `round13`ed vectors — the floor is exact, which is what lets
the integer core (`Checker/LocalNat.lean`, `sqrtNumLow26`) run the lower
sqrt as a bare `Nat.sqrt` on the numerator.
-/

namespace RationalApprox

/-- **Lower rational square root** (`√⁻`): returns `0` on `x ≤ 0`; otherwise
`Nat.sqrt ⌊x · 10²⁶⌋ / 10¹³ ≤ √x`, an integer multiple of `10⁻¹³`. -/
def sqrtℚLow13 (x : ℚ) : ℚ :=
  if x ≤ 0 then 0 else (Nat.sqrt ⌊x * 10 ^ 26⌋.toNat : ℚ) / 10 ^ 13

/-- Rational squared lower bound: `sqrtℚLow13 x · sqrtℚLow13 x ≤ x` for `0 ≤ x`. -/
theorem sqrtℚLow13_mul_self_le {x : ℚ} (hx : 0 ≤ x) :
    sqrtℚLow13 x * sqrtℚLow13 x ≤ x := by
  unfold sqrtℚLow13
  split_ifs with h0
  · simpa using hx
  · push Not at h0
    set N : ℕ := ⌊x * 10 ^ 26⌋.toNat with hN
    have hfloor_nonneg : (0 : ℤ) ≤ ⌊x * 10 ^ 26⌋ := Int.floor_nonneg.mpr (by positivity)
    have hNle : (N : ℚ) ≤ x * 10 ^ 26 := by
      have hcast : ((N : ℤ) : ℚ) = (⌊x * 10 ^ 26⌋ : ℚ) := by
        rw [hN]; exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (Int.toNat_of_nonneg hfloor_nonneg)
      calc (N : ℚ) = ((N : ℤ) : ℚ) := by push_cast; ring
        _ = (⌊x * 10 ^ 26⌋ : ℚ) := hcast
        _ ≤ x * 10 ^ 26 := Int.floor_le _
    have hsq : ((Nat.sqrt N : ℚ)) * (Nat.sqrt N : ℚ) ≤ (N : ℚ) := by
      exact_mod_cast Nat.sqrt_le N
    calc (Nat.sqrt N : ℚ) / 10 ^ 13 * ((Nat.sqrt N : ℚ) / 10 ^ 13)
        = (Nat.sqrt N : ℚ) * (Nat.sqrt N : ℚ) / 10 ^ 26 := by ring
      _ ≤ (N : ℚ) / 10 ^ 26 := by gcongr
      _ ≤ x := by linarith [hNle]

theorem sqrtℚLow13_nonneg (x : ℚ) : 0 ≤ sqrtℚLow13 x := by
  unfold sqrtℚLow13
  positivity

/-- `√⁻ x ≤ √x` for `x ≥ 0`. -/
theorem sqrtℚLow13_le_sqrt {x : ℚ} (hx : 0 ≤ x) :
    ((sqrtℚLow13 x : ℚ) : ℝ) ≤ Real.sqrt ((x : ℚ) : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  have h := sqrtℚLow13_mul_self_le hx
  calc ((sqrtℚLow13 x : ℚ) : ℝ) ^ 2
      = ((sqrtℚLow13 x * sqrtℚLow13 x : ℚ) : ℝ) := by push_cast; ring
    _ ≤ ((x : ℚ) : ℝ) := by exact_mod_cast h

def lowerSqrt : LowerSqrt where
  f := sqrtℚLow13
  bound _ := sqrtℚLow13_le_sqrt

end RationalApprox

/-! ## Sanity checks -/
section Examples
open RationalApprox

/-- info: 1414213562373 / 1000000000000 -/
#guard_msgs in
#eval sqrtℚLow13 2

/-- info: 1414213562373 / 2000000000000 -/
#guard_msgs in
#eval sqrtℚLow13 (1/2)

/-- info: 10 -/
#guard_msgs in
#eval sqrtℚLow13 100

end Examples

end
