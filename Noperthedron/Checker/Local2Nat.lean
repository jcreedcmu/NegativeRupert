module

public import Noperthedron.Checker.Local2Fast
public import Noperthedron.Checker.Local2
public import Noperthedron.Checker.LocalNat
public import Noperthedron.RationalApprox.NewtonSqrt

@[expose] public section


/-!
# Integer core of the second-order local checks

Integer renderings of the `Local2Fast` checkers, with the same scale
conventions as the first-order `checkN` family (`Checker/LocalNat.lean`):
trig numerators at `10¹³`, family entries at `10²⁶`, vertices at `10¹⁶`,
applied family components at `10⁴²`, product atoms at `10⁸⁴`, `sqrtℚUp16`
values at `10¹⁶`, `κℚ` absorbed into the constants, and every comparison
cross-multiplied by the positive denominator product
`6·(εθ.den·εφ.den)³·10^s` (and `r.den`/`δ.den` where they appear).

The shared shape of all four second-order budgets is the ε-weighted
5-atom polynomial `budN` with its value bridge `budN_div_eq`; the per-atom
work is the `10⁴²`/`10⁸⁴`-scale dots, which the checks hoist exactly as
`Local2Fast` does.
-/

namespace Noperthedron.Solution.Local2Nat

open Noperthedron RationalApprox
open Noperthedron.Solution.BεℚPy (sqrtNum26 sqrtNumLow26)
open Noperthedron.Solution.Local2Fast

/-- Vertex coordinates as integer numerators at scale `10¹⁶` (the local
copy of `Checker/LocalNat.lean`'s private bridge). -/
private lemma pythonVertexA_intCast (a : VertexIndex) (c : Fin 3) :
    pythonVertexA a c = (pythonVertexNumCurried a.ℓ a.i a.k c : ℚ) / 10 ^ 16 := by
  rw [pythonVertexA_eq]
  exact pythonVertexNumCurried_eq a.ℓ a.i a.k c

/-! ## Scaled square roots -/

/-- Integer form of `sqrtℚUp16` on inputs `S/10³²`: the inner
`⌈(S/10³²)·10³²⌉ = S` is exact. Output scale `10¹⁶`. -/
def sqrtNum32 (S : ℤ) : ℤ :=
  if S ≤ 0 then 0 else (Nat.sqrt S.toNat + 1 : ℕ)

/-- Integer form of `sqrtℚUp16` on inputs `S/10⁸⁴`: the inner ceiling
`⌈S/10⁵²⌉` is `-((-S)/10⁵²)` (floor division). Output scale `10¹⁶`. -/
def sqrtNum84 (S : ℤ) : ℤ :=
  if S ≤ 0 then 0 else (Nat.sqrt (-(-S / 10 ^ 52)).toNat + 1 : ℕ)

private lemma sqrtℚUp16_intCast_div32 (S : ℤ) :
    RationalApprox.sqrtℚUp16 ((S : ℚ) / 10 ^ 32) = (sqrtNum32 S : ℚ) / 10 ^ 16 := by
  unfold RationalApprox.sqrtℚUp16 sqrtNum32
  rcases le_or_gt S 0 with hS | hS
  · rw [if_pos (div_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast hS, by positivity⟩)),
        if_pos hS]
    simp
  · have hSQ : (0:ℚ) < (S : ℚ) := by exact_mod_cast hS
    rw [if_neg (not_le.mpr (by positivity)), if_neg (not_le.mpr hS)]
    have hceil : ⌈(S : ℚ) / 10 ^ 32 * 10 ^ 32⌉ = S := by
      rw [div_mul_cancel₀ _ (by norm_num : ((10:ℚ) ^ 32) ≠ 0)]
      exact Int.ceil_intCast _
    rw [hceil]
    push_cast
    ring

private lemma sqrtℚUp16_intCast_div84 (S : ℤ) :
    RationalApprox.sqrtℚUp16 ((S : ℚ) / 10 ^ 84) = (sqrtNum84 S : ℚ) / 10 ^ 16 := by
  unfold RationalApprox.sqrtℚUp16 sqrtNum84
  rcases le_or_gt S 0 with hS | hS
  · rw [if_pos (div_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast hS, by positivity⟩)),
        if_pos hS]
    simp
  · have hSQ : (0:ℚ) < (S : ℚ) := by exact_mod_cast hS
    rw [if_neg (not_le.mpr (by positivity)), if_neg (not_le.mpr hS)]
    have hceil : ⌈(S : ℚ) / 10 ^ 84 * 10 ^ 32⌉ = -(-S / 10 ^ 52) := by
      rw [show (S : ℚ) / 10 ^ 84 * 10 ^ 32 = -(((-S : ℤ) : ℚ) / ((10 ^ 52 : ℕ) : ℚ)) from by
        push_cast; ring]
      rw [Int.ceil_neg, Rat.floor_intCast_div_natCast]
      norm_num
    rw [hceil]
    push_cast
    ring

/-! ## The generic ε-weighted budget polynomial -/

/-- Cross-multiplied form (by `6·(εθ.den·εφ.den)³·10^s`) of the shared
budget shape `εθ·a1 + εφ·a2 + ½(εθ²·a3 + 2εθεφ·a4 + εφ²·a5) + rem·(εθ+εφ)³/6`
with the atoms `aᵢ` and the remainder coefficient `rem` at scale `10^s`. -/
def budN (a1 a2 a3 a4 a5 rem en ed fn fd : ℤ) : ℤ :=
  6 * en * ed ^ 2 * fd ^ 3 * a1 + 6 * fn * fd ^ 2 * ed ^ 3 * a2
    + 3 * en ^ 2 * ed * fd ^ 3 * a3 + 6 * en * fn * ed ^ 2 * fd ^ 2 * a4
    + 3 * fn ^ 2 * fd * ed ^ 3 * a5
    + (en * fd + fn * ed) ^ 3 * rem

/-- Value bridge for `budN`, over independent numerator/denominator data. -/
private lemma budN_div_eq' (a1N a2N a3N a4N a5N remN n m : ℤ) (d e : ℕ)
    {a1 a2 a3 a4 a5 rem εθ εφ : ℚ} (s : ℕ)
    (hd : d ≠ 0) (he : e ≠ 0)
    (hθ : εθ = (n : ℚ) / (d : ℚ)) (hφ : εφ = (m : ℚ) / (e : ℚ))
    (h1 : a1 = (a1N : ℚ) / 10 ^ s) (h2 : a2 = (a2N : ℚ) / 10 ^ s)
    (h3 : a3 = (a3N : ℚ) / 10 ^ s) (h4 : a4 = (a4N : ℚ) / 10 ^ s)
    (h5 : a5 = (a5N : ℚ) / 10 ^ s) (hrem : rem = (remN : ℚ) / 10 ^ s) :
    εθ * a1 + εφ * a2 + (1/2) * (εθ^2 * a3 + 2*(εθ*εφ) * a4 + εφ^2 * a5)
        + rem * (εθ + εφ)^3 / 6
      = ((budN a1N a2N a3N a4N a5N remN n d m e : ℤ) : ℚ)
        / (6 * ((d : ℚ) * (e : ℚ))^3 * 10 ^ s) := by
  have hdQ : ((d : ℚ)) ≠ 0 := by exact_mod_cast hd
  have heQ : ((e : ℚ)) ≠ 0 := by exact_mod_cast he
  have h10 : ((10:ℚ)) ^ s ≠ 0 := by positivity
  rw [h1, h2, h3, h4, h5, hrem, hθ, hφ]
  unfold budN
  push_cast
  field_simp
  ring

/-- Value bridge for `budN` at the `Rat` num/den projections. -/
lemma budN_div_eq (a1N a2N a3N a4N a5N remN : ℤ) {a1 a2 a3 a4 a5 rem : ℚ}
    (εθ εφ : ℚ) (s : ℕ)
    (h1 : a1 = (a1N : ℚ) / 10 ^ s) (h2 : a2 = (a2N : ℚ) / 10 ^ s)
    (h3 : a3 = (a3N : ℚ) / 10 ^ s) (h4 : a4 = (a4N : ℚ) / 10 ^ s)
    (h5 : a5 = (a5N : ℚ) / 10 ^ s) (hrem : rem = (remN : ℚ) / 10 ^ s) :
    εθ * a1 + εφ * a2 + (1/2) * (εθ^2 * a3 + 2*(εθ*εφ) * a4 + εφ^2 * a5)
        + rem * (εθ + εφ)^3 / 6
      = ((budN a1N a2N a3N a4N a5N remN εθ.num εθ.den εφ.num εφ.den : ℤ) : ℚ)
        / (6 * ((εθ.den : ℚ) * (εφ.den : ℚ))^3 * 10 ^ s) :=
  budN_div_eq' a1N a2N a3N a4N a5N remN εθ.num εφ.num εθ.den εφ.den s
    εθ.den_nz εφ.den_nz (Rat.num_div_den εθ).symm (Rat.num_div_den εφ).symm
    h1 h2 h3 h4 h5 hrem

/-- Cross-multiplication of `a/D < b/D` for a shared positive denominator. -/
private lemma intCast_div_lt_div_iff_same {a b : ℤ} {D : ℚ} (hD : 0 < D) :
    ((a : ℚ) / D < (b : ℚ) / D) ↔ a < b := by
  rw [div_lt_div_iff_of_pos_right hD]
  exact_mod_cast Iff.rfl

/-! ## `Aε₂ℚσ` integer core -/

/-- Per-vertex integer `Aε₂` test. `x…`/`xt…`/… are the X-family entry
numerators at scale `10²⁶`, `sg = ±1`, `W = 6·(εθ.den·εφ.den)³`. -/
@[inline] def aeVertN (x0 x1 x2 xt0 xt1 xf0 xf1 xf2 xtt0 xtt1 xtf0 xtf1
    sg en ed fn fd W : ℤ) (a : VertexIndex) : Bool :=
  let w0 := pythonVertexNumCurried a.ℓ a.i a.k 0
  let w1 := pythonVertexNumCurried a.ℓ a.i a.k 1
  let w2 := pythonVertexNumCurried a.ℓ a.i a.k 2
  let dX := x0 * w0 + x1 * w1 + x2 * w2
  let dXt := xt0 * w0 + xt1 * w1
  let dXf := xf0 * w0 + xf1 * w1 + xf2 * w2
  let dXtt := xtt0 * w0 + xtt1 * w1
  let dXtf := xtf0 * w0 + xtf1 * w1
  decide (budN (|dXt| + 3 * 10 ^ 32) (|dXf| + 3 * 10 ^ 32) (|dXtt| + 3 * 10 ^ 32)
      (|dXtf| + 3 * 10 ^ 32) (|dX| + 3 * 10 ^ 32) (10 ^ 42) en ed fn fd
      + W * (3 * 10 ^ 32) < W * (sg * dX))

/-- Integer rendering of `Local2Fast.aeCheck`. -/
def aeCheckN (θ φ : ℚ) (idx : Fin 3 → VertexIndex) (εθ εφ : ℚ) (σ : ℕ) : Bool :=
  let stN : ℤ := sinNum13 θ
  let ctN : ℤ := cosNum13 θ
  let sfN : ℤ := sinNum13 φ
  let cfN : ℤ := cosNum13 φ
  let sg : ℤ := (-1) ^ σ
  let x0 := ctN * sfN
  let x1 := stN * sfN
  let x2 := cfN * 10 ^ 13
  let xt0 := -(stN * sfN)
  let xt1 := ctN * sfN
  let xf0 := ctN * cfN
  let xf1 := stN * cfN
  let xf2 := -(sfN * 10 ^ 13)
  let xtt0 := -(ctN * sfN)
  let xtt1 := -(stN * sfN)
  let xtf0 := -(stN * cfN)
  let xtf1 := ctN * cfN
  let en := εθ.num
  let ed : ℤ := εθ.den
  let fn := εφ.num
  let fd : ℤ := εφ.den
  let W := 6 * (ed * fd) ^ 3
  aeVertN x0 x1 x2 xt0 xt1 xf0 xf1 xf2 xtt0 xtt1 xtf0 xtf1 sg en ed fn fd W (idx 0)
    && aeVertN x0 x1 x2 xt0 xt1 xf0 xf1 xf2 xtt0 xtt1 xtf0 xtf1 sg en ed fn fd W (idx 1)
    && aeVertN x0 x1 x2 xt0 xt1 xf0 xf1 xf2 xtt0 xtt1 xtf0 xtf1 sg en ed fn fd W (idx 2)

section AeSound

/-- An abs-atom plus a `κ`-slack at scale `10⁴²`. -/
private lemma abs_add_slack42 {x : ℚ} (m c : ℤ) (h : x = (m : ℚ) / 10 ^ 42) :
    |x| + (c : ℚ) / 10 ^ 10 = ((|m| + c * 10 ^ 32 : ℤ) : ℚ) / 10 ^ 42 := by
  rw [h, abs_div, abs_of_pos (by norm_num : (0:ℚ) < 10 ^ 42)]
  push_cast
  ring

/-- One vertex of `aeVertN` decides the corresponding `Local2Fast.aeVert`. -/
private lemma ae_test_iff (dXN dXtN dXfN dXttN dXtfN sg : ℤ)
    {dX dXt dXf dXtt dXtf sgq : ℚ} (εθ εφ : ℚ)
    (hsg : sgq = (sg : ℚ))
    (hdX : dX = (dXN : ℚ) / 10 ^ 42) (hdXt : dXt = (dXtN : ℚ) / 10 ^ 42)
    (hdXf : dXf = (dXfN : ℚ) / 10 ^ 42) (hdXtt : dXtt = (dXttN : ℚ) / 10 ^ 42)
    (hdXtf : dXtf = (dXtfN : ℚ) / 10 ^ 42) :
    (budN (|dXtN| + 3 * 10 ^ 32) (|dXfN| + 3 * 10 ^ 32) (|dXttN| + 3 * 10 ^ 32)
        (|dXtfN| + 3 * 10 ^ 32) (|dXN| + 3 * 10 ^ 32) (10 ^ 42)
        εθ.num εθ.den εφ.num εφ.den
      + 6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * (3 * 10 ^ 32)
      < 6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * (sg * dXN))
    ↔ dVecX dX dXt dXf dXtt dXtf εθ εφ + 3 * κℚ < sgq * dX := by
  have hκ : (κℚ : ℚ) = 1 / 10 ^ 10 := rfl
  have hWpos : (0:ℚ) < 6 * ((εθ.den : ℚ) * (εφ.den : ℚ)) ^ 3 := by
    have h1 : (0:ℚ) < (εθ.den : ℚ) := by exact_mod_cast εθ.pos
    have h2 : (0:ℚ) < (εφ.den : ℚ) := by exact_mod_cast εφ.pos
    positivity
  have hb := budN_div_eq (|dXtN| + 3 * 10 ^ 32) (|dXfN| + 3 * 10 ^ 32)
    (|dXttN| + 3 * 10 ^ 32) (|dXtfN| + 3 * 10 ^ 32) (|dXN| + 3 * 10 ^ 32) (10 ^ 42)
    (a1 := |dXt| + 3 * κℚ) (a2 := |dXf| + 3 * κℚ) (a3 := |dXtt| + 3 * κℚ)
    (a4 := |dXtf| + 3 * κℚ) (a5 := |dX| + 3 * κℚ) (rem := 1) εθ εφ 42
    (by rw [hκ, show (3:ℚ) * (1/10^10) = (3:ℤ) / 10 ^ 10 from by push_cast; ring]
        exact abs_add_slack42 dXtN 3 hdXt)
    (by rw [hκ, show (3:ℚ) * (1/10^10) = (3:ℤ) / 10 ^ 10 from by push_cast; ring]
        exact abs_add_slack42 dXfN 3 hdXf)
    (by rw [hκ, show (3:ℚ) * (1/10^10) = (3:ℤ) / 10 ^ 10 from by push_cast; ring]
        exact abs_add_slack42 dXttN 3 hdXtt)
    (by rw [hκ, show (3:ℚ) * (1/10^10) = (3:ℤ) / 10 ^ 10 from by push_cast; ring]
        exact abs_add_slack42 dXtfN 3 hdXtf)
    (by rw [hκ, show (3:ℚ) * (1/10^10) = (3:ℤ) / 10 ^ 10 from by push_cast; ring]
        exact abs_add_slack42 dXN 3 hdX)
    (by norm_num)
  rw [show dVecX dX dXt dXf dXtt dXtf εθ εφ
      = εθ * (|dXt| + 3 * κℚ) + εφ * (|dXf| + 3 * κℚ)
        + (1/2) * (εθ^2 * (|dXtt| + 3 * κℚ) + 2*(εθ*εφ) * (|dXtf| + 3 * κℚ)
            + εφ^2 * (|dX| + 3 * κℚ))
        + (1:ℚ) * (εθ + εφ)^3 / 6 from by unfold dVecX; ring]
  rw [hb, hsg, hdX, hκ]
  set W : ℚ := 6 * ((εθ.den : ℚ) * (εφ.den : ℚ)) ^ 3 with hWdef
  have hD : (0:ℚ) < W * 10 ^ 42 := mul_pos hWpos (by norm_num)
  rw [show (3:ℚ) * (1 / 10 ^ 10)
        = ((6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * (3 * 10 ^ 32) : ℤ) : ℚ) / (W * 10 ^ 42) from by
      rw [eq_div_iff hD.ne', hWdef]; push_cast; ring,
    show ((sg : ℚ)) * ((dXN : ℚ) / 10 ^ 42)
        = ((6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * (sg * dXN) : ℤ) : ℚ) / (W * 10 ^ 42) from by
      rw [eq_div_iff hD.ne', hWdef]; push_cast; ring]
  rw [← add_div, ← Int.cast_add, intCast_div_lt_div_iff_same hD]

end AeSound

/-- The integer core computes exactly `Local2Fast.aeCheck` at
`pythonVertexA`. -/
theorem aeCheckN_eq (θ φ : ℚ) (idx : Fin 3 → VertexIndex) (εθ εφ : ℚ) (σ : ℕ) :
    aeCheckN θ φ idx εθ εφ σ
      = Local2Fast.aeCheck θ φ (pythonVertexA ∘ idx) εθ εφ σ := by
  have hsg : ((-1 : ℚ)) ^ σ = (((-1) ^ σ : ℤ) : ℚ) := by push_cast; ring
  have hv := pythonVertexA_intCast
  have hdX : ∀ a : VertexIndex,
      cosℚ θ * sinℚ φ * pythonVertexA a 0 + sinℚ θ * sinℚ φ * pythonVertexA a 1
        + cosℚ φ * pythonVertexA a 2
      = ((cosNum13 θ * sinNum13 φ * pythonVertexNumCurried a.ℓ a.i a.k 0
          + sinNum13 θ * sinNum13 φ * pythonVertexNumCurried a.ℓ a.i a.k 1
          + cosNum13 φ * 10 ^ 13 * pythonVertexNumCurried a.ℓ a.i a.k 2 : ℤ) : ℚ)
        / 10 ^ 42 := by
    intro a
    rw [hv a 0, hv a 1, hv a 2, ← sinNum13_div_eq θ, ← cosNum13_div_eq θ,
      ← sinNum13_div_eq φ, ← cosNum13_div_eq φ]
    push_cast
    ring
  have hdXt : ∀ a : VertexIndex,
      -sinℚ θ * sinℚ φ * pythonVertexA a 0 + cosℚ θ * sinℚ φ * pythonVertexA a 1
        + 0 * pythonVertexA a 2
      = ((-(sinNum13 θ * sinNum13 φ) * pythonVertexNumCurried a.ℓ a.i a.k 0
          + cosNum13 θ * sinNum13 φ * pythonVertexNumCurried a.ℓ a.i a.k 1 : ℤ) : ℚ)
        / 10 ^ 42 := by
    intro a
    rw [hv a 0, hv a 1, hv a 2, ← sinNum13_div_eq θ, ← cosNum13_div_eq θ,
      ← sinNum13_div_eq φ]
    push_cast
    ring
  have hdXf : ∀ a : VertexIndex,
      cosℚ θ * cosℚ φ * pythonVertexA a 0 + sinℚ θ * cosℚ φ * pythonVertexA a 1
        + -sinℚ φ * pythonVertexA a 2
      = ((cosNum13 θ * cosNum13 φ * pythonVertexNumCurried a.ℓ a.i a.k 0
          + sinNum13 θ * cosNum13 φ * pythonVertexNumCurried a.ℓ a.i a.k 1
          + -(sinNum13 φ * 10 ^ 13) * pythonVertexNumCurried a.ℓ a.i a.k 2 : ℤ) : ℚ)
        / 10 ^ 42 := by
    intro a
    rw [hv a 0, hv a 1, hv a 2, ← sinNum13_div_eq θ, ← cosNum13_div_eq θ,
      ← sinNum13_div_eq φ, ← cosNum13_div_eq φ]
    push_cast
    ring
  have hdXtt : ∀ a : VertexIndex,
      -cosℚ θ * sinℚ φ * pythonVertexA a 0 + -sinℚ θ * sinℚ φ * pythonVertexA a 1
        + 0 * pythonVertexA a 2
      = ((-(cosNum13 θ * sinNum13 φ) * pythonVertexNumCurried a.ℓ a.i a.k 0
          + -(sinNum13 θ * sinNum13 φ) * pythonVertexNumCurried a.ℓ a.i a.k 1 : ℤ) : ℚ)
        / 10 ^ 42 := by
    intro a
    rw [hv a 0, hv a 1, hv a 2, ← sinNum13_div_eq θ, ← cosNum13_div_eq θ,
      ← sinNum13_div_eq φ]
    push_cast
    ring
  have hdXtf : ∀ a : VertexIndex,
      -sinℚ θ * cosℚ φ * pythonVertexA a 0 + cosℚ θ * cosℚ φ * pythonVertexA a 1
        + 0 * pythonVertexA a 2
      = ((-(sinNum13 θ * cosNum13 φ) * pythonVertexNumCurried a.ℓ a.i a.k 0
          + cosNum13 θ * cosNum13 φ * pythonVertexNumCurried a.ℓ a.i a.k 1 : ℤ) : ℚ)
        / 10 ^ 42 := by
    intro a
    rw [hv a 0, hv a 1, hv a 2, ← sinNum13_div_eq θ, ← cosNum13_div_eq θ,
      ← cosNum13_div_eq φ]
    push_cast
    ring
  rw [Bool.eq_iff_iff]
  unfold aeCheckN aeVertN Local2Fast.aeCheck Local2Fast.aeVert
  simp only [Bool.and_eq_true, decide_eq_true_eq, Function.comp_apply]
  exact and_congr
    (and_congr
      (ae_test_iff _ _ _ _ _ _ εθ εφ hsg (hdX (idx 0)) (hdXt (idx 0)) (hdXf (idx 0))
        (hdXtt (idx 0)) (hdXtf (idx 0)))
      (ae_test_iff _ _ _ _ _ _ εθ εφ hsg (hdX (idx 1)) (hdXt (idx 1)) (hdXf (idx 1))
        (hdXtt (idx 1)) (hdXtf (idx 1))))
    (ae_test_iff _ _ _ _ _ _ εθ εφ hsg (hdX (idx 2)) (hdXt (idx 2)) (hdXf (idx 2))
      (hdXtt (idx 2)) (hdXtf (idx 2)))

/-- `Aε₂ℚσ` at `pythonVertexA` decided through the integer core.
Out-prioritizes `Local2Fast.instDecidableAε₂ℚσ`. -/
instance (priority := 10600) instDecidableAε₂N (θ φ : ℚ) (idx : Fin 3 → VertexIndex)
    (εθ εφ : ℚ) (σ : ℕ) :
    Decidable (Local.TriangleQ.Aε₂ℚσ θ φ (pythonVertexA ∘ idx) εθ εφ σ) :=
  decidable_of_iff (aeCheckN θ φ idx εθ εφ σ = true)
    (by rw [aeCheckN_eq]
        exact Local2Fast.aeCheck_iff θ φ (pythonVertexA ∘ idx) εθ εφ σ)

/-! ## Applied-family integer components

`app6N` mirrors `Local2Fast.app6 (fam2 θ φ) (pythonVertexA a)` with integer
numerators at scale `10⁴²` (entries at `10²⁶` × vertices at `10¹⁶`). -/

structure App6N : Type where
  (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 f0 f1 : ℤ)
deriving Inhabited

/-- The applied family of one vertex, from the trig numerators. -/
@[inline] def app6N (stN ctN sfN cfN : ℤ) (a : VertexIndex) : App6N :=
  let w0 := pythonVertexNumCurried a.ℓ a.i a.k 0
  let w1 := pythonVertexNumCurried a.ℓ a.i a.k 1
  let w2 := pythonVertexNumCurried a.ℓ a.i a.k 2
  { a0 := -(stN * 10 ^ 13) * w0 + ctN * 10 ^ 13 * w1,
    a1 := -(ctN * cfN) * w0 + -(stN * cfN) * w1 + sfN * 10 ^ 13 * w2,
    b0 := -(ctN * 10 ^ 13) * w0 + -(stN * 10 ^ 13) * w1,
    b1 := stN * cfN * w0 + -(ctN * cfN) * w1,
    c0 := 0,
    c1 := ctN * sfN * w0 + stN * sfN * w1 + cfN * 10 ^ 13 * w2,
    d0 := stN * 10 ^ 13 * w0 + -(ctN * 10 ^ 13) * w1,
    d1 := ctN * cfN * w0 + stN * cfN * w1,
    e0 := 0,
    e1 := -(stN * sfN) * w0 + ctN * sfN * w1,
    f0 := 0,
    f1 := ctN * cfN * w0 + stN * cfN * w1 + -(sfN * 10 ^ 13) * w2 }

/-- The canonical `App6` of an `App6N` (all fields over `10⁴²`). -/
@[inline] def app6QofN (z : App6N) : App6 :=
  { a0 := (z.a0 : ℚ) / 10 ^ 42, a1 := (z.a1 : ℚ) / 10 ^ 42,
    b0 := (z.b0 : ℚ) / 10 ^ 42, b1 := (z.b1 : ℚ) / 10 ^ 42,
    c0 := (z.c0 : ℚ) / 10 ^ 42, c1 := (z.c1 : ℚ) / 10 ^ 42,
    d0 := (z.d0 : ℚ) / 10 ^ 42, d1 := (z.d1 : ℚ) / 10 ^ 42,
    e0 := (z.e0 : ℚ) / 10 ^ 42, e1 := (z.e1 : ℚ) / 10 ^ 42,
    f0 := (z.f0 : ℚ) / 10 ^ 42, f1 := (z.f1 : ℚ) / 10 ^ 42 }

/-- Componentwise difference of `App6N`s. -/
@[inline] def App6N.sub (x y : App6N) : App6N :=
  ⟨x.a0 - y.a0, x.a1 - y.a1, x.b0 - y.b0, x.b1 - y.b1, x.c0 - y.c0, x.c1 - y.c1,
   x.d0 - y.d0, x.d1 - y.d1, x.e0 - y.e0, x.e1 - y.e1, x.f0 - y.f0, x.f1 - y.f1⟩

lemma app6QofN_sub (x y : App6N) :
    (app6QofN x).sub (app6QofN y) = app6QofN (x.sub y) := by
  unfold app6QofN App6.sub App6N.sub
  congr 1 <;> push_cast <;> ring

section App6Bridges

variable (θ φ : ℚ) (a : VertexIndex)

private lemma q_app6 :
    app6 (fam2 θ φ) (pythonVertexA a)
      = { a0 := -sinℚ θ * pythonVertexA a 0 + cosℚ θ * pythonVertexA a 1
            + 0 * pythonVertexA a 2,
          a1 := -(cosℚ θ * cosℚ φ) * pythonVertexA a 0
            + -(sinℚ θ * cosℚ φ) * pythonVertexA a 1 + sinℚ φ * pythonVertexA a 2,
          b0 := -cosℚ θ * pythonVertexA a 0 + -sinℚ θ * pythonVertexA a 1
            + 0 * pythonVertexA a 2,
          b1 := sinℚ θ * cosℚ φ * pythonVertexA a 0
            + -(cosℚ θ * cosℚ φ) * pythonVertexA a 1 + 0 * pythonVertexA a 2,
          c0 := 0 * pythonVertexA a 0 + 0 * pythonVertexA a 1 + 0 * pythonVertexA a 2,
          c1 := cosℚ θ * sinℚ φ * pythonVertexA a 0
            + sinℚ θ * sinℚ φ * pythonVertexA a 1 + cosℚ φ * pythonVertexA a 2,
          d0 := sinℚ θ * pythonVertexA a 0 + -cosℚ θ * pythonVertexA a 1
            + 0 * pythonVertexA a 2,
          d1 := cosℚ θ * cosℚ φ * pythonVertexA a 0
            + sinℚ θ * cosℚ φ * pythonVertexA a 1 + 0 * pythonVertexA a 2,
          e0 := 0 * pythonVertexA a 0 + 0 * pythonVertexA a 1 + 0 * pythonVertexA a 2,
          e1 := -(sinℚ θ * sinℚ φ) * pythonVertexA a 0
            + cosℚ θ * sinℚ φ * pythonVertexA a 1 + 0 * pythonVertexA a 2,
          f0 := 0 * pythonVertexA a 0 + 0 * pythonVertexA a 1 + 0 * pythonVertexA a 2,
          f1 := cosℚ θ * cosℚ φ * pythonVertexA a 0
            + sinℚ θ * cosℚ φ * pythonVertexA a 1 + -sinℚ φ * pythonVertexA a 2 } := by
  simp only [app6, fam2]
  congr 1 <;> ring

/-- All twelve component bridges at once: `app6` at a python vertex is the
canonical cast of the integer `app6N`. -/
private lemma app6_intCast :
    app6 (fam2 θ φ) (pythonVertexA a)
      = app6QofN (app6N (sinNum13 θ) (cosNum13 θ) (sinNum13 φ) (cosNum13 φ) a) := by
  rw [q_app6]
  unfold app6QofN
  have hv := pythonVertexA_intCast
  simp only [app6N]
  congr 1 <;>
    simp only [hv, ← sinNum13_div_eq, ← cosNum13_div_eq] <;>
    push_cast <;> ring

end App6Bridges

/-! ## `Spanning₂ℚ` integer core -/

/-- Per-pair integer spanning test (`W = 6·(εθ.den·εφ.den)³`). -/
@[inline] def spanPairN (qv qw : App6N) (en ed fn fd W : ℤ) : Bool :=
  let Pθ := (qv.b0 * qw.a1 - qv.b1 * qw.a0) + (qv.a0 * qw.b1 - qv.a1 * qw.b0)
  let Pφ := (qv.c0 * qw.a1 - qv.c1 * qw.a0) + (qv.a0 * qw.c1 - qv.a1 * qw.c0)
  let Pθθ := (qv.d0 * qw.a1 - qv.d1 * qw.a0) + 2 * (qv.b0 * qw.b1 - qv.b1 * qw.b0)
      + (qv.a0 * qw.d1 - qv.a1 * qw.d0)
  let Pθφ := (qv.e0 * qw.a1 - qv.e1 * qw.a0) + (qv.b0 * qw.c1 - qv.b1 * qw.c0)
      + (qv.c0 * qw.b1 - qv.c1 * qw.b0) + (qv.a0 * qw.e1 - qv.a1 * qw.e0)
  let Pφφ := (qv.f0 * qw.a1 - qv.f1 * qw.a0) + 2 * (qv.c0 * qw.c1 - qv.c1 * qw.c0)
      + (qv.a0 * qw.f1 - qv.a1 * qw.f0)
  let f0 := qv.a0 * qw.a1 - qv.a1 * qw.a0
  decide (budN (|Pθ| + 10 * 10 ^ 74) (|Pφ| + 10 * 10 ^ 74) (|Pθθ| + 20 * 10 ^ 74)
      (|Pθφ| + 20 * 10 ^ 74) (|Pφφ| + 20 * 10 ^ 74) (8 * 10 ^ 84) en ed fn fd
      + W * (5 * 10 ^ 74) < W * f0)

/-- Integer rendering of `Local2Fast.spanCheck`. -/
def spanCheckN (θ φ : ℚ) (idx : Fin 3 → VertexIndex) (εθ εφ : ℚ) : Bool :=
  let stN : ℤ := sinNum13 θ
  let ctN : ℤ := cosNum13 θ
  let sfN : ℤ := sinNum13 φ
  let cfN : ℤ := cosNum13 φ
  let en := εθ.num
  let ed : ℤ := εθ.den
  let fn := εφ.num
  let fd : ℤ := εφ.den
  let W := 6 * (ed * fd) ^ 3
  let q0 := app6N stN ctN sfN cfN (idx 0)
  let q1 := app6N stN ctN sfN cfN (idx 1)
  let q2 := app6N stN ctN sfN cfN (idx 2)
  spanPairN q0 q1 en ed fn fd W && spanPairN q1 q2 en ed fn fd W
    && spanPairN q2 q0 en ed fn fd W

section SpanSound

/-- An abs-atom plus a `κ`-slack at scale `10⁸⁴`. -/
private lemma abs_add_slack84 {x : ℚ} (m c : ℤ) (h : x = (m : ℚ) / 10 ^ 84) :
    |x| + (c : ℚ) / 10 ^ 10 = ((|m| + c * 10 ^ 74 : ℤ) : ℚ) / 10 ^ 84 := by
  rw [h, abs_div, abs_of_pos (by norm_num : (0:ℚ) < 10 ^ 84)]
  push_cast
  ring

/-- One pair of `spanPairN` decides the corresponding `Local2Fast.spanPair`. -/
private lemma span_test_iff (PθN PφN PθθN PθφN PφφN f0N : ℤ)
    {Pθ Pφ Pθθ Pθφ Pφφ f0 : ℚ} (εθ εφ : ℚ)
    (hPθ : Pθ = (PθN : ℚ) / 10 ^ 84) (hPφ : Pφ = (PφN : ℚ) / 10 ^ 84)
    (hPθθ : Pθθ = (PθθN : ℚ) / 10 ^ 84) (hPθφ : Pθφ = (PθφN : ℚ) / 10 ^ 84)
    (hPφφ : Pφφ = (PφφN : ℚ) / 10 ^ 84) (hf0 : f0 = (f0N : ℚ) / 10 ^ 84) :
    (budN (|PθN| + 10 * 10 ^ 74) (|PφN| + 10 * 10 ^ 74) (|PθθN| + 20 * 10 ^ 74)
        (|PθφN| + 20 * 10 ^ 74) (|PφφN| + 20 * 10 ^ 74) (8 * 10 ^ 84)
        εθ.num εθ.den εφ.num εφ.den
      + 6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * (5 * 10 ^ 74)
      < 6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * f0N)
    ↔ εθ * (|Pθ| + 2 * (5 * κℚ)) + εφ * (|Pφ| + 2 * (5 * κℚ))
        + (1/2) * (εθ^2 * (|Pθθ| + 4 * (5 * κℚ)) + 2*(εθ*εφ) * (|Pθφ| + 4 * (5 * κℚ))
            + εφ^2 * (|Pφφ| + 4 * (5 * κℚ)))
        + 8 * 1 * (εθ + εφ)^3 / 6 + 5 * κℚ < f0 := by
  have hκ : (κℚ : ℚ) = 1 / 10 ^ 10 := rfl
  have hWpos : (0:ℚ) < 6 * ((εθ.den : ℚ) * (εφ.den : ℚ)) ^ 3 := by
    have h1 : (0:ℚ) < (εθ.den : ℚ) := by exact_mod_cast εθ.pos
    have h2 : (0:ℚ) < (εφ.den : ℚ) := by exact_mod_cast εφ.pos
    positivity
  have hb := budN_div_eq (|PθN| + 10 * 10 ^ 74) (|PφN| + 10 * 10 ^ 74)
    (|PθθN| + 20 * 10 ^ 74) (|PθφN| + 20 * 10 ^ 74) (|PφφN| + 20 * 10 ^ 74) (8 * 10 ^ 84)
    (a1 := |Pθ| + 2 * (5 * κℚ)) (a2 := |Pφ| + 2 * (5 * κℚ)) (a3 := |Pθθ| + 4 * (5 * κℚ))
    (a4 := |Pθφ| + 4 * (5 * κℚ)) (a5 := |Pφφ| + 4 * (5 * κℚ)) (rem := 8 * 1) εθ εφ 84
    (by rw [show (2:ℚ) * (5 * κℚ) = ((10:ℤ) : ℚ) / 10 ^ 10 from by norm_num [κℚ]]
        exact abs_add_slack84 PθN 10 hPθ)
    (by rw [show (2:ℚ) * (5 * κℚ) = ((10:ℤ) : ℚ) / 10 ^ 10 from by norm_num [κℚ]]
        exact abs_add_slack84 PφN 10 hPφ)
    (by rw [show (4:ℚ) * (5 * κℚ) = ((20:ℤ) : ℚ) / 10 ^ 10 from by norm_num [κℚ]]
        exact abs_add_slack84 PθθN 20 hPθθ)
    (by rw [show (4:ℚ) * (5 * κℚ) = ((20:ℤ) : ℚ) / 10 ^ 10 from by norm_num [κℚ]]
        exact abs_add_slack84 PθφN 20 hPθφ)
    (by rw [show (4:ℚ) * (5 * κℚ) = ((20:ℤ) : ℚ) / 10 ^ 10 from by norm_num [κℚ]]
        exact abs_add_slack84 PφφN 20 hPφφ)
    (by norm_num)
  rw [hb, hf0, hκ]
  set W : ℚ := 6 * ((εθ.den : ℚ) * (εφ.den : ℚ)) ^ 3 with hWdef
  have hD : (0:ℚ) < W * 10 ^ 84 := mul_pos hWpos (by norm_num)
  rw [show (5:ℚ) * (1 / 10 ^ 10)
        = ((6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * (5 * 10 ^ 74) : ℤ) : ℚ) / (W * 10 ^ 84) from by
      rw [eq_div_iff hD.ne', hWdef]; push_cast; ring,
    show ((f0N : ℚ)) / 10 ^ 84
        = ((6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * f0N : ℤ) : ℚ) / (W * 10 ^ 84) from by
      rw [eq_div_iff hD.ne', hWdef]; push_cast; ring]
  rw [← add_div, ← Int.cast_add, intCast_div_lt_div_iff_same hD]

/-- The integer core computes exactly `Local2Fast.spanCheck` at
`pythonVertexA`. -/
theorem spanCheckN_eq (θ φ : ℚ) (idx : Fin 3 → VertexIndex) (εθ εφ : ℚ) :
    spanCheckN θ φ idx εθ εφ
      = Local2Fast.spanCheck θ φ (pythonVertexA ∘ idx) εθ εφ := by
  have hq := app6_intCast θ φ
  have pairIff : ∀ a b : VertexIndex,
      (spanPairN (app6N (sinNum13 θ) (cosNum13 θ) (sinNum13 φ) (cosNum13 φ) a)
        (app6N (sinNum13 θ) (cosNum13 θ) (sinNum13 φ) (cosNum13 φ) b)
        εθ.num εθ.den εφ.num εφ.den (6 * ((εθ.den : ℤ) * εφ.den) ^ 3) = true)
      ↔ (Local2Fast.spanPair (app6 (fam2 θ φ) (pythonVertexA a))
          (app6 (fam2 θ φ) (pythonVertexA b)) εθ εφ = true) := by
    intro a b
    unfold spanPairN Local2Fast.spanPair Local2Fast.dProd90
    simp only [decide_eq_true_eq]
    refine span_test_iff _ _ _ _ _ _ εθ εφ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [hq, app6QofN] <;> push_cast <;> ring
  rw [Bool.eq_iff_iff]
  unfold spanCheckN Local2Fast.spanCheck
  simp only [Bool.and_eq_true, Function.comp_apply]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    exact ⟨⟨(pairIff (idx 0) (idx 1)).mp h0, (pairIff (idx 1) (idx 2)).mp h1⟩,
      (pairIff (idx 2) (idx 0)).mp h2⟩
  · rintro ⟨⟨h0, h1⟩, h2⟩
    exact ⟨⟨(pairIff (idx 0) (idx 1)).mpr h0, (pairIff (idx 1) (idx 2)).mpr h1⟩,
      (pairIff (idx 2) (idx 0)).mpr h2⟩

/-- `Spanning₂ℚ` at `pythonVertexA` decided through the integer core.
Out-prioritizes `Local2Fast.instDecidableSpanning₂ℚ`. -/
instance (priority := 10600) instDecidableSpanning₂N (θ φ : ℚ)
    (idx : Fin 3 → VertexIndex) (εθ εφ : ℚ) :
    Decidable (Local.TriangleQ.Spanning₂ℚ θ φ (pythonVertexA ∘ idx) εθ εφ) :=
  decidable_of_iff (spanCheckN θ φ idx εθ εφ = true)
    (by rw [spanCheckN_eq]
        exact Local2Fast.spanCheck_iff θ φ (pythonVertexA ∘ idx) εθ εφ)

end SpanSound

/-! ## `BoundR₂ℚ` integer core -/

section BrSound

private lemma upper_f_eq (x : ℚ) :
    RationalApprox.sqrtApprox16.upper_sqrt.f x = RationalApprox.sqrtℚUp16 x := rfl

private lemma lower_f_eq (x : ℚ) :
    RationalApprox.sqrtApprox16.lower_sqrt.f x = RationalApprox.sqrtℚLow13 x := rfl

/-- `round13` on a scale-`10⁴²` integer fraction is integer division by
`10²⁹` (local copy of `Checker/LocalNat.lean`'s private bridge). -/
private lemma round13_intCast_div42 (m : ℤ) :
    RationalApprox.round13 ((m : ℚ) / 10 ^ 42) = ((m / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13 := by
  rw [show ((10:ℚ) ^ 42) = 10 ^ 13 * ((10 ^ 29 : ℕ) : ℚ) from by norm_num,
    RationalApprox.round13_intCast_div,
    show ((10 ^ 29 : ℕ) : ℤ) = 10 ^ 29 from by norm_num]

/-- `sqrtℚLow13` on a scale-`10²⁶` integer fraction is `sqrtNumLow26` (local
copy of `Checker/LocalNat.lean`'s private bridge). -/
private lemma sqrtℚLow13_intCast_div26 (S : ℤ) :
    RationalApprox.sqrtℚLow13 ((S : ℚ) / 10 ^ 26) = (sqrtNumLow26 S : ℚ) / 10 ^ 13 := by
  unfold RationalApprox.sqrtℚLow13 BεℚPy.sqrtNumLow26
  rcases le_or_gt S 0 with hS | hS
  · rw [if_pos (div_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast hS, by positivity⟩)),
      Int.toNat_of_nonpos hS]
    simp
  · have hSQ : (0:ℚ) < (S : ℚ) := by exact_mod_cast hS
    rw [if_neg (not_le.mpr (by positivity))]
    have hfloor : ⌊(S : ℚ) / 10 ^ 26 * 10 ^ 26⌋ = S := by
      rw [div_mul_cancel₀ _ (by norm_num : ((10:ℚ) ^ 26) ≠ 0)]
      exact Int.floor_intCast _
    rw [hfloor]
    push_cast
    ring

end BrSound

/-- Per-vertex integer `BoundR₂` test (`W = 6·(εθ.den·εφ.den)³`). -/
@[inline] def brVertN (rn en ed fn fd W : ℤ) (rd : ℤ) (q : App6N) : Bool :=
  let sb := sqrtNum84 (q.b0 * q.b0 + q.b1 * q.b1)
  let sc := sqrtNum84 (q.c0 * q.c0 + q.c1 * q.c1)
  let sd := sqrtNum84 (q.d0 * q.d0 + q.d1 * q.d1)
  let se := sqrtNum84 (q.e0 * q.e0 + q.e1 * q.e1)
  let sf := sqrtNum84 (q.f0 * q.f0 + q.f1 * q.f1)
  let q0 := q.a0 / 10 ^ 29
  let q1 := q.a1 / 10 ^ 29
  let slN := sqrtNumLow26 (q0 * q0 + q1 * q1)
  decide (rn * (W * 10 ^ 16)
      + rd * budN (sb + 3 * 10 ^ 6) (sc + 3 * 10 ^ 6) (sd + 3 * 10 ^ 6)
          (se + 3 * 10 ^ 6) (sf + 3 * 10 ^ 6) (10 ^ 16) en ed fn fd
      + rd * (W * (3 * 10 ^ 6))
      < rd * (W * (slN * 10 ^ 3)))

/-- Integer rendering of `Local2Fast.brCheck`. -/
def brCheckN (r : ℚ) (p : Pose ℚ) (idx : Fin 3 → VertexIndex) (εθ εφ : ℚ) : Bool :=
  let stN : ℤ := sinNum13 p.θ₂
  let ctN : ℤ := cosNum13 p.θ₂
  let sfN : ℤ := sinNum13 p.φ₂
  let cfN : ℤ := cosNum13 p.φ₂
  let en := εθ.num
  let ed : ℤ := εθ.den
  let fn := εφ.num
  let fd : ℤ := εφ.den
  let W := 6 * (ed * fd) ^ 3
  let rn := r.num
  let rd : ℤ := r.den
  brVertN rn en ed fn fd W rd (app6N stN ctN sfN cfN (idx 0))
    && brVertN rn en ed fn fd W rd (app6N stN ctN sfN cfN (idx 1))
    && brVertN rn en ed fn fd W rd (app6N stN ctN sfN cfN (idx 2))

section BrSound2

/-- One vertex of `brVertN` decides the corresponding `Local2Fast.brCheck`
body, over independent `r`-numerator data. -/
private lemma br_test_iff (b0N b1N c0N c1N d0N d1N e0N e1N f0N f1N a0N a1N rn : ℤ)
    (rd : ℕ)
    {qb0 qb1 qc0 qc1 qd0 qd1 qe0 qe1 qf0 qf1 qa0 qa1 r : ℚ} (εθ εφ : ℚ)
    (hrd : rd ≠ 0) (hrq : r = (rn : ℚ) / (rd : ℚ))
    (hb0 : qb0 = (b0N : ℚ) / 10 ^ 42) (hb1 : qb1 = (b1N : ℚ) / 10 ^ 42)
    (hc0 : qc0 = (c0N : ℚ) / 10 ^ 42) (hc1 : qc1 = (c1N : ℚ) / 10 ^ 42)
    (hd0 : qd0 = (d0N : ℚ) / 10 ^ 42) (hd1 : qd1 = (d1N : ℚ) / 10 ^ 42)
    (he0 : qe0 = (e0N : ℚ) / 10 ^ 42) (he1 : qe1 = (e1N : ℚ) / 10 ^ 42)
    (hf0 : qf0 = (f0N : ℚ) / 10 ^ 42) (hf1 : qf1 = (f1N : ℚ) / 10 ^ 42)
    (ha0 : qa0 = (a0N : ℚ) / 10 ^ 42) (ha1 : qa1 = (a1N : ℚ) / 10 ^ 42) :
    (rn * (6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * 10 ^ 16)
      + rd * budN (sqrtNum84 (b0N * b0N + b1N * b1N) + 3 * 10 ^ 6)
          (sqrtNum84 (c0N * c0N + c1N * c1N) + 3 * 10 ^ 6)
          (sqrtNum84 (d0N * d0N + d1N * d1N) + 3 * 10 ^ 6)
          (sqrtNum84 (e0N * e0N + e1N * e1N) + 3 * 10 ^ 6)
          (sqrtNum84 (f0N * f0N + f1N * f1N) + 3 * 10 ^ 6) (10 ^ 16)
          εθ.num εθ.den εφ.num εφ.den
      + rd * (6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * (3 * 10 ^ 6))
      < rd * (6 * ((εθ.den : ℤ) * εφ.den) ^ 3
          * (sqrtNumLow26 ((a0N / 10 ^ 29) * (a0N / 10 ^ 29)
              + (a1N / 10 ^ 29) * (a1N / 10 ^ 29)) * 10 ^ 3)))
    ↔ r + (εθ * (RationalApprox.sqrtApprox16.upper_sqrt.f (qb0 * qb0 + qb1 * qb1) + 3 * κℚ)
          + εφ * (RationalApprox.sqrtApprox16.upper_sqrt.f (qc0 * qc0 + qc1 * qc1) + 3 * κℚ)
          + (1/2) * (εθ^2 * (RationalApprox.sqrtApprox16.upper_sqrt.f (qd0 * qd0 + qd1 * qd1)
                  + 3 * κℚ)
              + 2*(εθ*εφ) * (RationalApprox.sqrtApprox16.upper_sqrt.f (qe0 * qe0 + qe1 * qe1)
                  + 3 * κℚ)
              + εφ^2 * (RationalApprox.sqrtApprox16.upper_sqrt.f (qf0 * qf0 + qf1 * qf1)
                  + 3 * κℚ))
          + 1 * (εθ + εφ)^3 / 6) + 3 * κℚ
        < RationalApprox.sqrtApprox16.lower_sqrt.f
            (RationalApprox.round13 qa0 * RationalApprox.round13 qa0
              + RationalApprox.round13 qa1 * RationalApprox.round13 qa1) := by
  have hκ : (κℚ : ℚ) = 1 / 10 ^ 10 := rfl
  have hWpos : (0:ℚ) < 6 * ((εθ.den : ℚ) * (εφ.den : ℚ)) ^ 3 := by
    have h1 : (0:ℚ) < (εθ.den : ℚ) := by exact_mod_cast εθ.pos
    have h2 : (0:ℚ) < (εφ.den : ℚ) := by exact_mod_cast εφ.pos
    positivity
  have hrdQ : (0:ℚ) < (rd : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero hrd
  -- sqrt atoms
  have hsq : ∀ (u v : ℤ) (x y : ℚ), x = (u : ℚ) / 10 ^ 42 → y = (v : ℚ) / 10 ^ 42 →
      RationalApprox.sqrtApprox16.upper_sqrt.f (x * x + y * y) + 3 * κℚ
        = ((sqrtNum84 (u * u + v * v) + 3 * 10 ^ 6 : ℤ) : ℚ) / 10 ^ 16 := by
    intro u v x y hx hy
    rw [hx, hy, upper_f_eq,
      show ((u:ℚ)/10^42) * ((u:ℚ)/10^42) + ((v:ℚ)/10^42) * ((v:ℚ)/10^42)
        = ((u * u + v * v : ℤ) : ℚ) / 10 ^ 84 from by push_cast; ring,
      sqrtℚUp16_intCast_div84, hκ]
    push_cast
    ring
  -- the lower-sqrt side
  have hsl : RationalApprox.sqrtApprox16.lower_sqrt.f
      (RationalApprox.round13 qa0 * RationalApprox.round13 qa0
        + RationalApprox.round13 qa1 * RationalApprox.round13 qa1)
      = ((sqrtNumLow26 ((a0N / 10 ^ 29) * (a0N / 10 ^ 29)
          + (a1N / 10 ^ 29) * (a1N / 10 ^ 29)) : ℤ) : ℚ) / 10 ^ 13 := by
    rw [ha0, ha1, round13_intCast_div42, round13_intCast_div42, lower_f_eq,
      show (((a0N / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13) * (((a0N / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13)
          + (((a1N / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13) * (((a1N / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13)
        = (((a0N / 10 ^ 29) * (a0N / 10 ^ 29)
            + (a1N / 10 ^ 29) * (a1N / 10 ^ 29) : ℤ) : ℚ) / 10 ^ 26 from by push_cast; ring,
      sqrtℚLow13_intCast_div26]
  have hb := budN_div_eq (sqrtNum84 (b0N * b0N + b1N * b1N) + 3 * 10 ^ 6)
    (sqrtNum84 (c0N * c0N + c1N * c1N) + 3 * 10 ^ 6)
    (sqrtNum84 (d0N * d0N + d1N * d1N) + 3 * 10 ^ 6)
    (sqrtNum84 (e0N * e0N + e1N * e1N) + 3 * 10 ^ 6)
    (sqrtNum84 (f0N * f0N + f1N * f1N) + 3 * 10 ^ 6) (10 ^ 16)
    (a1 := RationalApprox.sqrtApprox16.upper_sqrt.f (qb0 * qb0 + qb1 * qb1) + 3 * κℚ)
    (a2 := RationalApprox.sqrtApprox16.upper_sqrt.f (qc0 * qc0 + qc1 * qc1) + 3 * κℚ)
    (a3 := RationalApprox.sqrtApprox16.upper_sqrt.f (qd0 * qd0 + qd1 * qd1) + 3 * κℚ)
    (a4 := RationalApprox.sqrtApprox16.upper_sqrt.f (qe0 * qe0 + qe1 * qe1) + 3 * κℚ)
    (a5 := RationalApprox.sqrtApprox16.upper_sqrt.f (qf0 * qf0 + qf1 * qf1) + 3 * κℚ)
    (rem := 1) εθ εφ 16
    (hsq b0N b1N qb0 qb1 hb0 hb1) (hsq c0N c1N qc0 qc1 hc0 hc1)
    (hsq d0N d1N qd0 qd1 hd0 hd1) (hsq e0N e1N qe0 qe1 he0 he1)
    (hsq f0N f1N qf0 qf1 hf0 hf1) (by norm_num)
  rw [hb, hsl, hrq, hκ]
  set W : ℚ := 6 * ((εθ.den : ℚ) * (εφ.den : ℚ)) ^ 3 with hWdef
  have hD : (0:ℚ) < (rd : ℚ) * (W * 10 ^ 16) := by positivity
  rw [show ((rn : ℚ)) / (rd : ℚ)
        = ((rn * (6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * 10 ^ 16) : ℤ) : ℚ)
          / ((rd : ℚ) * (W * 10 ^ 16)) from by
      rw [eq_div_iff hD.ne', hWdef]; push_cast; field_simp; ring,
    show ((budN (sqrtNum84 (b0N * b0N + b1N * b1N) + 3 * 10 ^ 6)
          (sqrtNum84 (c0N * c0N + c1N * c1N) + 3 * 10 ^ 6)
          (sqrtNum84 (d0N * d0N + d1N * d1N) + 3 * 10 ^ 6)
          (sqrtNum84 (e0N * e0N + e1N * e1N) + 3 * 10 ^ 6)
          (sqrtNum84 (f0N * f0N + f1N * f1N) + 3 * 10 ^ 6) (10 ^ 16)
          εθ.num εθ.den εφ.num εφ.den : ℤ) : ℚ) / (W * 10 ^ 16)
        = (((rd : ℤ) * budN (sqrtNum84 (b0N * b0N + b1N * b1N) + 3 * 10 ^ 6)
          (sqrtNum84 (c0N * c0N + c1N * c1N) + 3 * 10 ^ 6)
          (sqrtNum84 (d0N * d0N + d1N * d1N) + 3 * 10 ^ 6)
          (sqrtNum84 (e0N * e0N + e1N * e1N) + 3 * 10 ^ 6)
          (sqrtNum84 (f0N * f0N + f1N * f1N) + 3 * 10 ^ 6) (10 ^ 16)
          εθ.num εθ.den εφ.num εφ.den : ℤ) : ℚ) / ((rd : ℚ) * (W * 10 ^ 16)) from by
      rw [div_eq_div_iff (by positivity) hD.ne']
      push_cast; ring,
    show (3:ℚ) * (1 / 10 ^ 10)
        = (((rd : ℤ) * (6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * (3 * 10 ^ 6)) : ℤ) : ℚ)
          / ((rd : ℚ) * (W * 10 ^ 16)) from by
      rw [eq_div_iff hD.ne', hWdef]; push_cast; ring,
    show ((sqrtNumLow26 ((a0N / 10 ^ 29) * (a0N / 10 ^ 29)
            + (a1N / 10 ^ 29) * (a1N / 10 ^ 29)) : ℤ) : ℚ) / 10 ^ 13
        = (((rd : ℤ) * (6 * ((εθ.den : ℤ) * εφ.den) ^ 3
            * (sqrtNumLow26 ((a0N / 10 ^ 29) * (a0N / 10 ^ 29)
                + (a1N / 10 ^ 29) * (a1N / 10 ^ 29)) * 10 ^ 3)) : ℤ) : ℚ)
          / ((rd : ℚ) * (W * 10 ^ 16)) from by
      rw [div_eq_div_iff (by norm_num) hD.ne', hWdef]
      push_cast; ring]
  rw [← add_div, ← add_div, ← Int.cast_add, ← Int.cast_add,
    intCast_div_lt_div_iff_same hD]

/-- The integer core computes exactly `Local2Fast.brCheck` at
`pythonVertexA`. -/
theorem brCheckN_eq (r : ℚ) (p : Pose ℚ) (idx : Fin 3 → VertexIndex) (εθ εφ : ℚ) :
    brCheckN r p idx εθ εφ
      = Local2Fast.brCheck r p (pythonVertexA ∘ idx) εθ εφ := by
  have hq := app6_intCast p.θ₂ p.φ₂
  have vertIff : ∀ a : VertexIndex,
      (brVertN r.num εθ.num εθ.den εφ.num εφ.den (6 * ((εθ.den : ℤ) * εφ.den) ^ 3)
        r.den (app6N (sinNum13 p.θ₂) (cosNum13 p.θ₂) (sinNum13 p.φ₂) (cosNum13 p.φ₂) a)
        = true)
      ↔ (r + Local2Fast.dRotMs RationalApprox.sqrtApprox16.upper_sqrt (3 * κℚ)
            (app6 (fam2 p.θ₂ p.φ₂) (pythonVertexA a)) εθ εφ 1 + 3 * κℚ
          < RationalApprox.sqrtApprox16.lower_sqrt.f
              (RationalApprox.round13 (app6 (fam2 p.θ₂ p.φ₂) (pythonVertexA a)).a0
                  * RationalApprox.round13 (app6 (fam2 p.θ₂ p.φ₂) (pythonVertexA a)).a0
                + RationalApprox.round13 (app6 (fam2 p.θ₂ p.φ₂) (pythonVertexA a)).a1
                  * RationalApprox.round13 (app6 (fam2 p.θ₂ p.φ₂) (pythonVertexA a)).a1)) := by
    intro a
    unfold brVertN Local2Fast.dRotMs
    simp only [decide_eq_true_eq, hq, app6QofN]
    exact br_test_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ εθ εφ r.den_nz
      (Rat.num_div_den r).symm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rw [Bool.eq_iff_iff]
  unfold brCheckN Local2Fast.brCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, Function.comp_apply,
    List.all_eq_true, List.mem_finRange, forall_const]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩ i
    fin_cases i
    · exact (vertIff (idx 0)).mp h0
    · exact (vertIff (idx 1)).mp h1
    · exact (vertIff (idx 2)).mp h2
  · intro h
    exact ⟨⟨(vertIff (idx 0)).mpr (h 0), (vertIff (idx 1)).mpr (h 1)⟩,
      (vertIff (idx 2)).mpr (h 2)⟩

/-- `BoundR₂ℚ` at `pythonVertexA` decided through the integer core.
Out-prioritizes `Local2Fast.instDecidableBoundR₂ℚ`. -/
instance (priority := 10600) instDecidableBoundR₂N (r : ℚ) (p : Pose ℚ)
    (idx : Fin 3 → VertexIndex) (εθ εφ : ℚ) :
    Decidable (RationalApprox.LocalTheorem.BoundR₂ℚ r p (pythonVertexA ∘ idx) εθ εφ
      RationalApprox.sqrtApprox16) :=
  decidable_of_iff (brCheckN r p idx εθ εφ = true)
    (by rw [brCheckN_eq]
        exact Local2Fast.brCheck_iff r p (pythonVertexA ∘ idx) εθ εφ)

end BrSound2

/-! ## `Bε₂ℚ` integer core -/

section BeSound

/-- `su.f` of a squared pair of scale-`10⁴²` fractions, plus a `10¹⁶`-scale
slack. -/
private lemma upper_f_pair42 (u v slackN : ℤ) {slack : ℚ}
    (hslack : slack = (slackN : ℚ) / 10 ^ 16) :
    RationalApprox.sqrtApprox16.upper_sqrt.f
        (((u : ℚ) / 10 ^ 42) * ((u : ℚ) / 10 ^ 42)
          + ((v : ℚ) / 10 ^ 42) * ((v : ℚ) / 10 ^ 42)) + slack
      = ((sqrtNum84 (u * u + v * v) + slackN : ℤ) : ℚ) / 10 ^ 16 := by
  rw [hslack, upper_f_eq,
    show ((u:ℚ)/10^42) * ((u:ℚ)/10^42) + ((v:ℚ)/10^42) * ((v:ℚ)/10^42)
      = ((u * u + v * v : ℤ) : ℚ) / 10 ^ 84 from by push_cast; ring,
    sqrtℚUp16_intCast_div84]
  push_cast
  ring

/-- `upper_f_pair42` at the `a`-fields of a canonical cast structure. -/
private lemma upper_f_pair42' (z : App6N) (slackN : ℤ) {slack : ℚ}
    (hslack : slack = (slackN : ℚ) / 10 ^ 16) :
    RationalApprox.sqrtApprox16.upper_sqrt.f
        ((app6QofN z).a0 * (app6QofN z).a0 + (app6QofN z).a1 * (app6QofN z).a1) + slack
      = ((sqrtNum84 (z.a0 * z.a0 + z.a1 * z.a1) + slackN : ℤ) : ℚ) / 10 ^ 16 := by
  simp only [app6QofN]
  exact upper_f_pair42 z.a0 z.a1 slackN hslack

/-- `dRotMs` at a canonical cast structure, as an integer fraction. -/
private lemma dRotMs_intCast (z : App6N) {slack scale : ℚ} (slackN scaleN : ℤ)
    (εθ εφ : ℚ)
    (hslack : slack = (slackN : ℚ) / 10 ^ 16) (hscale : scale = (scaleN : ℚ) / 10 ^ 16) :
    Local2Fast.dRotMs RationalApprox.sqrtApprox16.upper_sqrt slack (app6QofN z) εθ εφ scale
      = ((budN (sqrtNum84 (z.b0 * z.b0 + z.b1 * z.b1) + slackN)
          (sqrtNum84 (z.c0 * z.c0 + z.c1 * z.c1) + slackN)
          (sqrtNum84 (z.d0 * z.d0 + z.d1 * z.d1) + slackN)
          (sqrtNum84 (z.e0 * z.e0 + z.e1 * z.e1) + slackN)
          (sqrtNum84 (z.f0 * z.f0 + z.f1 * z.f1) + slackN) scaleN
          εθ.num εθ.den εφ.num εφ.den : ℤ) : ℚ)
        / (6 * ((εθ.den : ℚ) * (εφ.den : ℚ)) ^ 3 * 10 ^ 16) := by
  unfold Local2Fast.dRotMs
  simp only [app6QofN]
  exact budN_div_eq _ _ _ _ _ _ εθ εφ 16
    (upper_f_pair42 z.b0 z.b1 slackN hslack) (upper_f_pair42 z.c0 z.c1 slackN hslack)
    (upper_f_pair42 z.d0 z.d1 slackN hslack) (upper_f_pair42 z.e0 z.e1 slackN hslack)
    (upper_f_pair42 z.f0 z.f1 slackN hslack) hscale

/-- `dProd1` at canonical cast structures, as an integer fraction. -/
private lemma dProd1_intCast (x y : App6N) {nrm : ℚ} (nrmN : ℤ) (εθ εφ : ℚ)
    (hnrm : nrm = (nrmN : ℚ) / 10 ^ 16) :
    Local2Fast.dProd1 (9 * κℚ) (app6QofN x) (app6QofN y) εθ εφ nrm
      = ((budN (|(x.b0 * y.a0 + x.b1 * y.a1) + (x.a0 * y.b0 + x.a1 * y.b1)| + 18 * 10 ^ 74)
          (|(x.c0 * y.a0 + x.c1 * y.a1) + (x.a0 * y.c0 + x.a1 * y.c1)| + 18 * 10 ^ 74)
          (|(x.d0 * y.a0 + x.d1 * y.a1) + 2 * (x.b0 * y.b0 + x.b1 * y.b1)
              + (x.a0 * y.d0 + x.a1 * y.d1)| + 36 * 10 ^ 74)
          (|(x.e0 * y.a0 + x.e1 * y.a1) + (x.b0 * y.c0 + x.b1 * y.c1)
              + (x.c0 * y.b0 + x.c1 * y.b1) + (x.a0 * y.e0 + x.a1 * y.e1)| + 36 * 10 ^ 74)
          (|(x.f0 * y.a0 + x.f1 * y.a1) + 2 * (x.c0 * y.c0 + x.c1 * y.c1)
              + (x.a0 * y.f0 + x.a1 * y.f1)| + 36 * 10 ^ 74)
          (8 * nrmN * 10 ^ 68)
          εθ.num εθ.den εφ.num εφ.den : ℤ) : ℚ)
        / (6 * ((εθ.den : ℚ) * (εφ.den : ℚ)) ^ 3 * 10 ^ 84) := by
  unfold Local2Fast.dProd1
  simp only [app6QofN]
  refine budN_div_eq _ _ _ _ _ _ εθ εφ 84 ?_ ?_ ?_ ?_ ?_
    (by rw [hnrm]; push_cast; ring)
  · rw [show ((x.b0:ℚ)/10^42) * ((y.a0:ℚ)/10^42) + ((x.b1:ℚ)/10^42) * ((y.a1:ℚ)/10^42)
          + (((x.a0:ℚ)/10^42) * ((y.b0:ℚ)/10^42) + ((x.a1:ℚ)/10^42) * ((y.b1:ℚ)/10^42))
        = (((x.b0 * y.a0 + x.b1 * y.a1) + (x.a0 * y.b0 + x.a1 * y.b1) : ℤ) : ℚ) / 10 ^ 84
        from by push_cast; ring,
      show (2:ℚ) * (9 * κℚ) = ((18 : ℤ) : ℚ) / 10 ^ 10 from by norm_num [κℚ]]
    exact abs_add_slack84 _ 18 rfl
  · rw [show ((x.c0:ℚ)/10^42) * ((y.a0:ℚ)/10^42) + ((x.c1:ℚ)/10^42) * ((y.a1:ℚ)/10^42)
          + (((x.a0:ℚ)/10^42) * ((y.c0:ℚ)/10^42) + ((x.a1:ℚ)/10^42) * ((y.c1:ℚ)/10^42))
        = (((x.c0 * y.a0 + x.c1 * y.a1) + (x.a0 * y.c0 + x.a1 * y.c1) : ℤ) : ℚ) / 10 ^ 84
        from by push_cast; ring,
      show (2:ℚ) * (9 * κℚ) = ((18 : ℤ) : ℚ) / 10 ^ 10 from by norm_num [κℚ]]
    exact abs_add_slack84 _ 18 rfl
  · rw [show ((x.d0:ℚ)/10^42) * ((y.a0:ℚ)/10^42) + ((x.d1:ℚ)/10^42) * ((y.a1:ℚ)/10^42)
          + 2 * (((x.b0:ℚ)/10^42) * ((y.b0:ℚ)/10^42) + ((x.b1:ℚ)/10^42) * ((y.b1:ℚ)/10^42))
          + (((x.a0:ℚ)/10^42) * ((y.d0:ℚ)/10^42) + ((x.a1:ℚ)/10^42) * ((y.d1:ℚ)/10^42))
        = (((x.d0 * y.a0 + x.d1 * y.a1) + 2 * (x.b0 * y.b0 + x.b1 * y.b1)
            + (x.a0 * y.d0 + x.a1 * y.d1) : ℤ) : ℚ) / 10 ^ 84 from by push_cast; ring,
      show (4:ℚ) * (9 * κℚ) = ((36 : ℤ) : ℚ) / 10 ^ 10 from by norm_num [κℚ]]
    exact abs_add_slack84 _ 36 rfl
  · rw [show ((x.e0:ℚ)/10^42) * ((y.a0:ℚ)/10^42) + ((x.e1:ℚ)/10^42) * ((y.a1:ℚ)/10^42)
          + (((x.b0:ℚ)/10^42) * ((y.c0:ℚ)/10^42) + ((x.b1:ℚ)/10^42) * ((y.c1:ℚ)/10^42))
          + (((x.c0:ℚ)/10^42) * ((y.b0:ℚ)/10^42) + ((x.c1:ℚ)/10^42) * ((y.b1:ℚ)/10^42))
          + (((x.a0:ℚ)/10^42) * ((y.e0:ℚ)/10^42) + ((x.a1:ℚ)/10^42) * ((y.e1:ℚ)/10^42))
        = (((x.e0 * y.a0 + x.e1 * y.a1) + (x.b0 * y.c0 + x.b1 * y.c1)
            + (x.c0 * y.b0 + x.c1 * y.b1) + (x.a0 * y.e0 + x.a1 * y.e1) : ℤ) : ℚ) / 10 ^ 84
        from by push_cast; ring,
      show (4:ℚ) * (9 * κℚ) = ((36 : ℤ) : ℚ) / 10 ^ 10 from by norm_num [κℚ]]
    exact abs_add_slack84 _ 36 rfl
  · rw [show ((x.f0:ℚ)/10^42) * ((y.a0:ℚ)/10^42) + ((x.f1:ℚ)/10^42) * ((y.a1:ℚ)/10^42)
          + 2 * (((x.c0:ℚ)/10^42) * ((y.c0:ℚ)/10^42) + ((x.c1:ℚ)/10^42) * ((y.c1:ℚ)/10^42))
          + (((x.a0:ℚ)/10^42) * ((y.f0:ℚ)/10^42) + ((x.a1:ℚ)/10^42) * ((y.f1:ℚ)/10^42))
        = (((x.f0 * y.a0 + x.f1 * y.a1) + 2 * (x.c0 * y.c0 + x.c1 * y.c1)
            + (x.a0 * y.f0 + x.a1 * y.f1) : ℤ) : ℚ) / 10 ^ 84 from by push_cast; ring,
      show (4:ℚ) * (9 * κℚ) = ((36 : ℤ) : ℚ) / 10 ^ 10 from by norm_num [κℚ]]
    exact abs_add_slack84 _ 36 rfl

/-- `dRotMs` is nonnegative on nonnegative data. -/
private lemma dRotMs_nonneg {slack scale : ℚ} (q : App6) (εθ εφ : ℚ)
    (hs : 0 ≤ slack) (hsc : 0 ≤ scale) (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ) :
    0 ≤ Local2Fast.dRotMs RationalApprox.sqrtApprox16.upper_sqrt slack q εθ εφ scale := by
  unfold Local2Fast.dRotMs
  simp only [upper_f_eq]
  have h := RationalApprox.sqrtℚUp16_nonneg
  have hE3 : (0:ℚ) ≤ (εθ + εφ)^3 := pow_nonneg (by linarith) 3
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
  · exact mul_nonneg hεθ (add_nonneg (h _) hs)
  · exact mul_nonneg hεφ (add_nonneg (h _) hs)
  · refine mul_nonneg (by norm_num) (add_nonneg (add_nonneg ?_ ?_) ?_)
    · exact mul_nonneg (sq_nonneg _) (add_nonneg (h _) hs)
    · exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hεθ hεφ))
        (add_nonneg (h _) hs)
    · exact mul_nonneg (sq_nonneg _) (add_nonneg (h _) hs)
  · exact div_nonneg (mul_nonneg hsc hE3) (by norm_num)

/-- Cross-multiplication for integer-cast fractions (local copy of
`Checker/LocalNat.lean`'s private bridge). -/
private lemma intCast_div_lt_div_iff {a b A B : ℤ} (hA : (0:ℤ) < A) (hB : (0:ℤ) < B) :
    (a : ℚ) / (A : ℚ) < (b : ℚ) / (B : ℚ) ↔ a * B < b * A := by
  rw [div_lt_div_iff₀ (by exact_mod_cast hA) (by exact_mod_cast hB)]
  exact_mod_cast Iff.rfl

/-- The final per-pair comparison structure of `Bε₂ℚ`, cross-multiplied. -/
private lemma be_pair_iff (numN D1N D2N Wi δn rn : ℤ) (δd rd : ℕ)
    {num D1 D2 δ r : ℚ}
    (hWpos : 0 < Wi)
    (hδd : δd ≠ 0) (hδq : δ = (δn : ℚ) / (δd : ℚ))
    (hrd : rd ≠ 0) (hrq : r = (rn : ℚ) / (rd : ℚ)) (hrn : 0 < rn)
    (hnum : num = (numN : ℚ) / ((Wi : ℚ) * 10 ^ 84))
    (hD1 : D1 = (D1N : ℚ) / ((Wi : ℚ) * 10 ^ 16)) (hD1pos : 0 < D1)
    (hD2 : D2 = (D2N : ℚ) / ((Wi : ℚ) * 10 ^ 16)) (hD2pos : 0 < D2) :
    (0 < numN ∧ δn * rd * (10 ^ 52 * (D1N * D2N)) < numN * Wi * (δd * rn))
    ↔ (0 < num ∧ δ / r < num / (D1 * D2)) := by
  have hWQ : (0:ℚ) < (Wi : ℚ) := by exact_mod_cast hWpos
  have hδdQ : (0:ℚ) < (δd : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hδd
  have hrdQ : (0:ℚ) < (rd : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hrd
  have hrnQ : (0:ℚ) < (rn : ℚ) := by exact_mod_cast hrn
  have hD1N : (0:ℤ) < D1N := by
    have h : (0:ℚ) < (D1N : ℚ) / ((Wi : ℚ) * 10 ^ 16) := hD1 ▸ hD1pos
    have := (div_pos_iff_of_pos_right (by positivity)).mp h
    exact_mod_cast this
  have hD2N : (0:ℤ) < D2N := by
    have h : (0:ℚ) < (D2N : ℚ) / ((Wi : ℚ) * 10 ^ 16) := hD2 ▸ hD2pos
    have := (div_pos_iff_of_pos_right (by positivity)).mp h
    exact_mod_cast this
  refine and_congr ?_ ?_
  · rw [hnum]
    rw [show (0:ℚ) < (numN : ℚ) / ((Wi : ℚ) * 10 ^ 84)
        ↔ (0:ℚ) < (numN : ℚ) from div_pos_iff_of_pos_right (by positivity)]
    exact_mod_cast Iff.rfl
  · rw [hδq, hrq, hnum, hD1, hD2]
    rw [show (δn : ℚ) / (δd : ℚ) / ((rn : ℚ) / (rd : ℚ))
          = ((δn * rd : ℤ) : ℚ) / ((δd * rn : ℤ) : ℚ) from by
        push_cast
        field_simp,
      show (numN : ℚ) / ((Wi : ℚ) * 10 ^ 84)
            / ((D1N : ℚ) / ((Wi : ℚ) * 10 ^ 16) * ((D2N : ℚ) / ((Wi : ℚ) * 10 ^ 16)))
          = ((numN * Wi : ℤ) : ℚ) / ((10 ^ 52 * (D1N * D2N) : ℤ) : ℚ) from by
        have h1 : ((D1N : ℚ)) ≠ 0 := by exact_mod_cast hD1N.ne'
        have h2 : ((D2N : ℚ)) ≠ 0 := by exact_mod_cast hD2N.ne'
        push_cast
        field_simp
        ring]
    rw [intCast_div_lt_div_iff (by positivity) (by positivity)]

end BeSound

/-- Integer rendering of `Local2Fast.beCheck` (the `Bε₂ℚ` conjunct),
parameterized by the two scaled square-root bounds so the exact core
(`sqrtNum84`/`sqrtNum32`) and the Newton fast tier (`nUp84`/`nUp32`) share
one body. -/
def beCheckNCore (sq84 : ℤ → ℤ) (Qi : Fin 3 → VertexIndex) (p : Pose ℚ)
    (εθ εφ δ r : ℚ) : Bool :=
  let stN : ℤ := sinNum13 p.θ₂
  let ctN : ℤ := cosNum13 p.θ₂
  let sfN : ℤ := sinNum13 p.φ₂
  let cfN : ℤ := cosNum13 p.φ₂
  let en := εθ.num
  let ed : ℤ := εθ.den
  let fn := εφ.num
  let fd : ℤ := εφ.den
  let W : ℤ := 6 * (ed * fd) ^ 3
  let δn := δ.num
  let δd : ℤ := δ.den
  let rn := r.num
  let rd : ℤ := r.den
  (List.finRange 3).all fun i =>
    let Qk := Qi i
    let qv := app6N stN ctN sfN cfN Qk
    let D1N := W * (sq84 (qv.a0 * qv.a0 + qv.a1 * qv.a1) + 3 * 10 ^ 6)
      + budN (sq84 (qv.b0 * qv.b0 + qv.b1 * qv.b1) + 3 * 10 ^ 6)
          (sq84 (qv.c0 * qv.c0 + qv.c1 * qv.c1) + 3 * 10 ^ 6)
          (sq84 (qv.d0 * qv.d0 + qv.d1 * qv.d1) + 3 * 10 ^ 6)
          (sq84 (qv.e0 * qv.e0 + qv.e1 * qv.e1) + 3 * 10 ^ 6)
          (sq84 (qv.f0 * qv.f0 + qv.f1 * qv.f1) + 3 * 10 ^ 6) (10 ^ 16) en ed fn fd
    decide <| ∀ k : VertexIndex, k ≠ Qk →
      let vk := app6N stN ctN sfN cfN k
      let dq := qv.sub vk
      let nrmN := sqrtDvCurriedN Qk.ℓ Qk.i Qk.k k.ℓ k.i k.k + 2 * 10 ^ 6
      let numN := W * (qv.a0 * dq.a0 + qv.a1 * dq.a1) - W * (9 * 10 ^ 74)
        - budN (|(qv.b0 * dq.a0 + qv.b1 * dq.a1) + (qv.a0 * dq.b0 + qv.a1 * dq.b1)|
              + 18 * 10 ^ 74)
            (|(qv.c0 * dq.a0 + qv.c1 * dq.a1) + (qv.a0 * dq.c0 + qv.a1 * dq.c1)|
              + 18 * 10 ^ 74)
            (|(qv.d0 * dq.a0 + qv.d1 * dq.a1) + 2 * (qv.b0 * dq.b0 + qv.b1 * dq.b1)
                + (qv.a0 * dq.d0 + qv.a1 * dq.d1)| + 36 * 10 ^ 74)
            (|(qv.e0 * dq.a0 + qv.e1 * dq.a1) + (qv.b0 * dq.c0 + qv.b1 * dq.c1)
                + (qv.c0 * dq.b0 + qv.c1 * dq.b1) + (qv.a0 * dq.e0 + qv.a1 * dq.e1)|
              + 36 * 10 ^ 74)
            (|(qv.f0 * dq.a0 + qv.f1 * dq.a1) + 2 * (qv.c0 * dq.c0 + qv.c1 * dq.c1)
                + (qv.a0 * dq.f0 + qv.a1 * dq.f1)| + 36 * 10 ^ 74)
            (8 * nrmN * 10 ^ 68) en ed fn fd
      let D2N := W * (sq84 (dq.a0 * dq.a0 + dq.a1 * dq.a1) + 5 * 10 ^ 6)
        + budN (sq84 (dq.b0 * dq.b0 + dq.b1 * dq.b1) + 5 * 10 ^ 6)
            (sq84 (dq.c0 * dq.c0 + dq.c1 * dq.c1) + 5 * 10 ^ 6)
            (sq84 (dq.d0 * dq.d0 + dq.d1 * dq.d1) + 5 * 10 ^ 6)
            (sq84 (dq.e0 * dq.e0 + dq.e1 * dq.e1) + 5 * 10 ^ 6)
            (sq84 (dq.f0 * dq.f0 + dq.f1 * dq.f1) + 5 * 10 ^ 6) nrmN en ed fn fd
      0 < numN ∧ δn * rd * (10 ^ 52 * (D1N * D2N)) < numN * W * (δd * rn)

/-- The exact integer core. -/
def beCheckN (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (εθ εφ δ r : ℚ) : Bool :=
  beCheckNCore sqrtNum84 Qi p εθ εφ δ r

section BeSound2

/-- The integer core computes exactly `Local2Fast.beCheck` in the
`0 ≤ εθ`, `0 ≤ εφ`, `0 < r` regime. -/
theorem beCheckN_eq (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) {εθ εφ : ℚ} (δ : ℚ) {r : ℚ}
    (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ) (hr : 0 < r) :
    beCheckN Qi p εθ εφ δ r = Local2Fast.beCheck Qi p εθ εφ δ r := by
  have hq := app6_intCast p.θ₂ p.φ₂
  have hv := pythonVertexA_intCast
  have hκ2 : (2:ℚ) * κℚ = ((2 * 10 ^ 6 : ℤ) : ℚ) / 10 ^ 16 := by norm_num [κℚ]
  have hκ3 : (3:ℚ) * κℚ = ((3 * 10 ^ 6 : ℤ) : ℚ) / 10 ^ 16 := by norm_num [κℚ]
  have hκ5 : (5:ℚ) * κℚ = ((5 * 10 ^ 6 : ℤ) : ℚ) / 10 ^ 16 := by norm_num [κℚ]
  have hone : (1:ℚ) = ((10 ^ 16 : ℤ) : ℚ) / 10 ^ 16 := by norm_num
  have hWpos : (0:ℤ) < 6 * ((εθ.den : ℤ) * εφ.den) ^ 3 := by
    have h1 : (0:ℤ) < (εθ.den : ℤ) := by exact_mod_cast εθ.pos
    have h2 : (0:ℤ) < (εφ.den : ℤ) := by exact_mod_cast εφ.pos
    positivity
  have hWcast : ((6 * ((εθ.den : ℤ) * εφ.den) ^ 3 : ℤ) : ℚ)
      = 6 * ((εθ.den : ℚ) * (εφ.den : ℚ)) ^ 3 := by push_cast; ring
  rw [Bool.eq_iff_iff]
  unfold beCheckN beCheckNCore Local2Fast.beCheck
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq,
    Local2Fast.apps6Get_apps6, hq, app6QofN_sub]
  refine forall_congr' fun i => ?_
  refine forall_congr' fun k => ?_
  refine imp_congr_right fun _ => ?_
  set X := app6N (sinNum13 p.θ₂) (cosNum13 p.θ₂) (sinNum13 p.φ₂) (cosNum13 p.φ₂) (Qi i)
    with hX
  set Y := X.sub (app6N (sinNum13 p.θ₂) (cosNum13 p.θ₂) (sinNum13 p.φ₂) (cosNum13 p.φ₂) k)
    with hY
  -- the nrm bridge: the pair distance's upper norm is the `sqrtDv` literal
  have hnrm : RationalApprox.sqrtApprox16.upper_sqrt.f
        ((pythonVertexA (Qi i) 0 - pythonVertexA k 0)
            * (pythonVertexA (Qi i) 0 - pythonVertexA k 0)
          + (pythonVertexA (Qi i) 1 - pythonVertexA k 1)
            * (pythonVertexA (Qi i) 1 - pythonVertexA k 1)
          + (pythonVertexA (Qi i) 2 - pythonVertexA k 2)
            * (pythonVertexA (Qi i) 2 - pythonVertexA k 2)) + 2 * κℚ
      = ((sqrtDvCurriedN (Qi i).ℓ (Qi i).i (Qi i).k k.ℓ k.i k.k + 2 * 10 ^ 6 : ℤ) : ℚ)
        / 10 ^ 16 := by
    rw [show RationalApprox.sqrtApprox16.upper_sqrt.f
          ((pythonVertexA (Qi i) 0 - pythonVertexA k 0)
              * (pythonVertexA (Qi i) 0 - pythonVertexA k 0)
            + (pythonVertexA (Qi i) 1 - pythonVertexA k 1)
              * (pythonVertexA (Qi i) 1 - pythonVertexA k 1)
            + (pythonVertexA (Qi i) 2 - pythonVertexA k 2)
              * (pythonVertexA (Qi i) 2 - pythonVertexA k 2))
        = RationalApprox.sqrtApprox16.upper_sqrt.norm
            (pythonVertexA (Qi i) - pythonVertexA k) from by
      rw [norm3_eq]
      simp only [Pi.sub_apply]]
    rw [← sqrtDv_eq,
      show sqrtDv (Qi i) k
          = ((sqrtDvCurriedN (Qi i).ℓ (Qi i).i (Qi i).k k.ℓ k.i k.k : ℤ) : ℚ) / 10 ^ 16
        from rfl, hκ2]
    push_cast
    ring
  -- the assembled value bridges
  have hcenter : (app6QofN X).a0 * (app6QofN Y).a0 + (app6QofN X).a1 * (app6QofN Y).a1
      = ((X.a0 * Y.a0 + X.a1 * Y.a1 : ℤ) : ℚ) / 10 ^ 84 := by
    simp only [app6QofN]
    push_cast
    ring
  refine be_pair_iff _ _ _ (6 * ((εθ.den : ℤ) * εφ.den) ^ 3) δ.num r.num δ.den r.den
    hWpos δ.den_nz (Rat.num_div_den δ).symm r.den_nz (Rat.num_div_den r).symm
    (Rat.num_pos.mpr hr) ?_ ?_ ?_ ?_ ?_ |>.symm.symm
  -- hnum
  · rw [hcenter, dProd1_intCast X Y _ εθ εφ hnrm,
      show (9:ℚ) * κℚ = ((9 * 10 ^ 74 : ℤ) : ℚ) / 10 ^ 84 from by norm_num [κℚ]]
    rw [eq_div_iff (by rw [hWcast] at *; positivity), hWcast]
    push_cast
    field_simp
  -- hD1
  · rw [upper_f_pair42' X (3 * 10 ^ 6) hκ3,
      dRotMs_intCast X (3 * 10 ^ 6) (10 ^ 16) εθ εφ hκ3 hone]
    rw [eq_div_iff (by rw [hWcast] at *; positivity), hWcast]
    push_cast
    field_simp
  -- hD1pos
  · have h1 : (0:ℚ) ≤ RationalApprox.sqrtApprox16.upper_sqrt.f
        ((app6QofN X).a0 * (app6QofN X).a0 + (app6QofN X).a1 * (app6QofN X).a1) := by
      rw [upper_f_eq]; exact RationalApprox.sqrtℚUp16_nonneg _
    have h2 : (0:ℚ) ≤ Local2Fast.dRotMs RationalApprox.sqrtApprox16.upper_sqrt (3 * κℚ)
        (app6QofN X) εθ εφ 1 :=
      dRotMs_nonneg _ εθ εφ (by norm_num [κℚ]) (by norm_num) hεθ hεφ
    have h3 : (0:ℚ) < 3 * κℚ := by norm_num [κℚ]
    linarith
  -- hD2
  · rw [upper_f_pair42' Y (5 * 10 ^ 6) hκ5,
      dRotMs_intCast Y (5 * 10 ^ 6) _ εθ εφ hκ5 hnrm]
    rw [eq_div_iff (by rw [hWcast] at *; positivity), hWcast]
    push_cast
    field_simp
  -- hD2pos
  · have h1 : (0:ℚ) ≤ RationalApprox.sqrtApprox16.upper_sqrt.f
        ((app6QofN Y).a0 * (app6QofN Y).a0 + (app6QofN Y).a1 * (app6QofN Y).a1) := by
      rw [upper_f_eq]; exact RationalApprox.sqrtℚUp16_nonneg _
    have hnrm_nn : (0:ℚ) ≤ RationalApprox.sqrtApprox16.upper_sqrt.f
          ((pythonVertexA (Qi i) 0 - pythonVertexA k 0)
              * (pythonVertexA (Qi i) 0 - pythonVertexA k 0)
            + (pythonVertexA (Qi i) 1 - pythonVertexA k 1)
              * (pythonVertexA (Qi i) 1 - pythonVertexA k 1)
            + (pythonVertexA (Qi i) 2 - pythonVertexA k 2)
              * (pythonVertexA (Qi i) 2 - pythonVertexA k 2)) + 2 * κℚ := by
      have := RationalApprox.sqrtℚUp16_nonneg
        ((pythonVertexA (Qi i) 0 - pythonVertexA k 0)
            * (pythonVertexA (Qi i) 0 - pythonVertexA k 0)
          + (pythonVertexA (Qi i) 1 - pythonVertexA k 1)
            * (pythonVertexA (Qi i) 1 - pythonVertexA k 1)
          + (pythonVertexA (Qi i) 2 - pythonVertexA k 2)
            * (pythonVertexA (Qi i) 2 - pythonVertexA k 2))
      rw [upper_f_eq]
      have hκp : (0:ℚ) < 2 * κℚ := by norm_num [κℚ]
      linarith
    have h2 : (0:ℚ) ≤ Local2Fast.dRotMs RationalApprox.sqrtApprox16.upper_sqrt (5 * κℚ)
        (app6QofN Y) εθ εφ _ :=
      dRotMs_nonneg _ εθ εφ (by norm_num [κℚ]) hnrm_nn hεθ hεφ
    have h3 : (0:ℚ) < 5 * κℚ := by norm_num [κℚ]
    linarith

end BeSound2


/-! ## Newton upper bounds for the fast tier

Every square root of `beCheckN` sits on the conservative side of its
comparison (denominators, the subtracted product budget, and the `nrm`
factor of the subtracted remainder), so a fuel-based Newton *upper* bound
(`NewtonSqrt.newtonSqrtUp`, ~9 divisions instead of `Nat.sqrt`'s ~70)
gives a sound sufficient test. The start is branch-selected by input
magnitude so the overshoot stays small; inputs beyond `10³⁴` (never hit on
table data) fall back to the exact square root. -/

/-- Branch-started Newton upper bound for `Nat.sqrt m + 1`. -/
def nUp (m : ℕ) : ℕ :=
  if m ≤ 10 ^ 8 then Noperthedron.NewtonSqrt.newtonSqrtUp m 9 (2 * 10 ^ 4) + 1
  else if m ≤ 10 ^ 16 then Noperthedron.NewtonSqrt.newtonSqrtUp m 9 (2 * 10 ^ 8) + 1
  else if m ≤ 10 ^ 24 then Noperthedron.NewtonSqrt.newtonSqrtUp m 9 (2 * 10 ^ 12) + 1
  else if m ≤ 10 ^ 34 then Noperthedron.NewtonSqrt.newtonSqrtUp m 10 (2 * 10 ^ 17) + 1
  else Nat.sqrt m + 1

private lemma sqrt_le_of_le {m s : ℕ} (h : m ≤ s * s) : Nat.sqrt m ≤ s :=
  le_trans (Nat.sqrt_le_sqrt h)
    (le_of_eq (by rw [show s * s = s ^ 2 from (sq s).symm]; exact Nat.sqrt_eq' s))

lemma sqrt_succ_le_nUp (m : ℕ) : Nat.sqrt m + 1 ≤ nUp m := by
  unfold nUp
  split_ifs with h1 h2 h3 h4
  · exact Nat.succ_le_succ (Noperthedron.NewtonSqrt.newtonSqrtUp_ge_sqrt (by norm_num)
      (sqrt_le_of_le (le_trans h1 (by norm_num))))
  · exact Nat.succ_le_succ (Noperthedron.NewtonSqrt.newtonSqrtUp_ge_sqrt (by norm_num)
      (sqrt_le_of_le (le_trans h2 (by norm_num))))
  · exact Nat.succ_le_succ (Noperthedron.NewtonSqrt.newtonSqrtUp_ge_sqrt (by norm_num)
      (sqrt_le_of_le (le_trans h3 (by norm_num))))
  · exact Nat.succ_le_succ (Noperthedron.NewtonSqrt.newtonSqrtUp_ge_sqrt (by norm_num)
      (sqrt_le_of_le (le_trans h4 (by norm_num))))
  · exact le_refl _

/-- Newton upper bound for `sqrtNum84`. -/
def nUp84 (S : ℤ) : ℤ :=
  if S ≤ 0 then 0 else (nUp (-(-S / 10 ^ 52)).toNat : ℕ)

/-- Newton upper bound for `sqrtNum32`. -/
def nUp32 (S : ℤ) : ℤ :=
  if S ≤ 0 then 0 else (nUp S.toNat : ℕ)

lemma sqrtNum84_le_nUp84 (S : ℤ) : sqrtNum84 S ≤ nUp84 S := by
  unfold sqrtNum84 nUp84
  split_ifs with h
  · exact le_refl _
  · exact_mod_cast sqrt_succ_le_nUp _

lemma sqrtNum32_le_nUp32 (S : ℤ) : sqrtNum32 S ≤ nUp32 S := by
  unfold sqrtNum32 nUp32
  split_ifs with h
  · exact le_refl _
  · exact_mod_cast sqrt_succ_le_nUp _

/-- The Newton fast tier (one-sided: `true` implies `beCheckN`). -/
def beFastN (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (εθ εφ δ r : ℚ) : Bool :=
  beCheckNCore nUp84 Qi p εθ εφ δ r

lemma sqrtNum84_nonneg (S : ℤ) : 0 ≤ sqrtNum84 S := by
  unfold sqrtNum84
  split_ifs <;> positivity

lemma sqrtNum32_nonneg (S : ℤ) : 0 ≤ sqrtNum32 S := by
  unfold sqrtNum32
  split_ifs <;> positivity

/-! ## Fast-tier soundness -/

section FastSound

private lemma budN_mono {a1 a2 a3 a4 a5 rem a1' a2' a3' a4' a5' rem' en ed fn fd : ℤ}
    (hen : 0 ≤ en) (hed : 0 ≤ ed) (hfn : 0 ≤ fn) (hfd : 0 ≤ fd)
    (h1 : a1 ≤ a1') (h2 : a2 ≤ a2') (h3 : a3 ≤ a3') (h4 : a4 ≤ a4') (h5 : a5 ≤ a5')
    (hr : rem ≤ rem') :
    budN a1 a2 a3 a4 a5 rem en ed fn fd ≤ budN a1' a2' a3' a4' a5' rem' en ed fn fd := by
  unfold budN
  have c1 : (0:ℤ) ≤ 6 * en * ed ^ 2 * fd ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hen) (pow_nonneg hed 2))
      (pow_nonneg hfd 3)
  have c2 : (0:ℤ) ≤ 6 * fn * fd ^ 2 * ed ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hfn) (pow_nonneg hfd 2))
      (pow_nonneg hed 3)
  have c3 : (0:ℤ) ≤ 3 * en ^ 2 * ed * fd ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hed)
      (pow_nonneg hfd 3)
  have c4 : (0:ℤ) ≤ 6 * en * fn * ed ^ 2 * fd ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hen) hfn)
      (pow_nonneg hed 2)) (pow_nonneg hfd 2)
  have c5 : (0:ℤ) ≤ 3 * fn ^ 2 * fd * ed ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hfd)
      (pow_nonneg hed 3)
  have cE : (0:ℤ) ≤ (en * fd + fn * ed) ^ 3 :=
    pow_nonneg (add_nonneg (mul_nonneg hen hfd) (mul_nonneg hfn hed)) 3
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left h1 c1) (mul_le_mul_of_nonneg_left h2 c2))
    (mul_le_mul_of_nonneg_left h3 c3)) (mul_le_mul_of_nonneg_left h4 c4))
    (mul_le_mul_of_nonneg_left h5 c5)) (mul_le_mul_of_nonneg_left hr cE)

private lemma budN_nonneg {a1 a2 a3 a4 a5 rem en ed fn fd : ℤ}
    (hen : 0 ≤ en) (hed : 0 ≤ ed) (hfn : 0 ≤ fn) (hfd : 0 ≤ fd)
    (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3) (h4 : 0 ≤ a4) (h5 : 0 ≤ a5)
    (hr : 0 ≤ rem) :
    0 ≤ budN a1 a2 a3 a4 a5 rem en ed fn fd := by
  have := budN_mono (a1 := 0) (a2 := 0) (a3 := 0) (a4 := 0) (a5 := 0) (rem := 0)
    hen hed hfn hfd h1 h2 h3 h4 h5 hr
  simpa [budN] using this

private lemma be_pair_mono {numF numE D1F D1E D2F D2E δn rd δd rn W : ℤ}
    (hnum : numF ≤ numE) (hD1 : D1E ≤ D1F) (hD2 : D2E ≤ D2F)
    (hD1nn : 0 ≤ D1E) (hD2nn : 0 ≤ D2E)
    (hδ : 0 ≤ δn) (hrd : 0 ≤ rd) (hδd : 0 ≤ δd) (hrn : 0 ≤ rn) (hW : 0 ≤ W)
    (h1 : 0 < numF) (h2 : δn * rd * (10 ^ 52 * (D1F * D2F)) < numF * W * (δd * rn)) :
    0 < numE ∧ δn * rd * (10 ^ 52 * (D1E * D2E)) < numE * W * (δd * rn) := by
  constructor
  · linarith
  · have hp : D1E * D2E ≤ D1F * D2F := mul_le_mul hD1 hD2 hD2nn (le_trans hD1nn hD1)
    have hL : δn * rd * (10 ^ 52 * (D1E * D2E)) ≤ δn * rd * (10 ^ 52 * (D1F * D2F)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by positivity))
        (mul_nonneg hδ hrd)
    have hR : numF * W * (δd * rn) ≤ numE * W * (δd * rn) := by
      calc numF * W * (δd * rn) = numF * (W * (δd * rn)) := by ring
        _ ≤ numE * (W * (δd * rn)) :=
            mul_le_mul_of_nonneg_right hnum (mul_nonneg hW (mul_nonneg hδd hrn))
        _ = numE * W * (δd * rn) := by ring
    linarith

private lemma sqrtDvCurriedN_nonneg (a b : VertexIndex) :
    0 ≤ sqrtDvCurriedN a.ℓ a.i a.k b.ℓ b.i b.k := by
  have h : (0:ℚ) ≤ ((sqrtDvCurriedN a.ℓ a.i a.k b.ℓ b.i b.k : ℤ) : ℚ) / 10 ^ 16 := by
    rw [show ((sqrtDvCurriedN a.ℓ a.i a.k b.ℓ b.i b.k : ℤ) : ℚ) / 10 ^ 16
        = sqrtDv a b from rfl, sqrtDv_eq]
    rw [show RationalApprox.sqrtApprox16.upper_sqrt.norm
          (pythonVertexA a - pythonVertexA b)
        = RationalApprox.sqrtℚUp16 ((pythonVertexA a - pythonVertexA b)
            ⬝ᵥ (pythonVertexA a - pythonVertexA b)) from rfl]
    exact RationalApprox.sqrtℚUp16_nonneg _
  have h2 : (0:ℚ) ≤ ((sqrtDvCurriedN a.ℓ a.i a.k b.ℓ b.i b.k : ℤ) : ℚ) := by
    have := mul_le_mul_of_nonneg_right h (show (0:ℚ) ≤ 10 ^ 16 by norm_num)
    simpa using this
  exact_mod_cast h2

/-- The fast tier is sound: `beFastN = true` implies `beCheckN = true` in the
`0 ≤ εθ.num`, `0 ≤ εφ.num`, `0 ≤ δ.num`, `0 < r.num` regime. -/
theorem beFastN_imp_beCheckN {Qi : Fin 3 → VertexIndex} {p : Pose ℚ} {εθ εφ δ r : ℚ}
    (hεθ : 0 ≤ εθ.num) (hεφ : 0 ≤ εφ.num) (hδ : 0 ≤ δ.num) (hr : 0 < r.num)
    (h : beFastN Qi p εθ εφ δ r = true) : beCheckN Qi p εθ εφ δ r = true := by
  have hed : (0:ℤ) ≤ (εθ.den : ℤ) := Int.natCast_nonneg _
  have hfd : (0:ℤ) ≤ (εφ.den : ℤ) := Int.natCast_nonneg _
  have hW : (0:ℤ) ≤ 6 * ((εθ.den : ℤ) * εφ.den) ^ 3 := by positivity
  unfold beFastN at h
  unfold beCheckN
  unfold beCheckNCore at h ⊢
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq] at h ⊢
  intro i k hk
  have hik := h i k hk
  refine be_pair_mono ?_ ?_ ?_ ?_ ?_ hδ (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    hr.le hW hik.1 hik.2
  -- numF ≤ numE : only the subtracted budget's remainder differs
  · exact sub_le_sub_left (budN_mono hεθ hed hεφ hfd (le_refl _) (le_refl _) (le_refl _)
      (le_refl _) (le_refl _) (le_refl _)) _
  -- D1E ≤ D1F
  · refine add_le_add (mul_le_mul_of_nonneg_left
      (add_le_add (sqrtNum84_le_nUp84 _) (le_refl _)) hW) ?_
    exact budN_mono hεθ hed hεφ hfd
      (add_le_add (sqrtNum84_le_nUp84 _) (le_refl _)) (add_le_add (sqrtNum84_le_nUp84 _) (le_refl _))
      (add_le_add (sqrtNum84_le_nUp84 _) (le_refl _)) (add_le_add (sqrtNum84_le_nUp84 _) (le_refl _))
      (add_le_add (sqrtNum84_le_nUp84 _) (le_refl _)) (le_refl _)
  -- D2E ≤ D2F
  · refine add_le_add (mul_le_mul_of_nonneg_left
      (add_le_add (sqrtNum84_le_nUp84 _) (le_refl _)) hW) ?_
    exact budN_mono hεθ hed hεφ hfd
      (add_le_add (sqrtNum84_le_nUp84 _) (le_refl _)) (add_le_add (sqrtNum84_le_nUp84 _) (le_refl _))
      (add_le_add (sqrtNum84_le_nUp84 _) (le_refl _)) (add_le_add (sqrtNum84_le_nUp84 _) (le_refl _))
      (add_le_add (sqrtNum84_le_nUp84 _) (le_refl _)) (le_refl _)
  -- 0 ≤ D1E
  · refine add_nonneg (mul_nonneg hW (add_nonneg (sqrtNum84_nonneg _) (by norm_num))) ?_
    exact budN_nonneg hεθ hed hεφ hfd
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num)) (by norm_num)
  -- 0 ≤ D2E
  · refine add_nonneg (mul_nonneg hW (add_nonneg (sqrtNum84_nonneg _) (by norm_num))) ?_
    exact budN_nonneg hεθ hed hεφ hfd
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtDvCurriedN_nonneg _ _) (by norm_num))

end FastSound

/-- `Bε₂ℚ` decided through the Newton fast tier when `0 ≤ εθ`, `0 ≤ εφ`,
`0 ≤ δ`, `0 < r` (the regime `Row.ValidLocal₂` evaluates it in), falling
back to the exact integer core and then the hoisted ℚ checker.
Out-prioritizes `Local2Fast.instDecidableBε₂ℚ`. -/
instance (priority := 10600) instDecidableBε₂N (Qi : Fin 3 → VertexIndex)
    (p : Pose ℚ) (εθ εφ δ r : ℚ) :
    Decidable (Local.TriangleQ.Bε₂ℚ Qi pythonVertexA p εθ εφ δ r
      RationalApprox.sqrtApprox16.upper_sqrt) :=
  if h : 0 ≤ εθ ∧ 0 ≤ εφ ∧ 0 ≤ δ ∧ 0 < r then
    dite (beFastN Qi p εθ εφ δ r = true)
      (fun hf => .isTrue ((Local2Fast.beCheck_iff Qi p εθ εφ δ r).mp
        (beCheckN_eq Qi p δ h.1 h.2.1 h.2.2.2 ▸ beFastN_imp_beCheckN
          (Rat.num_nonneg.mpr h.1) (Rat.num_nonneg.mpr h.2.1)
          (Rat.num_nonneg.mpr h.2.2.1) (Rat.num_pos.mpr h.2.2.2) hf)))
      (fun _ => decidable_of_iff (beCheckN Qi p εθ εφ δ r = true)
        (by rw [beCheckN_eq Qi p δ h.1 h.2.1 h.2.2.2]
            exact Local2Fast.beCheck_iff Qi p εθ εφ δ r))
  else
    decidable_of_iff _ (Local2Fast.beCheck_iff Qi p εθ εφ δ r)

end Noperthedron.Solution.Local2Nat

namespace Noperthedron.Solution

/-- Re-derived `Row.ValidLocal₂` decision procedure: identical statement to
the instance in `Checker/Local2.lean`, but elaborated with the
`Local2Nat` integer-core instances in scope. -/
instance (priority := 10600) (row : Row) : Decidable (Row.ValidLocal₂ row) :=
  decidable_of_iff _ (Row.validLocal₂_iff row).symm

end Noperthedron.Solution
end
