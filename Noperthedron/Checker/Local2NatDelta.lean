module

public import Noperthedron.Checker.Local2NatOffset

@[expose] public section

/-!
# Integer rendering of `Row.δ₂` (kernel)

`Row.δ₂` is defined through the ℚ budget formulas (`ΔrotRMℚ`/`ΔrotMℚ`,
matrix norms, `Finset.max'`), and evaluating it under the kernel costs
~0.4s per second-order local row — a third of the remaining per-row time
after the offset tier.  This module renders the *exact* value as an
unreduced integer fraction `Row.δ₂PairZ : ℤ × ℤ`, computed from the same
`app6N` applied families the `Bε₂` core already evaluates (so the kernel's
term cache shares them), plus one `sqrtNum110` for the scale-`10¹¹⁰` head
atom and a three-variable analogue `budRM3` of `budN` for the `ΔrotRMℚ`
polynomial.

`Row.δ₂PairZ_eq` proves `Row.δ₂ = num / den` with `0 < den`, and the final
`Row.ValidLocal₂` instance (priority 10800) substitutes the fraction into
the `Bε₂ℚ` conjunct before deciding, so the ℚ definition is never
evaluated: the only ℚ-normalization left is the single division that
produces the fraction's `Rat` value.
-/

namespace Noperthedron.Solution.Local2Nat

open scoped Matrix

open RationalApprox (sinNum13 cosNum13 sinℚ cosℚ κℚ ΔrotMℚ ΔrotRMℚ ΔrotMℚs
  sqrtApprox16 UpperSqrt)
open Noperthedron.Solution.Local2Fast (App6 app6 fam2 norm2_eq app6_a0 app6_a1
  app6_b0 app6_b1 app6_c0 app6_c1 app6_d0 app6_d1 app6_e0 app6_e1 app6_f0
  app6_f1 dRotMs dRotMs_eq)

/-! ## Scale-`10¹¹⁰` upper square root -/

/-- `sqrtℚUp16` numerator for inputs at scale `10¹¹⁰`. -/
def sqrtNum110 (S : ℤ) : ℤ :=
  if S ≤ 0 then 0 else (Nat.sqrt (-(-S / 10 ^ 78)).toNat + 1 : ℕ)

lemma sqrtℚUp16_intCast_div110 (S : ℤ) :
    RationalApprox.sqrtℚUp16 ((S : ℚ) / 10 ^ 110) = (sqrtNum110 S : ℚ) / 10 ^ 16 := by
  unfold RationalApprox.sqrtℚUp16 sqrtNum110
  rcases le_or_gt S 0 with hS | hS
  · rw [if_pos (div_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast hS, by positivity⟩)),
      if_pos hS]
    simp
  · have hSQ : (0 : ℚ) < (S : ℚ) := by exact_mod_cast hS
    rw [if_neg (not_le.mpr (by positivity)), if_neg (not_le.mpr hS)]
    have hceil : ⌈(S : ℚ) / 10 ^ 110 * 10 ^ 32⌉ = -(-S / 10 ^ 78) := by
      rw [show (S : ℚ) / 10 ^ 110 * 10 ^ 32
          = -(((-S : ℤ) : ℚ) / ((10 ^ 78 : ℕ) : ℚ)) from by push_cast; ring]
      rw [Int.ceil_neg, Rat.floor_intCast_div_natCast]
      norm_num
    rw [hceil]
    push_cast
    ring

/-! ## Three-variable ε-budget polynomial (`ΔrotRMℚ` shape) -/

/-- Cross-multiplied form (by `6·(ad·td·fd)³·10^s`) of the `ΔrotRMℚ` budget
`εα·a0 + εθ·a1 + εφ·a2 + ½(εα²a0 + 2εαεθ a1 + 2εαεφ a2 + εθ²a3 + 2εθεφ a4
+ εφ²a5) + rem·(εα+εθ+εφ)³/6` with atoms at scale `10^s`. -/
def budRM3 (a0 a1 a2 a3 a4 a5 rem an ad tn td fn fd : ℤ) : ℤ :=
  6 * an * ad ^ 2 * (td * fd) ^ 3 * a0
    + 6 * tn * td ^ 2 * (ad * fd) ^ 3 * a1
    + 6 * fn * fd ^ 2 * (ad * td) ^ 3 * a2
    + 3 * an ^ 2 * ad * (td * fd) ^ 3 * a0
    + 6 * an * tn * ad ^ 2 * td ^ 2 * fd ^ 3 * a1
    + 6 * an * fn * ad ^ 2 * fd ^ 2 * td ^ 3 * a2
    + 3 * tn ^ 2 * td * (ad * fd) ^ 3 * a3
    + 6 * tn * fn * td ^ 2 * fd ^ 2 * ad ^ 3 * a4
    + 3 * fn ^ 2 * fd * (ad * td) ^ 3 * a5
    + (an * td * fd + tn * ad * fd + fn * ad * td) ^ 3 * rem

/-- Value bridge for `budRM3`, over independent numerator/denominator data. -/
private lemma budRM3_div_eq' (a0N a1N a2N a3N a4N a5N remN u n m : ℤ) (c d e : ℕ)
    {a0 a1 a2 a3 a4 a5 rem εα εθ εφ : ℚ} (s : ℕ)
    (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hα : εα = (u : ℚ) / (c : ℚ)) (hθ : εθ = (n : ℚ) / (d : ℚ))
    (hφ : εφ = (m : ℚ) / (e : ℚ))
    (h0 : a0 = (a0N : ℚ) / 10 ^ s) (h1 : a1 = (a1N : ℚ) / 10 ^ s)
    (h2 : a2 = (a2N : ℚ) / 10 ^ s) (h3 : a3 = (a3N : ℚ) / 10 ^ s)
    (h4 : a4 = (a4N : ℚ) / 10 ^ s) (h5 : a5 = (a5N : ℚ) / 10 ^ s)
    (hrem : rem = (remN : ℚ) / 10 ^ s) :
    εα * a0 + εθ * a1 + εφ * a2
        + (1/2) * (εα ^ 2 * a0 + 2 * (εα * εθ) * a1 + 2 * (εα * εφ) * a2
          + εθ ^ 2 * a3 + 2 * (εθ * εφ) * a4 + εφ ^ 2 * a5)
        + rem * (εα + εθ + εφ) ^ 3 / 6
      = ((budRM3 a0N a1N a2N a3N a4N a5N remN u c n d m e : ℤ) : ℚ)
        / (6 * ((c : ℚ) * (d : ℚ) * (e : ℚ)) ^ 3 * 10 ^ s) := by
  have hcQ : ((c : ℚ)) ≠ 0 := by exact_mod_cast hc
  have hdQ : ((d : ℚ)) ≠ 0 := by exact_mod_cast hd
  have heQ : ((e : ℚ)) ≠ 0 := by exact_mod_cast he
  have h10 : ((10 : ℚ)) ^ s ≠ 0 := by positivity
  rw [h0, h1, h2, h3, h4, h5, hrem, hα, hθ, hφ]
  unfold budRM3
  push_cast
  field_simp
  ring

/-- Value bridge for `budRM3` at the `Rat` num/den projections. -/
lemma budRM3_div_eq (a0N a1N a2N a3N a4N a5N remN : ℤ)
    {a0 a1 a2 a3 a4 a5 rem : ℚ} (εα εθ εφ : ℚ) (s : ℕ)
    (h0 : a0 = (a0N : ℚ) / 10 ^ s) (h1 : a1 = (a1N : ℚ) / 10 ^ s)
    (h2 : a2 = (a2N : ℚ) / 10 ^ s) (h3 : a3 = (a3N : ℚ) / 10 ^ s)
    (h4 : a4 = (a4N : ℚ) / 10 ^ s) (h5 : a5 = (a5N : ℚ) / 10 ^ s)
    (hrem : rem = (remN : ℚ) / 10 ^ s) :
    εα * a0 + εθ * a1 + εφ * a2
        + (1/2) * (εα ^ 2 * a0 + 2 * (εα * εθ) * a1 + 2 * (εα * εφ) * a2
          + εθ ^ 2 * a3 + 2 * (εθ * εφ) * a4 + εφ ^ 2 * a5)
        + rem * (εα + εθ + εφ) ^ 3 / 6
      = ((budRM3 a0N a1N a2N a3N a4N a5N remN
            εα.num εα.den εθ.num εθ.den εφ.num εφ.den : ℤ) : ℚ)
        / (6 * ((εα.den : ℚ) * (εθ.den : ℚ) * (εφ.den : ℚ)) ^ 3 * 10 ^ s) :=
  budRM3_div_eq' a0N a1N a2N a3N a4N a5N remN εα.num εθ.num εφ.num
    εα.den εθ.den εφ.den s εα.den_nz εθ.den_nz εφ.den_nz
    (Rat.num_div_den εα).symm (Rat.num_div_den εθ).symm (Rat.num_div_den εφ).symm
    h0 h1 h2 h3 h4 h5 hrem

/-! ## `ΔrotRMℚ` over `app6` fields -/

/-- The scalar `ΔrotRMℚ` on `app6` fields. -/
@[inline] def dRotRMs (su : UpperSqrt) (slack : ℚ) (q : App6) (εα εθ εφ : ℚ) : ℚ :=
  εα * (su.f (q.a0 * q.a0 + q.a1 * q.a1) + slack)
  + εθ * (su.f (q.b0 * q.b0 + q.b1 * q.b1) + slack)
  + εφ * (su.f (q.c0 * q.c0 + q.c1 * q.c1) + slack)
  + (1/2) * (εα ^ 2 * (su.f (q.a0 * q.a0 + q.a1 * q.a1) + slack)
      + 2 * (εα * εθ) * (su.f (q.b0 * q.b0 + q.b1 * q.b1) + slack)
      + 2 * (εα * εφ) * (su.f (q.c0 * q.c0 + q.c1 * q.c1) + slack)
      + εθ ^ 2 * (su.f (q.d0 * q.d0 + q.d1 * q.d1) + slack)
      + 2 * (εθ * εφ) * (su.f (q.e0 * q.e0 + q.e1 * q.e1) + slack)
      + εφ ^ 2 * (su.f (q.f0 * q.f0 + q.f1 * q.f1) + slack))
  + (εα + εθ + εφ) ^ 3 / 6

lemma dRotRMs_eq (su : UpperSqrt) (θ φ : ℚ) (v : Fin 3 → ℚ) (εα εθ εφ : ℚ) :
    ΔrotRMℚ su θ φ v εα εθ εφ
      = dRotRMs su (3 * κℚ) (app6 (fam2 θ φ) v) εα εθ εφ := by
  unfold ΔrotRMℚ dRotRMs
  simp only [norm2_eq, app6_a0, app6_a1, app6_b0, app6_b1, app6_c0, app6_c1,
    app6_d0, app6_d1, app6_e0, app6_e1, app6_f0, app6_f1]

/-! ## The δ₂ fraction -/

/-- Common denominator of the three `BoundDelta₂ℚi` numerators. -/
def δ₂DZ (row : Row) : ℤ :=
  10 ^ 16 * (6 * ((row.εα.den : ℤ) * row.εθ₁.den * row.εφ₁.den) ^ 3)
    * (6 * ((row.εθ₂.den : ℤ) * row.εφ₂.den) ^ 3)

/-- Integer numerator of `Row.BoundDelta₂ℚi i` at denominator `δ₂DZ`. -/
def δ₂BZ (row : Row) (i : Fin 3) : ℤ :=
  let p := row.interval.centerPose
  let zP := app6N (sinNum13 p.θ₁) (cosNum13 p.θ₁) (sinNum13 p.φ₁)
    (cosNum13 p.φ₁) (row.Pi i)
  let zQ := app6N (sinNum13 p.θ₂) (cosNum13 p.θ₂) (sinNum13 p.φ₂)
    (cosNum13 p.φ₂) (row.Qi i)
  let sa := sinNum13 p.α
  let ca := cosNum13 p.α
  let H0 := ca * zP.a0 - sa * zP.a1 - 10 ^ 13 * zQ.a0
  let H1 := sa * zP.a0 + ca * zP.a1 - 10 ^ 13 * zQ.a1
  let hd := sqrtNum110 (H0 * H0 + H1 * H1) + 6 * 10 ^ 6
  let W3 : ℤ := 6 * ((row.εα.den : ℤ) * row.εθ₁.den * row.εφ₁.den) ^ 3
  let W2 : ℤ := 6 * ((row.εθ₂.den : ℤ) * row.εφ₂.den) ^ 3
  let nRM := budRM3 (sqrtNum84 (zP.a0 * zP.a0 + zP.a1 * zP.a1) + 3 * 10 ^ 6)
    (sqrtNum84 (zP.b0 * zP.b0 + zP.b1 * zP.b1) + 3 * 10 ^ 6)
    (sqrtNum84 (zP.c0 * zP.c0 + zP.c1 * zP.c1) + 3 * 10 ^ 6)
    (sqrtNum84 (zP.d0 * zP.d0 + zP.d1 * zP.d1) + 3 * 10 ^ 6)
    (sqrtNum84 (zP.e0 * zP.e0 + zP.e1 * zP.e1) + 3 * 10 ^ 6)
    (sqrtNum84 (zP.f0 * zP.f0 + zP.f1 * zP.f1) + 3 * 10 ^ 6)
    (10 ^ 16) row.εα.num row.εα.den row.εθ₁.num row.εθ₁.den
    row.εφ₁.num row.εφ₁.den
  let nM := budN (sqrtNum84 (zQ.b0 * zQ.b0 + zQ.b1 * zQ.b1) + 3 * 10 ^ 6)
    (sqrtNum84 (zQ.c0 * zQ.c0 + zQ.c1 * zQ.c1) + 3 * 10 ^ 6)
    (sqrtNum84 (zQ.d0 * zQ.d0 + zQ.d1 * zQ.d1) + 3 * 10 ^ 6)
    (sqrtNum84 (zQ.e0 * zQ.e0 + zQ.e1 * zQ.e1) + 3 * 10 ^ 6)
    (sqrtNum84 (zQ.f0 * zQ.f0 + zQ.f1 * zQ.f1) + 3 * 10 ^ 6)
    (10 ^ 16) row.εθ₂.num row.εθ₂.den row.εφ₂.num row.εφ₂.den
  hd * (W3 * W2) + nRM * W2 + nM * W3

/-- The unreduced `δ₂` fraction: `Row.δ₂ = fst / snd` with `0 < snd`. -/
def _root_.Noperthedron.Solution.Row.δ₂PairZ (row : Row) : ℤ × ℤ :=
  (max (δ₂BZ row 0) (max (δ₂BZ row 1) (δ₂BZ row 2)) * 10 ^ 10 + 2 * δ₂DZ row,
   2 * δ₂DZ row * 10 ^ 10)

section DeltaBridge

private lemma mulVec2_c0 (M : Matrix (Fin 2) (Fin 2) ℚ) (w : Fin 2 → ℚ) :
    (M *ᵥ w) 0 = M 0 0 * w 0 + M 0 1 * w 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma mulVec2_c1 (M : Matrix (Fin 2) (Fin 2) ℚ) (w : Fin 2 → ℚ) :
    (M *ᵥ w) 1 = M 1 0 * w 0 + M 1 1 * w 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma hf16 : sqrtApprox16.upper_sqrt.f = RationalApprox.sqrtℚUp16 := rfl

/-- Norm atom with `3κ` slack, integer form. -/
private lemma atom84 {x y : ℚ} {zx zy : ℤ}
    (hx : x = (zx : ℚ) / 10 ^ 42) (hy : y = (zy : ℚ) / 10 ^ 42) :
    sqrtApprox16.upper_sqrt.f (x * x + y * y) + 3 * κℚ
      = ((sqrtNum84 (zx * zx + zy * zy) + 3 * 10 ^ 6 : ℤ) : ℚ) / 10 ^ 16 := by
  rw [hx, hy, hf16,
    show ((zx : ℚ) / 10 ^ 42 * ((zx : ℚ) / 10 ^ 42)
        + (zy : ℚ) / 10 ^ 42 * ((zy : ℚ) / 10 ^ 42))
      = ((zx * zx + zy * zy : ℤ) : ℚ) / 10 ^ 84 from by push_cast; ring,
    sqrtℚUp16_intCast_div84,
    show (3 * κℚ : ℚ) = ((3 * 10 ^ 6 : ℤ) : ℚ) / 10 ^ 16 from by
      norm_num [RationalApprox.κℚ]]
  push_cast
  ring

set_option maxHeartbeats 1600000 in
/-- `Row.BoundDelta₂ℚi` as the integer fraction. -/
private lemma boundDelta_bridge (row : Row) (i : Fin 3) :
    row.BoundDelta₂ℚi i = ((δ₂BZ row i : ℤ) : ℚ) / ((δ₂DZ row : ℤ) : ℚ) := by
  have dα : ((row.εα.den : ℚ)) ≠ 0 := by exact_mod_cast row.εα.den_nz
  have dθ1 : ((row.εθ₁.den : ℚ)) ≠ 0 := by exact_mod_cast row.εθ₁.den_nz
  have dφ1 : ((row.εφ₁.den : ℚ)) ≠ 0 := by exact_mod_cast row.εφ₁.den_nz
  have dθ2 : ((row.εθ₂.den : ℚ)) ≠ 0 := by exact_mod_cast row.εθ₂.den_nz
  have dφ2 : ((row.εφ₂.den : ℚ)) ≠ 0 := by exact_mod_cast row.εφ₂.den_nz
  unfold Row.BoundDelta₂ℚi δ₂BZ δ₂DZ
  dsimp only
  simp only [Function.comp_apply]
  set p : Pose ℚ := row.interval.centerPose with hp
  set Pv : Fin 3 → ℚ := pythonVertexA (row.Pi i) with hPv
  set Qv : Fin 3 → ℚ := pythonVertexA (row.Qi i) with hQv
  set zP : App6N := app6N (sinNum13 p.θ₁) (cosNum13 p.θ₁) (sinNum13 p.φ₁)
    (cosNum13 p.φ₁) (row.Pi i) with hzP
  set zQ : App6N := app6N (sinNum13 p.θ₂) (cosNum13 p.θ₂) (sinNum13 p.φ₂)
    (cosNum13 p.φ₂) (row.Qi i) with hzQ
  have hAP := app6_intCast p.θ₁ p.φ₁ (row.Pi i)
  have hAQ := app6_intCast p.θ₂ p.φ₂ (row.Qi i)
  rw [← hzP] at hAP
  rw [← hzQ] at hAQ
  -- projection casts
  have pa0 : (app6 (fam2 p.θ₁ p.φ₁) Pv).a0 = (zP.a0 : ℚ) / 10 ^ 42 := by rw [hAP]; rfl
  have pa1 : (app6 (fam2 p.θ₁ p.φ₁) Pv).a1 = (zP.a1 : ℚ) / 10 ^ 42 := by rw [hAP]; rfl
  have pb0 : (app6 (fam2 p.θ₁ p.φ₁) Pv).b0 = (zP.b0 : ℚ) / 10 ^ 42 := by rw [hAP]; rfl
  have pb1 : (app6 (fam2 p.θ₁ p.φ₁) Pv).b1 = (zP.b1 : ℚ) / 10 ^ 42 := by rw [hAP]; rfl
  have pc0 : (app6 (fam2 p.θ₁ p.φ₁) Pv).c0 = (zP.c0 : ℚ) / 10 ^ 42 := by rw [hAP]; rfl
  have pc1 : (app6 (fam2 p.θ₁ p.φ₁) Pv).c1 = (zP.c1 : ℚ) / 10 ^ 42 := by rw [hAP]; rfl
  have pd0 : (app6 (fam2 p.θ₁ p.φ₁) Pv).d0 = (zP.d0 : ℚ) / 10 ^ 42 := by rw [hAP]; rfl
  have pd1 : (app6 (fam2 p.θ₁ p.φ₁) Pv).d1 = (zP.d1 : ℚ) / 10 ^ 42 := by rw [hAP]; rfl
  have pe0 : (app6 (fam2 p.θ₁ p.φ₁) Pv).e0 = (zP.e0 : ℚ) / 10 ^ 42 := by rw [hAP]; rfl
  have pe1 : (app6 (fam2 p.θ₁ p.φ₁) Pv).e1 = (zP.e1 : ℚ) / 10 ^ 42 := by rw [hAP]; rfl
  have pf0 : (app6 (fam2 p.θ₁ p.φ₁) Pv).f0 = (zP.f0 : ℚ) / 10 ^ 42 := by rw [hAP]; rfl
  have pf1 : (app6 (fam2 p.θ₁ p.φ₁) Pv).f1 = (zP.f1 : ℚ) / 10 ^ 42 := by rw [hAP]; rfl
  have qa0 : (app6 (fam2 p.θ₂ p.φ₂) Qv).a0 = (zQ.a0 : ℚ) / 10 ^ 42 := by rw [hAQ]; rfl
  have qa1 : (app6 (fam2 p.θ₂ p.φ₂) Qv).a1 = (zQ.a1 : ℚ) / 10 ^ 42 := by rw [hAQ]; rfl
  have qb0 : (app6 (fam2 p.θ₂ p.φ₂) Qv).b0 = (zQ.b0 : ℚ) / 10 ^ 42 := by rw [hAQ]; rfl
  have qb1 : (app6 (fam2 p.θ₂ p.φ₂) Qv).b1 = (zQ.b1 : ℚ) / 10 ^ 42 := by rw [hAQ]; rfl
  have qc0 : (app6 (fam2 p.θ₂ p.φ₂) Qv).c0 = (zQ.c0 : ℚ) / 10 ^ 42 := by rw [hAQ]; rfl
  have qc1 : (app6 (fam2 p.θ₂ p.φ₂) Qv).c1 = (zQ.c1 : ℚ) / 10 ^ 42 := by rw [hAQ]; rfl
  have qd0 : (app6 (fam2 p.θ₂ p.φ₂) Qv).d0 = (zQ.d0 : ℚ) / 10 ^ 42 := by rw [hAQ]; rfl
  have qd1 : (app6 (fam2 p.θ₂ p.φ₂) Qv).d1 = (zQ.d1 : ℚ) / 10 ^ 42 := by rw [hAQ]; rfl
  have qe0 : (app6 (fam2 p.θ₂ p.φ₂) Qv).e0 = (zQ.e0 : ℚ) / 10 ^ 42 := by rw [hAQ]; rfl
  have qe1 : (app6 (fam2 p.θ₂ p.φ₂) Qv).e1 = (zQ.e1 : ℚ) / 10 ^ 42 := by rw [hAQ]; rfl
  have qf0 : (app6 (fam2 p.θ₂ p.φ₂) Qv).f0 = (zQ.f0 : ℚ) / 10 ^ 42 := by rw [hAQ]; rfl
  have qf1 : (app6 (fam2 p.θ₂ p.φ₂) Qv).f1 = (zQ.f1 : ℚ) / 10 ^ 42 := by rw [hAQ]; rfl
  -- head components
  have eM0 : p.rotM₁ℚ Pv 0 = (zP.a0 : ℚ) / 10 ^ 42 := by
    rw [show p.rotM₁ℚ Pv = RationalApprox.rotMℚ_mat p.θ₁ p.φ₁ *ᵥ Pv from by
        simp [Pose.rotM₁ℚ, RationalApprox.rotMℚ, Matrix.toLin'_apply],
      ← app6_a0]
    exact pa0
  have eM1 : p.rotM₁ℚ Pv 1 = (zP.a1 : ℚ) / 10 ^ 42 := by
    rw [show p.rotM₁ℚ Pv = RationalApprox.rotMℚ_mat p.θ₁ p.φ₁ *ᵥ Pv from by
        simp [Pose.rotM₁ℚ, RationalApprox.rotMℚ, Matrix.toLin'_apply],
      ← app6_a1]
    exact pa1
  have eN0 : p.rotM₂ℚ Qv 0 = (zQ.a0 : ℚ) / 10 ^ 42 := by
    rw [show p.rotM₂ℚ Qv = RationalApprox.rotMℚ_mat p.θ₂ p.φ₂ *ᵥ Qv from by
        simp [Pose.rotM₂ℚ, RationalApprox.rotMℚ, Matrix.toLin'_apply],
      ← app6_a0]
    exact qa0
  have eN1 : p.rotM₂ℚ Qv 1 = (zQ.a1 : ℚ) / 10 ^ 42 := by
    rw [show p.rotM₂ℚ Qv = RationalApprox.rotMℚ_mat p.θ₂ p.φ₂ *ᵥ Qv from by
        simp [Pose.rotM₂ℚ, RationalApprox.rotMℚ, Matrix.toLin'_apply],
      ← app6_a1]
    exact qa1
  have hR : p.rotRℚ (p.rotM₁ℚ Pv) = RationalApprox.rotRℚ_mat p.α *ᵥ p.rotM₁ℚ Pv := by
    simp [Pose.rotRℚ, RationalApprox.rotRℚ, Matrix.toLin'_apply]
  have hw0 : (p.rotRℚ (p.rotM₁ℚ Pv) - p.rotM₂ℚ Qv) 0
      = ((cosNum13 p.α * zP.a0 - sinNum13 p.α * zP.a1 - 10 ^ 13 * zQ.a0 : ℤ) : ℚ)
        / 10 ^ 55 := by
    rw [Pi.sub_apply, hR, mulVec2_c0,
      show (RationalApprox.rotRℚ_mat p.α : Matrix (Fin 2) (Fin 2) ℚ) 0 0
        = cosℚ p.α from by simp [RationalApprox.rotRℚ_mat],
      show (RationalApprox.rotRℚ_mat p.α : Matrix (Fin 2) (Fin 2) ℚ) 0 1
        = -sinℚ p.α from by simp [RationalApprox.rotRℚ_mat],
      eM0, eM1, eN0, ← RationalApprox.sinNum13_div_eq p.α,
      ← RationalApprox.cosNum13_div_eq p.α]
    push_cast
    ring
  have hw1 : (p.rotRℚ (p.rotM₁ℚ Pv) - p.rotM₂ℚ Qv) 1
      = ((sinNum13 p.α * zP.a0 + cosNum13 p.α * zP.a1 - 10 ^ 13 * zQ.a1 : ℤ) : ℚ)
        / 10 ^ 55 := by
    rw [Pi.sub_apply, hR, mulVec2_c1,
      show (RationalApprox.rotRℚ_mat p.α : Matrix (Fin 2) (Fin 2) ℚ) 1 0
        = sinℚ p.α from by simp [RationalApprox.rotRℚ_mat],
      show (RationalApprox.rotRℚ_mat p.α : Matrix (Fin 2) (Fin 2) ℚ) 1 1
        = cosℚ p.α from by simp [RationalApprox.rotRℚ_mat],
      eM0, eM1, eN1, ← RationalApprox.sinNum13_div_eq p.α,
      ← RationalApprox.cosNum13_div_eq p.α]
    push_cast
    ring
  -- the three summands
  have hhead : sqrtApprox16.upper_sqrt.norm (p.rotRℚ (p.rotM₁ℚ Pv) - p.rotM₂ℚ Qv)
        + 6 * κℚ
      = ((sqrtNum110 ((cosNum13 p.α * zP.a0 - sinNum13 p.α * zP.a1 - 10 ^ 13 * zQ.a0)
            * (cosNum13 p.α * zP.a0 - sinNum13 p.α * zP.a1 - 10 ^ 13 * zQ.a0)
          + (sinNum13 p.α * zP.a0 + cosNum13 p.α * zP.a1 - 10 ^ 13 * zQ.a1)
            * (sinNum13 p.α * zP.a0 + cosNum13 p.α * zP.a1 - 10 ^ 13 * zQ.a1))
          + 6 * 10 ^ 6 : ℤ) : ℚ) / 10 ^ 16 := by
    rw [norm2_eq, hw0, hw1, hf16,
      show ∀ a b : ℤ, ((a : ℚ) / 10 ^ 55 * ((a : ℚ) / 10 ^ 55)
          + (b : ℚ) / 10 ^ 55 * ((b : ℚ) / 10 ^ 55))
        = ((a * a + b * b : ℤ) : ℚ) / 10 ^ 110 from fun a b => by push_cast; ring,
      sqrtℚUp16_intCast_div110,
      show (6 * κℚ : ℚ) = ((6 * 10 ^ 6 : ℤ) : ℚ) / 10 ^ 16 from by
        norm_num [RationalApprox.κℚ]]
    push_cast
    ring
  have hRM : ΔrotRMℚ sqrtApprox16.upper_sqrt p.θ₁ p.φ₁ Pv row.εα row.εθ₁ row.εφ₁
      = ((budRM3 (sqrtNum84 (zP.a0 * zP.a0 + zP.a1 * zP.a1) + 3 * 10 ^ 6)
          (sqrtNum84 (zP.b0 * zP.b0 + zP.b1 * zP.b1) + 3 * 10 ^ 6)
          (sqrtNum84 (zP.c0 * zP.c0 + zP.c1 * zP.c1) + 3 * 10 ^ 6)
          (sqrtNum84 (zP.d0 * zP.d0 + zP.d1 * zP.d1) + 3 * 10 ^ 6)
          (sqrtNum84 (zP.e0 * zP.e0 + zP.e1 * zP.e1) + 3 * 10 ^ 6)
          (sqrtNum84 (zP.f0 * zP.f0 + zP.f1 * zP.f1) + 3 * 10 ^ 6)
          (10 ^ 16) row.εα.num row.εα.den row.εθ₁.num row.εθ₁.den
          row.εφ₁.num row.εφ₁.den : ℤ) : ℚ)
        / (6 * ((row.εα.den : ℚ) * (row.εθ₁.den : ℚ) * (row.εφ₁.den : ℚ)) ^ 3
          * 10 ^ 16) := by
    rw [dRotRMs_eq]
    unfold dRotRMs
    rw [show (row.εα + row.εθ₁ + row.εφ₁) ^ 3 / 6
        = (1 : ℚ) * (row.εα + row.εθ₁ + row.εφ₁) ^ 3 / 6 from by ring]
    exact budRM3_div_eq _ _ _ _ _ _ _ row.εα row.εθ₁ row.εφ₁ 16
      (atom84 pa0 pa1) (atom84 pb0 pb1) (atom84 pc0 pc1) (atom84 pd0 pd1)
      (atom84 pe0 pe1) (atom84 pf0 pf1) (by push_cast; norm_num)
  have hM : ΔrotMℚ sqrtApprox16.upper_sqrt p.θ₂ p.φ₂ Qv row.εθ₂ row.εφ₂
      = ((budN (sqrtNum84 (zQ.b0 * zQ.b0 + zQ.b1 * zQ.b1) + 3 * 10 ^ 6)
          (sqrtNum84 (zQ.c0 * zQ.c0 + zQ.c1 * zQ.c1) + 3 * 10 ^ 6)
          (sqrtNum84 (zQ.d0 * zQ.d0 + zQ.d1 * zQ.d1) + 3 * 10 ^ 6)
          (sqrtNum84 (zQ.e0 * zQ.e0 + zQ.e1 * zQ.e1) + 3 * 10 ^ 6)
          (sqrtNum84 (zQ.f0 * zQ.f0 + zQ.f1 * zQ.f1) + 3 * 10 ^ 6)
          (10 ^ 16) row.εθ₂.num row.εθ₂.den row.εφ₂.num row.εφ₂.den : ℤ) : ℚ)
        / (6 * ((row.εθ₂.den : ℚ) * (row.εφ₂.den : ℚ)) ^ 3 * 10 ^ 16) := by
    unfold RationalApprox.ΔrotMℚ
    rw [dRotMs_eq]
    unfold dRotMs
    exact budN_div_eq _ _ _ _ _ _ row.εθ₂ row.εφ₂ 16
      (atom84 qb0 qb1) (atom84 qc0 qc1) (atom84 qd0 qd1) (atom84 qe0 qe1)
      (atom84 qf0 qf1) (by push_cast; norm_num)
  rw [hhead, hRM, hM]
  push_cast
  field_simp
  ring

end DeltaBridge



/-- `Finset.max'` of a `Fin 3` image as a nested `max`. -/
private lemma max'_image_fin3 (f : Fin 3 → ℚ) :
    Finset.max' (Finset.image f Finset.univ)
        (Finset.image_nonempty.mpr ⟨0, Finset.mem_univ 0⟩)
      = max (f 0) (max (f 1) (f 2)) := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    fin_cases j
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  · refine max_le (Finset.le_max' _ _ ?_) (max_le (Finset.le_max' _ _ ?_)
      (Finset.le_max' _ _ ?_)) <;>
      exact Finset.mem_image_of_mem f (Finset.mem_univ _)

lemma δ₂DZ_pos (row : Row) : 0 < δ₂DZ row := by
  unfold δ₂DZ
  have h1 := row.εα.pos
  have h2 := row.εθ₁.pos
  have h3 := row.εφ₁.pos
  have h4 := row.εθ₂.pos
  have h5 := row.εφ₂.pos
  positivity

lemma _root_.Noperthedron.Solution.Row.δ₂PairZ_snd_pos (row : Row) : 0 < (row.δ₂PairZ).2 := by
  unfold Row.δ₂PairZ
  have := δ₂DZ_pos row
  positivity

/-- The exact-value bridge: `Row.δ₂` is the unreduced integer fraction. -/
theorem _root_.Noperthedron.Solution.Row.δ₂PairZ_eq (row : Row) :
    Row.δ₂ row = (((row.δ₂PairZ).1 : ℤ) : ℚ) / (((row.δ₂PairZ).2 : ℤ) : ℚ) := by
  have hD := δ₂DZ_pos row
  have hDQ : (0 : ℚ) < ((δ₂DZ row : ℤ) : ℚ) := by exact_mod_cast hD
  unfold Row.δ₂ Row.δ₂PairZ
  rw [max'_image_fin3, boundDelta_bridge, boundDelta_bridge, boundDelta_bridge]
  rw [max_div_div_right hDQ.le, max_div_div_right hDQ.le]
  rw [show (κℚ : ℚ) = 1 / 10 ^ 10 from rfl]
  have hmax : ((max (δ₂BZ row 0) (max (δ₂BZ row 1) (δ₂BZ row 2)) : ℤ) : ℚ)
      = max ((δ₂BZ row 0 : ℤ) : ℚ) (max ((δ₂BZ row 1 : ℤ) : ℚ) ((δ₂BZ row 2 : ℤ) : ℚ)) := by
    push_cast
    rfl
  rw [← hmax]
  push_cast
  field_simp
  ring

end Noperthedron.Solution.Local2Nat

namespace Noperthedron.Solution

open Local2Nat in
/-- `Row.ValidLocal₂` decided with the δ₂ fraction substituted into the
`Bε₂ℚ` conjunct, so the kernel never evaluates the ℚ definition of
`Row.δ₂` (the offset tier then receives the unreduced fraction and pays a
single `Rat` normalization). -/
instance (priority := 10800) (row : Row) : Decidable (Row.ValidLocal₂ row) :=
  decidable_of_iff
    (row.nodeType = 2 ∧
      row.interval.centerPose ∈ fourInterval ℚ ∧
      (∃ s : TriangleSymmetry,
        s.applicable row.Qi ∧ ∀ i, row.Pi i = s.apply (row.Qi i)) ∧
      Local.TriangleQ.Aε₂ℚσ row.θ₁ row.φ₁ (pythonVertexA ∘ row.Pi)
        row.εθ₁ row.εφ₁ 0 ∧
      Local.TriangleQ.Aε₂ℚσ row.θ₂ row.φ₂ (pythonVertexA ∘ row.Qi)
        row.εθ₂ row.εφ₂ row.sigma_Q.val ∧
      Local.TriangleQ.Spanning₂ℚ row.θ₁ row.φ₁ (pythonVertexA ∘ row.Pi)
        row.εθ₁ row.εφ₁ ∧
      Local.TriangleQ.Spanning₂ℚ row.θ₂ row.φ₂ (pythonVertexA ∘ row.Qi)
        row.εθ₂ row.εφ₂ ∧
      0 < row.r ∧
      RationalApprox.LocalTheorem.BoundR₂ℚ row.r row.interval.centerPose
        (pythonVertexA ∘ row.Qi) row.εθ₂ row.εφ₂ RationalApprox.sqrtApprox16 ∧
      Local.TriangleQ.Bε₂ℚ row.Qi pythonVertexA row.interval.centerPose
        row.εθ₂ row.εφ₂ ((((row.δ₂PairZ).1 : ℤ) : ℚ) / (((row.δ₂PairZ).2 : ℤ) : ℚ))
        row.r RationalApprox.sqrtApprox16.upper_sqrt)
    (by rw [← Row.δ₂PairZ_eq row]; exact (Row.validLocal₂_iff row).symm)

end Noperthedron.Solution

end
