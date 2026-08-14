module

public import Noperthedron.RationalApprox.RationalGlobal

@[expose] public section


/-!
# All-`Nat` fast path for the global check

`Gℚ_gt_maxHℚ_fastNat` decides the same tiered test as `Gℚ_gt_maxHℚ_check`,
but one-sidedly (`Gℚ_gt_maxHℚ_fastNat_sound`: `true` implies the ℚ check;
`false` means "fall back to the exact checker") and with every hot-loop
operation a single kernel-accelerated `Nat` primitive, which makes it the
row check of choice for the kernel-only route (`decide +kernel` verifies a
global row ~18× faster than through the exact integer arithmetic it
replaced). The wiring into
`Row.G_gt_maxH` — including the concrete packed vertex table — lives in
`Checker/Global.lean`; this file is generic over the table.
-/

namespace RationalApprox.GlobalTheorem

/-! ## The checker

`Gℚ_gt_maxHℚ_fastNat` decides the same tiered test as `Gℚ_gt_maxHℚ_check`,
but one-sidedly (`true` implies the ℚ check; `false` means "fall back")
and with every per-vertex operation a single kernel-accelerated `Nat`
primitive:

* vertex coordinates come from a packed table literal (57-bit binary
  fields, offset-encoded `coord·10¹⁶ + 2⁵⁶`, 171 bits per vertex — see
  `Vertices/PythonNat.lean`), one shift + mask per vertex;
* the per-pose scalars are computed once, exactly, in fixed-scale `ℤ`
  (numerator `ediv` mirroring `round13`), then conservatively rounded to
  fixed power-of-10 scales — `g` down (`glo ≤ g·10¹³`), all the bound
  scalars up — so each tier comparison cross-multiplies into a pure-`Nat`
  inequality with *fixed* denominators instead of per-row `Rat.den`
  products;
* signed per-vertex dot products use offset algebra: with `â = a + 2⁴⁷`,
  `p̂ = p + 2⁵⁶` all `Nat`, `a·p = (Σâp̂ + 3·2¹⁰³) − (2⁵⁶Σâ + 2⁴⁷Σp̂)`, and
  the absolute values the tiers need are one comparison + subtraction;
* the loop is structural `Nat` recursion (no `Fintype`/`Finset.univ`
  walk).

Row-level guards (`0 < wd`, `0 ≤ ε` numerators, `0 < glo`, offset
nonnegativity) make the soundness direction unconditional; rows that fail
any guard or any tier return `false` and are re-decided by the exact
checker. -/

namespace Gℚ_gt_maxHℚ

/-- `|x − y|` on `ℕ` (one comparison + one subtraction). -/
@[inline] def natAbsDiff (x y : ℕ) : ℕ := if x ≤ y then y - x else x - y

/-- Ceiling division `⌈n/d⌉` (for `0 < d`). -/
@[inline] def cdiv (n d : ℤ) : ℤ := -(-n / d)

/-- Offset-nonnegativity guard for a scale-13 entry. -/
@[inline] def offOk (x : ℤ) : Bool := decide (0 ≤ x + 2 ^ 47)

/-- The per-vertex tier test on extracted (offset) vertex fields
`P0 P1 P2`. The tier-1 path — which decides all but the near-binding
vertices — is written directly in the kernel's accelerated `Nat` primitives
(`Nat.mul`/`Nat.add`/`Nat.ble`/`Nat.blt`/`Nat.sub`/`cond`), bypassing the
`HMul`/`Decidable` instance wrappers, which measurably halve kernel
throughput; the rare tier-2/3 fallbacks stay in ordinary notation. -/
def natTierBody (A0 A1 A2 fsA B0 B1 B2 fsB C0 C1 C2 fsC
    D0 D1 D2 fsD E0 E1 E2 fsE F0 F1 F2 fsF
    g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθ eφ q1 q2 q3 P0 P1 P2 : ℕ) : Bool :=
  let sp := Nat.add (Nat.add P0 P1) P2
  let gsp := Nat.mul (2 ^ 47) sp
  let s := Nat.add (Nat.add
      (cond (Nat.ble P0 (2 ^ 56)) (Nat.sub (2 ^ 56) P0) (Nat.sub P0 (2 ^ 56)))
      (cond (Nat.ble P1 (2 ^ 56)) (Nat.sub (2 ^ 56) P1) (Nat.sub P1 (2 ^ 56))))
      (cond (Nat.ble P2 (2 ^ 56)) (Nat.sub (2 ^ 56) P2) (Nat.sub P2 (2 ^ 56)))
  let XA := Nat.add (Nat.add (Nat.add (Nat.mul A0 P0) (Nat.mul A1 P1))
      (Nat.mul A2 P2)) (3 * 2 ^ 103)
  let CA := Nat.add fsA gsp
  (Nat.blt (Nat.add (Nat.add XA (Nat.mul fsBh s)) kR16) (Nat.add g16 CA)).or
    ((let bp := natAbsDiff (B0 * P0 + B1 * P1 + B2 * P2 + 3 * 2 ^ 103) (fsB + gsp)
      let cp := natAbsDiff (C0 * P0 + C1 * P1 + C2 * P2 + 3 * 2 ^ 103) (fsC + gsp)
      decide (XA * 10 ^ 13 + eθ * bp + eφ * cp + soB13 * s + kR29 < g29 + CA * 10 ^ 13)).or
      (let bp := natAbsDiff (B0 * P0 + B1 * P1 + B2 * P2 + 3 * 2 ^ 103) (fsB + gsp)
       let cp := natAbsDiff (C0 * P0 + C1 * P1 + C2 * P2 + 3 * 2 ^ 103) (fsC + gsp)
       let dp := natAbsDiff (D0 * P0 + D1 * P1 + D2 * P2 + 3 * 2 ^ 103) (fsD + gsp)
       let ep := natAbsDiff (E0 * P0 + E1 * P1 + E2 * P2 + 3 * 2 ^ 103) (fsE + gsp)
       let fp := natAbsDiff (F0 * P0 + F1 * P1 + F2 * P2 + 3 * 2 ^ 103) (fsF + gsp)
       decide (XA * (2 * 10 ^ 26) + (eθ * bp + eφ * cp) * (2 * 10 ^ 13)
           + q1 * dp + q2 * ep + q3 * fp + kR42 < g42 + CA * (2 * 10 ^ 26))))

/-- The all-`Nat` per-vertex loop: extract the three 57-bit offset fields of
flat vertex `j` from the packed table (one accelerated shift + mask each)
and run `natTierBody`; `j` counts down over flat vertex indices. -/
def natTierLoop (bigT A0 A1 A2 fsA B0 B1 B2 fsB C0 C1 C2 fsC
    D0 D1 D2 fsD E0 E1 E2 fsE F0 F1 F2 fsF
    g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθ eφ q1 q2 q3 : ℕ) : ℕ → Bool
  | 0 => true
  | j + 1 =>
    (let v := Nat.land (Nat.shiftRight bigT (Nat.mul 171 j)) (2 ^ 171 - 1)
     natTierBody A0 A1 A2 fsA B0 B1 B2 fsB C0 C1 C2 fsC
       D0 D1 D2 fsD E0 E1 E2 fsE F0 F1 F2 fsF
       g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθ eφ q1 q2 q3
       (Nat.land v (2 ^ 57 - 1)) (Nat.land (Nat.shiftRight v 57) (2 ^ 57 - 1))
       (Nat.shiftRight v 114)).and
    (natTierLoop bigT A0 A1 A2 fsA B0 B1 B2 fsB C0 C1 C2 fsC
      D0 D1 D2 fsD E0 E1 E2 fsE F0 F1 F2 fsF
      g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθ eφ q1 q2 q3 j)

/-! ### Soundness bridges for the fast path -/

/-- `natAbsDiff` casts to an integer absolute difference. -/
private lemma natAbsDiff_cast (x y : ℕ) : ((natAbsDiff x y : ℕ) : ℤ) = |(x : ℤ) - y| := by
  unfold natAbsDiff
  split
  · rename_i h
    rw [abs_sub_comm, abs_of_nonneg (by omega : (0:ℤ) ≤ (y:ℤ) - x)]
    omega
  · rename_i h
    rw [abs_of_nonneg (by omega : (0:ℤ) ≤ (x:ℤ) - y)]
    omega

/-- Scale-`10¹⁶` instance of `RationalApprox.abs_intCast_div_pow`. -/
private lemma abs_intCast_div16 (n : ℤ) :
    |(n : ℚ) / 10 ^ 16| = ((|n| : ℤ) : ℚ) / 10 ^ 16 :=
  RationalApprox.abs_intCast_div_pow 16 n

/-- `cdiv` bounds the exact quotient from above. -/
private lemma le_cdiv {n d : ℤ} (hd : (0:ℤ) < d) : (n : ℚ) / (d : ℚ) ≤ ((cdiv n d : ℤ) : ℚ) := by
  unfold cdiv
  have hdq : (0:ℚ) < (d : ℚ) := by exact_mod_cast hd
  rw [div_le_iff₀ hdq]
  have h1 : n ≤ -(-n / d) * d := by
    have h2 := Int.mul_ediv_add_emod (-n) d
    have h3 := Int.emod_nonneg (-n) (ne_of_gt hd)
    linarith
  exact_mod_cast h1

/-- Integer division bounds the exact quotient from below. -/
private lemma ediv_le {n d : ℤ} (hd : (0:ℤ) < d) : ((n / d : ℤ) : ℚ) ≤ (n : ℚ) / (d : ℚ) := by
  have hdq : (0:ℚ) < (d : ℚ) := by exact_mod_cast hd
  rw [le_div_iff₀ hdq]
  have h1 : n / d * d ≤ n := by
    have h2 := Int.mul_ediv_add_emod n d
    have h3 := Int.emod_nonneg n (ne_of_gt hd)
    linarith
  exact_mod_cast h1

/-- Cast an offset-encoded `natAbsDiff` dot product to the absolute value of
the underlying signed dot product (the offsets cancel). -/
private lemma natAbsDiff_offset_cast (x0 x1 x2 y0 y1 y2 : ℤ) (X0 X1 X2 Y0 Y1 Y2 : ℕ)
    (hX0 : (X0 : ℤ) = x0 + 2 ^ 47) (hX1 : (X1 : ℤ) = x1 + 2 ^ 47)
    (hX2 : (X2 : ℤ) = x2 + 2 ^ 47)
    (hY0 : (Y0 : ℤ) = y0 + 2 ^ 56) (hY1 : (Y1 : ℤ) = y1 + 2 ^ 56)
    (hY2 : (Y2 : ℤ) = y2 + 2 ^ 56) :
    ((natAbsDiff (X0 * Y0 + X1 * Y1 + X2 * Y2 + 3 * 2 ^ 103)
        (2 ^ 56 * (X0 + X1 + X2) + 2 ^ 47 * (Y0 + Y1 + Y2)) : ℕ) : ℤ)
      = |x0 * y0 + x1 * y1 + x2 * y2| := by
  rw [natAbsDiff_cast]
  congr 1
  push_cast
  rw [hX0, hX1, hX2, hY0, hY1, hY2]
  ring

/-- Sibling of `abs_intCast_div16` at the dot-product scale. -/
private lemma abs_intCast_div29 (n : ℤ) :
    |(n : ℚ) / 10 ^ 29| = ((|n| : ℤ) : ℚ) / 10 ^ 29 :=
  RationalApprox.abs_intCast_div_pow 29 n

/-- The crux of the fast path: a true `natTierBody` at one vertex implies the
ℚ tiered test at that vertex. Every argument enters through an equation or a
directional bound, so the caller controls the exact pipeline shapes. -/
private lemma natTierBody_sound
    {e : HScalars} {εθ εφ kt soB fsB kR g p0q p1q p2q : ℚ}
    {a0N a1N a2N b0N b1N b2N c0N c1N c2N d0N d1N d2N e0N e1N e2N f0N f1N f2N : ℤ}
    (ha0 : e.a0 = (a0N : ℚ) / 10 ^ 13) (ha1 : e.a1 = (a1N : ℚ) / 10 ^ 13)
    (ha2 : e.a2 = (a2N : ℚ) / 10 ^ 13)
    (hb0 : e.b0 = (b0N : ℚ) / 10 ^ 13) (hb1 : e.b1 = (b1N : ℚ) / 10 ^ 13)
    (hb2 : e.b2 = (b2N : ℚ) / 10 ^ 13)
    (hc0 : e.c0 = (c0N : ℚ) / 10 ^ 13) (hc1 : e.c1 = (c1N : ℚ) / 10 ^ 13)
    (hc2 : e.c2 = (c2N : ℚ) / 10 ^ 13)
    (hd0 : e.d0 = (d0N : ℚ) / 10 ^ 13) (hd1 : e.d1 = (d1N : ℚ) / 10 ^ 13)
    (hd2 : e.d2 = (d2N : ℚ) / 10 ^ 13)
    (he0 : e.e0 = (e0N : ℚ) / 10 ^ 13) (he1 : e.e1 = (e1N : ℚ) / 10 ^ 13)
    (he2 : e.e2 = (e2N : ℚ) / 10 ^ 13)
    (hf0 : e.f0 = (f0N : ℚ) / 10 ^ 13) (hf1 : e.f1 = (f1N : ℚ) / 10 ^ 13)
    (hf2 : e.f2 = (f2N : ℚ) / 10 ^ 13)
    {P0 P1 P2 : ℕ} {p0N p1N p2N : ℤ}
    (hP0 : (P0 : ℤ) = p0N + 2 ^ 56) (hP1 : (P1 : ℤ) = p1N + 2 ^ 56)
    (hP2 : (P2 : ℤ) = p2N + 2 ^ 56)
    (hp0 : p0q = (p0N : ℚ) / 10 ^ 16) (hp1 : p1q = (p1N : ℚ) / 10 ^ 16)
    (hp2 : p2q = (p2N : ℚ) / 10 ^ 16)
    {A0 A1 A2 B0 B1 B2 C0 C1 C2 D0 D1 D2 E0 E1 E2 F0 F1 F2 : ℕ}
    (hA0 : (A0 : ℤ) = a0N + 2 ^ 47) (hA1 : (A1 : ℤ) = a1N + 2 ^ 47)
    (hA2 : (A2 : ℤ) = a2N + 2 ^ 47)
    (hB0 : (B0 : ℤ) = b0N + 2 ^ 47) (hB1 : (B1 : ℤ) = b1N + 2 ^ 47)
    (hB2 : (B2 : ℤ) = b2N + 2 ^ 47)
    (hC0 : (C0 : ℤ) = c0N + 2 ^ 47) (hC1 : (C1 : ℤ) = c1N + 2 ^ 47)
    (hC2 : (C2 : ℤ) = c2N + 2 ^ 47)
    (hD0 : (D0 : ℤ) = d0N + 2 ^ 47) (hD1 : (D1 : ℤ) = d1N + 2 ^ 47)
    (hD2 : (D2 : ℤ) = d2N + 2 ^ 47)
    (hE0 : (E0 : ℤ) = e0N + 2 ^ 47) (hE1 : (E1 : ℤ) = e1N + 2 ^ 47)
    (hE2 : (E2 : ℤ) = e2N + 2 ^ 47)
    (hF0 : (F0 : ℤ) = f0N + 2 ^ 47) (hF1 : (F1 : ℤ) = f1N + 2 ^ 47)
    (hF2 : (F2 : ℤ) = f2N + 2 ^ 47)
    {glo kRhi fsHi soHi eθhi eφhi : ℤ}
    (hglo : ((glo : ℤ) : ℚ) / 10 ^ 13 ≤ g)
    (hkRq : kR = (εθ + εφ) ^ 3 / 6 + kt)
    (hkR : ((εθ + εφ) ^ 3 / 6 + kt) * 10 ^ 13 ≤ ((kRhi : ℤ) : ℚ))
    (hfs : fsB * 10 ^ 13 ≤ ((fsHi : ℤ) : ℚ))
    (hsoB : soB * 10 ^ 13 ≤ ((soHi : ℤ) : ℚ))
    (heθq : εθ * 10 ^ 13 ≤ ((eθhi : ℤ) : ℚ))
    (heφq : εφ * 10 ^ 13 ≤ ((eφhi : ℤ) : ℚ))
    (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    {fsA fsB' fsC fsD fsE fsF g16 g29 g42 fsBh soB13 kR16 kR29 kR42
     eθN eφN q1 q2 q3 : ℕ}
    (hfsA : fsA = 2 ^ 56 * (A0 + A1 + A2)) (hfsB : fsB' = 2 ^ 56 * (B0 + B1 + B2))
    (hfsC : fsC = 2 ^ 56 * (C0 + C1 + C2)) (hfsD : fsD = 2 ^ 56 * (D0 + D1 + D2))
    (hfsE : fsE = 2 ^ 56 * (E0 + E1 + E2)) (hfsF : fsF = 2 ^ 56 * (F0 + F1 + F2))
    (hg16 : (g16 : ℤ) = glo * 10 ^ 16) (hg29 : (g29 : ℤ) = glo * 10 ^ 29)
    (hg42 : (g42 : ℤ) = 2 * glo * 10 ^ 42)
    (hfsBh : (fsBh : ℤ) = fsHi) (hsoB13 : (soB13 : ℤ) = soHi * 10 ^ 13)
    (hkR16 : (kR16 : ℤ) = kRhi * 10 ^ 16) (hkR29 : (kR29 : ℤ) = kRhi * 10 ^ 29)
    (hkR42 : (kR42 : ℤ) = 2 * kRhi * 10 ^ 42)
    (heθN : (eθN : ℤ) = eθhi) (heφN : (eφN : ℤ) = eφhi)
    (hq1 : (q1 : ℤ) = eθhi ^ 2) (hq2 : (q2 : ℤ) = 2 * eθhi * eφhi)
    (hq3 : (q3 : ℤ) = eφhi ^ 2)
    (h : natTierBody A0 A1 A2 fsA B0 B1 B2 fsB' C0 C1 C2 fsC
      D0 D1 D2 fsD E0 E1 E2 fsE F0 F1 F2 fsF
      g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθN eφN q1 q2 q3 P0 P1 P2 = true) :
    tieredHs_lt e εθ εφ kt soB fsB kR g p0q p1q p2q = true := by
  subst hfsA hfsB hfsC hfsD hfsE hfsF
  unfold natTierBody at h
  simp only [Bool.or_eq_true, Nat.blt_eq, decide_eq_true_eq] at h
  unfold tieredHs_lt
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  -- shared ℚ-side facts
  have hSnn : (0:ℚ) ≤ |(p0N : ℚ)| + |(p1N : ℚ)| + |(p2N : ℚ)| := by positivity
  rcases h with h | h | h
  · -- tier 1 ⟹ the `cheapestHs` disjunct
    left; left
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
    zify at h
    rw [cond_ble_sub_cast, cond_ble_sub_cast, cond_ble_sub_cast,
      hg16, hkR16, hfsBh, hP0, hP1, hP2, hA0, hA1, hA2] at h
    push_cast at h
    simp only [add_sub_cancel_right] at h
    have key : a0N * p0N + a1N * p1N + a2N * p2N
        + fsHi * (|p0N| + |p1N| + |p2N|) + kRhi * 10 ^ 16 < glo * 10 ^ 16 := by
      linarith
    have keyQ : ((a0N * p0N + a1N * p1N + a2N * p2N
        + fsHi * (|p0N| + |p1N| + |p2N|) + kRhi * 10 ^ 16 : ℤ) : ℚ)
        < ((glo * 10 ^ 16 : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at keyQ
    have hb1 : fsB * 10 ^ 13 * (|(p0N : ℚ)| + |(p1N : ℚ)| + |(p2N : ℚ)|)
        ≤ (fsHi : ℚ) * (|(p0N : ℚ)| + |(p1N : ℚ)| + |(p2N : ℚ)|) :=
      mul_le_mul_of_nonneg_right hfs hSnn
    have hkR' : kR * 10 ^ 13 ≤ (kRhi : ℚ) := hkRq ▸ hkR
    unfold cheapestHs
    rw [ha0, ha1, ha2, hp0, hp1, hp2, abs_intCast_div16, abs_intCast_div16,
      abs_intCast_div16]
    push_cast
    linarith
  · -- tier 2 ⟹ the `cheapHs` disjunct
    left; right
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
    zify at h
    rw [cond_ble_sub_cast, cond_ble_sub_cast, cond_ble_sub_cast,
      natAbsDiff_offset_cast b0N b1N b2N p0N p1N p2N B0 B1 B2 P0 P1 P2
        hB0 hB1 hB2 hP0 hP1 hP2,
      natAbsDiff_offset_cast c0N c1N c2N p0N p1N p2N C0 C1 C2 P0 P1 P2
        hC0 hC1 hC2 hP0 hP1 hP2,
      hg29, hkR29, hsoB13, heθN, heφN, hP0, hP1, hP2, hA0, hA1, hA2] at h
    push_cast at h
    simp only [add_sub_cancel_right] at h
    have key : (a0N * p0N + a1N * p1N + a2N * p2N) * 10 ^ 13
        + eθhi * |b0N * p0N + b1N * p1N + b2N * p2N|
        + eφhi * |c0N * p0N + c1N * p1N + c2N * p2N|
        + soHi * 10 ^ 13 * (|p0N| + |p1N| + |p2N|)
        + kRhi * 10 ^ 29 < glo * 10 ^ 29 := by linarith
    have keyQ : (((a0N * p0N + a1N * p1N + a2N * p2N) * 10 ^ 13
        + eθhi * |b0N * p0N + b1N * p1N + b2N * p2N|
        + eφhi * |c0N * p0N + c1N * p1N + c2N * p2N|
        + soHi * 10 ^ 13 * (|p0N| + |p1N| + |p2N|)
        + kRhi * 10 ^ 29 : ℤ) : ℚ) < ((glo * 10 ^ 29 : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at keyQ
    have hbq : e.b0 * p0q + e.b1 * p1q + e.b2 * p2q
        = ((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ) / 10 ^ 29 := by
      rw [hb0, hb1, hb2, hp0, hp1, hp2]
      push_cast
      ring
    have hcq : e.c0 * p0q + e.c1 * p1q + e.c2 * p2q
        = ((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ) / 10 ^ 29 := by
      rw [hc0, hc1, hc2, hp0, hp1, hp2]
      push_cast
      ring
    have hbabs : |e.b0 * p0q + e.b1 * p1q + e.b2 * p2q|
        = |((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ)| / 10 ^ 29 := by
      rw [hbq, abs_intCast_div29]
      push_cast
      ring
    have hcabs : |e.c0 * p0q + e.c1 * p1q + e.c2 * p2q|
        = |((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ)| / 10 ^ 29 := by
      rw [hcq, abs_intCast_div29]
      push_cast
      ring
    have hbB : εθ * 10 ^ 13 * |((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ)|
        ≤ (eθhi : ℚ) * |((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ)| :=
      mul_le_mul_of_nonneg_right heθq (abs_nonneg _)
    have hcB : εφ * 10 ^ 13 * |((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ)|
        ≤ (eφhi : ℚ) * |((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ)| :=
      mul_le_mul_of_nonneg_right heφq (abs_nonneg _)
    have hsB : soB * 10 ^ 13 * (|(p0N : ℚ)| + |(p1N : ℚ)| + |(p2N : ℚ)|)
        ≤ (soHi : ℚ) * (|(p0N : ℚ)| + |(p1N : ℚ)| + |(p2N : ℚ)|) :=
      mul_le_mul_of_nonneg_right hsoB hSnn
    push_cast at hbB hcB hsB
    unfold cheapHs
    rw [ha0, ha1, ha2]
    rw [show (a0N : ℚ) / 10 ^ 13 * p0q + (a1N : ℚ) / 10 ^ 13 * p1q
        + (a2N : ℚ) / 10 ^ 13 * p2q
        + εθ * |e.b0 * p0q + e.b1 * p1q + e.b2 * p2q|
        + εφ * |e.c0 * p0q + e.c1 * p1q + e.c2 * p2q|
        + soB * (|p0q| + |p1q| + |p2q|) + (εθ + εφ) ^ 3 / 6 + kt
        = (a0N : ℚ) / 10 ^ 13 * p0q + (a1N : ℚ) / 10 ^ 13 * p1q
        + (a2N : ℚ) / 10 ^ 13 * p2q
        + εθ * |e.b0 * p0q + e.b1 * p1q + e.b2 * p2q|
        + εφ * |e.c0 * p0q + e.c1 * p1q + e.c2 * p2q|
        + soB * (|p0q| + |p1q| + |p2q|) + ((εθ + εφ) ^ 3 / 6 + kt) from by ring]
    rw [hbabs, hcabs, hp0, hp1, hp2, abs_intCast_div16, abs_intCast_div16,
      abs_intCast_div16]
    push_cast
    linarith
  · -- tier 3 ⟹ the exact `fastHs` disjunct
    right
    simp only [Nat.add_eq, Nat.mul_eq] at h
    zify at h
    rw [natAbsDiff_offset_cast b0N b1N b2N p0N p1N p2N B0 B1 B2 P0 P1 P2
        hB0 hB1 hB2 hP0 hP1 hP2,
      natAbsDiff_offset_cast c0N c1N c2N p0N p1N p2N C0 C1 C2 P0 P1 P2
        hC0 hC1 hC2 hP0 hP1 hP2,
      natAbsDiff_offset_cast d0N d1N d2N p0N p1N p2N D0 D1 D2 P0 P1 P2
        hD0 hD1 hD2 hP0 hP1 hP2,
      natAbsDiff_offset_cast e0N e1N e2N p0N p1N p2N E0 E1 E2 P0 P1 P2
        hE0 hE1 hE2 hP0 hP1 hP2,
      natAbsDiff_offset_cast f0N f1N f2N p0N p1N p2N F0 F1 F2 P0 P1 P2
        hF0 hF1 hF2 hP0 hP1 hP2,
      hg42, hkR42, hq1, hq2, hq3, heθN, heφN, hP0, hP1, hP2, hA0, hA1, hA2] at h
    push_cast at h
    have key : (a0N * p0N + a1N * p1N + a2N * p2N) * (2 * 10 ^ 26)
        + (eθhi * |b0N * p0N + b1N * p1N + b2N * p2N|
           + eφhi * |c0N * p0N + c1N * p1N + c2N * p2N|) * (2 * 10 ^ 13)
        + eθhi ^ 2 * |d0N * p0N + d1N * p1N + d2N * p2N|
        + 2 * eθhi * eφhi * |e0N * p0N + e1N * p1N + e2N * p2N|
        + eφhi ^ 2 * |f0N * p0N + f1N * p1N + f2N * p2N|
        + 2 * kRhi * 10 ^ 42 < 2 * glo * 10 ^ 42 := by linarith
    have keyQ : (((a0N * p0N + a1N * p1N + a2N * p2N) * (2 * 10 ^ 26)
        + (eθhi * |b0N * p0N + b1N * p1N + b2N * p2N|
           + eφhi * |c0N * p0N + c1N * p1N + c2N * p2N|) * (2 * 10 ^ 13)
        + eθhi ^ 2 * |d0N * p0N + d1N * p1N + d2N * p2N|
        + 2 * eθhi * eφhi * |e0N * p0N + e1N * p1N + e2N * p2N|
        + eφhi ^ 2 * |f0N * p0N + f1N * p1N + f2N * p2N|
        + 2 * kRhi * 10 ^ 42 : ℤ) : ℚ) < ((2 * glo * 10 ^ 42 : ℤ) : ℚ) := by
      exact_mod_cast key
    push_cast at keyQ
    have hbabs : |e.b0 * p0q + e.b1 * p1q + e.b2 * p2q|
        = |((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ)| / 10 ^ 29 := by
      rw [show e.b0 * p0q + e.b1 * p1q + e.b2 * p2q
          = ((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ) / 10 ^ 29 from by
        rw [hb0, hb1, hb2, hp0, hp1, hp2]; push_cast; ring]
      rw [abs_intCast_div29]
      push_cast
      ring
    have hcabs : |e.c0 * p0q + e.c1 * p1q + e.c2 * p2q|
        = |((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ)| / 10 ^ 29 := by
      rw [show e.c0 * p0q + e.c1 * p1q + e.c2 * p2q
          = ((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ) / 10 ^ 29 from by
        rw [hc0, hc1, hc2, hp0, hp1, hp2]; push_cast; ring]
      rw [abs_intCast_div29]
      push_cast
      ring
    have hdabs : |e.d0 * p0q + e.d1 * p1q + e.d2 * p2q|
        = |((d0N * p0N + d1N * p1N + d2N * p2N : ℤ) : ℚ)| / 10 ^ 29 := by
      rw [show e.d0 * p0q + e.d1 * p1q + e.d2 * p2q
          = ((d0N * p0N + d1N * p1N + d2N * p2N : ℤ) : ℚ) / 10 ^ 29 from by
        rw [hd0, hd1, hd2, hp0, hp1, hp2]; push_cast; ring]
      rw [abs_intCast_div29]
      push_cast
      ring
    have heabs : |e.e0 * p0q + e.e1 * p1q + e.e2 * p2q|
        = |((e0N * p0N + e1N * p1N + e2N * p2N : ℤ) : ℚ)| / 10 ^ 29 := by
      rw [show e.e0 * p0q + e.e1 * p1q + e.e2 * p2q
          = ((e0N * p0N + e1N * p1N + e2N * p2N : ℤ) : ℚ) / 10 ^ 29 from by
        rw [he0, he1, he2, hp0, hp1, hp2]; push_cast; ring]
      rw [abs_intCast_div29]
      push_cast
      ring
    have hfabs : |e.f0 * p0q + e.f1 * p1q + e.f2 * p2q|
        = |((f0N * p0N + f1N * p1N + f2N * p2N : ℤ) : ℚ)| / 10 ^ 29 := by
      rw [show e.f0 * p0q + e.f1 * p1q + e.f2 * p2q
          = ((f0N * p0N + f1N * p1N + f2N * p2N : ℤ) : ℚ) / 10 ^ 29 from by
        rw [hf0, hf1, hf2, hp0, hp1, hp2]; push_cast; ring]
      rw [abs_intCast_div29]
      push_cast
      ring
    have hbB : εθ * 10 ^ 13 * |((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ)|
        ≤ (eθhi : ℚ) * |((b0N * p0N + b1N * p1N + b2N * p2N : ℤ) : ℚ)| :=
      mul_le_mul_of_nonneg_right heθq (abs_nonneg _)
    have hcB : εφ * 10 ^ 13 * |((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ)|
        ≤ (eφhi : ℚ) * |((c0N * p0N + c1N * p1N + c2N * p2N : ℤ) : ℚ)| :=
      mul_le_mul_of_nonneg_right heφq (abs_nonneg _)
    have heθ13 : (0:ℚ) ≤ εθ * 10 ^ 13 := by positivity
    have heφ13 : (0:ℚ) ≤ εφ * 10 ^ 13 := by positivity
    have heθhi0 : (0:ℚ) ≤ (eθhi : ℚ) := le_trans heθ13 heθq
    have heφhi0 : (0:ℚ) ≤ (eφhi : ℚ) := le_trans heφ13 heφq
    have hdB : (εθ * 10 ^ 13) ^ 2 * |((d0N * p0N + d1N * p1N + d2N * p2N : ℤ) : ℚ)|
        ≤ (eθhi : ℚ) ^ 2 * |((d0N * p0N + d1N * p1N + d2N * p2N : ℤ) : ℚ)| :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ heθ13 heθq 2) (abs_nonneg _)
    have heB : (εθ * 10 ^ 13) * (εφ * 10 ^ 13)
          * |((e0N * p0N + e1N * p1N + e2N * p2N : ℤ) : ℚ)|
        ≤ (eθhi : ℚ) * (eφhi : ℚ) * |((e0N * p0N + e1N * p1N + e2N * p2N : ℤ) : ℚ)| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul heθq heφq heφ13 heθhi0) (abs_nonneg _)
    have hfB : (εφ * 10 ^ 13) ^ 2 * |((f0N * p0N + f1N * p1N + f2N * p2N : ℤ) : ℚ)|
        ≤ (eφhi : ℚ) ^ 2 * |((f0N * p0N + f1N * p1N + f2N * p2N : ℤ) : ℚ)| :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ heφ13 heφq 2) (abs_nonneg _)
    push_cast at hbB hcB hdB heB hfB
    unfold fastHs
    rw [ha0, ha1, ha2, hbabs, hcabs, hdabs, heabs, hfabs, hp0, hp1, hp2]
    push_cast
    linarith

/-- `round13` of an integer fraction over `10²⁶·wd` (H-entry scale). -/
private lemma round13_intCast_div26 (A : ℤ) (wd : ℕ) :
    RationalApprox.round13 ((A : ℚ) / (10 ^ 26 * (wd : ℚ)))
      = ((A / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  rw [show (10:ℚ) ^ 26 * (wd : ℚ) = 10 ^ 13 * ((10 ^ 13 * wd : ℕ) : ℚ) from by
        push_cast; ring,
    RationalApprox.round13_intCast_div,
    show ((10 ^ 13 * wd : ℕ) : ℤ) = 10 ^ 13 * (wd : ℤ) from by push_cast; ring]

/-- `round13` of an integer fraction over `10³⁹·wd` (G-entry scale). -/
private lemma round13_intCast_div39 (A : ℤ) (wd : ℕ) :
    RationalApprox.round13 ((A : ℚ) / (10 ^ 39 * (wd : ℚ)))
      = ((A / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  rw [show (10:ℚ) ^ 39 * (wd : ℚ) = 10 ^ 13 * ((10 ^ 26 * wd : ℕ) : ℚ) from by
        push_cast; ring,
    RationalApprox.round13_intCast_div,
    show ((10 ^ 26 * wd : ℕ) : ℤ) = 10 ^ 26 * (wd : ℤ) from by push_cast; ring]

/-- `cdiv` of a nonnegative numerator is nonnegative. -/
private lemma cdiv_nonneg {n d : ℤ} (hn : 0 ≤ n) (hd : (0:ℤ) < d) : 0 ≤ cdiv n d := by
  have h := le_cdiv (n := n) (d := d) hd
  have hq : (0:ℚ) ≤ (n : ℚ) / (d : ℚ) := by positivity
  exact_mod_cast le_trans hq h
section HEntryBridge

open RationalApprox (sinNum13 cosNum13)

variable {p : Pose ℚ} {w : Fin 2 → ℚ} {wxn wyn : ℤ} {wd : ℕ}

private lemma hentry_a0 (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.a0
      = (((-(sinNum13 p.θ₂ * wxn) * 10 ^ 13 - cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2tw 0
      = (((-(sinNum13 p.θ₂ * wxn) * 10 ^ 13 - cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero]
    simp only [hw0, hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2tw 0) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_a1 (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.a1
      = (((cosNum13 p.θ₂ * wxn * 10 ^ 13 - sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2tw 1
      = (((cosNum13 p.θ₂ * wxn * 10 ^ 13 - sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hw0, hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2tw 1) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_a2 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.a2
      = (((sinNum13 p.φ₂ * wyn * 10 ^ 13) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2tw 2
      = (((sinNum13 p.φ₂ * wyn * 10 ^ 13) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    simp only [hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2tw 2) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_b0 (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.b0
      = (((-(cosNum13 p.θ₂ * wxn) * 10 ^ 13 + sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2θtw 0
      = (((-(cosNum13 p.θ₂ * wxn) * 10 ^ 13 + sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero]
    simp only [hw0, hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2θtw 0) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_b1 (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.b1
      = (((-(sinNum13 p.θ₂ * wxn) * 10 ^ 13 - cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2θtw 1
      = (((-(sinNum13 p.θ₂ * wxn) * 10 ^ 13 - cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hw0, hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2θtw 1) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_c0 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.c0
      = (((cosNum13 p.θ₂ * sinNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2φtw 0
      = (((cosNum13 p.θ₂ * sinNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero]
    simp only [hw1]
    push_cast
    all_goals field_simp
  show RationalApprox.round13 ((hEntries p w).m2φtw 0) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_c1 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.c1
      = (((sinNum13 p.θ₂ * sinNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2φtw 1
      = (((sinNum13 p.θ₂ * sinNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hw1]
    push_cast
    all_goals field_simp
  show RationalApprox.round13 ((hEntries p w).m2φtw 1) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_c2 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.c2
      = (((cosNum13 p.φ₂ * wyn * 10 ^ 13) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2φtw 2
      = (((cosNum13 p.φ₂ * wyn * 10 ^ 13) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    simp only [hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2φtw 2) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_d0 (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.d0
      = (((-(-(sinNum13 p.θ₂ * wxn) * 10 ^ 13 - cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn)) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2θθtw 0
      = (((-(-(sinNum13 p.θ₂ * wxn) * 10 ^ 13 - cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn)) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero]
    simp only [hw0, hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2θθtw 0) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_d1 (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.d1
      = (((-(cosNum13 p.θ₂ * wxn) * 10 ^ 13 + sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2θθtw 1
      = (((-(cosNum13 p.θ₂ * wxn) * 10 ^ 13 + sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hw0, hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2θθtw 1) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_e0 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.e0
      = (((-(sinNum13 p.θ₂ * sinNum13 p.φ₂ * wyn)) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2θφtw 0
      = (((-(sinNum13 p.θ₂ * sinNum13 p.φ₂ * wyn)) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero]
    simp only [hw1]
    push_cast
    all_goals field_simp
  show RationalApprox.round13 ((hEntries p w).m2θφtw 0) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_e1 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.e1
      = (((cosNum13 p.θ₂ * sinNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2θφtw 1
      = (((cosNum13 p.θ₂ * sinNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hw1]
    push_cast
    all_goals field_simp
  show RationalApprox.round13 ((hEntries p w).m2θφtw 1) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_f0 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.f0
      = (((cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2φφtw 0
      = (((cosNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero]
    simp only [hw1]
    push_cast
    all_goals field_simp
  show RationalApprox.round13 ((hEntries p w).m2φφtw 0) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_f1 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.f1
      = (((sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2φφtw 1
      = (((sinNum13 p.θ₂ * cosNum13 p.φ₂ * wyn) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hw1]
    push_cast
    all_goals field_simp
  show RationalApprox.round13 ((hEntries p w).m2φφtw 1) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

private lemma hentry_f2 (hwd : 0 < wd)
    (_hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ)) :
    (hEntriesR p w).scalars.f2
      = (((-(sinNum13 p.φ₂ * wyn * 10 ^ 13)) / (10 ^ 13 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hstep : (hEntries p w).m2φφtw 2
      = (((-(sinNum13 p.φ₂ * wyn * 10 ^ 13)) : ℤ) : ℚ) / (10 ^ 26 * (wd : ℚ)) := by
    simp only [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    simp only [hw1]
    push_cast
    all_goals field_simp
    all_goals ring
  show RationalApprox.round13 ((hEntries p w).m2φφtw 2) = _
  rw [hstep]
  exact round13_intCast_div26 _ _

/-- The identically-zero component `b2` rounds to `0`. -/
private lemma hentry_b2 : (hEntriesR p w).scalars.b2 = ((0 : ℤ) : ℚ) / 10 ^ 13 := by
  show RationalApprox.round13 ((hEntries p w).m2θtw 2) = _
  rw [show (hEntries p w).m2θtw 2 = 0 from by
    simp [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
  unfold RationalApprox.round13
  norm_num

private lemma hentry_b2' : (hEntriesR p w).scalars.b2 = 0 := by
  rw [hentry_b2 (p := p) (w := w)]
  norm_num

/-- The identically-zero component `d2` rounds to `0`. -/
private lemma hentry_d2 : (hEntriesR p w).scalars.d2 = ((0 : ℤ) : ℚ) / 10 ^ 13 := by
  show RationalApprox.round13 ((hEntries p w).m2θθtw 2) = _
  rw [show (hEntries p w).m2θθtw 2 = 0 from by
    simp [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
  unfold RationalApprox.round13
  norm_num

private lemma hentry_d2' : (hEntriesR p w).scalars.d2 = 0 := by
  rw [hentry_d2 (p := p) (w := w)]
  norm_num

/-- The identically-zero component `e2` rounds to `0`. -/
private lemma hentry_e2 : (hEntriesR p w).scalars.e2 = ((0 : ℤ) : ℚ) / 10 ^ 13 := by
  show RationalApprox.round13 ((hEntries p w).m2θφtw 2) = _
  rw [show (hEntries p w).m2θφtw 2 = 0 from by
    simp [hEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
  unfold RationalApprox.round13
  norm_num

private lemma hentry_e2' : (hEntriesR p w).scalars.e2 = 0 := by
  rw [hentry_e2 (p := p) (w := w)]
  norm_num

end HEntryBridge

section GDotBridge

open RationalApprox (sinNum13 cosNum13)

variable {p : Pose ℚ} {w : Fin 2 → ℚ} {wxn wyn : ℤ} {wd : ℕ}
  {S : Fin 3 → ℚ} {s0 s1 s2 : ℤ}

private lemma gdot_R (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1RTw ⬝ᵥ S
      = (((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1RTw 0
      = (((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1RTw 0) = _
    rw [show (gEntries p w).m1RTw 0 = (((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1RTw 1
      = (((cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1RTw 1) = _
    rw [show (gEntries p w).m1RTw 1 = (((cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1RTw 2
      = (((sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1RTw 2) = _
    rw [show (gEntries p w).m1RTw 2 = (((sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_R' (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1R'Tw ⬝ᵥ S
      = (((-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1R'Tw 0
      = (((-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1R'Tw 0) = _
    rw [show (gEntries p w).m1R'Tw 0 = (((-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1R'Tw 1
      = (((cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1R'Tw 1) = _
    rw [show (gEntries p w).m1R'Tw 1 = (((cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1R'Tw 2
      = (((-(sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1R'Tw 2) = _
    rw [show (gEntries p w).m1R'Tw 2 = (((-(sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_θR (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1θRTw ⬝ᵥ S
      = (((-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1θRTw 0
      = (((-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θRTw 0) = _
    rw [show (gEntries p w).m1θRTw 0 = (((-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1θRTw 1
      = (((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θRTw 1) = _
    rw [show (gEntries p w).m1θRTw 1 = (((-(sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 - cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1θRTw 2 = 0 := by
    show RationalApprox.round13 ((gEntries p w).m1θRTw 2) = _
    rw [show (gEntries p w).m1θRTw 2 = 0 from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
    unfold RationalApprox.round13
    norm_num
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_φR (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1φRTw ⬝ᵥ S
      = (((cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1φRTw 0
      = (((cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φRTw 0) = _
    rw [show (gEntries p w).m1φRTw 0 = (((cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1φRTw 1
      = (((sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φRTw 1) = _
    rw [show (gEntries p w).m1φRTw 1 = (((sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1φRTw 2
      = (((cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φRTw 2) = _
    rw [show (gEntries p w).m1φRTw 2 = (((cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn) * 10 ^ 13) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_θR' (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1θR'Tw ⬝ᵥ S
      = (((-(cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1θR'Tw 0
      = (((-(cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θR'Tw 0) = _
    rw [show (gEntries p w).m1θR'Tw 0 = (((-(cosNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 - sinNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1θR'Tw 1
      = (((-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θR'Tw 1) = _
    rw [show (gEntries p w).m1θR'Tw 1 = (((-(sinNum13 p.θ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1θR'Tw 2 = 0 := by
    show RationalApprox.round13 ((gEntries p w).m1θR'Tw 2) = _
    rw [show (gEntries p w).m1θR'Tw 2 = 0 from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
    unfold RationalApprox.round13
    norm_num
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_φR' (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1φR'Tw ⬝ᵥ S
      = (((-(cosNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1φR'Tw 0
      = (((-(cosNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φR'Tw 0) = _
    rw [show (gEntries p w).m1φR'Tw 0 = (((-(cosNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1φR'Tw 1
      = (((-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φR'Tw 1) = _
    rw [show (gEntries p w).m1φR'Tw 1 = (((-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn))) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1φR'Tw 2
      = (((-(cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φR'Tw 2) = _
    rw [show (gEntries p w).m1φR'Tw 2 = (((-(cosNum13 p.φ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_θθR (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1θθRTw ⬝ᵥ S
      = (((sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1θθRTw 0
      = (((sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θθRTw 0) = _
    rw [show (gEntries p w).m1θθRTw 0 = (((sinNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn) * 10 ^ 13 + cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1θθRTw 1
      = (((-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θθRTw 1) = _
    rw [show (gEntries p w).m1θθRTw 1 = (((-(cosNum13 p.θ₁ * (cosNum13 p.α * wxn + sinNum13 p.α * wyn)) * 10 ^ 13 + sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1θθRTw 2 = 0 := by
    show RationalApprox.round13 ((gEntries p w).m1θθRTw 2) = _
    rw [show (gEntries p w).m1θθRTw 2 = 0 from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
    unfold RationalApprox.round13
    norm_num
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_θφR (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1θφRTw ⬝ᵥ S
      = (((-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) * s0 + (cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1θφRTw 0
      = (((-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn))) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θφRTw 0) = _
    rw [show (gEntries p w).m1θφRTw 0 = (((-(sinNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn))) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1θφRTw 1
      = (((cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1θφRTw 1) = _
    rw [show (gEntries p w).m1θφRTw 1 = (((cosNum13 p.θ₁ * sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1θφRTw 2 = 0 := by
    show RationalApprox.round13 ((gEntries p w).m1θφRTw 2) = _
    rw [show (gEntries p w).m1θφRTw 2 = 0 from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]]
    unfold RationalApprox.round13
    norm_num
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

private lemma gdot_φφR (hwd : 0 < wd)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (hS0 : S 0 = (s0 : ℚ) / 10 ^ 16) (hS1 : S 1 = (s1 : ℚ) / 10 ^ 16)
    (hS2 : S 2 = (s2 : ℚ) / 10 ^ 16) :
    (gEntriesR p w).m1φφRTw ⬝ᵥ S
      = (((cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s0 + (sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) * s1 + (-(sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) * s2 : ℤ) : ℚ) / 10 ^ 29 := by
  have hwdQ : ((wd : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hwd.ne'
  have hc0 : (gEntriesR p w).m1φφRTw 0
      = (((cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φφRTw 0) = _
    rw [show (gEntries p w).m1φφRTw 0 = (((cosNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp]
    exact round13_intCast_div39 _ _
  have hc1 : (gEntriesR p w).m1φφRTw 1
      = (((sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φφRTw 1) = _
    rw [show (gEntries p w).m1φφRTw 1 = (((sinNum13 p.θ₁ * cosNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp]
    exact round13_intCast_div39 _ _
  have hc2 : (gEntriesR p w).m1φφRTw 2
      = (((-(sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13) / (10 ^ 26 * (wd : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    show RationalApprox.round13 ((gEntries p w).m1φφRTw 2) = _
    rw [show (gEntries p w).m1φφRTw 2 = (((-(sinNum13 p.φ₁ * (-(sinNum13 p.α * wxn) + cosNum13 p.α * wyn)) * 10 ^ 13) : ℤ) : ℚ) / (10 ^ 39 * (wd : ℚ)) from by
      simp only [gEntries, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      simp only [hw0, hw1]
      push_cast
      all_goals field_simp
      all_goals ring]
    exact round13_intCast_div39 _ _
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hc2, hS0, hS1, hS2]
  push_cast
  ring

end GDotBridge

section GloBound

open RationalApprox (sinNum13 cosNum13)

variable {p : Pose ℚ} {w : Fin 2 → ℚ} {wxn wyn : ℤ} {wd : ℕ}
  {S : Fin 3 → ℚ} {s0 s1 s2 : ℤ} {εα εθ₁ εφ₁ : ℚ}

/-- One first-order subtracted term of `fastG`, bounded by its `cdiv`. -/
private lemma eps_term_le (ε : ℚ) (X : ℕ) :
    ε * (((X : ℤ) : ℚ) / 10 ^ 29)
      ≤ ((cdiv (ε.num * (X : ℤ)) ((ε.den : ℤ) * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13 := by
  have hd : (0:ℤ) < (ε.den : ℤ) * 10 ^ 16 := by positivity
  have hdQ : ((ε.den : ℚ)) ≠ 0 := by positivity
  calc ε * (((X : ℤ) : ℚ) / 10 ^ 29)
      = ((ε.num * (X : ℤ) : ℤ) : ℚ) / (((ε.den : ℤ) * 10 ^ 16 : ℤ) : ℚ) / 10 ^ 13 := by
        rw [show ε * (((X : ℤ) : ℚ) / 10 ^ 29)
            = (ε.num : ℚ) / (ε.den : ℚ) * (((X : ℤ) : ℚ) / 10 ^ 29) from by
          rw [Rat.num_div_den]]
        push_cast
        field_simp
        ring
    _ ≤ _ := by
        gcongr
        exact le_cdiv hd

/-- One diagonal second-order subtracted term of `fastG`. -/
private lemma eps_sq_term_le (ε : ℚ) (X : ℕ) :
    ε ^ 2 / 2 * (((X : ℤ) : ℚ) / 10 ^ 29)
      ≤ ((cdiv (ε.num ^ 2 * (X : ℤ)) (2 * (ε.den : ℤ) ^ 2 * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13 := by
  have hd : (0:ℤ) < 2 * (ε.den : ℤ) ^ 2 * 10 ^ 16 := by positivity
  have hdQ : ((ε.den : ℚ)) ≠ 0 := by positivity
  calc ε ^ 2 / 2 * (((X : ℤ) : ℚ) / 10 ^ 29)
      = ((ε.num ^ 2 * (X : ℤ) : ℤ) : ℚ) / ((2 * (ε.den : ℤ) ^ 2 * 10 ^ 16 : ℤ) : ℚ) / 10 ^ 13 := by
        rw [show ε ^ 2 / 2 * (((X : ℤ) : ℚ) / 10 ^ 29)
            = ((ε.num : ℚ) / (ε.den : ℚ)) ^ 2 / 2 * (((X : ℤ) : ℚ) / 10 ^ 29) from by
          rw [Rat.num_div_den]]
        push_cast
        field_simp
        ring
    _ ≤ _ := by
        gcongr
        exact le_cdiv hd

/-- One cross second-order subtracted term of `fastG`. -/
private lemma eps_mul_term_le (ε ε' : ℚ) (X : ℕ) :
    ε * ε' * (((X : ℤ) : ℚ) / 10 ^ 29)
      ≤ ((cdiv (ε.num * ε'.num * (X : ℤ)) ((ε.den : ℤ) * (ε'.den : ℤ) * 10 ^ 16) : ℤ) : ℚ)
        / 10 ^ 13 := by
  have hd : (0:ℤ) < (ε.den : ℤ) * (ε'.den : ℤ) * 10 ^ 16 := by positivity
  have hdQ : ((ε.den : ℚ)) ≠ 0 := by positivity
  have hdQ' : ((ε'.den : ℚ)) ≠ 0 := by positivity
  calc ε * ε' * (((X : ℤ) : ℚ) / 10 ^ 29)
      = ((ε.num * ε'.num * (X : ℤ) : ℤ) : ℚ)
          / (((ε.den : ℤ) * (ε'.den : ℤ) * 10 ^ 16 : ℤ) : ℚ) / 10 ^ 13 := by
        rw [show ε * ε' * (((X : ℤ) : ℚ) / 10 ^ 29)
            = ((ε.num : ℚ) / (ε.den : ℚ)) * ((ε'.num : ℚ) / (ε'.den : ℚ))
              * (((X : ℤ) : ℚ) / 10 ^ 29) from by
          rw [Rat.num_div_den, Rat.num_div_den]]
        push_cast
        field_simp
        ring
    _ ≤ _ := by
        gcongr
        exact le_cdiv hd

/-- The Lagrange-cube subtracted term of `fastG`. -/
private lemma cube_term_le :
    (εα + εθ₁ + εφ₁) ^ 3 / 6
      ≤ ((cdiv ((εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 3 * 10 ^ 13) (6 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 3) : ℤ) : ℚ) / 10 ^ 13 := by
  have hd : (0:ℤ) < 6 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 3 := by positivity
  have hdQ : ((εα.den : ℚ)) ≠ 0 := by positivity
  have hdQ' : ((εθ₁.den : ℚ)) ≠ 0 := by positivity
  have hdQ'' : ((εφ₁.den : ℚ)) ≠ 0 := by positivity
  calc (εα + εθ₁ + εφ₁) ^ 3 / 6
      = (((εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 3 * 10 ^ 13 : ℤ) : ℚ) / ((6 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 3 : ℤ) : ℚ) / 10 ^ 13 := by
        conv_lhs => rw [← Rat.num_div_den εα, ← Rat.num_div_den εθ₁, ← Rat.num_div_den εφ₁]
        push_cast
        field_simp
        ring
    _ ≤ _ := by
        gcongr
        exact le_cdiv hd

/-- The `κ`-slack subtracted term of `fastG`. -/
private lemma kappa_term_le :
    4 * RationalApprox.κℚ * (1 + (εα + εθ₁ + εφ₁) + (εα + εθ₁ + εφ₁) ^ 2 / 2)
      ≤ ((cdiv (4000 * (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2 + 2 * (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) + (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 2))
            (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2) : ℤ) : ℚ) / 10 ^ 13 := by
  have hd : (0:ℤ) < 2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2 := by positivity
  have hdQ : ((εα.den : ℚ)) ≠ 0 := by positivity
  have hdQ' : ((εθ₁.den : ℚ)) ≠ 0 := by positivity
  have hdQ'' : ((εφ₁.den : ℚ)) ≠ 0 := by positivity
  calc 4 * RationalApprox.κℚ * (1 + (εα + εθ₁ + εφ₁) + (εα + εθ₁ + εφ₁) ^ 2 / 2)
      = ((4000 * (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2 + 2 * (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) + (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 2) : ℤ) : ℚ)
          / ((2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2 : ℤ) : ℚ) / 10 ^ 13 := by
        rw [show RationalApprox.κℚ = 1 / 10 ^ 10 from rfl]
        conv_lhs => rw [← Rat.num_div_den εα, ← Rat.num_div_den εθ₁, ← Rat.num_div_den εφ₁]
        push_cast
        field_simp
        ring
    _ ≤ _ := by
        gcongr
        exact le_cdiv hd

/-- The conservative integer `glo` of the fast path bounds `fastG` from
below (scaled by `10¹³`). Stated over the nine dot numerators `dᵢN`; the
call site instantiates them with the `gdot_*` bridge lemmas, so the giant
numerator literals appear only once (inside those bridges). -/
private lemma glo_bound {d1N d2N d3N d4N d5N d6N d7N d8N d9N : ℤ}
    (hd1 : (gEntriesR p w).m1RTw ⬝ᵥ S = (d1N : ℚ) / 10 ^ 29)
    (hd2 : (gEntriesR p w).m1R'Tw ⬝ᵥ S = (d2N : ℚ) / 10 ^ 29)
    (hd3 : (gEntriesR p w).m1θRTw ⬝ᵥ S = (d3N : ℚ) / 10 ^ 29)
    (hd4 : (gEntriesR p w).m1φRTw ⬝ᵥ S = (d4N : ℚ) / 10 ^ 29)
    (hd5 : (gEntriesR p w).m1θR'Tw ⬝ᵥ S = (d5N : ℚ) / 10 ^ 29)
    (hd6 : (gEntriesR p w).m1φR'Tw ⬝ᵥ S = (d6N : ℚ) / 10 ^ 29)
    (hd7 : (gEntriesR p w).m1θθRTw ⬝ᵥ S = (d7N : ℚ) / 10 ^ 29)
    (hd8 : (gEntriesR p w).m1θφRTw ⬝ᵥ S = (d8N : ℚ) / 10 ^ 29)
    (hd9 : (gEntriesR p w).m1φφRTw ⬝ᵥ S = (d9N : ℚ) / 10 ^ 29) :
    ((d1N / 10 ^ 16
      - (cdiv (εα.num * (d2N.natAbs : ℤ)) ((εα.den : ℤ) * 10 ^ 16)
        + cdiv (εθ₁.num * (d3N.natAbs : ℤ)) ((εθ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εφ₁.num * (d4N.natAbs : ℤ)) ((εφ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εα.num ^ 2 * (d1N.natAbs : ℤ)) (2 * (εα.den : ℤ) ^ 2 * 10 ^ 16)
        + cdiv (εα.num * εθ₁.num * (d5N.natAbs : ℤ)) ((εα.den : ℤ) * (εθ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εα.num * εφ₁.num * (d6N.natAbs : ℤ)) ((εα.den : ℤ) * (εφ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εθ₁.num ^ 2 * (d7N.natAbs : ℤ)) (2 * (εθ₁.den : ℤ) ^ 2 * 10 ^ 16)
        + cdiv (εθ₁.num * εφ₁.num * (d8N.natAbs : ℤ)) ((εθ₁.den : ℤ) * (εφ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εφ₁.num ^ 2 * (d9N.natAbs : ℤ)) (2 * (εφ₁.den : ℤ) ^ 2 * 10 ^ 16)
        + cdiv ((εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 3 * 10 ^ 13) (6 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 3)
        + cdiv (4000 * (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2 + 2 * (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) + (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 2)) (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2)) : ℤ) : ℚ) / 10 ^ 13
      ≤ fastG (gEntriesR p w) εα εθ₁ εφ₁ S := by
  have hlead : ((d1N / 10 ^ 16 : ℤ) : ℚ) / 10 ^ 13 ≤ (d1N : ℚ) / 10 ^ 29 := by
    calc ((d1N / 10 ^ 16 : ℤ) : ℚ) / 10 ^ 13
        ≤ ((d1N : ℚ) / ((10 ^ 16 : ℤ) : ℚ)) / 10 ^ 13 := by
          gcongr
          exact ediv_le (by norm_num)
      _ = (d1N : ℚ) / 10 ^ 29 := by
          rw [div_div]
          norm_num
  have ht0 := eps_term_le εα d2N.natAbs
  have ht1 := eps_term_le εθ₁ d3N.natAbs
  have ht2 := eps_term_le εφ₁ d4N.natAbs
  have ht3 := eps_sq_term_le εα d1N.natAbs
  have ht4 := eps_mul_term_le εα εθ₁ d5N.natAbs
  have ht5 := eps_mul_term_le εα εφ₁ d6N.natAbs
  have ht6 := eps_sq_term_le εθ₁ d7N.natAbs
  have ht7 := eps_mul_term_le εθ₁ εφ₁ d8N.natAbs
  have ht8 := eps_sq_term_le εφ₁ d9N.natAbs
  have ht9 := cube_term_le (εα := εα) (εθ₁ := εθ₁) (εφ₁ := εφ₁)
  have ht10 := kappa_term_le (εα := εα) (εθ₁ := εθ₁) (εφ₁ := εφ₁)
  unfold fastG
  rw [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9]
  rw [abs_intCast_div29, abs_intCast_div29, abs_intCast_div29, abs_intCast_div29,
    abs_intCast_div29, abs_intCast_div29, abs_intCast_div29, abs_intCast_div29,
    abs_intCast_div29]
  simp only [Int.abs_eq_natAbs]
  rw [show ((d1N / 10 ^ 16
      - (cdiv (εα.num * (d2N.natAbs : ℤ)) ((εα.den : ℤ) * 10 ^ 16)
        + cdiv (εθ₁.num * (d3N.natAbs : ℤ)) ((εθ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εφ₁.num * (d4N.natAbs : ℤ)) ((εφ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εα.num ^ 2 * (d1N.natAbs : ℤ)) (2 * (εα.den : ℤ) ^ 2 * 10 ^ 16)
        + cdiv (εα.num * εθ₁.num * (d5N.natAbs : ℤ)) ((εα.den : ℤ) * (εθ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εα.num * εφ₁.num * (d6N.natAbs : ℤ)) ((εα.den : ℤ) * (εφ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εθ₁.num ^ 2 * (d7N.natAbs : ℤ)) (2 * (εθ₁.den : ℤ) ^ 2 * 10 ^ 16)
        + cdiv (εθ₁.num * εφ₁.num * (d8N.natAbs : ℤ)) ((εθ₁.den : ℤ) * (εφ₁.den : ℤ) * 10 ^ 16)
        + cdiv (εφ₁.num ^ 2 * (d9N.natAbs : ℤ)) (2 * (εφ₁.den : ℤ) ^ 2 * 10 ^ 16)
        + cdiv ((εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 3 * 10 ^ 13) (6 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 3)
        + cdiv (4000 * (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2 + 2 * (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) + (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 2)) (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2)) : ℤ) : ℚ) / 10 ^ 13
    = ((d1N / 10 ^ 16 : ℤ) : ℚ) / 10 ^ 13
      - (((cdiv (εα.num * (d2N.natAbs : ℤ)) ((εα.den : ℤ) * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13
        + ((cdiv (εθ₁.num * (d3N.natAbs : ℤ)) ((εθ₁.den : ℤ) * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13
        + ((cdiv (εφ₁.num * (d4N.natAbs : ℤ)) ((εφ₁.den : ℤ) * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13
        + ((cdiv (εα.num ^ 2 * (d1N.natAbs : ℤ)) (2 * (εα.den : ℤ) ^ 2 * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13
        + ((cdiv (εα.num * εθ₁.num * (d5N.natAbs : ℤ)) ((εα.den : ℤ) * (εθ₁.den : ℤ) * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13
        + ((cdiv (εα.num * εφ₁.num * (d6N.natAbs : ℤ)) ((εα.den : ℤ) * (εφ₁.den : ℤ) * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13
        + ((cdiv (εθ₁.num ^ 2 * (d7N.natAbs : ℤ)) (2 * (εθ₁.den : ℤ) ^ 2 * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13
        + ((cdiv (εθ₁.num * εφ₁.num * (d8N.natAbs : ℤ)) ((εθ₁.den : ℤ) * (εφ₁.den : ℤ) * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13
        + ((cdiv (εφ₁.num ^ 2 * (d9N.natAbs : ℤ)) (2 * (εφ₁.den : ℤ) ^ 2 * 10 ^ 16) : ℤ) : ℚ) / 10 ^ 13
        + ((cdiv ((εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 3 * 10 ^ 13) (6 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 3) : ℤ) : ℚ) / 10 ^ 13
        + ((cdiv (4000 * (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2 + 2 * (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) + (εα.num * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ)) + εθ₁.num * ((εα.den : ℤ) * (εφ₁.den : ℤ)) + εφ₁.num * ((εα.den : ℤ) * (εθ₁.den : ℤ))) ^ 2)) (2 * ((εα.den : ℤ) * ((εθ₁.den : ℤ) * (εφ₁.den : ℤ))) ^ 2) : ℤ) : ℚ) / 10 ^ 13) from by
    push_cast
    ring]
  linarith [hlead, ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10]

end GloBound

section HBounds

variable {εθ₂ εφ₂ : ℚ}

/-- `|·|` through a scale-`10¹³` integer fraction. -/
private lemma abs_intCast_div13 (n : ℤ) :
    |(n : ℚ) / 10 ^ 13| = ((|n| : ℤ) : ℚ) / 10 ^ 13 :=
  RationalApprox.abs_intCast_div_pow 13 n

/-- The pipeline `kRhi` bounds `(εθ₂+εφ₂)³/6 + kappaTerm` from above. -/
private lemma kR_bound :
    ((εθ₂ + εφ₂) ^ 3 / 6
        + 3 * RationalApprox.κℚ * (1 + (εθ₂ + εφ₂) + (εθ₂ + εφ₂) ^ 2 / 2)) * 10 ^ 13
      ≤ ((cdiv ((εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 3 * 10 ^ 13) (6 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 3)
          + cdiv (3000 * (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2 + 2 * (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) + (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 2))
              (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2) : ℤ) : ℚ) := by
  have hdQ : ((εθ₂.den : ℚ)) ≠ 0 := by positivity
  have hdQ' : ((εφ₂.den : ℚ)) ≠ 0 := by positivity
  have h1 : (εθ₂ + εφ₂) ^ 3 / 6 * 10 ^ 13
      ≤ ((cdiv ((εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 3 * 10 ^ 13) (6 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 3) : ℤ) : ℚ) := by
    calc (εθ₂ + εφ₂) ^ 3 / 6 * 10 ^ 13
        = (((εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 3 * 10 ^ 13 : ℤ) : ℚ) / ((6 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 3 : ℤ) : ℚ) := by
          conv_lhs => rw [← Rat.num_div_den εθ₂, ← Rat.num_div_den εφ₂]
          push_cast
          field_simp
          ring
      _ ≤ _ := le_cdiv (by positivity)
  have h2 : 3 * RationalApprox.κℚ * (1 + (εθ₂ + εφ₂) + (εθ₂ + εφ₂) ^ 2 / 2) * 10 ^ 13
      ≤ ((cdiv (3000 * (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2 + 2 * (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) + (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 2))
            (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2) : ℤ) : ℚ) := by
    calc 3 * RationalApprox.κℚ * (1 + (εθ₂ + εφ₂) + (εθ₂ + εφ₂) ^ 2 / 2) * 10 ^ 13
        = ((3000 * (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2 + 2 * (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) + (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 2) : ℤ) : ℚ)
            / ((2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2 : ℤ) : ℚ) := by
          rw [show RationalApprox.κℚ = 1 / 10 ^ 10 from rfl]
          conv_lhs => rw [← Rat.num_div_den εθ₂, ← Rat.num_div_den εφ₂]
          push_cast
          field_simp
          ring
      _ ≤ _ := le_cdiv (by positivity)
  push_cast
  linarith

/-- The pipeline `eθhi`/`eφhi` bound the radii from above. -/
private lemma eps13_bound (ε : ℚ) :
    ε * 10 ^ 13 ≤ ((cdiv (ε.num * 10 ^ 13) (ε.den : ℤ) : ℤ) : ℚ) := by
  have hdQ : ((ε.den : ℚ)) ≠ 0 := by positivity
  calc ε * 10 ^ 13 = ((ε.num * 10 ^ 13 : ℤ) : ℚ) / (((ε.den : ℤ) : ℤ) : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den ε]
        push_cast
        field_simp
        norm_num
    _ ≤ _ := le_cdiv (by exact_mod_cast ε.pos)

/-- The pipeline `soHi` bounds `soBound` from above, given the scale-`10¹³`
integer forms of the second-order scalars. -/
private lemma so_bound {e : HScalars} {d0 d1 e0 e1 f0 f1 f2 : ℤ}
    (hd0 : e.d0 = (d0 : ℚ) / 10 ^ 13) (hd1 : e.d1 = (d1 : ℚ) / 10 ^ 13)
    (hd2 : e.d2 = 0)
    (he0 : e.e0 = (e0 : ℚ) / 10 ^ 13) (he1 : e.e1 = (e1 : ℚ) / 10 ^ 13)
    (he2 : e.e2 = 0)
    (hf0 : e.f0 = (f0 : ℚ) / 10 ^ 13) (hf1 : e.f1 = (f1 : ℚ) / 10 ^ 13)
    (hf2 : e.f2 = (f2 : ℚ) / 10 ^ 13) :
    soBound e εθ₂ εφ₂ * 10 ^ 13
      ≤ ((cdiv (εθ₂.num ^ 2 * (max (d0.natAbs : ℤ) (d1.natAbs : ℤ)) * (εφ₂.den : ℤ) ^ 2
            + 2 * εθ₂.num * εφ₂.num * (max (e0.natAbs : ℤ) (e1.natAbs : ℤ)) * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ))
            + εφ₂.num ^ 2 * (max (f0.natAbs : ℤ) (max (f1.natAbs : ℤ) (f2.natAbs : ℤ)))
                * (εθ₂.den : ℤ) ^ 2)
          (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2) : ℤ) : ℚ) := by
  have hdQ : ((εθ₂.den : ℚ)) ≠ 0 := by positivity
  have hdQ' : ((εφ₂.den : ℚ)) ≠ 0 := by positivity
  have hmaxd : max |e.d0| (max |e.d1| |e.d2|)
      = ((max (d0.natAbs : ℤ) (d1.natAbs : ℤ) : ℤ) : ℚ) / 10 ^ 13 := by
    rw [hd0, hd1, hd2, abs_intCast_div13, abs_intCast_div13, abs_zero]
    rw [show max (((|d1| : ℤ) : ℚ) / 10 ^ 13) 0 = ((|d1| : ℤ) : ℚ) / 10 ^ 13 from
      max_eq_left (by positivity)]
    rw [max_div_div_right (by positivity : (0:ℚ) ≤ 10 ^ 13), ← Int.cast_max,
      Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  have hmaxe : max |e.e0| (max |e.e1| |e.e2|)
      = ((max (e0.natAbs : ℤ) (e1.natAbs : ℤ) : ℤ) : ℚ) / 10 ^ 13 := by
    rw [he0, he1, he2, abs_intCast_div13, abs_intCast_div13, abs_zero]
    rw [show max (((|e1| : ℤ) : ℚ) / 10 ^ 13) 0 = ((|e1| : ℤ) : ℚ) / 10 ^ 13 from
      max_eq_left (by positivity)]
    rw [max_div_div_right (by positivity : (0:ℚ) ≤ 10 ^ 13), ← Int.cast_max,
      Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  have hmaxf : max |e.f0| (max |e.f1| |e.f2|)
      = ((max (f0.natAbs : ℤ) (max (f1.natAbs : ℤ) (f2.natAbs : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    rw [hf0, hf1, hf2, abs_intCast_div13, abs_intCast_div13, abs_intCast_div13]
    rw [max_div_div_right (by positivity : (0:ℚ) ≤ 10 ^ 13),
      max_div_div_right (by positivity : (0:ℚ) ≤ 10 ^ 13), ← Int.cast_max, ← Int.cast_max,
      Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  unfold soBound
  rw [hmaxd, hmaxe, hmaxf]
  calc 1 / 2 * (εθ₂ ^ 2 * (((max (d0.natAbs : ℤ) (d1.natAbs : ℤ) : ℤ) : ℚ) / 10 ^ 13)
        + 2 * (εθ₂ * εφ₂) * (((max (e0.natAbs : ℤ) (e1.natAbs : ℤ) : ℤ) : ℚ) / 10 ^ 13)
        + εφ₂ ^ 2 * (((max (f0.natAbs : ℤ) (max (f1.natAbs : ℤ) (f2.natAbs : ℤ)) : ℤ) : ℚ)
            / 10 ^ 13)) * 10 ^ 13
      = ((εθ₂.num ^ 2 * (max (d0.natAbs : ℤ) (d1.natAbs : ℤ)) * (εφ₂.den : ℤ) ^ 2
            + 2 * εθ₂.num * εφ₂.num * (max (e0.natAbs : ℤ) (e1.natAbs : ℤ)) * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ))
            + εφ₂.num ^ 2 * (max (f0.natAbs : ℤ) (max (f1.natAbs : ℤ) (f2.natAbs : ℤ)))
                * (εθ₂.den : ℤ) ^ 2 : ℤ) : ℚ)
          / ((2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2 : ℤ) : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den εθ₂, ← Rat.num_div_den εφ₂]
        push_cast
        field_simp
    _ ≤ _ := le_cdiv (by positivity)

/-- The pipeline `foHi` summand bounds `foBound` from above. -/
private lemma fo_bound {e : HScalars} {b0 b1 c0 c1 c2 : ℤ}
    (hb0 : e.b0 = (b0 : ℚ) / 10 ^ 13) (hb1 : e.b1 = (b1 : ℚ) / 10 ^ 13)
    (hb2 : e.b2 = 0)
    (hc0 : e.c0 = (c0 : ℚ) / 10 ^ 13) (hc1 : e.c1 = (c1 : ℚ) / 10 ^ 13)
    (hc2 : e.c2 = (c2 : ℚ) / 10 ^ 13) :
    foBound e εθ₂ εφ₂ * 10 ^ 13
      ≤ ((cdiv (εθ₂.num * (max (b0.natAbs : ℤ) (b1.natAbs : ℤ)) * (εφ₂.den : ℤ)
            + εφ₂.num * (max (c0.natAbs : ℤ) (max (c1.natAbs : ℤ) (c2.natAbs : ℤ)))
                * (εθ₂.den : ℤ))
          ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) : ℤ) : ℚ) := by
  have hdQ : ((εθ₂.den : ℚ)) ≠ 0 := by positivity
  have hdQ' : ((εφ₂.den : ℚ)) ≠ 0 := by positivity
  have hmaxb : max |e.b0| (max |e.b1| |e.b2|)
      = ((max (b0.natAbs : ℤ) (b1.natAbs : ℤ) : ℤ) : ℚ) / 10 ^ 13 := by
    rw [hb0, hb1, hb2, abs_intCast_div13, abs_intCast_div13, abs_zero]
    rw [show max (((|b1| : ℤ) : ℚ) / 10 ^ 13) 0 = ((|b1| : ℤ) : ℚ) / 10 ^ 13 from
      max_eq_left (by positivity)]
    rw [max_div_div_right (by positivity : (0:ℚ) ≤ 10 ^ 13), ← Int.cast_max,
      Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  have hmaxc : max |e.c0| (max |e.c1| |e.c2|)
      = ((max (c0.natAbs : ℤ) (max (c1.natAbs : ℤ) (c2.natAbs : ℤ)) : ℤ) : ℚ) / 10 ^ 13 := by
    rw [hc0, hc1, hc2, abs_intCast_div13, abs_intCast_div13, abs_intCast_div13]
    rw [max_div_div_right (by positivity : (0:ℚ) ≤ 10 ^ 13),
      max_div_div_right (by positivity : (0:ℚ) ≤ 10 ^ 13), ← Int.cast_max, ← Int.cast_max,
      Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  unfold foBound
  rw [hmaxb, hmaxc]
  calc (εθ₂ * (((max (b0.natAbs : ℤ) (b1.natAbs : ℤ) : ℤ) : ℚ) / 10 ^ 13)
        + εφ₂ * (((max (c0.natAbs : ℤ) (max (c1.natAbs : ℤ) (c2.natAbs : ℤ)) : ℤ) : ℚ)
            / 10 ^ 13)) * 10 ^ 13
      = ((εθ₂.num * (max (b0.natAbs : ℤ) (b1.natAbs : ℤ)) * (εφ₂.den : ℤ)
            + εφ₂.num * (max (c0.natAbs : ℤ) (max (c1.natAbs : ℤ) (c2.natAbs : ℤ)))
                * (εθ₂.den : ℤ) : ℤ) : ℚ)
          / ((((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) : ℤ) : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den εθ₂, ← Rat.num_div_den εφ₂]
        push_cast
        field_simp
    _ ≤ _ := le_cdiv (by positivity)

end HBounds

/-- Unroll a true `natTierLoop` into per-vertex `natTierBody` facts. -/
private lemma natTierLoop_forall
    {bigT A0 A1 A2 fsA B0 B1 B2 fsB C0 C1 C2 fsC D0 D1 D2 fsD E0 E1 E2 fsE
     F0 F1 F2 fsF g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθ eφ q1 q2 q3 : ℕ} :
    ∀ {n : ℕ}, natTierLoop bigT A0 A1 A2 fsA B0 B1 B2 fsB C0 C1 C2 fsC
      D0 D1 D2 fsD E0 E1 E2 fsE F0 F1 F2 fsF
      g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθ eφ q1 q2 q3 n = true →
    ∀ j, j < n →
      (let v := Nat.land (Nat.shiftRight bigT (Nat.mul 171 j)) (2 ^ 171 - 1)
       natTierBody A0 A1 A2 fsA B0 B1 B2 fsB C0 C1 C2 fsC
         D0 D1 D2 fsD E0 E1 E2 fsE F0 F1 F2 fsF
         g16 g29 g42 fsBh soB13 kR16 kR29 kR42 eθ eφ q1 q2 q3
         (Nat.land v (2 ^ 57 - 1)) (Nat.land (Nat.shiftRight v 57) (2 ^ 57 - 1))
         (Nat.shiftRight v 114)) = true := by
  intro n
  induction n with
  | zero => exact fun _ j hj => absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    intro h j hj
    rw [natTierLoop, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
    · exact ih h.2 j h'
    · exact h.1

end Gℚ_gt_maxHℚ

open Gℚ_gt_maxHℚ in
/-- One-sided all-`Nat` fast path for `Gℚ_gt_maxHℚ_check` (see the section
docstring). `bigT` is the packed vertex table covering flat indices
`[0, nV)`, `sflat` the flat index of `S`, and `w = ![wxn/wd, wyn/wd]`. -/
def Gℚ_gt_maxHℚ_fastNat (bigT nV sflat : ℕ) (p : Pose ℚ)
    (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ) (wxn wyn : ℤ) (wd : ℕ) : Bool :=
  -- trig integer cores (scale 10¹³)
  let st2 := RationalApprox.sinNum13 p.θ₂
  let ct2 := RationalApprox.cosNum13 p.θ₂
  let sp2 := RationalApprox.sinNum13 p.φ₂
  let cp2 := RationalApprox.cosNum13 p.φ₂
  let st1 := RationalApprox.sinNum13 p.θ₁
  let ct1 := RationalApprox.cosNum13 p.θ₁
  let sp1 := RationalApprox.sinNum13 p.φ₁
  let cp1 := RationalApprox.cosNum13 p.φ₁
  let sa := RationalApprox.sinNum13 p.α
  let ca := RationalApprox.cosNum13 p.α
  let wdZ : ℤ := wd
  -- H-side entry numerators over 10²⁶·wd, rounded to scale 10¹³ (= hEntriesR)
  let dh : ℤ := 10 ^ 13 * wdZ
  let ctcp := ct2 * cp2
  let stcp := st2 * cp2
  let Aa0 := -(st2 * wxn) * 10 ^ 13 - ctcp * wyn
  let Aa1 := ct2 * wxn * 10 ^ 13 - stcp * wyn
  let Aa2 := sp2 * wyn * 10 ^ 13
  let Ab0 := -(ct2 * wxn) * 10 ^ 13 + stcp * wyn
  let Ac0 := ct2 * sp2 * wyn
  let Ac1 := st2 * sp2 * wyn
  let Ac2 := cp2 * wyn * 10 ^ 13
  let a0N := Aa0 / dh
  let a1N := Aa1 / dh
  let a2N := Aa2 / dh
  let b0N := Ab0 / dh
  let b1N := Aa0 / dh
  let c0N := Ac0 / dh
  let c1N := Ac1 / dh
  let c2N := Ac2 / dh
  let d0N := (-Aa0) / dh
  let d1N := Ab0 / dh
  let e0N := (-Ac1) / dh
  let e1N := Ac0 / dh
  let f0N := (ctcp * wyn) / dh
  let f1N := (stcp * wyn) / dh
  let f2N := (-Aa2) / dh
  -- G-side: Rᵀw / R'ᵀw at scale 10¹³·wd, entries over 10³⁹·wd → scale 10¹³
  let dg : ℤ := 10 ^ 26 * wdZ
  let u0 := ca * wxn + sa * wyn
  let u1 := -(sa * wxn) + ca * wyn
  let ctcp1 := ct1 * cp1
  let stcp1 := st1 * cp1
  let r0N := (-(st1 * u0) * 10 ^ 13 - ctcp1 * u1) / dg
  let r1N := (ct1 * u0 * 10 ^ 13 - stcp1 * u1) / dg
  let r2N := (sp1 * u1 * 10 ^ 13) / dg
  let s0N := (-(st1 * u1) * 10 ^ 13 + ctcp1 * u0) / dg
  let s1N := (ct1 * u1 * 10 ^ 13 + stcp1 * u0) / dg
  let s2N := (-(sp1 * u0) * 10 ^ 13) / dg
  let t0N := (-(ct1 * u0) * 10 ^ 13 + stcp1 * u1) / dg
  let t1N := (-(st1 * u0) * 10 ^ 13 - ctcp1 * u1) / dg
  let u0N' := (ct1 * sp1 * u1) / dg
  let u1N' := (st1 * sp1 * u1) / dg
  let u2N' := (cp1 * u1 * 10 ^ 13) / dg
  let v0N := (-(ct1 * u1) * 10 ^ 13 - stcp1 * u0) / dg
  let v1N := (-(st1 * u1) * 10 ^ 13 + ctcp1 * u0) / dg
  let w0N := (-(ct1 * sp1 * u0)) / dg
  let w1N := (-(st1 * sp1 * u0)) / dg
  let w2N := (-(cp1 * u0) * 10 ^ 13) / dg
  let x0N := (st1 * u0 * 10 ^ 13 + ctcp1 * u1) / dg
  let x1N := (-(ct1 * u0) * 10 ^ 13 + stcp1 * u1) / dg
  let y0N := (-(st1 * sp1 * u1)) / dg
  let y1N := (ct1 * sp1 * u1) / dg
  let z0N := (ctcp1 * u1) / dg
  let z1N := (stcp1 * u1) / dg
  let z2N := (-(sp1 * u1) * 10 ^ 13) / dg
  -- S coordinates (scale 10¹⁶) from the packed table
  let m57 : ℕ := 2 ^ 57 - 1
  let sv := (bigT >>> (171 * sflat)) &&& (2 ^ 171 - 1)
  let S0 : ℤ := ((sv &&& m57 : ℕ) : ℤ) - 2 ^ 56
  let S1 : ℤ := (((sv >>> 57) &&& m57 : ℕ) : ℤ) - 2 ^ 56
  let S2 : ℤ := ((sv >>> 114 : ℕ) : ℤ) - 2 ^ 56
  -- the nine G dots (scale 10²⁹)
  let dR := r0N * S0 + r1N * S1 + r2N * S2
  let dR' := (s0N * S0 + s1N * S1 + s2N * S2).natAbs
  let dθR := (t0N * S0 + t1N * S1).natAbs
  let dφR := (u0N' * S0 + u1N' * S1 + u2N' * S2).natAbs
  let dθR' := (v0N * S0 + v1N * S1).natAbs
  let dφR' := (w0N * S0 + w1N * S1 + w2N * S2).natAbs
  let dθθR := (x0N * S0 + x1N * S1).natAbs
  let dθφR := (y0N * S0 + y1N * S1).natAbs
  let dφφR := (z0N * S0 + z1N * S1 + z2N * S2).natAbs
  let dRabs : ℤ := dR.natAbs
  -- g lower bound at scale 10¹³: leading dot floored, every subtracted
  -- term ceiled
  let εαn := εα.num
  let εαd : ℤ := εα.den
  let εθ₁n := εθ₁.num
  let εθ₁d : ℤ := εθ₁.den
  let εφ₁n := εφ₁.num
  let εφ₁d : ℤ := εφ₁.den
  let En := εαn * (εθ₁d * εφ₁d) + εθ₁n * (εαd * εφ₁d) + εφ₁n * (εαd * εθ₁d)
  let Ed := εαd * (εθ₁d * εφ₁d)
  let glo := dR / 10 ^ 16
    - (cdiv (εαn * dR') (εαd * 10 ^ 16)
      + cdiv (εθ₁n * dθR) (εθ₁d * 10 ^ 16)
      + cdiv (εφ₁n * dφR) (εφ₁d * 10 ^ 16)
      + cdiv (εαn ^ 2 * dRabs) (2 * εαd ^ 2 * 10 ^ 16)
      + cdiv (εαn * εθ₁n * dθR') (εαd * εθ₁d * 10 ^ 16)
      + cdiv (εαn * εφ₁n * dφR') (εαd * εφ₁d * 10 ^ 16)
      + cdiv (εθ₁n ^ 2 * dθθR) (2 * εθ₁d ^ 2 * 10 ^ 16)
      + cdiv (εθ₁n * εφ₁n * dθφR) (εθ₁d * εφ₁d * 10 ^ 16)
      + cdiv (εφ₁n ^ 2 * dφφR) (2 * εφ₁d ^ 2 * 10 ^ 16)
      + cdiv (En ^ 3 * 10 ^ 13) (6 * Ed ^ 3)
      + cdiv (4000 * (2 * Ed ^ 2 + 2 * En * Ed + En ^ 2)) (2 * Ed ^ 2))
  -- H-side row constants, rounded up at scale 10¹³
  let εθ₂n := εθ₂.num
  let εθ₂d : ℤ := εθ₂.den
  let εφ₂n := εφ₂.num
  let εφ₂d : ℤ := εφ₂.den
  let E2n := εθ₂n * εφ₂d + εφ₂n * εθ₂d
  let E2d := εθ₂d * εφ₂d
  let kRhi := cdiv (E2n ^ 3 * 10 ^ 13) (6 * E2d ^ 3)
    + cdiv (3000 * (2 * E2d ^ 2 + 2 * E2n * E2d + E2n ^ 2)) (2 * E2d ^ 2)
  let maxbN : ℤ := max b0N.natAbs b1N.natAbs
  let maxcN : ℤ := max c0N.natAbs (max c1N.natAbs c2N.natAbs)
  let maxdN : ℤ := max d0N.natAbs d1N.natAbs
  let maxeN : ℤ := max e0N.natAbs e1N.natAbs
  let maxfN : ℤ := max f0N.natAbs (max f1N.natAbs f2N.natAbs)
  let soHi := cdiv (εθ₂n ^ 2 * maxdN * εφ₂d ^ 2 + 2 * εθ₂n * εφ₂n * maxeN * E2d
      + εφ₂n ^ 2 * maxfN * εθ₂d ^ 2) (2 * E2d ^ 2)
  let fsHi := soHi + cdiv (εθ₂n * maxbN * εφ₂d + εφ₂n * maxcN * εθ₂d) E2d
  let eθhi := cdiv (εθ₂n * 10 ^ 13) εθ₂d
  let eφhi := cdiv (εφ₂n * 10 ^ 13) εφ₂d
  -- guards, then the pure-Nat loop
  decide (0 < wd) && decide (0 ≤ εαn) && decide (0 ≤ εθ₁n) && decide (0 ≤ εφ₁n) &&
  decide (0 ≤ εθ₂n) && decide (0 ≤ εφ₂n) && decide (0 < glo) &&
  offOk a0N && offOk a1N && offOk a2N &&
  offOk b0N && offOk b1N &&
  offOk c0N && offOk c1N && offOk c2N &&
  offOk d0N && offOk d1N &&
  offOk e0N && offOk e1N &&
  offOk f0N && offOk f1N && offOk f2N &&
  (let A0 := (a0N + 2 ^ 47).toNat
   let A1 := (a1N + 2 ^ 47).toNat
   let A2 := (a2N + 2 ^ 47).toNat
   let B0 := (b0N + 2 ^ 47).toNat
   let B1 := (b1N + 2 ^ 47).toNat
   let B2 : ℕ := 2 ^ 47
   let C0 := (c0N + 2 ^ 47).toNat
   let C1 := (c1N + 2 ^ 47).toNat
   let C2 := (c2N + 2 ^ 47).toNat
   let D0 := (d0N + 2 ^ 47).toNat
   let D1 := (d1N + 2 ^ 47).toNat
   let D2 : ℕ := 2 ^ 47
   let E0 := (e0N + 2 ^ 47).toNat
   let E1 := (e1N + 2 ^ 47).toNat
   let E2 : ℕ := 2 ^ 47
   let F0 := (f0N + 2 ^ 47).toNat
   let F1 := (f1N + 2 ^ 47).toNat
   let F2 := (f2N + 2 ^ 47).toNat
   let gloN := glo.toNat
   let kRN := kRhi.toNat
   let fsBh := fsHi.toNat
   let soB13 := soHi.toNat * 10 ^ 13
   let eθN := eθhi.toNat
   let eφN := eφhi.toNat
   natTierLoop bigT A0 A1 A2 (2 ^ 56 * (A0 + A1 + A2))
     B0 B1 B2 (2 ^ 56 * (B0 + B1 + B2))
     C0 C1 C2 (2 ^ 56 * (C0 + C1 + C2))
     D0 D1 D2 (2 ^ 56 * (D0 + D1 + D2))
     E0 E1 E2 (2 ^ 56 * (E0 + E1 + E2))
     F0 F1 F2 (2 ^ 56 * (F0 + F1 + F2))
     (gloN * 10 ^ 16) (gloN * 10 ^ 29) (2 * gloN * 10 ^ 42)
     fsBh soB13 (kRN * 10 ^ 16) (kRN * 10 ^ 29) (2 * kRN * 10 ^ 42)
     eθN eφN (eθN ^ 2) (2 * eθN * eφN) (eφN ^ 2) nV)

open Gℚ_gt_maxHℚ in
/-- **Soundness of the all-`Nat` fast path**: if `Gℚ_gt_maxHℚ_fastNat` accepts,
the ℚ tiered check accepts. `bigT` is an arbitrary packed vertex table; the
`hfield`/`hS` hypotheses state (in exactly the shapes the fast path reads)
that its fields are the offset-encoded coordinates of `poly.v ∘ ix` and `S`,
and `hcover` that `ix` covers `ι` below `nV`. -/
theorem Gℚ_gt_maxHℚ_fastNat_sound {ι : Type} [Fintype ι] [DecidableEq ι]
    (bigT nV sflat : ℕ) (p : Pose ℚ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ)
    (wxn wyn : ℤ) (wd : ℕ)
    (S : Fin 3 → ℚ) (poly : Polyhedron ι (Fin 3 → ℚ)) (w : Fin 2 → ℚ)
    (hw0 : w 0 = (wxn : ℚ) / (wd : ℚ)) (hw1 : w 1 = (wyn : ℚ) / (wd : ℚ))
    (ix : ℕ → ι)
    (hcover : ∀ k : ι, ∃ j, j < nV ∧ ix j = k)
    (hfield : ∀ j, j < nV →
      (let v := Nat.land (Nat.shiftRight bigT (Nat.mul 171 j)) (2 ^ 171 - 1)
       ((Nat.land v (2 ^ 57 - 1) : ℕ) : ℚ) = poly.v (ix j) 0 * 10 ^ 16 + 2 ^ 56
        ∧ ((Nat.land (Nat.shiftRight v 57) (2 ^ 57 - 1) : ℕ) : ℚ)
            = poly.v (ix j) 1 * 10 ^ 16 + 2 ^ 56
        ∧ ((Nat.shiftRight v 114 : ℕ) : ℚ) = poly.v (ix j) 2 * 10 ^ 16 + 2 ^ 56))
    (hS0 : S 0 = (((((bigT >>> (171 * sflat)) &&& (2 ^ 171 - 1)) &&& (2 ^ 57 - 1) : ℕ) : ℤ)
        - 2 ^ 56 : ℤ) / 10 ^ 16)
    (hS1 : S 1 = ((((((bigT >>> (171 * sflat)) &&& (2 ^ 171 - 1)) >>> 57) &&& (2 ^ 57 - 1)
        : ℕ) : ℤ) - 2 ^ 56 : ℤ) / 10 ^ 16)
    (hS2 : S 2 = (((((bigT >>> (171 * sflat)) &&& (2 ^ 171 - 1)) >>> 114 : ℕ) : ℤ)
        - 2 ^ 56 : ℤ) / 10 ^ 16)
    (h : Gℚ_gt_maxHℚ_fastNat bigT nV sflat p εα εθ₁ εφ₁ εθ₂ εφ₂ wxn wyn wd = true) :
    Gℚ_gt_maxHℚ_check p εα εθ₁ εφ₁ εθ₂ εφ₂ S poly w = true := by
  unfold Gℚ_gt_maxHℚ_fastNat at h
  simp only [offOk, Bool.and_eq_true, and_assoc, decide_eq_true_eq] at h
  obtain ⟨hwd, hεαn, hεθ₁n, hεφ₁n, hεθ₂n, hεφ₂n, hglo0, hoa0, hoa1, hoa2,
    hob0, hob1, hoc0, hoc1, hoc2, hod0, hod1, hoe0, hoe1, hof0, hof1, hof2,
    hloop⟩ := h
  have hεα : 0 ≤ εα := Rat.num_nonneg.mp hεαn
  have hεθ₁' : 0 ≤ εθ₁ := Rat.num_nonneg.mp hεθ₁n
  have hεφ₁' : 0 ≤ εφ₁ := Rat.num_nonneg.mp hεφ₁n
  have hεθ₂' : 0 ≤ εθ₂ := Rat.num_nonneg.mp hεθ₂n
  have hεφ₂' : 0 ≤ εφ₂ := Rat.num_nonneg.mp hεφ₂n
  unfold Gℚ_gt_maxHℚ_check
  simp only [decide_eq_true_eq]
  intro k
  obtain ⟨j, hj, rfl⟩ := hcover k
  have hbody := natTierLoop_forall hloop j hj
  obtain ⟨hf0, hf1, hf2⟩ := hfield j hj
  have hwdQpos : 0 < wd := hwd
  -- vertex coordinate links
  have hp0 : poly.v (ix j) 0
      = (((((Nat.land (Nat.land (Nat.shiftRight bigT (Nat.mul 171 j)) (2 ^ 171 - 1)) (2 ^ 57 - 1) : ℕ) : ℤ) - 2 ^ 56 : ℤ) : ℚ)) / 10 ^ 16 := by
    push_cast at hf0 ⊢
    linarith
  have hp1 : poly.v (ix j) 1
      = (((((Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight bigT (Nat.mul 171 j)) (2 ^ 171 - 1)) 57) (2 ^ 57 - 1) : ℕ) : ℤ) - 2 ^ 56 : ℤ) : ℚ)) / 10 ^ 16 := by
    push_cast at hf1 ⊢
    linarith
  have hp2 : poly.v (ix j) 2
      = (((((Nat.shiftRight (Nat.land (Nat.shiftRight bigT (Nat.mul 171 j)) (2 ^ 171 - 1)) 114 : ℕ) : ℤ) - 2 ^ 56 : ℤ) : ℚ)) / 10 ^ 16 := by
    push_cast at hf2 ⊢
    linarith
  -- nonnegativity of the rounded-up row constants (for the `toNat` links)
  have hE2n : (0:ℤ) ≤ (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) :=
    add_nonneg (mul_nonneg hεθ₂n (by positivity)) (mul_nonneg hεφ₂n (by positivity))
  have hE2d : (0:ℤ) < (εθ₂.den : ℤ) * (εφ₂.den : ℤ) := by positivity
  have hkRhi0 : (0:ℤ) ≤ cdiv ((εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 3 * 10 ^ 13)
        (6 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 3)
      + cdiv (3000 * (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2
          + 2 * (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) + (εθ₂.num * (εφ₂.den : ℤ) + εφ₂.num * (εθ₂.den : ℤ)) ^ 2))
        (2 * ((εθ₂.den : ℤ) * (εφ₂.den : ℤ)) ^ 2) :=
    add_nonneg
      (cdiv_nonneg (mul_nonneg (pow_nonneg hE2n 3) (by norm_num)) (by positivity))
      (cdiv_nonneg
        (mul_nonneg (by norm_num)
          (add_nonneg (add_nonneg (by positivity)
            (mul_nonneg (mul_nonneg (by norm_num) hE2n) hE2d.le)) (pow_nonneg hE2n 2)))
        (by positivity))
  have heθhi0 : (0:ℤ) ≤ cdiv (εθ₂.num * 10 ^ 13) (εθ₂.den : ℤ) :=
    cdiv_nonneg (mul_nonneg hεθ₂n (by norm_num)) (by exact_mod_cast εθ₂.pos)
  have heφhi0 : (0:ℤ) ≤ cdiv (εφ₂.num * 10 ^ 13) (εφ₂.den : ℤ) :=
    cdiv_nonneg (mul_nonneg hεφ₂n (by norm_num)) (by exact_mod_cast εφ₂.pos)
  have ha0 := hentry_a0 (p := p) hwd hw0 hw1
  have ha1 := hentry_a1 (p := p) hwd hw0 hw1
  have ha2 := hentry_a2 (p := p) hwd hw0 hw1
  have hb0 := hentry_b0 (p := p) hwd hw0 hw1
  have hb1 := hentry_b1 (p := p) hwd hw0 hw1
  have hb2 := hentry_b2 (p := p) (w := w)
  have hc0 := hentry_c0 (p := p) hwd hw0 hw1
  have hc1 := hentry_c1 (p := p) hwd hw0 hw1
  have hc2 := hentry_c2 (p := p) hwd hw0 hw1
  have hd0 := hentry_d0 (p := p) hwd hw0 hw1
  have hd1 := hentry_d1 (p := p) hwd hw0 hw1
  have hd2 := hentry_d2 (p := p) (w := w)
  have he0 := hentry_e0 (p := p) hwd hw0 hw1
  have he1 := hentry_e1 (p := p) hwd hw0 hw1
  have he2 := hentry_e2 (p := p) (w := w)
  have hf0 := hentry_f0 (p := p) hwd hw0 hw1
  have hf1 := hentry_f1 (p := p) hwd hw0 hw1
  have hf2 := hentry_f2 (p := p) hwd hw0 hw1
  have hb2' := hentry_b2' (p := p) (w := w)
  have hd2' := hentry_d2' (p := p) (w := w)
  have he2' := hentry_e2' (p := p) (w := w)
  refine natTierBody_sound (b2N := 0) (d2N := 0) (e2N := 0)
    ha0 ha1 ha2 hb0 hb1 hb2 hc0 hc1 hc2 hd0 hd1 hd2 he0 he1 he2 hf0 hf1 hf2
    (by ring) (by ring) (by ring)
    hp0 hp1 hp2
    (Int.toNat_of_nonneg hoa0) (Int.toNat_of_nonneg hoa1) (Int.toNat_of_nonneg hoa2)
    (Int.toNat_of_nonneg hob0) (Int.toNat_of_nonneg hob1) ?hB2
    (Int.toNat_of_nonneg hoc0) (Int.toNat_of_nonneg hoc1) (Int.toNat_of_nonneg hoc2)
    (Int.toNat_of_nonneg hod0) (Int.toNat_of_nonneg hod1) ?hD2
    (Int.toNat_of_nonneg hoe0) (Int.toNat_of_nonneg hoe1) ?hE2
    (Int.toNat_of_nonneg hof0) (Int.toNat_of_nonneg hof1) (Int.toNat_of_nonneg hof2)
    (glo_bound
      (gdot_R (p := p) hwd hw0 hw1 hS0 hS1 hS2) (gdot_R' (p := p) hwd hw0 hw1 hS0 hS1 hS2)
      (gdot_θR (p := p) hwd hw0 hw1 hS0 hS1 hS2) (gdot_φR (p := p) hwd hw0 hw1 hS0 hS1 hS2)
      (gdot_θR' (p := p) hwd hw0 hw1 hS0 hS1 hS2) (gdot_φR' (p := p) hwd hw0 hw1 hS0 hS1 hS2)
      (gdot_θθR (p := p) hwd hw0 hw1 hS0 hS1 hS2) (gdot_θφR (p := p) hwd hw0 hw1 hS0 hS1 hS2)
      (gdot_φφR (p := p) hwd hw0 hw1 hS0 hS1 hS2))
    rfl (kR_bound (εθ₂ := εθ₂) (εφ₂ := εφ₂)) ?hfs
    (so_bound (εθ₂ := εθ₂) (εφ₂ := εφ₂) hd0 hd1 hd2' he0 he1 he2' hf0 hf1 hf2)
    (eps13_bound εθ₂) (eps13_bound εφ₂) hεθ₂' hεφ₂'
    rfl rfl rfl rfl rfl rfl
    ?hg16 ?hg29 ?hg42
    (Int.toNat_of_nonneg ?hfsHi0) ?hsoB13
    ?hkR16 ?hkR29 ?hkR42
    (Int.toNat_of_nonneg heθhi0) (Int.toNat_of_nonneg heφhi0)
    ?hq1 ?hq2 ?hq3
    hbody
  case hB2 => norm_num
  case hD2 => norm_num
  case hE2 => norm_num
  case hfs =>
    have h1 := fo_bound (εθ₂ := εθ₂) (εφ₂ := εφ₂) hb0 hb1 hb2' hc0 hc1 hc2
    have h2 := so_bound (εθ₂ := εθ₂) (εφ₂ := εφ₂) hd0 hd1 hd2' he0 he1 he2' hf0 hf1 hf2
    push_cast
    push_cast at h1 h2
    linarith
  case hfsHi0 =>
    refine add_nonneg ?_ ?_
    · exact cdiv_nonneg
        (add_nonneg
          (add_nonneg
            (mul_nonneg (mul_nonneg (pow_nonneg hεθ₂n 2)
              (le_max_iff.mpr (Or.inl (by positivity)))) (by positivity))
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hεθ₂n) hεφ₂n)
              (le_max_iff.mpr (Or.inl (by positivity)))) hE2d.le))
          (mul_nonneg (mul_nonneg (pow_nonneg hεφ₂n 2)
            (le_max_iff.mpr (Or.inl (by positivity)))) (by positivity)))
        (by positivity)
    · exact cdiv_nonneg
        (add_nonneg
          (mul_nonneg (mul_nonneg hεθ₂n (le_max_iff.mpr (Or.inl (by positivity))))
            (by positivity))
          (mul_nonneg (mul_nonneg hεφ₂n (le_max_iff.mpr (Or.inl (by positivity))))
            (by positivity)))
        hE2d
  case hsoB13 =>
    rw [Nat.cast_mul, Int.toNat_of_nonneg ?_]
    · push_cast
      ring
    · exact cdiv_nonneg
        (add_nonneg
          (add_nonneg
            (mul_nonneg (mul_nonneg (pow_nonneg hεθ₂n 2)
              (le_max_iff.mpr (Or.inl (by positivity)))) (by positivity))
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hεθ₂n) hεφ₂n)
              (le_max_iff.mpr (Or.inl (by positivity)))) hE2d.le))
          (mul_nonneg (mul_nonneg (pow_nonneg hεφ₂n 2)
            (le_max_iff.mpr (Or.inl (by positivity)))) (by positivity)))
        (by positivity)
  case hg16 =>
    rw [Nat.cast_mul, Int.toNat_of_nonneg hglo0.le]
    push_cast
    ring
  case hg29 =>
    rw [Nat.cast_mul, Int.toNat_of_nonneg hglo0.le]
    push_cast
    ring
  case hg42 =>
    rw [Nat.cast_mul, Nat.cast_mul, Int.toNat_of_nonneg hglo0.le]
    push_cast
    ring
  case hkR16 =>
    rw [Nat.cast_mul, Int.toNat_of_nonneg hkRhi0]
    push_cast
    ring
  case hkR29 =>
    rw [Nat.cast_mul, Int.toNat_of_nonneg hkRhi0]
    push_cast
    ring
  case hkR42 =>
    rw [Nat.cast_mul, Nat.cast_mul, Int.toNat_of_nonneg hkRhi0]
    push_cast
    ring
  case hq1 =>
    rw [Nat.cast_pow, Int.toNat_of_nonneg heθhi0]
  case hq2 =>
    rw [Nat.cast_mul, Nat.cast_mul, Int.toNat_of_nonneg heθhi0,
      Int.toNat_of_nonneg heφhi0]
    push_cast
    ring
  case hq3 =>
    rw [Nat.cast_pow, Int.toNat_of_nonneg heφhi0]
end RationalApprox.GlobalTheorem

end
