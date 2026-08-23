module

public import Noperthedron.Checker.Local2Nat
public import Noperthedron.Vertices.PythonNat
public import Noperthedron.Checker.SqrtDvNat

@[expose] public section

/-!
# Offset-encoded fast tier for `Row.ValidLocal₂` (kernel)

An all-`Nat` rendering of the `beFastN` pair body, kernel-measured at
~2.8× the speed of the `Int` tier (3.8s → 1.27s per second-order local
row; see `scripts/offset_pairbody_prototype.lean` for the validated
prototype and the measured-negative design alternatives).

Encoding: `App6N` fields carry offset `BF = 10⁴⁶`, family coefficients
offset `Bc = 10²⁸`, vertex coordinates come pre-offset by `2⁵⁶` from the
packed literal `pythonVertexBig`; pair norms are read from `sqrtDvBig`
(row pre-shifted once per corner). Per-corner constants are pos/neg
split, so each dot-product term is two `Nat.mul` (one by zero) and each
abs atom needs a single branch; squares are branchless via
`(d̂² + BF²) − 2·BF·d̂`. Newton square roots use factor-100 windowed
starts with fixed fuel (no per-step branch), and every `budN`
coefficient is nonnegative in the guarded regime, so the budget
polynomial is pure `Nat`.

`beFastO` guards its own regime (trig-numerator magnitudes and
`ε/δ/r` signs) so `beFastO_imp_beCheckN` needs no hypotheses; the
`Row.ValidLocal₂` instance tries it before `beFastN`/`beCheckN`.
-/

namespace Noperthedron.Solution.Local2Nat

open Noperthedron.NewtonSqrt (newtonSqrtUp)

/-! ## Windowed Newton upper bounds -/

/-- Factor-100 windows: the start is within 10× of the root, so fixed
fuel 5 (6 in the top window) converges; each start dominates the window's
square roots, so `newtonSqrtUp_ge_sqrt` applies per branch. -/
def nUpO (m : ℕ) : ℕ :=
  (if m ≤ 10 ^ 16 then
    if m ≤ 10 ^ 8 then
      if m ≤ 10 ^ 4 then
        if m ≤ 10 ^ 2 then newtonSqrtUp m 5 20 else newtonSqrtUp m 5 200
      else
        if m ≤ 10 ^ 6 then newtonSqrtUp m 5 (2 * 10 ^ 3)
        else newtonSqrtUp m 5 (2 * 10 ^ 4)
    else
      if m ≤ 10 ^ 12 then
        if m ≤ 10 ^ 10 then newtonSqrtUp m 5 (2 * 10 ^ 5)
        else newtonSqrtUp m 5 (2 * 10 ^ 6)
      else
        if m ≤ 10 ^ 14 then newtonSqrtUp m 5 (2 * 10 ^ 7)
        else newtonSqrtUp m 5 (2 * 10 ^ 8)
  else
    if m ≤ 10 ^ 24 then
      if m ≤ 10 ^ 20 then
        if m ≤ 10 ^ 18 then newtonSqrtUp m 5 (2 * 10 ^ 9)
        else newtonSqrtUp m 5 (2 * 10 ^ 10)
      else
        if m ≤ 10 ^ 22 then newtonSqrtUp m 5 (2 * 10 ^ 11)
        else newtonSqrtUp m 5 (2 * 10 ^ 12)
    else
      if m ≤ 10 ^ 30 then
        if m ≤ 10 ^ 26 then newtonSqrtUp m 5 (2 * 10 ^ 13)
        else if m ≤ 10 ^ 28 then newtonSqrtUp m 5 (2 * 10 ^ 14)
        else newtonSqrtUp m 5 (2 * 10 ^ 15)
      else
        if m ≤ 10 ^ 32 then newtonSqrtUp m 5 (2 * 10 ^ 16)
        else if m ≤ 10 ^ 34 then newtonSqrtUp m 6 (2 * 10 ^ 17)
        else Nat.sqrt m) + 1

lemma sqrt_succ_le_nUpO (m : ℕ) : Nat.sqrt m + 1 ≤ nUpO m := by
  unfold nUpO
  have sq : ∀ {s : ℕ}, m ≤ s * s → Nat.sqrt m ≤ s := fun {s} h =>
    le_trans (Nat.sqrt_le_sqrt h)
      (le_of_eq (by rw [show s * s = s ^ 2 from (sq s).symm]; exact Nat.sqrt_eq' s))
  refine Nat.succ_le_succ ?_
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 <;>
    first
      | exact le_refl _
      | exact Noperthedron.NewtonSqrt.newtonSqrtUp_ge_sqrt (by norm_num)
          (sq (by omega))

/-- `ceil(S / 10⁵²)` for the 84→32 scale drop (inputs are nonnegative). -/
def ceil52 (S : ℕ) : ℕ := if S = 0 then 0 else (S - 1) / 10 ^ 52 + 1

def nUpO84 (S : ℕ) : ℕ := nUpO (ceil52 S)

/-- The `ℤ`-facing wrapper, for the monotone bridge to `beCheckNCore`. -/
def nUpOZ84 (S : ℤ) : ℤ := if S ≤ 0 then 0 else (nUpO84 S.toNat : ℕ)

lemma nUpOZ84_nonneg (S : ℤ) : 0 ≤ nUpOZ84 S := by
  unfold nUpOZ84; split_ifs <;> positivity

lemma ceil52_eq (S : ℤ) (h : 0 < S) : (ceil52 S.toNat : ℤ) = -(-S / 10 ^ 52) := by
  unfold ceil52
  rw [if_neg (by omega)]
  omega

lemma sqrtNum84_le_nUpOZ84 (S : ℤ) : sqrtNum84 S ≤ nUpOZ84 S := by
  unfold sqrtNum84 nUpOZ84
  split_ifs with h
  · exact le_refl _
  · have hc := ceil52_eq S (by omega)
    have ht : (-(-S / 10 ^ 52)).toNat = ceil52 S.toNat := by omega
    rw [ht]
    exact_mod_cast sqrt_succ_le_nUpO _

/-! ## Offsets, packed reads, row constants -/

def BcO : ℕ := 10 ^ 28
def BFO : ℕ := 10 ^ 46
def M171 : ℕ := Nat.pow 2 171 - 1
def M57 : ℕ := Nat.pow 2 57 - 1
def M5130 : ℕ := Nat.pow 2 5130 - 1
def E74x18 : ℕ := 18 * Nat.pow 10 74
def E74x36 : ℕ := 36 * Nat.pow 10 74
def E74x9 : ℕ := 9 * Nat.pow 10 74
def E68x8 : ℕ := 8 * Nat.pow 10 68
def E6x2 : ℕ := 2 * Nat.pow 10 6
def E6x5 : ℕ := 5 * Nat.pow 10 6
def E6x3 : ℕ := 3 * Nat.pow 10 6
def E16 : ℕ := Nat.pow 10 16

/-- Flat vertex index (the packing order of the big literals). -/
def flatIx (a : VertexIndex) : ℕ := 45 * a.ℓ.val + 15 * a.i.val + a.k.val

/-- `budN` with all-`Nat` inputs and prefolded nonnegative coefficients. -/
def budO (k1 k2 k3 k4 k5 k6 a1 a2 a3 a4 a5 rem : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
    (Nat.mul k1 a1) (Nat.mul k2 a2)) (Nat.mul k3 a3)) (Nat.mul k4 a4))
    (Nat.mul k5 a5)) (Nat.mul k6 rem)

/-- Per-row constants: the nine field-coefficient slots offset by `BcO`,
per-field additive constants `K∗` (absorbing the offset corrections), the
prefolded `budN` coefficients, `W`, and the two comparison constants. -/
structure RCO where
  (ca0_0 ca0_1 ca1_0 ca1_1 ca1_2 : ℕ)
  (cb0_0 cb0_1 cb1_0 cb1_1 : ℕ)
  (cc1_0 cc1_1 cc1_2 : ℕ)
  (cd0_0 cd0_1 cd1_0 cd1_1 : ℕ)
  (ce1_0 ce1_1 : ℕ)
  (cf1_0 cf1_1 cf1_2 : ℕ)
  (Ka0 Ka1 Kb0 Kb1 Kc1 Kd0 Kd1 Ke1 Kf1 : ℕ)
  (k1 k2 k3 k4 k5 k6 W : ℕ)
  (cmpL cmpRc : ℕ)

/-- Offset applied family (9 nonzero fields; `c0/e0/f0` of `App6N` are
identically zero). -/
structure A6O where
  (a0 a1 b0 b1 c1 d0 d1 e1 f1 : ℕ)

/-- Applied family at flat vertex `j`, from the packed vertex literal. -/
def appO (rc : RCO) (j : ℕ) : A6O :=
  let v := Nat.land (Nat.shiftRight pythonVertexBig (Nat.mul 171 j)) M171
  let w0 := Nat.land v M57
  let w1 := Nat.land (Nat.shiftRight v 57) M57
  let w2 := Nat.shiftRight v 114
  let s2 := Nat.add w0 w1
  let s3 := Nat.add s2 w2
  { a0 := Nat.add (Nat.add (Nat.mul rc.ca0_0 w0) (Nat.mul rc.ca0_1 w1)) rc.Ka0
      - Nat.mul BcO s2,
    a1 := Nat.add (Nat.add (Nat.add (Nat.mul rc.ca1_0 w0) (Nat.mul rc.ca1_1 w1))
      (Nat.mul rc.ca1_2 w2)) rc.Ka1 - Nat.mul BcO s3,
    b0 := Nat.add (Nat.add (Nat.mul rc.cb0_0 w0) (Nat.mul rc.cb0_1 w1)) rc.Kb0
      - Nat.mul BcO s2,
    b1 := Nat.add (Nat.add (Nat.mul rc.cb1_0 w0) (Nat.mul rc.cb1_1 w1)) rc.Kb1
      - Nat.mul BcO s2,
    c1 := Nat.add (Nat.add (Nat.add (Nat.mul rc.cc1_0 w0) (Nat.mul rc.cc1_1 w1))
      (Nat.mul rc.cc1_2 w2)) rc.Kc1 - Nat.mul BcO s3,
    d0 := Nat.add (Nat.add (Nat.mul rc.cd0_0 w0) (Nat.mul rc.cd0_1 w1)) rc.Kd0
      - Nat.mul BcO s2,
    d1 := Nat.add (Nat.add (Nat.mul rc.cd1_0 w0) (Nat.mul rc.cd1_1 w1)) rc.Kd1
      - Nat.mul BcO s2,
    e1 := Nat.add (Nat.add (Nat.mul rc.ce1_0 w0) (Nat.mul rc.ce1_1 w1)) rc.Ke1
      - Nat.mul BcO s2,
    f1 := Nat.add (Nat.add (Nat.add (Nat.mul rc.cf1_0 w0) (Nat.mul rc.cf1_1 w1))
      (Nat.mul rc.cf1_2 w2)) rc.Kf1 - Nat.mul BcO s3 }

/-- `BFO²` and `2·BFO`, prefolded. -/
def BF2O : ℕ := Nat.mul BFO BFO
def BFO2x : ℕ := Nat.mul 2 BFO

/-- Branchless offset square: `(d̂ − BFO)²` for `d̂` within range. -/
def sqdO (dh : ℕ) : ℕ := Nat.add (Nat.mul dh dh) BF2O - Nat.mul BFO2x dh

/-- Offset square of a pos/neg split value. -/
def sqsO (pp nn : ℕ) : ℕ := Nat.mul (Nat.add pp nn) (Nat.add pp nn)

/-- Two-term dot accumulator (one side of the sign split). -/
def dotPO (q0 q1 d0 d1 x : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.mul q0 d0) (Nat.mul q1 d1)) x

/-- Two-term abs atom: `|q₀·d₀ + q₁·d₁| + slack` over offset/split data. -/
def atomA2 (qP0 qN0 qP1 qN1 d0 d1 xP xN slack : ℕ) : ℕ :=
  let p := Nat.add (Nat.add (Nat.mul qP0 d0) (Nat.mul qP1 d1)) xN
  let n := Nat.add (Nat.add (Nat.mul qN0 d0) (Nat.mul qN1 d1)) xP
  Nat.add (if n ≤ p then p - n else n - p) slack

/-- Three-term abs atom. -/
def atomA3 (qP0 qN0 qP1 qN1 qP2 qN2 d0 d1 d2 xP xN slack : ℕ) : ℕ :=
  let p := Nat.add (Nat.add (Nat.add (Nat.mul qP0 d0) (Nat.mul qP1 d1))
    (Nat.mul qP2 d2)) xN
  let n := Nat.add (Nat.add (Nat.add (Nat.mul qN0 d0) (Nat.mul qN1 d1))
    (Nat.mul qN2 d2)) xP
  Nat.add (if n ≤ p then p - n else n - p) slack

/-- Four-term abs atom. -/
def atomA4 (qP0 qN0 qP1 qN1 qP2 qN2 qP3 qN3 d0 d1 d2 d3 xP xN slack : ℕ) : ℕ :=
  let p := Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul qP0 d0) (Nat.mul qP1 d1))
    (Nat.mul qP2 d2)) (Nat.mul qP3 d3)) xN
  let n := Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul qN0 d0) (Nat.mul qN1 d1))
    (Nat.mul qN2 d2)) (Nat.mul qN3 d3)) xP
  Nat.add (if n ≤ p then p - n else n - p) slack

/-- Six-term abs atom. -/
def atomA6 (qP0 qN0 qP1 qN1 qP2 qN2 qP3 qN3 qP4 qN4 qP5 qN5
    d0 d1 d2 d3 d4 d5 xP xN slack : ℕ) : ℕ :=
  let p := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
    (Nat.mul qP0 d0) (Nat.mul qP1 d1)) (Nat.mul qP2 d2)) (Nat.mul qP3 d3))
    (Nat.mul qP4 d4)) (Nat.mul qP5 d5)) xN
  let n := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
    (Nat.mul qN0 d0) (Nat.mul qN1 d1)) (Nat.mul qN2 d2)) (Nat.mul qN3 d3))
    (Nat.mul qN4 d4)) (Nat.mul qN5 d5)) xP
  Nat.add (if n ≤ p then p - n else n - p) slack

/-- Per-corner data: the `Qi i` fields pos/neg split, `q̂ + BFO` for the
one-`Nat.sub` `dq`, the per-atom offset-correction constants, `D1N`, and
the pre-shifted pair-norm row. -/
structure QCO where
  (a0P a0N a1P a1N b0P b0N b1P b1N c1P c1N d0P d0N d1P d1N e1P e1N f1P f1N : ℕ)
  (pa0 pa1 pb0 pb1 pc1 pd0 pd1 pe1 pf1 : ℕ)
  (xmP xmN x1P x1N x2P x2N x3P x3N x4P x4N x5P x5N : ℕ)
  (D1N qrow : ℕ)

def qcO (rc : RCO) (jq : ℕ) : QCO :=
  let q := appO rc jq
  let a0P := q.a0 - BFO; let a0N := BFO - q.a0
  let a1P := q.a1 - BFO; let a1N := BFO - q.a1
  let b0P := q.b0 - BFO; let b0N := BFO - q.b0
  let b1P := q.b1 - BFO; let b1N := BFO - q.b1
  let c1P := q.c1 - BFO; let c1N := BFO - q.c1
  let d0P := q.d0 - BFO; let d0N := BFO - q.d0
  let d1P := q.d1 - BFO; let d1N := BFO - q.d1
  let e1P := q.e1 - BFO; let e1N := BFO - q.e1
  let f1P := q.f1 - BFO; let f1N := BFO - q.f1
  let D1N := Nat.add
    (Nat.mul rc.W (Nat.add (nUpO84 (Nat.add (sqsO a0P a0N) (sqsO a1P a1N))) E6x3))
    (budO rc.k1 rc.k2 rc.k3 rc.k4 rc.k5 rc.k6
      (Nat.add (nUpO84 (Nat.add (sqsO b0P b0N) (sqsO b1P b1N))) E6x3)
      (Nat.add (nUpO84 (sqsO c1P c1N)) E6x3)
      (Nat.add (nUpO84 (Nat.add (sqsO d0P d0N) (sqsO d1P d1N))) E6x3)
      (Nat.add (nUpO84 (sqsO e1P e1N)) E6x3)
      (Nat.add (nUpO84 (sqsO f1P f1N)) E6x3) E16)
  { a0P := a0P, a0N := a0N, a1P := a1P, a1N := a1N,
    b0P := b0P, b0N := b0N, b1P := b1P, b1N := b1N,
    c1P := c1P, c1N := c1N, d0P := d0P, d0N := d0N,
    d1P := d1P, d1N := d1N, e1P := e1P, e1N := e1N, f1P := f1P, f1N := f1N,
    pa0 := Nat.add q.a0 BFO, pa1 := Nat.add q.a1 BFO,
    pb0 := Nat.add q.b0 BFO, pb1 := Nat.add q.b1 BFO,
    pc1 := Nat.add q.c1 BFO, pd0 := Nat.add q.d0 BFO,
    pd1 := Nat.add q.d1 BFO, pe1 := Nat.add q.e1 BFO,
    pf1 := Nat.add q.f1 BFO,
    xmP := Nat.mul BFO (Nat.add a0P a1P), xmN := Nat.mul BFO (Nat.add a0N a1N),
    x1P := Nat.mul BFO (Nat.add (Nat.add (Nat.add b0P b1P) a0P) a1P),
    x1N := Nat.mul BFO (Nat.add (Nat.add (Nat.add b0N b1N) a0N) a1N),
    x2P := Nat.mul BFO (Nat.add c1P a1P), x2N := Nat.mul BFO (Nat.add c1N a1N),
    x3P := Nat.mul BFO (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add d0P d1P)
      (Nat.mul 2 b0P)) (Nat.mul 2 b1P)) a0P) a1P),
    x3N := Nat.mul BFO (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add d0N d1N)
      (Nat.mul 2 b0N)) (Nat.mul 2 b1N)) a0N) a1N),
    x4P := Nat.mul BFO (Nat.add (Nat.add (Nat.add e1P b1P) c1P) a1P),
    x4N := Nat.mul BFO (Nat.add (Nat.add (Nat.add e1N b1N) c1N) a1N),
    x5P := Nat.mul BFO (Nat.add (Nat.add f1P (Nat.mul 2 c1P)) a1P),
    x5N := Nat.mul BFO (Nat.add (Nat.add f1N (Nat.mul 2 c1N)) a1N),
    D1N := D1N,
    qrow := Nat.land (Nat.shiftRight sqrtDvBig (Nat.mul 5130 jq)) M5130 }

/-- The pair test over the per-pair offset differences and the norm read
(kept as plain arguments so the soundness proof works over variables). -/
def pairCore (rc : RCO) (qc : QCO)
    (da0 da1 db0 db1 dc1 dd0 dd1 de1 df1 nrmN : ℕ) : Bool :=
  let mdA := dotPO qc.a0P qc.a1P da0 da1 qc.xmN
  let mdB := dotPO qc.a0N qc.a1N da0 da1 qc.xmP
  let t1 := atomA4 qc.b0P qc.b0N qc.b1P qc.b1N qc.a0P qc.a0N qc.a1P qc.a1N
    da0 da1 db0 db1 qc.x1P qc.x1N E74x18
  let t2 := atomA2 qc.c1P qc.c1N qc.a1P qc.a1N da1 dc1 qc.x2P qc.x2N E74x18
  let t3 := atomA6 qc.d0P qc.d0N qc.d1P qc.d1N (Nat.mul 2 qc.b0P) (Nat.mul 2 qc.b0N)
    (Nat.mul 2 qc.b1P) (Nat.mul 2 qc.b1N) qc.a0P qc.a0N qc.a1P qc.a1N
    da0 da1 db0 db1 dd0 dd1 qc.x3P qc.x3N E74x36
  let t4 := atomA4 qc.e1P qc.e1N qc.b1P qc.b1N qc.c1P qc.c1N qc.a1P qc.a1N
    da1 dc1 db1 de1 qc.x4P qc.x4N E74x36
  let t5 := atomA3 qc.f1P qc.f1N (Nat.mul 2 qc.c1P) (Nat.mul 2 qc.c1N)
    qc.a1P qc.a1N da1 dc1 df1 qc.x5P qc.x5N E74x36
  let bud := budO rc.k1 rc.k2 rc.k3 rc.k4 rc.k5 rc.k6 t1 t2 t3 t4 t5
    (Nat.mul E68x8 nrmN)
  let D2N := Nat.add
    (Nat.mul rc.W (Nat.add (nUpO84 (Nat.add (sqdO da0) (sqdO da1))) E6x5))
    (budO rc.k1 rc.k2 rc.k3 rc.k4 rc.k5 rc.k6
      (Nat.add (nUpO84 (Nat.add (sqdO db0) (sqdO db1))) E6x5)
      (Nat.add (nUpO84 (sqdO dc1)) E6x5)
      (Nat.add (nUpO84 (Nat.add (sqdO dd0) (sqdO dd1))) E6x5)
      (Nat.add (nUpO84 (sqdO de1)) E6x5)
      (Nat.add (nUpO84 (sqdO df1)) E6x5) nrmN)
  let A := Nat.mul rc.W mdA
  let B := Nat.add (Nat.add (Nat.mul rc.W mdB) (Nat.mul rc.W E74x9)) bud
  decide (B < A) &&
    decide (Nat.add (Nat.mul rc.cmpL (Nat.mul qc.D1N D2N)) (Nat.mul B rc.cmpRc)
      < Nat.mul A rc.cmpRc)

/-- The all-`Nat` pair test at flat index `j`. -/
def pairO (rc : RCO) (qc : QCO) (j : ℕ) : Bool :=
  let v := appO rc j
  pairCore rc qc
    (qc.pa0 - v.a0) (qc.pa1 - v.a1) (qc.pb0 - v.b0) (qc.pb1 - v.b1)
    (qc.pc1 - v.c1) (qc.pd0 - v.d0) (qc.pd1 - v.d1) (qc.pe1 - v.e1)
    (qc.pf1 - v.f1)
    (Nat.add (Nat.land (Nat.shiftRight qc.qrow (Nat.mul 57 j)) M57) E6x2)

/-- Countdown pair loop over flat indices, skipping the corner itself. -/
def pairLoopO (rc : RCO) (qc : QCO) (qskip : ℕ) : ℕ → Bool
  | 0 => true
  | j + 1 => (Nat.beq j qskip || pairO rc qc j) && pairLoopO rc qc qskip j

/-- Coefficient offset. Exact (`= c + BcO` over `ℤ`) whenever `|c| ≤ BcO`. -/
def coO (c : ℤ) : ℕ := (c + (BcO : ℤ)).toNat

/-- Two-slot field constant; over `ℤ` it is `BFO − 2⁵⁶·(c1 + c2)`. -/
def K2O (c1 c2 : ℤ) : ℕ :=
  ((BFO : ℤ) + 2 * (BcO : ℤ) * 2 ^ 56
    - 2 ^ 56 * ((c1 + BcO) + (c2 + BcO))).toNat

/-- Three-slot field constant; over `ℤ` it is `BFO − 2⁵⁶·(c1 + c2 + c3)`. -/
def K3O (c1 c2 c3 : ℤ) : ℕ :=
  ((BFO : ℤ) + 3 * (BcO : ℤ) * 2 ^ 56
    - 2 ^ 56 * ((c1 + BcO) + (c2 + BcO) + (c3 + BcO))).toNat

/-- Row constants from the trig numerators and `ε/δ/r` (evaluated once per
row; all `Int.toNat`s are exact under `beFastO`'s guards). -/
def mkRCO (stN ctN sfN cfN : ℤ) (εθ εφ δ r : ℚ) : RCO :=
  let st13 := stN * 10 ^ 13
  let ct13 := ctN * 10 ^ 13
  let sf13 := sfN * 10 ^ 13
  let cf13 := cfN * 10 ^ 13
  let ctcf := ctN * cfN
  let stcf := stN * cfN
  let ctsf := ctN * sfN
  let stsf := stN * sfN
  let co := coO
  let K2 := K2O
  let K3 := K3O
  let en := εθ.num
  let ed : ℤ := εθ.den
  let fn := εφ.num
  let fd : ℤ := εφ.den
  let W : ℤ := 6 * (ed * fd) ^ 3
  { ca0_0 := co (-st13), ca0_1 := co ct13,
    ca1_0 := co (-ctcf), ca1_1 := co (-stcf), ca1_2 := co sf13,
    cb0_0 := co (-ct13), cb0_1 := co (-st13),
    cb1_0 := co stcf, cb1_1 := co (-ctcf),
    cc1_0 := co ctsf, cc1_1 := co stsf, cc1_2 := co cf13,
    cd0_0 := co st13, cd0_1 := co (-ct13),
    cd1_0 := co ctcf, cd1_1 := co stcf,
    ce1_0 := co (-stsf), ce1_1 := co ctsf,
    cf1_0 := co ctcf, cf1_1 := co stcf, cf1_2 := co (-sf13),
    Ka0 := K2 (-st13) ct13, Ka1 := K3 (-ctcf) (-stcf) sf13,
    Kb0 := K2 (-ct13) (-st13), Kb1 := K2 stcf (-ctcf),
    Kc1 := K3 ctsf stsf cf13,
    Kd0 := K2 st13 (-ct13), Kd1 := K2 ctcf stcf,
    Ke1 := K2 (-stsf) ctsf,
    Kf1 := K3 ctcf stcf (-sf13),
    k1 := (6 * en * ed ^ 2 * fd ^ 3).toNat, k2 := (6 * fn * fd ^ 2 * ed ^ 3).toNat,
    k3 := (3 * en ^ 2 * ed * fd ^ 3).toNat, k4 := (6 * en * fn * ed ^ 2 * fd ^ 2).toNat,
    k5 := (3 * fn ^ 2 * fd * ed ^ 3).toNat, k6 := ((en * fd + fn * ed) ^ 3).toNat,
    W := W.toNat,
    cmpL := (δ.num * r.den * 10 ^ 52).toNat,
    cmpRc := (W * (δ.den * r.num)).toNat }

/-- The offset fast tier: regime guards (trig-numerator magnitudes and
`ε/δ/r` signs), then the three per-corner pair loops. One-sided:
`beFastO_imp_beCheckN`. -/
def beFastO (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (εθ εφ δ r : ℚ) : Bool :=
  let stN := RationalApprox.sinNum13 p.θ₂
  let ctN := RationalApprox.cosNum13 p.θ₂
  let sfN := RationalApprox.sinNum13 p.φ₂
  let cfN := RationalApprox.cosNum13 p.φ₂
  decide (stN.natAbs ≤ 10 ^ 14) && decide (ctN.natAbs ≤ 10 ^ 14) &&
  decide (sfN.natAbs ≤ 10 ^ 14) && decide (cfN.natAbs ≤ 10 ^ 14) &&
  decide (0 ≤ εθ.num) && decide (0 ≤ εφ.num) &&
  decide (0 ≤ δ.num) && decide (0 < r.num) &&
  (let rc := mkRCO stN ctN sfN cfN εθ εφ δ r
   (List.finRange 3).all fun i =>
     let jq := flatIx (Qi i)
     pairLoopO rc (qcO rc jq) jq 90)

/-- `pairLoopO` gives every flat index below its fuel (except the skip). -/
lemma pairLoopO_forall {rc : RCO} {qc : QCO} {qskip : ℕ} :
    ∀ {n : ℕ}, pairLoopO rc qc qskip n = true →
      ∀ j, j < n → j ≠ qskip → pairO rc qc j = true := by
  intro n
  induction n with
  | zero => exact fun _ j hj => absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    intro h j hj hne
    rw [pairLoopO, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
    · exact ih h.2 j h' hne
    · rcases h.1 with h1 | h1
      · exact absurd (Nat.eq_of_beq_eq_true h1) hne
      · exact h1

/-! ## Soundness: value bridges -/

section OffsetSound

/-- Truncated-subtraction cast: exact when the `ℤ` value is nonnegative. -/
private lemma natSub_cast {a b : ℕ} {v : ℤ} (h : (a : ℤ) - b = v) (hv : 0 ≤ v) :
    ((a - b : ℕ) : ℤ) = v := by omega

/-- The one-branch abs: `(if b ≤ a then a − b else b − a : ℕ)` casts to
`|a − b|` over `ℤ`. -/
private lemma absSub_cast (a b : ℕ) :
    ((if b ≤ a then a - b else b - a : ℕ) : ℤ) = |(a : ℤ) - b| := by
  split_ifs with h <;> [skip; rw [abs_sub_comm]] <;> rw [abs_of_nonneg (by omega)] <;> omega

/-- `coO` is exact on coefficients within the offset. -/
private lemma coO_cast {c : ℤ} (h : |c| ≤ (BcO : ℤ)) : ((coO c : ℕ) : ℤ) = c + BcO := by
  unfold coO
  rw [Int.toNat_of_nonneg (by have := abs_le.mp h; omega)]

private lemma K2O_cast {c1 c2 : ℤ} (h1 : |c1| ≤ (BcO : ℤ)) (h2 : |c2| ≤ (BcO : ℤ)) :
    ((K2O c1 c2 : ℕ) : ℤ) = BFO - 2 ^ 56 * (c1 + c2) := by
  unfold K2O
  rw [Int.toNat_of_nonneg]
  · ring
  · have b1 := abs_le.mp h1
    have b2 := abs_le.mp h2
    have : (BcO : ℤ) = 10 ^ 28 := by norm_num [BcO]
    have : (BFO : ℤ) = 10 ^ 46 := by norm_num [BFO]
    nlinarith

private lemma K3O_cast {c1 c2 c3 : ℤ} (h1 : |c1| ≤ (BcO : ℤ)) (h2 : |c2| ≤ (BcO : ℤ))
    (h3 : |c3| ≤ (BcO : ℤ)) :
    ((K3O c1 c2 c3 : ℕ) : ℤ) = BFO - 2 ^ 56 * (c1 + c2 + c3) := by
  unfold K3O
  rw [Int.toNat_of_nonneg]
  · ring
  · have b1 := abs_le.mp h1
    have b2 := abs_le.mp h2
    have b3 := abs_le.mp h3
    have : (BcO : ℤ) = 10 ^ 28 := by norm_num [BcO]
    have : (BFO : ℤ) = 10 ^ 46 := by norm_num [BFO]
    nlinarith

/-- The packed vertex read at a flat index: values and ranges. -/
private lemma vertex_read (k : VertexIndex) :
    (let v := Nat.land (Nat.shiftRight pythonVertexBig (Nat.mul 171 (flatIx k))) M171
     let w0 := Nat.land v M57
     let w1 := Nat.land (Nat.shiftRight v 57) M57
     let w2 := Nat.shiftRight v 114
     ((w0 : ℤ) = pythonVertexNumCurried k.ℓ k.i k.k 0 + 2 ^ 56 ∧ w0 < 2 ^ 57) ∧
     ((w1 : ℤ) = pythonVertexNumCurried k.ℓ k.i k.k 1 + 2 ^ 56 ∧ w1 < 2 ^ 57) ∧
     ((w2 : ℤ) = pythonVertexNumCurried k.ℓ k.i k.k 2 + 2 ^ 56 ∧ w2 < 2 ^ 57)) := by
  have hflat : flatIx k < 90 := by
    have h1 := k.ℓ.isLt
    have h2 := k.i.isLt
    have h3 := k.k.isLt
    unfold flatIx
    omega
  have hspec := pythonVertexBig_spec ⟨flatIx k, hflat⟩
  have hof : VertexIndex.ofFin90 ⟨flatIx k, hflat⟩ = k := by
    have h := VertexIndex.ofFin90_flat k
    have e : (⟨(45 * k.ℓ.val + 15 * k.i.val + k.k.val) % 90,
        Nat.mod_lt _ (by decide)⟩ : Fin 90) = ⟨flatIx k, hflat⟩ := by
      apply Fin.ext
      show (45 * k.ℓ.val + 15 * k.i.val + k.k.val) % 90 = flatIx k
      exact Nat.mod_eq_of_lt (by unfold flatIx at hflat; exact hflat)
    rwa [e] at h
  rw [hof] at hspec
  simp only [show ∀ a b : ℕ, Nat.land a b = a &&& b from fun _ _ => rfl,
    show ∀ a b : ℕ, Nat.shiftRight a b = a >>> b from fun _ _ => rfl,
    show ∀ a b : ℕ, Nat.mul a b = a * b from fun _ _ => rfl, M171, M57,
    Nat.pow_eq]
  obtain ⟨h0, h1, h2⟩ := hspec
  simp only [pythonVertexNum] at h0 h1 h2
  refine ⟨⟨h0, ?_⟩, ⟨h1, ?_⟩, ⟨h2, ?_⟩⟩
  · exact lt_of_le_of_lt Nat.and_le_right (by norm_num [Nat.pow])
  · exact lt_of_le_of_lt Nat.and_le_right (by norm_num [Nat.pow])
  · have hv : (pythonVertexBig >>> (171 * flatIx k)) &&& (2 ^ 171 - 1) ≤ 2 ^ 171 - 1 :=
      Nat.and_le_right
    rw [Nat.shiftRight_eq_div_pow]
    have : ((pythonVertexBig >>> (171 * flatIx k)) &&& (2 ^ 171 - 1)) / 2 ^ 114
        ≤ (2 ^ 171 - 1) / 2 ^ 114 := Nat.div_le_div_right hv
    calc _ ≤ (2 ^ 171 - 1) / 2 ^ 114 := this
      _ < 2 ^ 57 := by norm_num

/-- Field magnitude bound: `3 · BcO · 2⁵⁶`. -/
private def FBI : ℤ := 3 * 10 ^ 28 * 2 ^ 56

private lemma natAdd_eq (a b : ℕ) : Nat.add a b = a + b := rfl
private lemma natMul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl

/-- Generic two-slot offset field. -/
private lemma field2_bridge {c1 c2 : ℤ} {w0 w1 : ℕ} {W0 W1 : ℤ}
    (hc1 : |c1| ≤ (BcO : ℤ)) (hc2 : |c2| ≤ (BcO : ℤ))
    (hw0 : (w0 : ℤ) = W0 + 2 ^ 56) (hw1 : (w1 : ℤ) = W1 + 2 ^ 56)
    (hW0 : |W0| ≤ 2 ^ 56) (hW1 : |W1| ≤ 2 ^ 56) :
    ((Nat.add (Nat.add (Nat.mul (coO c1) w0) (Nat.mul (coO c2) w1)) (K2O c1 c2)
      - Nat.mul BcO (Nat.add w0 w1) : ℕ) : ℤ)
      = c1 * W0 + c2 * W1 + BFO
      ∧ |c1 * W0 + c2 * W1| ≤ FBI := by
  have e1 := coO_cast hc1
  have e2 := coO_cast hc2
  have eK := K2O_cast hc1 hc2
  have b1 := abs_le.mp hc1
  have b2 := abs_le.mp hc2
  have a0 := abs_le.mp hW0
  have a1 := abs_le.mp hW1
  have hBc : (BcO : ℤ) = 10 ^ 28 := by norm_num [BcO]
  have hBF : (BFO : ℤ) = 10 ^ 46 := by norm_num [BFO]
  have habs : |c1 * W0 + c2 * W1| ≤ FBI := by
    have m1 : |c1 * W0| ≤ 10 ^ 28 * 2 ^ 56 := by
      rw [abs_mul]
      exact mul_le_mul (hBc ▸ hc1) hW0 (abs_nonneg _) (by positivity)
    have m2 : |c2 * W1| ≤ 10 ^ 28 * 2 ^ 56 := by
      rw [abs_mul]
      exact mul_le_mul (hBc ▸ hc2) hW1 (abs_nonneg _) (by positivity)
    calc |c1 * W0 + c2 * W1| ≤ |c1 * W0| + |c2 * W1| := abs_add_le _ _
      _ ≤ FBI := by unfold FBI; linarith
  refine ⟨natSub_cast ?_ ?_, habs⟩
  · simp only [natAdd_eq, natMul_eq]
    push_cast [e1, e2, eK, hw0, hw1]
    ring
  · have := abs_le.mp habs
    unfold FBI at this
    linarith

/-- Generic three-slot offset field. -/
private lemma field3_bridge {c1 c2 c3 : ℤ} {w0 w1 w2 : ℕ} {W0 W1 W2 : ℤ}
    (hc1 : |c1| ≤ (BcO : ℤ)) (hc2 : |c2| ≤ (BcO : ℤ)) (hc3 : |c3| ≤ (BcO : ℤ))
    (hw0 : (w0 : ℤ) = W0 + 2 ^ 56) (hw1 : (w1 : ℤ) = W1 + 2 ^ 56)
    (hw2 : (w2 : ℤ) = W2 + 2 ^ 56)
    (hW0 : |W0| ≤ 2 ^ 56) (hW1 : |W1| ≤ 2 ^ 56) (hW2 : |W2| ≤ 2 ^ 56) :
    ((Nat.add (Nat.add (Nat.add (Nat.mul (coO c1) w0) (Nat.mul (coO c2) w1))
        (Nat.mul (coO c3) w2)) (K3O c1 c2 c3)
      - Nat.mul BcO (Nat.add (Nat.add w0 w1) w2) : ℕ) : ℤ)
      = c1 * W0 + c2 * W1 + c3 * W2 + BFO
      ∧ |c1 * W0 + c2 * W1 + c3 * W2| ≤ FBI := by
  have e1 := coO_cast hc1
  have e2 := coO_cast hc2
  have e3 := coO_cast hc3
  have eK := K3O_cast hc1 hc2 hc3
  have hBc : (BcO : ℤ) = 10 ^ 28 := by norm_num [BcO]
  have hBF : (BFO : ℤ) = 10 ^ 46 := by norm_num [BFO]
  have habs : |c1 * W0 + c2 * W1 + c3 * W2| ≤ FBI := by
    have m : ∀ (c W : ℤ), |c| ≤ (BcO : ℤ) → |W| ≤ 2 ^ 56 →
        |c * W| ≤ 10 ^ 28 * 2 ^ 56 := fun c W hc hW => by
      rw [abs_mul]
      exact mul_le_mul (hBc ▸ hc) hW (abs_nonneg _) (by positivity)
    calc |c1 * W0 + c2 * W1 + c3 * W2|
        ≤ |c1 * W0 + c2 * W1| + |c3 * W2| := abs_add_le _ _
      _ ≤ |c1 * W0| + |c2 * W1| + |c3 * W2| := by
          have := abs_add_le (c1 * W0) (c2 * W1); linarith
      _ ≤ FBI := by
          have h1 := m c1 W0 hc1 hW0
          have h2 := m c2 W1 hc2 hW1
          have h3 := m c3 W2 hc3 hW2
          unfold FBI; linarith
  refine ⟨natSub_cast ?_ ?_, habs⟩
  · simp only [natAdd_eq, natMul_eq]
    push_cast [e1, e2, e3, eK, hw0, hw1, hw2]
    ring
  · have := abs_le.mp habs
    unfold FBI at this
    linarith

/-- All nine `appO` fields bridge to `app6N` (+`BFO`), with magnitude
bounds, under the trig guards. -/
private lemma appO_bridge {stN ctN sfN cfN : ℤ}
    (hst : stN.natAbs ≤ 10 ^ 14) (hct : ctN.natAbs ≤ 10 ^ 14)
    (hsf : sfN.natAbs ≤ 10 ^ 14) (hcf : cfN.natAbs ≤ 10 ^ 14)
    (εθ εφ δ r : ℚ) (k : VertexIndex) :
    let q := appO (mkRCO stN ctN sfN cfN εθ εφ δ r) (flatIx k)
    let z := app6N stN ctN sfN cfN k
    ((q.a0 : ℤ) = z.a0 + BFO ∧ |z.a0| ≤ FBI) ∧
    ((q.a1 : ℤ) = z.a1 + BFO ∧ |z.a1| ≤ FBI) ∧
    ((q.b0 : ℤ) = z.b0 + BFO ∧ |z.b0| ≤ FBI) ∧
    ((q.b1 : ℤ) = z.b1 + BFO ∧ |z.b1| ≤ FBI) ∧
    ((q.c1 : ℤ) = z.c1 + BFO ∧ |z.c1| ≤ FBI) ∧
    ((q.d0 : ℤ) = z.d0 + BFO ∧ |z.d0| ≤ FBI) ∧
    ((q.d1 : ℤ) = z.d1 + BFO ∧ |z.d1| ≤ FBI) ∧
    ((q.e1 : ℤ) = z.e1 + BFO ∧ |z.e1| ≤ FBI) ∧
    ((q.f1 : ℤ) = z.f1 + BFO ∧ |z.f1| ≤ FBI) := by
  have hv := vertex_read k
  simp only at hv
  obtain ⟨⟨hw0, hb0⟩, ⟨hw1, hb1⟩, hw2, hb2⟩ := hv
  have hW0 : |pythonVertexNumCurried k.ℓ k.i k.k 0| ≤ 2 ^ 56 := by rw [abs_le]; omega
  have hW1 : |pythonVertexNumCurried k.ℓ k.i k.k 1| ≤ 2 ^ 56 := by rw [abs_le]; omega
  have hW2 : |pythonVertexNumCurried k.ℓ k.i k.k 2| ≤ 2 ^ 56 := by rw [abs_le]; omega
  have hBc : (BcO : ℤ) = 10 ^ 28 := by norm_num [BcO]
  have hp : ∀ x y : ℤ, x.natAbs ≤ 10 ^ 14 → y.natAbs ≤ 10 ^ 14 →
      |x * y| ≤ (BcO : ℤ) := by
    intro x y hx hy
    rw [abs_mul, hBc]
    calc |x| * |y| ≤ 10 ^ 14 * 10 ^ 14 := by
          refine mul_le_mul ?_ ?_ (abs_nonneg _) (by norm_num)
          · rw [Int.abs_eq_natAbs]; exact_mod_cast hx
          · rw [Int.abs_eq_natAbs]; exact_mod_cast hy
      _ = 10 ^ 28 := by norm_num
  have h13 : ∀ x : ℤ, x.natAbs ≤ 10 ^ 14 → |x * 10 ^ 13| ≤ (BcO : ℤ) := by
    intro x hx
    rw [abs_mul, hBc]
    calc |x| * |(10 ^ 13 : ℤ)| ≤ 10 ^ 14 * 10 ^ 13 := by
          refine mul_le_mul ?_ (by norm_num) (abs_nonneg _) (by norm_num)
          rw [Int.abs_eq_natAbs]; exact_mod_cast hx
      _ ≤ 10 ^ 28 := by norm_num
  have hn : ∀ {x : ℤ}, |x| ≤ (BcO : ℤ) → |(-x)| ≤ (BcO : ℤ) := fun h => by
    rwa [abs_neg]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa only [appO, mkRCO, app6N] using
      (field2_bridge (hn (h13 _ hst)) (h13 _ hct) hw0 hw1 hW0 hW1).1
  · simpa only [app6N] using
      (field2_bridge (hn (h13 _ hst)) (h13 _ hct) hw0 hw1 hW0 hW1).2
  · simpa only [appO, mkRCO, app6N] using
      (field3_bridge (hn (hp _ _ hct hcf)) (hn (hp _ _ hst hcf)) (h13 _ hsf)
        hw0 hw1 hw2 hW0 hW1 hW2).1
  · simpa only [app6N] using
      (field3_bridge (hn (hp _ _ hct hcf)) (hn (hp _ _ hst hcf)) (h13 _ hsf)
        hw0 hw1 hw2 hW0 hW1 hW2).2
  · simpa only [appO, mkRCO, app6N] using
      (field2_bridge (hn (h13 _ hct)) (hn (h13 _ hst)) hw0 hw1 hW0 hW1).1
  · simpa only [app6N] using
      (field2_bridge (hn (h13 _ hct)) (hn (h13 _ hst)) hw0 hw1 hW0 hW1).2
  · simpa only [appO, mkRCO, app6N] using
      (field2_bridge (hp _ _ hst hcf) (hn (hp _ _ hct hcf)) hw0 hw1 hW0 hW1).1
  · simpa only [app6N] using
      (field2_bridge (hp _ _ hst hcf) (hn (hp _ _ hct hcf)) hw0 hw1 hW0 hW1).2
  · simpa only [appO, mkRCO, app6N] using
      (field3_bridge (hp _ _ hct hsf) (hp _ _ hst hsf) (h13 _ hcf)
        hw0 hw1 hw2 hW0 hW1 hW2).1
  · simpa only [app6N] using
      (field3_bridge (hp _ _ hct hsf) (hp _ _ hst hsf) (h13 _ hcf)
        hw0 hw1 hw2 hW0 hW1 hW2).2
  · simpa only [appO, mkRCO, app6N] using
      (field2_bridge (h13 _ hst) (hn (h13 _ hct)) hw0 hw1 hW0 hW1).1
  · simpa only [app6N] using
      (field2_bridge (h13 _ hst) (hn (h13 _ hct)) hw0 hw1 hW0 hW1).2
  · simpa only [appO, mkRCO, app6N] using
      (field2_bridge (hp _ _ hct hcf) (hp _ _ hst hcf) hw0 hw1 hW0 hW1).1
  · simpa only [app6N] using
      (field2_bridge (hp _ _ hct hcf) (hp _ _ hst hcf) hw0 hw1 hW0 hW1).2
  · simpa only [appO, mkRCO, app6N] using
      (field2_bridge (hn (hp _ _ hst hsf)) (hp _ _ hct hsf) hw0 hw1 hW0 hW1).1
  · simpa only [app6N] using
      (field2_bridge (hn (hp _ _ hst hsf)) (hp _ _ hct hsf) hw0 hw1 hW0 hW1).2
  · simpa only [appO, mkRCO, app6N] using
      (field3_bridge (hp _ _ hct hcf) (hp _ _ hst hcf) (hn (h13 _ hsf))
        hw0 hw1 hw2 hW0 hW1 hW2).1
  · simpa only [app6N] using
      (field3_bridge (hp _ _ hct hcf) (hp _ _ hst hcf) (hn (h13 _ hsf))
        hw0 hw1 hw2 hW0 hW1 hW2).2

/-- Pos/neg split of an offset value: difference, sum-as-abs. -/
private lemma split_facts {qh : ℕ} {z : ℤ} (h : (qh : ℤ) = z + BFO) :
    ((qh - BFO : ℕ) : ℤ) - ((BFO - qh : ℕ) : ℤ) = z ∧
    ((qh - BFO : ℕ) : ℤ) + ((BFO - qh : ℕ) : ℤ) = |z| := by
  rw [Int.abs_eq_natAbs]
  omega

/-- Offset difference: `(q̂ + BFO) ∸ v̂` carries `zq − zv` at offset `BFO`
when both values are within `FBI`. -/
private lemma dsub_cast {qh vh : ℕ} {zq zv : ℤ}
    (hq : (qh : ℤ) = zq + BFO) (hv : (vh : ℤ) = zv + BFO)
    (hbq : |zq| ≤ FBI) (hbv : |zv| ≤ FBI) :
    ((Nat.add qh BFO - vh : ℕ) : ℤ) = (zq - zv) + BFO := by
  have h1 := abs_le.mp hbq
  have h2 := abs_le.mp hbv
  have hB : (BFO : ℤ) = 10 ^ 46 := by norm_num [BFO]
  have hF : FBI = 3 * 10 ^ 28 * 2 ^ 56 := rfl
  simp only [natAdd_eq]
  omega

/-- Branchless square cast. -/
private lemma sqdO_cast {dh : ℕ} {y : ℤ} (h : (dh : ℤ) = y + BFO)
    {V : ℤ} (hval : y * y = V) :
    ((sqdO dh : ℕ) : ℤ) = V := by
  subst hval
  unfold sqdO BF2O BFO2x
  refine natSub_cast ?_ (mul_self_nonneg y)
  simp only [natAdd_eq, natMul_eq]
  push_cast [h]
  ring

/-- Split square cast. -/
private lemma sqsO_cast {pp nn : ℕ} {z : ℤ}
    (_hd : (pp : ℤ) - nn = z) (hs : (pp : ℤ) + nn = |z|) :
    ((sqsO pp nn : ℕ) : ℤ) = z * z := by
  unfold sqsO
  simp only [natAdd_eq, natMul_eq]
  push_cast
  rw [show ((pp : ℤ) + nn) = |z| from hs]
  rw [← abs_mul, abs_mul_self]

/-- Two-term atom cast. -/
private lemma atomA2_cast {qP0 qN0 qP1 qN1 d0 d1 xP xN slack : ℕ}
    {q0 q1 y0 y1 sl : ℤ}
    (hq0 : (qP0 : ℤ) - qN0 = q0) (hq1 : (qP1 : ℤ) - qN1 = q1)
    (hd0 : (d0 : ℤ) = y0 + BFO) (hd1 : (d1 : ℤ) = y1 + BFO)
    (hxP : (xP : ℤ) = BFO * (qP0 + qP1)) (hxN : (xN : ℤ) = BFO * (qN0 + qN1))
    (hsl : (slack : ℤ) = sl) {V : ℤ} (hval : q0 * y0 + q1 * y1 = V) :
    ((atomA2 qP0 qN0 qP1 qN1 d0 d1 xP xN slack : ℕ) : ℤ) = |V| + sl := by
  subst hval
  unfold atomA2
  simp only [natAdd_eq, natMul_eq, Nat.cast_add, absSub_cast]
  rw [hsl]
  refine congrArg (fun t => |t| + sl) ?_
  push_cast
  rw [hd0, hd1, hxP, hxN]
  linear_combination (y0 : ℤ) * hq0 + (y1 : ℤ) * hq1

/-- Three-term atom cast. -/
private lemma atomA3_cast {qP0 qN0 qP1 qN1 qP2 qN2 d0 d1 d2 xP xN slack : ℕ}
    {q0 q1 q2 y0 y1 y2 sl : ℤ}
    (hq0 : (qP0 : ℤ) - qN0 = q0) (hq1 : (qP1 : ℤ) - qN1 = q1)
    (hq2 : (qP2 : ℤ) - qN2 = q2)
    (hd0 : (d0 : ℤ) = y0 + BFO) (hd1 : (d1 : ℤ) = y1 + BFO)
    (hd2 : (d2 : ℤ) = y2 + BFO)
    (hxP : (xP : ℤ) = BFO * (qP0 + qP1 + qP2))
    (hxN : (xN : ℤ) = BFO * (qN0 + qN1 + qN2))
    (hsl : (slack : ℤ) = sl) {V : ℤ}
    (hval : q0 * y0 + q1 * y1 + q2 * y2 = V) :
    ((atomA3 qP0 qN0 qP1 qN1 qP2 qN2 d0 d1 d2 xP xN slack : ℕ) : ℤ) = |V| + sl := by
  subst hval
  unfold atomA3
  simp only [natAdd_eq, natMul_eq, Nat.cast_add, absSub_cast]
  rw [hsl]
  refine congrArg (fun t => |t| + sl) ?_
  push_cast
  rw [hd0, hd1, hd2, hxP, hxN]
  linear_combination (y0 : ℤ) * hq0 + (y1 : ℤ) * hq1 + (y2 : ℤ) * hq2

/-- Four-term atom cast. -/
private lemma atomA4_cast {qP0 qN0 qP1 qN1 qP2 qN2 qP3 qN3 d0 d1 d2 d3 xP xN slack : ℕ}
    {q0 q1 q2 q3 y0 y1 y2 y3 sl : ℤ}
    (hq0 : (qP0 : ℤ) - qN0 = q0) (hq1 : (qP1 : ℤ) - qN1 = q1)
    (hq2 : (qP2 : ℤ) - qN2 = q2) (hq3 : (qP3 : ℤ) - qN3 = q3)
    (hd0 : (d0 : ℤ) = y0 + BFO) (hd1 : (d1 : ℤ) = y1 + BFO)
    (hd2 : (d2 : ℤ) = y2 + BFO) (hd3 : (d3 : ℤ) = y3 + BFO)
    (hxP : (xP : ℤ) = BFO * (qP0 + qP1 + qP2 + qP3))
    (hxN : (xN : ℤ) = BFO * (qN0 + qN1 + qN2 + qN3))
    (hsl : (slack : ℤ) = sl) {V : ℤ}
    (hval : q0 * y0 + q1 * y1 + q2 * y2 + q3 * y3 = V) :
    ((atomA4 qP0 qN0 qP1 qN1 qP2 qN2 qP3 qN3 d0 d1 d2 d3 xP xN slack : ℕ) : ℤ)
      = |V| + sl := by
  subst hval
  unfold atomA4
  simp only [natAdd_eq, natMul_eq, Nat.cast_add, absSub_cast]
  rw [hsl]
  refine congrArg (fun t => |t| + sl) ?_
  push_cast
  rw [hd0, hd1, hd2, hd3, hxP, hxN]
  linear_combination (y0 : ℤ) * hq0 + (y1 : ℤ) * hq1 + (y2 : ℤ) * hq2
    + (y3 : ℤ) * hq3

/-- Six-term atom cast. -/
private lemma atomA6_cast
    {qP0 qN0 qP1 qN1 qP2 qN2 qP3 qN3 qP4 qN4 qP5 qN5
     d0 d1 d2 d3 d4 d5 xP xN slack : ℕ}
    {q0 q1 q2 q3 q4 q5 y0 y1 y2 y3 y4 y5 sl : ℤ}
    (hq0 : (qP0 : ℤ) - qN0 = q0) (hq1 : (qP1 : ℤ) - qN1 = q1)
    (hq2 : (qP2 : ℤ) - qN2 = q2) (hq3 : (qP3 : ℤ) - qN3 = q3)
    (hq4 : (qP4 : ℤ) - qN4 = q4) (hq5 : (qP5 : ℤ) - qN5 = q5)
    (hd0 : (d0 : ℤ) = y0 + BFO) (hd1 : (d1 : ℤ) = y1 + BFO)
    (hd2 : (d2 : ℤ) = y2 + BFO) (hd3 : (d3 : ℤ) = y3 + BFO)
    (hd4 : (d4 : ℤ) = y4 + BFO) (hd5 : (d5 : ℤ) = y5 + BFO)
    (hxP : (xP : ℤ) = BFO * (qP0 + qP1 + qP2 + qP3 + qP4 + qP5))
    (hxN : (xN : ℤ) = BFO * (qN0 + qN1 + qN2 + qN3 + qN4 + qN5))
    (hsl : (slack : ℤ) = sl) {V : ℤ}
    (hval : q0 * y0 + q1 * y1 + q2 * y2 + q3 * y3 + q4 * y4 + q5 * y5 = V) :
    ((atomA6 qP0 qN0 qP1 qN1 qP2 qN2 qP3 qN3 qP4 qN4 qP5 qN5
        d0 d1 d2 d3 d4 d5 xP xN slack : ℕ) : ℤ) = |V| + sl := by
  subst hval
  unfold atomA6
  simp only [natAdd_eq, natMul_eq, Nat.cast_add, absSub_cast]
  rw [hsl]
  refine congrArg (fun t => |t| + sl) ?_
  push_cast
  rw [hd0, hd1, hd2, hd3, hd4, hd5, hxP, hxN]
  linear_combination (y0 : ℤ) * hq0 + (y1 : ℤ) * hq1 + (y2 : ℤ) * hq2
    + (y3 : ℤ) * hq3 + (y4 : ℤ) * hq4 + (y5 : ℤ) * hq5

/-- The windowed Newton bound dominates `sqrtNum84` through the `ℕ` cast. -/
private lemma nUpO84_dom {S : ℕ} {Sz : ℤ} (h : (S : ℤ) = Sz) :
    sqrtNum84 Sz ≤ (nUpO84 S : ℤ) := by
  rcases lt_or_eq_of_le (show (0 : ℤ) ≤ Sz from by omega) with hpos | hzero
  · have := sqrtNum84_le_nUpOZ84 Sz
    unfold nUpOZ84 at this
    rw [if_neg (by omega)] at this
    rwa [show Sz.toNat = S from by omega] at this
  · rw [show sqrtNum84 Sz = 0 from by unfold sqrtNum84; rw [if_pos (by omega)]]
    positivity

/-- Sign-split main dot: the difference of the two `dotPO` sides. -/
private lemma dotPO_sub_cast {qP0 qN0 qP1 qN1 d0 d1 xP xN : ℕ} {q0 q1 y0 y1 : ℤ}
    (hq0 : (qP0 : ℤ) - qN0 = q0) (hq1 : (qP1 : ℤ) - qN1 = q1)
    (hd0 : (d0 : ℤ) = y0 + BFO) (hd1 : (d1 : ℤ) = y1 + BFO)
    (hxP : (xP : ℤ) = BFO * (qP0 + qP1)) (hxN : (xN : ℤ) = BFO * (qN0 + qN1))
    {V : ℤ} (hval : q0 * y0 + q1 * y1 = V) :
    ((dotPO qP0 qP1 d0 d1 xN : ℕ) : ℤ) - ((dotPO qN0 qN1 d0 d1 xP : ℕ) : ℤ)
      = V := by
  subst hval
  unfold dotPO
  simp only [natAdd_eq, natMul_eq]
  push_cast
  rw [hd0, hd1, hxP, hxN]
  linear_combination (y0 : ℤ) * hq0 + (y1 : ℤ) * hq1

/-- `budO` casts to `budN` given exact coefficient casts. -/
private lemma budO_cast {k1 k2 k3 k4 k5 k6 a1 a2 a3 a4 a5 rem : ℕ}
    {en ed fn fd : ℤ}
    (h1 : (k1 : ℤ) = 6 * en * ed ^ 2 * fd ^ 3)
    (h2 : (k2 : ℤ) = 6 * fn * fd ^ 2 * ed ^ 3)
    (h3 : (k3 : ℤ) = 3 * en ^ 2 * ed * fd ^ 3)
    (h4 : (k4 : ℤ) = 6 * en * fn * ed ^ 2 * fd ^ 2)
    (h5 : (k5 : ℤ) = 3 * fn ^ 2 * fd * ed ^ 3)
    (h6 : (k6 : ℤ) = (en * fd + fn * ed) ^ 3) :
    ((budO k1 k2 k3 k4 k5 k6 a1 a2 a3 a4 a5 rem : ℕ) : ℤ)
      = budN (a1 : ℤ) (a2 : ℤ) (a3 : ℤ) (a4 : ℤ) (a5 : ℤ) (rem : ℤ) en ed fn fd := by
  unfold budO budN
  simp only [natAdd_eq, natMul_eq]
  push_cast
  rw [h1, h2, h3, h4, h5, h6]

/-- The `mkRCO` numeric constants cast exactly in the guarded regime. -/
private lemma mkRCO_casts {stN ctN sfN cfN : ℤ} {εθ εφ δ r : ℚ}
    (hεθ : 0 ≤ εθ.num) (hεφ : 0 ≤ εφ.num) (hδ : 0 ≤ δ.num) (hr : 0 < r.num) :
    let rc := mkRCO stN ctN sfN cfN εθ εφ δ r
    let en := εθ.num
    let ed : ℤ := εθ.den
    let fn := εφ.num
    let fd : ℤ := εφ.den
    ((rc.k1 : ℤ) = 6 * en * ed ^ 2 * fd ^ 3) ∧
    ((rc.k2 : ℤ) = 6 * fn * fd ^ 2 * ed ^ 3) ∧
    ((rc.k3 : ℤ) = 3 * en ^ 2 * ed * fd ^ 3) ∧
    ((rc.k4 : ℤ) = 6 * en * fn * ed ^ 2 * fd ^ 2) ∧
    ((rc.k5 : ℤ) = 3 * fn ^ 2 * fd * ed ^ 3) ∧
    ((rc.k6 : ℤ) = (en * fd + fn * ed) ^ 3) ∧
    ((rc.W : ℤ) = 6 * (ed * fd) ^ 3) ∧
    ((rc.cmpL : ℤ) = δ.num * r.den * 10 ^ 52) ∧
    ((rc.cmpRc : ℤ) = 6 * (ed * fd) ^ 3 * (δ.den * r.num)) := by
  have hed : (0 : ℤ) ≤ (εθ.den : ℤ) := Int.natCast_nonneg _
  have hfd : (0 : ℤ) ≤ (εφ.den : ℤ) := Int.natCast_nonneg _
  have hδd : (0 : ℤ) ≤ (δ.den : ℤ) := Int.natCast_nonneg _
  have hrd : (0 : ℤ) ≤ (r.den : ℤ) := Int.natCast_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [mkRCO] <;> rw [Int.toNat_of_nonneg] <;> first | rfl | positivity

set_option maxHeartbeats 3200000 in
/-- The crux, over plain variables: a true `pairCore` implies the
`beCheckN` (exact-`sqrtNum84`) pair conjunction, given the bridge facts
for every input. -/
private lemma pairCore_sound {εθ εφ δ r : ℚ} {rc : RCO} {qc : QCO}
    {da0 da1 db0 db1 dc1 dd0 dd1 de1 df1 nrmN : ℕ}
    {zq zv : App6N} {nrmZ : ℤ}
    (hεθ : 0 ≤ εθ.num) (hεφ : 0 ≤ εφ.num) (hδ : 0 ≤ δ.num) (hr : 0 < r.num)
    (k1e : (rc.k1 : ℤ) = 6 * εθ.num * (εθ.den : ℤ) ^ 2 * (εφ.den : ℤ) ^ 3)
    (k2e : (rc.k2 : ℤ) = 6 * εφ.num * (εφ.den : ℤ) ^ 2 * (εθ.den : ℤ) ^ 3)
    (k3e : (rc.k3 : ℤ) = 3 * εθ.num ^ 2 * (εθ.den : ℤ) * (εφ.den : ℤ) ^ 3)
    (k4e : (rc.k4 : ℤ) = 6 * εθ.num * εφ.num * (εθ.den : ℤ) ^ 2 * (εφ.den : ℤ) ^ 2)
    (k5e : (rc.k5 : ℤ) = 3 * εφ.num ^ 2 * (εφ.den : ℤ) * (εθ.den : ℤ) ^ 3)
    (k6e : (rc.k6 : ℤ) = (εθ.num * (εφ.den : ℤ) + εφ.num * (εθ.den : ℤ)) ^ 3)
    (We : (rc.W : ℤ) = 6 * ((εθ.den : ℤ) * εφ.den) ^ 3)
    (cLe : (rc.cmpL : ℤ) = δ.num * r.den * 10 ^ 52)
    (cRe : (rc.cmpRc : ℤ) = 6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * ((δ.den : ℤ) * r.num))
    (sa0d : (qc.a0P : ℤ) - qc.a0N = zq.a0) (sa1d : (qc.a1P : ℤ) - qc.a1N = zq.a1)
    (sb0d : (qc.b0P : ℤ) - qc.b0N = zq.b0) (sb1d : (qc.b1P : ℤ) - qc.b1N = zq.b1)
    (sc1d : (qc.c1P : ℤ) - qc.c1N = zq.c1)
    (sd0d : (qc.d0P : ℤ) - qc.d0N = zq.d0) (sd1d : (qc.d1P : ℤ) - qc.d1N = zq.d1)
    (se1d : (qc.e1P : ℤ) - qc.e1N = zq.e1) (sf1d : (qc.f1P : ℤ) - qc.f1N = zq.f1)
    (xmP : (qc.xmP : ℤ) = BFO * (qc.a0P + qc.a1P))
    (xmN : (qc.xmN : ℤ) = BFO * (qc.a0N + qc.a1N))
    (x1P : (qc.x1P : ℤ) = BFO * (qc.b0P + qc.b1P + qc.a0P + qc.a1P))
    (x1N : (qc.x1N : ℤ) = BFO * (qc.b0N + qc.b1N + qc.a0N + qc.a1N))
    (x2P : (qc.x2P : ℤ) = BFO * (qc.c1P + qc.a1P))
    (x2N : (qc.x2N : ℤ) = BFO * (qc.c1N + qc.a1N))
    (x3P : (qc.x3P : ℤ)
      = BFO * (qc.d0P + qc.d1P + 2 * qc.b0P + 2 * qc.b1P + qc.a0P + qc.a1P))
    (x3N : (qc.x3N : ℤ)
      = BFO * (qc.d0N + qc.d1N + 2 * qc.b0N + 2 * qc.b1N + qc.a0N + qc.a1N))
    (x4P : (qc.x4P : ℤ) = BFO * (qc.e1P + qc.b1P + qc.c1P + qc.a1P))
    (x4N : (qc.x4N : ℤ) = BFO * (qc.e1N + qc.b1N + qc.c1N + qc.a1N))
    (x5P : (qc.x5P : ℤ) = BFO * (qc.f1P + 2 * qc.c1P + qc.a1P))
    (x5N : (qc.x5N : ℤ) = BFO * (qc.f1N + 2 * qc.c1N + qc.a1N))
    (hda0 : (da0 : ℤ) = (zq.sub zv).a0 + BFO) (hda1 : (da1 : ℤ) = (zq.sub zv).a1 + BFO)
    (hdb0 : (db0 : ℤ) = (zq.sub zv).b0 + BFO) (hdb1 : (db1 : ℤ) = (zq.sub zv).b1 + BFO)
    (hdc1 : (dc1 : ℤ) = (zq.sub zv).c1 + BFO)
    (hdd0 : (dd0 : ℤ) = (zq.sub zv).d0 + BFO) (hdd1 : (dd1 : ℤ) = (zq.sub zv).d1 + BFO)
    (hde1 : (de1 : ℤ) = (zq.sub zv).e1 + BFO)
    (hdf1 : (df1 : ℤ) = (zq.sub zv).f1 + BFO)
    (hnrm : (nrmN : ℤ) = nrmZ)
    (hzc0 : zq.c0 = 0) (hze0 : zq.e0 = 0) (hzf0 : zq.f0 = 0)
    (hvc0 : zv.c0 = 0) (hve0 : zv.e0 = 0) (hvf0 : zv.f0 = 0)
    (hD1 : 6 * ((εθ.den : ℤ) * εφ.den) ^ 3
        * (sqrtNum84 (zq.a0 * zq.a0 + zq.a1 * zq.a1) + 3 * 10 ^ 6)
      + budN (sqrtNum84 (zq.b0 * zq.b0 + zq.b1 * zq.b1) + 3 * 10 ^ 6)
          (sqrtNum84 (zq.c0 * zq.c0 + zq.c1 * zq.c1) + 3 * 10 ^ 6)
          (sqrtNum84 (zq.d0 * zq.d0 + zq.d1 * zq.d1) + 3 * 10 ^ 6)
          (sqrtNum84 (zq.e0 * zq.e0 + zq.e1 * zq.e1) + 3 * 10 ^ 6)
          (sqrtNum84 (zq.f0 * zq.f0 + zq.f1 * zq.f1) + 3 * 10 ^ 6) (10 ^ 16)
          εθ.num (εθ.den : ℤ) εφ.num (εφ.den : ℤ) ≤ (qc.D1N : ℤ))
    (h : pairCore rc qc da0 da1 db0 db1 dc1 dd0 dd1 de1 df1 nrmN = true) :
    0 < 6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * (zq.a0 * (zq.sub zv).a0 + zq.a1 * (zq.sub zv).a1)
        - 6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * (9 * 10 ^ 74)
        - budN (|(zq.b0 * (zq.sub zv).a0 + zq.b1 * (zq.sub zv).a1)
              + (zq.a0 * (zq.sub zv).b0 + zq.a1 * (zq.sub zv).b1)| + 18 * 10 ^ 74)
            (|(zq.c0 * (zq.sub zv).a0 + zq.c1 * (zq.sub zv).a1)
              + (zq.a0 * (zq.sub zv).c0 + zq.a1 * (zq.sub zv).c1)| + 18 * 10 ^ 74)
            (|(zq.d0 * (zq.sub zv).a0 + zq.d1 * (zq.sub zv).a1)
              + 2 * (zq.b0 * (zq.sub zv).b0 + zq.b1 * (zq.sub zv).b1)
              + (zq.a0 * (zq.sub zv).d0 + zq.a1 * (zq.sub zv).d1)| + 36 * 10 ^ 74)
            (|(zq.e0 * (zq.sub zv).a0 + zq.e1 * (zq.sub zv).a1)
              + (zq.b0 * (zq.sub zv).c0 + zq.b1 * (zq.sub zv).c1)
              + (zq.c0 * (zq.sub zv).b0 + zq.c1 * (zq.sub zv).b1)
              + (zq.a0 * (zq.sub zv).e0 + zq.a1 * (zq.sub zv).e1)| + 36 * 10 ^ 74)
            (|(zq.f0 * (zq.sub zv).a0 + zq.f1 * (zq.sub zv).a1)
              + 2 * (zq.c0 * (zq.sub zv).c0 + zq.c1 * (zq.sub zv).c1)
              + (zq.a0 * (zq.sub zv).f0 + zq.a1 * (zq.sub zv).f1)| + 36 * 10 ^ 74)
            (8 * nrmZ * 10 ^ 68) εθ.num (εθ.den : ℤ) εφ.num (εφ.den : ℤ) ∧
      δ.num * (r.den : ℤ)
          * (10 ^ 52 * ((6 * ((εθ.den : ℤ) * εφ.den) ^ 3
              * (sqrtNum84 (zq.a0 * zq.a0 + zq.a1 * zq.a1) + 3 * 10 ^ 6)
            + budN (sqrtNum84 (zq.b0 * zq.b0 + zq.b1 * zq.b1) + 3 * 10 ^ 6)
                (sqrtNum84 (zq.c0 * zq.c0 + zq.c1 * zq.c1) + 3 * 10 ^ 6)
                (sqrtNum84 (zq.d0 * zq.d0 + zq.d1 * zq.d1) + 3 * 10 ^ 6)
                (sqrtNum84 (zq.e0 * zq.e0 + zq.e1 * zq.e1) + 3 * 10 ^ 6)
                (sqrtNum84 (zq.f0 * zq.f0 + zq.f1 * zq.f1) + 3 * 10 ^ 6) (10 ^ 16)
                εθ.num (εθ.den : ℤ) εφ.num (εφ.den : ℤ))
            * (6 * ((εθ.den : ℤ) * εφ.den) ^ 3
              * (sqrtNum84 ((zq.sub zv).a0 * (zq.sub zv).a0
                  + (zq.sub zv).a1 * (zq.sub zv).a1) + 5 * 10 ^ 6)
            + budN (sqrtNum84 ((zq.sub zv).b0 * (zq.sub zv).b0
                  + (zq.sub zv).b1 * (zq.sub zv).b1) + 5 * 10 ^ 6)
                (sqrtNum84 ((zq.sub zv).c0 * (zq.sub zv).c0
                  + (zq.sub zv).c1 * (zq.sub zv).c1) + 5 * 10 ^ 6)
                (sqrtNum84 ((zq.sub zv).d0 * (zq.sub zv).d0
                  + (zq.sub zv).d1 * (zq.sub zv).d1) + 5 * 10 ^ 6)
                (sqrtNum84 ((zq.sub zv).e0 * (zq.sub zv).e0
                  + (zq.sub zv).e1 * (zq.sub zv).e1) + 5 * 10 ^ 6)
                (sqrtNum84 ((zq.sub zv).f0 * (zq.sub zv).f0
                  + (zq.sub zv).f1 * (zq.sub zv).f1) + 5 * 10 ^ 6) nrmZ
                εθ.num (εθ.den : ℤ) εφ.num (εφ.den : ℤ))))
        < (6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * (zq.a0 * (zq.sub zv).a0 + zq.a1 * (zq.sub zv).a1)
            - 6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * (9 * 10 ^ 74)
            - budN (|(zq.b0 * (zq.sub zv).a0 + zq.b1 * (zq.sub zv).a1)
                  + (zq.a0 * (zq.sub zv).b0 + zq.a1 * (zq.sub zv).b1)| + 18 * 10 ^ 74)
                (|(zq.c0 * (zq.sub zv).a0 + zq.c1 * (zq.sub zv).a1)
                  + (zq.a0 * (zq.sub zv).c0 + zq.a1 * (zq.sub zv).c1)| + 18 * 10 ^ 74)
                (|(zq.d0 * (zq.sub zv).a0 + zq.d1 * (zq.sub zv).a1)
                  + 2 * (zq.b0 * (zq.sub zv).b0 + zq.b1 * (zq.sub zv).b1)
                  + (zq.a0 * (zq.sub zv).d0 + zq.a1 * (zq.sub zv).d1)| + 36 * 10 ^ 74)
                (|(zq.e0 * (zq.sub zv).a0 + zq.e1 * (zq.sub zv).a1)
                  + (zq.b0 * (zq.sub zv).c0 + zq.b1 * (zq.sub zv).c1)
                  + (zq.c0 * (zq.sub zv).b0 + zq.c1 * (zq.sub zv).b1)
                  + (zq.a0 * (zq.sub zv).e0 + zq.a1 * (zq.sub zv).e1)| + 36 * 10 ^ 74)
                (|(zq.f0 * (zq.sub zv).a0 + zq.f1 * (zq.sub zv).a1)
                  + 2 * (zq.c0 * (zq.sub zv).c0 + zq.c1 * (zq.sub zv).c1)
                  + (zq.a0 * (zq.sub zv).f0 + zq.a1 * (zq.sub zv).f1)| + 36 * 10 ^ 74)
                (8 * nrmZ * 10 ^ 68) εθ.num (εθ.den : ℤ) εφ.num (εφ.den : ℤ))
          * (6 * ((εθ.den : ℤ) * εφ.den) ^ 3) * ((δ.den : ℤ) * r.num) := by
  have hWnn : (0 : ℤ) ≤ 6 * ((εθ.den : ℤ) * εφ.den) ^ 3 := by positivity
  have hed : (0 : ℤ) ≤ (εθ.den : ℤ) := Int.natCast_nonneg _
  have hfd : (0 : ℤ) ≤ (εφ.den : ℤ) := Int.natCast_nonneg _
  have e18 : ((E74x18 : ℕ) : ℤ) = 18 * 10 ^ 74 := by norm_num [E74x18, Nat.pow_eq]
  have e36 : ((E74x36 : ℕ) : ℤ) = 36 * 10 ^ 74 := by norm_num [E74x36, Nat.pow_eq]
  have e9 : ((E74x9 : ℕ) : ℤ) = 9 * 10 ^ 74 := by norm_num [E74x9, Nat.pow_eq]
  have e68 : ((E68x8 : ℕ) : ℤ) = 8 * 10 ^ 68 := by norm_num [E68x8, Nat.pow_eq]
  have e65 : ((E6x5 : ℕ) : ℤ) = 5 * 10 ^ 6 := by norm_num [E6x5, Nat.pow_eq]
  unfold pairCore at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  -- doubled splits
  have sb0d2 : ((Nat.mul 2 qc.b0P : ℕ) : ℤ) - (Nat.mul 2 qc.b0N : ℕ) = 2 * zq.b0 := by
    simp only [natMul_eq]; push_cast; linarith
  have sb1d2 : ((Nat.mul 2 qc.b1P : ℕ) : ℤ) - (Nat.mul 2 qc.b1N : ℕ) = 2 * zq.b1 := by
    simp only [natMul_eq]; push_cast; linarith
  have sc1d2 : ((Nat.mul 2 qc.c1P : ℕ) : ℤ) - (Nat.mul 2 qc.c1N : ℕ) = 2 * zq.c1 := by
    simp only [natMul_eq]; push_cast; linarith
  -- doubled x-constants (with the Nat.mul 2 arguments)
  have x3P' : (qc.x3P : ℤ)
      = BFO * (qc.d0P + qc.d1P + (Nat.mul 2 qc.b0P : ℕ) + (Nat.mul 2 qc.b1P : ℕ)
        + qc.a0P + qc.a1P) := by
    rw [x3P]; simp only [natMul_eq]; push_cast; ring
  have x3N' : (qc.x3N : ℤ)
      = BFO * (qc.d0N + qc.d1N + (Nat.mul 2 qc.b0N : ℕ) + (Nat.mul 2 qc.b1N : ℕ)
        + qc.a0N + qc.a1N) := by
    rw [x3N]; simp only [natMul_eq]; push_cast; ring
  have x5P' : (qc.x5P : ℤ)
      = BFO * (qc.f1P + (Nat.mul 2 qc.c1P : ℕ) + qc.a1P) := by
    rw [x5P]; simp only [natMul_eq]; push_cast; ring
  have x5N' : (qc.x5N : ℤ)
      = BFO * (qc.f1N + (Nat.mul 2 qc.c1N : ℕ) + qc.a1N) := by
    rw [x5N]; simp only [natMul_eq]; push_cast; ring
  -- main dot and abs atoms
  have hmd := dotPO_sub_cast sa0d sa1d hda0 hda1 xmP xmN
    (V := zq.a0 * (zq.sub zv).a0 + zq.a1 * (zq.sub zv).a1) rfl
  have t1e := atomA4_cast sb0d sb1d sa0d sa1d hda0 hda1 hdb0 hdb1 x1P x1N e18
    (V := (zq.b0 * (zq.sub zv).a0 + zq.b1 * (zq.sub zv).a1)
      + (zq.a0 * (zq.sub zv).b0 + zq.a1 * (zq.sub zv).b1)) (by ring)
  have t2e := atomA2_cast sc1d sa1d hda1 hdc1 x2P x2N e18
    (V := (zq.c0 * (zq.sub zv).a0 + zq.c1 * (zq.sub zv).a1)
      + (zq.a0 * (zq.sub zv).c0 + zq.a1 * (zq.sub zv).c1))
    (by rw [hzc0, show (zq.sub zv).c0 = zq.c0 - zv.c0 from rfl, hzc0, hvc0]; ring)
  have t3e := atomA6_cast sd0d sd1d sb0d2 sb1d2 sa0d sa1d
    hda0 hda1 hdb0 hdb1 hdd0 hdd1 x3P' x3N' e36
    (V := (zq.d0 * (zq.sub zv).a0 + zq.d1 * (zq.sub zv).a1)
      + 2 * (zq.b0 * (zq.sub zv).b0 + zq.b1 * (zq.sub zv).b1)
      + (zq.a0 * (zq.sub zv).d0 + zq.a1 * (zq.sub zv).d1)) (by ring)
  have t4e := atomA4_cast se1d sb1d sc1d sa1d hda1 hdc1 hdb1 hde1 x4P x4N e36
    (V := (zq.e0 * (zq.sub zv).a0 + zq.e1 * (zq.sub zv).a1)
      + (zq.b0 * (zq.sub zv).c0 + zq.b1 * (zq.sub zv).c1)
      + (zq.c0 * (zq.sub zv).b0 + zq.c1 * (zq.sub zv).b1)
      + (zq.a0 * (zq.sub zv).e0 + zq.a1 * (zq.sub zv).e1))
    (by rw [show (zq.sub zv).c0 = zq.c0 - zv.c0 from rfl,
          show (zq.sub zv).e0 = zq.e0 - zv.e0 from rfl, hzc0, hvc0, hze0, hve0]; ring)
  have t5e := atomA3_cast sf1d sc1d2 sa1d hda1 hdc1 hdf1 x5P' x5N' e36
    (V := (zq.f0 * (zq.sub zv).a0 + zq.f1 * (zq.sub zv).a1)
      + 2 * (zq.c0 * (zq.sub zv).c0 + zq.c1 * (zq.sub zv).c1)
      + (zq.a0 * (zq.sub zv).f0 + zq.a1 * (zq.sub zv).f1))
    (by rw [show (zq.sub zv).c0 = zq.c0 - zv.c0 from rfl,
          show (zq.sub zv).f0 = zq.f0 - zv.f0 from rfl, hzc0, hvc0, hzf0, hvf0]; ring)
  -- the budget cast
  have hrem : ((Nat.mul E68x8 nrmN : ℕ) : ℤ) = 8 * nrmZ * 10 ^ 68 := by
    simp only [natMul_eq]; push_cast; rw [e68, hnrm]; ring
  have hbud : ((budO rc.k1 rc.k2 rc.k3 rc.k4 rc.k5 rc.k6
      (atomA4 qc.b0P qc.b0N qc.b1P qc.b1N qc.a0P qc.a0N qc.a1P qc.a1N
        da0 da1 db0 db1 qc.x1P qc.x1N E74x18)
      (atomA2 qc.c1P qc.c1N qc.a1P qc.a1N da1 dc1 qc.x2P qc.x2N E74x18)
      (atomA6 qc.d0P qc.d0N qc.d1P qc.d1N (Nat.mul 2 qc.b0P) (Nat.mul 2 qc.b0N)
        (Nat.mul 2 qc.b1P) (Nat.mul 2 qc.b1N) qc.a0P qc.a0N qc.a1P qc.a1N
        da0 da1 db0 db1 dd0 dd1 qc.x3P qc.x3N E74x36)
      (atomA4 qc.e1P qc.e1N qc.b1P qc.b1N qc.c1P qc.c1N qc.a1P qc.a1N
        da1 dc1 db1 de1 qc.x4P qc.x4N E74x36)
      (atomA3 qc.f1P qc.f1N (Nat.mul 2 qc.c1P) (Nat.mul 2 qc.c1N)
        qc.a1P qc.a1N da1 dc1 df1 qc.x5P qc.x5N E74x36)
      (Nat.mul E68x8 nrmN) : ℕ) : ℤ)
      = budN (|(zq.b0 * (zq.sub zv).a0 + zq.b1 * (zq.sub zv).a1)
            + (zq.a0 * (zq.sub zv).b0 + zq.a1 * (zq.sub zv).b1)| + 18 * 10 ^ 74)
          (|(zq.c0 * (zq.sub zv).a0 + zq.c1 * (zq.sub zv).a1)
            + (zq.a0 * (zq.sub zv).c0 + zq.a1 * (zq.sub zv).c1)| + 18 * 10 ^ 74)
          (|(zq.d0 * (zq.sub zv).a0 + zq.d1 * (zq.sub zv).a1)
            + 2 * (zq.b0 * (zq.sub zv).b0 + zq.b1 * (zq.sub zv).b1)
            + (zq.a0 * (zq.sub zv).d0 + zq.a1 * (zq.sub zv).d1)| + 36 * 10 ^ 74)
          (|(zq.e0 * (zq.sub zv).a0 + zq.e1 * (zq.sub zv).a1)
            + (zq.b0 * (zq.sub zv).c0 + zq.b1 * (zq.sub zv).c1)
            + (zq.c0 * (zq.sub zv).b0 + zq.c1 * (zq.sub zv).b1)
            + (zq.a0 * (zq.sub zv).e0 + zq.a1 * (zq.sub zv).e1)| + 36 * 10 ^ 74)
          (|(zq.f0 * (zq.sub zv).a0 + zq.f1 * (zq.sub zv).a1)
            + 2 * (zq.c0 * (zq.sub zv).c0 + zq.c1 * (zq.sub zv).c1)
            + (zq.a0 * (zq.sub zv).f0 + zq.a1 * (zq.sub zv).f1)| + 36 * 10 ^ 74)
          (8 * nrmZ * 10 ^ 68) εθ.num (εθ.den : ℤ) εφ.num (εφ.den : ℤ) := by
    rw [budO_cast k1e k2e k3e k4e k5e k6e, t1e, t2e, t3e, t4e, t5e, hrem]
  -- numerator equality (expanded-cast form)
  have hAB : (6 * ((εθ.den : ℤ) * εφ.den) ^ 3) * ((dotPO qc.a0P qc.a1P da0 da1 qc.xmN : ℕ) : ℤ)
      - ((6 * ((εθ.den : ℤ) * εφ.den) ^ 3) * ((dotPO qc.a0N qc.a1N da0 da1 qc.xmP : ℕ) : ℤ)
        + (6 * ((εθ.den : ℤ) * εφ.den) ^ 3) * (9 * 10 ^ 74)
        + budN (|zq.b0 * (zq.sub zv).a0 + zq.b1 * (zq.sub zv).a1
              + (zq.a0 * (zq.sub zv).b0 + zq.a1 * (zq.sub zv).b1)| + 18 * 10 ^ 74)
            (|zq.c0 * (zq.sub zv).a0 + zq.c1 * (zq.sub zv).a1
              + (zq.a0 * (zq.sub zv).c0 + zq.a1 * (zq.sub zv).c1)| + 18 * 10 ^ 74)
            (|zq.d0 * (zq.sub zv).a0 + zq.d1 * (zq.sub zv).a1
              + 2 * (zq.b0 * (zq.sub zv).b0 + zq.b1 * (zq.sub zv).b1)
              + (zq.a0 * (zq.sub zv).d0 + zq.a1 * (zq.sub zv).d1)| + 36 * 10 ^ 74)
            (|zq.e0 * (zq.sub zv).a0 + zq.e1 * (zq.sub zv).a1
              + (zq.b0 * (zq.sub zv).c0 + zq.b1 * (zq.sub zv).c1)
              + (zq.c0 * (zq.sub zv).b0 + zq.c1 * (zq.sub zv).b1)
              + (zq.a0 * (zq.sub zv).e0 + zq.a1 * (zq.sub zv).e1)| + 36 * 10 ^ 74)
            (|zq.f0 * (zq.sub zv).a0 + zq.f1 * (zq.sub zv).a1
              + 2 * (zq.c0 * (zq.sub zv).c0 + zq.c1 * (zq.sub zv).c1)
              + (zq.a0 * (zq.sub zv).f0 + zq.a1 * (zq.sub zv).f1)| + 36 * 10 ^ 74)
            (8 * nrmZ * 10 ^ 68) εθ.num (εθ.den : ℤ) εφ.num (εφ.den : ℤ))
      = 6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * (zq.a0 * (zq.sub zv).a0 + zq.a1 * (zq.sub zv).a1)
        - 6 * ((εθ.den : ℤ) * εφ.den) ^ 3 * (9 * 10 ^ 74)
        - budN (|zq.b0 * (zq.sub zv).a0 + zq.b1 * (zq.sub zv).a1
              + (zq.a0 * (zq.sub zv).b0 + zq.a1 * (zq.sub zv).b1)| + 18 * 10 ^ 74)
            (|zq.c0 * (zq.sub zv).a0 + zq.c1 * (zq.sub zv).a1
              + (zq.a0 * (zq.sub zv).c0 + zq.a1 * (zq.sub zv).c1)| + 18 * 10 ^ 74)
            (|zq.d0 * (zq.sub zv).a0 + zq.d1 * (zq.sub zv).a1
              + 2 * (zq.b0 * (zq.sub zv).b0 + zq.b1 * (zq.sub zv).b1)
              + (zq.a0 * (zq.sub zv).d0 + zq.a1 * (zq.sub zv).d1)| + 36 * 10 ^ 74)
            (|zq.e0 * (zq.sub zv).a0 + zq.e1 * (zq.sub zv).a1
              + (zq.b0 * (zq.sub zv).c0 + zq.b1 * (zq.sub zv).c1)
              + (zq.c0 * (zq.sub zv).b0 + zq.c1 * (zq.sub zv).b1)
              + (zq.a0 * (zq.sub zv).e0 + zq.a1 * (zq.sub zv).e1)| + 36 * 10 ^ 74)
            (|zq.f0 * (zq.sub zv).a0 + zq.f1 * (zq.sub zv).a1
              + 2 * (zq.c0 * (zq.sub zv).c0 + zq.c1 * (zq.sub zv).c1)
              + (zq.a0 * (zq.sub zv).f0 + zq.a1 * (zq.sub zv).f1)| + 36 * 10 ^ 74)
            (8 * nrmZ * 10 ^ 68) εθ.num (εθ.den : ℤ) εφ.num (εφ.den : ℤ) := by
    linear_combination (6 * ((εθ.den : ℤ) * εφ.den) ^ 3) * hmd
  -- D2 square-argument casts
  have Sa2 : ((Nat.add (sqdO da0) (sqdO da1) : ℕ) : ℤ)
      = (zq.sub zv).a0 * (zq.sub zv).a0 + (zq.sub zv).a1 * (zq.sub zv).a1 := by
    simp only [natAdd_eq]; push_cast; rw [sqdO_cast hda0 rfl, sqdO_cast hda1 rfl]
  have Sb2 : ((Nat.add (sqdO db0) (sqdO db1) : ℕ) : ℤ)
      = (zq.sub zv).b0 * (zq.sub zv).b0 + (zq.sub zv).b1 * (zq.sub zv).b1 := by
    simp only [natAdd_eq]; push_cast; rw [sqdO_cast hdb0 rfl, sqdO_cast hdb1 rfl]
  have Sd2 : ((Nat.add (sqdO dd0) (sqdO dd1) : ℕ) : ℤ)
      = (zq.sub zv).d0 * (zq.sub zv).d0 + (zq.sub zv).d1 * (zq.sub zv).d1 := by
    simp only [natAdd_eq]; push_cast; rw [sqdO_cast hdd0 rfl, sqdO_cast hdd1 rfl]
  have Sc2 : ((sqdO dc1 : ℕ) : ℤ)
      = (zq.sub zv).c0 * (zq.sub zv).c0 + (zq.sub zv).c1 * (zq.sub zv).c1 := by
    rw [sqdO_cast hdc1 rfl, show (zq.sub zv).c0 = zq.c0 - zv.c0 from rfl, hzc0, hvc0]
    ring
  have Se2 : ((sqdO de1 : ℕ) : ℤ)
      = (zq.sub zv).e0 * (zq.sub zv).e0 + (zq.sub zv).e1 * (zq.sub zv).e1 := by
    rw [sqdO_cast hde1 rfl, show (zq.sub zv).e0 = zq.e0 - zv.e0 from rfl, hze0, hve0]
    ring
  have Sf2 : ((sqdO df1 : ℕ) : ℤ)
      = (zq.sub zv).f0 * (zq.sub zv).f0 + (zq.sub zv).f1 * (zq.sub zv).f1 := by
    rw [sqdO_cast hdf1 rfl, show (zq.sub zv).f0 = zq.f0 - zv.f0 from rfl, hzf0, hvf0]
    ring
  have nA := nUpO84_dom Sa2
  have nB := nUpO84_dom Sb2
  have nC := nUpO84_dom Sc2
  have nD := nUpO84_dom Sd2
  have nE := nUpO84_dom Se2
  have nF := nUpO84_dom Sf2
  -- D2 domination (expanded-cast form)
  have hD2 : 6 * ((εθ.den : ℤ) * εφ.den) ^ 3
        * (sqrtNum84 ((zq.sub zv).a0 * (zq.sub zv).a0 + (zq.sub zv).a1 * (zq.sub zv).a1)
          + 5 * 10 ^ 6)
      + budN (sqrtNum84 ((zq.sub zv).b0 * (zq.sub zv).b0 + (zq.sub zv).b1 * (zq.sub zv).b1)
            + 5 * 10 ^ 6)
          (sqrtNum84 ((zq.sub zv).c0 * (zq.sub zv).c0 + (zq.sub zv).c1 * (zq.sub zv).c1)
            + 5 * 10 ^ 6)
          (sqrtNum84 ((zq.sub zv).d0 * (zq.sub zv).d0 + (zq.sub zv).d1 * (zq.sub zv).d1)
            + 5 * 10 ^ 6)
          (sqrtNum84 ((zq.sub zv).e0 * (zq.sub zv).e0 + (zq.sub zv).e1 * (zq.sub zv).e1)
            + 5 * 10 ^ 6)
          (sqrtNum84 ((zq.sub zv).f0 * (zq.sub zv).f0 + (zq.sub zv).f1 * (zq.sub zv).f1)
            + 5 * 10 ^ 6) nrmZ εθ.num (εθ.den : ℤ) εφ.num (εφ.den : ℤ)
      ≤ (6 * ((εθ.den : ℤ) * εφ.den) ^ 3)
          * (((nUpO84 (Nat.add (sqdO da0) (sqdO da1)) : ℕ) : ℤ) + 5 * 10 ^ 6)
        + budN (((nUpO84 (Nat.add (sqdO db0) (sqdO db1)) : ℕ) : ℤ) + 5 * 10 ^ 6)
            (((nUpO84 (sqdO dc1) : ℕ) : ℤ) + 5 * 10 ^ 6)
            (((nUpO84 (Nat.add (sqdO dd0) (sqdO dd1)) : ℕ) : ℤ) + 5 * 10 ^ 6)
            (((nUpO84 (sqdO de1) : ℕ) : ℤ) + 5 * 10 ^ 6)
            (((nUpO84 (sqdO df1) : ℕ) : ℤ) + 5 * 10 ^ 6) nrmZ
            εθ.num (εθ.den : ℤ) εφ.num (εφ.den : ℤ) := by
    refine add_le_add (mul_le_mul_of_nonneg_left (add_le_add nA (le_refl _)) hWnn) ?_
    exact budN_mono hεθ hed hεφ hfd (add_le_add nB (le_refl _)) (add_le_add nC (le_refl _))
      (add_le_add nD (le_refl _)) (add_le_add nE (le_refl _)) (add_le_add nF (le_refl _))
      (le_refl _)
  -- nonnegativity of the exact D's
  have hD1Enn : (0 : ℤ) ≤ 6 * ((εθ.den : ℤ) * εφ.den) ^ 3
        * (sqrtNum84 (zq.a0 * zq.a0 + zq.a1 * zq.a1) + 3 * 10 ^ 6)
      + budN (sqrtNum84 (zq.b0 * zq.b0 + zq.b1 * zq.b1) + 3 * 10 ^ 6)
          (sqrtNum84 (zq.c0 * zq.c0 + zq.c1 * zq.c1) + 3 * 10 ^ 6)
          (sqrtNum84 (zq.d0 * zq.d0 + zq.d1 * zq.d1) + 3 * 10 ^ 6)
          (sqrtNum84 (zq.e0 * zq.e0 + zq.e1 * zq.e1) + 3 * 10 ^ 6)
          (sqrtNum84 (zq.f0 * zq.f0 + zq.f1 * zq.f1) + 3 * 10 ^ 6) (10 ^ 16)
          εθ.num (εθ.den : ℤ) εφ.num (εφ.den : ℤ) := by
    refine add_nonneg (mul_nonneg hWnn
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))) ?_
    exact budN_nonneg hεθ hed hεφ hfd
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num)) (by norm_num)
  have hnrmZnn : (0 : ℤ) ≤ nrmZ := by rw [← hnrm]; positivity
  have hD2Enn : (0 : ℤ) ≤ 6 * ((εθ.den : ℤ) * εφ.den) ^ 3
        * (sqrtNum84 ((zq.sub zv).a0 * (zq.sub zv).a0 + (zq.sub zv).a1 * (zq.sub zv).a1)
          + 5 * 10 ^ 6)
      + budN (sqrtNum84 ((zq.sub zv).b0 * (zq.sub zv).b0 + (zq.sub zv).b1 * (zq.sub zv).b1)
            + 5 * 10 ^ 6)
          (sqrtNum84 ((zq.sub zv).c0 * (zq.sub zv).c0 + (zq.sub zv).c1 * (zq.sub zv).c1)
            + 5 * 10 ^ 6)
          (sqrtNum84 ((zq.sub zv).d0 * (zq.sub zv).d0 + (zq.sub zv).d1 * (zq.sub zv).d1)
            + 5 * 10 ^ 6)
          (sqrtNum84 ((zq.sub zv).e0 * (zq.sub zv).e0 + (zq.sub zv).e1 * (zq.sub zv).e1)
            + 5 * 10 ^ 6)
          (sqrtNum84 ((zq.sub zv).f0 * (zq.sub zv).f0 + (zq.sub zv).f1 * (zq.sub zv).f1)
            + 5 * 10 ^ 6) nrmZ εθ.num (εθ.den : ℤ) εφ.num (εφ.den : ℤ) := by
    refine add_nonneg (mul_nonneg hWnn
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))) ?_
    exact budN_nonneg hεθ hed hεφ hfd
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num))
      (add_nonneg (sqrtNum84_nonneg _) (by norm_num)) hnrmZnn
  -- cast h1 and h2, distributing only the outer coercions
  have cAdd : ∀ a b : ℕ, ((Nat.add a b : ℕ) : ℤ) = (a : ℤ) + b := fun a b => by
    simp only [natAdd_eq]; push_cast; ring
  have cMul : ∀ a b : ℕ, ((Nat.mul a b : ℕ) : ℤ) = (a : ℤ) * b := fun a b => by
    simp only [natMul_eq]; push_cast; ring
  have h1' := (Nat.cast_lt (α := ℤ)).mpr h1
  simp only [cAdd, cMul] at h1'
  rw [We, e9, budO_cast k1e k2e k3e k4e k5e k6e, t1e, t2e, t3e, t4e, t5e, hrem] at h1'
  have h2' := (Nat.cast_lt (α := ℤ)).mpr h2
  simp only [cAdd, cMul] at h2'
  rw [We, e9, e65, cLe, cRe, budO_cast k1e k2e k3e k4e k5e k6e,
    budO_cast k1e k2e k3e k4e k5e k6e, t1e, t2e, t3e, t4e, t5e, hrem, hnrm] at h2'
  simp only [cAdd, e65] at h2'
  refine be_pair_mono (le_of_eq hAB) hD1 hD2 hD1Enn hD2Enn hδ (Int.natCast_nonneg _)
    (Int.natCast_nonneg _) hr.le hWnn ?_ ?_
  · linarith
  · ring_nf at h2' ⊢
    linarith [h2']



/-- Flat indices are below 90. -/
private lemma flatIx_lt (k : VertexIndex) : flatIx k < 90 := by
  have h1 := k.ℓ.isLt
  have h2 := k.i.isLt
  have h3 := k.k.isLt
  unfold flatIx
  omega

/-- Distinct vertices have distinct flat indices. -/
private lemma flatIx_ne {k q : VertexIndex} (h : k ≠ q) : flatIx k ≠ flatIx q :=
  fun he => h (VertexIndex.flat_inj k q he)

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 65536 in
set_option exponentiation.threshold 5200 in
/-- The offset tier is sound: `beFastO = true` implies `beCheckN = true`,
with no side conditions (the guards are part of `beFastO`). -/
theorem beFastO_imp_beCheckN {Qi : Fin 3 → VertexIndex} {p : Pose ℚ} {εθ εφ δ r : ℚ}
    (h : beFastO Qi p εθ εφ δ r = true) : beCheckN Qi p εθ εφ δ r = true := by
  unfold beFastO at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, forall_const] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hst, hct⟩, hsf⟩, hcf⟩, hεθ⟩, hεφ⟩, hδ⟩, hr⟩, hloop⟩ := h
  unfold beCheckN beCheckNCore
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]
  intro i k hk
  have hpair := pairLoopO_forall (hloop i) (flatIx k) (flatIx_lt k) (flatIx_ne hk)
  unfold pairO at hpair
  -- names
  have hK := mkRCO_casts (stN := RationalApprox.sinNum13 p.θ₂)
    (ctN := RationalApprox.cosNum13 p.θ₂) (sfN := RationalApprox.sinNum13 p.φ₂)
    (cfN := RationalApprox.cosNum13 p.φ₂) (δ := δ) (r := r) hεθ hεφ hδ hr
  dsimp only at hK
  obtain ⟨k1e, k2e, k3e, k4e, k5e, k6e, We, cLe, cRe⟩ := hK
  have hAq := appO_bridge hst hct hsf hcf εθ εφ δ r (Qi i)
  have hAv := appO_bridge hst hct hsf hcf εθ εφ δ r k
  dsimp only at hAq hAv
  obtain ⟨⟨qa0e, qa0b⟩, ⟨qa1e, qa1b⟩, ⟨qb0e, qb0b⟩, ⟨qb1e, qb1b⟩, ⟨qc1e, qc1b⟩,
    ⟨qd0e, qd0b⟩, ⟨qd1e, qd1b⟩, ⟨qe1e, qe1b⟩, ⟨qf1e, qf1b⟩⟩ := hAq
  obtain ⟨⟨va0e, va0b⟩, ⟨va1e, va1b⟩, ⟨vb0e, vb0b⟩, ⟨vb1e, vb1b⟩, ⟨vc1e, vc1b⟩,
    ⟨vd0e, vd0b⟩, ⟨vd1e, vd1b⟩, ⟨ve1e, ve1b⟩, ⟨vf1e, vf1b⟩⟩ := hAv
  have e63 : ((E6x3 : ℕ) : ℤ) = 3 * 10 ^ 6 := by norm_num [E6x3, Nat.pow_eq]
  have e62 : ((E6x2 : ℕ) : ℤ) = 2 * 10 ^ 6 := by norm_num [E6x2, Nat.pow_eq]
  have e16 : ((E16 : ℕ) : ℤ) = 10 ^ 16 := by norm_num [E16, Nat.pow_eq]
  have cAdd : ∀ a b : ℕ, ((Nat.add a b : ℕ) : ℤ) = (a : ℤ) + b := fun a b => by
    simp only [natAdd_eq]; push_cast; ring
  have cMul : ∀ a b : ℕ, ((Nat.mul a b : ℕ) : ℤ) = (a : ℤ) * b := fun a b => by
    simp only [natMul_eq]; push_cast; ring
  have hWnn : (0 : ℤ) ≤ 6 * ((εθ.den : ℤ) * εφ.den) ^ 3 := by positivity
  have hed : (0 : ℤ) ≤ (εθ.den : ℤ) := Int.natCast_nonneg _
  have hfd : (0 : ℤ) ≤ (εφ.den : ℤ) := Int.natCast_nonneg _
  -- compact names
  set rc : RCO := mkRCO (RationalApprox.sinNum13 p.θ₂) (RationalApprox.cosNum13 p.θ₂)
    (RationalApprox.sinNum13 p.φ₂) (RationalApprox.cosNum13 p.φ₂) εθ εφ δ r with hrc
  set Q : A6O := appO rc (flatIx (Qi i)) with hQdef
  set v : A6O := appO rc (flatIx k) with hvdef
  set zq : App6N := app6N (RationalApprox.sinNum13 p.θ₂) (RationalApprox.cosNum13 p.θ₂)
    (RationalApprox.sinNum13 p.φ₂) (RationalApprox.cosNum13 p.φ₂) (Qi i) with hzq
  set zv : App6N := app6N (RationalApprox.sinNum13 p.θ₂) (RationalApprox.cosNum13 p.θ₂)
    (RationalApprox.sinNum13 p.φ₂) (RationalApprox.cosNum13 p.φ₂) k with hzv
  -- qcO projections (definitional)
  have pj : (qcO rc (flatIx (Qi i))).a0P = Q.a0 - BFO ∧
      (qcO rc (flatIx (Qi i))).a0N = BFO - Q.a0 ∧
      (qcO rc (flatIx (Qi i))).a1P = Q.a1 - BFO ∧
      (qcO rc (flatIx (Qi i))).a1N = BFO - Q.a1 ∧
      (qcO rc (flatIx (Qi i))).b0P = Q.b0 - BFO ∧
      (qcO rc (flatIx (Qi i))).b0N = BFO - Q.b0 ∧
      (qcO rc (flatIx (Qi i))).b1P = Q.b1 - BFO ∧
      (qcO rc (flatIx (Qi i))).b1N = BFO - Q.b1 ∧
      (qcO rc (flatIx (Qi i))).c1P = Q.c1 - BFO ∧
      (qcO rc (flatIx (Qi i))).c1N = BFO - Q.c1 ∧
      (qcO rc (flatIx (Qi i))).d0P = Q.d0 - BFO ∧
      (qcO rc (flatIx (Qi i))).d0N = BFO - Q.d0 ∧
      (qcO rc (flatIx (Qi i))).d1P = Q.d1 - BFO ∧
      (qcO rc (flatIx (Qi i))).d1N = BFO - Q.d1 ∧
      (qcO rc (flatIx (Qi i))).e1P = Q.e1 - BFO ∧
      (qcO rc (flatIx (Qi i))).e1N = BFO - Q.e1 ∧
      (qcO rc (flatIx (Qi i))).f1P = Q.f1 - BFO ∧
      (qcO rc (flatIx (Qi i))).f1N = BFO - Q.f1 := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  obtain ⟨pa0P, pa0N, pa1P, pa1N, pb0P, pb0N, pb1P, pb1N, pc1P, pc1N,
    pd0P, pd0N, pd1P, pd1N, pe1P, pe1N, pf1P, pf1N⟩ := pj
  -- splits
  have sa0d : ((qcO rc (flatIx (Qi i))).a0P : ℤ) - (qcO rc (flatIx (Qi i))).a0N
      = zq.a0 := by rw [pa0P, pa0N]; exact (split_facts qa0e).1
  have sa1d : ((qcO rc (flatIx (Qi i))).a1P : ℤ) - (qcO rc (flatIx (Qi i))).a1N
      = zq.a1 := by rw [pa1P, pa1N]; exact (split_facts qa1e).1
  have sb0d : ((qcO rc (flatIx (Qi i))).b0P : ℤ) - (qcO rc (flatIx (Qi i))).b0N
      = zq.b0 := by rw [pb0P, pb0N]; exact (split_facts qb0e).1
  have sb1d : ((qcO rc (flatIx (Qi i))).b1P : ℤ) - (qcO rc (flatIx (Qi i))).b1N
      = zq.b1 := by rw [pb1P, pb1N]; exact (split_facts qb1e).1
  have sc1d : ((qcO rc (flatIx (Qi i))).c1P : ℤ) - (qcO rc (flatIx (Qi i))).c1N
      = zq.c1 := by rw [pc1P, pc1N]; exact (split_facts qc1e).1
  have sd0d : ((qcO rc (flatIx (Qi i))).d0P : ℤ) - (qcO rc (flatIx (Qi i))).d0N
      = zq.d0 := by rw [pd0P, pd0N]; exact (split_facts qd0e).1
  have sd1d : ((qcO rc (flatIx (Qi i))).d1P : ℤ) - (qcO rc (flatIx (Qi i))).d1N
      = zq.d1 := by rw [pd1P, pd1N]; exact (split_facts qd1e).1
  have se1d : ((qcO rc (flatIx (Qi i))).e1P : ℤ) - (qcO rc (flatIx (Qi i))).e1N
      = zq.e1 := by rw [pe1P, pe1N]; exact (split_facts qe1e).1
  have sf1d : ((qcO rc (flatIx (Qi i))).f1P : ℤ) - (qcO rc (flatIx (Qi i))).f1N
      = zq.f1 := by rw [pf1P, pf1N]; exact (split_facts qf1e).1
  -- offset-correction constants
  have xm1 : (((qcO rc (flatIx (Qi i))).xmP : ℕ) : ℤ)
      = BFO * (((qcO rc (flatIx (Qi i))).a0P : ℤ) + ((qcO rc (flatIx (Qi i))).a1P : ℤ)) := by
    simp only [qcO]
    simp only [natAdd_eq, natMul_eq]
    push_cast
    ring
  have xm2 : (((qcO rc (flatIx (Qi i))).xmN : ℕ) : ℤ)
      = BFO * (((qcO rc (flatIx (Qi i))).a0N : ℤ) + ((qcO rc (flatIx (Qi i))).a1N : ℤ)) := by
    simp only [qcO]
    simp only [natAdd_eq, natMul_eq]
    push_cast
    ring
  have x11 : (((qcO rc (flatIx (Qi i))).x1P : ℕ) : ℤ)
      = BFO * (((qcO rc (flatIx (Qi i))).b0P : ℤ) + ((qcO rc (flatIx (Qi i))).b1P : ℤ) + ((qcO rc (flatIx (Qi i))).a0P : ℤ) + ((qcO rc (flatIx (Qi i))).a1P : ℤ)) := by
    simp only [qcO]
    simp only [natAdd_eq, natMul_eq]
    push_cast
    ring
  have x12 : (((qcO rc (flatIx (Qi i))).x1N : ℕ) : ℤ)
      = BFO * (((qcO rc (flatIx (Qi i))).b0N : ℤ) + ((qcO rc (flatIx (Qi i))).b1N : ℤ) + ((qcO rc (flatIx (Qi i))).a0N : ℤ) + ((qcO rc (flatIx (Qi i))).a1N : ℤ)) := by
    simp only [qcO]
    simp only [natAdd_eq, natMul_eq]
    push_cast
    ring
  have x21 : (((qcO rc (flatIx (Qi i))).x2P : ℕ) : ℤ)
      = BFO * (((qcO rc (flatIx (Qi i))).c1P : ℤ) + ((qcO rc (flatIx (Qi i))).a1P : ℤ)) := by
    simp only [qcO]
    simp only [natAdd_eq, natMul_eq]
    push_cast
    ring
  have x22 : (((qcO rc (flatIx (Qi i))).x2N : ℕ) : ℤ)
      = BFO * (((qcO rc (flatIx (Qi i))).c1N : ℤ) + ((qcO rc (flatIx (Qi i))).a1N : ℤ)) := by
    simp only [qcO]
    simp only [natAdd_eq, natMul_eq]
    push_cast
    ring
  have x31 : (((qcO rc (flatIx (Qi i))).x3P : ℕ) : ℤ)
      = BFO * (((qcO rc (flatIx (Qi i))).d0P : ℤ) + ((qcO rc (flatIx (Qi i))).d1P : ℤ) + 2 * ((qcO rc (flatIx (Qi i))).b0P : ℤ) + 2 * ((qcO rc (flatIx (Qi i))).b1P : ℤ) + ((qcO rc (flatIx (Qi i))).a0P : ℤ) + ((qcO rc (flatIx (Qi i))).a1P : ℤ)) := by
    simp only [qcO]
    simp only [natAdd_eq, natMul_eq]
    push_cast
    ring
  have x32 : (((qcO rc (flatIx (Qi i))).x3N : ℕ) : ℤ)
      = BFO * (((qcO rc (flatIx (Qi i))).d0N : ℤ) + ((qcO rc (flatIx (Qi i))).d1N : ℤ) + 2 * ((qcO rc (flatIx (Qi i))).b0N : ℤ) + 2 * ((qcO rc (flatIx (Qi i))).b1N : ℤ) + ((qcO rc (flatIx (Qi i))).a0N : ℤ) + ((qcO rc (flatIx (Qi i))).a1N : ℤ)) := by
    simp only [qcO]
    simp only [natAdd_eq, natMul_eq]
    push_cast
    ring
  have x41 : (((qcO rc (flatIx (Qi i))).x4P : ℕ) : ℤ)
      = BFO * (((qcO rc (flatIx (Qi i))).e1P : ℤ) + ((qcO rc (flatIx (Qi i))).b1P : ℤ) + ((qcO rc (flatIx (Qi i))).c1P : ℤ) + ((qcO rc (flatIx (Qi i))).a1P : ℤ)) := by
    simp only [qcO]
    simp only [natAdd_eq, natMul_eq]
    push_cast
    ring
  have x42 : (((qcO rc (flatIx (Qi i))).x4N : ℕ) : ℤ)
      = BFO * (((qcO rc (flatIx (Qi i))).e1N : ℤ) + ((qcO rc (flatIx (Qi i))).b1N : ℤ) + ((qcO rc (flatIx (Qi i))).c1N : ℤ) + ((qcO rc (flatIx (Qi i))).a1N : ℤ)) := by
    simp only [qcO]
    simp only [natAdd_eq, natMul_eq]
    push_cast
    ring
  have x51 : (((qcO rc (flatIx (Qi i))).x5P : ℕ) : ℤ)
      = BFO * (((qcO rc (flatIx (Qi i))).f1P : ℤ) + 2 * ((qcO rc (flatIx (Qi i))).c1P : ℤ) + ((qcO rc (flatIx (Qi i))).a1P : ℤ)) := by
    simp only [qcO]
    simp only [natAdd_eq, natMul_eq]
    push_cast
    ring
  have x52 : (((qcO rc (flatIx (Qi i))).x5N : ℕ) : ℤ)
      = BFO * (((qcO rc (flatIx (Qi i))).f1N : ℤ) + 2 * ((qcO rc (flatIx (Qi i))).c1N : ℤ) + ((qcO rc (flatIx (Qi i))).a1N : ℤ)) := by
    simp only [qcO]
    simp only [natAdd_eq, natMul_eq]
    push_cast
    ring
  -- offset differences
  have hda0 : (((qcO rc (flatIx (Qi i))).pa0 - v.a0 : ℕ) : ℤ) = (zq.sub zv).a0 + BFO := by
    rw [show (qcO rc (flatIx (Qi i))).pa0 = Nat.add Q.a0 BFO from rfl,
      show (zq.sub zv).a0 = zq.a0 - zv.a0 from rfl]
    exact dsub_cast qa0e va0e qa0b va0b
  have hda1 : (((qcO rc (flatIx (Qi i))).pa1 - v.a1 : ℕ) : ℤ) = (zq.sub zv).a1 + BFO := by
    rw [show (qcO rc (flatIx (Qi i))).pa1 = Nat.add Q.a1 BFO from rfl,
      show (zq.sub zv).a1 = zq.a1 - zv.a1 from rfl]
    exact dsub_cast qa1e va1e qa1b va1b
  have hdb0 : (((qcO rc (flatIx (Qi i))).pb0 - v.b0 : ℕ) : ℤ) = (zq.sub zv).b0 + BFO := by
    rw [show (qcO rc (flatIx (Qi i))).pb0 = Nat.add Q.b0 BFO from rfl,
      show (zq.sub zv).b0 = zq.b0 - zv.b0 from rfl]
    exact dsub_cast qb0e vb0e qb0b vb0b
  have hdb1 : (((qcO rc (flatIx (Qi i))).pb1 - v.b1 : ℕ) : ℤ) = (zq.sub zv).b1 + BFO := by
    rw [show (qcO rc (flatIx (Qi i))).pb1 = Nat.add Q.b1 BFO from rfl,
      show (zq.sub zv).b1 = zq.b1 - zv.b1 from rfl]
    exact dsub_cast qb1e vb1e qb1b vb1b
  have hdc1 : (((qcO rc (flatIx (Qi i))).pc1 - v.c1 : ℕ) : ℤ) = (zq.sub zv).c1 + BFO := by
    rw [show (qcO rc (flatIx (Qi i))).pc1 = Nat.add Q.c1 BFO from rfl,
      show (zq.sub zv).c1 = zq.c1 - zv.c1 from rfl]
    exact dsub_cast qc1e vc1e qc1b vc1b
  have hdd0 : (((qcO rc (flatIx (Qi i))).pd0 - v.d0 : ℕ) : ℤ) = (zq.sub zv).d0 + BFO := by
    rw [show (qcO rc (flatIx (Qi i))).pd0 = Nat.add Q.d0 BFO from rfl,
      show (zq.sub zv).d0 = zq.d0 - zv.d0 from rfl]
    exact dsub_cast qd0e vd0e qd0b vd0b
  have hdd1 : (((qcO rc (flatIx (Qi i))).pd1 - v.d1 : ℕ) : ℤ) = (zq.sub zv).d1 + BFO := by
    rw [show (qcO rc (flatIx (Qi i))).pd1 = Nat.add Q.d1 BFO from rfl,
      show (zq.sub zv).d1 = zq.d1 - zv.d1 from rfl]
    exact dsub_cast qd1e vd1e qd1b vd1b
  have hde1 : (((qcO rc (flatIx (Qi i))).pe1 - v.e1 : ℕ) : ℤ) = (zq.sub zv).e1 + BFO := by
    rw [show (qcO rc (flatIx (Qi i))).pe1 = Nat.add Q.e1 BFO from rfl,
      show (zq.sub zv).e1 = zq.e1 - zv.e1 from rfl]
    exact dsub_cast qe1e ve1e qe1b ve1b
  have hdf1 : (((qcO rc (flatIx (Qi i))).pf1 - v.f1 : ℕ) : ℤ) = (zq.sub zv).f1 + BFO := by
    rw [show (qcO rc (flatIx (Qi i))).pf1 = Nat.add Q.f1 BFO from rfl,
      show (zq.sub zv).f1 = zq.f1 - zv.f1 from rfl]
    exact dsub_cast qf1e vf1e qf1b vf1b
  -- pair norm from the packed table
  have hnrm : ((Nat.add (Nat.land (Nat.shiftRight (qcO rc (flatIx (Qi i))).qrow
      (Nat.mul 57 (flatIx k))) M57) E6x2 : ℕ) : ℤ)
      = sqrtDvCurriedN (Qi i).ℓ (Qi i).i (Qi i).k k.ℓ k.i k.k + 2 * 10 ^ 6 := by
    have hs := sqrtDvBig_spec (Qi i).ℓ (Qi i).i (Qi i).k k.ℓ k.i k.k
    dsimp only at hs
    rw [cAdd, e62,
      show (qcO rc (flatIx (Qi i))).qrow = Nat.land (Nat.shiftRight sqrtDvBig
        (Nat.mul 5130 (flatIx (Qi i)))) M5130 from rfl,
      show M5130 = 2 ^ 5130 - 1 from by norm_num [M5130, Nat.pow_eq],
      show M57 = 2 ^ 57 - 1 from by norm_num [M57, Nat.pow_eq],
      show flatIx (Qi i) = 45 * (Qi i).ℓ.val + 15 * (Qi i).i.val + (Qi i).k.val from rfl,
      show flatIx k = 45 * k.ℓ.val + 15 * k.i.val + k.k.val from rfl, hs]
  -- D1 domination
  have T1 : ((Nat.add (sqsO (Q.a0 - BFO) (BFO - Q.a0)) (sqsO (Q.a1 - BFO) (BFO - Q.a1)) : ℕ) : ℤ)
      = zq.a0 * zq.a0 + zq.a1 * zq.a1 := by
    rw [cAdd, sqsO_cast (split_facts qa0e).1 (split_facts qa0e).2,
      sqsO_cast (split_facts qa1e).1 (split_facts qa1e).2]
  have T2 : ((Nat.add (sqsO (Q.b0 - BFO) (BFO - Q.b0)) (sqsO (Q.b1 - BFO) (BFO - Q.b1)) : ℕ) : ℤ)
      = zq.b0 * zq.b0 + zq.b1 * zq.b1 := by
    rw [cAdd, sqsO_cast (split_facts qb0e).1 (split_facts qb0e).2,
      sqsO_cast (split_facts qb1e).1 (split_facts qb1e).2]
  have T4 : ((Nat.add (sqsO (Q.d0 - BFO) (BFO - Q.d0)) (sqsO (Q.d1 - BFO) (BFO - Q.d1)) : ℕ) : ℤ)
      = zq.d0 * zq.d0 + zq.d1 * zq.d1 := by
    rw [cAdd, sqsO_cast (split_facts qd0e).1 (split_facts qd0e).2,
      sqsO_cast (split_facts qd1e).1 (split_facts qd1e).2]
  have T3 : ((sqsO (Q.c1 - BFO) (BFO - Q.c1) : ℕ) : ℤ)
      = zq.c0 * zq.c0 + zq.c1 * zq.c1 := by
    rw [sqsO_cast (split_facts qc1e).1 (split_facts qc1e).2,
      show zq.c0 = 0 from rfl]
    ring
  have T5 : ((sqsO (Q.e1 - BFO) (BFO - Q.e1) : ℕ) : ℤ)
      = zq.e0 * zq.e0 + zq.e1 * zq.e1 := by
    rw [sqsO_cast (split_facts qe1e).1 (split_facts qe1e).2,
      show zq.e0 = 0 from rfl]
    ring
  have T6 : ((sqsO (Q.f1 - BFO) (BFO - Q.f1) : ℕ) : ℤ)
      = zq.f0 * zq.f0 + zq.f1 * zq.f1 := by
    rw [sqsO_cast (split_facts qf1e).1 (split_facts qf1e).2,
      show zq.f0 = 0 from rfl]
    ring
  have hD1 : 6 * ((εθ.den : ℤ) * εφ.den) ^ 3
        * (sqrtNum84 (zq.a0 * zq.a0 + zq.a1 * zq.a1) + 3 * 10 ^ 6)
      + budN (sqrtNum84 (zq.b0 * zq.b0 + zq.b1 * zq.b1) + 3 * 10 ^ 6)
          (sqrtNum84 (zq.c0 * zq.c0 + zq.c1 * zq.c1) + 3 * 10 ^ 6)
          (sqrtNum84 (zq.d0 * zq.d0 + zq.d1 * zq.d1) + 3 * 10 ^ 6)
          (sqrtNum84 (zq.e0 * zq.e0 + zq.e1 * zq.e1) + 3 * 10 ^ 6)
          (sqrtNum84 (zq.f0 * zq.f0 + zq.f1 * zq.f1) + 3 * 10 ^ 6) (10 ^ 16)
          εθ.num (εθ.den : ℤ) εφ.num (εφ.den : ℤ)
      ≤ ((qcO rc (flatIx (Qi i))).D1N : ℤ) := by
    rw [show (qcO rc (flatIx (Qi i))).D1N = Nat.add (Nat.mul rc.W (Nat.add (nUpO84
        (Nat.add (sqsO (Q.a0 - BFO) (BFO - Q.a0)) (sqsO (Q.a1 - BFO) (BFO - Q.a1)))) E6x3))
      (budO rc.k1 rc.k2 rc.k3 rc.k4 rc.k5 rc.k6
        (Nat.add (nUpO84 (Nat.add (sqsO (Q.b0 - BFO) (BFO - Q.b0))
          (sqsO (Q.b1 - BFO) (BFO - Q.b1)))) E6x3)
        (Nat.add (nUpO84 (sqsO (Q.c1 - BFO) (BFO - Q.c1))) E6x3)
        (Nat.add (nUpO84 (Nat.add (sqsO (Q.d0 - BFO) (BFO - Q.d0))
          (sqsO (Q.d1 - BFO) (BFO - Q.d1)))) E6x3)
        (Nat.add (nUpO84 (sqsO (Q.e1 - BFO) (BFO - Q.e1))) E6x3)
        (Nat.add (nUpO84 (sqsO (Q.f1 - BFO) (BFO - Q.f1))) E6x3) E16) from rfl]
    simp only [cAdd, cMul]
    rw [We, budO_cast k1e k2e k3e k4e k5e k6e]
    simp only [cAdd, e63, e16]
    refine add_le_add (mul_le_mul_of_nonneg_left
      (add_le_add (nUpO84_dom T1) (le_refl _)) hWnn) ?_
    exact budN_mono hεθ hed hεφ hfd (add_le_add (nUpO84_dom T2) (le_refl _))
      (add_le_add (nUpO84_dom T3) (le_refl _)) (add_le_add (nUpO84_dom T4) (le_refl _))
      (add_le_add (nUpO84_dom T5) (le_refl _)) (add_le_add (nUpO84_dom T6) (le_refl _))
      (le_refl _)
  exact pairCore_sound hεθ hεφ hδ hr k1e k2e k3e k4e k5e k6e We cLe cRe
    sa0d sa1d sb0d sb1d sc1d sd0d sd1d se1d sf1d xm1 xm2 x11 x12 x21 x22
    x31 x32 x41 x42 x51 x52 hda0 hda1 hdb0 hdb1 hdc1 hdd0 hdd1 hde1 hdf1
    hnrm rfl rfl rfl rfl rfl rfl hD1 hpair

end OffsetSound

/-- The offset tier first; on rejection fall back to the `Int` tiers of
`instDecidableBε₂N` (Newton, exact, then ℚ). -/
instance (priority := 10700) instDecidableBε₂O (Qi : Fin 3 → VertexIndex)
    (p : Pose ℚ) (εθ εφ δ r : ℚ) :
    Decidable (Local.TriangleQ.Bε₂ℚ Qi pythonVertexA p εθ εφ δ r
      RationalApprox.sqrtApprox16.upper_sqrt) :=
  dite (beFastO Qi p εθ εφ δ r = true)
    (fun hf => .isTrue (by
      have hg := hf
      unfold beFastO at hg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hεθ⟩, hεφ⟩, hδ⟩, hr⟩, _⟩ := hg
      exact (Local2Fast.beCheck_iff Qi p εθ εφ δ r).mp
        (beCheckN_eq Qi p δ (Rat.num_nonneg.mp hεθ) (Rat.num_nonneg.mp hεφ)
          (Rat.num_pos.mp hr) ▸ beFastO_imp_beCheckN hf)))
    (fun _ => instDecidableBε₂N Qi p εθ εφ δ r)

end Noperthedron.Solution.Local2Nat

namespace Noperthedron.Solution

/-- Re-derived `Row.ValidLocal₂` decision procedure with the offset tier in
scope (beats the `Local2Nat` instance). -/
instance (priority := 10700) (row : Row) : Decidable (Row.ValidLocal₂ row) :=
  decidable_of_iff _ (Row.validLocal₂_iff row).symm

end Noperthedron.Solution

end
