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
  let sq := fun (pp nn : ℕ) => Nat.mul (Nat.add pp nn) (Nat.add pp nn)
  let D1N := Nat.add
    (Nat.mul rc.W (Nat.add (nUpO84 (Nat.add (sq a0P a0N) (sq a1P a1N))) E6x3))
    (budO rc.k1 rc.k2 rc.k3 rc.k4 rc.k5 rc.k6
      (Nat.add (nUpO84 (Nat.add (sq b0P b0N) (sq b1P b1N))) E6x3)
      (Nat.add (nUpO84 (sq c1P c1N)) E6x3)
      (Nat.add (nUpO84 (Nat.add (sq d0P d0N) (sq d1P d1N))) E6x3)
      (Nat.add (nUpO84 (sq e1P e1N)) E6x3)
      (Nat.add (nUpO84 (sq f1P f1N)) E6x3) E16)
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

/-- The all-`Nat` pair test at flat index `j`. -/
def pairO (rc : RCO) (qc : QCO) (j : ℕ) : Bool :=
  let v := appO rc j
  let da0 := qc.pa0 - v.a0; let da1 := qc.pa1 - v.a1
  let db0 := qc.pb0 - v.b0; let db1 := qc.pb1 - v.b1
  let dc1 := qc.pc1 - v.c1
  let dd0 := qc.pd0 - v.d0; let dd1 := qc.pd1 - v.d1
  let de1 := qc.pe1 - v.e1
  let df1 := qc.pf1 - v.f1
  let nrmN := Nat.add (Nat.land (Nat.shiftRight qc.qrow (Nat.mul 57 j)) M57) E6x2
  let mdA := Nat.add (Nat.add (Nat.mul qc.a0P da0) (Nat.mul qc.a1P da1)) qc.xmN
  let mdB := Nat.add (Nat.add (Nat.mul qc.a0N da0) (Nat.mul qc.a1N da1)) qc.xmP
  let p1 := Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul qc.b0P da0)
    (Nat.mul qc.b1P da1)) (Nat.mul qc.a0P db0)) (Nat.mul qc.a1P db1)) qc.x1N
  let n1 := Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul qc.b0N da0)
    (Nat.mul qc.b1N da1)) (Nat.mul qc.a0N db0)) (Nat.mul qc.a1N db1)) qc.x1P
  let t1 := Nat.add (if n1 ≤ p1 then p1 - n1 else n1 - p1) E74x18
  let p2 := Nat.add (Nat.add (Nat.mul qc.c1P da1) (Nat.mul qc.a1P dc1)) qc.x2N
  let n2 := Nat.add (Nat.add (Nat.mul qc.c1N da1) (Nat.mul qc.a1N dc1)) qc.x2P
  let t2 := Nat.add (if n2 ≤ p2 then p2 - n2 else n2 - p2) E74x18
  let p3 := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
    (Nat.mul qc.d0P da0) (Nat.mul qc.d1P da1)) (Nat.mul (Nat.mul 2 qc.b0P) db0))
    (Nat.mul (Nat.mul 2 qc.b1P) db1)) (Nat.mul qc.a0P dd0))
    (Nat.mul qc.a1P dd1)) qc.x3N
  let n3 := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add
    (Nat.mul qc.d0N da0) (Nat.mul qc.d1N da1)) (Nat.mul (Nat.mul 2 qc.b0N) db0))
    (Nat.mul (Nat.mul 2 qc.b1N) db1)) (Nat.mul qc.a0N dd0))
    (Nat.mul qc.a1N dd1)) qc.x3P
  let t3 := Nat.add (if n3 ≤ p3 then p3 - n3 else n3 - p3) E74x36
  let p4 := Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul qc.e1P da1)
    (Nat.mul qc.b1P dc1)) (Nat.mul qc.c1P db1)) (Nat.mul qc.a1P de1)) qc.x4N
  let n4 := Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul qc.e1N da1)
    (Nat.mul qc.b1N dc1)) (Nat.mul qc.c1N db1)) (Nat.mul qc.a1N de1)) qc.x4P
  let t4 := Nat.add (if n4 ≤ p4 then p4 - n4 else n4 - p4) E74x36
  let p5 := Nat.add (Nat.add (Nat.add (Nat.mul qc.f1P da1)
    (Nat.mul (Nat.mul 2 qc.c1P) dc1)) (Nat.mul qc.a1P df1)) qc.x5N
  let n5 := Nat.add (Nat.add (Nat.add (Nat.mul qc.f1N da1)
    (Nat.mul (Nat.mul 2 qc.c1N) dc1)) (Nat.mul qc.a1N df1)) qc.x5P
  let t5 := Nat.add (if n5 ≤ p5 then p5 - n5 else n5 - p5) E74x36
  let bud := budO rc.k1 rc.k2 rc.k3 rc.k4 rc.k5 rc.k6 t1 t2 t3 t4 t5
    (Nat.mul E68x8 nrmN)
  let BF2 := Nat.mul BFO BFO
  let sqd := fun (dh : ℕ) =>
    Nat.add (Nat.mul dh dh) BF2 - Nat.mul (Nat.mul 2 BFO) dh
  let D2N := Nat.add
    (Nat.mul rc.W (Nat.add (nUpO84 (Nat.add (sqd da0) (sqd da1))) E6x5))
    (budO rc.k1 rc.k2 rc.k3 rc.k4 rc.k5 rc.k6
      (Nat.add (nUpO84 (Nat.add (sqd db0) (sqd db1))) E6x5)
      (Nat.add (nUpO84 (sqd dc1)) E6x5)
      (Nat.add (nUpO84 (Nat.add (sqd dd0) (sqd dd1))) E6x5)
      (Nat.add (nUpO84 (sqd de1)) E6x5)
      (Nat.add (nUpO84 (sqd df1)) E6x5) nrmN)
  let A := Nat.mul rc.W mdA
  let B := Nat.add (Nat.add (Nat.mul rc.W mdB) (Nat.mul rc.W E74x9)) bud
  decide (B < A) &&
    decide (Nat.add (Nat.mul rc.cmpL (Nat.mul qc.D1N D2N)) (Nat.mul B rc.cmpRc)
      < Nat.mul A rc.cmpRc)

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

end OffsetSound

end Noperthedron.Solution.Local2Nat

end
