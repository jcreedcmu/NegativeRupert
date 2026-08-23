-- PROOFLESS TIMING PROTOTYPE (validated 2026-08-22): all-Nat offset rendering
-- of the beFastN pair body; measured 1.27s vs 3.6-4.1s for beFastN on row 71419
-- under decide +kernel. See memory: project_second_order_local. Not imported
-- by anything; hardcoded to row 71419 of solution_tree_v7.csv.
module

public import Noperthedron.SolutionTable.Load
public meta import Noperthedron.SolutionTable.Load

/-! Proofless timing prototype: all-Nat offset rendering of the beFastN pair
body, on the real row 71419. Goal: validate the projected kernel speedup
before investing in the soundness proofs. -/

open Noperthedron Noperthedron.Solution Noperthedron.Solution.Local2Nat _root_.RationalApprox

load_csv_rows "solution_tree_v7.csv" from 71419 to 71420

noncomputable def rr : Row := csvRows_71419_71420.headI

namespace Proto

/-- Fixed-fuel Newton (no per-step branch). -/
def iterF (n : ℕ) : ℕ → ℕ → ℕ
  | 0, g => g
  | fuel+1, g => iterF n fuel ((g + n / g) / 2 + 1)

/-- Factor-100 windows (start within 10× of the root), binary dispatch,
fixed fuel 5. -/
def nUpE (m : ℕ) : ℕ :=
  (if m ≤ 10 ^ 16 then
    if m ≤ 10 ^ 8 then
      if m ≤ 10 ^ 4 then
        if m ≤ 10 ^ 2 then iterF m 5 20 else iterF m 5 200
      else
        if m ≤ 10 ^ 6 then iterF m 5 (2 * 10 ^ 3) else iterF m 5 (2 * 10 ^ 4)
    else
      if m ≤ 10 ^ 12 then
        if m ≤ 10 ^ 10 then iterF m 5 (2 * 10 ^ 5) else iterF m 5 (2 * 10 ^ 6)
      else
        if m ≤ 10 ^ 14 then iterF m 5 (2 * 10 ^ 7) else iterF m 5 (2 * 10 ^ 8)
  else
    if m ≤ 10 ^ 24 then
      if m ≤ 10 ^ 20 then
        if m ≤ 10 ^ 18 then iterF m 5 (2 * 10 ^ 9) else iterF m 5 (2 * 10 ^ 10)
      else
        if m ≤ 10 ^ 22 then iterF m 5 (2 * 10 ^ 11) else iterF m 5 (2 * 10 ^ 12)
    else
      if m ≤ 10 ^ 30 then
        if m ≤ 10 ^ 26 then iterF m 5 (2 * 10 ^ 13)
        else if m ≤ 10 ^ 28 then iterF m 5 (2 * 10 ^ 14) else iterF m 5 (2 * 10 ^ 15)
      else
        if m ≤ 10 ^ 32 then iterF m 5 (2 * 10 ^ 16)
        else if m ≤ 10 ^ 34 then iterF m 6 (2 * 10 ^ 17) else Nat.sqrt m) + 1

/-- ceil(S / 10^52) for the 84→32 scale drop (S ≥ 0). -/
def ceil52 (S : ℕ) : ℕ := if S = 0 then 0 else (S - 1) / 10 ^ 52 + 1

def nUpE84 (S : ℕ) : ℕ := nUpE (ceil52 S)

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

/-- Flat vertex index (packing order of the big literals). -/
def flatIx (a : VertexIndex) : ℕ := 45 * a.ℓ.val + 15 * a.i.val + a.k.val

/-- Signed value as (sign?, magnitude): `true` means nonneg. -/
def smOf (B xh : ℕ) : Bool × ℕ :=
  if B ≤ xh then (true, xh - B) else (false, B - xh)

/-- budN with all-Nat inputs and per-row prefolded nonneg coefficients. -/
local infixl:65 " +~ " => Nat.add
local infixl:70 " *~ " => Nat.mul
local infixl:65 " -~ " => Nat.sub

def budNat (k1 k2 k3 k4 k5 k6 a1 a2 a3 a4 a5 rem : ℕ) : ℕ :=
  k1 *~ a1 +~ k2 *~ a2 +~ k3 *~ a3 +~ k4 *~ a4 +~ k5 *~ a5 +~ k6 *~ rem

/-- The offset constants. Bc = coefficient offset (10^27 ≥ |trig·10^13| and
|trig·trig| ≤ 10^26); Bv = 10^17; BF = field offset (10^44 ≥ |field|). -/
def Bc : ℕ := 10 ^ 27
def Bv : ℕ := 2 ^ 56
def BF : ℕ := 10 ^ 44

/-- The all-Nat pair check. Arguments: per-row data.
ĉ* : the nine field-coefficient triples, offset by Bc (zeros for absent
slots use Bc itself so they contribute exactly the correction constant);
K2/K3 : per-field constant `BF +~ |J|·Bc·Bv − Bv·Σĉ_J` for |J| = 2, 3
(precomputed per row per field, as Nat);
kq* : per-i data for the three triangle corners. -/
structure RowConsts where
  (ca0_0 ca0_1 ca1_0 ca1_1 ca1_2 : ℕ)  -- a0 : 2 slots, a1 : 3 slots
  (cb0_0 cb0_1 cb1_0 cb1_1 : ℕ)
  (cc1_0 cc1_1 cc1_2 : ℕ)
  (cd0_0 cd0_1 cd1_0 cd1_1 : ℕ)
  (ce1_0 ce1_1 : ℕ)
  (cf1_0 cf1_1 cf1_2 : ℕ)
  (Ka0 Ka1 Kb0 Kb1 Kc1 Kd0 Kd1 Ke1 Kf1 : ℕ)  -- per-field additive constants
  (k1 k2 k3 k4 k5 k6 W : ℕ)                   -- budN coefficients, W
  (cmpL cmpRc : ℕ)                            -- δn·rd·10^52 and W·(δd·rn)

/-- Offset App6N (9 nonzero fields; c0/e0/f0 are identically 0). -/
structure A6O where
  (a0 a1 b0 b1 c1 d0 d1 e1 f1 : ℕ)

def appO (rc : RowConsts) (j : ℕ) : A6O :=
  let v := Nat.land (Nat.shiftRight pythonVertexBig (171 *~ j)) M171
  let w0 := Nat.land v M57
  let w1 := Nat.land (Nat.shiftRight v 57) M57
  let w2 := Nat.shiftRight v 114
  let s2 := w0 +~ w1
  let s3 := s2 +~ w2
  { a0 := rc.ca0_0 *~ w0 +~ rc.ca0_1 *~ w1 +~ rc.Ka0 -~ Bc *~ s2,
    a1 := rc.ca1_0 *~ w0 +~ rc.ca1_1 *~ w1 +~ rc.ca1_2 *~ w2 +~ rc.Ka1 -~ Bc *~ s3,
    b0 := rc.cb0_0 *~ w0 +~ rc.cb0_1 *~ w1 +~ rc.Kb0 -~ Bc *~ s2,
    b1 := rc.cb1_0 *~ w0 +~ rc.cb1_1 *~ w1 +~ rc.Kb1 -~ Bc *~ s2,
    c1 := rc.cc1_0 *~ w0 +~ rc.cc1_1 *~ w1 +~ rc.cc1_2 *~ w2 +~ rc.Kc1 -~ Bc *~ s3,
    d0 := rc.cd0_0 *~ w0 +~ rc.cd0_1 *~ w1 +~ rc.Kd0 -~ Bc *~ s2,
    d1 := rc.cd1_0 *~ w0 +~ rc.cd1_1 *~ w1 +~ rc.Kd1 -~ Bc *~ s2,
    e1 := rc.ce1_0 *~ w0 +~ rc.ce1_1 *~ w1 +~ rc.Ke1 -~ Bc *~ s2,
    f1 := rc.cf1_0 *~ w0 +~ rc.cf1_1 *~ w1 +~ rc.cf1_2 *~ w2 +~ rc.Kf1 -~ Bc *~ s3 }

/-- Signed dot-term accumulator: (s1,m1)·(s2,m2) added into (pos, neg). -/
def mulAcc (s1 : Bool) (m1 : ℕ) (s2 : Bool) (m2 : ℕ) (pn : ℕ × ℕ) : ℕ × ℕ :=
  if s1 == s2 then (pn.1 +~ m1 *~ m2, pn.2) else (pn.1, pn.2 +~ m1 *~ m2)

def absPN (pn : ℕ × ℕ) : ℕ := if pn.2 ≤ pn.1 then pn.1 -~ pn.2 else pn.2 -~ pn.1

/-- Per-corner data: q-fields split pos/neg, q̂+BF for the dq subtraction,
per-atom BF-correction constants, and D1N. -/
structure QC where
  (a0P a0N a1P a1N b0P b0N b1P b1N c1P c1N d0P d0N d1P d1N e1P e1N f1P f1N : ℕ)
  (pa0 pa1 pb0 pb1 pc1 pd0 pd1 pe1 pf1 : ℕ)  -- q̂ +~ BF
  (cmP cmN c1P' c1N' c2P c2N c3P c3N c4P c4N c5P c5N : ℕ)  -- BF·Σcoef pos/neg per atom
  (D1N qrow : ℕ)
  (Qk : VertexIndex)

def qcOf (rc : RowConsts) (Qk : VertexIndex) : QC :=
  let q := appO rc (flatIx Qk)
  -- pos/neg parts via truncated subtraction (one of each pair is 0)
  let a0P := q.a0 -~ BF; let a0N := BF -~ q.a0
  let a1P := q.a1 -~ BF; let a1N := BF -~ q.a1
  let b0P := q.b0 -~ BF; let b0N := BF -~ q.b0
  let b1P := q.b1 -~ BF; let b1N := BF -~ q.b1
  let c1P := q.c1 -~ BF; let c1N := BF -~ q.c1
  let d0P := q.d0 -~ BF; let d0N := BF -~ q.d0
  let d1P := q.d1 -~ BF; let d1N := BF -~ q.d1
  let e1P := q.e1 -~ BF; let e1N := BF -~ q.e1
  let f1P := q.f1 -~ BF; let f1N := BF -~ q.f1
  let sq := fun (pp nn : ℕ) => (pp +~ nn) *~ (pp +~ nn)  -- |q| = pos +~ neg
  let D1N := rc.W *~ (nUpE84 (sq a0P a0N +~ sq a1P a1N) +~ E6x3)
    +~ budNat rc.k1 rc.k2 rc.k3 rc.k4 rc.k5 rc.k6
        (nUpE84 (sq b0P b0N +~ sq b1P b1N) +~ E6x3)
        (nUpE84 (sq c1P c1N) +~ E6x3)
        (nUpE84 (sq d0P d0N +~ sq d1P d1N) +~ E6x3)
        (nUpE84 (sq e1P e1N) +~ E6x3)
        (nUpE84 (sq f1P f1N) +~ E6x3) E16
  { a0P := a0P, a0N := a0N, a1P := a1P, a1N := a1N,
    b0P := b0P, b0N := b0N, b1P := b1P, b1N := b1N,
    c1P := c1P, c1N := c1N, d0P := d0P, d0N := d0N,
    d1P := d1P, d1N := d1N, e1P := e1P, e1N := e1N, f1P := f1P, f1N := f1N,
    pa0 := q.a0 +~ BF, pa1 := q.a1 +~ BF, pb0 := q.b0 +~ BF, pb1 := q.b1 +~ BF,
    pc1 := q.c1 +~ BF, pd0 := q.d0 +~ BF, pd1 := q.d1 +~ BF, pe1 := q.e1 +~ BF,
    pf1 := q.f1 +~ BF,
    cmP := BF *~ (a0P +~ a1P), cmN := BF *~ (a0N +~ a1N),
    c1P' := BF *~ (b0P +~ b1P +~ a0P +~ a1P), c1N' := BF *~ (b0N +~ b1N +~ a0N +~ a1N),
    c2P := BF *~ (c1P +~ a1P), c2N := BF *~ (c1N +~ a1N),
    c3P := BF *~ (d0P +~ d1P +~ 2 *~ b0P +~ 2 *~ b1P +~ a0P +~ a1P),
    c3N := BF *~ (d0N +~ d1N +~ 2 *~ b0N +~ 2 *~ b1N +~ a0N +~ a1N),
    c4P := BF *~ (e1P +~ b1P +~ c1P +~ a1P), c4N := BF *~ (e1N +~ b1N +~ c1N +~ a1N),
    c5P := BF *~ (f1P +~ 2 *~ c1P +~ a1P), c5N := BF *~ (f1N +~ 2 *~ c1N +~ a1N),
    D1N := D1N,
    qrow := Nat.land (Nat.shiftRight sqrtDvBig (5130 *~ flatIx Qk)) M5130,
    Qk := Qk }

def pairOk (rc : RowConsts) (qc : QC) (j : ℕ) : Bool :=
  let v := appO rc j
  -- dq offset fields: one Nat.sub each (offset BF preserved)
  let da0 := qc.pa0 -~ v.a0; let da1 := qc.pa1 -~ v.a1
  let db0 := qc.pb0 -~ v.b0; let db1 := qc.pb1 -~ v.b1
  let dc1 := qc.pc1 -~ v.c1
  let dd0 := qc.pd0 -~ v.d0; let dd1 := qc.pd1 -~ v.d1
  let de1 := qc.pe1 -~ v.e1
  let df1 := qc.pf1 -~ v.f1
  let nrmN := Nat.land (Nat.shiftRight qc.qrow (57 *~ j)) M57 +~ E6x2
  -- atom accumulators: P := Σ qPos·d̂ +~ CN, N := Σ qNeg·d̂ +~ CP; atom = P − N
  let mdA := qc.a0P *~ da0 +~ qc.a1P *~ da1 +~ qc.cmN
  let mdB := qc.a0N *~ da0 +~ qc.a1N *~ da1 +~ qc.cmP
  let p1 := qc.b0P *~ da0 +~ qc.b1P *~ da1 +~ qc.a0P *~ db0 +~ qc.a1P *~ db1 +~ qc.c1N'
  let n1 := qc.b0N *~ da0 +~ qc.b1N *~ da1 +~ qc.a0N *~ db0 +~ qc.a1N *~ db1 +~ qc.c1P'
  let t1 := (if n1 ≤ p1 then p1 -~ n1 else n1 -~ p1) +~ E74x18
  let p2 := qc.c1P *~ da1 +~ qc.a1P *~ dc1 +~ qc.c2N
  let n2 := qc.c1N *~ da1 +~ qc.a1N *~ dc1 +~ qc.c2P
  let t2 := (if n2 ≤ p2 then p2 -~ n2 else n2 -~ p2) +~ E74x18
  let p3 := qc.d0P *~ da0 +~ qc.d1P *~ da1 +~ 2 *~ qc.b0P *~ db0 +~ 2 *~ qc.b1P *~ db1
    +~ qc.a0P *~ dd0 +~ qc.a1P *~ dd1 +~ qc.c3N
  let n3 := qc.d0N *~ da0 +~ qc.d1N *~ da1 +~ 2 *~ qc.b0N *~ db0 +~ 2 *~ qc.b1N *~ db1
    +~ qc.a0N *~ dd0 +~ qc.a1N *~ dd1 +~ qc.c3P
  let t3 := (if n3 ≤ p3 then p3 -~ n3 else n3 -~ p3) +~ E74x36
  let p4 := qc.e1P *~ da1 +~ qc.b1P *~ dc1 +~ qc.c1P *~ db1 +~ qc.a1P *~ de1 +~ qc.c4N
  let n4 := qc.e1N *~ da1 +~ qc.b1N *~ dc1 +~ qc.c1N *~ db1 +~ qc.a1N *~ de1 +~ qc.c4P
  let t4 := (if n4 ≤ p4 then p4 -~ n4 else n4 -~ p4) +~ E74x36
  let p5 := qc.f1P *~ da1 +~ 2 *~ qc.c1P *~ dc1 +~ qc.a1P *~ df1 +~ qc.c5N
  let n5 := qc.f1N *~ da1 +~ 2 *~ qc.c1N *~ dc1 +~ qc.a1N *~ df1 +~ qc.c5P
  let t5 := (if n5 ≤ p5 then p5 -~ n5 else n5 -~ p5) +~ E74x36
  let bud := budNat rc.k1 rc.k2 rc.k3 rc.k4 rc.k5 rc.k6 t1 t2 t3 t4 t5
    (Nat.mul E68x8 nrmN)
  -- branchless squares: (d̂ − BF)² = d̂² +~ BF² − 2·BF·d̂
  let BF2 := BF *~ BF
  let sqd := fun (dh : ℕ) => dh *~ dh +~ BF2 -~ 2 *~ BF *~ dh
  let D2N := rc.W *~ (nUpE84 (sqd da0 +~ sqd da1) +~ E6x5)
    +~ budNat rc.k1 rc.k2 rc.k3 rc.k4 rc.k5 rc.k6
        (nUpE84 (sqd db0 +~ sqd db1) +~ E6x5)
        (nUpE84 (sqd dc1) +~ E6x5)
        (nUpE84 (sqd dd0 +~ sqd dd1) +~ E6x5)
        (nUpE84 (sqd de1) +~ E6x5)
        (nUpE84 (sqd df1) +~ E6x5) nrmN
  let A := rc.W *~ mdA
  let B := rc.W *~ mdB +~ Nat.mul rc.W E74x9 +~ bud
  (B < A) && (rc.cmpL *~ (qc.D1N *~ D2N) +~ B *~ rc.cmpRc < A *~ rc.cmpRc)

/-- Countdown pair loop over flat indices, skipping the corner itself. -/
def pairLoop (rc : RowConsts) (qc : QC) (qskip : ℕ) : ℕ → Bool
  | 0 => true
  | j+1 => (Nat.beq j qskip || pairOk rc qc j) && pairLoop rc qc qskip j

def checkO (rc : RowConsts) (Qi : Fin 3 → VertexIndex) : Bool :=
  (List.finRange 3).all fun i =>
    let qc := qcOf rc (Qi i)
    pairLoop rc qc (flatIx (Qi i)) 90

/-- Build the row constants from the row (Int arithmetic, once per row). -/
noncomputable def rcOf (row : Row) : RowConsts :=
  let p := row.interval.centerPose
  let stN := sinNum13 p.θ₂
  let ctN := cosNum13 p.θ₂
  let sfN := sinNum13 p.φ₂
  let cfN := cosNum13 p.φ₂
  let st13 := stN * 10 ^ 13
  let ct13 := ctN * 10 ^ 13
  let sf13 := sfN * 10 ^ 13
  let cf13 := cfN * 10 ^ 13
  let ctcf := ctN * cfN
  let stcf := stN * cfN
  let ctsf := ctN * sfN
  let stsf := stN * sfN
  let co : ℤ → ℕ := fun c => (c + (Bc : ℤ)).toNat
  let K : List ℤ → ℕ := fun cs =>
    ((BF : ℤ) + cs.length * (Bc : ℤ) * (Bv : ℤ)
      - (Bv : ℤ) * (cs.foldl (· + · + (Bc : ℤ)) 0 - 0)).toNat
  -- Σĉ_J = Σ(c + Bc); fold computes Σ(c)+|J|Bc directly
  let en := row.εθ₂.num; let ed : ℤ := row.εθ₂.den
  let fn := row.εφ₂.num; let fd : ℤ := row.εφ₂.den
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
    Ka0 := K [-st13, ct13], Ka1 := K [-ctcf, -stcf, sf13],
    Kb0 := K [-ct13, -st13], Kb1 := K [stcf, -ctcf],
    Kc1 := K [ctsf, stsf, cf13],
    Kd0 := K [st13, -ct13], Kd1 := K [ctcf, stcf],
    Ke1 := K [-stsf, ctsf],
    Kf1 := K [ctcf, stcf, -sf13],
    k1 := (6 * en * ed ^ 2 * fd ^ 3).toNat, k2 := (6 * fn * fd ^ 2 * ed ^ 3).toNat,
    k3 := (3 * en ^ 2 * ed * fd ^ 3).toNat, k4 := (6 * en * fn * ed ^ 2 * fd ^ 2).toNat,
    k5 := (3 * fn ^ 2 * fd * ed ^ 3).toNat, k6 := ((en * fd + fn * ed) ^ 3).toNat,
    W := W.toNat,
    cmpL := (row.δ₂.num * row.r.den * 10 ^ 52).toNat,
    cmpRc := (W * (row.δ₂.den * row.r.num)).toNat }

end Proto

set_option maxHeartbeats 24000000
set_option profiler true
set_option diagnostics true
set_option diagnostics.threshold 5000

-- control: the current tier on the same row, same session
theorem control_beFastN :
    Local2Nat.beFastN rr.Qi rr.interval.centerPose rr.εθ₂ rr.εφ₂ rr.δ₂ rr.r
      = true := by
  decide +kernel

-- the prototype
theorem probe_offset : Proto.checkO (Proto.rcOf rr) rr.Qi = true := by
  decide +kernel

