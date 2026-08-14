module

public import Noperthedron.Checker.LocalNat
public import Noperthedron.Checker.SqrtDvNat
public import Noperthedron.Vertices.PythonNat
public import Noperthedron.RationalApprox.NewtonSqrt

@[expose] public section


/-!
# All-`Nat` fast path for the local `Bεℚ` check

`BεℚPy.fastNat` re-decides `BεℚPy.checkN` one-sidedly (`true` implies the
integer check; `false` falls back), with every per-pair operation a single
kernel-accelerated `Nat` primitive:

* vertex coordinates and pair norms come from the packed table literals
  (`pythonVertexBig`, `sqrtDvBig`) — one shift + mask per read instead of
  a curried `Fin.cons` walk;
* the per-pair floor divisions stay `Nat`-exact through the pad identity
  `⌊z/D⌋ + K = ⌊(z + K·D)/D⌋`: the offset row-dot difference
  `d̂ = d + 2⁴⁷` is a `Nat` division of a `ble`-guarded padded difference,
  with the signed matrix entries offset by `2⁸⁷` and the packed vertex
  fields already offset by `2⁵⁶`;
* the row dots `q0/q1` are sign-split once per `i`, outside the pair loop;
  the pair test `cond`-dispatches on the two sign flags;
* every square root is replaced by the fuel-based Newton *upper* bound
  (`NewtonSqrt.newtonSqrtUp`, ~6 divisions instead of `Nat.sqrt`'s ~70).
  All three sqrt slots (`F2N`, `s1`, `s2`) sit on the bound side of their
  comparisons, so an upper bound is conservative — provided the bound
  coefficient is nonnegative, which the row-level guards (`0 ≤ ε.num`,
  `0 ≤ δ.num`, `0 < r.num`) ensure.

Rows that fail any guard or any pair test return `false` and are
re-decided by `checkN`; on table rows the fast path accepts, so the kernel
never evaluates the fallback.
-/

namespace Noperthedron.Solution.BεℚPy

open Noperthedron.NewtonSqrt

/-- The all-`Nat` pair test, over flat vertex index `j` (counting down;
`j = qskip`, the vertex `Qi i` itself, is vacuous).

Arguments (all `Nat`, built once per row or per `i`): `qp0/qn0/qp1/qn1` the
sign-selected magnitudes of the row dots (`qp − qn = q`, one of each pair
zero; scale `10¹³`); `e00..e12` the matrix
entries offset by `2⁸⁷` (scale `10²⁶`); `ce0/ce1` the entry-offset
corrections `2⁵⁶·(e00+e01)` and `2⁵⁶·(e10+e11+e12)`; `m0pad/m1pad` the row
dots `mq` padded by `2⁴⁷·10²⁹`; `rowT` the pre-shifted 5,130-bit
pair-norm row of `Qi i`; `c1 = 50·εd²`, `c2p − c2n = c1·(2⁴⁷·(q0+q1) + 10¹⁷)` the `A`-offset correction, `etermC10 = εn·(142εd+100εn)·10¹⁰`;
`L1/L2/cheapM` the cheap-tier comparison constants and `L3/R2` the exact
tier's, with `ed100/en284/ed600` the `denom2` pieces. -/
def pairBody
    (qskip qp0 qn0 qp1 qn1 e00 e01 e10 e11 e12 ce0 ce1 m0pad m1pad rowT
     c1 c2p c2n etermC10 L1 L2 cheapM L3 R2 ed100 en284 ed600 : ℕ)
    (j : ℕ) : Bool :=
  (Nat.beq j qskip).or (
    let v := Nat.land (Nat.shiftRight pythonVertexBig (Nat.mul 171 j)) (2 ^ 171 - 1)
    let v0 := Nat.land v (2 ^ 57 - 1)
    let v1 := Nat.land (Nat.shiftRight v 57) (2 ^ 57 - 1)
    let v2 := Nat.shiftRight v 114
    let n0 := Nat.add (Nat.add (Nat.mul e00 v0) (Nat.mul e01 v1)) (2 * 2 ^ 143)
    let n1 := Nat.add (Nat.add (Nat.add (Nat.mul e10 v0) (Nat.mul e11 v1))
      (Nat.mul e12 v2)) (3 * 2 ^ 143)
    let p0 := Nat.add (Nat.add m0pad ce0) (Nat.mul (2 ^ 87) (Nat.add v0 v1))
    let p1 := Nat.add (Nat.add m1pad ce1)
      (Nat.mul (2 ^ 87) (Nat.add (Nat.add v0 v1) v2))
    (Nat.ble n0 p0).and ((Nat.ble n1 p1).and (
      let dh0 := Nat.div (Nat.sub p0 n0) (10 ^ 29)
      let dh1 := Nat.div (Nat.sub p1 n1) (10 ^ 29)
      let np := Nat.add (Nat.mul c1 (Nat.add (Nat.mul qp0 dh0) (Nat.mul qp1 dh1))) c2n
      let ndv := Nat.land (Nat.shiftRight rowT (Nat.mul 57 j)) (2 ^ 57 - 1)
      let nn := Nat.add (Nat.add
        (Nat.mul c1 (Nat.add (Nat.mul qn0 dh0) (Nat.mul qn1 dh1))) c2p)
        (Nat.mul etermC10 (Nat.add ndv (2 * 10 ^ 6)))
      (Nat.ble nn np).and (
        let numer := Nat.sub np nn
        (Nat.blt (Nat.add (Nat.mul L1 ndv) L2) (Nat.mul numer cheapM)).or (
          -- exact tier: Newton upper bound for `s2`
          let ad0 := cond (Nat.ble dh0 (2 ^ 47)) (Nat.sub (2 ^ 47) dh0)
            (Nat.sub dh0 (2 ^ 47))
          let ad1 := cond (Nat.ble dh1 (2 ^ 47)) (Nat.sub (2 ^ 47) dh1)
            (Nat.sub dh1 (2 ^ 47))
          let s2 := Nat.add (newtonSqrtUp
            (Nat.mul (Nat.add (Nat.mul ad0 ad0) (Nat.mul ad1 ad1)) (10 ^ 6))
            6 (Nat.add (Nat.mul (Nat.add ad0 ad1) (10 ^ 3)) 1)) 1
          let denom2 := Nat.add (Nat.add (Nat.mul ed100 s2) en284) ed600
          Nat.blt (Nat.mul L3 denom2) (Nat.mul numer R2))))))

/-- Countdown pair loop. -/
def pairLoop
    (qskip qp0 qn0 qp1 qn1 e00 e01 e10 e11 e12 ce0 ce1 m0pad m1pad rowT
     c1 c2p c2n etermC10 L1 L2 cheapM L3 R2 ed100 en284 ed600 : ℕ) : ℕ → Bool
  | 0 => true
  | j + 1 =>
    (pairBody qskip qp0 qn0 qp1 qn1 e00 e01 e10 e11 e12 ce0 ce1 m0pad m1pad
      rowT c1 c2p c2n etermC10 L1 L2 cheapM L3 R2 ed100 en284 ed600 j).and
    (pairLoop qskip qp0 qn0 qp1 qn1 e00 e01 e10 e11 e12 ce0 ce1 m0pad m1pad
      rowT c1 c2p c2n etermC10 L1 L2 cheapM L3 R2 ed100 en284 ed600 j)

/-- The per-`i` stage of the fast local check: reads the `Qi i` vertex from
the packed table, computes the row dots and their sign split, the Newton
`s1`, and the tier constants, then runs the pure-`Nat` pair loop. All row
constants enter as arguments (computed once in `fastNat`). -/
def perIFast (E00 E01 E10 E11 E12 εn εd _δn _δd _rn _rd : ℤ)
    (F2N' e00 e01 e10 e11 e12 ce0 ce1 c1 etermC10 cheapMN boundNN DnN Dd1N R2
     cDNN ed100 en284 ed600 : ℕ) (qi : VertexIndex) : Bool :=
   let qflat := 45 * qi.ℓ.val + 15 * qi.i.val + qi.k.val
   let wv := Nat.land (Nat.shiftRight pythonVertexBig (Nat.mul 171 qflat))
     (2 ^ 171 - 1)
   let w0 : ℤ := ((Nat.land wv (2 ^ 57 - 1) : ℕ) : ℤ) - 2 ^ 56
   let w1 : ℤ := ((Nat.land (Nat.shiftRight wv 57) (2 ^ 57 - 1) : ℕ) : ℤ) - 2 ^ 56
   let w2 : ℤ := ((Nat.shiftRight wv 114 : ℕ) : ℤ) - 2 ^ 56
   let mq0 := E00 * w0 + E01 * w1
   let mq1 := E10 * w0 + E11 * w1 + E12 * w2
   let q0 := mq0 / 10 ^ 29
   let q1 := mq1 / 10 ^ 29
   decide (0 ≤ mq0 + 2 ^ 47 * 10 ^ 29) &&
   decide (0 ≤ mq1 + 2 ^ 47 * 10 ^ 29) &&
   (let s1 := Nat.add (newtonSqrtUp
      (Nat.mul (Nat.add (Nat.mul q0.natAbs q0.natAbs)
        (Nat.mul q1.natAbs q1.natAbs)) (10 ^ 6)) 6
      (Nat.add (Nat.mul (Nat.add q0.natAbs q1.natAbs) (10 ^ 3)) 1)) 1
    let denom1 := Nat.add (Nat.add (Nat.mul ed100 s1) ((142 * εn * 10 ^ 16).toNat))
      ((300 * εd * 10 ^ 6).toNat)
    let bd := Nat.mul boundNN denom1
    let L1 := Nat.mul (Nat.mul (Nat.mul bd F2N') Dd1N) DnN
    let L2 := Nat.mul (Nat.mul (Nat.mul bd cDNN) (10 ^ 32)) DnN
    let L3 := Nat.mul (Nat.mul boundNN DnN) denom1
    let c2 : ℤ := (50 * εd ^ 2) * (2 ^ 47 * (q0 + q1) + 10 ^ 17)
    pairLoop qflat (q0.toNat) ((-q0).toNat) (q1.toNat) ((-q1).toNat)
      e00 e01 e10 e11 e12 ce0 ce1
      ((mq0 + 2 ^ 47 * 10 ^ 29).toNat)
      ((mq1 + 2 ^ 47 * 10 ^ 29).toNat)
      (Nat.land (Nat.shiftRight sqrtDvBig (Nat.mul 5130 qflat)) (2 ^ 5130 - 1))
      c1 (c2.toNat) ((-c2).toNat) etermC10
      L1 L2 cheapMN L3 R2 ed100 en284 ed600 90)

/-- One-sided all-`Nat` fast path for `BεℚPy.checkN` (see the module
docstring). Guards, the per-pose fixed-scale ℤ stage, the per-`i` sign
split, and the pure-`Nat` pair loop. -/
def fastNat (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (ε δ r : ℚ) : Bool :=
  -- trig integer cores and matrix entries (scale 10²⁶), as in `checkN`
  let stN := RationalApprox.sinNum13 p.θ₂
  let ctN := RationalApprox.cosNum13 p.θ₂
  let spN := RationalApprox.sinNum13 p.φ₂
  let cpN := RationalApprox.cosNum13 p.φ₂
  let E00 := -stN * 10 ^ 13
  let E01 := ctN * 10 ^ 13
  let E10 := -(ctN * cpN)
  let E11 := -(stN * cpN)
  let E12 := spN * 10 ^ 13
  let εn : ℤ := ε.num
  let εd : ℤ := ε.den
  let δn : ℤ := δ.num
  let δd : ℤ := δ.den
  let rn : ℤ := r.num
  let rd : ℤ := r.den
  -- Newton upper bound for `F2N = sqrtNum52 froN`: the inner
  -- `⌈froN/10²⁰⌉ ≤ froN.toNat/10²⁰ + 1`, and `froN ≥ 0` is a sum of squares
  let froNat := (E00.natAbs * E00.natAbs + E01.natAbs * E01.natAbs
    + E10.natAbs * E10.natAbs + E11.natAbs * E11.natAbs
    + E12.natAbs * E12.natAbs : ℕ)
  let F2N' : ℕ := newtonSqrtUp (froNat / 10 ^ 20 + 1) 6 (2 ^ 55) + 1
  -- row constants, exactly as in `checkN` (ℤ), plus their `Nat` casts
  let Dd1 := 100 * εd * 10 ^ 16
  let Dn := 50 * εd ^ 2 * 10 ^ 26
  let Db := 100 * δd * εd * rn
  let boundN := (100 * δn * εd + 224 * εn * δd) * rd
  let cDN := 200 * εd * 10 ^ 3 + 200 * εd + 284 * εn * 10 ^ 16 + 600 * εd * 10 ^ 6
  let etermC := εn * (142 * εd + 100 * εn)
  let cheapM := Db * Dd1 ^ 2 * 10 ^ 32
  -- guards: signs that make the conservative sqrt slack sound, and the
  -- offset ranges of the matrix entries
  decide (0 ≤ εn) && decide (0 ≤ δn) && decide (0 < rn) &&
  decide (0 ≤ E00 + 2 ^ 87) && decide (E00 + 2 ^ 87 < 2 ^ 88) &&
  decide (0 ≤ E01 + 2 ^ 87) && decide (E01 + 2 ^ 87 < 2 ^ 88) &&
  decide (0 ≤ E10 + 2 ^ 87) && decide (E10 + 2 ^ 87 < 2 ^ 88) &&
  decide (0 ≤ E11 + 2 ^ 87) && decide (E11 + 2 ^ 87 < 2 ^ 88) &&
  decide (0 ≤ E12 + 2 ^ 87) && decide (E12 + 2 ^ 87 < 2 ^ 88) &&
  (let e00 := (E00 + 2 ^ 87).toNat
   let e01 := (E01 + 2 ^ 87).toNat
   let e10 := (E10 + 2 ^ 87).toNat
   let e11 := (E11 + 2 ^ 87).toNat
   let e12 := (E12 + 2 ^ 87).toNat
   let ce0 := 2 ^ 56 * (e00 + e01)
   let ce1 := 2 ^ 56 * (e10 + e11 + e12)
   let c1 : ℕ := (50 * εd ^ 2).toNat
   let etermC10 : ℕ := (etermC * 10 ^ 10).toNat
   let cheapMN : ℕ := cheapM.toNat
   let boundNN : ℕ := boundN.toNat
   let DnN : ℕ := Dn.toNat
   let Dd1N : ℕ := Dd1.toNat
   let R2 : ℕ := (Dd1 ^ 2 * Db).toNat
   let cDNN : ℕ := cDN.toNat
   let ed100 : ℕ := (100 * εd).toNat
   let en284 : ℕ := (284 * εn * 10 ^ 16).toNat
   let ed600 : ℕ := (600 * εd * 10 ^ 6).toNat
   perIFast E00 E01 E10 E11 E12 ε.num ε.den δ.num δ.den r.num r.den F2N'
     e00 e01 e10 e11 e12 ce0 ce1 c1 etermC10 cheapMN boundNN DnN Dd1N R2 cDNN
     ed100 en284 ed600 (Qi 0) &&
   perIFast E00 E01 E10 E11 E12 ε.num ε.den δ.num δ.den r.num r.den F2N'
     e00 e01 e10 e11 e12 ce0 ce1 c1 etermC10 cheapMN boundNN DnN Dd1N R2 cDNN
     ed100 en284 ed600 (Qi 1) &&
   perIFast E00 E01 E10 E11 E12 ε.num ε.den δ.num δ.den r.num r.den F2N'
     e00 e01 e10 e11 e12 ce0 ce1 c1 etermC10 cheapMN boundNN DnN Dd1N R2 cDNN
     ed100 en284 ed600 (Qi 2))


/-! ## Soundness: `fastNat = true → checkN = true`

Everything here is `ℤ`-level: the fast path computes the non-sqrt
quantities of `checkN` *exactly* (offset/pad identities), and its Newton
square roots dominate `checkN`'s (`newtonSqrtUp_ge_sqrt`), which only
strengthens every comparison since the sqrt slots multiply the nonnegative
`boundN` side. -/

section Sound

open Noperthedron.NewtonSqrt

/-- The Newton seed dominates the root: `√((a² + b²)·10⁶) ≤ (a+b)·10³ + 1`. -/
private lemma sqrt_seed_le (a b : ℕ) :
    Nat.sqrt ((a * a + b * b) * 10 ^ 6) ≤ (a + b) * 10 ^ 3 + 1 := by
  have h1 : (a * a + b * b) * 10 ^ 6 ≤ ((a + b) * 10 ^ 3) * ((a + b) * 10 ^ 3) := by
    have : a * a + b * b ≤ (a + b) * (a + b) := by
      have hab := Nat.zero_le (a * b)
      linarith
    calc (a * a + b * b) * 10 ^ 6 ≤ ((a + b) * (a + b)) * 10 ^ 6 :=
          Nat.mul_le_mul_right _ this
      _ = ((a + b) * 10 ^ 3) * ((a + b) * 10 ^ 3) := by ring
  calc Nat.sqrt ((a * a + b * b) * 10 ^ 6)
      ≤ Nat.sqrt (((a + b) * 10 ^ 3) * ((a + b) * 10 ^ 3)) := Nat.sqrt_le_sqrt h1
    _ = (a + b) * 10 ^ 3 := Nat.sqrt_eq _
    _ ≤ (a + b) * 10 ^ 3 + 1 := Nat.le_succ _

/-- Unroll a true `pairLoop` into per-pair `pairBody` facts. -/
private lemma pairLoop_forall
    {qskip qp0 qn0 qp1 qn1 e00 e01 e10 e11 e12 ce0 ce1 m0pad m1pad rowT
     c1 c2p c2n etermC10 L1 L2 cheapM L3 R2 ed100 en284 ed600 : ℕ} :
    ∀ {n : ℕ}, pairLoop qskip qp0 qn0 qp1 qn1 e00 e01 e10 e11 e12 ce0 ce1
      m0pad m1pad rowT c1 c2p c2n etermC10 L1 L2 cheapM L3 R2
      ed100 en284 ed600 n = true →
    ∀ j, j < n → pairBody qskip qp0 qn0 qp1 qn1 e00 e01 e10 e11 e12 ce0 ce1
      m0pad m1pad rowT c1 c2p c2n etermC10 L1 L2 cheapM L3 R2
      ed100 en284 ed600 j = true := by
  intro n
  induction n with
  | zero => exact fun _ j hj => absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    intro h j hj
    rw [pairLoop, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
    · exact ih h.2 j h'
    · exact h.1

/-- The value-seeded Newton bound dominates `sqrtNum26`. -/
private lemma sqrtNum26_le_newton (q0 q1 : ℤ) :
    sqrtNum26 (q0 * q0 + q1 * q1)
      ≤ ((newtonSqrtUp ((q0.natAbs * q0.natAbs + q1.natAbs * q1.natAbs) * 10 ^ 6)
          6 ((q0.natAbs + q1.natAbs) * 10 ^ 3 + 1) + 1 : ℕ) : ℤ) := by
  unfold sqrtNum26
  split
  · positivity
  · rename_i hpos
    have htn : ((q0 * q0 + q1 * q1) * 10 ^ 6).toNat
        = (q0.natAbs * q0.natAbs + q1.natAbs * q1.natAbs) * 10 ^ 6 := by
      have h0 : (q0.natAbs * q0.natAbs : ℤ) = q0 * q0 := Int.natAbs_mul_self
      have h1 : (q1.natAbs * q1.natAbs : ℤ) = q1 * q1 := Int.natAbs_mul_self
      rw [show (q0 * q0 + q1 * q1) * 10 ^ 6
          = (((q0.natAbs * q0.natAbs + q1.natAbs * q1.natAbs) * 10 ^ 6 : ℕ) : ℤ) from by
        push_cast
        simp]
      exact Int.toNat_natCast _
    rw [htn]
    have hseed := sqrt_seed_le q0.natAbs q1.natAbs
    have hnewton := newtonSqrtUp_ge_sqrt
      (n := (q0.natAbs * q0.natAbs + q1.natAbs * q1.natAbs) * 10 ^ 6)
      (fuel := 6) (start := (q0.natAbs + q1.natAbs) * 10 ^ 3 + 1)
      (Nat.succ_pos _) hseed
    exact_mod_cast Nat.succ_le_succ hnewton

/-- The pad identity: a `ble`-guarded padded `Nat` division computes the
offset floor quotient exactly. -/
private lemma pad_div_eq {z : ℤ} {P N : ℕ} (hle : N ≤ P)
    (hPN : (P : ℤ) - N = z + 2 ^ 47 * 10 ^ 29) :
    (((P - N : ℕ) / 10 ^ 29 : ℕ) : ℤ) = z / 10 ^ 29 + 2 ^ 47 := by
  have hcast : ((P - N : ℕ) : ℤ) = z + 2 ^ 47 * 10 ^ 29 := by
    rw [Nat.cast_sub hle]
    exact hPN
  rw [Int.natCast_div, hcast]
  exact Int.add_mul_ediv_right z (2 ^ 47) (by norm_num)

/-- Raw-primitive normalizers for the bridge proofs. -/
private lemma nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl
private lemma nat_land_eq (a b : ℕ) : Nat.land a b = a &&& b := rfl
private lemma nat_shiftRight_eq (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl

/-- `ceil ≤ floor + 1` for the `F2` inner division. -/
private lemma neg_neg_ediv_le (a : ℤ) (b : ℕ) (hb : 0 < (b : ℤ)) :
    -(-a / (b : ℤ)) ≤ a / b + 1 := by
  have h1 := Int.mul_ediv_add_emod a b
  have h2 := Int.mul_ediv_add_emod (-a) b
  have h3 := Int.emod_nonneg a (ne_of_gt hb)
  have h4 := Int.emod_lt_of_pos (-a) hb
  have h5 := Int.emod_lt_of_pos a hb
  have h6 := Int.emod_nonneg (-a) (ne_of_gt hb)
  set q : ℤ := a / (b : ℤ) + -a / (b : ℤ) with hq
  have hbq : (b : ℤ) * q = -(a % b + -a % b) := by
    rw [hq]
    linarith
  have hcases : q = 0 ∨ q = -1 := by
    rcases lt_trichotomy q (-1) with h | h | h
    · exfalso
      have hle : q ≤ -2 := by omega
      have := mul_le_mul_of_nonneg_left hle hb.le
      linarith
    · right; exact h
    · left
      have hge : 0 ≤ q := by omega
      have h0 : q ≤ 0 := by
        by_contra hgt
        have hge1 : 1 ≤ q := by omega
        have := mul_le_mul_of_nonneg_left hge1 hb.le
        linarith
      omega
  rcases hcases with h | h <;> omega

/-- The fixed-seed Newton bound dominates `sqrtNum52`, given the entry
bounds the guards provide. -/
private lemma sqrtNum52_le_newton {E00 E01 E10 E11 E12 : ℤ}
    (h00 : E00.natAbs ≤ 2 ^ 87) (h01 : E01.natAbs ≤ 2 ^ 87)
    (h10 : E10.natAbs ≤ 2 ^ 87) (h11 : E11.natAbs ≤ 2 ^ 87)
    (h12 : E12.natAbs ≤ 2 ^ 87) :
    sqrtNum52 (E00 * E00 + E01 * E01 + E10 * E10 + E11 * E11 + E12 * E12)
      ≤ ((newtonSqrtUp ((E00.natAbs * E00.natAbs + E01.natAbs * E01.natAbs
            + E10.natAbs * E10.natAbs + E11.natAbs * E11.natAbs
            + E12.natAbs * E12.natAbs : ℕ) / 10 ^ 20 + 1) 6 (2 ^ 55) + 1 : ℕ) : ℤ) := by
  set fro : ℤ := E00 * E00 + E01 * E01 + E10 * E10 + E11 * E11 + E12 * E12 with hfro
  set froNat : ℕ := E00.natAbs * E00.natAbs + E01.natAbs * E01.natAbs
    + E10.natAbs * E10.natAbs + E11.natAbs * E11.natAbs
    + E12.natAbs * E12.natAbs with hfroNat
  have hcast : (froNat : ℤ) = fro := by
    rw [hfroNat, hfro]
    push_cast
    simp
  unfold sqrtNum52
  split
  · positivity
  · set M : ℕ := froNat / 10 ^ 20 + 1 with hM
    have hXM : (-(-fro / 10 ^ 20)).toNat ≤ M := by
      have hceil := neg_neg_ediv_le fro (10 ^ 20) (by norm_num)
      have hMz : ((M : ℕ) : ℤ) = fro / 10 ^ 20 + 1 := by
        rw [hM, ← hcast]
        push_cast [Int.natCast_div]
        norm_num
      calc (-(-fro / 10 ^ 20)).toNat ≤ (fro / 10 ^ 20 + 1).toNat :=
            Int.toNat_le_toNat (by exact_mod_cast hceil)
        _ = M := by rw [← hMz, Int.toNat_natCast]
    have hsqrtM : Nat.sqrt M ≤ 2 ^ 55 := by
      have hfroNat_le : froNat ≤ 5 * 2 ^ 174 := by
        have b00 := Nat.mul_le_mul h00 h00
        have b01 := Nat.mul_le_mul h01 h01
        have b10 := Nat.mul_le_mul h10 h10
        have b11 := Nat.mul_le_mul h11 h11
        have b12 := Nat.mul_le_mul h12 h12
        rw [hfroNat]
        calc E00.natAbs * E00.natAbs + E01.natAbs * E01.natAbs
              + E10.natAbs * E10.natAbs + E11.natAbs * E11.natAbs
              + E12.natAbs * E12.natAbs
            ≤ 2 ^ 87 * 2 ^ 87 + 2 ^ 87 * 2 ^ 87 + 2 ^ 87 * 2 ^ 87
              + 2 ^ 87 * 2 ^ 87 + 2 ^ 87 * 2 ^ 87 := by omega
          _ = 5 * 2 ^ 174 := by norm_num [pow_succ, pow_zero]
      have hMle : M ≤ 2 ^ 110 := by
        rw [hM]
        have := Nat.div_le_div_right (c := 10 ^ 20) hfroNat_le
        omega
      calc Nat.sqrt M ≤ Nat.sqrt (2 ^ 110) := Nat.sqrt_le_sqrt hMle
        _ = 2 ^ 55 := by
            rw [show (2 : ℕ) ^ 110 = (2 ^ 55) ^ 2 from by ring]
            exact Nat.sqrt_eq' _
    have hnewton := newtonSqrtUp_ge_sqrt (n := M) (fuel := 6) (start := 2 ^ 55)
      (by positivity) hsqrtM
    have : Nat.sqrt ((-(-fro / 10 ^ 20)).toNat) + 1 ≤ newtonSqrtUp M 6 (2 ^ 55) + 1 :=
      Nat.succ_le_succ (le_trans (Nat.sqrt_le_sqrt hXM) hnewton)
    exact_mod_cast this

/-- `sqrtNum26` is nonnegative. -/
private lemma sqrtNum26_nonneg' (S : ℤ) : 0 ≤ sqrtNum26 S := by
  unfold sqrtNum26
  positivity

/-- The exact-tier `cond`/`ble`/`sub` absolute value: with `↑X = z + 2⁴⁷`,
the branch computes `|z|`. -/
private lemma cond_pad_abs {X : ℕ} {z : ℤ} (hX : (X : ℤ) = z + 2 ^ 47) :
    ((cond (Nat.ble X (2 ^ 47)) (2 ^ 47 - X) (X - 2 ^ 47) : ℕ) : ℤ)
      = |z| := by
  rw [RationalApprox.cond_ble_sub_cast]
  congr 1
  push_cast
  omega

set_option maxHeartbeats 3200000 in
/-- The crux: a true `pairBody` at flat index `J ≠ qskip` implies `checkN`'s
pair disjunction, stated as a let-tower mirroring its zeta-reduced body.
Atoms: matrix entries `E∗∗` (scale `10²⁶`), the `Qi i` vertex `w∗` and the
pair vertex `v∗` (scale `10¹⁶`), the pair norm `ndv` (scale `10¹⁶`, `≥ 0`),
and the `ε/δ/r` numerators/denominators. Each `Nat` argument of `pairBody`
enters through an equation or a one-sided bound. -/
private lemma pairBody_sound
    {εn εd δn δd rn rd E00 E01 E10 E11 E12 w0 w1 w2 v0 v1 v2 ndv : ℤ}
    (hεn : 0 ≤ εn) (hεd : 0 < εd) (_hδn : 0 ≤ δn) (_hδd : 0 < δd)
    (_hrn : 0 < rn) (_hrd : 0 < rd) (hndv : 0 ≤ ndv)
    -- `Nat` argument links (exact)
    {J QSKIP QP0 QN0 QP1 QN1 e00 e01 e10 e11 e12 ce0 ce1 m0pad m1pad
     V0 V1 V2 NDV c1 c2p c2n etermC10 cheapM R2 ed100 en284 ed600 : ℕ}
    (hne : Nat.beq J QSKIP = false)
    (hqp0 : (QP0 : ℤ) = (E00 * w0 + E01 * w1) / 10 ^ 29 + QN0)
    (hqp1 : (QP1 : ℤ) = (E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29 + QN1)
    (he00 : (e00 : ℤ) = E00 + 2 ^ 87) (he01 : (e01 : ℤ) = E01 + 2 ^ 87)
    (he10 : (e10 : ℤ) = E10 + 2 ^ 87) (he11 : (e11 : ℤ) = E11 + 2 ^ 87)
    (he12 : (e12 : ℤ) = E12 + 2 ^ 87)
    (hce0 : ce0 = 2 ^ 56 * (e00 + e01)) (hce1 : ce1 = 2 ^ 56 * (e10 + e11 + e12))
    (hm0 : (m0pad : ℤ) = (E00 * w0 + E01 * w1) + 2 ^ 47 * 10 ^ 29)
    (hm1 : (m1pad : ℤ) = (E10 * w0 + E11 * w1 + E12 * w2) + 2 ^ 47 * 10 ^ 29)
    (hV0 : (V0 : ℤ) = v0 + 2 ^ 56) (hV1 : (V1 : ℤ) = v1 + 2 ^ 56)
    (hV2 : (V2 : ℤ) = v2 + 2 ^ 56)
    (hNDV : (NDV : ℤ) = ndv)
    (hc1 : (c1 : ℤ) = 50 * εd ^ 2)
    (hc2 : (c2p : ℤ) = 50 * εd ^ 2
      * (2 ^ 47 * ((E00 * w0 + E01 * w1) / 10 ^ 29
          + (E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29) + 10 ^ 17) + c2n)
    (het : (etermC10 : ℤ) = εn * (142 * εd + 100 * εn) * 10 ^ 10)
    (hcheapM : (cheapM : ℤ) = 100 * δd * εd * rn * (100 * εd * 10 ^ 16) ^ 2 * 10 ^ 32)
    (hR2 : (R2 : ℤ) = (100 * εd * 10 ^ 16) ^ 2 * (100 * δd * εd * rn))
    (hed100 : (ed100 : ℤ) = 100 * εd)
    (hen284 : (en284 : ℤ) = 284 * εn * 10 ^ 16)
    (hed600 : (ed600 : ℤ) = 600 * εd * 10 ^ 6)
    -- one-sided per-`i` bounds (the sqrt slack sits inside `L1/L2/L3`)
    {L1 L2 L3 rowT : ℕ} {denom1N F2N : ℤ}
    (_hdenom1 : (100 * εd * sqrtNum26 ((E00 * w0 + E01 * w1) / 10 ^ 29
        * ((E00 * w0 + E01 * w1) / 10 ^ 29)
        + (E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29
        * ((E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29))
      + 142 * εn * 10 ^ 16 + 300 * εd * 10 ^ 6) = denom1N)
    (_hF2 : sqrtNum52 (E00 * E00 + E01 * E01 + E10 * E10 + E11 * E11 + E12 * E12)
      = F2N)
    (_hdenom1nn : 0 ≤ denom1N) (_hF2nn : 0 ≤ F2N)
    (hL1 : (100 * δn * εd + 224 * εn * δd) * rd * denom1N * F2N
        * (100 * εd * 10 ^ 16) * (50 * εd ^ 2 * 10 ^ 26) ≤ (L1 : ℤ))
    (hL2 : (100 * δn * εd + 224 * εn * δd) * rd * denom1N
        * (200 * εd * 10 ^ 3 + 200 * εd + 284 * εn * 10 ^ 16 + 600 * εd * 10 ^ 6)
        * 10 ^ 32 * (50 * εd ^ 2 * 10 ^ 26) ≤ (L2 : ℤ))
    (hL3 : (100 * δn * εd + 224 * εn * δd) * rd * (50 * εd ^ 2 * 10 ^ 26) * denom1N
      ≤ (L3 : ℤ))
    (hbody : pairBody QSKIP QP0 QN0 QP1 QN1 e00 e01 e10 e11 e12 ce0 ce1
      m0pad m1pad rowT c1 c2p c2n etermC10 L1 L2 cheapM L3 R2
      ed100 en284 ed600 J = true)
    (hrowRead : ((Nat.land (Nat.shiftRight rowT (Nat.mul 57 J)) (2 ^ 57 - 1) : ℕ) : ℤ)
      = ndv)
    (hvRead0 : Nat.land (Nat.land (Nat.shiftRight pythonVertexBig (Nat.mul 171 J))
        (2 ^ 171 - 1)) (2 ^ 57 - 1) = V0)
    (hvRead1 : Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight pythonVertexBig
        (Nat.mul 171 J)) (2 ^ 171 - 1)) 57) (2 ^ 57 - 1) = V1)
    (hvRead2 : Nat.shiftRight (Nat.land (Nat.shiftRight pythonVertexBig
        (Nat.mul 171 J)) (2 ^ 171 - 1)) 114 = V2) :
    (let mq0 := E00 * w0 + E01 * w1
     let mq1 := E10 * w0 + E11 * w1 + E12 * w2
     let q0 := mq0 / 10 ^ 29
     let q1 := mq1 / 10 ^ 29
     let εnl : ℤ := εn
     let εdl : ℤ := εd
     let δnl : ℤ := δn
     let δdl : ℤ := δd
     let rnl : ℤ := rn
     let rdl : ℤ := rd
     let Dd1 := 100 * εdl * 10 ^ 16
     let Dn := 50 * εdl ^ 2 * 10 ^ 26
     let Db := 100 * δdl * εdl * rnl
     let boundN := (100 * δnl * εdl + 224 * εnl * δdl) * rdl
     let cDN := 200 * εdl * 10 ^ 3 + 200 * εdl + 284 * εnl * 10 ^ 16
       + 600 * εdl * 10 ^ 6
     let etermC := εnl * (142 * εdl + 100 * εnl)
     let cheapMl := Db * Dd1 ^ 2 * 10 ^ 32
     let d0 := (mq0 - (E00 * v0 + E01 * v1)) / 10 ^ 29
     let d1 := (mq1 - (E10 * v0 + E11 * v1 + E12 * v2)) / 10 ^ 29
     let A := q0 * d0 + q1 * d1 - 10 ^ 17
     let B := ndv + 2 * 10 ^ 6
     let numerN := 50 * εdl ^ 2 * A - etermC * B * 10 ^ 10
     (0 ≤ numerN ∧ 0 ≤ εnl ∧
       boundN * denom1N * (F2N * ndv * Dd1 + cDN * 10 ^ 32) * Dn
         < numerN * cheapMl) ∨
       (let s2 := sqrtNum26 (d0 * d0 + d1 * d1)
        let denom2N := 100 * εdl * s2 + 284 * εnl * 10 ^ 16 + 600 * εdl * 10 ^ 6
        boundN * (Dn * (denom1N * denom2N)) < numerN * Dd1 ^ 2 * Db)) := by
  -- reduce the fast body to its three guards and the tier disjunction
  unfold pairBody at hbody
  rw [hne, Bool.false_or] at hbody
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq,
    nat_div_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hbody
  have hNDVread : Nat.land (Nat.shiftRight rowT (Nat.mul 57 J)) (2 ^ 57 - 1) = NDV := by
    have := hrowRead.trans hNDV.symm
    exact_mod_cast this
  have hv0' := hvRead0
  have hv1' := hvRead1
  have hv2' := hvRead2
  have hnr' := hNDVread
  simp only [Nat.mul_eq] at hv0' hv1' hv2' hnr'
  rw [hv0', hv1', hv2', hnr'] at hbody
  obtain ⟨hple0, hple1, hnple, hlast⟩ := hbody
  -- the two padded differences compute `d + 2⁴⁷` exactly
  have hPN0 : ((m0pad + ce0 + 2 ^ 87 * (V0 + V1) : ℕ) : ℤ)
      - (e00 * V0 + e01 * V1 + 2 * 2 ^ 143 : ℕ)
      = ((E00 * w0 + E01 * w1) - (E00 * v0 + E01 * v1)) + 2 ^ 47 * 10 ^ 29 := by
    push_cast
    rw [he00, he01, hce0, hm0, hV0, hV1]
    push_cast [he00, he01]
    ring
  have hPN1 : ((m1pad + ce1 + 2 ^ 87 * (V0 + V1 + V2) : ℕ) : ℤ)
      - (e10 * V0 + e11 * V1 + e12 * V2 + 3 * 2 ^ 143 : ℕ)
      = ((E10 * w0 + E11 * w1 + E12 * w2) - (E10 * v0 + E11 * v1 + E12 * v2))
        + 2 ^ 47 * 10 ^ 29 := by
    push_cast
    rw [he10, he11, he12, hce1, hm1, hV0, hV1, hV2]
    push_cast [he10, he11, he12]
    ring
  have hd0 := pad_div_eq hple0 hPN0
  have hd1 := pad_div_eq hple1 hPN1
  -- the numerator is exact
  set d0 : ℤ := ((E00 * w0 + E01 * w1) - (E00 * v0 + E01 * v1)) / 10 ^ 29 with hd0def
  set d1 : ℤ := ((E10 * w0 + E11 * w1 + E12 * w2)
    - (E10 * v0 + E11 * v1 + E12 * v2)) / 10 ^ 29 with hd1def
  set q0 : ℤ := (E00 * w0 + E01 * w1) / 10 ^ 29 with hq0def
  set q1 : ℤ := (E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29 with hq1def
  set DH0 : ℕ := (m0pad + ce0 + 2 ^ 87 * (V0 + V1)
    - (e00 * V0 + e01 * V1 + 2 * 2 ^ 143)) / 10 ^ 29 with hDH0
  set DH1 : ℕ := (m1pad + ce1 + 2 ^ 87 * (V0 + V1 + V2)
    - (e10 * V0 + e11 * V1 + e12 * V2 + 3 * 2 ^ 143)) / 10 ^ 29 with hDH1
  have hnumer : ((c1 * (QP0 * DH0 + QP1 * DH1) + c2n : ℕ) : ℤ)
      - (c1 * (QN0 * DH0 + QN1 * DH1) + c2p + etermC10 * (NDV + 2 * 10 ^ 6))
      = 50 * εd ^ 2 * (q0 * d0 + q1 * d1 - 10 ^ 17)
        - εn * (142 * εd + 100 * εn) * (ndv + 2 * 10 ^ 6) * 10 ^ 10 := by
    push_cast
    rw [hqp0, hqp1, hc1, hc2, het, hNDV, hd0, hd1]
    push_cast
    ring
  -- numerator nonnegativity (shared by both branches)
  have hnn0 : 0 ≤ 50 * εd ^ 2 * (q0 * d0 + q1 * d1 - 10 ^ 17)
      - εn * (142 * εd + 100 * εn) * (ndv + 2 * 10 ^ 6) * 10 ^ 10 := by
    rw [← hnumer]
    have h := hnple
    zify at h
    push_cast at h ⊢
    linarith
  rcases hlast with hcheap | hexact
  · -- cheap tier
    refine Or.inl ⟨hnn0, hεn, ?_⟩
    have hsub : ((c1 * (QP0 * DH0 + QP1 * DH1) + c2n
        - (c1 * (QN0 * DH0 + QN1 * DH1) + c2p + etermC10 * (NDV + 2 * 10 ^ 6)) : ℕ) : ℤ)
        = 50 * εd ^ 2 * (q0 * d0 + q1 * d1 - 10 ^ 17)
          - εn * (142 * εd + 100 * εn) * (ndv + 2 * 10 ^ 6) * 10 ^ 10 := by
      rw [Nat.cast_sub hnple]
      exact hnumer
    have hlt : ((L1 * NDV + L2 : ℕ) : ℤ)
        < (50 * εd ^ 2 * (q0 * d0 + q1 * d1 - 10 ^ 17)
          - εn * (142 * εd + 100 * εn) * (ndv + 2 * 10 ^ 6) * 10 ^ 10) * cheapM := by
      rw [← hsub]
      exact_mod_cast hcheap
    have hcoef1 : (100 * δn * εd + 224 * εn * δd) * rd * denom1N * F2N
        * (100 * εd * 10 ^ 16) * (50 * εd ^ 2 * 10 ^ 26) * ndv ≤ (L1 : ℤ) * ndv :=
      mul_le_mul_of_nonneg_right hL1 hndv
    have hcast : ((L1 * NDV + L2 : ℕ) : ℤ) = (L1 : ℤ) * ndv + L2 := by
      push_cast [hNDV]
      ring
    rw [hcast] at hlt
    rw [hcheapM] at hlt
    linarith
  · -- exact tier
    refine Or.inr ?_
    have had0 : ((cond (Nat.ble DH0 (2 ^ 47)) (2 ^ 47 - DH0)
        (DH0 - 2 ^ 47) : ℕ) : ℤ) = |d0| := cond_pad_abs hd0
    have had1 : ((cond (Nat.ble DH1 (2 ^ 47)) (2 ^ 47 - DH1)
        (DH1 - 2 ^ 47) : ℕ) : ℤ) = |d1| := cond_pad_abs hd1
    -- align the Newton argument with `natAbs`
    have habs0 : (cond (Nat.ble DH0 (2 ^ 47)) (2 ^ 47 - DH0)
        (DH0 - 2 ^ 47) : ℕ) = d0.natAbs := by
      have := had0.trans (Int.abs_eq_natAbs d0)
      exact_mod_cast this
    have habs1 : (cond (Nat.ble DH1 (2 ^ 47)) (2 ^ 47 - DH1)
        (DH1 - 2 ^ 47) : ℕ) = d1.natAbs := by
      have := had1.trans (Int.abs_eq_natAbs d1)
      exact_mod_cast this
    rw [habs0, habs1] at hexact
    have hs2 : sqrtNum26 (d0 * d0 + d1 * d1)
        ≤ ((newtonSqrtUp ((d0.natAbs * d0.natAbs + d1.natAbs * d1.natAbs) * 10 ^ 6)
            6 ((d0.natAbs + d1.natAbs) * 10 ^ 3 + 1) + 1 : ℕ) : ℤ) :=
      sqrtNum26_le_newton d0 d1
    set S2N : ℕ := newtonSqrtUp ((d0.natAbs * d0.natAbs + d1.natAbs * d1.natAbs) * 10 ^ 6)
      6 ((d0.natAbs + d1.natAbs) * 10 ^ 3 + 1) + 1 with hS2N
    have hdenom2 : 100 * εd * sqrtNum26 (d0 * d0 + d1 * d1) + 284 * εn * 10 ^ 16
        + 600 * εd * 10 ^ 6 ≤ ((ed100 * S2N + en284 + ed600 : ℕ) : ℤ) := by
      push_cast
      rw [hed100, hen284, hed600]
      have := mul_le_mul_of_nonneg_left hs2 (by positivity : (0:ℤ) ≤ 100 * εd)
      linarith
    have hdenom2nn : 0 ≤ 100 * εd * sqrtNum26 (d0 * d0 + d1 * d1) + 284 * εn * 10 ^ 16
        + 600 * εd * 10 ^ 6 := by
      have := sqrtNum26_nonneg' (d0 * d0 + d1 * d1)
      positivity
    have hsub : ((c1 * (QP0 * DH0 + QP1 * DH1) + c2n
        - (c1 * (QN0 * DH0 + QN1 * DH1) + c2p + etermC10 * (NDV + 2 * 10 ^ 6)) : ℕ) : ℤ)
        = 50 * εd ^ 2 * (q0 * d0 + q1 * d1 - 10 ^ 17)
          - εn * (142 * εd + 100 * εn) * (ndv + 2 * 10 ^ 6) * 10 ^ 10 := by
      rw [Nat.cast_sub hnple]
      exact hnumer
    have hlt : ((L3 : ℤ)) * (ed100 * S2N + en284 + ed600 : ℕ)
        < (50 * εd ^ 2 * (q0 * d0 + q1 * d1 - 10 ^ 17)
          - εn * (142 * εd + 100 * εn) * (ndv + 2 * 10 ^ 6) * 10 ^ 10) * R2 := by
      rw [← hsub]
      exact_mod_cast hexact
    -- chain: boundN·(Dn·(denom1N·denom2N)) ≤ L3·denom2N ≤ L3·denom2' < numerN·R2
    have hchain1 : (100 * δn * εd + 224 * εn * δd) * rd * (50 * εd ^ 2 * 10 ^ 26)
        * denom1N * (100 * εd * sqrtNum26 (d0 * d0 + d1 * d1) + 284 * εn * 10 ^ 16
          + 600 * εd * 10 ^ 6)
        ≤ (L3 : ℤ) * (100 * εd * sqrtNum26 (d0 * d0 + d1 * d1) + 284 * εn * 10 ^ 16
          + 600 * εd * 10 ^ 6) :=
      mul_le_mul_of_nonneg_right hL3 hdenom2nn
    have hchain2 : (L3 : ℤ) * (100 * εd * sqrtNum26 (d0 * d0 + d1 * d1)
        + 284 * εn * 10 ^ 16 + 600 * εd * 10 ^ 6)
        ≤ (L3 : ℤ) * (ed100 * S2N + en284 + ed600 : ℕ) :=
      mul_le_mul_of_nonneg_left hdenom2 (by positivity)
    rw [hR2] at hlt
    linarith

/-- `sqrtNum52` is nonnegative. -/
private lemma sqrtNum52_nonneg' (S : ℤ) : 0 ≤ sqrtNum52 S := by
  unfold sqrtNum52
  positivity

set_option maxHeartbeats 6400000 in
/-- Per-`i` soundness: a true `perIFast` implies `checkN`\'s per-`i` body.
The row-level links come in as equations/bounds; `qi` is the `Qi i`. -/
private lemma perIFast_sound
    {E00 E01 E10 E11 E12 εn εd δn δd rn rd : ℤ}
    (hεn : 0 ≤ εn) (hεd : 0 < εd) (hδn : 0 ≤ δn) (hδd : 0 < δd)
    (hrn : 0 < rn) (hrd : 0 < rd)
    {F2N' e00 e01 e10 e11 e12 ce0 ce1 c1 etermC10 cheapMN boundNN DnN Dd1N R2
     cDNN ed100 en284 ed600 : ℕ} (qi : VertexIndex)
    (he00 : (e00 : ℤ) = E00 + 2 ^ 87) (he01 : (e01 : ℤ) = E01 + 2 ^ 87)
    (he10 : (e10 : ℤ) = E10 + 2 ^ 87) (he11 : (e11 : ℤ) = E11 + 2 ^ 87)
    (he12 : (e12 : ℤ) = E12 + 2 ^ 87)
    (hce0 : ce0 = 2 ^ 56 * (e00 + e01)) (hce1 : ce1 = 2 ^ 56 * (e10 + e11 + e12))
    (hc1 : (c1 : ℤ) = 50 * εd ^ 2)
    (het : (etermC10 : ℤ) = εn * (142 * εd + 100 * εn) * 10 ^ 10)
    (hcheapM : (cheapMN : ℤ) = 100 * δd * εd * rn * (100 * εd * 10 ^ 16) ^ 2 * 10 ^ 32)
    (hboundN : (boundNN : ℤ) = (100 * δn * εd + 224 * εn * δd) * rd)
    (hDn : (DnN : ℤ) = 50 * εd ^ 2 * 10 ^ 26)
    (hDd1 : (Dd1N : ℤ) = 100 * εd * 10 ^ 16)
    (hR2 : (R2 : ℤ) = (100 * εd * 10 ^ 16) ^ 2 * (100 * δd * εd * rn))
    (hcDN : (cDNN : ℤ) = 200 * εd * 10 ^ 3 + 200 * εd + 284 * εn * 10 ^ 16
      + 600 * εd * 10 ^ 6)
    (hed100 : (ed100 : ℤ) = 100 * εd)
    (hen284 : (en284 : ℤ) = 284 * εn * 10 ^ 16)
    (hed600 : (ed600 : ℤ) = 600 * εd * 10 ^ 6)
    (hF2 : sqrtNum52 (E00 * E00 + E01 * E01 + E10 * E10 + E11 * E11 + E12 * E12)
      ≤ (F2N' : ℤ))
    (hp : perIFast E00 E01 E10 E11 E12 εn εd δn δd rn rd F2N'
      e00 e01 e10 e11 e12 ce0 ce1 c1 etermC10 cheapMN boundNN DnN Dd1N R2 cDNN
      ed100 en284 ed600 qi = true) :
    (let w0 := pythonVertexNumCurried qi.ℓ qi.i qi.k 0
     let w1 := pythonVertexNumCurried qi.ℓ qi.i qi.k 1
     let w2 := pythonVertexNumCurried qi.ℓ qi.i qi.k 2
     let mq0 := E00 * w0 + E01 * w1
     let mq1 := E10 * w0 + E11 * w1 + E12 * w2
     let q0 := mq0 / 10 ^ 29
     let q1 := mq1 / 10 ^ 29
     let s1 := sqrtNum26 (q0 * q0 + q1 * q1)
     let denom1N := 100 * εd * s1 + 142 * εn * 10 ^ 16 + 300 * εd * 10 ^ 6
     let bdN := ((100 * δn * εd + 224 * εn * δd) * rd) * denom1N
     decide (∀ k : VertexIndex, k ≠ qi →
      let v0 := pythonVertexNumCurried k.ℓ k.i k.k 0
      let v1 := pythonVertexNumCurried k.ℓ k.i k.k 1
      let v2 := pythonVertexNumCurried k.ℓ k.i k.k 2
      let d0 := (mq0 - (E00 * v0 + E01 * v1)) / 10 ^ 29
      let d1 := (mq1 - (E10 * v0 + E11 * v1 + E12 * v2)) / 10 ^ 29
      let ndv := sqrtDvCurriedN qi.ℓ qi.i qi.k k.ℓ k.i k.k
      let A := q0 * d0 + q1 * d1 - 10 ^ 17
      let B := ndv + 2 * 10 ^ 6
      let numerN := 50 * εd ^ 2 * A - (εn * (142 * εd + 100 * εn)) * B * 10 ^ 10
      (0 ≤ numerN ∧ 0 ≤ εn ∧
        bdN * (sqrtNum52 (E00 * E00 + E01 * E01 + E10 * E10 + E11 * E11
            + E12 * E12) * ndv * (100 * εd * 10 ^ 16)
          + (200 * εd * 10 ^ 3 + 200 * εd + 284 * εn * 10 ^ 16
            + 600 * εd * 10 ^ 6) * 10 ^ 32) * (50 * εd ^ 2 * 10 ^ 26)
          < numerN * (100 * δd * εd * rn * (100 * εd * 10 ^ 16) ^ 2 * 10 ^ 32)) ∨
        (let s2 := sqrtNum26 (d0 * d0 + d1 * d1)
         let denom2N := 100 * εd * s2 + 284 * εn * 10 ^ 16 + 600 * εd * 10 ^ 6
         ((100 * δn * εd + 224 * εn * δd) * rd)
           * ((50 * εd ^ 2 * 10 ^ 26) * (denom1N * denom2N))
           < numerN * (100 * εd * 10 ^ 16) ^ 2 * (100 * δd * εd * rn))) = true) := by
  -- destructure the fast per-`i` stage
  unfold perIFast at hp
  rw [Bool.and_eq_true] at hp
  obtain ⟨hpads, hloop⟩ := hp
  rw [Bool.and_eq_true] at hpads
  obtain ⟨hpad0, hpad1⟩ := hpads
  rw [decide_eq_true_eq] at hpad0 hpad1
  simp only [] at hloop
  -- the `Qi i` vertex from the packed table
  have h90 : 45 * qi.ℓ.val + 15 * qi.i.val + qi.k.val < 90 := by
    have h1 := qi.ℓ.isLt
    have h2 := qi.i.isLt
    have h3 := qi.k.isLt
    omega
  have hqix : VertexIndex.ofFin90
      ⟨45 * qi.ℓ.val + 15 * qi.i.val + qi.k.val, h90⟩ = qi := by
    have := VertexIndex.ofFin90_flat qi
    simpa only [Nat.mod_eq_of_lt h90] using this
  have hqspec := pythonVertexBig_spec ⟨45 * qi.ℓ.val + 15 * qi.i.val + qi.k.val, h90⟩
  rw [hqix] at hqspec
  dsimp only at hqspec
  unfold pythonVertexNum at hqspec
  obtain ⟨hw0z, hw1z, hw2z⟩ := hqspec
  -- rewrite the packed reads into the exact vertex numerators
  simp only [nat_land_eq, nat_shiftRight_eq, Nat.mul_eq, Nat.add_eq]
    at hpad0 hpad1 hloop
  rw [hw0z, hw1z] at hpad0
  rw [hw0z, hw1z, hw2z] at hpad1
  rw [hw0z, hw1z, hw2z] at hloop
  simp only [add_sub_cancel_right] at hpad0 hpad1 hloop
  simp only [decide_eq_true_eq]
  intro k hk
  -- the pair vertex and pair norm from the packed tables
  have hj90 : 45 * k.ℓ.val + 15 * k.i.val + k.k.val < 90 := by
    have h1 := k.ℓ.isLt
    have h2 := k.i.isLt
    have h3 := k.k.isLt
    omega
  have hkix : VertexIndex.ofFin90
      ⟨45 * k.ℓ.val + 15 * k.i.val + k.k.val, hj90⟩ = k := by
    have := VertexIndex.ofFin90_flat k
    simpa only [Nat.mod_eq_of_lt hj90] using this
  have hkspec := pythonVertexBig_spec ⟨45 * k.ℓ.val + 15 * k.i.val + k.k.val, hj90⟩
  rw [hkix] at hkspec
  dsimp only at hkspec
  unfold pythonVertexNum at hkspec
  obtain ⟨hv0z, hv1z, hv2z⟩ := hkspec
  have hndvz := sqrtDvBig_spec qi.ℓ qi.i qi.k k.ℓ k.i k.k
  dsimp only at hndvz
  -- the pair test from the loop
  have hbody := pairLoop_forall hloop (45 * k.ℓ.val + 15 * k.i.val + k.k.val) hj90
  have hne : Nat.beq (45 * k.ℓ.val + 15 * k.i.val + k.k.val)
      (45 * qi.ℓ.val + 15 * qi.i.val + qi.k.val) = false := by
    rcases hbeq : Nat.beq (45 * k.ℓ.val + 15 * k.i.val + k.k.val)
        (45 * qi.ℓ.val + 15 * qi.i.val + qi.k.val) with _ | _
    · rfl
    · exact absurd (VertexIndex.flat_inj k qi (Nat.eq_of_beq_eq_true hbeq)) hk
  -- numerators are nonnegative where needed
  have hboundnn : (0:ℤ) ≤ (100 * δn * εd + 224 * εn * δd) * rd := by positivity
  have hndvnn : (0:ℤ) ≤ sqrtDvCurriedN qi.ℓ qi.i qi.k k.ℓ k.i k.k := by
    rw [← hndvz]
    positivity
  -- the per-`i` sqrt bound and the padded denominator
  have hs1 : sqrtNum26 (((E00 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E01 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1) / 10 ^ 29) * ((E00 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E01 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1) / 10 ^ 29) + ((E10 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E11 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1
      + E12 * pythonVertexNumCurried qi.ℓ qi.i qi.k 2) / 10 ^ 29) * ((E10 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E11 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1
      + E12 * pythonVertexNumCurried qi.ℓ qi.i qi.k 2) / 10 ^ 29))
      ≤ ((newtonSqrtUp (((((E00 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E01 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1) / 10 ^ 29).natAbs * ((E00 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E01 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1) / 10 ^ 29).natAbs
          + ((E10 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E11 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1
      + E12 * pythonVertexNumCurried qi.ℓ qi.i qi.k 2) / 10 ^ 29).natAbs * ((E10 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E11 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1
      + E12 * pythonVertexNumCurried qi.ℓ qi.i qi.k 2) / 10 ^ 29).natAbs)) * 10 ^ 6) 6
          ((((E00 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E01 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1) / 10 ^ 29).natAbs + ((E10 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E11 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1
      + E12 * pythonVertexNumCurried qi.ℓ qi.i qi.k 2) / 10 ^ 29).natAbs) * 10 ^ 3 + 1) + 1 : ℕ) : ℤ) :=
    sqrtNum26_le_newton _ _
  set S1F : ℕ := newtonSqrtUp (((((E00 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E01 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1) / 10 ^ 29).natAbs * ((E00 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E01 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1) / 10 ^ 29).natAbs
      + ((E10 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E11 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1
      + E12 * pythonVertexNumCurried qi.ℓ qi.i qi.k 2) / 10 ^ 29).natAbs * ((E10 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E11 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1
      + E12 * pythonVertexNumCurried qi.ℓ qi.i qi.k 2) / 10 ^ 29).natAbs)) * 10 ^ 6) 6
      ((((E00 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E01 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1) / 10 ^ 29).natAbs + ((E10 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E11 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1
      + E12 * pythonVertexNumCurried qi.ℓ qi.i qi.k 2) / 10 ^ 29).natAbs) * 10 ^ 3 + 1) + 1 with hS1F
  have hd1f : 100 * εd * sqrtNum26 (((E00 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E01 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1) / 10 ^ 29) * ((E00 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E01 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1) / 10 ^ 29) + ((E10 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E11 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1
      + E12 * pythonVertexNumCurried qi.ℓ qi.i qi.k 2) / 10 ^ 29) * ((E10 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E11 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1
      + E12 * pythonVertexNumCurried qi.ℓ qi.i qi.k 2) / 10 ^ 29))
      + 142 * εn * 10 ^ 16 + 300 * εd * 10 ^ 6
      ≤ (ed100 : ℤ) * S1F + ((142 * εn * 10 ^ 16).toNat : ℤ)
        + ((300 * εd * 10 ^ 6).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (by positivity : (0:ℤ) ≤ 142 * εn * 10 ^ 16),
      Int.toNat_of_nonneg (by positivity : (0:ℤ) ≤ 300 * εd * 10 ^ 6), hed100]
    have := mul_le_mul_of_nonneg_left hs1 (by positivity : (0:ℤ) ≤ 100 * εd)
    linarith
  push_cast at hd1f
  have hd1fnn : (0:ℤ) ≤ 100 * εd * sqrtNum26 (((E00 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E01 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1) / 10 ^ 29) * ((E00 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E01 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1) / 10 ^ 29) + ((E10 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E11 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1
      + E12 * pythonVertexNumCurried qi.ℓ qi.i qi.k 2) / 10 ^ 29) * ((E10 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E11 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1
      + E12 * pythonVertexNumCurried qi.ℓ qi.i qi.k 2) / 10 ^ 29))
      + 142 * εn * 10 ^ 16 + 300 * εd * 10 ^ 6 := by
    have := sqrtNum26_nonneg' (((E00 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E01 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1) / 10 ^ 29) * ((E00 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E01 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1) / 10 ^ 29) + ((E10 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E11 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1
      + E12 * pythonVertexNumCurried qi.ℓ qi.i qi.k 2) / 10 ^ 29) * ((E10 * pythonVertexNumCurried qi.ℓ qi.i qi.k 0
      + E11 * pythonVertexNumCurried qi.ℓ qi.i qi.k 1
      + E12 * pythonVertexNumCurried qi.ℓ qi.i qi.k 2) / 10 ^ 29))
    positivity
  refine pairBody_sound hεn hεd hδn hδd hrn hrd hndvnn hne
    ?hqp0 ?hqp1 he00 he01 he10 he11 he12 hce0 hce1 ?hm0 ?hm1
    hv0z hv1z hv2z hndvz hc1 ?hc2 het hcheapM hR2 hed100 hen284 hed600
    rfl rfl ?hd1nn ?hF2nn ?hL1 ?hL2 ?hL3 hbody hndvz rfl rfl rfl
  case hqp0 =>
    omega
  case hqp1 =>
    omega
  case hm0 =>
    rw [Int.toNat_of_nonneg hpad0]
  case hm1 =>
    rw [Int.toNat_of_nonneg hpad1]
  case hc2 =>
    omega
  case hd1nn =>
    exact hd1fnn
  case hF2nn =>
    exact sqrtNum52_nonneg' _
  case hL1 =>
    push_cast
    rw [hboundN, hDd1, hDn]
    have hstep := mul_le_mul hd1f hF2 (sqrtNum52_nonneg' _)
      (le_trans hd1fnn hd1f)
    have hstep2 := mul_le_mul_of_nonneg_left hstep hboundnn
    have hpos : (0:ℤ) < (100 * εd * 10 ^ 16) * (50 * εd ^ 2 * 10 ^ 26) := by positivity
    have hstep3 := mul_le_mul_of_nonneg_right hstep2 hpos.le
    linarith
  case hL2 =>
    push_cast
    rw [hboundN, hDn, hcDN]
    have hstep2 := mul_le_mul_of_nonneg_left hd1f hboundnn
    have hpos : (0:ℤ) < (200 * εd * 10 ^ 3 + 200 * εd + 284 * εn * 10 ^ 16
        + 600 * εd * 10 ^ 6) * 10 ^ 32 * (50 * εd ^ 2 * 10 ^ 26) := by positivity
    have hstep3 := mul_le_mul_of_nonneg_right hstep2 hpos.le
    linarith
  case hL3 =>
    push_cast
    rw [hboundN, hDn]
    have hstep2 := mul_le_mul_of_nonneg_left hd1f
      (by positivity : (0:ℤ) ≤ ((100 * δn * εd + 224 * εn * δd) * rd)
        * (50 * εd ^ 2 * 10 ^ 26))
    linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 200000 in
/-- **Soundness of the local fast path.** -/
theorem fastNat_imp_checkN {Qi : Fin 3 → VertexIndex} {p : Pose ℚ} {ε δ r : ℚ}
    (h : fastNat Qi p ε δ r = true) : checkN Qi p ε δ r = true := by
  unfold fastNat at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h, hperI⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨h, hE12u⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨h, hE12l⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨h, hE11u⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨h, hE11l⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨h, hE10u⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨h, hE10l⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨h, hE01u⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨h, hE01l⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨h, hE00u⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨h, hE00l⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨hεn, hrn⟩ := h
  rw [Bool.and_eq_true] at hεn
  obtain ⟨hεn, hδn⟩ := hεn
  rw [decide_eq_true_eq] at hεn hδn hrn hE00l hE00u hE01l hE01u
  rw [decide_eq_true_eq] at hE10l hE10u hE11l hE11u hE12l hE12u
  rw [Bool.and_eq_true] at hperI
  obtain ⟨hperI, hperI2⟩ := hperI
  rw [Bool.and_eq_true] at hperI
  obtain ⟨hperI0, hperI1⟩ := hperI
  -- row-level facts feeding the per-`i` lemma
  have hεd' : (0:ℤ) < (ε.den : ℤ) := by exact_mod_cast ε.pos
  have hδd' : (0:ℤ) < (δ.den : ℤ) := by exact_mod_cast δ.pos
  have hrd' : (0:ℤ) < (r.den : ℤ) := by exact_mod_cast r.pos
  have habs00 : (-RationalApprox.sinNum13 p.θ₂ * 10 ^ 13).natAbs ≤ 2 ^ 87 := by omega
  have habs01 : (RationalApprox.cosNum13 p.θ₂ * 10 ^ 13).natAbs ≤ 2 ^ 87 := by omega
  have habs10 : (-(RationalApprox.cosNum13 p.θ₂ * RationalApprox.cosNum13 p.φ₂)).natAbs
      ≤ 2 ^ 87 := by omega
  have habs11 : (-(RationalApprox.sinNum13 p.θ₂ * RationalApprox.cosNum13 p.φ₂)).natAbs
      ≤ 2 ^ 87 := by omega
  have habs12 : (RationalApprox.sinNum13 p.φ₂ * 10 ^ 13).natAbs ≤ 2 ^ 87 := by omega
  have h142 : (0:ℤ) ≤ 142 * (ε.den : ℤ) + 100 * ε.num := by
    have h1 : (0:ℤ) ≤ 142 * (ε.den : ℤ) := by positivity
    have h2 : (0:ℤ) ≤ 100 * ε.num := by linarith
    linarith
  have hetnn : (0:ℤ) ≤ ε.num * (142 * (ε.den : ℤ) + 100 * ε.num) * 10 ^ 10 :=
    mul_nonneg (mul_nonneg hεn h142) (by norm_num)
  have hboundnn : (0:ℤ) ≤ (100 * δ.num * (ε.den : ℤ) + 224 * ε.num * (δ.den : ℤ))
      * (r.den : ℤ) :=
    mul_nonneg (add_nonneg
      (mul_nonneg (by linarith : (0:ℤ) ≤ 100 * δ.num) hεd'.le)
      (mul_nonneg (by linarith : (0:ℤ) ≤ 224 * ε.num) hδd'.le)) hrd'.le
  have hcheapnn : (0:ℤ) ≤ 100 * (δ.den : ℤ) * (ε.den : ℤ) * r.num
      * (100 * (ε.den : ℤ) * 10 ^ 16) ^ 2 * 10 ^ 32 := by
    have : (0:ℤ) ≤ 100 * (δ.den : ℤ) * (ε.den : ℤ) * r.num := by positivity
    positivity
  have hR2nn : (0:ℤ) ≤ (100 * (ε.den : ℤ) * 10 ^ 16) ^ 2
      * (100 * (δ.den : ℤ) * (ε.den : ℤ) * r.num) := by positivity
  have hcDNnn : (0:ℤ) ≤ 200 * (ε.den : ℤ) * 10 ^ 3 + 200 * (ε.den : ℤ)
      + 284 * ε.num * 10 ^ 16 + 600 * (ε.den : ℤ) * 10 ^ 6 := by
    have : (0:ℤ) ≤ 284 * ε.num * 10 ^ 16 := by
      have : (0:ℤ) ≤ 284 * ε.num := by linarith
      positivity
    positivity
  have hen284nn : (0:ℤ) ≤ 284 * ε.num * 10 ^ 16 := by
    have : (0:ℤ) ≤ 284 * ε.num := by linarith
    positivity
  have hsound := fun (qi : VertexIndex) hp => perIFast_sound
    hεn hεd' hδn hδd' hrn hrd' qi
    (Int.toNat_of_nonneg hE00l) (Int.toNat_of_nonneg hE01l)
    (Int.toNat_of_nonneg hE10l) (Int.toNat_of_nonneg hE11l)
    (Int.toNat_of_nonneg hE12l) rfl rfl
    (Int.toNat_of_nonneg (by positivity : (0:ℤ) ≤ 50 * (ε.den : ℤ) ^ 2))
    (Int.toNat_of_nonneg hetnn)
    (Int.toNat_of_nonneg hcheapnn)
    (Int.toNat_of_nonneg hboundnn)
    (Int.toNat_of_nonneg (by positivity : (0:ℤ) ≤ 50 * (ε.den : ℤ) ^ 2 * 10 ^ 26))
    (Int.toNat_of_nonneg (by positivity : (0:ℤ) ≤ 100 * (ε.den : ℤ) * 10 ^ 16))
    (Int.toNat_of_nonneg hR2nn)
    (Int.toNat_of_nonneg hcDNnn)
    (Int.toNat_of_nonneg (by positivity : (0:ℤ) ≤ 100 * (ε.den : ℤ)))
    (Int.toNat_of_nonneg hen284nn)
    (Int.toNat_of_nonneg (by positivity : (0:ℤ) ≤ 600 * (ε.den : ℤ) * 10 ^ 6))
    (sqrtNum52_le_newton habs00 habs01 habs10 habs11 habs12)
    hp
  unfold checkN
  rw [List.all_eq_true]
  intro i hi
  fin_cases i
  · exact hsound (Qi 0) hperI0
  · exact hsound (Qi 1) hperI1
  · exact hsound (Qi 2) hperI2

/-! ## The rerouted instances -/

/-- `Bεℚ` decided through the all-`Nat` fast path when `0 < ε` and `0 < r`
(the only regime `Row.ValidLocal` evaluates it in), falling back to the
integer core `checkN` and then the ℚ checker. Out-prioritizes
`instDecidablePy` (`Checker/Local.lean`). -/
instance (priority := 10600) instDecidableFastPy (Qi : Fin 3 → VertexIndex)
    (p : Pose ℚ) (ε δ r : ℚ) :
    Decidable (Local.TriangleQ.Bεℚ Qi pythonVertexA p ε δ r
      RationalApprox.sqrtApprox16) :=
  if h : 0 < ε ∧ 0 < r then
    dite (fastNat Qi p ε δ r = true)
      (fun hf => .isTrue ((check_iff Qi p ε δ r).mp
        (checkN_eq_check Qi p h.1 h.2 ▸ fastNat_imp_checkN hf)))
      (fun _ => decidable_of_iff (checkN Qi p ε δ r = true)
        (by rw [checkN_eq_check Qi p h.1 h.2]; exact check_iff Qi p ε δ r))
  else
    decidable_of_iff _ (check_iff Qi p ε δ r)

end Sound

end Noperthedron.Solution.BεℚPy

namespace Noperthedron.Solution

/-- Re-derived `Row.ValidLocal` decision procedure: identical statement to
the instance in `Checker/Local.lean`, but elaborated with
`BεℚPy.instDecidableFastPy` in scope, so the `Bεℚ` conjunct evaluates
through the all-`Nat` fast path. -/
instance (priority := 10600) (row : Row) : Decidable (Row.ValidLocal row) :=
  decidable_of_iff _ (Row.validLocal_iff row).symm

end Noperthedron.Solution

end
