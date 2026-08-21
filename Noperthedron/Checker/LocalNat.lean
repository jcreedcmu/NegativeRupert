module

public import Noperthedron.Checker.Local
public import Noperthedron.RationalApprox.TrigInt
public import Noperthedron.Vertices.PythonInt

@[expose] public section


/-!
# Integer core of the local `Bεℚ` check

`BεℚPy.checkN` recomputes exactly what `BεℚPy.check` computes, but with every
hot-loop quantity represented by an integer numerator over a statically known
power-of-10 scale (enabled by the fixed-point `sqrtApprox16`):

* trig values `round13 (sin/cos_psum …)` — numerators at scale `10¹³`,
  obtained directly as `⌊… * 10¹³⌋`;
* matrix entries — scale `10²⁶`;
* vertex coordinates — bare `ℤ` literals at scale `10¹⁶`
  (`pythonVertexNumCurried`);
* row dots `M₂·v` — scale `10⁴²`; their `round13`s via `Int` division by
  `10²⁹` (which floors, for positive divisors) — scale `10¹³`;
* `sqrtℚUp16` values — `Nat.sqrt` of scaled integers, scale `10¹⁶`; the
  pose-independent pair norms come from the integer literals
  `sqrtDvCurriedN`;
* `κℚ`, `√2⁺ = 142/100`, `√5⁺ = 224/100` — absorbed into the constants;
* the row-uniform `ε`, `δ`, `r` enter through their num/den pairs, and each
  comparison is cross-multiplied by the (positive, row-constant) denominator
  products.

No `Array` appears anywhere: under `decide +kernel`, `Array.ofFn` tables cost
per *access* (the push chain re-reduces), which is why the first draft of
this function was no faster than the ℚ check. Curried `![…]` literals walk a
few dozen `Fin.cons` cells instead, and every arithmetic step is a single GMP
operation.

The equality lemma `checkN_eq_check` (for `0 < ε`, `0 < r` — the only regime
`Row.ValidLocal` evaluates it in) is the soundness bridge for the all-`Nat`
fast path in `Checker/LocalFastNat.lean`, whose `Decidable` instances route
`Bεℚ` through `fastNat` with `checkN` as the exact fallback.
-/

namespace Noperthedron.Solution.BεℚPy

open Noperthedron RationalApprox

/-- Integer form of `sqrtℚUp16` on inputs `S/10²⁶`: for `S ≤ 0` both are `0`;
otherwise the inner `⌈(S/10²⁶)·10³²⌉ = S·10⁶` is exact. Output scale `10¹⁶`. -/
def sqrtNum26 (S : ℤ) : ℤ :=
  if S ≤ 0 then 0 else (Nat.sqrt (S * 10 ^ 6).toNat + 1 : ℕ)

/-- Integer form of `sqrtℚUp16` on inputs `S/10⁵²`: the inner ceiling
`⌈S/10²⁰⌉` is `-((-S)/10²⁰)` (floor division). Output scale `10¹⁶`. -/
def sqrtNum52 (S : ℤ) : ℤ :=
  if S ≤ 0 then 0 else (Nat.sqrt (-(-S / 10 ^ 20)).toNat + 1 : ℕ)

/-- Integer form of the *lower* square root `sqrtℚLow13` on inputs `S/10²⁶`:
the inner `⌊(S/10²⁶)·10²⁶⌋ = S` is exact, and `S ≤ 0` lands on `Nat.sqrt 0`
without a branch. Output scale `10¹³`. -/
def sqrtNumLow26 (S : ℤ) : ℤ := (Nat.sqrt S.toNat : ℕ)

/-! ### Compiled-path table reads

A curried-literal lookup costs the compiled code ~30 µs (`Fin.cons`
dispatch), which is why `Checker/Local.lean` backs `sqrtDv` with an
`@[csimp]` array. `checkN` reads the *integer* tables
(`pythonVertexNumCurried`, `sqrtDvCurriedN`) directly, so those get the same
treatment: `Array`s built once per process from the literals, `O(1)` reads in
compiled code, kernel-checked equality (the kernel keeps reducing the honest
curried definitions). -/

/-- All 810 vertex numerators, flattened as `(45·ℓ + 15·i + k)·3 + c`
(as in `pythonVertexTable`). -/
def pythonVertexNumTable : Array ℤ :=
  Array.ofFn (n := 270) fun j =>
    pythonVertexNumCurried ⟨j.val / 135, by omega⟩ ⟨j.val / 45 % 3, by omega⟩
      ⟨j.val / 3 % 15, by omega⟩ ⟨j.val % 3, by omega⟩

def pythonVertexNumImpl (ℓ : Fin 2) (i : Fin 3) (k : Fin 15) (c : Fin 3) : ℤ :=
  pythonVertexNumTable[(45 * ℓ.val + 15 * i.val + k.val) * 3 + c.val]'(by
    have h1 := ℓ.isLt
    have h2 := i.isLt
    have h3 := k.isLt
    have h4 := c.isLt
    rw [pythonVertexNumTable, Array.size_ofFn]
    omega)

@[csimp]
theorem pythonVertexNumCurried_eq_impl :
    @pythonVertexNumCurried = @pythonVertexNumImpl := by
  funext ℓ i k c
  have h1 := ℓ.isLt
  have h2 := i.isLt
  have h3 := k.isLt
  have h4 := c.isLt
  have e1 : ((45 * ℓ.val + 15 * i.val + k.val) * 3 + c.val) / 135 = ℓ.val := by omega
  have e2 : ((45 * ℓ.val + 15 * i.val + k.val) * 3 + c.val) / 45 % 3 = i.val := by omega
  have e3 : ((45 * ℓ.val + 15 * i.val + k.val) * 3 + c.val) / 3 % 15 = k.val := by omega
  have e4 : ((45 * ℓ.val + 15 * i.val + k.val) * 3 + c.val) % 3 = c.val := by omega
  simp only [pythonVertexNumImpl, pythonVertexNumTable, Array.getElem_ofFn,
    e1, e2, e3, e4, Fin.eta]

/-- All 8100 pair-norm numerators, flattened as `flat a · 90 + flat b` with
`flat ⟨k, ℓ, i⟩ = 45·ℓ + 15·i + k` (as in `sqrtDvTable`). -/
def sqrtDvCurriedNTable : Array ℤ :=
  Array.ofFn (n := 8100) fun j =>
    sqrtDvCurriedN ⟨j.val / 90 / 45, by omega⟩ ⟨j.val / 90 / 15 % 3, by omega⟩
      ⟨j.val / 90 % 15, by omega⟩
      ⟨j.val % 90 / 45, by omega⟩ ⟨j.val % 90 / 15 % 3, by omega⟩ ⟨j.val % 90 % 15, by omega⟩

def sqrtDvCurriedNImpl (ℓa : Fin 2) (ia : Fin 3) (ka : Fin 15)
    (ℓb : Fin 2) (ib : Fin 3) (kb : Fin 15) : ℤ :=
  sqrtDvCurriedNTable[(45 * ℓa.val + 15 * ia.val + ka.val) * 90 +
      (45 * ℓb.val + 15 * ib.val + kb.val)]'(by
    have h1 := ℓa.isLt
    have h2 := ia.isLt
    have h3 := ka.isLt
    have h4 := ℓb.isLt
    have h5 := ib.isLt
    have h6 := kb.isLt
    rw [sqrtDvCurriedNTable, Array.size_ofFn]
    omega)

@[csimp]
theorem sqrtDvCurriedN_eq_impl : @sqrtDvCurriedN = @sqrtDvCurriedNImpl := by
  funext ℓa ia ka ℓb ib kb
  have h1 := ℓa.isLt
  have h2 := ia.isLt
  have h3 := ka.isLt
  have h4 := ℓb.isLt
  have h5 := ib.isLt
  have h6 := kb.isLt
  have e1 : ((45 * ℓa.val + 15 * ia.val + ka.val) * 90 +
      (45 * ℓb.val + 15 * ib.val + kb.val)) / 90 / 45 = ℓa.val := by omega
  have e2 : ((45 * ℓa.val + 15 * ia.val + ka.val) * 90 +
      (45 * ℓb.val + 15 * ib.val + kb.val)) / 90 / 15 % 3 = ia.val := by omega
  have e3 : ((45 * ℓa.val + 15 * ia.val + ka.val) * 90 +
      (45 * ℓb.val + 15 * ib.val + kb.val)) / 90 % 15 = ka.val := by omega
  have e4 : ((45 * ℓa.val + 15 * ia.val + ka.val) * 90 +
      (45 * ℓb.val + 15 * ib.val + kb.val)) % 90 / 45 = ℓb.val := by omega
  have e5 : ((45 * ℓa.val + 15 * ia.val + ka.val) * 90 +
      (45 * ℓb.val + 15 * ib.val + kb.val)) % 90 / 15 % 3 = ib.val := by omega
  have e6 : ((45 * ℓa.val + 15 * ia.val + ka.val) * 90 +
      (45 * ℓb.val + 15 * ib.val + kb.val)) % 90 % 15 = kb.val := by omega
  simp only [sqrtDvCurriedNImpl, sqrtDvCurriedNTable, Array.getElem_ofFn,
    e1, e2, e3, e4, e5, e6, Fin.eta]

/-- Integer rendering of `BεℚPy.check` (see the module docstring). All the
`let`-bound quantities are integer numerators; comments give the scales. -/
def checkN (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (ε δ r : ℚ) : Bool :=
  -- trig numerators (scale 10¹³) — the `round13` numerators of `sinℚ`/`cosℚ`,
  -- via the integer Horner cores (RationalApprox/TrigInt.lean)
  let stN : ℤ := sinNum13 p.θ₂
  let ctN : ℤ := cosNum13 p.θ₂
  let spN : ℤ := sinNum13 p.φ₂
  let cpN : ℤ := cosNum13 p.φ₂
  -- matrix entries (scale 10²⁶); m₀₂ = 0 is dropped
  let E00 := -stN * 10 ^ 13
  let E01 := ctN * 10 ^ 13
  let E10 := -(ctN * cpN)
  let E11 := -(stN * cpN)
  let E12 := spN * 10 ^ 13
  -- row-uniform rational data as num/den pairs
  let εn : ℤ := ε.num
  let εd : ℤ := ε.den
  let δn : ℤ := δ.num
  let δd : ℤ := δ.den
  let rn : ℤ := r.num
  let rd : ℤ := r.den
  -- Frobenius-norm bound F2 (scale 10¹⁶): f16 of the entry-square sum
  -- (scale 10⁵²), with the inner ⌈·/10²⁰⌉ as integer ceiling division
  let froN := E00 * E00 + E01 * E01 + E10 * E10 + E11 * E11 + E12 * E12
  let F2N := sqrtNum52 froN
  -- row-constant scale denominators (all positive when 0 < ε, 0 < r)
  let Dd1 := 100 * εd * 10 ^ 16                 -- scale of denom1/denom2/cD
  let Dn := 50 * εd ^ 2 * 10 ^ 26               -- scale of numer
  let Db := 100 * δd * εd * rn                  -- scale of bound
  let boundN := (100 * δn * εd + 224 * εn * δd) * rd
  let cDN := 200 * εd * 10 ^ 3 + 200 * εd + 284 * εn * 10 ^ 16 + 600 * εd * 10 ^ 6
  let etermC := εn * (142 * εd + 100 * εn)      -- eterm = etermC / (50·εd²)
  let cheapM := Db * Dd1 ^ 2 * 10 ^ 32          -- RHS multiplier, cheap test
  (List.finRange 3).all fun i =>
    let Qi_idx := Qi i
    let w0 := pythonVertexNumCurried Qi_idx.ℓ Qi_idx.i Qi_idx.k 0
    let w1 := pythonVertexNumCurried Qi_idx.ℓ Qi_idx.i Qi_idx.k 1
    let w2 := pythonVertexNumCurried Qi_idx.ℓ Qi_idx.i Qi_idx.k 2
    let mq0 := E00 * w0 + E01 * w1               -- scale 10⁴²
    let mq1 := E10 * w0 + E11 * w1 + E12 * w2
    let q0 := mq0 / 10 ^ 29                      -- scale 10¹³
    let q1 := mq1 / 10 ^ 29
    let s1 := sqrtNum26 (q0 * q0 + q1 * q1)
    let denom1N := 100 * εd * s1 + 142 * εn * 10 ^ 16 + 300 * εd * 10 ^ 6
    let bdN := boundN * denom1N
    decide <| ∀ k : VertexIndex, k ≠ Qi_idx →
      let v0 := pythonVertexNumCurried k.ℓ k.i k.k 0
      let v1 := pythonVertexNumCurried k.ℓ k.i k.k 1
      let v2 := pythonVertexNumCurried k.ℓ k.i k.k 2
      let d0 := (mq0 - (E00 * v0 + E01 * v1)) / 10 ^ 29               -- scale 10¹³
      let d1 := (mq1 - (E10 * v0 + E11 * v1 + E12 * v2)) / 10 ^ 29
      let ndv := sqrtDvCurriedN Qi_idx.ℓ Qi_idx.i Qi_idx.k k.ℓ k.i k.k -- scale 10¹⁶
      let A := q0 * d0 + q1 * d1 - 10 ^ 17       -- scale 10²⁶
      let B := ndv + 2 * 10 ^ 6                  -- scale 10¹⁶
      let numerN := 50 * εd ^ 2 * A - etermC * B * 10 ^ 10
      (0 ≤ numerN ∧ 0 ≤ εn ∧
        bdN * (F2N * ndv * Dd1 + cDN * 10 ^ 32) * Dn < numerN * cheapM) ∨
        (let s2 := sqrtNum26 (d0 * d0 + d1 * d1)
         let denom2N := 100 * εd * s2 + 284 * εn * 10 ^ 16 + 600 * εd * 10 ^ 6
         boundN * (Dn * (denom1N * denom2N)) < numerN * Dd1 ^ 2 * Db)

/-- The per-pair integer test of `checkN`, as a standalone `Prop` over its
atoms. `denom1N` and `F2N` enter as parameters so the fast-path soundness
lemmas (`Checker/LocalFastNat.lean`) can link them one-sidedly; `checkN`'s
inner `decide` body and the conclusions of `pairBody_sound`/`perIFast_sound`
are all zeta/delta-reducible to instances of this definition, so the
correspondence is machine-checked instead of hand-mirrored. Reducible so
that `Decidable` instance synthesis and `refine`/`exact` see through it. -/
abbrev checkNPairTest (E00 E01 E10 E11 E12 εn εd δn δd rn rd denom1N F2N
    w0 w1 w2 v0 v1 v2 ndv : ℤ) : Prop :=
  let mq0 := E00 * w0 + E01 * w1
  let mq1 := E10 * w0 + E11 * w1 + E12 * w2
  let q0 := mq0 / 10 ^ 29
  let q1 := mq1 / 10 ^ 29
  let Dd1 := 100 * εd * 10 ^ 16
  let Dn := 50 * εd ^ 2 * 10 ^ 26
  let Db := 100 * δd * εd * rn
  let boundN := (100 * δn * εd + 224 * εn * δd) * rd
  let cDN := 200 * εd * 10 ^ 3 + 200 * εd + 284 * εn * 10 ^ 16 + 600 * εd * 10 ^ 6
  let etermC := εn * (142 * εd + 100 * εn)
  let cheapM := Db * Dd1 ^ 2 * 10 ^ 32
  let d0 := (mq0 - (E00 * v0 + E01 * v1)) / 10 ^ 29
  let d1 := (mq1 - (E10 * v0 + E11 * v1 + E12 * v2)) / 10 ^ 29
  let A := q0 * d0 + q1 * d1 - 10 ^ 17
  let B := ndv + 2 * 10 ^ 6
  let numerN := 50 * εd ^ 2 * A - etermC * B * 10 ^ 10
  (0 ≤ numerN ∧ 0 ≤ εn ∧
    boundN * denom1N * (F2N * ndv * Dd1 + cDN * 10 ^ 32) * Dn < numerN * cheapM) ∨
    (let s2 := sqrtNum26 (d0 * d0 + d1 * d1)
     let denom2N := 100 * εd * s2 + 284 * εn * 10 ^ 16 + 600 * εd * 10 ^ 6
     boundN * (Dn * (denom1N * denom2N)) < numerN * Dd1 ^ 2 * Db)


/-! ## Soundness: value bridges between the ℚ and ℤ pipelines -/

section Bridges

private lemma sqrtNum26_nonneg (S : ℤ) : 0 ≤ sqrtNum26 S := by
  unfold sqrtNum26
  positivity

/-- Cross-multiplication for integer-cast fractions with positive
denominators. -/
private lemma intCast_div_lt_div_iff {a b A B : ℤ} (hA : (0:ℤ) < A) (hB : (0:ℤ) < B) :
    (a : ℚ) / (A : ℚ) < (b : ℚ) / (B : ℚ) ↔ a * B < b * A := by
  rw [div_lt_div_iff₀ (by exact_mod_cast hA) (by exact_mod_cast hB)]
  exact_mod_cast Iff.rfl

private lemma intCast_div_nonneg_iff {n D : ℤ} (hD : (0:ℤ) < D) :
    0 ≤ (n : ℚ) / (D : ℚ) ↔ 0 ≤ n := by
  rw [le_div_iff₀ (by exact_mod_cast hD : (0:ℚ) < (D:ℚ))]
  simp

/-- `round13` on a scale-`10⁴²` integer fraction is integer division by
`10²⁹` (at scale `10¹³`). -/
private lemma round13_intCast_div42 (m : ℤ) :
    RationalApprox.round13 ((m : ℚ) / 10 ^ 42) = ((m / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13 := by
  rw [show ((10:ℚ) ^ 42) = 10 ^ 13 * ((10 ^ 29 : ℕ) : ℚ) from by norm_num,
    RationalApprox.round13_intCast_div,
    show ((10 ^ 29 : ℕ) : ℤ) = 10 ^ 29 from by norm_num]

/-- `sqrtℚUp16` on a scale-`10²⁶` integer fraction is `sqrtNum26` (at scale
`10¹⁶`). -/
private lemma sqrtℚUp16_intCast_div26 (S : ℤ) :
    RationalApprox.sqrtℚUp16 ((S : ℚ) / 10 ^ 26) = (sqrtNum26 S : ℚ) / 10 ^ 16 := by
  unfold RationalApprox.sqrtℚUp16 sqrtNum26
  rcases le_or_gt S 0 with hS | hS
  · rw [if_pos (div_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast hS, by positivity⟩)),
        if_pos hS]
    simp
  · have hSQ : (0:ℚ) < (S : ℚ) := by exact_mod_cast hS
    rw [if_neg (not_le.mpr (by positivity)), if_neg (not_le.mpr hS)]
    have hceil : ⌈(S : ℚ) / 10 ^ 26 * 10 ^ 32⌉ = S * 10 ^ 6 := by
      rw [show (S : ℚ) / 10 ^ 26 * 10 ^ 32 = ((S * 10 ^ 6 : ℤ) : ℚ) from by
        push_cast; ring]
      exact Int.ceil_intCast _
    rw [hceil]
    push_cast
    ring

/-- `sqrtℚUp16` on a scale-`10⁵²` integer fraction is `sqrtNum52` (at scale
`10¹⁶`). -/
private lemma sqrtℚUp16_intCast_div52 (S : ℤ) :
    RationalApprox.sqrtℚUp16 ((S : ℚ) / 10 ^ 52) = (sqrtNum52 S : ℚ) / 10 ^ 16 := by
  unfold RationalApprox.sqrtℚUp16 sqrtNum52
  rcases le_or_gt S 0 with hS | hS
  · rw [if_pos (div_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast hS, by positivity⟩)),
        if_pos hS]
    simp
  · have hSQ : (0:ℚ) < (S : ℚ) := by exact_mod_cast hS
    rw [if_neg (not_le.mpr (by positivity)), if_neg (not_le.mpr hS)]
    have hceil : ⌈(S : ℚ) / 10 ^ 52 * 10 ^ 32⌉ = -(-S / 10 ^ 20) := by
      rw [show (S : ℚ) / 10 ^ 52 * 10 ^ 32 = -(((-S : ℤ) : ℚ) / ((10 ^ 20 : ℕ) : ℚ)) from by
        push_cast; ring]
      rw [Int.ceil_neg, Rat.floor_intCast_div_natCast]
      norm_num
    rw [hceil]
    push_cast
    ring

/-- `sqrtℚLow13` on a scale-`10²⁶` integer fraction is `sqrtNumLow26` (at
scale `10¹³`). -/
private lemma sqrtℚLow13_intCast_div26 (S : ℤ) :
    RationalApprox.sqrtℚLow13 ((S : ℚ) / 10 ^ 26) = (sqrtNumLow26 S : ℚ) / 10 ^ 13 := by
  unfold RationalApprox.sqrtℚLow13 sqrtNumLow26
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

end Bridges

/-! ## The per-pair equivalence -/

section PairIff

open RationalApprox (round13 sqrtApprox16 κℚ)

/-- One `(i, k)` pair of `checkN` decides exactly the corresponding pair of
`check`, given the atom correspondences (matrix entries at scale `10²⁶`,
vertex coordinates at `10¹⁶`, the pair norm at `10¹⁶`) and `0 < ε`, `0 < r`.
Both sides are stated as `let`-towers mirroring the zeta-reduced bodies of
`checkN` and `check`. -/
private lemma pair_test_iff
    (E00 E01 E10 E11 E12 w0 w1 w2 v0 v1 v2 ndv : ℤ)
    {m00 m01 m02 m10 m11 m12 wq0 wq1 wq2 vq0 vq1 vq2 ndq ε δ r : ℚ}
    (hm00 : m00 = (E00 : ℚ) / 10 ^ 26) (hm01 : m01 = (E01 : ℚ) / 10 ^ 26)
    (hm02 : m02 = 0)
    (hm10 : m10 = (E10 : ℚ) / 10 ^ 26) (hm11 : m11 = (E11 : ℚ) / 10 ^ 26)
    (hm12 : m12 = (E12 : ℚ) / 10 ^ 26)
    (hw0 : wq0 = (w0 : ℚ) / 10 ^ 16) (hw1 : wq1 = (w1 : ℚ) / 10 ^ 16)
    (hw2 : wq2 = (w2 : ℚ) / 10 ^ 16)
    (hv0 : vq0 = (v0 : ℚ) / 10 ^ 16) (hv1 : vq1 = (v1 : ℚ) / 10 ^ 16)
    (hv2 : vq2 = (v2 : ℚ) / 10 ^ 16)
    (hnd : ndq = (ndv : ℚ) / 10 ^ 16)
    (hε : 0 < ε) (hr : 0 < r) :
    checkNPairTest E00 E01 E10 E11 E12 ε.num ε.den δ.num δ.den r.num r.den
      (100 * ε.den * sqrtNum26 ((E00 * w0 + E01 * w1) / 10 ^ 29
          * ((E00 * w0 + E01 * w1) / 10 ^ 29)
        + (E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29
          * ((E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29))
        + 142 * ε.num * 10 ^ 16 + 300 * ε.den * 10 ^ 6)
      (sqrtNum52 (E00 * E00 + E01 * E01 + E10 * E10 + E11 * E11 + E12 * E12))
      w0 w1 w2 v0 v1 v2 ndv ↔
     (let bound := (δ + sqrtApprox16.upper_sqrt_five * ε) / r
      let F2 := sqrtApprox16.upper_sqrt.f
        (m00 * m00 + m01 * m01 + m02 * m02 + m10 * m10 + m11 * m11 + m12 * m12)
      let cD := 2 / 10 ^ 13 + 2 / 10 ^ 16 + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ
      let eterm := 2 * ε * (sqrtApprox16.upper_sqrt_two + ε)
      let mq0 := m00 * wq0 + m01 * wq1 + m02 * wq2
      let mq1 := m10 * wq0 + m11 * wq1 + m12 * wq2
      let q0 := round13 mq0
      let q1 := round13 mq1
      let denom1 := sqrtApprox16.upper_sqrt.f (q0 * q0 + q1 * q1)
                    + sqrtApprox16.upper_sqrt_two * ε + 3 * κℚ
      let bd := bound * denom1
      let d0 := round13 (mq0 - (m00 * vq0 + m01 * vq1 + m02 * vq2))
      let d1 := round13 (mq1 - (m10 * vq0 + m11 * vq1 + m12 * vq2))
      let numer := q0 * d0 + q1 * d1 - 10 * κℚ - eterm * (ndq + 2 * κℚ)
      (0 ≤ numer ∧ 0 ≤ ε ∧ bd * (F2 * ndq + cD) < numer) ∨
        bound < numer / (denom1 * (sqrtApprox16.upper_sqrt.f (d0 * d0 + d1 * d1)
          + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ))) := by
  simp only [checkNPairTest]
  -- constants and atoms
  have hf : sqrtApprox16.upper_sqrt.f = RationalApprox.sqrtℚUp16 := rfl
  have h2c : sqrtApprox16.upper_sqrt_two = 71 / 50 := by
    norm_num [RationalApprox.sqrtApprox16]
  have h5c : sqrtApprox16.upper_sqrt_five = 56 / 25 := by
    norm_num [RationalApprox.sqrtApprox16]
  have hκc : κℚ = 1 / 10 ^ 10 := rfl
  set en := ε.num with hen
  set ed : ℤ := (ε.den : ℤ) with hed
  set dn := δ.num with hdn
  set dd : ℤ := (δ.den : ℤ) with hdd
  set rn := r.num with hrn
  set rd : ℤ := (r.den : ℤ) with hrd
  have hen_pos : 0 < en := Rat.num_pos.mpr hε
  have hed_pos : (0:ℤ) < ed := by rw [hed]; exact_mod_cast ε.pos
  have hdd_pos : (0:ℤ) < dd := by rw [hdd]; exact_mod_cast δ.pos
  have hrn_pos : 0 < rn := Rat.num_pos.mpr hr
  have hrd_pos : (0:ℤ) < rd := by rw [hrd]; exact_mod_cast r.pos
  have hedQ : (0:ℚ) < (ed : ℚ) := by exact_mod_cast hed_pos
  have hddQ : (0:ℚ) < (dd : ℚ) := by exact_mod_cast hdd_pos
  have hrnQ : (0:ℚ) < (rn : ℚ) := by exact_mod_cast hrn_pos
  have hrdQ : (0:ℚ) < (rd : ℚ) := by exact_mod_cast hrd_pos
  have hεq : ε = (en : ℚ) / (ed : ℚ) := by
    rw [hen, hed]; push_cast; exact (Rat.num_div_den ε).symm
  have hδq : δ = (dn : ℚ) / (dd : ℚ) := by
    rw [hdn, hdd]; push_cast; exact (Rat.num_div_den δ).symm
  have hrq : r = (rn : ℚ) / (rd : ℚ) := by
    rw [hrn, hrd]; push_cast; exact (Rat.num_div_den r).symm
  rw [hm00, hm01, hm02, hm10, hm11, hm12, hw0, hw1, hw2, hv0, hv1, hv2, hnd]
  -- canonicalize the row-dot arguments to single integer fractions
  rw [show (E00 : ℚ) / 10 ^ 26 * ((w0 : ℚ) / 10 ^ 16) + (E01 : ℚ) / 10 ^ 26 * ((w1 : ℚ) / 10 ^ 16)
        + 0 * ((w2 : ℚ) / 10 ^ 16) = ((E00 * w0 + E01 * w1 : ℤ) : ℚ) / 10 ^ 42 from by
      push_cast; ring]
  rw [show (E10 : ℚ) / 10 ^ 26 * ((w0 : ℚ) / 10 ^ 16) + (E11 : ℚ) / 10 ^ 26 * ((w1 : ℚ) / 10 ^ 16)
        + (E12 : ℚ) / 10 ^ 26 * ((w2 : ℚ) / 10 ^ 16)
        = ((E10 * w0 + E11 * w1 + E12 * w2 : ℤ) : ℚ) / 10 ^ 42 from by
      push_cast; ring]
  rw [show ((E00 * w0 + E01 * w1 : ℤ) : ℚ) / 10 ^ 42 -
        ((E00 : ℚ) / 10 ^ 26 * ((v0 : ℚ) / 10 ^ 16) + (E01 : ℚ) / 10 ^ 26 * ((v1 : ℚ) / 10 ^ 16)
          + 0 * ((v2 : ℚ) / 10 ^ 16))
        = ((E00 * w0 + E01 * w1 - (E00 * v0 + E01 * v1) : ℤ) : ℚ) / 10 ^ 42 from by
      push_cast; ring]
  rw [show ((E10 * w0 + E11 * w1 + E12 * w2 : ℤ) : ℚ) / 10 ^ 42 -
        ((E10 : ℚ) / 10 ^ 26 * ((v0 : ℚ) / 10 ^ 16) + (E11 : ℚ) / 10 ^ 26 * ((v1 : ℚ) / 10 ^ 16)
          + (E12 : ℚ) / 10 ^ 26 * ((v2 : ℚ) / 10 ^ 16))
        = ((E10 * w0 + E11 * w1 + E12 * w2 - (E10 * v0 + E11 * v1 + E12 * v2) : ℤ) : ℚ) / 10 ^ 42 from by
      push_cast; ring]
  simp only [round13_intCast_div42]
  -- canonicalize the sqrt arguments
  rw [show ((((E00 * w0 + E01 * w1) / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13) *
        ((((E00 * w0 + E01 * w1) / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13) +
        ((((E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13) *
        ((((E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13)
        = (((E00 * w0 + E01 * w1) / 10 ^ 29 * ((E00 * w0 + E01 * w1) / 10 ^ 29) +
            (E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29 * ((E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29) : ℤ) : ℚ)
          / 10 ^ 26 from by push_cast; ring]
  rw [show ((((E00 * w0 + E01 * w1 - (E00 * v0 + E01 * v1)) / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13) *
        ((((E00 * w0 + E01 * w1 - (E00 * v0 + E01 * v1)) / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13) +
        ((((E10 * w0 + E11 * w1 + E12 * w2 - (E10 * v0 + E11 * v1 + E12 * v2)) / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13) *
        ((((E10 * w0 + E11 * w1 + E12 * w2 - (E10 * v0 + E11 * v1 + E12 * v2)) / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13)
        = (((E00 * w0 + E01 * w1 - (E00 * v0 + E01 * v1)) / 10 ^ 29 *
              ((E00 * w0 + E01 * w1 - (E00 * v0 + E01 * v1)) / 10 ^ 29) +
            (E10 * w0 + E11 * w1 + E12 * w2 - (E10 * v0 + E11 * v1 + E12 * v2)) / 10 ^ 29 *
              ((E10 * w0 + E11 * w1 + E12 * w2 - (E10 * v0 + E11 * v1 + E12 * v2)) / 10 ^ 29) : ℤ) : ℚ)
          / 10 ^ 26 from by push_cast; ring]
  rw [show (E00 : ℚ) / 10 ^ 26 * ((E00 : ℚ) / 10 ^ 26) + (E01 : ℚ) / 10 ^ 26 * ((E01 : ℚ) / 10 ^ 26)
        + 0 * 0 + (E10 : ℚ) / 10 ^ 26 * ((E10 : ℚ) / 10 ^ 26)
        + (E11 : ℚ) / 10 ^ 26 * ((E11 : ℚ) / 10 ^ 26) + (E12 : ℚ) / 10 ^ 26 * ((E12 : ℚ) / 10 ^ 26)
        = ((E00 * E00 + E01 * E01 + E10 * E10 + E11 * E11 + E12 * E12 : ℤ) : ℚ) / 10 ^ 52 from by
      push_cast; ring]
  rw [hf]
  simp only [sqrtℚUp16_intCast_div26, sqrtℚUp16_intCast_div52]
  rw [h2c, h5c, hκc, hεq, hδq, hrq]
  -- positivity of the two per-pair denominators (for the exact test)
  set S1 := sqrtNum26 ((E00 * w0 + E01 * w1) / 10 ^ 29 * ((E00 * w0 + E01 * w1) / 10 ^ 29) +
      (E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29 * ((E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29))
    with hS1def
  set S2 := sqrtNum26 ((E00 * w0 + E01 * w1 - (E00 * v0 + E01 * v1)) / 10 ^ 29 *
        ((E00 * w0 + E01 * w1 - (E00 * v0 + E01 * v1)) / 10 ^ 29) +
      (E10 * w0 + E11 * w1 + E12 * w2 - (E10 * v0 + E11 * v1 + E12 * v2)) / 10 ^ 29 *
        ((E10 * w0 + E11 * w1 + E12 * w2 - (E10 * v0 + E11 * v1 + E12 * v2)) / 10 ^ 29))
    with hS2def
  have hS1 : (0:ℤ) ≤ S1 := hS1def ▸ sqrtNum26_nonneg _
  have hS2 : (0:ℤ) ≤ S2 := hS2def ▸ sqrtNum26_nonneg _
  have henQ : (0:ℚ) < (en : ℚ) := by exact_mod_cast hen_pos
  have hd1pos : (0:ℚ) < (S1 : ℚ) / 10 ^ 16 + 71 / 50 * ((en : ℚ) / (ed : ℚ)) + 3 * (1 / 10 ^ 10) := by
    positivity
  have hd2pos : (0:ℚ) < (S2 : ℚ) / 10 ^ 16 + 2 * (71 / 50) * ((en : ℚ) / (ed : ℚ)) + 6 * (1 / 10 ^ 10) := by
    positivity
  have hd1ne : (S1 : ℚ) / 10 ^ 16 + 71 / 50 * ((en : ℚ) / (ed : ℚ)) + 3 * (1 / 10 ^ 10) ≠ 0 :=
    ne_of_gt hd1pos
  have hd2ne : (S2 : ℚ) / 10 ^ 16 + 2 * (71 / 50) * ((en : ℚ) / (ed : ℚ)) + 6 * (1 / 10 ^ 10) ≠ 0 :=
    ne_of_gt hd2pos
  -- three comparisons and the ε-sign conjunct
  refine or_congr (and_congr ?_ (and_congr ?_ ?_)) ?_
  · constructor <;> intro h <;> qify at h ⊢ <;> field_simp at h ⊢ <;> linarith
  · exact (intCast_div_nonneg_iff hed_pos).symm
  · constructor <;> intro h <;> qify at h ⊢ <;> field_simp at h ⊢ <;> linarith
  · constructor <;> intro h <;> qify at h ⊢ <;> field_simp at h ⊢ <;> linarith

end PairIff

/-! ## The equality theorem and the rerouted instances -/

open Local.TriangleQ.Bεℚ (matEntries)

/-! The entry and vertex bridges between the ℚ pipeline's atoms and the
integer numerators, shared by `checkN_eq_check` and the `BoundRPy` check
below. -/

private lemma matEntries_m₀₀ (p : Pose ℚ) : (matEntries p).m₀₀
    = ((-RationalApprox.sinNum13 p.θ₂ * 10 ^ 13 : ℤ) : ℚ) / 10 ^ 26 := by
  show -RationalApprox.sinℚ p.θ₂ = _
  rw [← RationalApprox.sinNum13_div_eq p.θ₂]
  push_cast
  ring

private lemma matEntries_m₀₁ (p : Pose ℚ) : (matEntries p).m₀₁
    = ((RationalApprox.cosNum13 p.θ₂ * 10 ^ 13 : ℤ) : ℚ) / 10 ^ 26 := by
  show RationalApprox.cosℚ p.θ₂ = _
  rw [← RationalApprox.cosNum13_div_eq p.θ₂]
  push_cast
  ring

private lemma matEntries_m₀₂ (p : Pose ℚ) : (matEntries p).m₀₂ = 0 := rfl

private lemma matEntries_m₁₀ (p : Pose ℚ) : (matEntries p).m₁₀
    = ((-(RationalApprox.cosNum13 p.θ₂ * RationalApprox.cosNum13 p.φ₂) : ℤ) : ℚ) / 10 ^ 26 := by
  show -RationalApprox.cosℚ p.θ₂ * RationalApprox.cosℚ p.φ₂ = _
  rw [← RationalApprox.cosNum13_div_eq p.θ₂, ← RationalApprox.cosNum13_div_eq p.φ₂]
  push_cast
  ring

private lemma matEntries_m₁₁ (p : Pose ℚ) : (matEntries p).m₁₁
    = ((-(RationalApprox.sinNum13 p.θ₂ * RationalApprox.cosNum13 p.φ₂) : ℤ) : ℚ) / 10 ^ 26 := by
  show -RationalApprox.sinℚ p.θ₂ * RationalApprox.cosℚ p.φ₂ = _
  rw [← RationalApprox.sinNum13_div_eq p.θ₂, ← RationalApprox.cosNum13_div_eq p.φ₂]
  push_cast
  ring

private lemma matEntries_m₁₂ (p : Pose ℚ) : (matEntries p).m₁₂
    = ((RationalApprox.sinNum13 p.φ₂ * 10 ^ 13 : ℤ) : ℚ) / 10 ^ 26 := by
  show RationalApprox.sinℚ p.φ₂ = _
  rw [← RationalApprox.sinNum13_div_eq p.φ₂]
  push_cast
  ring

private lemma pythonVertexA_intCast (a : VertexIndex) (c : Fin 3) :
    pythonVertexA a c = (pythonVertexNumCurried a.ℓ a.i a.k c : ℚ) / 10 ^ 16 := by
  rw [pythonVertexA_eq]
  exact pythonVertexNumCurried_eq a.ℓ a.i a.k c

/-- The integer core computes exactly the ℚ check (in the positive-radius
regime, which is the only one `Row.ValidLocal` evaluates it in). -/
theorem checkN_eq_check (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) {ε δ r : ℚ}
    (hε : 0 < ε) (hr : 0 < r) :
    checkN Qi p ε δ r = check Qi p ε δ r := by
  have hm00 := matEntries_m₀₀ p
  have hm01 := matEntries_m₀₁ p
  have hm02 := matEntries_m₀₂ p
  have hm10 := matEntries_m₁₀ p
  have hm11 := matEntries_m₁₁ p
  have hm12 := matEntries_m₁₂ p
  have hv := pythonVertexA_intCast
  rw [Bool.eq_iff_iff]
  unfold checkN check
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]
  refine forall_congr' fun i => ?_
  refine forall_congr' fun k => ?_
  refine imp_congr_right fun _ => ?_
  rw [rowDots_fst (matEntries p) (Qi i), rowDots_snd (matEntries p) (Qi i),
      rowDots_fst (matEntries p) k, rowDots_snd (matEntries p) k]
  exact pair_test_iff _ _ _ _ _ _ _ _ _ _ _
    (sqrtDvCurriedN (Qi i).ℓ (Qi i).i (Qi i).k k.ℓ k.i k.k)
    hm00 hm01 hm02 hm10 hm11 hm12
    (hv (Qi i) 0) (hv (Qi i) 1) (hv (Qi i) 2)
    (hv k 0) (hv k 1) (hv k 2)
    rfl hε hr

/-! ## Integer rendering of the `r`-condition (`BoundRℚ`)

`checkNR` recomputes `BoundRℚ.check` with the same scale conventions as
`checkN`: matrix entries at `10²⁶`, vertex coordinates at `10¹⁶`, the
`round13`ed row dots at `10¹³` via integer division by `10²⁹`, and the
fixed-point lower square root as a bare `Nat.sqrt` at scale `10¹³`
(`sqrtNumLow26`). The comparison against `r + √2⁺·ε + 3κℚ` is
cross-multiplied by the (always positive) denominator product
`100·r.den·ε.den·10¹³`, so no sign hypotheses are needed. -/

/-- Integer rendering of `BoundRℚ.check` (the `r_valid` conjunct of
`Row.ValidLocal`). -/
def checkNR (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (ε r : ℚ) : Bool :=
  -- trig numerators (scale 10¹³) and matrix entries (scale 10²⁶), as in `checkN`
  let stN : ℤ := sinNum13 p.θ₂
  let ctN : ℤ := cosNum13 p.θ₂
  let spN : ℤ := sinNum13 p.φ₂
  let cpN : ℤ := cosNum13 p.φ₂
  let E00 := -stN * 10 ^ 13
  let E01 := ctN * 10 ^ 13
  let E10 := -(ctN * cpN)
  let E11 := -(stN * cpN)
  let E12 := spN * 10 ^ 13
  -- `r + √2⁺·ε + 3κℚ < s/10¹³` cross-multiplied by `100·rd·εd·10¹³ > 0`
  let lhsN := (100 * r.num * (ε.den : ℤ) + 142 * ε.num * (r.den : ℤ)) * 10 ^ 13
      + 300 * (r.den : ℤ) * (ε.den : ℤ) * 10 ^ 3
  let c := 100 * (r.den : ℤ) * (ε.den : ℤ)
  (List.finRange 3).all fun i =>
    let a := Qi i
    let w0 := pythonVertexNumCurried a.ℓ a.i a.k 0
    let w1 := pythonVertexNumCurried a.ℓ a.i a.k 1
    let w2 := pythonVertexNumCurried a.ℓ a.i a.k 2
    let q0 := (E00 * w0 + E01 * w1) / 10 ^ 29                -- scale 10¹³
    let q1 := (E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29
    decide (lhsN < c * sqrtNumLow26 (q0 * q0 + q1 * q1))

/-- One `i` of `checkNR` decides exactly the corresponding test of
`BoundRℚ.check`, given the atom correspondences. Unlike `pair_test_iff`, no
positivity hypotheses on `ε`, `r` are needed: the cross-multiplier is a
product of denominators. -/
private lemma r_test_iff (E00 E01 E10 E11 E12 w0 w1 w2 : ℤ)
    {m00 m01 m02 m10 m11 m12 wq0 wq1 wq2 : ℚ} (ε r : ℚ)
    (hm00 : m00 = (E00 : ℚ) / 10 ^ 26) (hm01 : m01 = (E01 : ℚ) / 10 ^ 26)
    (hm02 : m02 = 0)
    (hm10 : m10 = (E10 : ℚ) / 10 ^ 26) (hm11 : m11 = (E11 : ℚ) / 10 ^ 26)
    (hm12 : m12 = (E12 : ℚ) / 10 ^ 26)
    (hw0 : wq0 = (w0 : ℚ) / 10 ^ 16) (hw1 : wq1 = (w1 : ℚ) / 10 ^ 16)
    (hw2 : wq2 = (w2 : ℚ) / 10 ^ 16) :
    ((100 * r.num * (ε.den : ℤ) + 142 * ε.num * (r.den : ℤ)) * 10 ^ 13
        + 300 * (r.den : ℤ) * (ε.den : ℤ) * 10 ^ 3
      < 100 * (r.den : ℤ) * (ε.den : ℤ) * sqrtNumLow26
          ((E00 * w0 + E01 * w1) / 10 ^ 29 * ((E00 * w0 + E01 * w1) / 10 ^ 29)
            + (E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29
              * ((E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29)))
    ↔ r + RationalApprox.sqrtApprox16.upper_sqrt_two * ε + 3 * RationalApprox.κℚ
        < RationalApprox.sqrtApprox16.lower_sqrt.f
            (RationalApprox.round13 (m00 * wq0 + m01 * wq1 + m02 * wq2)
              * RationalApprox.round13 (m00 * wq0 + m01 * wq1 + m02 * wq2)
              + RationalApprox.round13 (m10 * wq0 + m11 * wq1 + m12 * wq2)
                * RationalApprox.round13 (m10 * wq0 + m11 * wq1 + m12 * wq2)) := by
  have hf : RationalApprox.sqrtApprox16.lower_sqrt.f = RationalApprox.sqrtℚLow13 := rfl
  have h2c : RationalApprox.sqrtApprox16.upper_sqrt_two = 71 / 50 := by
    norm_num [RationalApprox.sqrtApprox16]
  have hκc : RationalApprox.κℚ = 1 / 10 ^ 10 := rfl
  rw [hm00, hm01, hm02, hm10, hm11, hm12, hw0, hw1, hw2]
  rw [show (E00 : ℚ) / 10 ^ 26 * ((w0 : ℚ) / 10 ^ 16) + (E01 : ℚ) / 10 ^ 26 * ((w1 : ℚ) / 10 ^ 16)
        + 0 * ((w2 : ℚ) / 10 ^ 16) = ((E00 * w0 + E01 * w1 : ℤ) : ℚ) / 10 ^ 42 from by
      push_cast; ring]
  rw [show (E10 : ℚ) / 10 ^ 26 * ((w0 : ℚ) / 10 ^ 16) + (E11 : ℚ) / 10 ^ 26 * ((w1 : ℚ) / 10 ^ 16)
        + (E12 : ℚ) / 10 ^ 26 * ((w2 : ℚ) / 10 ^ 16)
        = ((E10 * w0 + E11 * w1 + E12 * w2 : ℤ) : ℚ) / 10 ^ 42 from by
      push_cast; ring]
  simp only [round13_intCast_div42]
  rw [show ((((E00 * w0 + E01 * w1) / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13) *
        ((((E00 * w0 + E01 * w1) / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13) +
        ((((E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13) *
        ((((E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29 : ℤ) : ℚ) / 10 ^ 13)
        = (((E00 * w0 + E01 * w1) / 10 ^ 29 * ((E00 * w0 + E01 * w1) / 10 ^ 29) +
            (E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29 *
              ((E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29) : ℤ) : ℚ)
          / 10 ^ 26 from by push_cast; ring]
  rw [hf]
  simp only [sqrtℚLow13_intCast_div26]
  rw [h2c, hκc]
  set en := ε.num with hen
  set ed : ℤ := (ε.den : ℤ) with hed
  set rn := r.num with hrn
  set rd : ℤ := (r.den : ℤ) with hrd
  set S := sqrtNumLow26
      ((E00 * w0 + E01 * w1) / 10 ^ 29 * ((E00 * w0 + E01 * w1) / 10 ^ 29)
        + (E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29
          * ((E10 * w0 + E11 * w1 + E12 * w2) / 10 ^ 29)) with hS
  have hed_pos : (0:ℤ) < ed := by rw [hed]; exact_mod_cast ε.pos
  have hrd_pos : (0:ℤ) < rd := by rw [hrd]; exact_mod_cast r.pos
  have hedQ : (0:ℚ) < (ed : ℚ) := by exact_mod_cast hed_pos
  have hrdQ : (0:ℚ) < (rd : ℚ) := by exact_mod_cast hrd_pos
  have hεq : ε = (en : ℚ) / (ed : ℚ) := by
    rw [hen, hed]; push_cast; exact (Rat.num_div_den ε).symm
  have hrq : r = (rn : ℚ) / (rd : ℚ) := by
    rw [hrn, hrd]; push_cast; exact (Rat.num_div_den r).symm
  rw [hεq, hrq]
  constructor <;> intro h <;> qify at h ⊢ <;> field_simp at h ⊢ <;> linarith

/-- The integer core computes exactly the ℚ `r`-condition check. -/
theorem checkNR_eq_check (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (ε r : ℚ) :
    checkNR Qi p ε r
      = RationalApprox.LocalTheorem.BoundRℚ.check r ε p (pythonVertexA ∘ Qi)
          RationalApprox.sqrtApprox16 := by
  have hm00 := matEntries_m₀₀ p
  have hm01 := matEntries_m₀₁ p
  have hm02 := matEntries_m₀₂ p
  have hm10 := matEntries_m₁₀ p
  have hm11 := matEntries_m₁₁ p
  have hm12 := matEntries_m₁₂ p
  rw [Bool.eq_iff_iff]
  unfold checkNR RationalApprox.LocalTheorem.BoundRℚ.check
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq,
    Function.comp_apply]
  refine forall_congr' fun i => ?_
  exact r_test_iff _ _ _ _ _ _ _ _ ε r
    hm00 hm01 hm02 hm10 hm11 hm12
    (pythonVertexA_intCast (Qi i) 0) (pythonVertexA_intCast (Qi i) 1)
    (pythonVertexA_intCast (Qi i) 2)

/-- `BoundRℚ` (the `r_valid` conjunct of `Row.ValidLocal`) decided through
the integer core. Out-prioritizes the ℚ route
`BoundRℚ.instDecidablePyV` (`Checker/Local.lean`); picked up by the
re-derived `Row.ValidLocal` instance in `Checker/LocalFastNat.lean`. -/
instance (priority := 10600) instDecidableBoundRPy (r ε : ℚ) (p : Pose ℚ)
    (idx : Fin 3 → VertexIndex) :
    Decidable (RationalApprox.LocalTheorem.BoundRℚ r ε p (pythonVertexA ∘ idx)
      RationalApprox.sqrtApprox16) :=
  decidable_of_iff (checkNR idx p ε r = true)
    (by rw [checkNR_eq_check]
        exact RationalApprox.LocalTheorem.BoundRℚ.check_iff r ε p _ _)

end Noperthedron.Solution.BεℚPy

namespace Noperthedron.Solution

open Noperthedron RationalApprox

/-! ## Integer rendering of the `Aεℚσ` conjunct (for `X = vecXℚ θ φ`)

`Aεℚσ` is an exact ℚ inequality (no rounding), so the integer form is a pure
cross-multiplication: the `vecXℚ` components are `10²⁶`-scale numerators
(products of two `10¹³` trig numerators), vertices are `10¹⁶`-scale, and the
comparison against `√2⁺·ε + 3κℚ` is multiplied through by the positive
denominator product `50·ε.den·10⁴²`. -/

namespace AεℚPy

/-- Integer rendering of `Aεℚσ.check` at `X = vecXℚ θ φ`. -/
def checkN (θ φ : ℚ) (idx : Fin 3 → VertexIndex) (ε : ℚ) (σ : ℕ) : Bool :=
  let stN : ℤ := sinNum13 θ
  let ctN : ℤ := cosNum13 θ
  let spN : ℤ := sinNum13 φ
  let cpN : ℤ := cosNum13 φ
  let sg : ℤ := (-1) ^ σ
  let x0 := sg * (ctN * spN)                    -- scale 10²⁶
  let x1 := sg * (stN * spN)
  let x2 := sg * (cpN * 10 ^ 13)
  let εn : ℤ := ε.num
  let εd : ℤ := ε.den
  let rhsN := 71 * εn * 10 ^ 42 + 150 * εd * 10 ^ 32
  (List.finRange 3).all fun i =>
    let a := idx i
    let w0 := pythonVertexNumCurried a.ℓ a.i a.k 0
    let w1 := pythonVertexNumCurried a.ℓ a.i a.k 1
    let w2 := pythonVertexNumCurried a.ℓ a.i a.k 2
    decide (rhsN < 50 * εd * (x0 * w0 + x1 * w1 + x2 * w2))

/-- One `i` of `checkN` decides the corresponding test of `Aεℚσ.check`. -/
private lemma a_test_iff (X0 X1 X2 w0 w1 w2 : ℤ)
    {xq0 xq1 xq2 wq0 wq1 wq2 : ℚ} (ε : ℚ)
    (hx0 : xq0 = (X0 : ℚ) / 10 ^ 26) (hx1 : xq1 = (X1 : ℚ) / 10 ^ 26)
    (hx2 : xq2 = (X2 : ℚ) / 10 ^ 26)
    (hw0 : wq0 = (w0 : ℚ) / 10 ^ 16) (hw1 : wq1 = (w1 : ℚ) / 10 ^ 16)
    (hw2 : wq2 = (w2 : ℚ) / 10 ^ 16) :
    (71 * ε.num * 10 ^ 42 + 150 * (ε.den : ℤ) * 10 ^ 32
      < 50 * (ε.den : ℤ) * (X0 * w0 + X1 * w1 + X2 * w2))
    ↔ RationalApprox.sqrtApprox16.upper_sqrt_two * ε + 3 * RationalApprox.κℚ
        < xq0 * wq0 + xq1 * wq1 + xq2 * wq2 := by
  have h2c : RationalApprox.sqrtApprox16.upper_sqrt_two = 71 / 50 := by
    norm_num [RationalApprox.sqrtApprox16]
  have hκc : RationalApprox.κℚ = 1 / 10 ^ 10 := rfl
  rw [hx0, hx1, hx2, hw0, hw1, hw2, h2c, hκc]
  rw [show (X0 : ℚ) / 10 ^ 26 * ((w0 : ℚ) / 10 ^ 16) + (X1 : ℚ) / 10 ^ 26 * ((w1 : ℚ) / 10 ^ 16)
        + (X2 : ℚ) / 10 ^ 26 * ((w2 : ℚ) / 10 ^ 16)
        = ((X0 * w0 + X1 * w1 + X2 * w2 : ℤ) : ℚ) / 10 ^ 42 from by push_cast; ring]
  set en := ε.num with hen
  set ed : ℤ := (ε.den : ℤ) with hed
  have hed_pos : (0:ℤ) < ed := by rw [hed]; exact_mod_cast ε.pos
  have hedQ : (0:ℚ) < (ed : ℚ) := by exact_mod_cast hed_pos
  have hεq : ε = (en : ℚ) / (ed : ℚ) := by
    rw [hen, hed]; push_cast; exact (Rat.num_div_den ε).symm
  rw [hεq]
  constructor <;> intro h <;> qify at h ⊢ <;> field_simp at h ⊢ <;> linarith

/-- The integer core computes exactly the ℚ `Aεℚσ` check at `X = vecXℚ θ φ`. -/
theorem checkN_eq_check (θ φ : ℚ) (idx : Fin 3 → VertexIndex) (ε : ℚ) (σ : ℕ) :
    checkN θ φ idx ε σ
      = Local.TriangleQ.Aεℚσ.check (vecXℚ θ φ) (pythonVertexA ∘ idx) ε σ
          RationalApprox.sqrtApprox16 := by
  have hx0 : ((-1:ℚ)) ^ σ * vecXℚ θ φ 0
      = (((-1) ^ σ * (cosNum13 θ * sinNum13 φ) : ℤ) : ℚ) / 10 ^ 26 := by
    show ((-1:ℚ)) ^ σ * (cosℚ θ * sinℚ φ) = _
    rw [← cosNum13_div_eq θ, ← sinNum13_div_eq φ]
    push_cast
    ring
  have hx1 : ((-1:ℚ)) ^ σ * vecXℚ θ φ 1
      = (((-1) ^ σ * (sinNum13 θ * sinNum13 φ) : ℤ) : ℚ) / 10 ^ 26 := by
    show ((-1:ℚ)) ^ σ * (sinℚ θ * sinℚ φ) = _
    rw [← sinNum13_div_eq θ, ← sinNum13_div_eq φ]
    push_cast
    ring
  have hx2 : ((-1:ℚ)) ^ σ * vecXℚ θ φ 2
      = (((-1) ^ σ * (cosNum13 φ * 10 ^ 13) : ℤ) : ℚ) / 10 ^ 26 := by
    show ((-1:ℚ)) ^ σ * cosℚ φ = _
    rw [← cosNum13_div_eq φ]
    push_cast
    ring
  rw [Bool.eq_iff_iff]
  unfold checkN Local.TriangleQ.Aεℚσ.check
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq,
    Function.comp_apply]
  refine forall_congr' fun i => ?_
  exact a_test_iff _ _ _ _ _ _ ε hx0 hx1 hx2
    (BεℚPy.pythonVertexA_intCast (idx i) 0) (BεℚPy.pythonVertexA_intCast (idx i) 1)
    (BεℚPy.pythonVertexA_intCast (idx i) 2)

/-- `Aεℚσ` at `X = vecXℚ θ φ` decided through the integer core.
Out-prioritizes `Aεℚσ.instDecidablePyV` (`Checker/Local.lean`); picked up by
the re-derived `Row.ValidLocal` instance in `Checker/LocalFastNat.lean`. -/
instance (priority := 10600) instDecidableAPyN (θ φ : ℚ) (idx : Fin 3 → VertexIndex)
    (ε : ℚ) (σ : ℕ) :
    Decidable (Local.TriangleQ.Aεℚσ (vecXℚ θ φ) (pythonVertexA ∘ idx) ε σ
      RationalApprox.sqrtApprox16) :=
  decidable_of_iff (checkN θ φ idx ε σ = true)
    (by rw [checkN_eq_check]
        exact Local.TriangleQ.Aεℚσ.check_iff _ _ _ _ _)

end AεℚPy

/-! ## Integer rendering of the `Spanningℚ` conjunct

Also an exact ℚ inequality.  Both factors of each spanning product are
`10⁴²`-scale dots (matrix rows at `10²⁶` × vertices at `10¹⁶`), so the
products sit at `10⁸⁴`; the comparison against `2ε(√2⁺+ε) + 6κℚ` is
multiplied through by `50·ε.den²·10⁸⁴`. -/

namespace SpanningPy

/-- Integer rendering of `Spanningℚ.check`. -/
def checkN (θ φ ε : ℚ) (idx : Fin 3 → VertexIndex) : Bool :=
  let stN : ℤ := sinNum13 θ
  let ctN : ℤ := cosNum13 θ
  let spN : ℤ := sinNum13 φ
  let cpN : ℤ := cosNum13 φ
  let E00 := -stN * 10 ^ 13                     -- rows at scale 10²⁶
  let E01 := ctN * 10 ^ 13
  let E10 := -(ctN * cpN)
  let E11 := -(stN * cpN)
  let E12 := spN * 10 ^ 13
  let εn : ℤ := ε.num
  let εd : ℤ := ε.den
  let lhsN := 2 * εn * (71 * εd + 50 * εn) * 10 ^ 84 + 300 * εd ^ 2 * 10 ^ 74
  (List.finRange 3).all fun i =>
    let a := idx i
    let b := idx (i + 1)
    let v0 := pythonVertexNumCurried a.ℓ a.i a.k 0
    let v1 := pythonVertexNumCurried a.ℓ a.i a.k 1
    let v2 := pythonVertexNumCurried a.ℓ a.i a.k 2
    let w0 := pythonVertexNumCurried b.ℓ b.i b.k 0
    let w1 := pythonVertexNumCurried b.ℓ b.i b.k 1
    let w2 := pythonVertexNumCurried b.ℓ b.i b.k 2
    let r0v := E00 * v0 + E01 * v1               -- scale 10⁴²
    let r1v := E10 * v0 + E11 * v1 + E12 * v2
    let r0w := E00 * w0 + E01 * w1
    let r1w := E10 * w0 + E11 * w1 + E12 * w2
    decide (lhsN < 50 * εd ^ 2 * (-r1v * r0w + r0v * r1w))

/-- One `i` of `checkN` decides the corresponding test of `Spanningℚ.check`. -/
private lemma s_test_iff (stN ctN spN cpN v0 v1 v2 w0 w1 w2 : ℤ)
    {stq ctq spq cpq vq0 vq1 vq2 wq0 wq1 wq2 : ℚ} (ε : ℚ)
    (hst : stq = (stN : ℚ) / 10 ^ 13) (hct : ctq = (ctN : ℚ) / 10 ^ 13)
    (hsp : spq = (spN : ℚ) / 10 ^ 13) (hcp : cpq = (cpN : ℚ) / 10 ^ 13)
    (hv0 : vq0 = (v0 : ℚ) / 10 ^ 16) (hv1 : vq1 = (v1 : ℚ) / 10 ^ 16)
    (hv2 : vq2 = (v2 : ℚ) / 10 ^ 16)
    (hw0 : wq0 = (w0 : ℚ) / 10 ^ 16) (hw1 : wq1 = (w1 : ℚ) / 10 ^ 16)
    (hw2 : wq2 = (w2 : ℚ) / 10 ^ 16) :
    (2 * ε.num * (71 * (ε.den : ℤ) + 50 * ε.num) * 10 ^ 84
        + 300 * (ε.den : ℤ) ^ 2 * 10 ^ 74
      < 50 * (ε.den : ℤ) ^ 2 *
          (-(-(ctN * cpN) * v0 + -(stN * cpN) * v1 + spN * 10 ^ 13 * v2)
              * (-stN * 10 ^ 13 * w0 + ctN * 10 ^ 13 * w1)
            + (-stN * 10 ^ 13 * v0 + ctN * 10 ^ 13 * v1)
              * (-(ctN * cpN) * w0 + -(stN * cpN) * w1 + spN * 10 ^ 13 * w2)))
    ↔ 2 * ε * (sqrt_twoℚ + ε) + 6 * RationalApprox.κℚ
        < -(-ctq * cpq * vq0 + -stq * cpq * vq1 + spq * vq2) * (-stq * wq0 + ctq * wq1)
          + (-stq * vq0 + ctq * vq1) * (-ctq * cpq * wq0 + -stq * cpq * wq1 + spq * wq2) := by
  have h2c : sqrt_twoℚ = 71 / 50 := by norm_num [sqrt_twoℚ]
  have hκc : RationalApprox.κℚ = 1 / 10 ^ 10 := rfl
  rw [hst, hct, hsp, hcp, hv0, hv1, hv2, hw0, hw1, hw2, h2c, hκc]
  rw [show -(-((ctN : ℚ) / 10 ^ 13) * ((cpN : ℚ) / 10 ^ 13) * ((v0 : ℚ) / 10 ^ 16)
          + -((stN : ℚ) / 10 ^ 13) * ((cpN : ℚ) / 10 ^ 13) * ((v1 : ℚ) / 10 ^ 16)
          + (spN : ℚ) / 10 ^ 13 * ((v2 : ℚ) / 10 ^ 16))
          * (-((stN : ℚ) / 10 ^ 13) * ((w0 : ℚ) / 10 ^ 16)
            + (ctN : ℚ) / 10 ^ 13 * ((w1 : ℚ) / 10 ^ 16))
        + (-((stN : ℚ) / 10 ^ 13) * ((v0 : ℚ) / 10 ^ 16)
            + (ctN : ℚ) / 10 ^ 13 * ((v1 : ℚ) / 10 ^ 16))
          * (-((ctN : ℚ) / 10 ^ 13) * ((cpN : ℚ) / 10 ^ 13) * ((w0 : ℚ) / 10 ^ 16)
            + -((stN : ℚ) / 10 ^ 13) * ((cpN : ℚ) / 10 ^ 13) * ((w1 : ℚ) / 10 ^ 16)
            + (spN : ℚ) / 10 ^ 13 * ((w2 : ℚ) / 10 ^ 16))
        = ((-(-(ctN * cpN) * v0 + -(stN * cpN) * v1 + spN * 10 ^ 13 * v2)
              * (-stN * 10 ^ 13 * w0 + ctN * 10 ^ 13 * w1)
            + (-stN * 10 ^ 13 * v0 + ctN * 10 ^ 13 * v1)
              * (-(ctN * cpN) * w0 + -(stN * cpN) * w1 + spN * 10 ^ 13 * w2) : ℤ) : ℚ)
          / 10 ^ 84 from by push_cast; ring]
  set en := ε.num with hen
  set ed : ℤ := (ε.den : ℤ) with hed
  have hed_pos : (0:ℤ) < ed := by rw [hed]; exact_mod_cast ε.pos
  have hedQ : (0:ℚ) < (ed : ℚ) := by exact_mod_cast hed_pos
  have hεq : ε = (en : ℚ) / (ed : ℚ) := by
    rw [hen, hed]; push_cast; exact (Rat.num_div_den ε).symm
  rw [hεq]
  constructor <;> intro h <;> qify at h ⊢ <;> field_simp at h ⊢ <;> linarith

/-- The integer core computes exactly the ℚ spanning check. -/
theorem checkN_eq_check (θ φ ε : ℚ) (idx : Fin 3 → VertexIndex) :
    checkN θ φ ε idx = Spanningℚ.check θ φ ε (pythonVertexA ∘ idx) := by
  have hst := (sinNum13_div_eq θ).symm
  have hct := (cosNum13_div_eq θ).symm
  have hsp := (sinNum13_div_eq φ).symm
  have hcp := (cosNum13_div_eq φ).symm
  rw [Bool.eq_iff_iff]
  unfold checkN Spanningℚ.check
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq,
    Function.comp_apply]
  refine forall_congr' fun i => ?_
  exact s_test_iff _ _ _ _ _ _ _ _ _ _ ε hst hct hsp hcp
    (BεℚPy.pythonVertexA_intCast (idx i) 0) (BεℚPy.pythonVertexA_intCast (idx i) 1)
    (BεℚPy.pythonVertexA_intCast (idx i) 2)
    (BεℚPy.pythonVertexA_intCast (idx (i + 1)) 0)
    (BεℚPy.pythonVertexA_intCast (idx (i + 1)) 1)
    (BεℚPy.pythonVertexA_intCast (idx (i + 1)) 2)

/-- `Spanningℚ` decided through the integer core. Out-prioritizes
`Spanningℚ.instDecidablePyV` (`Checker/Local.lean`). -/
instance (priority := 10600) instDecidableSPyN (θ φ ε : ℚ) (idx : Fin 3 → VertexIndex) :
    Decidable (Spanningℚ θ φ ε (pythonVertexA ∘ idx)) :=
  decidable_of_iff (checkN θ φ ε idx = true)
    (by rw [checkN_eq_check]
        exact Spanningℚ.check_iff _ _ _ _)

end SpanningPy

end Noperthedron.Solution

end
