module

public import Mathlib.Data.Finset.Max

public import Noperthedron.Checker.ApproxSqrt
public import Noperthedron.Checker.SqrtDvLiterals
public import Noperthedron.Checker.SqrtFixed
public import Noperthedron.RationalApprox.TrigInt
public import Noperthedron.Local.Congruent
public import Noperthedron.RationalApprox.Basic
public import Noperthedron.RationalApprox.RationalLocal
public import Noperthedron.SolutionTable.Defs
public import Noperthedron.Vertices.Exact
public import Noperthedron.Vertices.Python
public import Noperthedron.Vertices.PythonInt
public import Noperthedron.Vertices.Symmetry
public import Noperthedron.Vertices.Trig
-- Mirror the imports at the meta phase so the test `#eval`s below can
-- interpret cross-module code under the module system.
public meta import Mathlib.Data.Finset.Max
public meta import Noperthedron.Checker.ApproxSqrt
public meta import Noperthedron.Checker.SqrtDvLiterals
public meta import Noperthedron.Checker.SqrtFixed
public meta import Noperthedron.RationalApprox.TrigInt
public meta import Noperthedron.Local.Congruent
public meta import Noperthedron.RationalApprox.Basic
public meta import Noperthedron.RationalApprox.RationalLocal
public meta import Noperthedron.SolutionTable.Defs
public meta import Noperthedron.Vertices.Exact
public meta import Noperthedron.Vertices.Python
public meta import Noperthedron.Vertices.PythonInt
public meta import Noperthedron.Vertices.Symmetry
public meta import Noperthedron.Vertices.Trig

@[expose] public section


/-!
# Local Validity Checker

A computable, pure-ℚ checker that verifies whether a decision-tree row
satisfies the preconditions of the rational local theorem. Everything
here is computable — no `noncomputable` keyword.
-/

namespace Noperthedron.Solution

abbrev sqrt_twoℚ : ℚ := 142 / 100

abbrev Row.Pi (r : Row) : Fin 3 → VertexIndex :=
  ![r.P1_index, r.P2_index, r.P3_index]

abbrev Row.Qi (r : Row) : Fin 3 → VertexIndex :=
  ![r.Q1_index, r.Q2_index, r.Q3_index]

abbrev Row.X₁ (r : Row) : Fin 3 → ℚ := RationalApprox.vecXℚ r.θ₁ r.φ₁

abbrev Row.X₂ (r : Row) : Fin 3 → ℚ := RationalApprox.vecXℚ r.θ₂ r.φ₂

abbrev rot90 : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, -1; 1, 0]

abbrev Row.r (row : Row) : ℚ :=
  row.r' / 1000

open scoped Matrix
open RationalApprox (sqrtApprox16 κℚ)

/-! ### Spanning condition: hoisted trig, scalarized applied vectors -/

/-- The rational matrix form of the ε-κ-spanning condition on the triangle `T`
for angles `(θ, φ)` (cf. `Local.Triangle.κSpanning`). Named so that its
`Decidable` instance (via `Spanningℚ.check`) can hoist the trig entries of
`rotMℚ_mat θ φ` out of the `i`-loop and bind the applied vectors' components
as scalars; the generic `mulVec`/`dotProduct` instances would re-evaluate the
trig partial sums on every component access. -/
def Spanningℚ (θ φ ε : ℚ) (T : Fin 3 → Fin 3 → ℚ) : Prop :=
  ∀ i : Fin 3,
    2 * ε * (sqrt_twoℚ + ε) + 6 * κℚ <
    (rot90 *ᵥ (RationalApprox.rotMℚ_mat θ φ *ᵥ T i)) ⬝ᵥ
      (RationalApprox.rotMℚ_mat θ φ *ᵥ T (i + 1))

namespace Spanningℚ

open RationalApprox (sinℚ cosℚ)

/-- The spanning dot product `⟨rot90 · M·v, M·w⟩` in scalar form. -/
private lemma term_eq (θ φ : ℚ) (v w : Fin 3 → ℚ) :
    (rot90 *ᵥ (RationalApprox.rotMℚ_mat θ φ *ᵥ v)) ⬝ᵥ
      (RationalApprox.rotMℚ_mat θ φ *ᵥ w) =
    -(-cosℚ θ * cosℚ φ * v 0 + -sinℚ θ * cosℚ φ * v 1 + sinℚ φ * v 2) *
        (-sinℚ θ * w 0 + cosℚ θ * w 1) +
      (-sinℚ θ * v 0 + cosℚ θ * v 1) *
        (-cosℚ θ * cosℚ φ * w 0 + -sinℚ θ * cosℚ φ * w 1 + sinℚ φ * w 2) := by
  simp only [dotProduct, Matrix.mulVec, rot90, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_fin_one, RationalApprox.rotMℚ_mat, neg_mul, Fin.sum_univ_three,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.sum_univ_two, zero_mul, add_zero, one_mul, neg_add_rev, neg_neg, zero_add]

/-- Bool-valued `Spanningℚ` check: trig partial sums are evaluated once per
pose and everything the `i`-loop touches is bound as a scalar. -/
def check (θ φ ε : ℚ) (T : Fin 3 → Fin 3 → ℚ) : Bool :=
  let st := sinℚ θ
  let ct := cosℚ θ
  let sp := sinℚ φ
  let cp := cosℚ φ
  let lhs := 2 * ε * (sqrt_twoℚ + ε) + 6 * κℚ
  (List.finRange 3).all fun i =>
    let v := T i
    let w := T (i + 1)
    let v0 := v 0
    let v1 := v 1
    let v2 := v 2
    let w0 := w 0
    let w1 := w 1
    let w2 := w 2
    decide (lhs <
      -(-ct * cp * v0 + -st * cp * v1 + sp * v2) * (-st * w0 + ct * w1) +
        (-st * v0 + ct * v1) * (-ct * cp * w0 + -st * cp * w1 + sp * w2))

theorem check_iff (θ φ ε : ℚ) (T : Fin 3 → Fin 3 → ℚ) :
    check θ φ ε T = true ↔ Spanningℚ θ φ ε T := by
  unfold check Spanningℚ
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]
  refine forall_congr' fun i => ?_
  rw [term_eq θ φ (T i) (T (i + 1))]

instance instDecidable (θ φ ε : ℚ) (T : Fin 3 → Fin 3 → ℚ) :
    Decidable (Spanningℚ θ φ ε T) :=
  decidable_of_iff _ (check_iff θ φ ε T)

end Spanningℚ

/-! ### `Row.δ`: max over per-`i` `BoundDeltaℚi` values, hoisting trig once -/

namespace Row.δ

open RationalApprox (sinℚ cosℚ)

/-- The ten sin/cos values (of `θ₁ φ₁ α θ₂ φ₂`) of a rational pose, evaluated once per pose. -/
structure PoseTrigQ where
  (st1 ct1 sp1 cp1 sa ca st2 ct2 sp2 cp2 : ℚ)

@[inline] def PoseTrigQ.ofPose (p : Pose ℚ) : PoseTrigQ where
  st1 := (RationalApprox.sinNum13 p.θ₁ : ℚ) / 10 ^ 13
  ct1 := (RationalApprox.cosNum13 p.θ₁ : ℚ) / 10 ^ 13
  sp1 := (RationalApprox.sinNum13 p.φ₁ : ℚ) / 10 ^ 13
  cp1 := (RationalApprox.cosNum13 p.φ₁ : ℚ) / 10 ^ 13
  sa := (RationalApprox.sinNum13 p.α : ℚ) / 10 ^ 13
  ca := (RationalApprox.cosNum13 p.α : ℚ) / 10 ^ 13
  st2 := (RationalApprox.sinNum13 p.θ₂ : ℚ) / 10 ^ 13
  ct2 := (RationalApprox.cosNum13 p.θ₂ : ℚ) / 10 ^ 13
  sp2 := (RationalApprox.sinNum13 p.φ₂ : ℚ) / 10 ^ 13
  cp2 := (RationalApprox.cosNum13 p.φ₂ : ℚ) / 10 ^ 13

/-- `BoundDeltaℚi` for a single `i`, with the 10 trig values used by
`M₁`, `R`, `M₂` passed in already evaluated. -/
@[inline] def boundDelta_at (t : PoseTrigQ) (P Q : Fin 3 → ℚ) : ℚ :=
  -- M₁ * P
  let m1p_0 := -t.st1 * P 0 + t.ct1 * P 1
  let m1p_1 := (-t.ct1 * t.cp1) * P 0 + (-t.st1 * t.cp1) * P 1 + t.sp1 * P 2
  -- R * (M₁ * P)
  let rm1p_0 := t.ca * m1p_0 + (-t.sa) * m1p_1
  let rm1p_1 := t.sa * m1p_0 + t.ca * m1p_1
  -- M₂ * Q
  let m2q_0 := -t.st2 * Q 0 + t.ct2 * Q 1
  let m2q_1 := (-t.ct2 * t.cp2) * Q 0 + (-t.st2 * t.cp2) * Q 1 + t.sp2 * Q 2
  let d0 := rm1p_0 - m2q_0
  let d1 := rm1p_1 - m2q_1
  let normSq := d0 * d0 + d1 * d1
  sqrtApprox16.upper_sqrt.f normSq / 2 + 3 * κℚ

lemma boundDelta_at_eq (p : Pose ℚ) (P Q : Fin 3 → ℚ) :
    boundDelta_at (.ofPose p) P Q =
    sqrtApprox16.upper_sqrt.norm (p.rotRℚ (p.rotM₁ℚ P) - p.rotM₂ℚ Q) / 2 + 3 * κℚ := by
  unfold boundDelta_at PoseTrigQ.ofPose RationalApprox.UpperSqrt.norm
  unfold Pose.rotRℚ Pose.rotM₁ℚ Pose.rotM₂ℚ
  unfold RationalApprox.rotRℚ RationalApprox.rotMℚ
  unfold RationalApprox.rotRℚ_mat RationalApprox.rotMℚ_mat
  rw [show (Matrix.toLin' _ : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ))
        ((Matrix.toLin' _ : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) P) -
       (Matrix.toLin' _ : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) Q
       = fun (j : Fin 2) =>
         (Matrix.toLin' _ ((Matrix.toLin' _ : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) P)) j -
         ((Matrix.toLin' _ : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) Q) j from rfl]
  simp [RationalApprox.sinNum13_div_eq, RationalApprox.cosNum13_div_eq,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ### Integer core

The norm² is assembled exactly at scale `10¹¹⁰` (difference vector at `10⁵⁵`)
and the upper square root becomes one integer ceiling division plus
`Nat.sqrt` (`sqrtNum110`, output scale `10¹⁶`), so the whole per-`i` value is
`(sqrtNum110 … + 6·10⁶) / (2·10¹⁶)`.  The ℚ helpers above stay as the
proof-side bridge to `BoundDeltaℚi`. -/

/-- Integer form of `sqrtℚUp16` on inputs `S/10¹¹⁰`: the inner ceiling
`⌈S/10⁷⁸⌉` is `-((-S)/10⁷⁸)` (floor division). Output scale `10¹⁶`. -/
def sqrtNum110 (S : ℤ) : ℤ :=
  if S ≤ 0 then 0 else (Nat.sqrt (-(-S / 10 ^ 78)).toNat + 1 : ℕ)

private lemma sqrtℚUp16_intCast_div110 (S : ℤ) :
    RationalApprox.sqrtℚUp16 ((S : ℚ) / 10 ^ 110) = (sqrtNum110 S : ℚ) / 10 ^ 16 := by
  unfold RationalApprox.sqrtℚUp16 sqrtNum110
  rcases le_or_gt S 0 with hS | hS
  · rw [if_pos (div_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast hS, by positivity⟩)),
        if_pos hS]
    simp
  · have hSQ : (0:ℚ) < (S : ℚ) := by exact_mod_cast hS
    rw [if_neg (not_le.mpr (by positivity)), if_neg (not_le.mpr hS)]
    have hceil : ⌈(S : ℚ) / 10 ^ 110 * 10 ^ 32⌉ = -(-S / 10 ^ 78) := by
      rw [show (S : ℚ) / 10 ^ 110 * 10 ^ 32 = -(((-S : ℤ) : ℚ) / ((10 ^ 78 : ℕ) : ℚ)) from by
        push_cast; ring]
      rw [Int.ceil_neg, Rat.floor_intCast_div_natCast]
      norm_num
    rw [hceil]
    push_cast
    ring

/-- The ten trig numerators (scale `10¹³`) of a rational pose. -/
structure PoseTrigN where
  (st1 ct1 sp1 cp1 sa ca st2 ct2 sp2 cp2 : ℤ)

@[inline] def PoseTrigN.ofPose (p : Pose ℚ) : PoseTrigN where
  st1 := RationalApprox.sinNum13 p.θ₁
  ct1 := RationalApprox.cosNum13 p.θ₁
  sp1 := RationalApprox.sinNum13 p.φ₁
  cp1 := RationalApprox.cosNum13 p.φ₁
  sa := RationalApprox.sinNum13 p.α
  ca := RationalApprox.cosNum13 p.α
  st2 := RationalApprox.sinNum13 p.θ₂
  ct2 := RationalApprox.cosNum13 p.θ₂
  sp2 := RationalApprox.sinNum13 p.φ₂
  cp2 := RationalApprox.cosNum13 p.φ₂

/-- Integer core of `boundDelta_at` (up to the final `(·+6·10⁶)/(2·10¹⁶)`):
`M₁`-rows lifted to scale `10²⁶`, dots at `10⁴²`, the `R`-rotated and
`M₂`-lifted difference at `10⁵⁵`, norm² at `10¹¹⁰`. -/
@[inline] def boundDeltaN (t : PoseTrigN) (P0 P1 P2 Q0 Q1 Q2 : ℤ) : ℤ :=
  let m1p0 := -t.st1 * 10 ^ 13 * P0 + t.ct1 * 10 ^ 13 * P1
  let m1p1 := -(t.ct1 * t.cp1) * P0 + -(t.st1 * t.cp1) * P1 + t.sp1 * 10 ^ 13 * P2
  let rm1p0 := t.ca * m1p0 + -t.sa * m1p1
  let rm1p1 := t.sa * m1p0 + t.ca * m1p1
  let m2q0 := (-t.st2 * 10 ^ 13 * Q0 + t.ct2 * 10 ^ 13 * Q1) * 10 ^ 13
  let m2q1 := (-(t.ct2 * t.cp2) * Q0 + -(t.st2 * t.cp2) * Q1 + t.sp2 * 10 ^ 13 * Q2) * 10 ^ 13
  let d0 := rm1p0 - m2q0
  let d1 := rm1p1 - m2q1
  sqrtNum110 (d0 * d0 + d1 * d1)

/-- Closing step for `boundDeltaN_div_eq`: once the sqrt argument is known to
be a scale-`10¹¹⁰` integer fraction, the whole per-`i` value is
`(sqrtNum110 · + 6·10⁶)/(2·10¹⁶)`.  Stated over an abstract argument so that
`refine` can unify `N` and `x` from the goal without restating them. -/
private lemma sqrtNum110_step (N : ℤ) (x : ℚ) (hx : x = (N : ℚ) / 10 ^ 110) :
    ((sqrtNum110 N + 6 * 10 ^ 6 : ℤ) : ℚ) / (2 * 10 ^ 16)
      = RationalApprox.sqrtℚUp16 x / 2 + 3 * (1 / 10 ^ 10) := by
  rw [hx, sqrtℚUp16_intCast_div110]
  push_cast
  ring

lemma boundDeltaN_div_eq (p : Pose ℚ) (a b : VertexIndex) :
    ((boundDeltaN (PoseTrigN.ofPose p)
        (pythonVertexNumCurried a.ℓ a.i a.k 0) (pythonVertexNumCurried a.ℓ a.i a.k 1)
        (pythonVertexNumCurried a.ℓ a.i a.k 2) (pythonVertexNumCurried b.ℓ b.i b.k 0)
        (pythonVertexNumCurried b.ℓ b.i b.k 1) (pythonVertexNumCurried b.ℓ b.i b.k 2)
        + 6 * 10 ^ 6 : ℤ) : ℚ) / (2 * 10 ^ 16)
      = boundDelta_at (PoseTrigQ.ofPose p) (pythonVertex a) (pythonVertex b) := by
  set st1 := RationalApprox.sinNum13 p.θ₁ with hst1
  set ct1 := RationalApprox.cosNum13 p.θ₁ with hct1
  set sp1 := RationalApprox.sinNum13 p.φ₁ with hsp1
  set cp1 := RationalApprox.cosNum13 p.φ₁ with hcp1
  set sa := RationalApprox.sinNum13 p.α with hsa
  set ca := RationalApprox.cosNum13 p.α with hca
  set st2 := RationalApprox.sinNum13 p.θ₂ with hst2
  set ct2 := RationalApprox.cosNum13 p.θ₂ with hct2
  set sp2 := RationalApprox.sinNum13 p.φ₂ with hsp2
  set cp2 := RationalApprox.cosNum13 p.φ₂ with hcp2
  set P0 := pythonVertexNumCurried a.ℓ a.i a.k 0 with hP0
  set P1 := pythonVertexNumCurried a.ℓ a.i a.k 1 with hP1
  set P2 := pythonVertexNumCurried a.ℓ a.i a.k 2 with hP2
  set Q0 := pythonVertexNumCurried b.ℓ b.i b.k 0 with hQ0
  set Q1 := pythonVertexNumCurried b.ℓ b.i b.k 1 with hQ1
  set Q2 := pythonVertexNumCurried b.ℓ b.i b.k 2 with hQ2
  show ((sqrtNum110
      ((ca * (-st1 * 10 ^ 13 * P0 + ct1 * 10 ^ 13 * P1)
          + -sa * (-(ct1 * cp1) * P0 + -(st1 * cp1) * P1 + sp1 * 10 ^ 13 * P2)
          - (-st2 * 10 ^ 13 * Q0 + ct2 * 10 ^ 13 * Q1) * 10 ^ 13)
        * (ca * (-st1 * 10 ^ 13 * P0 + ct1 * 10 ^ 13 * P1)
          + -sa * (-(ct1 * cp1) * P0 + -(st1 * cp1) * P1 + sp1 * 10 ^ 13 * P2)
          - (-st2 * 10 ^ 13 * Q0 + ct2 * 10 ^ 13 * Q1) * 10 ^ 13)
        + (sa * (-st1 * 10 ^ 13 * P0 + ct1 * 10 ^ 13 * P1)
            + ca * (-(ct1 * cp1) * P0 + -(st1 * cp1) * P1 + sp1 * 10 ^ 13 * P2)
            - (-(ct2 * cp2) * Q0 + -(st2 * cp2) * Q1 + sp2 * 10 ^ 13 * Q2) * 10 ^ 13)
          * (sa * (-st1 * 10 ^ 13 * P0 + ct1 * 10 ^ 13 * P1)
            + ca * (-(ct1 * cp1) * P0 + -(st1 * cp1) * P1 + sp1 * 10 ^ 13 * P2)
            - (-(ct2 * cp2) * Q0 + -(st2 * cp2) * Q1 + sp2 * 10 ^ 13 * Q2) * 10 ^ 13))
      + 6 * 10 ^ 6 : ℤ) : ℚ) / (2 * 10 ^ 16)
    = RationalApprox.sqrtApprox16.upper_sqrt.f
        (((ca : ℚ) / 10 ^ 13 * (-((st1 : ℚ) / 10 ^ 13) * pythonVertex a 0
              + (ct1 : ℚ) / 10 ^ 13 * pythonVertex a 1)
            + -((sa : ℚ) / 10 ^ 13) *
              (-((ct1 : ℚ) / 10 ^ 13) * ((cp1 : ℚ) / 10 ^ 13) * pythonVertex a 0
                + -((st1 : ℚ) / 10 ^ 13) * ((cp1 : ℚ) / 10 ^ 13) * pythonVertex a 1
                + (sp1 : ℚ) / 10 ^ 13 * pythonVertex a 2)
            - (-((st2 : ℚ) / 10 ^ 13) * pythonVertex b 0
                + (ct2 : ℚ) / 10 ^ 13 * pythonVertex b 1))
          * ((ca : ℚ) / 10 ^ 13 * (-((st1 : ℚ) / 10 ^ 13) * pythonVertex a 0
              + (ct1 : ℚ) / 10 ^ 13 * pythonVertex a 1)
            + -((sa : ℚ) / 10 ^ 13) *
              (-((ct1 : ℚ) / 10 ^ 13) * ((cp1 : ℚ) / 10 ^ 13) * pythonVertex a 0
                + -((st1 : ℚ) / 10 ^ 13) * ((cp1 : ℚ) / 10 ^ 13) * pythonVertex a 1
                + (sp1 : ℚ) / 10 ^ 13 * pythonVertex a 2)
            - (-((st2 : ℚ) / 10 ^ 13) * pythonVertex b 0
                + (ct2 : ℚ) / 10 ^ 13 * pythonVertex b 1))
          + ((sa : ℚ) / 10 ^ 13 * (-((st1 : ℚ) / 10 ^ 13) * pythonVertex a 0
              + (ct1 : ℚ) / 10 ^ 13 * pythonVertex a 1)
            + (ca : ℚ) / 10 ^ 13 *
              (-((ct1 : ℚ) / 10 ^ 13) * ((cp1 : ℚ) / 10 ^ 13) * pythonVertex a 0
                + -((st1 : ℚ) / 10 ^ 13) * ((cp1 : ℚ) / 10 ^ 13) * pythonVertex a 1
                + (sp1 : ℚ) / 10 ^ 13 * pythonVertex a 2)
            - (-((ct2 : ℚ) / 10 ^ 13) * ((cp2 : ℚ) / 10 ^ 13) * pythonVertex b 0
                + -((st2 : ℚ) / 10 ^ 13) * ((cp2 : ℚ) / 10 ^ 13) * pythonVertex b 1
                + (sp2 : ℚ) / 10 ^ 13 * pythonVertex b 2))
          * ((sa : ℚ) / 10 ^ 13 * (-((st1 : ℚ) / 10 ^ 13) * pythonVertex a 0
              + (ct1 : ℚ) / 10 ^ 13 * pythonVertex a 1)
            + (ca : ℚ) / 10 ^ 13 *
              (-((ct1 : ℚ) / 10 ^ 13) * ((cp1 : ℚ) / 10 ^ 13) * pythonVertex a 0
                + -((st1 : ℚ) / 10 ^ 13) * ((cp1 : ℚ) / 10 ^ 13) * pythonVertex a 1
                + (sp1 : ℚ) / 10 ^ 13 * pythonVertex a 2)
            - (-((ct2 : ℚ) / 10 ^ 13) * ((cp2 : ℚ) / 10 ^ 13) * pythonVertex b 0
                + -((st2 : ℚ) / 10 ^ 13) * ((cp2 : ℚ) / 10 ^ 13) * pythonVertex b 1
                + (sp2 : ℚ) / 10 ^ 13 * pythonVertex b 2))) / 2
      + 3 * RationalApprox.κℚ
  have hva0 : pythonVertex a 0 = (P0 : ℚ) / 10 ^ 16 := pythonVertexNumCurried_eq a.ℓ a.i a.k 0
  have hva1 : pythonVertex a 1 = (P1 : ℚ) / 10 ^ 16 := pythonVertexNumCurried_eq a.ℓ a.i a.k 1
  have hva2 : pythonVertex a 2 = (P2 : ℚ) / 10 ^ 16 := pythonVertexNumCurried_eq a.ℓ a.i a.k 2
  have hvb0 : pythonVertex b 0 = (Q0 : ℚ) / 10 ^ 16 := pythonVertexNumCurried_eq b.ℓ b.i b.k 0
  have hvb1 : pythonVertex b 1 = (Q1 : ℚ) / 10 ^ 16 := pythonVertexNumCurried_eq b.ℓ b.i b.k 1
  have hvb2 : pythonVertex b 2 = (Q2 : ℚ) / 10 ^ 16 := pythonVertexNumCurried_eq b.ℓ b.i b.k 2
  rw [hva0, hva1, hva2, hvb0, hvb1, hvb2,
    show RationalApprox.sqrtApprox16.upper_sqrt.f = RationalApprox.sqrtℚUp16 from rfl,
    show RationalApprox.κℚ = 1 / 10 ^ 10 from rfl]
  refine sqrtNum110_step _ _ ?_
  push_cast
  ring

end Row.δ

/-- The δ bound for a row: `max_i ‖R·M₁·P_i − M₂·Q_i‖ / 2 + 3κ`.
Equivalent to `Finset.max' (Finset.image BoundDeltaℚi univ) _` (see
`Row.δ_eq_max'_BoundDeltaℚi`), but the trig partial sums are hoisted once
per pose for a ~6× runtime speedup. -/
def Row.δ (row : Row) : ℚ :=
  let t := Row.δ.PoseTrigN.ofPose row.interval.centerPose
  let f : Fin 3 → ℚ := fun i =>
    let a := row.Pi i
    let b := row.Qi i
    ((Row.δ.boundDeltaN t
        (pythonVertexNumCurried a.ℓ a.i a.k 0) (pythonVertexNumCurried a.ℓ a.i a.k 1)
        (pythonVertexNumCurried a.ℓ a.i a.k 2) (pythonVertexNumCurried b.ℓ b.i b.k 0)
        (pythonVertexNumCurried b.ℓ b.i b.k 1) (pythonVertexNumCurried b.ℓ b.i b.k 2)
        + 6 * 10 ^ 6 : ℤ) : ℚ) / (2 * 10 ^ 16)
  Finset.max' (Finset.image f Finset.univ)
    (Finset.image_nonempty.mpr ⟨0, Finset.mem_univ 0⟩)

theorem Row.δ_eq_max'_BoundDeltaℚi (row : Row) :
    row.δ = Finset.max' (Finset.image
      (RationalApprox.LocalTheorem.BoundDeltaℚi row.interval.centerPose
        (pythonVertex ∘ row.Pi) (pythonVertex ∘ row.Qi) sqrtApprox16) Finset.univ)
      (Finset.image_nonempty.mpr ⟨0, Finset.mem_univ 0⟩) := by
  show (Finset.image
        (fun i => ((Row.δ.boundDeltaN
            (Row.δ.PoseTrigN.ofPose row.interval.centerPose)
            (pythonVertexNumCurried (row.Pi i).ℓ (row.Pi i).i (row.Pi i).k 0)
            (pythonVertexNumCurried (row.Pi i).ℓ (row.Pi i).i (row.Pi i).k 1)
            (pythonVertexNumCurried (row.Pi i).ℓ (row.Pi i).i (row.Pi i).k 2)
            (pythonVertexNumCurried (row.Qi i).ℓ (row.Qi i).i (row.Qi i).k 0)
            (pythonVertexNumCurried (row.Qi i).ℓ (row.Qi i).i (row.Qi i).k 1)
            (pythonVertexNumCurried (row.Qi i).ℓ (row.Qi i).i (row.Qi i).k 2)
            + 6 * 10 ^ 6 : ℤ) : ℚ) / (2 * 10 ^ 16)) Finset.univ).max' _ =
      (Finset.image
        (RationalApprox.LocalTheorem.BoundDeltaℚi row.interval.centerPose
          (pythonVertex ∘ row.Pi) (pythonVertex ∘ row.Qi) sqrtApprox16) Finset.univ).max' _
  congr 1
  apply Finset.image_congr
  intro i _
  dsimp only
  rw [Row.δ.boundDeltaN_div_eq row.interval.centerPose (row.Pi i) (row.Qi i),
    Row.δ.boundDelta_at_eq]
  rfl

/-! ### Precomputed pairwise vertex-difference norms for `Bεℚ`

The `n_dv` term of the `Bεℚ` predicate — `sqrtApprox16.upper_sqrt.norm
(Q_i − v_k)` — is pose-independent, but costs a `sqrtℚUp16` call on a
denominator-`10³²` input for each of the 270 `(i, k)` pairs of every local
row. `sqrtDv` reads all 90 × 90 pairs from the source-literal table
`sqrtDvCurried` (generated, see `Checker/SqrtDvLiterals.lean`), and
`BεℚPy.check` is the `pythonVertexA`/`sqrtApprox16` checker of `Bεℚ` that
reads it (the `Bεℚ` predicate itself is unchanged). The curried-literal form keeps
the table cheap for the kernel too: an access walks a few dozen `Fin.cons`
cells, where reducing an equivalent 8100-entry `Array.ofFn` push chain made
a single high-index access cost tens of gigabytes under `decide +kernel`. -/

/-- Decode the flat index `45·ℓ + 15·i + k` (see `rowDotsGet`). -/
def ofFlat (m : ℕ) (h : m < 90) : VertexIndex :=
  ⟨⟨m % 15, by omega⟩, ⟨m / 45, by omega⟩, ⟨m / 15 % 3, by omega⟩⟩

/-- Table-backed pairwise vertex-difference norm: equal to
`sqrtApprox16.upper_sqrt.norm (pythonVertexA a - pythonVertexA b)` by `sqrtDv_eq`. -/
def sqrtDv (a b : VertexIndex) : ℚ :=
  sqrtDvCurried a.ℓ a.i a.k b.ℓ b.i b.k

lemma sqrtDv_eq (a b : VertexIndex) :
    sqrtDv a b = sqrtApprox16.upper_sqrt.norm (pythonVertexA a - pythonVertexA b) :=
  sqrtDvCurried_eq a b

/-- Runtime lookup table for `sqrtDv`, built once per process from the
`sqrtDvCurried` literals; indexed by the flat pair index `flat a * 90 + flat b`
with `flat ⟨k, ℓ, i⟩ = 45·ℓ + 15·i + k`. -/
def sqrtDvTable : Array ℚ :=
  Array.ofFn (n := 8100) fun j =>
    sqrtDv (ofFlat (j.val / 90) (by omega)) (ofFlat (j.val % 90) (by omega))

/-- Array-backed implementation of `sqrtDv`: a per-pair curried lookup costs
~40 `Fin.cons` dispatches plus a `Rat` renormalization, which measurably slows
the compiled hot loop, so `sqrtDv_eq_sqrtDvImpl` (`@[csimp]`) substitutes this
`O(1)` array read in compiled code. The kernel keeps reducing the
curried-literal `sqrtDv` itself. -/
def sqrtDvImpl (a b : VertexIndex) : ℚ :=
  sqrtDvTable[(45 * a.ℓ.val + 15 * a.i.val + a.k.val) * 90 +
      (45 * b.ℓ.val + 15 * b.i.val + b.k.val)]'(by
    have h1 := a.ℓ.isLt
    have h2 := a.i.isLt
    have h3 := a.k.isLt
    have h4 := b.ℓ.isLt
    have h5 := b.i.isLt
    have h6 := b.k.isLt
    rw [sqrtDvTable, Array.size_ofFn]
    omega)

@[csimp]
theorem sqrtDv_eq_sqrtDvImpl : @sqrtDv = @sqrtDvImpl := by
  funext a b
  obtain ⟨ka, ℓa, ia⟩ := a
  obtain ⟨kb, ℓb, ib⟩ := b
  have h1 := ℓa.isLt
  have h2 := ia.isLt
  have h3 := ka.isLt
  have h4 := ℓb.isLt
  have h5 := ib.isLt
  have h6 := kb.isLt
  have e1 : ((45 * ℓa.val + 15 * ia.val + ka.val) * 90 +
      (45 * ℓb.val + 15 * ib.val + kb.val)) / 90 =
      45 * ℓa.val + 15 * ia.val + ka.val := by omega
  have e2 : ((45 * ℓa.val + 15 * ia.val + ka.val) * 90 +
      (45 * ℓb.val + 15 * ib.val + kb.val)) % 90 =
      45 * ℓb.val + 15 * ib.val + kb.val := by omega
  have f1 : (45 * ℓa.val + 15 * ia.val + ka.val) % 15 = ka.val := by omega
  have f2 : (45 * ℓa.val + 15 * ia.val + ka.val) / 45 = ℓa.val := by omega
  have f3 : (45 * ℓa.val + 15 * ia.val + ka.val) / 15 % 3 = ia.val := by omega
  have g1 : (45 * ℓb.val + 15 * ib.val + kb.val) % 15 = kb.val := by omega
  have g2 : (45 * ℓb.val + 15 * ib.val + kb.val) / 45 = ℓb.val := by omega
  have g3 : (45 * ℓb.val + 15 * ib.val + kb.val) / 15 % 3 = ib.val := by omega
  simp only [sqrtDvImpl, sqrtDvTable, Array.getElem_ofFn, ofFlat, e1, e2, f1, f2, f3,
    g1, g2, g3, Fin.eta]

namespace BεℚPy

open Local.TriangleQ.Bεℚ (MatEntries matEntries rotM₂Rℚ_c0 rotM₂Rℚ_c1)

/-- Per-pose table of the row dot products `((M₂ vⱼ)₀, (M₂ vⱼ)₁)` (unrounded)
for all 90 vertices, indexed by `flat ⟨k, ℓ, i⟩ = 45·ℓ + 15·i + k`. `check`
computes it once per pose; by linearity `M₂(v₁ - v₂) = M₂v₁ - M₂v₂`, each
`(i, k)` dot then costs one lookup and one subtraction instead of three
products. -/
def rowDots (e : MatEntries) : List (ℚ × ℚ) :=
  List.ofFn (n := 90) fun j =>
    let v := pythonVertexA (ofFlat j.val j.isLt)
    (e.m₀₀ * v 0 + e.m₀₁ * v 1 + e.m₀₂ * v 2,
     e.m₁₀ * v 0 + e.m₁₁ * v 1 + e.m₁₂ * v 2)

/-- Read a `rowDots` table at a vertex index. -/
def rowDotsGet (dots : List (ℚ × ℚ)) (a : VertexIndex) : ℚ × ℚ :=
  dots[45 * a.ℓ.val + 15 * a.i.val + a.k.val]!

private lemma rowDotsGet_rowDots (e : MatEntries) (a : VertexIndex) :
    rowDotsGet (rowDots e) a
      = (e.m₀₀ * pythonVertexA a 0 + e.m₀₁ * pythonVertexA a 1 + e.m₀₂ * pythonVertexA a 2,
         e.m₁₀ * pythonVertexA a 0 + e.m₁₁ * pythonVertexA a 1 + e.m₁₂ * pythonVertexA a 2) := by
  obtain ⟨ka, ℓa, ia⟩ := a
  have h1 := ℓa.isLt
  have h2 := ia.isLt
  have h3 := ka.isLt
  have hlt : 45 * ℓa.val + 15 * ia.val + ka.val < (rowDots e).length := by
    rw [rowDots, List.length_ofFn]; omega
  have f1 : (45 * ℓa.val + 15 * ia.val + ka.val) % 15 = ka.val := by omega
  have f2 : (45 * ℓa.val + 15 * ia.val + ka.val) / 45 = ℓa.val := by omega
  have f3 : (45 * ℓa.val + 15 * ia.val + ka.val) / 15 % 3 = ia.val := by omega
  show (rowDots e)[45 * ℓa.val + 15 * ia.val + ka.val]! = _
  rw [getElem!_pos (rowDots e) _ hlt]
  simp only [rowDots, List.getElem_ofFn, ofFlat, f1, f2, f3, Fin.eta]

lemma rowDots_fst (e : MatEntries) (a : VertexIndex) :
    (rowDotsGet (rowDots e) a).1
      = e.m₀₀ * pythonVertexA a 0 + e.m₀₁ * pythonVertexA a 1 + e.m₀₂ * pythonVertexA a 2 := by
  rw [rowDotsGet_rowDots]

lemma rowDots_snd (e : MatEntries) (a : VertexIndex) :
    (rowDotsGet (rowDots e) a).2
      = e.m₁₀ * pythonVertexA a 0 + e.m₁₁ * pythonVertexA a 1 + e.m₁₂ * pythonVertexA a 2 := by
  rw [rowDotsGet_rowDots]

/-- Bool-valued checker for `Bεℚ` at `pythonVertexA` and `sqrtApprox16`,
with the per-pose work hoisted out of the `k`-loop:

* the pose-independent `n_dv` norms come from the `sqrtDvCurried` literals;
* the unrounded row dots `M₂vⱼ` come from the per-pose `rowDots` table, so a
  pair's `d`-vector is one lookup and one subtraction (`M₂(v₁-v₂) = M₂v₁-M₂v₂`);
* the scalars `F2`, `cD`, `eterm`, `tenκ`, `twoκ`, `bd` are loop-invariant.

Each `(i, k)` pair first tries a *cheap sufficient* test (the left disjunct)
that avoids the per-pair `upper_sqrt.f` call on the denominator-`10²⁶` input
`d0² + d1²`: by Cauchy–Schwarz, `d0² + d1² ≤ (F·n_dv + 2·10⁻¹³)²` where `F`
is a per-pose Frobenius-norm bound (one sqrt call per pose), so the
fixed-point accuracy bound `sqrtℚUp16 x ≤ Y + 2·10⁻¹⁶` caps the exact
`denom2` by `F·n_dv + 2·10⁻¹³ + 2·10⁻¹⁶ + 2·√⁺2·ε + 6κ`
(see `cheap_sufficient`). Only pairs
that fail the cheap test — binding or near-binding `k` — fall back to the
exact test in the right disjunct; the `Or`/`And` `Decidable` instances are
`macro_inline`, so evaluation short-circuits. -/
def check (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (ε δ r : ℚ) : Bool :=
  let entries := matEntries p
  let bound := (δ + sqrtApprox16.upper_sqrt_five * ε) / r
  let F2 := sqrtApprox16.upper_sqrt.f
    (entries.m₀₀ * entries.m₀₀ + entries.m₀₁ * entries.m₀₁ + entries.m₀₂ * entries.m₀₂
      + entries.m₁₀ * entries.m₁₀ + entries.m₁₁ * entries.m₁₁ + entries.m₁₂ * entries.m₁₂)
  let cD := 2 / 10 ^ 13 + 2 / 10 ^ 16 + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ
  let eterm := 2 * ε * (sqrtApprox16.upper_sqrt_two + ε)
  let tenκ := 10 * κℚ
  let twoκ := 2 * κℚ
  let dots := rowDots entries
  (List.finRange 3).all fun i =>
    let Qi_idx := Qi i
    let mq := rowDotsGet dots Qi_idx
    let mq0 := mq.1
    let mq1 := mq.2
    let q0 := RationalApprox.round13 mq0
    let q1 := RationalApprox.round13 mq1
    let denom1 := sqrtApprox16.upper_sqrt.f (q0 * q0 + q1 * q1)
                  + sqrtApprox16.upper_sqrt_two * ε + 3 * κℚ
    let bd := bound * denom1
    decide <| ∀ k : VertexIndex, k ≠ Qi_idx →
      let dk := rowDotsGet dots k
      let d0 := RationalApprox.round13 (mq0 - dk.1)
      let d1 := RationalApprox.round13 (mq1 - dk.2)
      let n_dv := sqrtDv Qi_idx k
      let numer := q0 * d0 + q1 * d1 - tenκ - eterm * (n_dv + twoκ)
      (0 ≤ numer ∧ 0 ≤ ε ∧ bd * (F2 * n_dv + cD) < numer) ∨
        bound < numer / (denom1 * (sqrtApprox16.upper_sqrt.f (d0 * d0 + d1 * d1)
          + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ))

/-- 3-D Cauchy–Schwarz for the two matrix rows, in pure ℚ: the squared
2-vector `(u0, u1) = M·w` is bounded by the (squared) product of the
`sqrtℚUp16` Frobenius-norm bound of `M` and the `sqrtℚUp16` norm bound of `w`. -/
private lemma dots_sq_le (m00 m01 m02 m10 m11 m12 w0 w1 w2 : ℚ) :
    (m00 * w0 + m01 * w1 + m02 * w2) * (m00 * w0 + m01 * w1 + m02 * w2)
      + (m10 * w0 + m11 * w1 + m12 * w2) * (m10 * w0 + m11 * w1 + m12 * w2)
    ≤ (RationalApprox.sqrtℚUp16 (m00 * m00 + m01 * m01 + m02 * m02
          + m10 * m10 + m11 * m11 + m12 * m12)
        * RationalApprox.sqrtℚUp16 (w0 * w0 + w1 * w1 + w2 * w2))
      * (RationalApprox.sqrtℚUp16 (m00 * m00 + m01 * m01 + m02 * m02
          + m10 * m10 + m11 * m11 + m12 * m12)
        * RationalApprox.sqrtℚUp16 (w0 * w0 + w1 * w1 + w2 * w2)) := by
  have hfro_nn : (0:ℚ) ≤ m00 * m00 + m01 * m01 + m02 * m02
      + m10 * m10 + m11 * m11 + m12 * m12 := by
    have h0 := mul_self_nonneg m00
    have h1 := mul_self_nonneg m01
    have h2 := mul_self_nonneg m02
    have h3 := mul_self_nonneg m10
    have h4 := mul_self_nonneg m11
    have h5 := mul_self_nonneg m12
    linarith
  have hS2_nn : (0:ℚ) ≤ w0 * w0 + w1 * w1 + w2 * w2 := by
    have h0 := mul_self_nonneg w0
    have h1 := mul_self_nonneg w1
    have h2 := mul_self_nonneg w2
    linarith
  have hfro := RationalApprox.le_mul_self_sqrtℚUp16 hfro_nn
  have hS2 := RationalApprox.le_mul_self_sqrtℚUp16 hS2_nn
  -- Lagrange identities for the two rows.
  have l0 : (m00 * m00 + m01 * m01 + m02 * m02) * (w0 * w0 + w1 * w1 + w2 * w2)
      - (m00 * w0 + m01 * w1 + m02 * w2) * (m00 * w0 + m01 * w1 + m02 * w2)
      = (m00 * w1 - m01 * w0) ^ 2 + (m00 * w2 - m02 * w0) ^ 2
        + (m01 * w2 - m02 * w1) ^ 2 := by ring
  have l1 : (m10 * m10 + m11 * m11 + m12 * m12) * (w0 * w0 + w1 * w1 + w2 * w2)
      - (m10 * w0 + m11 * w1 + m12 * w2) * (m10 * w0 + m11 * w1 + m12 * w2)
      = (m10 * w1 - m11 * w0) ^ 2 + (m10 * w2 - m12 * w0) ^ 2
        + (m11 * w2 - m12 * w1) ^ 2 := by ring
  have hCS : (m00 * w0 + m01 * w1 + m02 * w2) * (m00 * w0 + m01 * w1 + m02 * w2)
      + (m10 * w0 + m11 * w1 + m12 * w2) * (m10 * w0 + m11 * w1 + m12 * w2)
      ≤ (m00 * m00 + m01 * m01 + m02 * m02 + m10 * m10 + m11 * m11 + m12 * m12)
        * (w0 * w0 + w1 * w1 + w2 * w2) := by
    have s0 := sq_nonneg (m00 * w1 - m01 * w0)
    have s1 := sq_nonneg (m00 * w2 - m02 * w0)
    have s2 := sq_nonneg (m01 * w2 - m02 * w1)
    have s3 := sq_nonneg (m10 * w1 - m11 * w0)
    have s4 := sq_nonneg (m10 * w2 - m12 * w0)
    have s5 := sq_nonneg (m11 * w2 - m12 * w1)
    have expand : (m00 * m00 + m01 * m01 + m02 * m02 + m10 * m10 + m11 * m11 + m12 * m12)
        * (w0 * w0 + w1 * w1 + w2 * w2)
        = (m00 * m00 + m01 * m01 + m02 * m02) * (w0 * w0 + w1 * w1 + w2 * w2)
          + (m10 * m10 + m11 * m11 + m12 * m12) * (w0 * w0 + w1 * w1 + w2 * w2) := by
      ring
    linarith
  calc (m00 * w0 + m01 * w1 + m02 * w2) * (m00 * w0 + m01 * w1 + m02 * w2)
      + (m10 * w0 + m11 * w1 + m12 * w2) * (m10 * w0 + m11 * w1 + m12 * w2)
      ≤ (m00 * m00 + m01 * m01 + m02 * m02 + m10 * m10 + m11 * m11 + m12 * m12)
        * (w0 * w0 + w1 * w1 + w2 * w2) := hCS
    _ ≤ (RationalApprox.sqrtℚUp16 (m00 * m00 + m01 * m01 + m02 * m02
          + m10 * m10 + m11 * m11 + m12 * m12)
        * RationalApprox.sqrtℚUp16 (m00 * m00 + m01 * m01 + m02 * m02
          + m10 * m10 + m11 * m11 + m12 * m12))
        * (w0 * w0 + w1 * w1 + w2 * w2) := mul_le_mul_of_nonneg_right hfro hS2_nn
    _ ≤ (RationalApprox.sqrtℚUp16 (m00 * m00 + m01 * m01 + m02 * m02
          + m10 * m10 + m11 * m11 + m12 * m12)
        * RationalApprox.sqrtℚUp16 (m00 * m00 + m01 * m01 + m02 * m02
          + m10 * m10 + m11 * m11 + m12 * m12))
        * (RationalApprox.sqrtℚUp16 (w0 * w0 + w1 * w1 + w2 * w2)
          * RationalApprox.sqrtℚUp16 (w0 * w0 + w1 * w1 + w2 * w2)) := by
      refine mul_le_mul_of_nonneg_left hS2 ?_
      exact mul_nonneg (RationalApprox.sqrtℚUp16_nonneg _) (RationalApprox.sqrtℚUp16_nonneg _)
    _ = _ := by ring

/-- Sufficiency of the cheap per-`(i, k)` test: if `(u0, u1)` is the unrounded
2-vector with `u0² + u1² ≤ (F·n_dv)²` (Cauchy–Schwarz, `dots_sq_le`) and
`(d0, d1)` its `round13` rounding, then `d0² + d1² ≤ (F·n_dv + 2·10⁻¹³)²`, so
the fixed-point accuracy bound `sqrtℚUp16 x ≤ Y + 2·10⁻¹⁶`
(`sqrtℚUp16_le_add_of_le_mul_self`) caps the exact `denom2` by the
cheap one, and a cheap pass forces an exact pass. -/
private lemma cheap_sufficient {bound denom1 F n_dv d0 d1 u0 u1 ε numer : ℚ}
    (hdenom1 : 0 < denom1)
    (hd0 : |d0 - u0| ≤ 1 / 10 ^ 13) (hd1 : |d1 - u1| ≤ 1 / 10 ^ 13)
    (hu : u0 * u0 + u1 * u1 ≤ (F * n_dv) * (F * n_dv))
    (hW : 0 ≤ F * n_dv)
    (hε : 0 ≤ ε) (hnum : 0 ≤ numer)
    (hcheap : bound * denom1 * (F * n_dv + (2 / 10 ^ 13 + 2 / 10 ^ 16
        + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ)) < numer) :
    bound < numer / (denom1 * (sqrtApprox16.upper_sqrt.f (d0 * d0 + d1 * d1)
        + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ)) := by
  -- Re-associate the hoisted cheap comparison.
  have hcheap' : bound * (denom1 * (((F * n_dv + 2 / 10 ^ 13) + 2 / 10 ^ 16)
      + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ)) < numer := by
    calc bound * (denom1 * (((F * n_dv + 2 / 10 ^ 13) + 2 / 10 ^ 16)
          + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ))
        = bound * denom1 * (F * n_dv + (2 / 10 ^ 13 + 2 / 10 ^ 16
          + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ)) := by ring
      _ < numer := hcheap
  have hst : (0:ℚ) ≤ sqrtApprox16.upper_sqrt_two := by
    norm_num [RationalApprox.sqrtApprox16]
  have hκ : (0:ℚ) < κℚ := by norm_num [κℚ]
  -- |u0| ≤ F·n_dv and |u1| ≤ F·n_dv.
  have habs0 : |u0| ≤ F * n_dv := by
    by_contra hcon
    push Not at hcon
    have h2 : (F * n_dv) * (F * n_dv) < |u0| * |u0| := mul_self_lt_mul_self hW hcon
    rw [abs_mul_abs_self] at h2
    have := mul_self_nonneg u1
    linarith
  have habs1 : |u1| ≤ F * n_dv := by
    by_contra hcon
    push Not at hcon
    have h2 : (F * n_dv) * (F * n_dv) < |u1| * |u1| := mul_self_lt_mul_self hW hcon
    rw [abs_mul_abs_self] at h2
    have := mul_self_nonneg u0
    linarith
  -- d0² + d1² ≤ (F·n_dv + 2·10⁻¹³)².
  have hb0 : |d0| ≤ |u0| + 1 / 10 ^ 13 := by
    calc |d0| = |u0 + (d0 - u0)| := by rw [add_sub_cancel]
      _ ≤ |u0| + |d0 - u0| := abs_add_le _ _
      _ ≤ |u0| + 1 / 10 ^ 13 := by linarith
  have hb1 : |d1| ≤ |u1| + 1 / 10 ^ 13 := by
    calc |d1| = |u1 + (d1 - u1)| := by rw [add_sub_cancel]
      _ ≤ |u1| + |d1 - u1| := abs_add_le _ _
      _ ≤ |u1| + 1 / 10 ^ 13 := by linarith
  have hsq0 : d0 * d0 ≤ (|u0| + 1 / 10 ^ 13) * (|u0| + 1 / 10 ^ 13) := by
    rw [← abs_mul_abs_self d0]
    exact mul_self_le_mul_self (abs_nonneg _) hb0
  have hsq1 : d1 * d1 ≤ (|u1| + 1 / 10 ^ 13) * (|u1| + 1 / 10 ^ 13) := by
    rw [← abs_mul_abs_self d1]
    exact mul_self_le_mul_self (abs_nonneg _) hb1
  have hx2 : d0 * d0 + d1 * d1
      ≤ (F * n_dv + 2 / 10 ^ 13) * (F * n_dv + 2 / 10 ^ 13) := by
    have e0 : (|u0| + 1 / 10 ^ 13) * (|u0| + 1 / 10 ^ 13)
        = u0 * u0 + 2 * (1 / 10 ^ 13) * |u0| + (1 / 10 ^ 13) * (1 / 10 ^ 13) := by
      have h := abs_mul_abs_self u0
      linear_combination h
    have e1 : (|u1| + 1 / 10 ^ 13) * (|u1| + 1 / 10 ^ 13)
        = u1 * u1 + 2 * (1 / 10 ^ 13) * |u1| + (1 / 10 ^ 13) * (1 / 10 ^ 13) := by
      have h := abs_mul_abs_self u1
      linear_combination h
    have expand : (F * n_dv + 2 / 10 ^ 13) * (F * n_dv + 2 / 10 ^ 13)
        = (F * n_dv) * (F * n_dv) + 4 * (1 / 10 ^ 13) * (F * n_dv)
          + 4 * ((1 / 10 ^ 13) * (1 / 10 ^ 13)) := by ring
    linarith
  -- Cap the exact denominator by the cheap one.
  have hY : (0:ℚ) ≤ F * n_dv + 2 / 10 ^ 13 := by linarith [hW]
  have hf : sqrtApprox16.upper_sqrt.f (d0 * d0 + d1 * d1)
      ≤ (F * n_dv + 2 / 10 ^ 13) + 2 / 10 ^ 16 :=
    RationalApprox.sqrtℚUp16_le_add_of_le_mul_self hY hx2
  have hf_nn : (0:ℚ) ≤ sqrtApprox16.upper_sqrt.f (d0 * d0 + d1 * d1) :=
    RationalApprox.sqrtℚUp16_nonneg _
  have hεst : (0:ℚ) ≤ 2 * sqrtApprox16.upper_sqrt_two * ε := by positivity
  have hd2_pos : 0 < sqrtApprox16.upper_sqrt.f (d0 * d0 + d1 * d1)
      + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ := by linarith
  have hd2_le : sqrtApprox16.upper_sqrt.f (d0 * d0 + d1 * d1)
      + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ
      ≤ ((F * n_dv + 2 / 10 ^ 13) + 2 / 10 ^ 16)
        + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ := by
    linarith
  rw [lt_div_iff₀ (mul_pos hdenom1 hd2_pos)]
  rcases le_or_gt 0 bound with hb | hb
  · calc bound * (denom1 * (sqrtApprox16.upper_sqrt.f (d0 * d0 + d1 * d1)
        + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ))
        ≤ bound * (denom1 * (((F * n_dv + 2 / 10 ^ 13) + 2 / 10 ^ 16)
          + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hd2_le (le_of_lt hdenom1)) hb
      _ < numer := hcheap'
  · have hneg : bound * (denom1 * (sqrtApprox16.upper_sqrt.f (d0 * d0 + d1 * d1)
        + 2 * sqrtApprox16.upper_sqrt_two * ε + 6 * κℚ)) < 0 :=
      mul_neg_of_neg_of_pos hb (mul_pos hdenom1 hd2_pos)
    linarith

theorem check_iff (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (ε δ r : ℚ) :
    check Qi p ε δ r = true ↔
      Local.TriangleQ.Bεℚ Qi pythonVertexA p ε δ r sqrtApprox16 := by
  unfold check Local.TriangleQ.Bεℚ Local.TriangleQ.Bεℚ.lhs
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]
  refine forall_congr' (fun i => ?_)
  refine forall_congr' (fun k => ?_)
  refine forall_congr' (fun _ => ?_)
  rw [rowDots_fst (matEntries p) (Qi i), rowDots_snd (matEntries p) (Qi i),
      rowDots_fst (matEntries p) k, rowDots_snd (matEntries p) k]
  -- Undo the hoisted `M₂(v₁ - v₂) = M₂v₁ - M₂v₂` linearity.
  rw [show (matEntries p).m₀₀ * pythonVertexA (Qi i) 0 + (matEntries p).m₀₁ *
        pythonVertexA (Qi i) 1 + (matEntries p).m₀₂ * pythonVertexA (Qi i) 2
        - ((matEntries p).m₀₀ * pythonVertexA k 0 + (matEntries p).m₀₁ *
          pythonVertexA k 1 + (matEntries p).m₀₂ * pythonVertexA k 2)
      = (matEntries p).m₀₀ * (pythonVertexA (Qi i) 0 - pythonVertexA k 0)
        + (matEntries p).m₀₁ * (pythonVertexA (Qi i) 1 - pythonVertexA k 1)
        + (matEntries p).m₀₂ * (pythonVertexA (Qi i) 2 - pythonVertexA k 2) from by ring,
      show (matEntries p).m₁₀ * pythonVertexA (Qi i) 0 + (matEntries p).m₁₁ *
        pythonVertexA (Qi i) 1 + (matEntries p).m₁₂ * pythonVertexA (Qi i) 2
        - ((matEntries p).m₁₀ * pythonVertexA k 0 + (matEntries p).m₁₁ *
          pythonVertexA k 1 + (matEntries p).m₁₂ * pythonVertexA k 2)
      = (matEntries p).m₁₀ * (pythonVertexA (Qi i) 0 - pythonVertexA k 0)
        + (matEntries p).m₁₁ * (pythonVertexA (Qi i) 1 - pythonVertexA k 1)
        + (matEntries p).m₁₂ * (pythonVertexA (Qi i) 2 - pythonVertexA k 2) from by ring]
  simp only [show ∀ c : Fin 3, pythonVertexA (Qi i) c - pythonVertexA k c =
    (pythonVertexA (Qi i) - pythonVertexA k) c from fun _ => rfl]
  rw [sqrtDv_eq,
      ← rotM₂Rℚ_c0 p (pythonVertexA (Qi i)), ← rotM₂Rℚ_c1 p (pythonVertexA (Qi i)),
      ← rotM₂Rℚ_c0 p (pythonVertexA (Qi i) - pythonVertexA k),
      ← rotM₂Rℚ_c1 p (pythonVertexA (Qi i) - pythonVertexA k)]
  simp only [RationalApprox.UpperSqrt.norm, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three]
  -- Undo the hoisted `eterm` factor order in `numer`.
  rw [mul_right_comm (2 * ε) (sqrtApprox16.upper_sqrt_two + ε)]
  refine or_iff_right_of_imp (fun hcheap => ?_)
  obtain ⟨hnum, hε, hlt⟩ := hcheap
  set w := pythonVertexA (Qi i) - pythonVertexA k with hw
  refine cheap_sufficient
    (u0 := (matEntries p).m₀₀ * w 0 + (matEntries p).m₀₁ * w 1 + (matEntries p).m₀₂ * w 2)
    (u1 := (matEntries p).m₁₀ * w 0 + (matEntries p).m₁₁ * w 1 + (matEntries p).m₁₂ * w 2)
    ?_ ?_ ?_ ?_ ?_ hε hnum hlt
  · -- 0 < denom1
    have h1 : (0:ℚ) ≤ sqrtApprox16.upper_sqrt.f
        (p.rotM₂Rℚ (pythonVertexA (Qi i)) 0 * p.rotM₂Rℚ (pythonVertexA (Qi i)) 0
          + p.rotM₂Rℚ (pythonVertexA (Qi i)) 1 * p.rotM₂Rℚ (pythonVertexA (Qi i)) 1) :=
      RationalApprox.sqrtℚUp16_nonneg _
    have hst : (0:ℚ) ≤ sqrtApprox16.upper_sqrt_two := by
      norm_num [RationalApprox.sqrtApprox16]
    have hκ : (0:ℚ) < κℚ := by norm_num [κℚ]
    positivity
  · -- |d0 - u0| ≤ 10⁻¹³
    rw [rotM₂Rℚ_c0]
    exact RationalApprox.abs_round13_sub_le _
  · -- |d1 - u1| ≤ 10⁻¹³
    rw [rotM₂Rℚ_c1]
    exact RationalApprox.abs_round13_sub_le _
  · -- Cauchy–Schwarz
    exact dots_sq_le _ _ _ _ _ _ _ _ _
  · -- 0 ≤ F·n_dv
    exact mul_nonneg (RationalApprox.sqrtℚUp16_nonneg _) (RationalApprox.sqrtℚUp16_nonneg _)

/-- Decision procedure for the `Bεℚ` conjunct of `Row.ValidLocal` (the only
one — the generic-`ι` checker layer was retired in favor of this
specialization). -/
instance (priority := high) instDecidablePy (Qi : Fin 3 → VertexIndex)
    (p : Pose ℚ) (ε δ r : ℚ) :
    Decidable (Local.TriangleQ.Bεℚ Qi pythonVertexA p ε δ r sqrtApprox16) :=
  decidable_of_iff _ (check_iff Qi p ε δ r)

end BεℚPy

/-! ### Kernel-path vertex reads for the remaining `Row.ValidLocal` conjuncts

The `Aεℚσ`/`Spanningℚ`/`BoundRℚ` conjuncts read vertices through
`pythonVertexA`; under `decide +kernel` its backing `Array.ofFn` push chain
re-reduces as a quadratic `List.concat` walk (~150k list-step unfoldings per
local row — the dominant cost, per kernel diagnostics). These instances
transport each conjunct to the curried `pythonVertex`, whose lookups cost the
kernel a few dozen `Fin.cons` steps; compiled code still gets `O(1)` array
reads via `pythonVertex`'s `@[csimp]`. -/

instance (priority := high) Aεℚσ.instDecidablePyV (X : Fin 3 → ℚ)
    (idx : Fin 3 → VertexIndex) (ε : ℚ) (σ : ℕ) (approx : RationalApprox.Approx) :
    Decidable (Local.TriangleQ.Aεℚσ X (pythonVertexA ∘ idx) ε σ approx) :=
  decidable_of_iff (Local.TriangleQ.Aεℚσ X (pythonVertex ∘ idx) ε σ approx)
    (by rw [pythonVertexA_eq])

instance (priority := high) Spanningℚ.instDecidablePyV (θ φ ε : ℚ)
    (idx : Fin 3 → VertexIndex) :
    Decidable (Spanningℚ θ φ ε (pythonVertexA ∘ idx)) :=
  decidable_of_iff (Spanningℚ θ φ ε (pythonVertex ∘ idx))
    (by rw [pythonVertexA_eq])

instance (priority := high) BoundRℚ.instDecidablePyV (r ε : ℚ) (p : Pose ℚ)
    (idx : Fin 3 → VertexIndex) (approx : RationalApprox.Approx) :
    Decidable (RationalApprox.LocalTheorem.BoundRℚ r ε p (pythonVertexA ∘ idx) approx) :=
  decidable_of_iff (RationalApprox.LocalTheorem.BoundRℚ r ε p (pythonVertex ∘ idx) approx)
    (by rw [pythonVertexA_eq])

/-- Assertion that a row constitutes a valid application of the rational global theorem.

The vertex functions are the table-backed `pythonVertexA` (equal to
`pythonVertex` by `pythonVertexA_eq`), so the hot loops of the `Decidable`
instance read precomputed coordinates instead of re-dividing on every access. -/
@[mk_iff]
structure Row.ValidLocal (row : Row) : Prop where
  nodeType_eq : row.nodeType = 2
  center_in_fourQ : row.interval.centerPose ∈ fourInterval ℚ
  epsilon_pos : 0 < row.epsilon
  exists_symmetry : ∃ s : TriangleSymmetry,
    s.applicable row.Qi ∧ ∀ i, row.Pi i = s.apply (row.Qi i)
  X₁_inner_gt : Local.TriangleQ.Aεℚσ
                  row.X₁ (pythonVertexA ∘ row.Pi) row.epsilon 0 sqrtApprox16
  X₂_inner_gt : Local.TriangleQ.Aεℚσ
                  row.X₂ (pythonVertexA ∘ row.Qi) row.epsilon row.sigma_Q.val sqrtApprox16
  P_spanning : Spanningℚ row.θ₁ row.φ₁ row.epsilon (pythonVertexA ∘ row.Pi)
  Q_spanning : Spanningℚ row.θ₂ row.φ₂ row.epsilon (pythonVertexA ∘ row.Qi)
  rpos : 0 < row.r
  r_valid : RationalApprox.LocalTheorem.BoundRℚ
              row.r row.epsilon row.interval.centerPose (pythonVertexA ∘ row.Qi) sqrtApprox16
  Bεℚ : Local.TriangleQ.Bεℚ
    row.Qi pythonVertexA row.interval.centerPose
    row.epsilon row.δ row.r sqrtApprox16

instance (row : Row) : Decidable (Row.ValidLocal row) :=
  decidable_of_iff _ (Row.validLocal_iff row).symm

/-! ## Smoke test -/

/-
ID,nodeType,nrChildren,IDfirstChild,split,
T1_min,T1_max,V1_min,V1_max,T2_min,T2_max,V2_min,V2_max,A_min,A_max,
P1_index,P2_index,P3_index,Q1_index,Q2_index,Q3_index,
r,sigma_Q,
wx_nominator,wy_nominator,w_denominator,S_index

245,2,,,,
0,201600,0,201600,0,201600,0,202240,-22853120,-22650880,
30,31,38,79,80,87,
955,1,
,,,
-/

/-- Row 245 from `data/solution_tree_300.csv` — the first local leaf. -/
def testLocalRow : Row := {
  ID := 245, nodeType := 2, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := Interval.ofIntPose
    { θ₁ := 0, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := -22853120 }
    { θ₁ := 201600, θ₂ := 201600, φ₁ := 201600, φ₂ := 202240, α := -22650880 }
    (by decide),
  S_index := 0, wx_numerator := 0, wy_numerator := 0, w_denominator := 0,
  P1_index := VertexIndex.ofFin90 ⟨30, by lia⟩,
  P2_index := VertexIndex.ofFin90 ⟨31, by lia⟩,
  P3_index := VertexIndex.ofFin90 ⟨38, by lia⟩,
  Q1_index := VertexIndex.ofFin90 ⟨79, by lia⟩,
  Q2_index := VertexIndex.ofFin90 ⟨80, by lia⟩,
  Q3_index := VertexIndex.ofFin90 ⟨87, by lia⟩,
  r' := 955, sigma_Q := ⟨1, by simp [Finset.mem_Icc]⟩
}

/-- info: true -/
#guard_msgs in
#eval testLocalRow.ValidLocal

/-
ID=2738018 from the full solution tree — a local leaf that requires
a reflection (k → -k) symmetry rather than just a rotation.
All vertices have i=1 (C2 orbit).

2738018,2,,,,0,403200,36691200,37094400,1209600,1612800,
11325440,11729920,-808960,-404480,
15,61,70,19,63,69,928,1,,,,
-/
def testLocalRowReflection : Row := {
  ID := 2738018, nodeType := 2, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := Interval.ofIntPose
    { θ₁ := 0, θ₂ := 1209600, φ₁ := 36691200, φ₂ := 11325440, α := -808960 }
    { θ₁ := 403200, θ₂ := 1612800, φ₁ := 37094400, φ₂ := 11729920, α := -404480 }
    (by decide),
  S_index := 0, wx_numerator := 0, wy_numerator := 0, w_denominator := 0,
  P1_index := VertexIndex.ofFin90 ⟨15, by lia⟩,
  P2_index := VertexIndex.ofFin90 ⟨61, by lia⟩,
  P3_index := VertexIndex.ofFin90 ⟨70, by lia⟩,
  Q1_index := VertexIndex.ofFin90 ⟨19, by lia⟩,
  Q2_index := VertexIndex.ofFin90 ⟨63, by lia⟩,
  Q3_index := VertexIndex.ofFin90 ⟨69, by lia⟩,
  r' := 928, sigma_Q := ⟨1, by simp [Finset.mem_Icc]⟩
}

/-- info: true -/
#guard_msgs in
#eval testLocalRowReflection.ValidLocal

end Noperthedron.Solution
end
