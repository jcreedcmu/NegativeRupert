module

public import Noperthedron.Local
public import Noperthedron.RationalApprox.Basic
public import Noperthedron.RationalApprox.Cast
public import Noperthedron.RationalApprox.EpsKapSpanning
public import Noperthedron.RationalApprox.BoundsKappa3
public import Noperthedron.RationalApprox.BoundsKappa4

@[expose] public section


open Local (Triangle)
open scoped RealInnerProductSpace Real

open RationalApprox (κ κℚ UpperSqrt)

namespace Local

abbrev TriangleQ : Type := Fin 3 → Fin 3 → ℚ

def TriangleQ.toReal (t : TriangleQ) : Triangle :=
  fun i => toR3 (t i)

def TriangleQ.Aεℚσ (X : Fin 3 → ℚ) (P_ : TriangleQ) (ε : ℚ) (σ : ℕ)
    (approx : RationalApprox.Approx) : Prop :=
  ∀ i : Fin 3, (-1)^σ * X ⬝ᵥ P_ i > approx.upper_sqrt_two * ε + 3 * κℚ

namespace TriangleQ.Aεℚσ

/-- Bool-valued `Aεℚσ` check that reads the components of `X` (each of which
re-evaluates two trig partial sums per access for `X = vecXℚ θ φ`) and the
right-hand side once, outside the `i`-loop. -/
def check (X : Fin 3 → ℚ) (P_ : TriangleQ) (ε : ℚ) (σ : ℕ)
    (approx : RationalApprox.Approx) : Bool :=
  let s : ℚ := (-1) ^ σ
  let x0 := s * X 0
  let x1 := s * X 1
  let x2 := s * X 2
  let rhs := approx.upper_sqrt_two * ε + 3 * κℚ
  (List.finRange 3).all fun i =>
    let Pi := P_ i
    decide (rhs < x0 * Pi 0 + x1 * Pi 1 + x2 * Pi 2)

theorem check_iff (X : Fin 3 → ℚ) (P_ : TriangleQ) (ε : ℚ) (σ : ℕ)
    (approx : RationalApprox.Approx) :
    check X P_ ε σ approx = true ↔ Aεℚσ X P_ ε σ approx := by
  unfold check Aεℚσ
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]
  refine forall_congr' fun i => ?_
  rw [show (-1 : ℚ) ^ σ * (X ⬝ᵥ P_ i) =
      (-1) ^ σ * X 0 * P_ i 0 + (-1) ^ σ * X 1 * P_ i 1 + (-1) ^ σ * X 2 * P_ i 2 from by
    simp only [dotProduct, Fin.sum_univ_three]; ring]

instance instDecidable (X : Fin 3 → ℚ) (P_ : TriangleQ) (ε : ℚ) (σ : ℕ)
    (approx : RationalApprox.Approx) : Decidable (Aεℚσ X P_ ε σ approx) :=
  decidable_of_iff _ (check_iff X P_ ε σ approx)

end TriangleQ.Aεℚσ

/--
Condition A_ε^ℚ from [SY25] Theorem 48
-/
def TriangleQ.Aεℚ (X : Fin 3 → ℚ) (P_ : TriangleQ) (ε : ℚ) (approx : RationalApprox.Approx) : Prop :=
  ∃ σ : ℕ, TriangleQ.Aεℚσ X P_ ε σ approx

/-- The left-hand side of the `Bεℚ` inequality. The applied vectors are the
*rounded* `p.rotM₂Rℚ` ones (multiples of `10⁻¹³` componentwise), so the dot
product and `UpperSqrt` norms here run on small denominators; the rounding
error is absorbed into the `10κℚ`/`3κℚ`/`6κℚ` terms (see `bounds_kappa4`). -/
def TriangleQ.Bεℚ.lhs (v₁ v₂ : Fin 3 → ℚ) (p : Pose ℚ) (ε : ℚ)
   (approx : RationalApprox.Approx) : ℚ :=
   (p.rotM₂Rℚ v₁ ⬝ᵥ p.rotM₂Rℚ (v₁ - v₂) - 10 * κℚ - 2 * ε * (approx.upper_sqrt.norm (v₁ - v₂) + 2 * κℚ) * (approx.upper_sqrt_two + ε))
   / ((approx.upper_sqrt.norm (p.rotM₂Rℚ v₁) + approx.upper_sqrt_two * ε + 3 * κℚ) * (approx.upper_sqrt.norm (p.rotM₂Rℚ (v₁ - v₂)) + 2 * approx.upper_sqrt_two * ε + 6 * κℚ))

/--
Condition B_ε^ℚ from [SY25] Theorem 48. As in `Local.Bε`, the triangle it
constrains is `v_ ∘ Qi`; taking the indices `Qi` rather than the triangle
itself guarantees that the triangle's vertices are among the polyhedron's
vertices `v_`.
-/
def TriangleQ.Bεℚ {ι : Type} [Fintype ι] [DecidableEq ι] (Qi : Fin 3 → ι)
    (v_ : ι → Fin 3 → ℚ) (p : Pose ℚ) (ε δ r : ℚ) (approx : RationalApprox.Approx) : Prop :=
  ∀ i : Fin 3, ∀ k : ι, k ≠ Qi i →
    (δ + approx.upper_sqrt_five * ε) / r < TriangleQ.Bεℚ.lhs (v_ (Qi i)) (v_ k) p ε approx

namespace TriangleQ.Bεℚ

/-- Hoisted entries of `rotMℚ_mat p.θ₂ p.φ₂` so that sin/cos partial sums
are evaluated once per pose, not once per matrix-vector multiply. -/
structure MatEntries : Type where
  m₀₀ : ℚ
  m₀₁ : ℚ
  m₀₂ : ℚ
  m₁₀ : ℚ
  m₁₁ : ℚ
  m₁₂ : ℚ

@[inline] def matEntries (p : Pose ℚ) : MatEntries :=
  let st := RationalApprox.sinℚ p.θ₂
  let ct := RationalApprox.cosℚ p.θ₂
  let sp := RationalApprox.sinℚ p.φ₂
  let cp := RationalApprox.cosℚ p.φ₂
  ⟨-st, ct, 0, -ct * cp, -st * cp, sp⟩

@[inline] def MatEntries.applyVec (e : MatEntries) (v : Fin 3 → ℚ) : Fin 2 → ℚ
  | 0 => e.m₀₀ * v 0 + e.m₀₁ * v 1 + e.m₀₂ * v 2
  | 1 => e.m₁₀ * v 0 + e.m₁₁ * v 1 + e.m₁₂ * v 2

private lemma MatEntries.applyVec_eq (p : Pose ℚ) (v : Fin 3 → ℚ) :
    (matEntries p).applyVec v = p.rotM₂ℚ v := by
  ext i
  unfold Pose.rotM₂ℚ RationalApprox.rotMℚ RationalApprox.rotMℚ_mat
  rw [Matrix.toLin'_apply]
  fin_cases i <;>
    simp [MatEntries.applyVec, matEntries, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Component form of `Pose.rotM₂Rℚ`, as computed by the scalarized checkers. -/
lemma rotM₂Rℚ_c0 (p : Pose ℚ) (u : Fin 3 → ℚ) :
    p.rotM₂Rℚ u 0 = RationalApprox.round13
      ((matEntries p).m₀₀ * u 0 + (matEntries p).m₀₁ * u 1 + (matEntries p).m₀₂ * u 2) :=
  congrArg RationalApprox.round13 (congrFun (MatEntries.applyVec_eq p u) 0).symm

lemma rotM₂Rℚ_c1 (p : Pose ℚ) (u : Fin 3 → ℚ) :
    p.rotM₂Rℚ u 1 = RationalApprox.round13
      ((matEntries p).m₁₀ * u 0 + (matEntries p).m₁₁ * u 1 + (matEntries p).m₁₂ * u 2) :=
  congrArg RationalApprox.round13 (congrFun (MatEntries.applyVec_eq p u) 1).symm

/-- Bool-valued `Bεℚ` check that hoists per-pose matrix entries and
per-`i` `M₂·Q_i` / sqrtUp norms out of the inner-`k` `decide`. The
outer `Fin 3` loop short-circuits via `List.all`. -/
def check {ι : Type} [Fintype ι] [DecidableEq ι] (Qi : Fin 3 → ι)
    (v_ : ι → Fin 3 → ℚ) (p : Pose ℚ) (ε δ r : ℚ)
    (approx : RationalApprox.Approx) : Bool :=
  let entries := matEntries p
  let bound := (δ + approx.upper_sqrt_five * ε) / r
  (List.finRange 3).all fun i =>
    let Qi_val := v_ (Qi i)
    -- All intermediate values are bound as scalars: `Fin n → ℚ` values are
    -- closures that would re-evaluate their components (vertex-coordinate
    -- divisions, matrix-vector products, `round13` calls) on every access
    -- in the `k`-loop below.
    let q0 := RationalApprox.round13
      (entries.m₀₀ * Qi_val 0 + entries.m₀₁ * Qi_val 1 + entries.m₀₂ * Qi_val 2)
    let q1 := RationalApprox.round13
      (entries.m₁₀ * Qi_val 0 + entries.m₁₁ * Qi_val 1 + entries.m₁₂ * Qi_val 2)
    let denom1 := approx.upper_sqrt.f (q0 * q0 + q1 * q1) + approx.upper_sqrt_two * ε + 3 * κℚ
    decide <| ∀ k : ι, k ≠ Qi i →
      let dv := Qi_val - v_ k
      let dv0 := dv 0
      let dv1 := dv 1
      let dv2 := dv 2
      let d0 := RationalApprox.round13 (entries.m₀₀ * dv0 + entries.m₀₁ * dv1 + entries.m₀₂ * dv2)
      let d1 := RationalApprox.round13 (entries.m₁₀ * dv0 + entries.m₁₁ * dv1 + entries.m₁₂ * dv2)
      let n_dv := approx.upper_sqrt.f (dv0 * dv0 + dv1 * dv1 + dv2 * dv2)
      let numer := q0 * d0 + q1 * d1 - 10 * κℚ
                   - 2 * ε * (n_dv + 2 * κℚ) * (approx.upper_sqrt_two + ε)
      let denom2 := approx.upper_sqrt.f (d0 * d0 + d1 * d1)
                    + 2 * approx.upper_sqrt_two * ε + 6 * κℚ
      bound < numer / (denom1 * denom2)

theorem check_iff {ι : Type} [Fintype ι] [DecidableEq ι] (Qi : Fin 3 → ι)
    (v_ : ι → Fin 3 → ℚ) (p : Pose ℚ) (ε δ r : ℚ) (approx : RationalApprox.Approx) :
    check Qi v_ p ε δ r approx = true ↔ Bεℚ Qi v_ p ε δ r approx := by
  unfold check Bεℚ Bεℚ.lhs
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]
  refine forall_congr' (fun i => ?_)
  refine forall_congr' (fun k => ?_)
  refine forall_congr' (fun _ => ?_)
  rw [← rotM₂Rℚ_c0 p (v_ (Qi i)), ← rotM₂Rℚ_c1 p (v_ (Qi i)),
      ← rotM₂Rℚ_c0 p (v_ (Qi i) - v_ k), ← rotM₂Rℚ_c1 p (v_ (Qi i) - v_ k)]
  simp only [RationalApprox.UpperSqrt.norm, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three]

instance instDecidable {ι : Type} [Fintype ι] [DecidableEq ι]
    (Qi : Fin 3 → ι) (v_ : ι → Fin 3 → ℚ)
    (p : Pose ℚ) (ε δ r : ℚ) (approx : RationalApprox.Approx) :
    Decidable (Bεℚ Qi v_ p ε δ r approx) :=
  decidable_of_iff _ (check_iff Qi v_ p ε δ r approx)

end TriangleQ.Bεℚ

end Local

namespace RationalApprox

/--
If we have indices `Pi` for a triangle in `poly`, yield the corresponding
triangle in `poly_` which κ-approximates it.
-/
def κApproxPoly.transportTri {ι : Type} [Fintype ι]
    {A : Polyhedron ι ℝ³} {B : Polyhedron ι (Fin 3 → ℚ)}
    (Pi : Fin 3 → ι)
    (hpoly : κApproxPoly A B) : Local.TriangleQ :=
  fun i => B.v (hpoly.bijection (Pi i))

namespace LocalTheorem

/--
Helper used inside `rational_local`'s `Aε` bridge: rephrases the rational
"angle" inequality on the real side, common to `ae₁'` and `ae₂'`.
-/
private lemma aε_bridge {θ φ : ℚ} {ε : ℚ} {approx : Approx}
    (T : Local.TriangleQ) (R : Triangle)
    (hθ : (θ : ℝ) ∈ Set.Icc (-4 : ℝ) 4) (hφ : (φ : ℝ) ∈ Set.Icc (-4 : ℝ) 4)
    (hRnorm : ∀ i : Fin 3, ‖R i‖ ≤ 1)
    (hRapprox : ∀ i : Fin 3, ‖R i - toR3 (T i)‖ ≤ κ)
    (hAε : T.Aεℚ (vecXℚ θ φ) ε approx)
    (hεℝ : 0 < (ε : ℝ)) :
    R.Aε (vecX (θ : ℝ) (φ : ℝ)) ε := by
  obtain ⟨σ, hσ₂⟩ := hAε
  refine ⟨σ, fun i => ?_⟩
  set θsub : Set.Icc (-4 : ℝ) 4 := ⟨(θ : ℝ), hθ⟩
  set φsub : Set.Icc (-4 : ℝ) 4 := ⟨(φ : ℝ), hφ⟩
  have hX : ‖⟪vecX (θsub : ℝ) (φsub : ℝ), R i⟫ -
            ⟪vecXℚℝ (θsub : ℝ) (φsub : ℝ), toR3 (T i)⟫‖ ≤ 3 * κ :=
    bounds_kappa3_X (θ := θsub) (φ := φsub) (hRnorm i) (hRapprox i)
  have h_inner_eq :
      @inner ℝ ℝ³ _ (vecXℚℝ (θ : ℝ) (φ : ℝ)) (toR3 (T i)) =
        (((vecXℚ θ φ) ⬝ᵥ T i : ℚ) : ℝ) := by
    rw [← toR3_vecXℚ]; exact inner_toR3 _ _
  have hσ₂i : (-1) ^ σ * ⟪vecXℚℝ (θ : ℝ) (φ : ℝ), toR3 (T i)⟫ >
      approx.upper_sqrt_two * ε + 3 * κ := by
    rw [h_inner_eq, ← cast_κℚ,
        show ((-1 : ℝ)) ^ σ = ((((-1 : ℚ)) ^ σ : ℚ) : ℝ) by push_cast; rfl]
    exact_mod_cast hσ₂ i
  have h_us2_eps : (√2 : ℝ) * ε ≤ approx.upper_sqrt_two * ε :=
    mul_le_mul_of_nonneg_right approx.upper_sqrt_two_gt_sqrt_two.le hεℝ.le
  rw [Real.norm_eq_abs] at hX
  have habs : |(-1 : ℝ) ^ σ| = 1 := abs_neg_one_pow σ
  have hdiff : |(-1 : ℝ) ^ σ * (⟪vecX (θ : ℝ) (φ : ℝ), R i⟫ -
                                  ⟪vecXℚℝ (θ : ℝ) (φ : ℝ), toR3 (T i)⟫)| ≤ 3 * κ := by
    rw [abs_mul, habs, one_mul]; exact hX
  rw [abs_le] at hdiff
  linarith [hdiff.1,
    mul_sub ((-1 : ℝ) ^ σ) ⟪vecX (θ : ℝ) (φ : ℝ), R i⟫
      ⟪vecXℚℝ (θ : ℝ) (φ : ℝ), toR3 (T i)⟫]


abbrev BoundDeltaℚi (p : Pose ℚ) (P_ Q_ : Local.TriangleQ) (approx : Approx) (i : Fin 3) : ℚ :=
  approx.upper_sqrt.norm (p.rotRℚ (p.rotM₁ℚ (P_ i)) - p.rotM₂ℚ (Q_ i)) / 2 + 3 * κℚ

/-- The condition on δ -/
def BoundDeltaℚ (δ : ℚ) (p : Pose ℚ) (P_ Q_ : Local.TriangleQ) (approx : Approx) : Prop :=
  ∀ i : Fin 3, δ ≥ BoundDeltaℚi p P_ Q_ approx i
deriving Decidable

/-- The condition on r. The applied vector is the *rounded* `p.rotM₂Rℚ` one
(multiples of `10⁻¹³` componentwise), so the `LowerSqrt` norm here runs on
small denominators; the rounding error is absorbed into the `3κℚ` term (see
`LowerSqrt_norm_round13v_le` and the `hr₁'` bridge in `rational_local`). -/
def BoundRℚ (r ε : ℚ) (p : Pose ℚ) (Q_ : Local.TriangleQ) (approx : Approx) : Prop :=
  ∀ i : Fin 3, approx.lower_sqrt.norm (p.rotM₂Rℚ (Q_ i)) > r + approx.upper_sqrt_two * ε + 3 * κℚ

namespace BoundRℚ

/-- Bool-valued `BoundRℚ` check that hoists the per-pose matrix entries
(trig partial sums) and the right-hand side out of the `i`-loop and binds
the applied vector's components as scalars. -/
def check (r ε : ℚ) (p : Pose ℚ) (Q_ : Local.TriangleQ) (approx : Approx) : Bool :=
  let entries := Local.TriangleQ.Bεℚ.matEntries p
  let rhs := r + approx.upper_sqrt_two * ε + 3 * κℚ
  (List.finRange 3).all fun i =>
    let Qi := Q_ i
    let v0 := Qi 0
    let v1 := Qi 1
    let v2 := Qi 2
    let q0 := round13 (entries.m₀₀ * v0 + entries.m₀₁ * v1 + entries.m₀₂ * v2)
    let q1 := round13 (entries.m₁₀ * v0 + entries.m₁₁ * v1 + entries.m₁₂ * v2)
    decide (rhs < approx.lower_sqrt.f (q0 * q0 + q1 * q1))

theorem check_iff (r ε : ℚ) (p : Pose ℚ) (Q_ : Local.TriangleQ) (approx : Approx) :
    check r ε p Q_ approx = true ↔ BoundRℚ r ε p Q_ approx := by
  unfold check BoundRℚ
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]
  refine forall_congr' fun i => ?_
  rw [← Local.TriangleQ.Bεℚ.rotM₂Rℚ_c0 p (Q_ i), ← Local.TriangleQ.Bεℚ.rotM₂Rℚ_c1 p (Q_ i)]
  simp only [LowerSqrt.norm, dotProduct, Fin.sum_univ_two]

instance instDecidable (r ε : ℚ) (p : Pose ℚ) (Q_ : Local.TriangleQ) (approx : Approx) :
    Decidable (BoundRℚ r ε p Q_ approx) :=
  decidable_of_iff _ (check_iff r ε p Q_ approx)

end BoundRℚ

/--
A compact way of saying "the rational pose `p_` satisfies the Rational Local
Theorem precondition at width `ε`": indices `Pi`, `Qi` of a pair of congruent
triangles among the vertices of `poly`, the bounds `δ` and `r`, and a
square-root approximation scheme, with all the hypotheses of [SY25] Theorem 48
packaged together. This is the form produced by the computational checker.
-/
structure RationalLocalTheoremPrecondition {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (poly : GoodPoly ι) (poly_ : Polyhedron ι (Fin 3 → ℚ))
    (hpoly : κApproxPoly poly.vertices poly_)
    (p_ : Pose ℚ) (ε : ℚ) : Type where
  Pi : Fin 3 → ι
  Qi : Fin 3 → ι
  cong_tri : Triangle.Congruent (poly.vertices.v ∘ Pi) (poly.vertices.v ∘ Qi)
  hp : p_ ∈ fourInterval ℚ
  δ : ℚ
  r : ℚ
  hr : 0 < r
  approx : Approx
  hr₁ : BoundRℚ r ε p_ (hpoly.transportTri Qi) approx
  hδ : BoundDeltaℚ δ p_ (hpoly.transportTri Pi) (hpoly.transportTri Qi) approx
  ae₁ : (hpoly.transportTri Pi).Aεℚ p_.vecX₁ℚ ε approx
  ae₂ : (hpoly.transportTri Qi).Aεℚ p_.vecX₂ℚ ε approx
  span₁ : (hpoly.transportTri Pi).toReal.κSpanning (p_.θ₁ : ℝ) (p_.φ₁ : ℝ) ε
  span₂ : (hpoly.transportTri Qi).toReal.κSpanning (p_.θ₂ : ℝ) (p_.φ₂ : ℝ) ε
  be : Local.TriangleQ.Bεℚ Qi
        (fun k => poly_.v (hpoly.bijection k)) p_ ε δ r approx

/-- Cast `Bεℚ.lhs` to `ℝ` (the rounded dot product stays a cast atom); the main
bridge used inside `rational_local`'s `Bε` argument. -/
private lemma Bεℚ_lhs_eq_real (p_ℚ : Pose ℚ) (ε : ℚ) (approx : Approx) (v₁ v₂ : Fin 3 → ℚ) :
    (Local.TriangleQ.Bεℚ.lhs v₁ v₂ p_ℚ ε approx : ℝ) =
    (((p_ℚ.rotM₂Rℚ v₁ ⬝ᵥ p_ℚ.rotM₂Rℚ (v₁ - v₂) : ℚ) : ℝ) - 10 * κ -
       2 * ε * ((approx.upper_sqrt.norm (v₁ - v₂) : ℝ) + 2 * κ) *
         (approx.upper_sqrt_two + ε)) /
    (((approx.upper_sqrt.norm (p_ℚ.rotM₂Rℚ v₁) : ℝ) + approx.upper_sqrt_two * ε + 3 * κ) *
     ((approx.upper_sqrt.norm (p_ℚ.rotM₂Rℚ (v₁ - v₂)) : ℝ) +
        2 * approx.upper_sqrt_two * ε + 6 * κ)) := by
  unfold Local.TriangleQ.Bεℚ.lhs
  push_cast [← cast_κℚ]
  ring

/-- Bridge `BoundRℚ` (rational side) to `BoundR` (real side), used inside `rational_local`. -/
private lemma boundR_bridge {p_ℚ : Pose ℚ} {ε r : ℚ} {approx : Approx}
    (T : Local.TriangleQ) (R : Triangle)
    (hθ : ((p_ℚ.θ₂ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ : ((p_ℚ.φ₂ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hRnorm : ∀ i : Fin 3, ‖R i‖ ≤ 1)
    (hRapprox : ∀ i : Fin 3, ‖R i - toR3 (T i)‖ ≤ κ)
    (hεℝ : 0 < (ε : ℝ))
    (hr₁ : BoundRℚ r ε p_ℚ T approx) :
    Local.BoundR r ε p_ℚ.toReal R := by
  intro i
  set θ₂ : Set.Icc (-4 : ℝ) 4 := ⟨(p_ℚ.θ₂ : ℝ), hθ⟩
  set φ₂ : Set.Icc (-4 : ℝ) 4 := ⟨(p_ℚ.φ₂ : ℝ), hφ⟩
  have h_us2_eps : (√2 : ℝ) * ε ≤ approx.upper_sqrt_two * ε :=
    mul_le_mul_of_nonneg_right approx.upper_sqrt_two_gt_sqrt_two.le hεℝ.le
  have h_toR2_eq : (rotMℚℝ ↑θ₂ ↑φ₂) (toR3 (T i)) = toR2 (p_ℚ.rotM₂ℚ (T i)) :=
    (toR2_pose_rotM₂ℚ _ _).symm
  have hsl : (approx.lower_sqrt.norm (p_ℚ.rotM₂Rℚ (T i)) : ℝ) ≤
      ‖(rotMℚℝ ↑θ₂ ↑φ₂) (toR3 (T i))‖ + 2 / 10 ^ 13 := by
    rw [h_toR2_eq]; exact LowerSqrt_norm_round13v_le approx.lower_sqrt _
  have hM₂diff : ‖rotM (↑θ₂ : ℝ) ↑φ₂ - rotMℚℝ ↑θ₂ ↑φ₂‖ ≤ κ :=
    M_difference_norm_bounded _ _ θ₂.property φ₂.property
  have hM₂ℚnorm : ‖rotMℚℝ (↑θ₂ : ℝ) ↑φ₂‖ ≤ 1 + κ :=
    Mℚ_norm_bounded θ₂.property φ₂.property
  have hMQ : |(‖(rotM ↑θ₂ ↑φ₂) (R i)‖ - ‖(rotMℚℝ ↑θ₂ ↑φ₂) (toR3 (T i))‖)| ≤ 2 * κ + κ ^ 2 :=
    (abs_norm_sub_norm_le _ _).trans
      (clm_approx_apply_sub hM₂diff hM₂ℚnorm (hRnorm i) (hRapprox i))
  show ‖(rotM ↑θ₂ ↑φ₂) (R i)‖ > r + √2 * ε
  have hr₁i : (approx.lower_sqrt.norm (p_ℚ.rotM₂Rℚ (T i)) : ℝ) > r + √2 * ε + 3 * κ := by
    have hcast : ((approx.lower_sqrt.norm (p_ℚ.rotM₂Rℚ (T i)) : ℚ) : ℝ) >
        ((r + approx.upper_sqrt_two * ε + 3 * κℚ : ℚ) : ℝ) := mod_cast hr₁ i
    push_cast [cast_κℚ] at hcast
    linarith [h_us2_eps]
  rw [abs_le] at hMQ
  have hκabsorb : 2 / 10 ^ 13 + (2 * κ + κ ^ 2) ≤ 3 * κ := by unfold κ; norm_num
  linarith [hMQ.1]

private lemma boundDelta_bridge {p_ℚ : Pose ℚ} {δ : ℚ} {approx : Approx}
    (T_P T_Q : Local.TriangleQ) (P Q : Triangle)
    (hθ₁b : ((p_ℚ.θ₁ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ₁b : ((p_ℚ.φ₁ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hθ₂b : ((p_ℚ.θ₂ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ₂b : ((p_ℚ.φ₂ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hαb : ((p_ℚ.α : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hPnorm : ∀ i : Fin 3, ‖P i‖ ≤ 1) (hQnorm : ∀ i : Fin 3, ‖Q i‖ ≤ 1)
    (hPapprox : ∀ i : Fin 3, ‖P i - toR3 (T_P i)‖ ≤ κ)
    (hQapprox : ∀ i : Fin 3, ‖Q i - toR3 (T_Q i)‖ ≤ κ)
    (hδ : BoundDeltaℚ δ p_ℚ T_P T_Q approx) :
    Local.BoundDelta δ p_ℚ.toReal P Q := by
  set p_ := p_ℚ.toReal with hp_def
  set P_ := T_P.toReal with hP_def
  set Q_ := T_Q.toReal with hQ_def
  set θ₁ : Set.Icc (-4 : ℝ) 4 := ⟨(p_ℚ.θ₁ : ℝ), hθ₁b⟩
  set φ₁ : Set.Icc (-4 : ℝ) 4 := ⟨(p_ℚ.φ₁ : ℝ), hφ₁b⟩
  set θ₂ : Set.Icc (-4 : ℝ) 4 := ⟨(p_ℚ.θ₂ : ℝ), hθ₂b⟩
  set φ₂ : Set.Icc (-4 : ℝ) 4 := ⟨(p_ℚ.φ₂ : ℝ), hφ₂b⟩
  intro i
  have hδi := hδ i
  -- su.norm ≥ ‖·‖ (rational form, then convert to real with toR2)
  have h_eq_real :
      toR2 (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ (T_P i)) - p_ℚ.rotM₂ℚ (T_Q i)) =
      p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i) := by
    rw [toR2_sub, toR2_pose_rotRℚ, toR2_pose_rotM₁ℚ, toR2_pose_rotM₂ℚ]; rfl
  have hsu : ‖p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ ≤
      (approx.upper_sqrt.norm (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ (T_P i)) -
          p_ℚ.rotM₂ℚ (T_Q i)) : ℝ) := by
    rw [← h_eq_real]; exact UpperSqrt_norm_le approx.upper_sqrt _
  -- ‖p_.rotR (rotM₁ℚℝ P_) - rotRℚℝ (rotM₁ℚℝ P_)‖ ≤ κ * (1 + κ)  (rotR vs rotRℚℝ discrepancy)
  have h_rotRdiff : ‖p_.rotR - p_.rotRℚℝ‖ ≤ κ := R_difference_norm_bounded p_.α hαb
  have hκ_nn : (0 : ℝ) ≤ κ := by unfold κ; norm_num
  have h_rotM₁ℚ_norm : ‖p_.rotM₁ℚℝ (P_ i)‖ ≤ (1 + κ) * (1 + κ) :=
    approx_image_norm_le (Mℚ_norm_bounded θ₁.property φ₁.property) (hPnorm i) (hPapprox i)
  have h_rotR_diff_apply : ‖p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i))‖ ≤
      κ * ((1 + κ) * (1 + κ)) := by
    have := ContinuousLinearMap.le_opNorm (p_.rotR - p_.rotRℚℝ) (p_.rotM₁ℚℝ (P_ i))
    simp only [sub_apply] at this
    exact this.trans (mul_le_mul h_rotRdiff h_rotM₁ℚ_norm (norm_nonneg _) (by linarith))
  -- ‖real - rational‖ ≤ 6κ
  have hM₁diff : ‖rotM (↑θ₁ : ℝ) ↑φ₁ - rotMℚℝ ↑θ₁ ↑φ₁‖ ≤ κ :=
    M_difference_norm_bounded _ _ θ₁.property φ₁.property
  have hM₁ℚnorm : ‖rotMℚℝ (↑θ₁ : ℝ) ↑φ₁‖ ≤ 1 + κ :=
    Mℚ_norm_bounded θ₁.property φ₁.property
  have hM₂diff : ‖rotM (↑θ₂ : ℝ) ↑φ₂ - rotMℚℝ ↑θ₂ ↑φ₂‖ ≤ κ :=
    M_difference_norm_bounded _ _ θ₂.property φ₂.property
  have hM₂ℚnorm : ‖rotMℚℝ (↑θ₂ : ℝ) ↑φ₂‖ ≤ 1 + κ :=
    Mℚ_norm_bounded θ₂.property φ₂.property
  have h₁ : ‖(rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub hM₁diff hM₁ℚnorm (hPnorm i) (hPapprox i)
  have h₂ : ‖(rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub hM₂diff hM₂ℚnorm (hQnorm i) (hQapprox i)
  have hdiff : ‖(p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i)) -
      (p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i))‖ ≤ 4 * κ + 2 * κ ^ 2 := by
    show ‖(rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i)) - (rotM ↑θ₂ ↑φ₂) (Q i)) -
          (rotR p_.α ((rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i))‖ ≤ _
    have hrw : rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i)) - (rotM ↑θ₂ ↑φ₂) (Q i) -
          (rotR p_.α ((rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)) =
          rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)) -
          ((rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)) := by
      simp [map_sub]; abel
    rw [hrw]
    calc ‖rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)) -
            ((rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i))‖
      _ ≤ ‖rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i))‖ +
          ‖(rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖ := norm_sub_le _ _
      _ = ‖(rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)‖ +
          ‖(rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖ := by
        rw [Bounding.rotR_preserves_norm]
      _ ≤ (2 * κ + κ ^ 2) + (2 * κ + κ ^ 2) := add_le_add h₁ h₂
      _ = 4 * κ + 2 * κ ^ 2 := by ring
  show (δ : ℝ) ≥ ‖p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i)‖ / 2
  have hnorm_le : ‖p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i)‖ ≤
      ‖p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ + (4 * κ + 2 * κ ^ 2) := by
    linarith [norm_le_insert' (p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i))
      (p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i))]
  -- Bridge `p_.rotR` to `p_.rotRℚℝ` introducing extra κ-slack.
  have h_rotR_to_rotRℚℝ : ‖p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ ≤
      ‖p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ + κ * ((1 + κ) * (1 + κ)) := by
    have h_diff_eq : p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i) =
        (p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)) +
        (p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i))) := by abel
    rw [h_diff_eq]
    calc ‖(p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)) +
          (p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)))‖
      _ ≤ ‖p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ +
          ‖p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i))‖ := norm_add_le _ _
      _ ≤ ‖p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ + κ * ((1 + κ) * (1 + κ)) := by
          linarith [h_rotR_diff_apply]
  have h_total_slack : κ * ((1 + κ) * (1 + κ)) + (4 * κ + 2 * κ ^ 2) ≤ 6 * κ := by
    unfold κ; norm_num
  -- Combine everything.
  have h_chain : ‖p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i)‖ ≤
      (approx.upper_sqrt.norm (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ (T_P i)) -
          p_ℚ.rotM₂ℚ (T_Q i)) : ℝ) + 6 * κ := by
    linarith [hsu, hnorm_le, h_rotR_to_rotRℚℝ, h_total_slack]
  -- Now use hδi: δ ≥ s.norm(...) / 2 + 3 * κℚ in ℚ
  have hδiℝ : (δ : ℝ) ≥
      (approx.upper_sqrt.norm (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ (T_P i)) -
          p_ℚ.rotM₂ℚ (T_Q i)) : ℝ) / 2 + 3 * κ := by
    have hcast : ((approx.upper_sqrt.norm (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ (T_P i)) -
          p_ℚ.rotM₂ℚ (T_Q i)) / 2 + 3 * κℚ : ℚ) : ℝ) ≤ (δ : ℝ) := by
      exact_mod_cast hδi
    push_cast [cast_κℚ] at hcast
    linarith
  linarith [hδiℝ, h_chain]

/-- Bridge `Bεℚ` (rational side) to `Bε` (real side), used inside `rational_local`. -/
private lemma bε_bridge {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {poly : GoodPoly ι} {poly_ : Polyhedron ι (Fin 3 → ℚ)}
    (hpoly : κApproxPoly poly.vertices poly_)
    (Qi : Fin 3 → ι) {p_ℚ : Pose ℚ} {ε δ r : ℚ} {approx : Approx}
    (hθ₂b : ((p_ℚ.θ₂ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ₂b : ((p_ℚ.φ₂ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hεℝ : 0 < (ε : ℝ)) (hr : 0 < r) (hδ_pos : 0 < (δ : ℝ))
    (be : Local.TriangleQ.Bεℚ Qi (fun k => poly_.v (hpoly.bijection k)) p_ℚ ε δ r approx) :
    Local.Bε Qi poly.vertices.v p_ℚ.toReal ε δ r := by
  set p_ := p_ℚ.toReal with hp_def
  set Q : Triangle := fun j => poly.vertices.v (Qi j) with hQdef
  set Q_ := (hpoly.transportTri Qi).toReal with hQ_def
  set θ₂ : Set.Icc (-4 : ℝ) 4 := ⟨(p_ℚ.θ₂ : ℝ), hθ₂b⟩
  set φ₂ : Set.Icc (-4 : ℝ) 4 := ⟨(p_ℚ.φ₂ : ℝ), hφ₂b⟩
  have hQnorm (j : Fin 3) : ‖Q j‖ ≤ 1 := poly.vertex_radius_le_one (Qi j)
  have hQapprox (j : Fin 3) : ‖Q j - Q_ j‖ ≤ κ := hpoly.approx (Qi j)
  have h_upper_norm_toR3 : ∀ (v : Fin 3 → ℚ),
      (approx.upper_sqrt.norm v : ℝ) ≥ ‖toR3 v‖ := fun v =>
    UpperSqrt_norm_le approx.upper_sqrt v
  have h_upper_norm_toR2 : ∀ (v : Fin 2 → ℚ),
      (approx.upper_sqrt.norm v : ℝ) ≥ ‖toR2 v‖ := fun v =>
    UpperSqrt_norm_le approx.upper_sqrt v
  have h_Bεℚ_lhs_bridge := Bεℚ_lhs_eq_real p_ℚ ε approx
  intro i k hne_k
  -- Map k to v_ in poly_
  let k' := hpoly.bijection k
  let v_ℚ : Fin 3 → ℚ := poly_.v k'
  set v_ : ℝ³ := poly_.toReal.v k'
  have hvapprox : ‖poly.vertices.v k - v_‖ ≤ κ := hpoly.approx k
  have hvnorm : ‖poly.vertices.v k‖ ≤ 1 := poly.vertex_radius_le_one k
  -- The rational forms of Q_ i and v_ (definitionally equal via toR3).
  let Q_ℚ : Fin 3 → ℚ := (hpoly.transportTri Qi) i
  -- Get the Bεℚ hypothesis
  have hbe : (δ + approx.upper_sqrt_five * ε) / r <
      Local.TriangleQ.Bεℚ.lhs Q_ℚ v_ℚ p_ℚ ε approx := be i k hne_k
  show (δ + √5 * ε) / r < Local.Bε.lhs (Q i) (poly.vertices.v k) p_ ε
  -- Use the bridge to rewrite `Bεℚ.lhs` into explicit real form.
  have h_bridge_Qv := h_Bεℚ_lhs_bridge Q_ℚ v_ℚ
  -- Bridge from approx.upper_sqrt_five to √5 (since upper_sqrt_five > √5)
  have hbe' : (↑δ + √5 * ↑ε) / ↑r <
      ((((p_ℚ.rotM₂Rℚ Q_ℚ ⬝ᵥ p_ℚ.rotM₂Rℚ (Q_ℚ - v_ℚ)) : ℚ) : ℝ) - 10 * κ -
         2 * ε * ((approx.upper_sqrt.norm (Q_ℚ - v_ℚ) : ℝ) + 2 * κ) * (approx.upper_sqrt_two + ε)) /
      (((approx.upper_sqrt.norm (p_ℚ.rotM₂Rℚ Q_ℚ) : ℝ) + approx.upper_sqrt_two * ε + 3 * κ) *
       ((approx.upper_sqrt.norm (p_ℚ.rotM₂Rℚ (Q_ℚ - v_ℚ)) : ℝ) + 2 * approx.upper_sqrt_two * ε + 6 * κ)) := by
    rw [← h_bridge_Qv]
    have h_le : (↑δ + √5 * ↑ε) / ↑r ≤ (↑δ + ↑approx.upper_sqrt_five * ↑ε) / ↑r := by
      gcongr
      exact approx.upper_sqrt_five_gt_sqrt_five.le
    have hbe_ℝ : ((δ + approx.upper_sqrt_five * ε) / r : ℝ) <
        (Local.TriangleQ.Bεℚ.lhs Q_ℚ v_ℚ p_ℚ ε approx : ℝ) := mod_cast hbe
    exact h_le.trans_lt hbe_ℝ
  -- Helper facts
  have hκ_pos : (0 : ℝ) < κ := by unfold κ; norm_num
  -- Bridges relating real and rational norms via UpperSqrt_norm_le.
  have h_toR3_sub_Qv : toR3 (Q_ℚ - v_ℚ) = toR3 Q_ℚ - toR3 v_ℚ := toR3_sub _ _
  have h_norm_Qv_rat : ‖toR3 Q_ℚ - toR3 v_ℚ‖ ≤ (approx.upper_sqrt.norm (Q_ℚ - v_ℚ) : ℝ) := by
    rw [← h_toR3_sub_Qv]; exact h_upper_norm_toR3 _
  have h_snorm_Q_nn : (0 : ℝ) ≤ (approx.upper_sqrt.norm (p_ℚ.rotM₂Rℚ Q_ℚ) : ℝ) :=
    le_trans (norm_nonneg (toR2 (p_ℚ.rotM₂Rℚ Q_ℚ))) (h_upper_norm_toR2 _)
  have h_snorm_Qv_nn : (0 : ℝ) ≤ (approx.upper_sqrt.norm (p_ℚ.rotM₂Rℚ (Q_ℚ - v_ℚ)) : ℝ) :=
    le_trans (norm_nonneg (toR2 (p_ℚ.rotM₂Rℚ (Q_ℚ - v_ℚ)))) (h_upper_norm_toR2 _)
  have h_us2_nn : (0 : ℝ) ≤ approx.upper_sqrt_two :=
    (Real.sqrt_nonneg 2).trans approx.upper_sqrt_two_gt_sqrt_two.le
  have h_us2_le : (√2 : ℝ) ≤ approx.upper_sqrt_two := approx.upper_sqrt_two_gt_sqrt_two.le
  have hsu_norm_nn : (0 : ℝ) ≤ (approx.upper_sqrt.norm (Q_ℚ - v_ℚ) : ℝ) :=
    (norm_nonneg _).trans h_norm_Qv_rat
  -- Denominator positivity
  have hden_pos : 0 < ((approx.upper_sqrt.norm (p_ℚ.rotM₂Rℚ Q_ℚ) : ℝ) + approx.upper_sqrt_two * ε + 3 * κ) *
      ((approx.upper_sqrt.norm (p_ℚ.rotM₂Rℚ (Q_ℚ - v_ℚ)) : ℝ) + 2 * approx.upper_sqrt_two * ε + 6 * κ) := by
    positivity
  -- Extract positivity of Bεℚ numerator
  have hBεℚ_num_pos : 0 < (((p_ℚ.rotM₂Rℚ Q_ℚ ⬝ᵥ p_ℚ.rotM₂Rℚ (Q_ℚ - v_ℚ)) : ℚ) : ℝ) - 10 * κ -
      2 * ε * ((approx.upper_sqrt.norm (Q_ℚ - v_ℚ) : ℝ) + 2 * κ) * (approx.upper_sqrt_two + ε) := by
    have h0 : 0 < (δ + √5 * ε) / r := by positivity
    refine (div_pos_iff_of_pos_right hden_pos).mp (h0.trans ?_)
    exact hbe'
  -- bounds_kappa4_Aℚ in real form
  have h_num_sub : 2 * (ε : ℝ) * (‖toR3 Q_ℚ - toR3 v_ℚ‖ + 2 * κ) * (√2 + ε) ≤
      2 * ε * ((approx.upper_sqrt.norm (Q_ℚ - v_ℚ) : ℝ) + 2 * κ) * (approx.upper_sqrt_two + ε) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith [h_norm_Qv_rat]) (by linarith))
      (by linarith) (by positivity) (by positivity)
  have hAℚ_num_pos : 0 < (((p_ℚ.rotM₂Rℚ Q_ℚ ⬝ᵥ p_ℚ.rotM₂Rℚ (Q_ℚ - v_ℚ)) : ℚ) : ℝ) - 10 * κ -
      2 * ε * (‖toR3 Q_ℚ - toR3 v_ℚ‖ + 2 * κ) * (√2 + ε) := by
    linarith [hBεℚ_num_pos]
  -- Approximation bound for `Q i - v k` (used for the ε-term comparison)
  have hQv_approx : ‖(Q i - poly.vertices.v k) - (toR3 Q_ℚ - toR3 v_ℚ)‖ ≤ 2 * κ := by
    rw [show toR3 Q_ℚ - toR3 v_ℚ = Q_ i - v_ from rfl]
    calc ‖(Q i - poly.vertices.v k) - (Q_ i - v_)‖
        = ‖(Q i - Q_ i) - (poly.vertices.v k - v_)‖ := by congr 1; abel
      _ ≤ ‖Q i - Q_ i‖ + ‖poly.vertices.v k - v_‖ := norm_sub_le _ _
      _ ≤ κ + κ := add_le_add (hQapprox i) hvapprox
      _ = 2 * κ := by ring
  -- Apply bounds_kappa4
  have h_Q_approx : ‖Q i - toR3 Q_ℚ‖ ≤ κ := hQapprox i
  have h_v_approx : ‖poly.vertices.v k - toR3 v_ℚ‖ ≤ κ := hvapprox
  have hA_nonneg : 0 ≤ ⟪(rotM (p_ℚ.θ₂ : ℝ) (p_ℚ.φ₂ : ℝ)) (Q i),
      (rotM (p_ℚ.θ₂ : ℝ) (p_ℚ.φ₂ : ℝ)) (Q i - poly.vertices.v k)⟫ -
      2 * ε * ‖Q i - poly.vertices.v k‖ * (√2 + ε) := by
    have h_inner_10 : |⟪(rotM (p_ℚ.θ₂ : ℝ) (p_ℚ.φ₂ : ℝ)) (Q i),
          (rotM (p_ℚ.θ₂ : ℝ) (p_ℚ.φ₂ : ℝ)) (Q i - poly.vertices.v k)⟫ -
        (((p_ℚ.rotM₂Rℚ Q_ℚ ⬝ᵥ p_ℚ.rotM₂Rℚ (Q_ℚ - v_ℚ)) : ℚ) : ℝ)| ≤ 10 * κ :=
      inner_product_bound_round_10kappa (θ := θ₂) (φ := φ₂) rfl rfl
        (hQnorm i) hvnorm h_Q_approx h_v_approx
    have h_inner_le : (((p_ℚ.rotM₂Rℚ Q_ℚ ⬝ᵥ p_ℚ.rotM₂Rℚ (Q_ℚ - v_ℚ)) : ℚ) : ℝ) - 10 * κ ≤
        ⟪(rotM (p_ℚ.θ₂ : ℝ) (p_ℚ.φ₂ : ℝ)) (Q i),
          (rotM (p_ℚ.θ₂ : ℝ) (p_ℚ.φ₂ : ℝ)) (Q i - poly.vertices.v k)⟫ :=
      sub_le_of_abs_sub_le_left h_inner_10
    have h_norm_QR : ‖Q i - poly.vertices.v k‖ ≤ ‖toR3 Q_ℚ - toR3 v_ℚ‖ + 2 * κ :=
      calc ‖Q i - poly.vertices.v k‖
        _ ≤ ‖toR3 Q_ℚ - toR3 v_ℚ‖ +
            ‖(Q i - poly.vertices.v k) - (toR3 Q_ℚ - toR3 v_ℚ)‖ := norm_le_insert' _ _
        _ ≤ ‖toR3 Q_ℚ - toR3 v_ℚ‖ + 2 * κ := by grw [hQv_approx]
    have h_eps_term : 2 * ε * ‖Q i - poly.vertices.v k‖ * (√2 + ε) ≤
        2 * ε * (‖toR3 Q_ℚ - toR3 v_ℚ‖ + 2 * κ) * (√2 + ε) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left h_norm_QR (by linarith)
      · positivity
    linarith [hAℚ_num_pos]
  have hbk4 : bounds_kappa4_Aℚ Q_ℚ v_ℚ p_ℚ ε approx.upper_sqrt ≤
      bounds_kappa4_A (Q i) (poly.vertices.v k) θ₂ φ₂ ε :=
    bounds_kappa4 (Q i) (poly.vertices.v k) Q_ℚ v_ℚ p_ℚ
      hθ₂b hφ₂b (hQnorm i) hvnorm h_Q_approx h_v_approx ε hεℝ
      approx.upper_sqrt hA_nonneg
  -- Bridge `Bεℚ.lhs` real form ≤ `bounds_kappa4_Aℚ`
  have hBεℚ_le :
      ((((p_ℚ.rotM₂Rℚ Q_ℚ ⬝ᵥ p_ℚ.rotM₂Rℚ (Q_ℚ - v_ℚ)) : ℚ) : ℝ) - 10 * κ -
          2 * ε * ((approx.upper_sqrt.norm (Q_ℚ - v_ℚ) : ℝ) + 2 * κ) * (approx.upper_sqrt_two + ε)) /
        (((approx.upper_sqrt.norm (p_ℚ.rotM₂Rℚ Q_ℚ) : ℝ) + approx.upper_sqrt_two * ε + 3 * κ) *
          ((approx.upper_sqrt.norm (p_ℚ.rotM₂Rℚ (Q_ℚ - v_ℚ)) : ℝ) +
            2 * approx.upper_sqrt_two * ε + 6 * κ)) ≤
      bounds_kappa4_Aℚ Q_ℚ v_ℚ p_ℚ ε approx.upper_sqrt := by
    show _ ≤ ((((p_ℚ.rotM₂Rℚ Q_ℚ ⬝ᵥ p_ℚ.rotM₂Rℚ (Q_ℚ - v_ℚ)) : ℚ) : ℝ) - 10 * κ -
          2 * ε * (‖toR3 (Q_ℚ - v_ℚ)‖ + 2 * κ) * (√2 + ε)) /
      (((approx.upper_sqrt.norm (p_ℚ.rotM₂Rℚ Q_ℚ) : ℝ) + √2 * ε + 3 * κ) *
       ((approx.upper_sqrt.norm (p_ℚ.rotM₂Rℚ (Q_ℚ - v_ℚ)) : ℝ) + 2 * √2 * ε + 6 * κ))
    have h_us2_eps : (√2 : ℝ) * ε ≤ approx.upper_sqrt_two * ε :=
      mul_le_mul_of_nonneg_right h_us2_le hεℝ.le
    rw [h_toR3_sub_Qv]
    refine div_le_div₀ hAℚ_num_pos.le (by linarith [h_num_sub]) (by positivity) ?_
    gcongr
  -- Combine (final step uses defeq `bounds_kappa4_A = Bε.lhs`).
  calc (δ + √5 * ε) / r
      < _ := hbe'
    _ ≤ bounds_kappa4_Aℚ Q_ℚ v_ℚ p_ℚ ε approx.upper_sqrt := hBεℚ_le
    _ ≤ bounds_kappa4_A (Q i) (poly.vertices.v k) θ₂ φ₂ ε := hbk4

/--
[SY25] Theorem 48 "The Rational Local Theorem"
-/
theorem rational_local {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (poly : GoodPoly ι) (poly_ : Polyhedron ι (Fin 3 → ℚ))
    (hpoly : κApproxPoly poly.vertices poly_)
    (p_ : Pose ℚ) (ε : ℚ)
    (pc : RationalLocalTheoremPrecondition poly poly_ hpoly p_ ε)
    : ¬∃ p ∈ Metric.closedBall p_.toReal ε, RupertPose p poly.hull := by
  obtain ⟨Pi, Qi, cong_tri, hp, δ, r, hr, approx,
          hr₁, hδ, ae₁, ae₂, span₁, span₂, be⟩ := pc
  have hεℝ : 0 < (ε : ℝ) := span₁.pos
  -- Keep a handle on the rational pose before shadowing.
  let p_ℚ : Pose ℚ := p_
  set p_ := p_.toReal
  have hp : (fourInterval ℝ).contains p_ := fourInterval_contains_toReal hp
  -- Define the triangles from indices
  let P : Triangle := fun i => poly.vertices.v (Pi i)
  let Q : Triangle := fun i => poly.vertices.v (Qi i)
  -- Abbreviations for transported triangles
  set P_ := (hpoly.transportTri Pi).toReal
  set Q_ := (hpoly.transportTri Qi).toReal
  -- Angle subtypes
  set θ₁ : Set.Icc (-4 : ℝ) 4 := ⟨p_.θ₁, hp.θ₁Bound⟩
  set φ₁ : Set.Icc (-4 : ℝ) 4 := ⟨p_.φ₁, hp.φ₁Bound⟩
  set θ₂ : Set.Icc (-4 : ℝ) 4 := ⟨p_.θ₂, hp.θ₂Bound⟩
  set φ₂ : Set.Icc (-4 : ℝ) 4 := ⟨p_.φ₂, hp.φ₂Bound⟩
  -- Vertex norm bounds
  have hPnorm (i : Fin 3) : ‖P i‖ ≤ 1 := poly.vertex_radius_le_one (Pi i)
  have hQnorm (i : Fin 3) : ‖Q i‖ ≤ 1 := poly.vertex_radius_le_one (Qi i)
  -- Approximation bounds
  have hPapprox (i : Fin 3) : ‖P i - P_ i‖ ≤ κ := hpoly.approx (Pi i)
  have hQapprox (i : Fin 3) : ‖Q i - Q_ i‖ ≤ κ := hpoly.approx (Qi i)
  -- Bridge: κSpanning → Spanning
  have span₁' : P.Spanning p_.θ₁ p_.φ₁ ε :=
    ek_spanning_imp_e_spanning P P_ hPapprox hPnorm hp.θ₁Bound hp.φ₁Bound span₁
  have span₂' : Q.Spanning p_.θ₂ p_.φ₂ ε :=
    ek_spanning_imp_e_spanning Q Q_ hQapprox hQnorm hp.θ₂Bound hp.φ₂Bound span₂
  -- Universal bridges (above) provide the rational ↔ real cast facts we need.
  have h_upper_norm_toR3 : ∀ (v : Fin 3 → ℚ),
      (approx.upper_sqrt.norm v : ℝ) ≥ ‖toR3 v‖ := fun v =>
    UpperSqrt_norm_le approx.upper_sqrt v
  have h_upper_norm_toR2 : ∀ (v : Fin 2 → ℚ),
      (approx.upper_sqrt.norm v : ℝ) ≥ ‖toR2 v‖ := fun v =>
    UpperSqrt_norm_le approx.upper_sqrt v
  -- Main bridge: cast `Bεℚ.lhs` to `ℝ` (the rounded dot product stays a cast atom).
  have h_Bεℚ_lhs_bridge := Bεℚ_lhs_eq_real p_ℚ ε approx
  have h_us2_eps : (√2 : ℝ) * ε ≤ approx.upper_sqrt_two * ε :=
    mul_le_mul_of_nonneg_right approx.upper_sqrt_two_gt_sqrt_two.le hεℝ.le
  have ae₁' : P.Aε p_.vecX₁ ε :=
    aε_bridge (T := hpoly.transportTri Pi) (R := P) hp.θ₁Bound hp.φ₁Bound
      hPnorm hPapprox ae₁ hεℝ
  have ae₂' : Q.Aε p_.vecX₂ ε :=
    aε_bridge (T := hpoly.transportTri Qi) (R := Q) hp.θ₂Bound hp.φ₂Bound
      hQnorm hQapprox ae₂ hεℝ
  -- Bridge: BoundRℚ → BoundR.
  have hr₁' : Local.BoundR r ε p_ Q :=
    boundR_bridge (hpoly.transportTri Qi) Q hp.θ₂Bound hp.φ₂Bound hQnorm hQapprox hεℝ hr₁
  have hδ' : Local.BoundDelta δ p_ P Q :=
    boundDelta_bridge (hpoly.transportTri Pi) (hpoly.transportTri Qi) P Q
      hp.θ₁Bound hp.φ₁Bound hp.θ₂Bound hp.φ₂Bound hp.αBound
      hPnorm hQnorm hPapprox hQapprox hδ
  -- Bridge: Bεℚ → Bε (the δ-positivity fact is extracted from `hδ 0`)
  have hδ_pos : 0 < (δ : ℝ) := by
    have hκ_pos : (0 : ℝ) < κ := by unfold κ; norm_num
    have hsu0 := UpperSqrt_norm_le approx.upper_sqrt
      (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ ((hpoly.transportTri Pi) 0)) -
        p_ℚ.rotM₂ℚ ((hpoly.transportTri Qi) 0))
    have hcast := (Rat.cast_le (K := ℝ)).mpr (hδ 0)
    push_cast [cast_κℚ] at hcast
    linarith [(norm_nonneg _).trans hsu0]
  have be' : Local.Bε Qi poly.vertices.v p_ ε δ r :=
    bε_bridge hpoly Qi hp.θ₂Bound hp.φ₂Bound hεℝ hr hδ_pos be
  -- Apply local_theorem
  exact Local.local_theorem poly p_ ε
    { Pi := Pi, Qi := Qi, cong_tri := cong_tri, δ := δ, r := r,
      hr := Rat.cast_pos.mpr hr,
      hr₁ := hr₁', hδ := hδ', ae₁ := ae₁', ae₂ := ae₂',
      span₁ := span₁', span₂ := span₂', be := be' }

end LocalTheorem
end RationalApprox
end
