module

public import Noperthedron.Nopert214.FundamentalDomain
public import Noperthedron.Nopert214.AtlasQuadratic
public import Noperthedron.Nopert214.QuadraticBernstein

@[expose] public section

/-!
# Checked fivefold fundamental-domain pruning

The two adjacent nontrivial fivefold rotations suffice to reject points
outside the identity max-trace cell.  After clearing the positive Cayley
denominator, each trace advantage is quadratic.  We evaluate a rational
approximation to that quadratic and reserve a fixed `2/125` error allowance
for the two trigonometric coefficients.
-/

namespace Noperthedron.Nopert214.AtlasFundamentalPrune

open scoped Matrix
open Noperthedron.Checker
open CayleyAtlas

inductive Direction where
  | negative
  | positive
deriving DecidableEq, Repr

def Direction.signQ : Direction → ℚ
  | .negative => -1
  | .positive => 1

def Direction.symmetryIndex : Direction → OrbitIndex
  | .negative => 4
  | .positive => 1

/-- Denominator-cleared `R00 + R11`. -/
def aQuadratic (chart : ChartIndex) : RatQuadratic3 :=
  AtlasQuadratic.numeratorQuadratic chart 0 0 +
    AtlasQuadratic.numeratorQuadratic chart 1 1

/-- Denominator-cleared `R01 - R10`. -/
def bQuadratic (chart : ChartIndex) : RatQuadratic3 :=
  AtlasQuadratic.numeratorQuadratic chart 0 1 -
    AtlasQuadratic.numeratorQuadratic chart 1 0

/-- Rational trace-advantage approximation using `cos(2π/5) ≈ 309/1000`
and `sin(2π/5) ≈ 951/1000`. -/
def advantageQuadratic (chart : ChartIndex)
    (direction : Direction) : RatQuadratic3 :=
  RatQuadratic3.scale (-691 / 1000) (aQuadratic chart) +
    RatQuadratic3.scale (direction.signQ * (951 / 1000))
      (bQuadratic chart)

def approximationError : ℚ := 2 / 125

structure Box where
  interval : AtlasInterval ℚ
  chart : ChartIndex
  direction : Direction
deriving DecidableEq

def Box.variableBalls (box : Box) : Fin 3 → RatBall :=
  ![box.interval.coordinateBall 2,
    box.interval.coordinateBall 3,
    box.interval.coordinateBall 4]

def Box.tightLower (box : Box) : ℚ :=
  let ball := RatQuadratic3.evalTightBall box.variableBalls
    (advantageQuadratic box.chart box.direction)
  ball.center - ball.radius

def Box.lower (box : Box) : ℚ :=
  max box.tightLower
    (QuadraticBernstein.lower box.variableBalls
      (advantageQuadratic box.chart box.direction))

def Box.Valid (box : Box) : Prop := approximationError < box.lower

instance (box : Box) : Decidable box.Valid := by
  unfold Box.Valid
  infer_instance

private theorem cos_two_pi_div_five_bounds :
    |Real.cos (2 * Real.pi / 5) - (309 / 1000 : ℝ)| ≤ 1 / 1000 := by
  have hsqrt0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  have hsqrtLower : (2236 / 1000 : ℝ) ≤ Real.sqrt 5 := by
    nlinarith [sq_nonneg (Real.sqrt 5 - 2236 / 1000)]
  have hsqrtUpper : Real.sqrt 5 ≤ (22361 / 10000 : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt 5 - 22361 / 10000)]
  rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring,
    Real.cos_two_mul, Real.cos_pi_div_five]
  rw [abs_le]
  constructor <;> nlinarith

private theorem sin_two_pi_div_five_bounds :
    |Real.sin (2 * Real.pi / 5) - (951 / 1000 : ℝ)| ≤ 1 / 1000 := by
  have hangle0 : 0 < 2 * Real.pi / 5 := by positivity
  have hanglePi : 2 * Real.pi / 5 < Real.pi := by
    nlinarith [Real.pi_pos]
  have hsin0 : 0 < Real.sin (2 * Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi hangle0 hanglePi
  have hcosBounds := cos_two_pi_div_five_bounds
  rw [abs_le] at hcosBounds ⊢
  have htrig := Real.sin_sq_add_cos_sq (2 * Real.pi / 5)
  constructor <;> nlinarith [sq_nonneg
    (Real.sin (2 * Real.pi / 5) - 951 / 1000),
    sq_nonneg (Real.sin (2 * Real.pi / 5) - 952 / 1000)]

theorem eval_a_abs_le_eight (chart : ChartIndex) (x y z : ℝ)
    (hbounded : x ^ 2 + y ^ 2 + z ^ 2 ≤ 3) :
    |(aQuadratic chart).evalReal x y z| ≤ 8 := by
  fin_cases chart <;>
    simp [aQuadratic, AtlasQuadratic.eval_numeratorQuadratic,
      chartMatrix, cayleyNumeratorMatrix, Matrix.mul_apply,
      RatQuadratic3.evalReal_add] <;>
    rw [abs_le] <;>
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]

theorem eval_b_abs_le_eight (chart : ChartIndex) (x y z : ℝ)
    (hbounded : x ^ 2 + y ^ 2 + z ^ 2 ≤ 3) :
    |(bQuadratic chart).evalReal x y z| ≤ 8 := by
  fin_cases chart <;>
    simp [bQuadratic, AtlasQuadratic.eval_numeratorQuadratic,
      chartMatrix, cayleyNumeratorMatrix, Matrix.mul_apply,
      RatQuadratic3.evalReal_sub] <;>
    rw [abs_le] <;>
    constructor <;> nlinarith [sq_nonneg (x-y), sq_nonneg (x+y),
      sq_nonneg x, sq_nonneg y, sq_nonneg z]

noncomputable def exactAdvantage (chart : ChartIndex) (direction : Direction)
    (x y z : ℝ) : ℝ :=
  (Real.cos (2 * Real.pi / 5) - 1) *
      (aQuadratic chart).evalReal x y z +
    (direction.signQ : ℝ) * Real.sin (2 * Real.pi / 5) *
      (bQuadratic chart).evalReal x y z

theorem advantage_approximation_error (chart : ChartIndex)
    (direction : Direction) (x y z : ℝ)
    (hbounded : x ^ 2 + y ^ 2 + z ^ 2 ≤ 3) :
    |exactAdvantage chart direction x y z -
        (advantageQuadratic chart direction).evalReal x y z| ≤
      (approximationError : ℝ) := by
  have hc := cos_two_pi_div_five_bounds
  have hs := sin_two_pi_div_five_bounds
  have ha := eval_a_abs_le_eight chart x y z hbounded
  have hb := eval_b_abs_le_eight chart x y z hbounded
  have hsign : |(direction.signQ : ℝ)| = 1 := by
    cases direction <;> norm_num [Direction.signQ]
  simp only [exactAdvantage, advantageQuadratic,
    RatQuadratic3.evalReal_add, RatQuadratic3.evalReal_scale]
  push_cast
  rw [show
      (Real.cos (2 * Real.pi / 5) - 1) *
          (aQuadratic chart).evalReal x y z +
        (direction.signQ : ℝ) * Real.sin (2 * Real.pi / 5) *
          (bQuadratic chart).evalReal x y z -
        ((-691 / 1000 : ℝ) * (aQuadratic chart).evalReal x y z +
          ((direction.signQ : ℝ) * (951 / 1000 : ℝ)) *
            (bQuadratic chart).evalReal x y z) =
      (Real.cos (2 * Real.pi / 5) - 309 / 1000) *
          (aQuadratic chart).evalReal x y z +
        (direction.signQ : ℝ) *
          (Real.sin (2 * Real.pi / 5) - 951 / 1000) *
            (bQuadratic chart).evalReal x y z by ring]
  calc
    _ ≤ |(Real.cos (2 * Real.pi / 5) - 309 / 1000) *
          (aQuadratic chart).evalReal x y z| +
        |(direction.signQ : ℝ) *
          (Real.sin (2 * Real.pi / 5) - 951 / 1000) *
            (bQuadratic chart).evalReal x y z| := abs_add_le _ _
    _ = |Real.cos (2 * Real.pi / 5) - 309 / 1000| *
          |(aQuadratic chart).evalReal x y z| +
        |(direction.signQ : ℝ)| *
          |Real.sin (2 * Real.pi / 5) - 951 / 1000| *
            |(bQuadratic chart).evalReal x y z| := by
      rw [abs_mul, abs_mul, abs_mul]
    _ ≤ (approximationError : ℝ) := by
      have hca :
          |Real.cos (2 * Real.pi / 5) - 309 / 1000| *
              |(aQuadratic chart).evalReal x y z| ≤
            (1 / 1000 : ℝ) * 8 :=
        mul_le_mul hc ha (abs_nonneg _) (by norm_num)
      have hsb :
          |Real.sin (2 * Real.pi / 5) - 951 / 1000| *
              |(bQuadratic chart).evalReal x y z| ≤
            (1 / 1000 : ℝ) * 8 :=
        mul_le_mul hs hb (abs_nonneg _) (by norm_num)
      rw [hsign]
      norm_num [approximationError]
      linarith

theorem Box.lower_le_eval (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    (box.lower : ℝ) ≤
      (advantageQuadratic box.chart box.direction).evalReal p.x p.y p.z := by
  have hvars : ∀ i : Fin 3,
      (box.variableBalls i).Holds (![p.x, p.y, p.z] i) := by
    intro i
    fin_cases i
    · exact box.interval.coordinateBall_holds hp 2
    · exact box.interval.coordinateBall_holds hp 3
    · exact box.interval.coordinateBall_holds hp 4
  have htight := RatBall.lower_le_of_holds
    (RatQuadratic3.evalTightBall_holds hvars
      (advantageQuadratic box.chart box.direction))
  have hbernstein := QuadraticBernstein.lower_le_evalReal hvars
    (advantageQuadratic box.chart box.direction)
  push_cast at htight hbernstein
  unfold Box.lower Box.tightLower
  push_cast
  exact max_le htight hbernstein

theorem eval_a_eq_denom_mul (chart : ChartIndex) (x y z : ℝ) :
    (aQuadratic chart).evalReal x y z =
      cayleyDenom x y z *
        ((chartMatrix chart * cayleyMatrix x y z) 0 0 +
          (chartMatrix chart * cayleyMatrix x y z) 1 1) := by
  have hmatrix :
      chartMatrix chart * cayleyNumeratorMatrix x y z =
        cayleyDenom x y z • (chartMatrix chart * cayleyMatrix x y z) := by
    rw [cayleyNumeratorMatrix_eq_denom_smul, Matrix.mul_smul]
  simp only [aQuadratic, RatQuadratic3.evalReal_add,
    AtlasQuadratic.eval_numeratorQuadratic]
  rw [hmatrix]
  simp [mul_add]

theorem eval_b_eq_denom_mul (chart : ChartIndex) (x y z : ℝ) :
    (bQuadratic chart).evalReal x y z =
      cayleyDenom x y z *
        ((chartMatrix chart * cayleyMatrix x y z) 0 1 -
          (chartMatrix chart * cayleyMatrix x y z) 1 0) := by
  have hmatrix :
      chartMatrix chart * cayleyNumeratorMatrix x y z =
        cayleyDenom x y z • (chartMatrix chart * cayleyMatrix x y z) := by
    rw [cayleyNumeratorMatrix_eq_denom_smul, Matrix.mul_smul]
  simp only [bQuadratic, RatQuadratic3.evalReal_sub,
    AtlasQuadratic.eval_numeratorQuadratic]
  rw [hmatrix]
  simp [mul_sub]

theorem trace_mul_Rz_sub (R : Matrix (Fin 3) (Fin 3) ℝ) (angle : ℝ) :
    Matrix.trace (R * Rz_mat angle) - Matrix.trace R =
      (Real.cos angle - 1) * (R 0 0 + R 1 1) +
        Real.sin angle * (R 0 1 - R 1 0) := by
  simp [Matrix.trace, Matrix.mul_apply, Rz_mat, Fin.sum_univ_three]
  ring

theorem fivefoldMatrix_direction (direction : Direction) :
    fivefoldMatrix direction.symmetryIndex =
      Rz_mat ((direction.signQ : ℝ) * (2 * Real.pi / 5)) := by
  cases direction
  · simp only [Direction.symmetryIndex, Direction.signQ]
    rw [fivefoldMatrix]
    have hangle : ((4 : OrbitIndex) : ℝ) * (2 * Real.pi / 5) =
        (-1 : ℝ) * (2 * Real.pi / 5) + (1 : ℤ) * (2 * Real.pi) := by
      norm_num
      ring
    rw [hangle, Rz_mat_add_int_mul_two_pi]
    norm_num
  · simp [Direction.symmetryIndex, Direction.signQ, fivefoldMatrix]

theorem trace_advantage_eq (chart : ChartIndex) (direction : Direction)
    (x y z : ℝ) :
    Matrix.trace ((chartMatrix chart * cayleyMatrix x y z) *
        fivefoldMatrix direction.symmetryIndex) -
        Matrix.trace (chartMatrix chart * cayleyMatrix x y z) =
      exactAdvantage chart direction x y z / cayleyDenom x y z := by
  rw [fivefoldMatrix_direction, trace_mul_Rz_sub]
  rw [exactAdvantage, eval_a_eq_denom_mul, eval_b_eq_denom_mul]
  cases direction <;>
    simp [Direction.signQ, Real.cos_neg, Real.sin_neg] <;>
    field_simp [cayleyDenom_ne] <;> ring

theorem positive_exactAdvantage_not_inFundamentalDomain
    {chart : ChartIndex} {direction : Direction} {x y z : ℝ}
    (hpositive : 0 < exactAdvantage chart direction x y z) :
    ¬ InFivefoldFundamentalDomain
      (chartMatrix chart * cayleyMatrix x y z) := by
  intro hfund
  have htrace : 0 <
      Matrix.trace ((chartMatrix chart * cayleyMatrix x y z) *
          fivefoldMatrix direction.symmetryIndex) -
        Matrix.trace (chartMatrix chart * cayleyMatrix x y z) := by
    rw [trace_advantage_eq]
    exact div_pos hpositive (cayleyDenom_pos x y z)
  have hle := hfund direction.symmetryIndex
  linarith

theorem Box.valid_imp_not_inFundamentalDomain
    (box : Box) (hvalid : box.Valid) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) (hbounded : p.CayleyBounded) :
    ¬ InFivefoldFundamentalDomain
      (chartMatrix box.chart * cayleyMatrix p.x p.y p.z) := by
  have hlower := box.lower_le_eval hp
  have herr := advantage_approximation_error box.chart box.direction
    p.x p.y p.z hbounded
  have hpositive : 0 < exactAdvantage box.chart box.direction p.x p.y p.z := by
    have hvalidQ : (2 / 125 : ℚ) < box.lower := by
      simpa [Box.Valid, approximationError] using hvalid
    have hvalidReal : (2 / 125 : ℝ) < (box.lower : ℝ) := by
      have hcast := (Rat.cast_lt (K := ℝ)).2 hvalidQ
      norm_num at hcast ⊢
      exact hcast
    rw [abs_le] at herr
    norm_num [approximationError] at herr
    linarith
  exact positive_exactAdvantage_not_inFundamentalDomain hpositive

/-- Fundamental-domain condition carried by an atlas representative. -/
def _root_.Noperthedron.Nopert214.AtlasPose.InFivefoldFundamentalDomain
    (p : AtlasPose ℝ) (chart : ChartIndex) : Prop :=
  Noperthedron.Nopert214.InFivefoldFundamentalDomain
    (chartMatrix chart * cayleyMatrix p.x p.y p.z)

@[simp] theorem AtlasPose.matrixPoseWithOffset_inFundamentalDomain_iff
    (p : AtlasPose ℝ) (chart : ChartIndex) (offset : ℝ²) :
    (p.matrixPoseWithOffset chart offset).InNopert214FundamentalDomain ↔
      p.InFivefoldFundamentalDomain chart := by
  rw [MatrixPose.InNopert214FundamentalDomain,
    AtlasPose.InFivefoldFundamentalDomain,
    AtlasPose.matrixPoseWithOffset_relativeRotation]

theorem matrixPoseWithOffset_ofPose_eq_rightSymmetry
    (euler : Pose ℝ) (offset : ℝ²) (k : OrbitIndex)
    (chart : ChartIndex) (x y z : ℝ)
    (hrelative :
      (euler.matrixPoseWithOffset offset).relativeRotation *
          fivefoldMatrix k =
        chartMatrix chart * cayleyMatrix x y z) :
    (AtlasPose.ofPose euler x y z).matrixPoseWithOffset chart offset =
      (euler.matrixPoseWithOffset offset).rightNopert214Symmetry k := by
  let oldPose := euler.matrixPoseWithOffset offset
  let reduced := oldPose.rightNopert214Symmetry k
  have hrelative' : reduced.relativeRotation =
      chartMatrix chart * cayleyMatrix x y z := by
    rw [Noperthedron.Nopert214.MatrixPose.relativeRotation_rightNopert214Symmetry]
    exact hrelative
  apply matrixPose_ext_val
  · calc
      ((AtlasPose.ofPose euler x y z).matrixPoseWithOffset chart offset).innerRot.val =
          oldPose.outerRot.val *
            (chartMatrix chart * cayleyMatrix x y z) := by
              change (rotRM_mat euler.θ₂ euler.φ₂ 0 *
                  chartMatrix chart) * cayleyMatrix x y z =
                rotRM_mat euler.θ₂ euler.φ₂ 0 *
                  (chartMatrix chart * cayleyMatrix x y z)
              rw [Matrix.mul_assoc]
      _ = reduced.outerRot.val * reduced.relativeRotation := by
            rw [hrelative']
            rfl
      _ = reduced.innerRot.val :=
            Noperthedron.SnubCube.MatrixPose.outer_mul_relativeRotation
              reduced
  · rfl
  · rfl

/-- Every matrix pose has an equivalent bounded atlas representative in the
fivefold relative-rotation Dirichlet cell. -/
theorem exists_fundamental_atlas_translated_pose (p : MatrixPose) :
    ∃ δ : ℝ, ∃ chart : ChartIndex, ∃ q : AtlasPose ℝ, ∃ offset : ℝ²,
      q ∈ AtlasPose.rootInterval ℝ ∧ q.CayleyBounded ∧ q.InViewWedge ∧
      q.InFivefoldFundamentalDomain chart ∧
      (RupertPose (q.matrixPoseWithOffset chart offset)
          exactPolyhedron.hull ↔
        RupertPose (p.rotateBy δ) exactPolyhedron.hull) := by
  obtain ⟨δ, euler, offset, heuler, hview, heq⟩ :=
    exists_tight_translated_pose p
  let oldPose := euler.matrixPoseWithOffset offset
  obtain ⟨k, hkfund⟩ :=
    Noperthedron.Nopert214.MatrixPose.exists_rightNopert214Symmetry_inFundamentalDomain
      oldPose
  let reduced := oldPose.rightNopert214Symmetry k
  obtain ⟨chart, x, hx, y, hy, z, hz, hradius, hrelative⟩ :=
    exists_bounded_chart_cayley reduced.relativeRotation
      (Noperthedron.SnubCube.MatrixPose.relativeRotation_mem_SO3 reduced)
  let q := AtlasPose.ofPose euler x y z
  have hq : q ∈ AtlasPose.rootInterval ℝ :=
    AtlasPose.ofPose_mem_root euler x y z heuler.1 hx hy hz
  have hmatrix : q.matrixPoseWithOffset chart offset = reduced := by
    apply matrixPoseWithOffset_ofPose_eq_rightSymmetry
    rw [← Noperthedron.Nopert214.MatrixPose.relativeRotation_rightNopert214Symmetry]
    exact hrelative
  have hqfund : q.InFivefoldFundamentalDomain chart := by
    rw [← AtlasPose.matrixPoseWithOffset_inFundamentalDomain_iff
      q chart offset, hmatrix]
    exact hkfund
  refine ⟨δ, chart, q, offset, hq, hradius, ?_, hqfund, ?_⟩
  · simpa [q, AtlasPose.InViewWedge, AtlasPose.ofPose, InViewWedge]
      using hview
  · rw [hmatrix, RupertPose_rightNopert214Symmetry_iff]
    exact heq

end Noperthedron.Nopert214.AtlasFundamentalPrune

end
