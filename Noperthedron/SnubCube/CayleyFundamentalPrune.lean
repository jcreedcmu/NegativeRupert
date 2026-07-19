module

public import Noperthedron.Checker.RatPolynomial
public import Noperthedron.SnubCube.CayleyInterval

@[expose] public section


/-!
# Polynomial fundamental-domain pruning in Cayley coordinates

Multiplying the max-trace inequalities by the positive Cayley denominator
turns every one into a quadratic polynomial.  A pruning row evaluates one
such polynomial with rational center-radius arithmetic and proves it is
strictly positive throughout its box.
-/

namespace Noperthedron.SnubCube.CayleyFundamentalPrune

open scoped Matrix
open Noperthedron.Checker

abbrev Polynomial := RatPolynomial 3

def px : Polynomial := .var 0
def py : Polynomial := .var 1
def pz : Polynomial := .var 2

/-- The polynomial numerator of the Cayley matrix. -/
def numeratorPolynomial : Matrix (Fin 3) (Fin 3) Polynomial :=
  !![1 + px * px - py * py - pz * pz,
      2 * (px * py - pz),
      2 * (px * pz + py);
     2 * (px * py + pz),
      1 - px * px + py * py - pz * pz,
      2 * (py * pz - px);
     2 * (px * pz - py),
      2 * (py * pz + px),
      1 - px * px - py * py + pz * pz]

def sum3 (f : Fin 3 → Polynomial) : Polynomial :=
  f 0 + f 1 + f 2

def symmetryDifferenceQ (g : VertexIndex) (i j : Fin 3) : ℚ :=
  (symmetryMatrixInt g i j : ℚ) - if i = j then 1 else 0

/-- Numerator of `trace (Cayley(x,y,z) * (g - I))`. -/
def advantagePolynomial (g : VertexIndex) : Polynomial :=
  sum3 fun i => sum3 fun j =>
    RatPolynomial.scale (symmetryDifferenceQ g j i)
      (numeratorPolynomial i j)

private theorem eval_numeratorPolynomial (x y z : ℝ) (i j : Fin 3) :
    RatPolynomial.evalReal ![x, y, z] (numeratorPolynomial i j) =
      cayleyNumeratorMatrix x y z i j := by
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals
    norm_num [numeratorPolynomial, px, py, pz,
      RatPolynomial.evalReal, cayleyNumeratorMatrix]
  all_goals simp

theorem eval_advantagePolynomial (x y z : ℝ) (g : VertexIndex) :
    RatPolynomial.evalReal ![x, y, z] (advantagePolynomial g) =
      Matrix.trace
        (cayleyNumeratorMatrix x y z * (symmetryMatrix g - 1)) := by
  simp only [advantagePolynomial, sum3, RatPolynomial.evalReal_add,
    RatPolynomial.evalReal_scale, eval_numeratorPolynomial]
  simp [symmetryDifferenceQ, symmetryMatrix, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem trace_cayley_symmetryDifference (x y z : ℝ) (g : VertexIndex) :
    Matrix.trace (cayleyMatrix x y z * (symmetryMatrix g - 1)) =
      RatPolynomial.evalReal ![x, y, z] (advantagePolynomial g) /
        cayleyDenom x y z := by
  rw [eval_advantagePolynomial]
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Fin.sum_univ_three, cayleyMatrix_eq_div_numerator]
  field_simp [cayleyDenom_ne]

theorem positive_advantage_not_inFundamentalDomain
    {x y z : ℝ} {g : VertexIndex}
    (hpos : 0 < RatPolynomial.evalReal ![x, y, z]
      (advantagePolynomial g)) :
    ¬ InFundamentalDomain (cayleyMatrix x y z) := by
  intro hfund
  have htrace :
      0 < Matrix.trace
        (cayleyMatrix x y z * (symmetryMatrix g - 1)) := by
    rw [trace_cayley_symmetryDifference]
    exact div_pos hpos (cayleyDenom_pos x y z)
  have hg := hfund g
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub] at htrace
  linarith

structure Box where
  interval : CayleyInterval ℚ
  symmetryIndex : VertexIndex
deriving DecidableEq

def Box.variableBalls (box : Box) : Fin 3 → RatBall :=
  ![box.interval.coordinateBall 2,
    box.interval.coordinateBall 3,
    box.interval.coordinateBall 4]

def Box.advantageBall (box : Box) : RatBall :=
  RatPolynomial.evalBall box.variableBalls
    (advantagePolynomial box.symmetryIndex)

def Box.Valid (box : Box) : Prop :=
  0 < box.advantageBall.center - box.advantageBall.radius

instance (box : Box) : Decidable box.Valid := by
  unfold Box.Valid
  infer_instance

theorem Box.valid_imp_not_inFundamentalDomain
    (box : Box) (h : box.Valid) {p : CayleyPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    ¬ InFundamentalDomain (cayleyMatrix p.x p.y p.z) := by
  have hvars : ∀ i : Fin 3,
      (box.variableBalls i).Holds (![p.x, p.y, p.z] i) := by
    intro i
    fin_cases i
    · exact box.interval.coordinateBall_holds hp 2
    · exact box.interval.coordinateBall_holds hp 3
    · exact box.interval.coordinateBall_holds hp 4
  have henclose := RatPolynomial.evalBall_holds hvars
    (advantagePolynomial box.symmetryIndex)
  have hpos := RatBall.pos_of_holds_of_lower_pos henclose h
  exact positive_advantage_not_inFundamentalDomain hpos

/-- Interval form consumed by a mixed Cayley solution tree. -/
theorem Box.valid_imp_no_fundamental_pose
    (box : Box) (h : box.Valid) :
    ¬ ∃ p ∈ box.interval.toReal, ∃ offset : ℝ²,
      (p.matrixPoseWithOffset offset).InSnubFundamentalDomain := by
  rintro ⟨p, hp, offset, hfund⟩
  have hnot := box.valid_imp_not_inFundamentalDomain h hp
  apply hnot
  simpa only [MatrixPose.InSnubFundamentalDomain,
    CayleyPose.matrixPoseWithOffset_relativeRotation] using hfund

end Noperthedron.SnubCube.CayleyFundamentalPrune

end
