module

public import Noperthedron.Checker.RatQuadratic3
public import Noperthedron.Checker.SqrtFixed
public import Noperthedron.SnubCube.ProjectiveEdgeCertificate
public import Noperthedron.SnubCube.ProjectiveLocalRigidity

@[expose] public section


/-!
# Rational projective local-rigidity certificates

Three moving support directions have weights linear in the normalized view,
so their first-variation vector is quadratic.  This file packages those
quadratics and evaluates them over rational projective triangles.  The final
checker combines four such triples into an axis-cover tetrahedron.
-/

namespace Noperthedron.SnubCube.ProjectiveLocalCertificate

open scoped RealInnerProductSpace
open Noperthedron.Checker
open Noperthedron.BalancedSupport
open CayleyEdgeCertificate ProjectiveView ProjectiveEdgeCertificate
open ProjectiveLocalRigidity

abbrev VectorQ := Fin 3 → ℚ

structure AxisCertificate where
  edgeStart : Fin 3 → VertexIndex
  edgeFinish : Fin 3 → VertexIndex
  supportIndex : Fin 3 → VertexIndex
  nonzeroWitness : Fin 3 → VertexIndex
  B : ℚ
deriving DecidableEq, Repr

structure Box where
  interval : CayleyInterval ℚ
  triangle : Triangle ℚ
  certificate : Fin 4 → AxisCertificate
  c : ℚ
  δ : ℚ
deriving DecidableEq

def AxisCertificate.edgeQ (cert : AxisCertificate) (i : Fin 3) : VectorQ :=
  normalizedRationalVertex (cert.edgeStart i) -
    normalizedRationalVertex (cert.edgeFinish i)

noncomputable def AxisCertificate.exactEdge
    (cert : AxisCertificate) (i : Fin 3) : ℝ³ :=
  normalizedExactVertex (cert.edgeStart i) -
    normalizedExactVertex (cert.edgeFinish i)

def AxisCertificate.weightCoefficient
    (cert : AxisCertificate) : Fin 3 → VectorQ := ![
  crossQ (cert.edgeQ 1) (cert.edgeQ 2),
  crossQ (cert.edgeQ 2) (cert.edgeQ 0),
  crossQ (cert.edgeQ 0) (cert.edgeQ 1)]

def linearPolynomial (coefficient : VectorQ) : RatQuadratic3 :=
  { c0 := 0, cx := coefficient 0, cy := coefficient 1,
    cz := coefficient 2, cxx := 0, cxy := 0, cxz := 0,
    cyy := 0, cyz := 0, czz := 0 }

/-- Product of two homogeneous linear forms. -/
def mulLinear (a b : VectorQ) : RatQuadratic3 :=
  { c0 := 0, cx := 0, cy := 0, cz := 0,
    cxx := a 0 * b 0,
    cxy := a 0 * b 1 + a 1 * b 0,
    cxz := a 0 * b 2 + a 2 * b 0,
    cyy := a 1 * b 1,
    cyz := a 1 * b 2 + a 2 * b 1,
    czz := a 2 * b 2 }

theorem evalReal_linearPolynomial (a : VectorQ) (n : Fin 3 → ℝ) :
    (linearPolynomial a).evalReal (n 0) (n 1) (n 2) =
      linearValue n (fun c => (a c : ℝ)) := by
  simp [linearPolynomial, RatQuadratic3.evalReal, linearValue]
  ring

theorem evalReal_mulLinear (a b : VectorQ) (n : Fin 3 → ℝ) :
    (mulLinear a b).evalReal (n 0) (n 1) (n 2) =
      linearValue n (fun c => (a c : ℝ)) *
        linearValue n (fun c => (b c : ℝ)) := by
  simp [mulLinear, RatQuadratic3.evalReal, linearValue]
  ring

/-- Coefficients of `cross(n, edge)` as a linear function of `n`. -/
def AxisCertificate.liftCoefficient (cert : AxisCertificate)
    (i coordinate : Fin 3) : VectorQ :=
  let edge := cert.edgeQ i
  match coordinate with
  | 0 => ![0, edge 2, -edge 1]
  | 1 => ![-edge 2, 0, edge 0]
  | 2 => ![edge 1, -edge 0, 0]

/-- Coefficients of `cross(vertex, cross(n, edge))`. -/
def AxisCertificate.crossLiftCoefficient (cert : AxisCertificate)
    (i coordinate : Fin 3) : VectorQ :=
  let vertex := normalizedRationalVertex (cert.supportIndex i)
  match coordinate with
  | 0 => vertex 1 • cert.liftCoefficient i 2 -
      vertex 2 • cert.liftCoefficient i 1
  | 1 => vertex 2 • cert.liftCoefficient i 0 -
      vertex 0 • cert.liftCoefficient i 2
  | 2 => vertex 0 • cert.liftCoefficient i 1 -
      vertex 1 • cert.liftCoefficient i 0

/-- Sum coefficients before interval evaluation, preserving cancellation
among all three contacts. -/
def AxisCertificate.variationPolynomial (cert : AxisCertificate)
    (coordinate : Fin 3) : RatQuadratic3 :=
  mulLinear (cert.weightCoefficient 0)
      (cert.crossLiftCoefficient 0 coordinate) +
    mulLinear (cert.weightCoefficient 1)
      (cert.crossLiftCoefficient 1 coordinate) +
    mulLinear (cert.weightCoefficient 2)
      (cert.crossLiftCoefficient 2 coordinate)

noncomputable def AxisCertificate.approxVariation
    (cert : AxisCertificate) (n : Fin 3 → ℝ) : ℝ³ :=
  ∑ i, linearValue n (fun c => (cert.weightCoefficient i c : ℝ)) •
    cross3 (toR3 (normalizedRationalVertex (cert.supportIndex i)))
      (cross3 (WithLp.toLp 2 n) (toR3 (cert.edgeQ i)))

theorem AxisCertificate.eval_variationPolynomial (cert : AxisCertificate)
    (n : Fin 3 → ℝ) (coordinate : Fin 3) :
    (cert.variationPolynomial coordinate).evalReal (n 0) (n 1) (n 2) =
      cert.approxVariation n coordinate := by
  fin_cases coordinate <;>
    simp [AxisCertificate.variationPolynomial,
      AxisCertificate.approxVariation, Fin.sum_univ_three,
      evalReal_mulLinear, AxisCertificate.weightCoefficient,
      AxisCertificate.crossLiftCoefficient,
      AxisCertificate.liftCoefficient, crossQ, cross3, cross_apply,
      toR3, linearValue] <;> ring

def Box.triangleBalls (box : Box) (coordinate : Fin 3) : RatBall :=
  RatBall.ofEndpoints
    (min3 fun j => box.triangle j coordinate)
    (max3 fun j => box.triangle j coordinate)

def Box.variationBall (box : Box) (j : Fin 4)
    (coordinate : Fin 3) : RatBall :=
  RatQuadratic3.evalBall box.triangleBalls
    ((box.certificate j).variationPolynomial coordinate)

def unitCoordinate (coordinate : Fin 3) : Fin 3 → ℝ :=
  fun c => if c = coordinate then 1 else 0

@[simp] theorem linearValue_unitCoordinate (n : Fin 3 → ℝ)
    (coordinate : Fin 3) :
    linearValue n (unitCoordinate coordinate) = n coordinate := by
  fin_cases coordinate <;> simp [linearValue, unitCoordinate]

theorem coordinate_mem_triangleBounds {triangle : Triangle ℚ}
    {n : Fin 3 → ℝ} (hmem : InTriangle (toReal triangle) n)
    (coordinate : Fin 3) :
    n coordinate ∈ Set.Icc
      ((min3 (fun j => triangle j coordinate) : ℚ) : ℝ)
      ((max3 (fun j => triangle j coordinate) : ℚ) : ℝ) := by
  constructor
  · rw [← linearValue_unitCoordinate n coordinate]
    apply le_linearValue_of_mem hmem
    intro j
    have hmin := min3_le (fun j => triangle j coordinate) j
    rw [linearValue_unitCoordinate]
    change ((min3 (fun j => triangle j coordinate) : ℚ) : ℝ) ≤
      (triangle j coordinate : ℝ)
    exact_mod_cast hmin
  · rw [← linearValue_unitCoordinate n coordinate]
    apply linearValue_le_of_mem hmem
    intro j
    have hmax := le_max3 (fun j => triangle j coordinate) j
    rw [linearValue_unitCoordinate]
    change (triangle j coordinate : ℝ) ≤
      ((max3 (fun j => triangle j coordinate) : ℚ) : ℝ)
    exact_mod_cast hmax

theorem Box.triangleBalls_holds (box : Box) {n : Fin 3 → ℝ}
    (hmem : InTriangle (toReal box.triangle) n) (coordinate : Fin 3) :
    (box.triangleBalls coordinate).Holds (n coordinate) := by
  apply RatBall.holds_of_mem_Icc
  exact coordinate_mem_triangleBounds hmem coordinate

theorem Box.variationBall_holds (box : Box) {n : Fin 3 → ℝ}
    (hmem : InTriangle (toReal box.triangle) n)
    (j : Fin 4) (coordinate : Fin 3) :
    (box.variationBall j coordinate).Holds
      ((box.certificate j).approxVariation n coordinate) := by
  have hvars : ∀ i, (box.triangleBalls i).Holds
      (![n 0, n 1, n 2] i) := by
    intro i
    fin_cases i
    · simpa using box.triangleBalls_holds hmem 0
    · simpa using box.triangleBalls_holds hmem 1
    · simpa using box.triangleBalls_holds hmem 2
  have hball := RatQuadratic3.evalBall_holds
    hvars
    ((box.certificate j).variationPolynomial coordinate)
  rw [(box.certificate j).eval_variationPolynomial n coordinate] at hball
  exact hball

noncomputable def normalizedView3 (p : CayleyPose ℝ) : ℝ³ :=
  WithLp.toLp 2 (normalizedView p)

theorem normalizedView3_eq (p : CayleyPose ℝ)
    (hsum : viewSum p ≠ 0) :
    normalizedView3 p = (viewSum p)⁻¹ • viewVector p := by
  ext coordinate
  fin_cases coordinate <;>
    simp [normalizedView3, normalizedView, smul_eq_mul] <;>
    field_simp [hsum]

theorem normalizedView3_norm_le_one {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber) :
    ‖normalizedView3 p‖ ≤ 1 := by
  have hsumPos := viewSum_pos hchamber
  rw [normalizedView3_eq p hsumPos.ne', norm_smul, viewVector_norm]
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hsumPos, mul_one]
  exact inv_le_one_of_one_le₀ (one_le_viewSum hchamber)

noncomputable def AxisCertificate.approxEdge
    (cert : AxisCertificate) (i : Fin 3) : ℝ³ :=
  toR3 (cert.edgeQ i)

theorem AxisCertificate.approxEdge_eq (cert : AxisCertificate) (i : Fin 3) :
    cert.approxEdge i =
      toR3 (normalizedRationalVertex (cert.edgeStart i)) -
        toR3 (normalizedRationalVertex (cert.edgeFinish i)) := by
  ext coordinate
  simp [AxisCertificate.approxEdge, AxisCertificate.edgeQ, toR3]

theorem AxisCertificate.exactEdge_norm_le_two
    (cert : AxisCertificate) (i : Fin 3) :
    ‖cert.exactEdge i‖ ≤ 2 := by
  unfold AxisCertificate.exactEdge
  exact (norm_sub_le _ _).trans (by
    linarith [normalizedExactVertex_norm_le_one (cert.edgeStart i),
      normalizedExactVertex_norm_le_one (cert.edgeFinish i)])

theorem AxisCertificate.approxEdge_norm_le
    (cert : AxisCertificate) (i : Fin 3) :
    ‖cert.approxEdge i‖ ≤ 2 * (1 + RationalApprox.κ) := by
  rw [cert.approxEdge_eq]
  exact (norm_sub_le _ _).trans (by
    linarith [CayleyGlobalCertificate.norm_normalizedRationalVertex_le
        (cert.edgeStart i),
      CayleyGlobalCertificate.norm_normalizedRationalVertex_le
        (cert.edgeFinish i)])

theorem AxisCertificate.exactEdge_sub_approx_norm_le
    (cert : AxisCertificate) (i : Fin 3) :
    ‖cert.exactEdge i - cert.approxEdge i‖ ≤ 2 * RationalApprox.κ := by
  rw [cert.approxEdge_eq]
  have hrearrange :
      cert.exactEdge i -
          (toR3 (normalizedRationalVertex (cert.edgeStart i)) -
            toR3 (normalizedRationalVertex (cert.edgeFinish i))) =
        (normalizedExactVertex (cert.edgeStart i) -
            toR3 (normalizedRationalVertex (cert.edgeStart i))) -
          (normalizedExactVertex (cert.edgeFinish i) -
            toR3 (normalizedRationalVertex (cert.edgeFinish i))) := by
    unfold AxisCertificate.exactEdge
    abel
  rw [hrearrange]
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ RationalApprox.κ + RationalApprox.κ := add_le_add
      (normalizedApproximation.approx (cert.edgeStart i))
      (normalizedApproximation.approx (cert.edgeFinish i))
    _ = 2 * RationalApprox.κ := by ring

noncomputable def AxisCertificate.approxWeight
    (cert : AxisCertificate) (n : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  linearValue n (fun coordinate => (cert.weightCoefficient i coordinate : ℝ))

noncomputable def AxisCertificate.approxWeightVector
    (cert : AxisCertificate) (i : Fin 3) : ℝ³ :=
  toR3 (cert.weightCoefficient i)

theorem AxisCertificate.approxWeightVector_eq (cert : AxisCertificate)
    (i : Fin 3) :
    cert.approxWeightVector i = match i with
      | 0 => cross3 (cert.approxEdge 1) (cert.approxEdge 2)
      | 1 => cross3 (cert.approxEdge 2) (cert.approxEdge 0)
      | 2 => cross3 (cert.approxEdge 0) (cert.approxEdge 1) := by
  fin_cases i <;>
    simp [AxisCertificate.approxWeightVector,
      AxisCertificate.weightCoefficient, AxisCertificate.approxEdge,
      toR3_crossQ]

theorem AxisCertificate.approxWeight_eq_inner (cert : AxisCertificate)
    (n : Fin 3 → ℝ) (i : Fin 3) :
    cert.approxWeight n i =
      ⟪WithLp.toLp 2 n, cert.approxWeightVector i⟫ := by
  simp [AxisCertificate.approxWeight, AxisCertificate.approxWeightVector,
    linearValue, PiLp.inner_apply, Fin.sum_univ_three, toR3]
  ring

theorem AxisCertificate.crossEdge_error (cert : AxisCertificate)
    (i j : Fin 3) :
    ‖cross3 (cert.exactEdge i) (cert.exactEdge j) -
        cross3 (cert.approxEdge i) (cert.approxEdge j)‖ ≤
      10 * RationalApprox.κ := by
  have hdecomp :
      cross3 (cert.exactEdge i) (cert.exactEdge j) -
          cross3 (cert.approxEdge i) (cert.approxEdge j) =
        cross3 (cert.exactEdge i - cert.approxEdge i)
            (cert.exactEdge j) +
          cross3 (cert.approxEdge i)
            (cert.exactEdge j - cert.approxEdge j) := by
    ext coordinate
    fin_cases coordinate <;> simp [cross3, cross_apply] <;> ring
  rw [hdecomp]
  calc
    _ ≤ ‖cross3 (cert.exactEdge i - cert.approxEdge i)
          (cert.exactEdge j)‖ +
        ‖cross3 (cert.approxEdge i)
          (cert.exactEdge j - cert.approxEdge j)‖ := norm_add_le _ _
    _ ≤ (2 * RationalApprox.κ) * 2 +
        (2 * (1 + RationalApprox.κ)) *
          (2 * RationalApprox.κ) := by
      exact add_le_add
        ((cross3_norm_le _ _).trans (mul_le_mul
          (cert.exactEdge_sub_approx_norm_le i)
          (cert.exactEdge_norm_le_two j) (norm_nonneg _)
          (by norm_num [RationalApprox.κ])))
        ((cross3_norm_le _ _).trans (mul_le_mul
          (cert.approxEdge_norm_le i)
          (cert.exactEdge_sub_approx_norm_le j) (norm_nonneg _)
          (by norm_num [RationalApprox.κ])))
    _ ≤ 10 * RationalApprox.κ := by
      norm_num [RationalApprox.κ]

noncomputable def AxisCertificate.exactWeight (cert : AxisCertificate)
    (p : CayleyPose ℝ) (i : Fin 3) : ℝ :=
  ProjectiveLocalRigidity.weight p (fun j => cert.exactEdge j) i

theorem linearValue_eq_inner_toLp (n : Fin 3 → ℝ) (v : ℝ³) :
    linearValue n v = inner ℝ (WithLp.toLp 2 n) v := by
  simp [linearValue, PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem AxisCertificate.exactWeight_sub_approx_abs_le
    (cert : AxisCertificate) {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (i : Fin 3) :
    |cert.exactWeight p i - cert.approxWeight (normalizedView p) i| ≤
      10 * RationalApprox.κ := by
  have hn := normalizedView3_norm_le_one hchamber
  fin_cases i
  · simp [AxisCertificate.exactWeight,
      ProjectiveLocalRigidity.weight]
    rw [linearValue_eq_inner_toLp, cert.approxWeight_eq_inner,
      cert.approxWeightVector_eq]
    change |⟪normalizedView3 p,
      cross3 (cert.exactEdge 1) (cert.exactEdge 2)⟫ -
        ⟪normalizedView3 p,
          cross3 (cert.approxEdge 1) (cert.approxEdge 2)⟫| ≤ _
    rw [← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left (cert.crossEdge_error 1 2)
        (norm_nonneg _)).trans
          (mul_le_of_le_one_left
            (by norm_num [RationalApprox.κ]) hn))
  · simp [AxisCertificate.exactWeight,
      ProjectiveLocalRigidity.weight]
    rw [linearValue_eq_inner_toLp, cert.approxWeight_eq_inner,
      cert.approxWeightVector_eq]
    change |⟪normalizedView3 p,
      cross3 (cert.exactEdge 2) (cert.exactEdge 0)⟫ -
        ⟪normalizedView3 p,
          cross3 (cert.approxEdge 2) (cert.approxEdge 0)⟫| ≤ _
    rw [← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left (cert.crossEdge_error 2 0)
        (norm_nonneg _)).trans
          (mul_le_of_le_one_left
            (by norm_num [RationalApprox.κ]) hn))
  · simp [AxisCertificate.exactWeight,
      ProjectiveLocalRigidity.weight]
    rw [linearValue_eq_inner_toLp, cert.approxWeight_eq_inner,
      cert.approxWeightVector_eq]
    change |⟪normalizedView3 p,
      cross3 (cert.exactEdge 0) (cert.exactEdge 1)⟫ -
        ⟪normalizedView3 p,
          cross3 (cert.approxEdge 0) (cert.approxEdge 1)⟫| ≤ _
    rw [← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left (cert.crossEdge_error 0 1)
        (norm_nonneg _)).trans
          (mul_le_of_le_one_left
            (by norm_num [RationalApprox.κ]) hn))

theorem AxisCertificate.exactWeight_abs_le_four
    (cert : AxisCertificate) {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (i : Fin 3) : |cert.exactWeight p i| ≤ 4 := by
  have hn := normalizedView3_norm_le_one hchamber
  fin_cases i
  all_goals
    simp [AxisCertificate.exactWeight,
      ProjectiveLocalRigidity.weight]
    rw [linearValue_eq_inner_toLp]
    change |⟪normalizedView3 p, cross3 _ _⟫| ≤ _ <;>
    apply (abs_real_inner_le_norm _ _).trans <;>
    apply (mul_le_mul hn (cross3_norm_le _ _) (norm_nonneg _) (by positivity)).trans <;>
    rw [one_mul]
    apply (mul_le_mul (cert.exactEdge_norm_le_two _)
      (cert.exactEdge_norm_le_two _) (norm_nonneg _) (by norm_num)).trans
    norm_num

theorem AxisCertificate.approxWeight_abs_le
    (cert : AxisCertificate) {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (i : Fin 3) :
    |cert.approxWeight (normalizedView p) i| ≤
      4 + 10 * RationalApprox.κ := by
  have herr := cert.exactWeight_sub_approx_abs_le hchamber i
  have hexact := cert.exactWeight_abs_le_four hchamber i
  calc
    _ ≤ |cert.exactWeight p i| +
        |cert.exactWeight p i -
          cert.approxWeight (normalizedView p) i| := by
      have htriangle := abs_add_le
        (cert.exactWeight p i)
        (cert.approxWeight (normalizedView p) i - cert.exactWeight p i)
      rw [add_sub_cancel] at htriangle
      simpa [abs_sub_comm] using htriangle
    _ ≤ 4 + 10 * RationalApprox.κ := add_le_add hexact herr

end Noperthedron.SnubCube.ProjectiveLocalCertificate

end
