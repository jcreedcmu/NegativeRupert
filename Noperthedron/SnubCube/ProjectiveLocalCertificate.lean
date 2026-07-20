module

public import Noperthedron.Checker.RatQuadratic3
public import Noperthedron.Checker.SqrtFixed
public import Noperthedron.SnubCube.LocalCertificate
public import Noperthedron.SnubCube.ProjectiveEdgeCertificate
public import Noperthedron.SnubCube.ProjectiveLocalRigidity
public import Noperthedron.SnubCube.ExactArithmetic

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

def AxisCertificate.deltaQ (cert : AxisCertificate) (i : Fin 3)
    (k : VertexIndex) : VectorQ :=
  normalizedRationalVertex k -
    normalizedRationalVertex (cert.supportIndex i)

noncomputable def AxisCertificate.exactDelta (cert : AxisCertificate)
    (i : Fin 3) (k : VertexIndex) : ℝ³ :=
  normalizedExactVertex k -
    normalizedExactVertex (cert.supportIndex i)

def Box.supportAt (box : Box) (j : Fin 4) (corner : Fin 3)
    (i : Fin 3) (k : VertexIndex) : ℚ :=
  dotQ (box.triangle corner)
    (crossQ ((box.certificate j).edgeQ i)
      ((box.certificate j).deltaQ i k))

def AxisCertificate.symbolicSupportCross (cert : AxisCertificate)
    (i : Fin 3) (k : VertexIndex) : Fin 3 → TribonacciExpr :=
  SnubCube.symbolicSupportCross (cert.edgeStart i) (cert.edgeFinish i)
    (cert.supportIndex i) k

def Box.symbolicSupportAt (box : Box) (j : Fin 4) (corner : Fin 3)
    (i : Fin 3) (k : VertexIndex) : TribonacciExpr :=
  Noperthedron.SnubCube.symbolicDotRat (box.triangle corner)
    ((box.certificate j).symbolicSupportCross i k)

/-- Exact algebraic support ties pay no decimal approximation error. -/
def Box.exactSupportZero (box : Box) (j : Fin 4) (i : Fin 3)
    (k : VertexIndex) : Prop :=
  ∀ corner, box.symbolicSupportAt j corner i k = 0

instance (box : Box) (j : Fin 4) (i : Fin 3) (k : VertexIndex) :
    Decidable (box.exactSupportZero j i k) := by
  unfold Box.exactSupportZero
  infer_instance

def Box.supportUpper (box : Box) (j : Fin 4) (i : Fin 3)
    (k : VertexIndex) : ℚ :=
  if box.exactSupportZero j i k then 0
  else
    max3 (fun corner => box.supportAt j corner i k) +
      CayleyEdgeCertificate.supportError

def Box.weightAt (box : Box) (j : Fin 4) (corner : Fin 3)
    (i : Fin 3) : ℚ :=
  dotQ (box.triangle corner)
    ((box.certificate j).weightCoefficient i)

def Box.weightLower (box : Box) (j : Fin 4) (i : Fin 3) : ℚ :=
  min3 (fun corner => box.weightAt j corner i) -
    CayleyEdgeCertificate.supportError

def Box.weightUpper (box : Box) (j : Fin 4) (i : Fin 3) : ℚ :=
  max3 (fun corner => box.weightAt j corner i) +
    CayleyEdgeCertificate.supportError

/-- Universal norm error between an exact three-contact projective
variation and its rational-vertex approximation. -/
def variationError : ℚ := 150 * RationalApprox.κℚ

def Box.approxNormalizedCenter (box : Box) (j : Fin 4) : VectorQ :=
  fun coordinate => (box.variationBall j coordinate).center /
    (box.certificate j).B

def Box.variationRadiusSum (box : Box) (j : Fin 4) : ℚ :=
  ∑ coordinate, (box.variationBall j coordinate).radius

def Box.weightBudget (box : Box) (j : Fin 4) : ℚ :=
  2 * ∑ i, box.weightUpper j i

def Box.octahedronTarget (box : Box) (k : Fin 6) : VectorQ :=
  (7 / 4 * (box.c + box.δ)) • LocalCertificate.octahedronAxis k

def Box.barycentric (box : Box) (k : Fin 6) : Fin 4 → ℚ :=
  LocalCertificate.tetraBarycentricQ box.approxNormalizedCenter
    (box.octahedronTarget k)

def Box.barycentricValid (box : Box) : Prop :=
  LocalCertificate.tetraDetQ box.approxNormalizedCenter ≠ 0 ∧
    ∀ k j, 0 ≤ box.barycentric k j

instance (box : Box) : Decidable box.barycentricValid := by
  unfold Box.barycentricValid
  infer_instance

/-- Geometry-free shell used to reuse the exact Cayley radius bound. -/
def Box.radiusShell (box : Box) : CayleyLocalCertificate.Box where
  interval := box.interval
  certificate := fun _ => { contact := fun _ => {
    index := VertexIndex.ofFin24 0
    direction := 0 } }
  c := box.c
  r := 0

abbrev Box.radiusSq (box : Box) : ℚ := box.radiusShell.radiusSq

@[mk_iff]
structure Box.Valid (box : Box) : Prop where
  triangle_valid : TriangleValid box.triangle
  c_nonneg : 0 ≤ box.c
  delta_nonneg : 0 ≤ box.δ
  B_pos : ∀ j, 0 < (box.certificate j).B
  weight_nonneg : ∀ j i, 0 ≤ box.weightLower j i
  weight_pos : ∀ j, ∃ i, 0 < box.weightLower j i
  support : ∀ j i k, box.supportUpper j i k ≤ 0
  direction_nonzero : ∀ j i,
    box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0
  budget : ∀ j, box.weightBudget j ≤ (box.certificate j).B
  variation : ∀ j,
    box.variationRadiusSum j + 3 * variationError ≤
      (box.certificate j).B * box.δ
  barycentric : box.barycentricValid
  radius : box.radiusSq ≤ box.c ^ 2

instance (box : Box) : Decidable box.Valid :=
  decidable_of_iff _ (Box.valid_iff box).symm

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

noncomputable def AxisCertificate.approxDelta (cert : AxisCertificate)
    (i : Fin 3) (k : VertexIndex) : ℝ³ :=
  toR3 (cert.deltaQ i k)

theorem AxisCertificate.approxDelta_eq (cert : AxisCertificate)
    (i : Fin 3) (k : VertexIndex) :
    cert.approxDelta i k =
      toR3 (normalizedRationalVertex k) -
        toR3 (normalizedRationalVertex (cert.supportIndex i)) := by
  ext coordinate
  simp [AxisCertificate.approxDelta, AxisCertificate.deltaQ, toR3]

theorem AxisCertificate.exactDelta_norm_le_two
    (cert : AxisCertificate) (i : Fin 3) (k : VertexIndex) :
    ‖cert.exactDelta i k‖ ≤ 2 := by
  unfold AxisCertificate.exactDelta
  exact (norm_sub_le _ _).trans (by
    linarith [normalizedExactVertex_norm_le_one k,
      normalizedExactVertex_norm_le_one (cert.supportIndex i)])

theorem AxisCertificate.exactDelta_sub_approx_norm_le
    (cert : AxisCertificate) (i : Fin 3) (k : VertexIndex) :
    ‖cert.exactDelta i k - cert.approxDelta i k‖ ≤
      2 * RationalApprox.κ := by
  rw [cert.approxDelta_eq]
  have hrearrange :
      cert.exactDelta i k -
          (toR3 (normalizedRationalVertex k) -
            toR3 (normalizedRationalVertex (cert.supportIndex i))) =
        (normalizedExactVertex k -
            toR3 (normalizedRationalVertex k)) -
          (normalizedExactVertex (cert.supportIndex i) -
            toR3 (normalizedRationalVertex (cert.supportIndex i))) := by
    unfold AxisCertificate.exactDelta
    abel
  rw [hrearrange]
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ RationalApprox.κ + RationalApprox.κ := add_le_add
      (normalizedApproximation.approx k)
      (normalizedApproximation.approx (cert.supportIndex i))
    _ = 2 * RationalApprox.κ := by ring

theorem AxisCertificate.supportCross_error (cert : AxisCertificate)
    (i : Fin 3) (k : VertexIndex) :
    ‖cross3 (cert.exactEdge i) (cert.exactDelta i k) -
        cross3 (cert.approxEdge i) (cert.approxDelta i k)‖ ≤
      10 * RationalApprox.κ := by
  have hdecomp :
      cross3 (cert.exactEdge i) (cert.exactDelta i k) -
          cross3 (cert.approxEdge i) (cert.approxDelta i k) =
        cross3 (cert.exactEdge i - cert.approxEdge i)
            (cert.exactDelta i k) +
          cross3 (cert.approxEdge i)
            (cert.exactDelta i k - cert.approxDelta i k) := by
    ext coordinate
    fin_cases coordinate <;> simp [cross3, cross_apply] <;> ring
  rw [hdecomp]
  calc
    _ ≤ ‖cross3 (cert.exactEdge i - cert.approxEdge i)
          (cert.exactDelta i k)‖ +
        ‖cross3 (cert.approxEdge i)
          (cert.exactDelta i k - cert.approxDelta i k)‖ := norm_add_le _ _
    _ ≤ (2 * RationalApprox.κ) * 2 +
        (2 * (1 + RationalApprox.κ)) *
          (2 * RationalApprox.κ) := by
      exact add_le_add
        ((cross3_norm_le _ _).trans (mul_le_mul
          (cert.exactEdge_sub_approx_norm_le i)
          (cert.exactDelta_norm_le_two i k) (norm_nonneg _)
          (by norm_num [RationalApprox.κ])))
        ((cross3_norm_le _ _).trans (mul_le_mul
          (cert.approxEdge_norm_le i)
          (cert.exactDelta_sub_approx_norm_le i k) (norm_nonneg _)
          (by norm_num [RationalApprox.κ])))
    _ ≤ 10 * RationalApprox.κ := by
      norm_num [RationalApprox.κ]

noncomputable def AxisCertificate.approxSupport
    (cert : AxisCertificate) (n : Fin 3 → ℝ)
    (i : Fin 3) (k : VertexIndex) : ℝ :=
  linearValue n
    (cross3 (cert.approxEdge i) (cert.approxDelta i k))

noncomputable def AxisCertificate.exactSupport
    (cert : AxisCertificate) (p : CayleyPose ℝ)
    (i : Fin 3) (k : VertexIndex) : ℝ :=
  linearValue (normalizedView p)
    (cross3 (cert.exactEdge i) (cert.exactDelta i k))

theorem Box.supportAt_cast (box : Box) (j : Fin 4)
    (corner : Fin 3) (i : Fin 3) (k : VertexIndex) :
    (box.supportAt j corner i k : ℝ) =
      (box.certificate j).approxSupport (toReal box.triangle corner) i k := by
  simp [Box.supportAt, AxisCertificate.approxSupport, dotQ,
    linearValue, ProjectiveView.toReal, AxisCertificate.approxEdge,
    AxisCertificate.approxDelta, CayleyEdgeCertificate.crossQ,
    cross3, cross_apply, toR3]

theorem Box.approxSupport_le_max (box : Box)
    {p : CayleyPose ℝ}
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) (i : Fin 3) (k : VertexIndex) :
    (box.certificate j).approxSupport (normalizedView p) i k ≤
      (max3 (fun corner => box.supportAt j corner i k) : ℝ) := by
  unfold AxisCertificate.approxSupport
  apply linearValue_le_of_mem hmem
  intro corner
  change (box.certificate j).approxSupport
    (toReal box.triangle corner) i k ≤ _
  rw [← box.supportAt_cast j corner i k]
  exact_mod_cast le_max3 (fun c => box.supportAt j c i k) corner

theorem AxisCertificate.exactSupport_sub_approx_abs_le
    (cert : AxisCertificate) {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (i : Fin 3) (k : VertexIndex) :
    |cert.exactSupport p i k -
        cert.approxSupport (normalizedView p) i k| ≤
      (CayleyEdgeCertificate.supportError : ℝ) := by
  rw [AxisCertificate.exactSupport, AxisCertificate.approxSupport,
    linearValue_eq_inner_toLp, linearValue_eq_inner_toLp,
    ← inner_sub_right]
  calc
    _ ≤ ‖normalizedView3 p‖ *
        ‖cross3 (cert.exactEdge i) (cert.exactDelta i k) -
          cross3 (cert.approxEdge i) (cert.approxDelta i k)‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ 10 * RationalApprox.κ := by
      exact (mul_le_mul_of_nonneg_left (cert.supportCross_error i k)
        (norm_nonneg _)).trans
          (mul_le_of_le_one_left
            (by norm_num [RationalApprox.κ])
            (normalizedView3_norm_le_one hchamber))
    _ = (CayleyEdgeCertificate.supportError : ℝ) := by
      norm_num [CayleyEdgeCertificate.supportError,
        RationalApprox.κ, RationalApprox.κℚ]

theorem Box.eval_symbolicSupportAt (box : Box) (j : Fin 4)
    (corner : Fin 3) (i : Fin 3) (k : VertexIndex) :
    TribonacciExpr.eval (box.symbolicSupportAt j corner i k) =
      linearValue (toReal box.triangle corner)
        (cross3 ((box.certificate j).exactEdge i)
          ((box.certificate j).exactDelta i k)) := by
  rw [Box.symbolicSupportAt,
    Noperthedron.SnubCube.eval_symbolicDotRat]
  apply congrArg (linearValue (toReal box.triangle corner))
  funext coordinate
  rw [AxisCertificate.symbolicSupportCross,
    Noperthedron.SnubCube.eval_symbolicSupportCross]
  rfl

theorem Box.exactSupport_eq_zero_of_symbolic (box : Box)
    {p : CayleyPose ℝ}
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) (i : Fin 3) (k : VertexIndex)
    (hzero : box.exactSupportZero j i k) :
    (box.certificate j).exactSupport p i k = 0 := by
  have hcorner (corner : Fin 3) :
      linearValue (toReal box.triangle corner)
        (cross3 ((box.certificate j).exactEdge i)
          ((box.certificate j).exactDelta i k)) = 0 := by
    rw [← box.eval_symbolicSupportAt j corner i k]
    exact TribonacciExpr.eval_eq_zero_of_eq_zero (hzero corner)
  have hle := linearValue_le_of_mem hmem (bound := 0)
    (fun corner => (hcorner corner).le)
  have hge := le_linearValue_of_mem hmem (bound := 0)
    (fun corner => (hcorner corner).ge)
  unfold AxisCertificate.exactSupport
  linarith

theorem Box.exactSupport_le_upper (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) (i : Fin 3) (k : VertexIndex) :
    (box.certificate j).exactSupport p i k ≤
      (box.supportUpper j i k : ℝ) := by
  by_cases hk : box.exactSupportZero j i k
  · have hzero := box.exactSupport_eq_zero_of_symbolic hmem j i k hk
    rw [hzero]
    simp [Box.supportUpper, hk]
  have happ := box.approxSupport_le_max hmem j i k
  have herr := (box.certificate j).exactSupport_sub_approx_abs_le
    hchamber i k
  rw [abs_le] at herr
  simp only [Box.supportUpper, if_neg hk]
  change _ ≤ ((max3 (fun corner => box.supportAt j corner i k) +
    CayleyEdgeCertificate.supportError : ℚ) : ℝ)
  push_cast
  linarith [herr.2]

theorem inner_direction_outerProjection_eq_support
    (p : CayleyPose ℝ) (offset : ℝ²) (edge delta : ℝ³)
    (hsum : viewSum p ≠ 0) :
    inner ℝ (direction p edge)
        (outerProjectionLinear (p.matrixPoseWithOffset offset) delta) =
      linearValue (normalizedView p) (cross3 edge delta) := by
  rw [direction, real_inner_smul_left]
  have hproj : outerProjectionLinear (p.matrixPoseWithOffset offset) delta =
      rotM p.θ p.φ delta := by
    simpa [outerProjectionLinear, ContinuousLinearMap.comp_apply] using
      p.matrixPoseWithOffset_outer_rotation_project offset delta
  rw [hproj, inner_quarterTurn_rotM_eq]
  simp [normalizedView, linearValue, Fin.sum_univ_three]
  field_simp [hsum]

theorem Box.valid_support (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (offset : ℝ²)
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) (i : Fin 3) (k : VertexIndex) :
    inner ℝ (direction p ((box.certificate j).exactEdge i))
        (outerProjectionLinear (p.matrixPoseWithOffset offset)
          (normalizedExactVertex k)) ≤
      inner ℝ (direction p ((box.certificate j).exactEdge i))
        (outerProjectionLinear (p.matrixPoseWithOffset offset)
          (normalizedExactVertex ((box.certificate j).supportIndex i))) := by
  have hsum := (viewSum_pos hchamber).ne'
  have hupper := box.exactSupport_le_upper h hchamber hmem j i k
  have hchecked := h.support j i k
  have hsigned : (box.certificate j).exactSupport p i k ≤ 0 :=
    hupper.trans (by exact_mod_cast hchecked)
  have hdiff :
      inner ℝ (direction p ((box.certificate j).exactEdge i))
          ((outerProjectionLinear (p.matrixPoseWithOffset offset))
            (normalizedExactVertex k) -
          (outerProjectionLinear (p.matrixPoseWithOffset offset))
            (normalizedExactVertex ((box.certificate j).supportIndex i))) =
        (box.certificate j).exactSupport p i k := by
    rw [← map_sub,
      inner_direction_outerProjection_eq_support p offset _ _ hsum]
    rfl
  rw [inner_sub_right] at hdiff
  linarith

theorem Box.valid_direction_nonzero (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (offset : ℝ²)
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) (i : Fin 3) :
    direction p ((box.certificate j).exactEdge i) ≠ 0 := by
  intro hzero
  let k := (box.certificate j).nonzeroWitness i
  have hupper := box.exactSupport_le_upper h hchamber hmem j i k
  have hstrict : (box.supportUpper j i k : ℝ) < 0 := by
    exact_mod_cast h.direction_nonzero j i
  have hexact : (box.certificate j).exactSupport p i k < 0 :=
    hupper.trans_lt hstrict
  have hsum := (viewSum_pos hchamber).ne'
  have heq := inner_direction_outerProjection_eq_support p offset
    ((box.certificate j).exactEdge i)
    ((box.certificate j).exactDelta i k) hsum
  rw [hzero, inner_zero_left] at heq
  change linearValue (normalizedView p)
    (cross3 ((box.certificate j).exactEdge i)
      ((box.certificate j).exactDelta i k)) < 0 at hexact
  rw [← heq] at hexact
  linarith

theorem Box.weightAt_cast (box : Box) (j : Fin 4)
    (corner : Fin 3) (i : Fin 3) :
    (box.weightAt j corner i : ℝ) =
      (box.certificate j).approxWeight (toReal box.triangle corner) i := by
  simp [Box.weightAt, AxisCertificate.approxWeight, dotQ,
    linearValue, ProjectiveView.toReal]

theorem Box.weightLower_le_approx (box : Box)
    {p : CayleyPose ℝ}
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) (i : Fin 3) :
    (box.weightLower j i : ℝ) ≤
      (box.certificate j).approxWeight (normalizedView p) i := by
  have hlinear :
      (min3 (fun corner => box.weightAt j corner i) : ℝ) ≤
        (box.certificate j).approxWeight (normalizedView p) i := by
    unfold AxisCertificate.approxWeight
    apply le_linearValue_of_mem hmem
    intro corner
    change (min3 (fun c => box.weightAt j c i) : ℝ) ≤
      (box.certificate j).approxWeight (toReal box.triangle corner) i
    rw [← box.weightAt_cast j corner i]
    exact_mod_cast min3_le (fun c => box.weightAt j c i) corner
  change ((min3 (fun corner => box.weightAt j corner i) -
    CayleyEdgeCertificate.supportError : ℚ) : ℝ) ≤ _
  push_cast
  have herr : (0 : ℝ) ≤
      (CayleyEdgeCertificate.supportError : ℝ) := by
    norm_num [CayleyEdgeCertificate.supportError,
      RationalApprox.κℚ]
  linarith

theorem Box.approxWeight_le_upper (box : Box)
    {p : CayleyPose ℝ}
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) (i : Fin 3) :
    (box.certificate j).approxWeight (normalizedView p) i ≤
      (box.weightUpper j i : ℝ) := by
  have hlinear :
      (box.certificate j).approxWeight (normalizedView p) i ≤
        (max3 (fun corner => box.weightAt j corner i) : ℝ) := by
    unfold AxisCertificate.approxWeight
    apply linearValue_le_of_mem hmem
    intro corner
    change (box.certificate j).approxWeight
      (toReal box.triangle corner) i ≤
        (max3 (fun c => box.weightAt j c i) : ℝ)
    rw [← box.weightAt_cast j corner i]
    exact_mod_cast le_max3 (fun c => box.weightAt j c i) corner
  change _ ≤ ((max3 (fun corner => box.weightAt j corner i) +
    CayleyEdgeCertificate.supportError : ℚ) : ℝ)
  push_cast
  have herr : (0 : ℝ) ≤
      (CayleyEdgeCertificate.supportError : ℝ) := by
    norm_num [CayleyEdgeCertificate.supportError,
      RationalApprox.κℚ]
  linarith

theorem Box.weightLower_le_exact (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) (i : Fin 3) :
    (box.weightLower j i : ℝ) ≤
      (box.certificate j).exactWeight p i := by
  have hmin : (min3 (fun corner => box.weightAt j corner i) : ℝ) ≤
      (box.certificate j).approxWeight (normalizedView p) i := by
    unfold AxisCertificate.approxWeight
    apply le_linearValue_of_mem hmem
    intro corner
    change (min3 (fun c => box.weightAt j c i) : ℝ) ≤
      (box.certificate j).approxWeight (toReal box.triangle corner) i
    rw [← box.weightAt_cast j corner i]
    exact_mod_cast min3_le (fun c => box.weightAt j c i) corner
  have herr := (box.certificate j).exactWeight_sub_approx_abs_le
    hchamber i
  rw [abs_le] at herr
  have herrorEq : (10 * RationalApprox.κ : ℝ) =
      (CayleyEdgeCertificate.supportError : ℝ) := by
    norm_num [CayleyEdgeCertificate.supportError,
      RationalApprox.κ, RationalApprox.κℚ]
  simp only [Box.weightLower]
  push_cast
  rw [herrorEq] at herr
  linarith [herr.1]

theorem Box.exactWeight_le_upper (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) (i : Fin 3) :
    (box.certificate j).exactWeight p i ≤
      (box.weightUpper j i : ℝ) := by
  have hmax :
      (box.certificate j).approxWeight (normalizedView p) i ≤
        (max3 (fun corner => box.weightAt j corner i) : ℝ) := by
    unfold AxisCertificate.approxWeight
    apply linearValue_le_of_mem hmem
    intro corner
    change (box.certificate j).approxWeight
      (toReal box.triangle corner) i ≤
        (max3 (fun c => box.weightAt j c i) : ℝ)
    rw [← box.weightAt_cast j corner i]
    exact_mod_cast le_max3 (fun c => box.weightAt j c i) corner
  have herr := (box.certificate j).exactWeight_sub_approx_abs_le
    hchamber i
  rw [abs_le] at herr
  have herrorEq : (10 * RationalApprox.κ : ℝ) =
      (CayleyEdgeCertificate.supportError : ℝ) := by
    norm_num [CayleyEdgeCertificate.supportError,
      RationalApprox.κ, RationalApprox.κℚ]
  simp only [Box.weightUpper]
  push_cast
  rw [herrorEq] at herr
  linarith [herr.2, hmax]

theorem Box.valid_weight_nonneg (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) (i : Fin 3) :
    0 ≤ (box.certificate j).exactWeight p i := by
  have hlower : (0 : ℝ) ≤ (box.weightLower j i : ℝ) := by
    exact_mod_cast h.weight_nonneg j i
  exact hlower.trans (box.weightLower_le_exact h hchamber hmem j i)

theorem Box.valid_weight_pos (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) :
    ∃ i, 0 < (box.certificate j).exactWeight p i := by
  obtain ⟨i, hi⟩ := h.weight_pos j
  refine ⟨i, ?_⟩
  have hiReal : (0 : ℝ) < (box.weightLower j i : ℝ) := by
    exact_mod_cast hi
  exact hiReal.trans_le (box.weightLower_le_exact h hchamber hmem j i)

noncomputable def AxisCertificate.exactVertex
    (cert : AxisCertificate) (i : Fin 3) : ℝ³ :=
  normalizedExactVertex (cert.supportIndex i)

noncomputable def AxisCertificate.approxVertex
    (cert : AxisCertificate) (i : Fin 3) : ℝ³ :=
  toR3 (normalizedRationalVertex (cert.supportIndex i))

theorem AxisCertificate.exactVertex_norm_le_one
    (cert : AxisCertificate) (i : Fin 3) :
    ‖cert.exactVertex i‖ ≤ 1 :=
  normalizedExactVertex_norm_le_one (cert.supportIndex i)

theorem AxisCertificate.approxVertex_norm_le
    (cert : AxisCertificate) (i : Fin 3) :
    ‖cert.approxVertex i‖ ≤ 1 + RationalApprox.κ :=
  CayleyGlobalCertificate.norm_normalizedRationalVertex_le
    (cert.supportIndex i)

theorem AxisCertificate.exactVertex_sub_approx_norm_le
    (cert : AxisCertificate) (i : Fin 3) :
    ‖cert.exactVertex i - cert.approxVertex i‖ ≤
      RationalApprox.κ :=
  normalizedApproximation.approx (cert.supportIndex i)

noncomputable def AxisCertificate.exactLift
    (cert : AxisCertificate) (p : CayleyPose ℝ) (i : Fin 3) : ℝ³ :=
  cross3 (normalizedView3 p) (cert.exactEdge i)

noncomputable def AxisCertificate.approxLift
    (cert : AxisCertificate) (p : CayleyPose ℝ) (i : Fin 3) : ℝ³ :=
  cross3 (normalizedView3 p) (cert.approxEdge i)

theorem AxisCertificate.exactLift_sub_approx_eq
    (cert : AxisCertificate) (p : CayleyPose ℝ) (i : Fin 3) :
    cert.exactLift p i - cert.approxLift p i =
      cross3 (normalizedView3 p)
        (cert.exactEdge i - cert.approxEdge i) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [AxisCertificate.exactLift, AxisCertificate.approxLift,
      cross3, cross_apply] <;> ring

theorem AxisCertificate.exactLift_sub_approx_norm_le
    (cert : AxisCertificate) {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (i : Fin 3) :
    ‖cert.exactLift p i - cert.approxLift p i‖ ≤
      2 * RationalApprox.κ := by
  rw [cert.exactLift_sub_approx_eq]
  exact (cross3_norm_le _ _).trans
    ((mul_le_mul (normalizedView3_norm_le_one hchamber)
      (cert.exactEdge_sub_approx_norm_le i) (norm_nonneg _)
      (by norm_num [RationalApprox.κ])).trans (by ring_nf; rfl))

theorem AxisCertificate.exactLift_norm_le_two
    (cert : AxisCertificate) {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (i : Fin 3) : ‖cert.exactLift p i‖ ≤ 2 := by
  unfold AxisCertificate.exactLift
  exact (cross3_norm_le _ _).trans
    ((mul_le_mul (normalizedView3_norm_le_one hchamber)
      (cert.exactEdge_norm_le_two i) (norm_nonneg _)
      (by positivity)).trans (by norm_num))

theorem AxisCertificate.approxLift_norm_le
    (cert : AxisCertificate) {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (i : Fin 3) :
    ‖cert.approxLift p i‖ ≤ 2 * (1 + RationalApprox.κ) := by
  unfold AxisCertificate.approxLift
  exact (cross3_norm_le _ _).trans
    ((mul_le_mul (normalizedView3_norm_le_one hchamber)
      (cert.approxEdge_norm_le i) (norm_nonneg _)
      (by norm_num [RationalApprox.κ])).trans (by ring_nf; rfl))

noncomputable def AxisCertificate.exactCross
    (cert : AxisCertificate) (p : CayleyPose ℝ) (i : Fin 3) : ℝ³ :=
  cross3 (cert.exactVertex i) (cert.exactLift p i)

noncomputable def AxisCertificate.approxCross
    (cert : AxisCertificate) (p : CayleyPose ℝ) (i : Fin 3) : ℝ³ :=
  cross3 (cert.approxVertex i) (cert.approxLift p i)

theorem AxisCertificate.exactCross_norm_le_two
    (cert : AxisCertificate) {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (i : Fin 3) : ‖cert.exactCross p i‖ ≤ 2 := by
  unfold AxisCertificate.exactCross
  exact (cross3_norm_le _ _).trans
    ((mul_le_mul (cert.exactVertex_norm_le_one i)
      (cert.exactLift_norm_le_two hchamber i) (norm_nonneg _)
      (by positivity)).trans (by norm_num))

theorem AxisCertificate.exactCross_sub_approx_norm_le
    (cert : AxisCertificate) {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (i : Fin 3) :
    ‖cert.exactCross p i - cert.approxCross p i‖ ≤
      5 * RationalApprox.κ := by
  have hdecomp : cert.exactCross p i - cert.approxCross p i =
      cross3 (cert.exactVertex i)
          (cert.exactLift p i - cert.approxLift p i) +
        cross3 (cert.exactVertex i - cert.approxVertex i)
          (cert.approxLift p i) := by
    unfold AxisCertificate.exactCross AxisCertificate.approxCross
    rw [cross3_sub_cross3]
  rw [hdecomp]
  calc
    _ ≤ ‖cross3 (cert.exactVertex i)
          (cert.exactLift p i - cert.approxLift p i)‖ +
        ‖cross3 (cert.exactVertex i - cert.approxVertex i)
          (cert.approxLift p i)‖ := norm_add_le _ _
    _ ≤ 1 * (2 * RationalApprox.κ) +
        RationalApprox.κ * (2 * (1 + RationalApprox.κ)) := by
      exact add_le_add
        ((cross3_norm_le _ _).trans (mul_le_mul
          (cert.exactVertex_norm_le_one i)
          (cert.exactLift_sub_approx_norm_le hchamber i)
          (norm_nonneg _) (by norm_num [RationalApprox.κ])))
        ((cross3_norm_le _ _).trans (mul_le_mul
          (cert.exactVertex_sub_approx_norm_le i)
          (cert.approxLift_norm_le hchamber i)
          (norm_nonneg _) (by norm_num [RationalApprox.κ])))
    _ ≤ 5 * RationalApprox.κ := by
      norm_num [RationalApprox.κ]

theorem AxisCertificate.approxVariation_eq_sum_approxCross
    (cert : AxisCertificate) (p : CayleyPose ℝ) :
    cert.approxVariation (normalizedView p) =
      ∑ i, cert.approxWeight (normalizedView p) i •
        cert.approxCross p i := by
  unfold AxisCertificate.approxVariation AxisCertificate.approxWeight
  unfold AxisCertificate.approxCross AxisCertificate.approxLift
  rfl

theorem AxisCertificate.variation_error
    (cert : AxisCertificate) {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber) :
    ‖variationVector p (fun i => cert.exactEdge i)
          (fun i => cert.exactVertex i) -
        cert.approxVariation (normalizedView p)‖ ≤
      (variationError : ℝ) := by
  rw [cert.approxVariation_eq_sum_approxCross]
  unfold variationVector
  change ‖(∑ i, cert.exactWeight p i • cert.exactCross p i) -
      ∑ i, cert.approxWeight (normalizedView p) i •
        cert.approxCross p i‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    ∑ i, ‖cert.exactWeight p i • cert.exactCross p i -
        cert.approxWeight (normalizedView p) i •
          cert.approxCross p i‖ ≤
        ∑ _i : Fin 3, 50 * RationalApprox.κ := by
      apply Finset.sum_le_sum
      intro i _
      have hdecomp :
          cert.exactWeight p i • cert.exactCross p i -
              cert.approxWeight (normalizedView p) i •
                cert.approxCross p i =
            (cert.exactWeight p i -
                cert.approxWeight (normalizedView p) i) •
              cert.exactCross p i +
            cert.approxWeight (normalizedView p) i •
              (cert.exactCross p i - cert.approxCross p i) := by
        module
      rw [hdecomp]
      calc
        _ ≤ ‖(cert.exactWeight p i -
                cert.approxWeight (normalizedView p) i) •
              cert.exactCross p i‖ +
            ‖cert.approxWeight (normalizedView p) i •
              (cert.exactCross p i - cert.approxCross p i)‖ :=
          norm_add_le _ _
        _ ≤ (10 * RationalApprox.κ) * 2 +
            (4 + 10 * RationalApprox.κ) *
              (5 * RationalApprox.κ) := by
          simp only [norm_smul, Real.norm_eq_abs]
          exact add_le_add
            (mul_le_mul
              (cert.exactWeight_sub_approx_abs_le hchamber i)
              (cert.exactCross_norm_le_two hchamber i)
              (norm_nonneg _)
              (by norm_num [RationalApprox.κ]))
            (mul_le_mul
              (cert.approxWeight_abs_le hchamber i)
              (cert.exactCross_sub_approx_norm_le hchamber i)
              (norm_nonneg _)
              (by norm_num [RationalApprox.κ]))
        _ ≤ 50 * RationalApprox.κ := by
          norm_num [RationalApprox.κ]
    _ = (variationError : ℝ) := by
      simp [Fin.sum_univ_three, variationError]
      norm_num [RationalApprox.κ, RationalApprox.κℚ]

def Box.variationCenterQ (box : Box) (j : Fin 4) : VectorQ :=
  fun coordinate => (box.variationBall j coordinate).center

noncomputable def Box.variationCenter (box : Box) (j : Fin 4) : ℝ³ :=
  toR3 (box.variationCenterQ j)

theorem norm_le_sum_abs_coordinates (v : ℝ³) :
    ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2),
      sq_abs (v 0), sq_abs (v 1), sq_abs (v 2)]

theorem Box.exactVariation_coordinate_error (box : Box)
    {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) (coordinate : Fin 3) :
    |variationVector p (fun i => (box.certificate j).exactEdge i)
          (fun i => (box.certificate j).exactVertex i) coordinate -
        box.variationCenter j coordinate| ≤
      ((box.variationBall j coordinate).radius : ℝ) +
        (variationError : ℝ) := by
  let cert := box.certificate j
  let exact := variationVector p (fun i => cert.exactEdge i)
    (fun i => cert.exactVertex i)
  let approx := cert.approxVariation (normalizedView p)
  have hvariation := cert.variation_error hchamber
  have hcoordinate := PiLp.norm_apply_le (exact - approx) coordinate
  have hcoordError : |exact coordinate - approx coordinate| ≤
      (variationError : ℝ) := by
    rw [show (exact - approx) coordinate =
      exact coordinate - approx coordinate by rfl,
      Real.norm_eq_abs] at hcoordinate
    exact hcoordinate.trans hvariation
  have hball := box.variationBall_holds hmem j coordinate
  have hball' : |approx coordinate -
      (box.variationBall j coordinate).center| ≤
        ((box.variationBall j coordinate).radius : ℝ) := by
    simpa [RatBall.Holds, cert, approx] using hball
  change |exact coordinate -
      (box.variationBall j coordinate).center| ≤ _
  calc
    _ ≤ |exact coordinate - approx coordinate| +
        |approx coordinate -
          (box.variationBall j coordinate).center| := by
      rw [show exact coordinate -
          (box.variationBall j coordinate).center =
        (exact coordinate - approx coordinate) +
          (approx coordinate -
            (box.variationBall j coordinate).center) by ring]
      exact abs_add_le _ _
    _ ≤ (variationError : ℝ) +
        ((box.variationBall j coordinate).radius : ℝ) :=
      add_le_add hcoordError hball'
    _ = ((box.variationBall j coordinate).radius : ℝ) +
        (variationError : ℝ) := by ring

theorem Box.exactVariation_sub_center_norm_le (box : Box)
    {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) :
    ‖variationVector p (fun i => (box.certificate j).exactEdge i)
          (fun i => (box.certificate j).exactVertex i) -
        box.variationCenter j‖ ≤
      (box.variationRadiusSum j : ℝ) + 3 * (variationError : ℝ) := by
  let diff := variationVector p
      (fun i => (box.certificate j).exactEdge i)
      (fun i => (box.certificate j).exactVertex i) -
    box.variationCenter j
  apply (norm_le_sum_abs_coordinates diff).trans
  have h0 := box.exactVariation_coordinate_error hchamber hmem j 0
  have h1 := box.exactVariation_coordinate_error hchamber hmem j 1
  have h2 := box.exactVariation_coordinate_error hchamber hmem j 2
  change |diff 0| ≤
    ((box.variationBall j 0).radius : ℝ) +
      (variationError : ℝ) at h0
  change |diff 1| ≤
    ((box.variationBall j 1).radius : ℝ) +
      (variationError : ℝ) at h1
  change |diff 2| ≤
    ((box.variationBall j 2).radius : ℝ) +
      (variationError : ℝ) at h2
  change |diff 0| + |diff 1| + |diff 2| ≤ _
  simp only [Box.variationRadiusSum, Fin.sum_univ_three]
  push_cast
  linarith

theorem Box.toR3_approxNormalizedCenter (box : Box) (h : box.Valid)
    (j : Fin 4) :
    toR3 (box.approxNormalizedCenter j) =
      (((box.certificate j).B : ℝ)⁻¹) • box.variationCenter j := by
  have hB : ((box.certificate j).B : ℝ) ≠ 0 := by
    exact_mod_cast (h.B_pos j).ne'
  ext coordinate
  simp [Box.approxNormalizedCenter, Box.variationCenter,
    Box.variationCenterQ, toR3, smul_eq_mul]
  field_simp [hB]

theorem Box.valid_normalizedVariation_move (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) :
    ‖normalizedVariation p
          (fun j i => (box.certificate j).exactEdge i)
          (fun j i => (box.certificate j).supportIndex i)
          (fun j => ((box.certificate j).B : ℝ)) j -
        toR3 (box.approxNormalizedCenter j)‖ ≤ (box.δ : ℝ) := by
  have hBpos : (0 : ℝ) < ((box.certificate j).B : ℝ) := by
    exact_mod_cast h.B_pos j
  have hBne := hBpos.ne'
  have hraw := box.exactVariation_sub_center_norm_le hchamber hmem j
  have hchecked :
      (box.variationRadiusSum j : ℝ) + 3 * (variationError : ℝ) ≤
        ((box.certificate j).B : ℝ) * (box.δ : ℝ) := by
    exact_mod_cast h.variation j
  rw [normalizedVariation, box.toR3_approxNormalizedCenter h j,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hBpos]
  calc
    ((box.certificate j).B : ℝ)⁻¹ *
        ‖variationVector p (fun i => (box.certificate j).exactEdge i)
            (fun i => normalizedExactVertex
              ((box.certificate j).supportIndex i)) -
          box.variationCenter j‖ ≤
      ((box.certificate j).B : ℝ)⁻¹ *
        ((box.variationRadiusSum j : ℝ) +
          3 * (variationError : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hBpos.le)
      simpa [AxisCertificate.exactVertex] using hraw
    _ ≤ ((box.certificate j).B : ℝ)⁻¹ *
        (((box.certificate j).B : ℝ) * (box.δ : ℝ)) :=
      mul_le_mul_of_nonneg_left hchecked (inv_nonneg.mpr hBpos.le)
    _ = (box.δ : ℝ) := by
      field_simp [hBne]

private theorem Box.barycentric_mem_convexHull (box : Box)
    (h : box.Valid) (k : Fin 6) :
    toR3 (box.octahedronTarget k) ∈
      convexHull ℝ {toR3 (box.approxNormalizedCenter j) | j} := by
  apply Noperthedron.BalancedSupport.mem_convexHull_of_barycentric
    (fun j => toR3 (box.approxNormalizedCenter j))
    (fun j => (box.barycentric k j : ℝ))
  · intro j
    exact_mod_cast h.barycentric.2 k j
  · exact_mod_cast LocalCertificate.tetraBarycentricQ_sum
      box.approxNormalizedCenter (box.octahedronTarget k)
  · ext coordinate
    have hcoordinate := congrFun
      (LocalCertificate.tetraBarycentricQ_combination
        box.approxNormalizedCenter (box.octahedronTarget k)
        h.barycentric.1) coordinate
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toR3,
      WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_toLp]
    exact_mod_cast hcoordinate

theorem Box.valid_center_axis_cover (box : Box) (h : box.Valid)
    (axis : ℝ³) (haxis : ‖axis‖ = 1) :
    ∃ j, ((box.c + box.δ : ℚ) : ℝ) ≤
      inner ℝ axis (toR3 (box.approxNormalizedCenter j)) := by
  apply Noperthedron.BalancedSupport.octahedral_axis_cover
    (fun j => toR3 (box.approxNormalizedCenter j))
    ((box.c + box.δ : ℚ) : ℝ)
  · exact_mod_cast add_nonneg h.c_nonneg h.delta_nonneg
  · have heq : toR3 (box.octahedronTarget 0) =
        (7 / 4 * (((box.c + box.δ : ℚ) : ℝ))) •
          Noperthedron.BalancedSupport.xAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_zero]
      ext i
      fin_cases i <;>
        norm_num [Noperthedron.BalancedSupport.xAxis3, toR3]
    rw [← heq]
    exact box.barycentric_mem_convexHull h 0
  · have heq : toR3 (box.octahedronTarget 1) =
        (- (7 / 4 * (((box.c + box.δ : ℚ) : ℝ)))) •
          Noperthedron.BalancedSupport.xAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_one]
      ext i
      fin_cases i <;>
        norm_num [Noperthedron.BalancedSupport.xAxis3, toR3]
    rw [← heq]
    exact box.barycentric_mem_convexHull h 1
  · have heq : toR3 (box.octahedronTarget 2) =
        (7 / 4 * (((box.c + box.δ : ℚ) : ℝ))) •
          Noperthedron.BalancedSupport.yAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_two]
      ext i
      fin_cases i <;>
        norm_num [Noperthedron.BalancedSupport.yAxis3, toR3]
    rw [← heq]
    exact box.barycentric_mem_convexHull h 2
  · have heq : toR3 (box.octahedronTarget 3) =
        (- (7 / 4 * (((box.c + box.δ : ℚ) : ℝ)))) •
          Noperthedron.BalancedSupport.yAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_three]
      ext i
      fin_cases i <;>
        norm_num [Noperthedron.BalancedSupport.yAxis3, toR3]
    rw [← heq]
    exact box.barycentric_mem_convexHull h 3
  · have heq : toR3 (box.octahedronTarget 4) =
        (7 / 4 * (((box.c + box.δ : ℚ) : ℝ))) •
          Noperthedron.BalancedSupport.zAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_four]
      ext i
      fin_cases i <;>
        norm_num [Noperthedron.BalancedSupport.zAxis3, toR3]
    rw [← heq]
    exact box.barycentric_mem_convexHull h 4
  · have heq : toR3 (box.octahedronTarget 5) =
        (- (7 / 4 * (((box.c + box.δ : ℚ) : ℝ)))) •
          Noperthedron.BalancedSupport.zAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_five]
      ext i
      fin_cases i <;>
        norm_num [Noperthedron.BalancedSupport.zAxis3, toR3]
    rw [← heq]
    exact box.barycentric_mem_convexHull h 5
  · exact haxis

theorem Box.valid_axis_cover (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (axis : ℝ³) (haxis : ‖axis‖ = 1) :
    ∃ j, (box.c : ℝ) ≤
      inner ℝ axis
        (normalizedVariation p
          (fun j i => (box.certificate j).exactEdge i)
          (fun j i => (box.certificate j).supportIndex i)
          (fun j => ((box.certificate j).B : ℝ)) j) := by
  obtain ⟨j, hcenter⟩ := box.valid_center_axis_cover h axis haxis
  refine ⟨j, ?_⟩
  have hmove := box.valid_normalizedVariation_move h hchamber hmem j
  have hinner := abs_real_inner_le_norm axis
    (normalizedVariation p
      (fun j i => (box.certificate j).exactEdge i)
      (fun j i => (box.certificate j).supportIndex i)
      (fun j => ((box.certificate j).B : ℝ)) j -
        toR3 (box.approxNormalizedCenter j))
  rw [haxis, one_mul] at hinner
  rw [inner_sub_right] at hinner
  have hdelta : (0 : ℝ) ≤ (box.δ : ℝ) := by
    exact_mod_cast h.delta_nonneg
  push_cast at hcenter
  rw [abs_le] at hinner
  linarith

theorem norm_quarterTurn (u : ℝ²) : ‖quarterTurn u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [quarterTurn, Fin.sum_univ_two, sq_abs]
  ring

theorem AxisCertificate.direction_norm_le_two
    (cert : AxisCertificate) {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (i : Fin 3) : ‖direction p (cert.exactEdge i)‖ ≤ 2 := by
  have hsumPos := viewSum_pos hchamber
  have hsumOne := one_le_viewSum hchamber
  have hinv : (viewSum p)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hsumOne
  have hrot : ‖rotM p.θ p.φ (cert.exactEdge i)‖ ≤ 2 := by
    calc
      _ ≤ ‖rotM p.θ p.φ‖ * ‖cert.exactEdge i‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖cert.exactEdge i‖ := by
        rw [Bounding.rotM_norm_one, one_mul]
      _ ≤ 2 := cert.exactEdge_norm_le_two i
  rw [direction, norm_smul, norm_quarterTurn, Real.norm_eq_abs,
    abs_inv, abs_of_pos hsumPos]
  exact (mul_le_mul hinv hrot (norm_nonneg _)
    (by norm_num)).trans (by norm_num)

theorem Box.valid_budget (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (j : Fin 4) :
    ∑ i, (box.certificate j).exactWeight p i *
      (‖direction p ((box.certificate j).exactEdge i)‖ *
        ‖normalizedExactVertex ((box.certificate j).supportIndex i)‖) ≤
      ((box.certificate j).B : ℝ) := by
  let cert := box.certificate j
  have hsum :
      ∑ i, cert.exactWeight p i *
          (‖direction p (cert.exactEdge i)‖ *
            ‖normalizedExactVertex (cert.supportIndex i)‖) ≤
        ∑ i, (box.weightUpper j i : ℝ) * 2 := by
    apply Finset.sum_le_sum
    intro i _
    have hw0 := box.valid_weight_nonneg h hchamber hmem j i
    have hwUpper := box.exactWeight_le_upper h hchamber hmem j i
    have hfactor :
        ‖direction p (cert.exactEdge i)‖ *
            ‖normalizedExactVertex (cert.supportIndex i)‖ ≤ 2 := by
      calc
        _ ≤ 2 * 1 := mul_le_mul
          (cert.direction_norm_le_two hchamber i)
          (normalizedExactVertex_norm_le_one (cert.supportIndex i))
          (norm_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    calc
      cert.exactWeight p i *
          (‖direction p (cert.exactEdge i)‖ *
            ‖normalizedExactVertex (cert.supportIndex i)‖) ≤
        cert.exactWeight p i * 2 :=
          mul_le_mul_of_nonneg_left hfactor hw0
      _ ≤ (box.weightUpper j i : ℝ) * 2 :=
        mul_le_mul_of_nonneg_right hwUpper (by norm_num)
  change ∑ i, (box.certificate j).exactWeight p i *
      (‖direction p ((box.certificate j).exactEdge i)‖ *
        ‖normalizedExactVertex ((box.certificate j).supportIndex i)‖) ≤ _
  apply hsum.trans
  rw [← Finset.sum_mul]
  have hchecked :
      (2 * ∑ i, box.weightUpper j i : ℝ) ≤
        ((box.certificate j).B : ℝ) := by
    exact_mod_cast h.budget j
  simpa [mul_comm] using hchecked

theorem Box.radius_le (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal) :
    Real.sqrt (p.x ^ 2 + p.y ^ 2 + p.z ^ 2) ≤ (box.c : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact_mod_cast h.c_nonneg
  · exact (box.radiusShell.sq_sum_le_radiusSq hp).trans
      (by exact_mod_cast h.radius)

/-- A valid rational projective-local row rules out every translated pose in
its Cayley interval and projective viewing triangle. -/
theorem Box.valid_imp_not_translated_rupert (box : Box) (h : box.Valid)
    (p : CayleyPose ℝ) (hp : p ∈ box.interval.toReal)
    (offset : ℝ²)
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p)) :
    ¬ RupertPose (p.matrixPoseWithOffset offset)
      normalizedExactPolyhedron.hull := by
  apply not_rupertPose_of_projective_local_certificates
    (p := p) (offset := offset)
    (edge := fun j i => (box.certificate j).exactEdge i)
    (index := fun j i => (box.certificate j).supportIndex i)
    (B := fun j => ((box.certificate j).B : ℝ))
    (c := (box.c : ℝ))
  · exact (viewSum_pos hchamber).ne'
  · intro j
    exact_mod_cast h.B_pos j
  · exact box.valid_axis_cover h hchamber hmem
  · exact box.valid_budget h hchamber hmem
  · exact box.radius_le h hp
  · exact box.valid_direction_nonzero h offset hchamber hmem
  · exact box.valid_weight_nonneg h hchamber hmem
  · exact box.valid_weight_pos h hchamber hmem
  · exact box.valid_support h offset hchamber hmem

theorem Box.valid_imp_no_translated_rupert_in_region
    (box : Box) (h : box.Valid) :
    ¬ ∃ p ∈ box.interval.toReal, ∃ offset : ℝ²,
      (p.matrixPoseWithOffset offset).InOuterViewChamber ∧
      InTriangle (toReal box.triangle) (normalizedView p) ∧
      RupertPose (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull := by
  rintro ⟨p, hp, offset, hchamber, hmem, hrupert⟩
  exact box.valid_imp_not_translated_rupert h p hp offset hchamber hmem
    hrupert

end Noperthedron.SnubCube.ProjectiveLocalCertificate

end
