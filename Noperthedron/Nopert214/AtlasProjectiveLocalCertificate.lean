module

public import Noperthedron.Nopert214.AtlasLocalCertificate
public import Noperthedron.Nopert214.AtlasProjectiveLocalRigidity
public import Noperthedron.Nopert214.AtlasProjectiveEdgeCertificate
public import Noperthedron.SnubCube.ProjectiveLocalCertificate

@[expose] public section

/-! # Rational projective local certificates for Nopert #214 -/

namespace Noperthedron.Nopert214.AtlasProjectiveLocalCertificate

open scoped RealInnerProductSpace
open Noperthedron.Checker
open Noperthedron.BalancedSupport
open Noperthedron.SnubCube.ProjectiveView
open AtlasProjectiveView AtlasProjectiveEdgeCertificate
open AtlasProjectiveLocalRigidity

abbrev VectorQ := Fin 3 → ℚ

structure AxisCertificate where
  edgeStart : Fin 3 → VertexIndex
  edgeFinish : Fin 3 → VertexIndex
  edgeStart₂ : Fin 3 → VertexIndex
  edgeFinish₂ : Fin 3 → VertexIndex
  /-- Convex mixing weight, interpreted as `mix / 1000`. -/
  mix : Fin 3 → Fin 1001
  /-- Inner index; the selected outer support vertex is its symmetry image. -/
  index : Fin 3 → VertexIndex
  nonzeroWitness : Fin 3 → VertexIndex
  B : ℚ
deriving DecidableEq, Repr

structure Box where
  interval : AtlasInterval ℚ
  root : Fin 8
  triangle : AtlasProjectiveView.Triangle ℚ
  chart : CayleyAtlas.ChartIndex
  symmetryIndex : OrbitIndex
  certificate : Fin 4 → AxisCertificate
  c : ℚ
  δ : ℚ
  r : ℚ
deriving DecidableEq

def AxisCertificate.supportIndex (box : Box) (cert : AxisCertificate)
    (i : Fin 3) : VertexIndex :=
  symmetryAction box.symmetryIndex (cert.index i)

def AxisCertificate.mixQ (cert : AxisCertificate) (i : Fin 3) : ℚ :=
  (cert.mix i).val / 1000

theorem AxisCertificate.mixQ_nonneg (cert : AxisCertificate) (i : Fin 3) :
    0 ≤ cert.mixQ i := by
  unfold AxisCertificate.mixQ
  positivity

theorem AxisCertificate.mixQ_le_one (cert : AxisCertificate) (i : Fin 3) :
    cert.mixQ i ≤ 1 := by
  unfold AxisCertificate.mixQ
  rw [div_le_iff₀ (by norm_num : (0 : ℚ) < 1000)]
  norm_num
  exact_mod_cast Nat.le_of_lt_succ (cert.mix i).isLt

def AxisCertificate.edgeQ (cert : AxisCertificate) (i : Fin 3) : VectorQ :=
  cert.mixQ i •
      (rationalVertex (cert.edgeStart i) -
        rationalVertex (cert.edgeFinish i)) +
    (1 - cert.mixQ i) •
      (rationalVertex (cert.edgeStart₂ i) -
        rationalVertex (cert.edgeFinish₂ i))

noncomputable def AxisCertificate.exactEdge
    (cert : AxisCertificate) (i : Fin 3) : ℝ³ :=
  (cert.mixQ i : ℝ) •
      (exactVertex (cert.edgeStart i) - exactVertex (cert.edgeFinish i)) +
    (1 - (cert.mixQ i : ℝ)) •
      (exactVertex (cert.edgeStart₂ i) - exactVertex (cert.edgeFinish₂ i))

def AxisCertificate.weightCoefficient
    (cert : AxisCertificate) : Fin 3 → VectorQ := ![
  LocalCertificate.crossQ (cert.edgeQ 1) (cert.edgeQ 2),
  LocalCertificate.crossQ (cert.edgeQ 2) (cert.edgeQ 0),
  LocalCertificate.crossQ (cert.edgeQ 0) (cert.edgeQ 1)]

/-- Coefficients of `cross(n, edge)` as a linear function of `n`. -/
def AxisCertificate.liftCoefficient (cert : AxisCertificate)
    (i coordinate : Fin 3) : VectorQ :=
  let edge := cert.edgeQ i
  match coordinate with
  | 0 => ![0, edge 2, -edge 1]
  | 1 => ![-edge 2, 0, edge 0]
  | 2 => ![edge 1, -edge 0, 0]

/-- Coefficients of `cross(vertex, cross(n, edge))`. -/
def AxisCertificate.crossLiftCoefficient (box : Box)
    (cert : AxisCertificate) (i coordinate : Fin 3) : VectorQ :=
  let vertex := rationalVertex (cert.supportIndex box i)
  match coordinate with
  | 0 => vertex 1 • cert.liftCoefficient i 2 -
      vertex 2 • cert.liftCoefficient i 1
  | 1 => vertex 2 • cert.liftCoefficient i 0 -
      vertex 0 • cert.liftCoefficient i 2
  | 2 => vertex 0 • cert.liftCoefficient i 1 -
      vertex 1 • cert.liftCoefficient i 0

def AxisCertificate.variationPolynomial (box : Box)
    (cert : AxisCertificate) (coordinate : Fin 3) : RatQuadratic3 :=
  Noperthedron.SnubCube.ProjectiveLocalCertificate.mulLinear
      (cert.weightCoefficient 0)
      (cert.crossLiftCoefficient box 0 coordinate) +
    Noperthedron.SnubCube.ProjectiveLocalCertificate.mulLinear
      (cert.weightCoefficient 1)
      (cert.crossLiftCoefficient box 1 coordinate) +
    Noperthedron.SnubCube.ProjectiveLocalCertificate.mulLinear
      (cert.weightCoefficient 2)
      (cert.crossLiftCoefficient box 2 coordinate)

def Box.triangleBalls (box : Box) (coordinate : Fin 3) : RatBall :=
  RatBall.ofEndpoints
    (min3 fun j => box.triangle j coordinate)
    (max3 fun j => box.triangle j coordinate)

def Box.variationBall (box : Box) (j : Fin 4)
    (coordinate : Fin 3) : RatBall :=
  RatQuadratic3.evalBall box.triangleBalls
    ((box.certificate j).variationPolynomial box coordinate)

def AxisCertificate.deltaQ (box : Box) (cert : AxisCertificate)
    (i : Fin 3) (k : VertexIndex) : VectorQ :=
  rationalVertex k - rationalVertex (cert.supportIndex box i)

def Box.supportAt (box : Box) (j : Fin 4) (corner : Fin 3)
    (i : Fin 3) (k : VertexIndex) : ℚ :=
  dotQ (box.triangle corner)
    (LocalCertificate.crossQ ((box.certificate j).edgeQ i)
      ((box.certificate j).deltaQ box i k))

/-- The selected support vertex gives an exact zero displacement. -/
def Box.exactSupportTie (box : Box) (j : Fin 4) (i : Fin 3)
    (k : VertexIndex) : Prop :=
  k = (box.certificate j).supportIndex box i

instance (box : Box) (j : Fin 4) (i : Fin 3) (k : VertexIndex) :
    Decidable (box.exactSupportTie j i k) := by
  unfold Box.exactSupportTie
  infer_instance

def supportError : ℚ := 10 * RationalApprox.κℚ

def Box.supportUpper (box : Box) (j : Fin 4) (i : Fin 3)
    (k : VertexIndex) : ℚ :=
  if box.exactSupportTie j i k then 0
  else max3 (fun corner => box.supportAt j corner i k) + supportError

def Box.weightAt (box : Box) (j : Fin 4) (corner : Fin 3)
    (i : Fin 3) : ℚ :=
  dotQ (box.triangle corner) ((box.certificate j).weightCoefficient i)

def Box.weightLower (box : Box) (j : Fin 4) (i : Fin 3) : ℚ :=
  min3 (fun corner => box.weightAt j corner i) - supportError

def Box.weightUpper (box : Box) (j : Fin 4) (i : Fin 3) : ℚ :=
  max3 (fun corner => box.weightAt j corner i) + supportError

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

/-- Reuse the denominator-cleared atlas mismatch evaluator.  Its geometric
certificate field is irrelevant to the mismatch definitions. -/
def Box.mismatchShell (box : Box) : AtlasLocalCertificate.Box where
  interval := box.interval
  chart := box.chart
  symmetryIndex := box.symmetryIndex
  certificate := fun _ => { contact := fun _ => { index := 0, direction := 0 } }
  c := box.c
  r := box.r

abbrev Box.mismatchRadius (box : Box) : ℚ := box.mismatchShell.mismatchRadius

@[mk_iff]
structure Box.ViewValid (box : Box) : Prop where
  triangle_valid : SignedTriangleValid box.root box.triangle
  c_nonneg : 0 ≤ box.c
  delta_nonneg : 0 ≤ box.δ
  r_nonneg : 0 ≤ box.r
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
  angle_bound : box.r ^ 2 * (1 + box.c ^ 2) ≤ 4 * box.c ^ 2

instance (box : Box) : Decidable box.ViewValid :=
  decidable_of_iff _ (Box.viewValid_iff box).symm

@[mk_iff]
structure Box.Valid (box : Box) : Prop where
  triangle_valid : SignedTriangleValid box.root box.triangle
  c_nonneg : 0 ≤ box.c
  delta_nonneg : 0 ≤ box.δ
  r_nonneg : 0 ≤ box.r
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
  mismatch_bound : box.mismatchRadius ≤ box.r
  angle_bound : box.r ^ 2 * (1 + box.c ^ 2) ≤ 4 * box.c ^ 2

instance (box : Box) : Decidable box.Valid :=
  decidable_of_iff _ (Box.valid_iff box).symm

theorem Box.Valid.viewValid {box : Box} (h : box.Valid) : box.ViewValid where
  triangle_valid := h.triangle_valid
  c_nonneg := h.c_nonneg
  delta_nonneg := h.delta_nonneg
  r_nonneg := h.r_nonneg
  B_pos := h.B_pos
  weight_nonneg := h.weight_nonneg
  weight_pos := h.weight_pos
  support := h.support
  direction_nonzero := h.direction_nonzero
  budget := h.budget
  variation := h.variation
  barycentric := h.barycentric
  angle_bound := h.angle_bound

theorem Box.Valid.of_viewValid {box : Box} (h : box.ViewValid)
    (hmismatch : box.mismatchRadius ≤ box.r) : box.Valid where
  triangle_valid := h.triangle_valid
  c_nonneg := h.c_nonneg
  delta_nonneg := h.delta_nonneg
  r_nonneg := h.r_nonneg
  B_pos := h.B_pos
  weight_nonneg := h.weight_nonneg
  weight_pos := h.weight_pos
  support := h.support
  direction_nonzero := h.direction_nonzero
  budget := h.budget
  variation := h.variation
  barycentric := h.barycentric
  mismatch_bound := hmismatch
  angle_bound := h.angle_bound

/-- Replace the relative-rotation box while retaining the view-local
certificate.  `ViewValid` deliberately depends on neither field. -/
def Box.retarget (box : Box) (interval : AtlasInterval ℚ)
    (chart : CayleyAtlas.ChartIndex) : Box :=
  { box with interval, chart }

theorem Box.ViewValid.retarget {box : Box} (h : box.ViewValid)
    (interval : AtlasInterval ℚ) (chart : CayleyAtlas.ChartIndex) :
    (box.retarget interval chart).ViewValid where
  triangle_valid := h.triangle_valid
  c_nonneg := h.c_nonneg
  delta_nonneg := h.delta_nonneg
  r_nonneg := h.r_nonneg
  B_pos := h.B_pos
  weight_nonneg := h.weight_nonneg
  weight_pos := h.weight_pos
  support := h.support
  direction_nonzero := h.direction_nonzero
  budget := h.budget
  variation := h.variation
  barycentric := h.barycentric
  angle_bound := h.angle_bound

noncomputable def AxisCertificate.approxVariation (box : Box)
    (cert : AxisCertificate) (n : Fin 3 → ℝ) : ℝ³ :=
  ∑ i, linearValue n (fun c => (cert.weightCoefficient i c : ℝ)) •
    cross3 (toR3 (rationalVertex (cert.supportIndex box i)))
      (cross3 (WithLp.toLp 2 n) (toR3 (cert.edgeQ i)))

theorem AxisCertificate.eval_variationPolynomial (box : Box)
    (cert : AxisCertificate) (n : Fin 3 → ℝ) (coordinate : Fin 3) :
    (cert.variationPolynomial box coordinate).evalReal
        (n 0) (n 1) (n 2) = cert.approxVariation box n coordinate := by
  fin_cases coordinate <;>
    simp [AxisCertificate.variationPolynomial,
      AxisCertificate.approxVariation, Fin.sum_univ_three,
      Noperthedron.SnubCube.ProjectiveLocalCertificate.evalReal_mulLinear,
      AxisCertificate.weightCoefficient,
      AxisCertificate.crossLiftCoefficient,
      AxisCertificate.liftCoefficient, LocalCertificate.crossQ,
      cross3, cross_apply, toR3, linearValue] <;> ring

theorem Box.triangleBalls_hold (box : Box)
    {n : Fin 3 → ℝ} (hmem : InTriangle (toReal box.triangle) n) :
    ∀ coordinate, (box.triangleBalls coordinate).Holds (n coordinate) := by
  intro coordinate
  exact RatBall.holds_of_mem_Icc
    (Noperthedron.SnubCube.ProjectiveLocalCertificate.coordinate_mem_triangleBounds
      hmem coordinate)

theorem Box.variationBall_holds (box : Box)
    {n : Fin 3 → ℝ} (hmem : InTriangle (toReal box.triangle) n)
    (j : Fin 4) (coordinate : Fin 3) :
    (box.variationBall j coordinate).Holds
      ((box.certificate j).approxVariation box n coordinate) := by
  have hvars : ∀ i, (box.triangleBalls i).Holds
      (![n 0, n 1, n 2] i) := by
    intro i
    fin_cases i
    · simpa using box.triangleBalls_hold hmem 0
    · simpa using box.triangleBalls_hold hmem 1
    · simpa using box.triangleBalls_hold hmem 2
  have h := RatQuadratic3.evalBall_holds hvars
    ((box.certificate j).variationPolynomial box coordinate)
  rw [(box.certificate j).eval_variationPolynomial] at h
  exact h

noncomputable def AxisCertificate.approxEdge
    (cert : AxisCertificate) (i : Fin 3) : ℝ³ :=
  toR3 (cert.edgeQ i)

noncomputable def AxisCertificate.exactSelectedVertex (box : Box)
    (cert : AxisCertificate) (i : Fin 3) : ℝ³ :=
  exactVertex (cert.supportIndex box i)

noncomputable def AxisCertificate.approxSelectedVertex (box : Box)
    (cert : AxisCertificate) (i : Fin 3) : ℝ³ :=
  toR3 (rationalVertex (cert.supportIndex box i))

noncomputable def AxisCertificate.exactDelta (box : Box)
    (cert : AxisCertificate) (i : Fin 3) (k : VertexIndex) : ℝ³ :=
  exactVertex k - cert.exactSelectedVertex box i

noncomputable def AxisCertificate.approxDelta (box : Box)
    (cert : AxisCertificate) (i : Fin 3) (k : VertexIndex) : ℝ³ :=
  toR3 (cert.deltaQ box i k)

theorem AxisCertificate.approxEdge_eq (cert : AxisCertificate) (i : Fin 3) :
    cert.approxEdge i =
      (cert.mixQ i : ℝ) •
          (toR3 (rationalVertex (cert.edgeStart i)) -
            toR3 (rationalVertex (cert.edgeFinish i))) +
        (1 - (cert.mixQ i : ℝ)) •
          (toR3 (rationalVertex (cert.edgeStart₂ i)) -
            toR3 (rationalVertex (cert.edgeFinish₂ i))) := by
  ext c
  simp [AxisCertificate.approxEdge, AxisCertificate.edgeQ, toR3]

theorem AxisCertificate.approxDelta_eq (box : Box)
    (cert : AxisCertificate) (i : Fin 3) (k : VertexIndex) :
    cert.approxDelta box i k = toR3 (rationalVertex k) -
      toR3 (rationalVertex (cert.supportIndex box i)) := by
  ext c
  simp [AxisCertificate.approxDelta, AxisCertificate.deltaQ, toR3]

theorem AxisCertificate.exactEdge_norm_le_two
    (cert : AxisCertificate) (i : Fin 3) : ‖cert.exactEdge i‖ ≤ 2 := by
  have hlambdaQ := cert.mixQ_nonneg i
  have hlambdaQ' := cert.mixQ_le_one i
  have hlambda : (0 : ℝ) ≤ (cert.mixQ i : ℝ) := by exact_mod_cast hlambdaQ
  have h1lambda : (0 : ℝ) ≤ 1 - (cert.mixQ i : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hlambdaQ')
  have hfirst :
      ‖exactVertex (cert.edgeStart i) - exactVertex (cert.edgeFinish i)‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      linarith [exactVertex_norm_le_one (cert.edgeStart i),
        exactVertex_norm_le_one (cert.edgeFinish i)])
  have hsecond :
      ‖exactVertex (cert.edgeStart₂ i) - exactVertex (cert.edgeFinish₂ i)‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      linarith [exactVertex_norm_le_one (cert.edgeStart₂ i),
        exactVertex_norm_le_one (cert.edgeFinish₂ i)])
  unfold AxisCertificate.exactEdge
  calc
    _ ≤ ‖(cert.mixQ i : ℝ) •
          (exactVertex (cert.edgeStart i) - exactVertex (cert.edgeFinish i))‖ +
        ‖(1 - (cert.mixQ i : ℝ)) •
          (exactVertex (cert.edgeStart₂ i) - exactVertex (cert.edgeFinish₂ i))‖ :=
      norm_add_le _ _
    _ = (cert.mixQ i : ℝ) *
          ‖exactVertex (cert.edgeStart i) - exactVertex (cert.edgeFinish i)‖ +
        (1 - (cert.mixQ i : ℝ)) *
          ‖exactVertex (cert.edgeStart₂ i) - exactVertex (cert.edgeFinish₂ i)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hlambda, abs_of_nonneg h1lambda]
    _ ≤ (cert.mixQ i : ℝ) * 2 + (1 - (cert.mixQ i : ℝ)) * 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst hlambda)
        (mul_le_mul_of_nonneg_left hsecond h1lambda)
    _ = 2 := by ring

theorem AxisCertificate.approxEdge_norm_le
    (cert : AxisCertificate) (i : Fin 3) :
    ‖cert.approxEdge i‖ ≤ 2 * (1 + RationalApprox.κ) := by
  have hlambdaQ := cert.mixQ_nonneg i
  have hlambdaQ' := cert.mixQ_le_one i
  have hlambda : (0 : ℝ) ≤ (cert.mixQ i : ℝ) := by exact_mod_cast hlambdaQ
  have h1lambda : (0 : ℝ) ≤ 1 - (cert.mixQ i : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hlambdaQ')
  have hfirst :
      ‖toR3 (rationalVertex (cert.edgeStart i)) -
          toR3 (rationalVertex (cert.edgeFinish i))‖ ≤
        2 * (1 + RationalApprox.κ) :=
    (norm_sub_le _ _).trans (by
      linarith [AtlasEdgeCertificate.norm_rationalVertex_le (cert.edgeStart i),
        AtlasEdgeCertificate.norm_rationalVertex_le (cert.edgeFinish i)])
  have hsecond :
      ‖toR3 (rationalVertex (cert.edgeStart₂ i)) -
          toR3 (rationalVertex (cert.edgeFinish₂ i))‖ ≤
        2 * (1 + RationalApprox.κ) :=
    (norm_sub_le _ _).trans (by
      linarith [AtlasEdgeCertificate.norm_rationalVertex_le (cert.edgeStart₂ i),
        AtlasEdgeCertificate.norm_rationalVertex_le (cert.edgeFinish₂ i)])
  rw [cert.approxEdge_eq]
  calc
    _ ≤ ‖(cert.mixQ i : ℝ) •
          (toR3 (rationalVertex (cert.edgeStart i)) -
            toR3 (rationalVertex (cert.edgeFinish i)))‖ +
        ‖(1 - (cert.mixQ i : ℝ)) •
          (toR3 (rationalVertex (cert.edgeStart₂ i)) -
            toR3 (rationalVertex (cert.edgeFinish₂ i)))‖ := norm_add_le _ _
    _ = (cert.mixQ i : ℝ) *
          ‖toR3 (rationalVertex (cert.edgeStart i)) -
            toR3 (rationalVertex (cert.edgeFinish i))‖ +
        (1 - (cert.mixQ i : ℝ)) *
          ‖toR3 (rationalVertex (cert.edgeStart₂ i)) -
            toR3 (rationalVertex (cert.edgeFinish₂ i))‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hlambda, abs_of_nonneg h1lambda]
    _ ≤ (cert.mixQ i : ℝ) * (2 * (1 + RationalApprox.κ)) +
        (1 - (cert.mixQ i : ℝ)) * (2 * (1 + RationalApprox.κ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst hlambda)
        (mul_le_mul_of_nonneg_left hsecond h1lambda)
    _ = 2 * (1 + RationalApprox.κ) := by ring

theorem AxisCertificate.exactEdge_sub_approx_norm_le
    (cert : AxisCertificate) (i : Fin 3) :
    ‖cert.exactEdge i - cert.approxEdge i‖ ≤ 2 * RationalApprox.κ := by
  have hlambdaQ := cert.mixQ_nonneg i
  have hlambdaQ' := cert.mixQ_le_one i
  have hlambda : (0 : ℝ) ≤ (cert.mixQ i : ℝ) := by exact_mod_cast hlambdaQ
  have h1lambda : (0 : ℝ) ≤ 1 - (cert.mixQ i : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hlambdaQ')
  rw [cert.approxEdge_eq]
  have hrearrange :
      cert.exactEdge i -
          ((cert.mixQ i : ℝ) •
              (toR3 (rationalVertex (cert.edgeStart i)) -
                toR3 (rationalVertex (cert.edgeFinish i))) +
            (1 - (cert.mixQ i : ℝ)) •
              (toR3 (rationalVertex (cert.edgeStart₂ i)) -
                toR3 (rationalVertex (cert.edgeFinish₂ i)))) =
        (cert.mixQ i : ℝ) •
            ((exactVertex (cert.edgeStart i) -
                toR3 (rationalVertex (cert.edgeStart i))) -
              (exactVertex (cert.edgeFinish i) -
                toR3 (rationalVertex (cert.edgeFinish i)))) +
          (1 - (cert.mixQ i : ℝ)) •
            ((exactVertex (cert.edgeStart₂ i) -
                toR3 (rationalVertex (cert.edgeStart₂ i))) -
              (exactVertex (cert.edgeFinish₂ i) -
                toR3 (rationalVertex (cert.edgeFinish₂ i)))) := by
    unfold AxisCertificate.exactEdge
    simp only [smul_sub]
    abel
  rw [hrearrange]
  have hfirst :
      ‖(exactVertex (cert.edgeStart i) -
            toR3 (rationalVertex (cert.edgeStart i))) -
          (exactVertex (cert.edgeFinish i) -
            toR3 (rationalVertex (cert.edgeFinish i)))‖ ≤
        2 * RationalApprox.κ := by
    calc
      _ ≤ ‖exactVertex (cert.edgeStart i) -
            toR3 (rationalVertex (cert.edgeStart i))‖ +
          ‖exactVertex (cert.edgeFinish i) -
            toR3 (rationalVertex (cert.edgeFinish i))‖ := norm_sub_le _ _
      _ ≤ RationalApprox.κ + RationalApprox.κ := add_le_add
        (exactApproximation.approx (cert.edgeStart i))
        (exactApproximation.approx (cert.edgeFinish i))
      _ = 2 * RationalApprox.κ := by ring
  have hsecond :
      ‖(exactVertex (cert.edgeStart₂ i) -
            toR3 (rationalVertex (cert.edgeStart₂ i))) -
          (exactVertex (cert.edgeFinish₂ i) -
            toR3 (rationalVertex (cert.edgeFinish₂ i)))‖ ≤
        2 * RationalApprox.κ := by
    calc
      _ ≤ ‖exactVertex (cert.edgeStart₂ i) -
            toR3 (rationalVertex (cert.edgeStart₂ i))‖ +
          ‖exactVertex (cert.edgeFinish₂ i) -
            toR3 (rationalVertex (cert.edgeFinish₂ i))‖ := norm_sub_le _ _
      _ ≤ RationalApprox.κ + RationalApprox.κ := add_le_add
        (exactApproximation.approx (cert.edgeStart₂ i))
        (exactApproximation.approx (cert.edgeFinish₂ i))
      _ = 2 * RationalApprox.κ := by ring
  calc
    _ ≤ ‖(cert.mixQ i : ℝ) •
          ((exactVertex (cert.edgeStart i) -
              toR3 (rationalVertex (cert.edgeStart i))) -
            (exactVertex (cert.edgeFinish i) -
              toR3 (rationalVertex (cert.edgeFinish i))))‖ +
        ‖(1 - (cert.mixQ i : ℝ)) •
          ((exactVertex (cert.edgeStart₂ i) -
              toR3 (rationalVertex (cert.edgeStart₂ i))) -
            (exactVertex (cert.edgeFinish₂ i) -
              toR3 (rationalVertex (cert.edgeFinish₂ i))))‖ := norm_add_le _ _
    _ = (cert.mixQ i : ℝ) * _ + (1 - (cert.mixQ i : ℝ)) * _ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hlambda, abs_of_nonneg h1lambda]
    _ ≤ (cert.mixQ i : ℝ) * (2 * RationalApprox.κ) +
        (1 - (cert.mixQ i : ℝ)) * (2 * RationalApprox.κ) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst hlambda)
        (mul_le_mul_of_nonneg_left hsecond h1lambda)
    _ = 2 * RationalApprox.κ := by ring

theorem AxisCertificate.exactSelectedVertex_norm_le_one (box : Box)
    (cert : AxisCertificate) (i : Fin 3) :
    ‖cert.exactSelectedVertex box i‖ ≤ 1 :=
  exactVertex_norm_le_one (cert.supportIndex box i)

theorem AxisCertificate.approxSelectedVertex_norm_le (box : Box)
    (cert : AxisCertificate) (i : Fin 3) :
    ‖cert.approxSelectedVertex box i‖ ≤ 1 + RationalApprox.κ :=
  AtlasEdgeCertificate.norm_rationalVertex_le (cert.supportIndex box i)

theorem AxisCertificate.exactSelectedVertex_sub_approx_norm_le (box : Box)
    (cert : AxisCertificate) (i : Fin 3) :
    ‖cert.exactSelectedVertex box i - cert.approxSelectedVertex box i‖ ≤
      RationalApprox.κ :=
  exactApproximation.approx (cert.supportIndex box i)

noncomputable def normalizedView3 (box : Box) (p : AtlasPose ℝ) : ℝ³ :=
  WithLp.toLp 2 (AtlasProjectiveView.normalizedView box.root p)

theorem normalizedView3_norm_le_one (box : Box) (p : AtlasPose ℝ)
    (hscale : 1 ≤ viewScale box.root p) :
    ‖normalizedView3 box p‖ ≤ 1 := by
  have hpos : 0 < viewScale box.root p := lt_of_lt_of_le (by norm_num) hscale
  have heq : normalizedView3 box p =
      (viewScale box.root p)⁻¹ • AtlasEdgeCertificate.viewVector p := by
    ext i
    simp [normalizedView3, AtlasProjectiveView.normalizedView,
      smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq, norm_smul, AtlasEdgeCertificate.viewVector_norm,
    mul_one, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
  exact (inv_le_one₀ (by positivity)).2 hscale

theorem AxisCertificate.exactDelta_norm_le_two (box : Box)
    (cert : AxisCertificate) (i : Fin 3) (k : VertexIndex) :
    ‖cert.exactDelta box i k‖ ≤ 2 := by
  unfold AxisCertificate.exactDelta
  exact (norm_sub_le _ _).trans (by
    linarith [exactVertex_norm_le_one k,
      cert.exactSelectedVertex_norm_le_one box i])

theorem AxisCertificate.approxDelta_norm_le (box : Box)
    (cert : AxisCertificate) (i : Fin 3) (k : VertexIndex) :
    ‖cert.approxDelta box i k‖ ≤ 2 * (1 + RationalApprox.κ) := by
  rw [cert.approxDelta_eq]
  exact (norm_sub_le _ _).trans (by
    linarith [AtlasEdgeCertificate.norm_rationalVertex_le k,
      AtlasEdgeCertificate.norm_rationalVertex_le (cert.supportIndex box i)])

theorem AxisCertificate.exactDelta_sub_approx_norm_le (box : Box)
    (cert : AxisCertificate) (i : Fin 3) (k : VertexIndex) :
    ‖cert.exactDelta box i k - cert.approxDelta box i k‖ ≤
      2 * RationalApprox.κ := by
  rw [cert.approxDelta_eq]
  have hrearrange : cert.exactDelta box i k -
        (toR3 (rationalVertex k) -
          toR3 (rationalVertex (cert.supportIndex box i))) =
      (exactVertex k - toR3 (rationalVertex k)) -
        (exactVertex (cert.supportIndex box i) -
          toR3 (rationalVertex (cert.supportIndex box i))) := by
    unfold AxisCertificate.exactDelta AxisCertificate.exactSelectedVertex
    abel
  rw [hrearrange]
  calc
    _ ≤ ‖exactVertex k - toR3 (rationalVertex k)‖ +
        ‖exactVertex (cert.supportIndex box i) -
          toR3 (rationalVertex (cert.supportIndex box i))‖ := norm_sub_le _ _
    _ ≤ RationalApprox.κ + RationalApprox.κ := add_le_add
      (exactApproximation.approx k)
      (exactApproximation.approx (cert.supportIndex box i))
    _ = 2 * RationalApprox.κ := by ring

theorem AxisCertificate.supportCross_error (box : Box)
    (cert : AxisCertificate) (i : Fin 3) (k : VertexIndex) :
    ‖cross3 (cert.exactEdge i) (cert.exactDelta box i k) -
        cross3 (cert.approxEdge i) (cert.approxDelta box i k)‖ ≤
      10 * RationalApprox.κ := by
  have hdecomp :
      cross3 (cert.exactEdge i) (cert.exactDelta box i k) -
          cross3 (cert.approxEdge i) (cert.approxDelta box i k) =
        cross3 (cert.exactEdge i - cert.approxEdge i)
            (cert.exactDelta box i k) +
          cross3 (cert.approxEdge i)
            (cert.exactDelta box i k - cert.approxDelta box i k) := by
    ext coordinate
    fin_cases coordinate <;> simp [cross3, cross_apply] <;> ring
  rw [hdecomp]
  calc
    _ ≤ ‖cross3 (cert.exactEdge i - cert.approxEdge i)
          (cert.exactDelta box i k)‖ +
        ‖cross3 (cert.approxEdge i)
          (cert.exactDelta box i k - cert.approxDelta box i k)‖ :=
      norm_add_le _ _
    _ ≤ (2 * RationalApprox.κ) * 2 +
        (2 * (1 + RationalApprox.κ)) *
          (2 * RationalApprox.κ) := by
      exact add_le_add
        ((cross3_norm_le _ _).trans (mul_le_mul
          (cert.exactEdge_sub_approx_norm_le i)
          (cert.exactDelta_norm_le_two box i k) (norm_nonneg _)
          (by norm_num [RationalApprox.κ])))
        ((cross3_norm_le _ _).trans (mul_le_mul
          (cert.approxEdge_norm_le i)
          (cert.exactDelta_sub_approx_norm_le box i k) (norm_nonneg _)
          (by norm_num [RationalApprox.κ])))
    _ ≤ 10 * RationalApprox.κ := by
      norm_num [RationalApprox.κ]

noncomputable def AxisCertificate.approxSupport (box : Box)
    (cert : AxisCertificate) (n : Fin 3 → ℝ)
    (i : Fin 3) (k : VertexIndex) : ℝ :=
  linearValue n (cross3 (cert.approxEdge i) (cert.approxDelta box i k))

noncomputable def AxisCertificate.exactSupport (box : Box)
    (cert : AxisCertificate) (p : AtlasPose ℝ)
    (i : Fin 3) (k : VertexIndex) : ℝ :=
  linearValue (AtlasProjectiveView.normalizedView box.root p)
    (cross3 (cert.exactEdge i) (cert.exactDelta box i k))

theorem linearValue_eq_inner_toLp (n : Fin 3 → ℝ) (v : ℝ³) :
    linearValue n v = inner ℝ (WithLp.toLp 2 n) v := by
  simp [linearValue, PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem linearValue_cast_eq_inner_toR3 (n : Fin 3 → ℝ)
    (q : Fin 3 → ℚ) :
    linearValue n (fun c => (q c : ℝ)) =
      inner ℝ (WithLp.toLp 2 n) (toR3 q) := by
  simp [linearValue, PiLp.inner_apply, Fin.sum_univ_three, toR3]
  ring

theorem Box.supportAt_cast (box : Box) (j : Fin 4)
    (corner : Fin 3) (i : Fin 3) (k : VertexIndex) :
    (box.supportAt j corner i k : ℝ) =
      (box.certificate j).approxSupport box (toReal box.triangle corner) i k := by
  simp [Box.supportAt, AxisCertificate.approxSupport, dotQ, linearValue,
    toReal, AxisCertificate.approxEdge, AxisCertificate.approxDelta,
    LocalCertificate.crossQ, cross3, cross_apply, toR3]

theorem Box.approxSupport_le_max (box : Box) {p : AtlasPose ℝ}
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (j : Fin 4) (i : Fin 3) (k : VertexIndex) :
    (box.certificate j).approxSupport box
        (AtlasProjectiveView.normalizedView box.root p) i k ≤
      (max3 (fun corner => box.supportAt j corner i k) : ℝ) := by
  unfold AxisCertificate.approxSupport
  apply linearValue_le_of_mem hmem
  intro corner
  change (box.certificate j).approxSupport box
    (toReal box.triangle corner) i k ≤ _
  rw [← box.supportAt_cast j corner i k]
  exact_mod_cast le_max3 (fun c => box.supportAt j c i k) corner

theorem AxisCertificate.exactSupport_sub_approx_abs_le (box : Box)
    (cert : AxisCertificate) {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p) (i : Fin 3) (k : VertexIndex) :
    |cert.exactSupport box p i k -
        cert.approxSupport box
          (AtlasProjectiveView.normalizedView box.root p) i k| ≤
      (supportError : ℝ) := by
  rw [AxisCertificate.exactSupport, AxisCertificate.approxSupport,
    linearValue_eq_inner_toLp, linearValue_eq_inner_toLp,
    ← inner_sub_right]
  calc
    _ ≤ ‖normalizedView3 box p‖ *
        ‖cross3 (cert.exactEdge i) (cert.exactDelta box i k) -
          cross3 (cert.approxEdge i) (cert.approxDelta box i k)‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ 10 * RationalApprox.κ := by
      exact (mul_le_mul_of_nonneg_left (cert.supportCross_error box i k)
        (norm_nonneg _)).trans
          (mul_le_of_le_one_left
            (by norm_num [RationalApprox.κ])
            (normalizedView3_norm_le_one box p hscale))
    _ = (supportError : ℝ) := by
      norm_num [supportError, RationalApprox.κ, RationalApprox.κℚ]

theorem Box.exactSupport_eq_zero_of_tie (box : Box) {p : AtlasPose ℝ}
    (j : Fin 4) (i : Fin 3) (k : VertexIndex)
    (htie : box.exactSupportTie j i k) :
    (box.certificate j).exactSupport box p i k = 0 := by
  subst k
  have hdelta :
      (box.certificate j).exactDelta box i
          ((box.certificate j).supportIndex box i) = 0 := by
    simp [AxisCertificate.exactDelta, AxisCertificate.exactSelectedVertex]
  unfold AxisCertificate.exactSupport
  rw [hdelta]
  simp [linearValue, cross3]

theorem Box.exactSupport_le_upper (box : Box)
    {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (j : Fin 4) (i : Fin 3) (k : VertexIndex) :
    (box.certificate j).exactSupport box p i k ≤
      (box.supportUpper j i k : ℝ) := by
  by_cases hk : box.exactSupportTie j i k
  · rw [box.exactSupport_eq_zero_of_tie j i k hk]
    simp [Box.supportUpper, hk]
  · have happ := box.approxSupport_le_max hmem j i k
    have herr := (box.certificate j).exactSupport_sub_approx_abs_le
      box hscale i k
    rw [abs_le] at herr
    simp only [Box.supportUpper, if_neg hk]
    change _ ≤ ((max3 (fun corner => box.supportAt j corner i k) +
      supportError : ℚ) : ℝ)
    push_cast
    linarith [herr.2]

theorem Box.valid_support (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (j : Fin 4) (i : Fin 3) (k : VertexIndex) :
    inner ℝ (direction box.root p ((box.certificate j).exactEdge i))
        (outerProjectionLinear (p.matrixPoseWithOffset box.chart offset)
          (exactVertex k)) ≤
      inner ℝ (direction box.root p ((box.certificate j).exactEdge i))
        (outerProjectionLinear (p.matrixPoseWithOffset box.chart offset)
          (exactVertex ((box.certificate j).supportIndex box i))) := by
  have hscaleNe :=
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hscale).ne'
  have hupper := box.exactSupport_le_upper hscale hmem j i k
  have hchecked := h.support j i k
  have hsigned : (box.certificate j).exactSupport box p i k ≤ 0 :=
    hupper.trans (by exact_mod_cast hchecked)
  have hdiff :
      inner ℝ (direction box.root p ((box.certificate j).exactEdge i))
          ((outerProjectionLinear (p.matrixPoseWithOffset box.chart offset))
            (exactVertex k) -
          (outerProjectionLinear (p.matrixPoseWithOffset box.chart offset))
            (exactVertex ((box.certificate j).supportIndex box i))) =
        (box.certificate j).exactSupport box p i k := by
    rw [← map_sub,
      inner_direction_outerProjection_eq_support box.root p box.chart offset
        _ _ hscaleNe]
    rfl
  rw [inner_sub_right] at hdiff
  linarith

theorem Box.valid_direction_nonzero (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (j : Fin 4) (i : Fin 3) :
    direction box.root p ((box.certificate j).exactEdge i) ≠ 0 := by
  intro hzero
  let k := (box.certificate j).nonzeroWitness i
  have hupper := box.exactSupport_le_upper hscale hmem j i k
  have hstrict : (box.supportUpper j i k : ℝ) < 0 := by
    exact_mod_cast h.direction_nonzero j i
  have hexact : (box.certificate j).exactSupport box p i k < 0 :=
    hupper.trans_lt hstrict
  have hscaleNe :=
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hscale).ne'
  have heq := inner_direction_outerProjection_eq_support box.root p
    box.chart offset ((box.certificate j).exactEdge i)
    ((box.certificate j).exactDelta box i k) hscaleNe
  rw [hzero, inner_zero_left] at heq
  change linearValue (AtlasProjectiveView.normalizedView box.root p)
    (cross3 ((box.certificate j).exactEdge i)
      ((box.certificate j).exactDelta box i k)) < 0 at hexact
  rw [← heq] at hexact
  linarith

noncomputable def AxisCertificate.approxWeight (cert : AxisCertificate)
    (n : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  linearValue n (fun c => (cert.weightCoefficient i c : ℝ))

noncomputable def AxisCertificate.exactWeight (box : Box)
    (cert : AxisCertificate) (p : AtlasPose ℝ) (i : Fin 3) : ℝ :=
  weight box.root p (fun j => cert.exactEdge j) i

theorem toR3_crossQ (a b : Fin 3 → ℚ) :
    toR3 (LocalCertificate.crossQ a b) = cross3 (toR3 a) (toR3 b) := by
  ext c
  fin_cases c <;>
    simp [LocalCertificate.crossQ, cross3, cross_apply, toR3]

theorem AxisCertificate.approxWeightVector_eq (cert : AxisCertificate)
    (i : Fin 3) :
    toR3 (cert.weightCoefficient i) =
      match i with
      | 0 => cross3 (cert.approxEdge 1) (cert.approxEdge 2)
      | 1 => cross3 (cert.approxEdge 2) (cert.approxEdge 0)
      | 2 => cross3 (cert.approxEdge 0) (cert.approxEdge 1) := by
  fin_cases i <;>
    simp [AxisCertificate.weightCoefficient, AxisCertificate.approxEdge,
      toR3_crossQ]

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

theorem AxisCertificate.exactWeight_sub_approx_abs_le (box : Box)
    (cert : AxisCertificate) {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p) (i : Fin 3) :
    |cert.exactWeight box p i - cert.approxWeight
        (AtlasProjectiveView.normalizedView box.root p) i| ≤
      10 * RationalApprox.κ := by
  have hn := normalizedView3_norm_le_one box p hscale
  fin_cases i
  all_goals
    simp [AxisCertificate.exactWeight, weight,
      AxisCertificate.approxWeight]
    rw [linearValue_eq_inner_toLp, linearValue_cast_eq_inner_toR3]
    change |⟪normalizedView3 box p, _⟫ -
      ⟪normalizedView3 box p, toR3 (cert.weightCoefficient _)⟫| ≤ _
    rw [cert.approxWeightVector_eq]
    rw [← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left (cert.crossEdge_error _ _)
        (norm_nonneg _)).trans
          (mul_le_of_le_one_left
            (by norm_num [RationalApprox.κ]) hn))

theorem Box.weightAt_cast (box : Box) (j : Fin 4)
    (corner : Fin 3) (i : Fin 3) :
    (box.weightAt j corner i : ℝ) =
      (box.certificate j).approxWeight (toReal box.triangle corner) i := by
  simp [Box.weightAt, AxisCertificate.approxWeight, dotQ,
    linearValue, toReal]

theorem Box.weightLower_le_exact (box : Box)
    {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (j : Fin 4) (i : Fin 3) :
    (box.weightLower j i : ℝ) ≤
      (box.certificate j).exactWeight box p i := by
  have hmin : (min3 (fun corner => box.weightAt j corner i) : ℝ) ≤
      (box.certificate j).approxWeight
        (AtlasProjectiveView.normalizedView box.root p) i := by
    unfold AxisCertificate.approxWeight
    apply le_linearValue_of_mem hmem
    intro corner
    change (min3 (fun c => box.weightAt j c i) : ℝ) ≤
      (box.certificate j).approxWeight (toReal box.triangle corner) i
    rw [← box.weightAt_cast j corner i]
    exact_mod_cast min3_le (fun c => box.weightAt j c i) corner
  have herr := (box.certificate j).exactWeight_sub_approx_abs_le
    box hscale i
  rw [abs_le] at herr
  have herrorEq : (10 * RationalApprox.κ : ℝ) = (supportError : ℝ) := by
    norm_num [supportError, RationalApprox.κ, RationalApprox.κℚ]
  simp only [Box.weightLower]
  push_cast
  rw [herrorEq] at herr
  linarith [herr.1]

theorem Box.exactWeight_le_upper (box : Box)
    {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (j : Fin 4) (i : Fin 3) :
    (box.certificate j).exactWeight box p i ≤
      (box.weightUpper j i : ℝ) := by
  have hmax :
      (box.certificate j).approxWeight
          (AtlasProjectiveView.normalizedView box.root p) i ≤
        (max3 (fun corner => box.weightAt j corner i) : ℝ) := by
    unfold AxisCertificate.approxWeight
    apply linearValue_le_of_mem hmem
    intro corner
    change (box.certificate j).approxWeight
      (toReal box.triangle corner) i ≤ _
    rw [← box.weightAt_cast j corner i]
    exact_mod_cast le_max3 (fun c => box.weightAt j c i) corner
  have herr := (box.certificate j).exactWeight_sub_approx_abs_le
    box hscale i
  rw [abs_le] at herr
  have herrorEq : (10 * RationalApprox.κ : ℝ) = (supportError : ℝ) := by
    norm_num [supportError, RationalApprox.κ, RationalApprox.κℚ]
  simp only [Box.weightUpper]
  push_cast
  rw [herrorEq] at herr
  linarith [herr.2, hmax]

theorem Box.valid_weight_nonneg (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (j : Fin 4) (i : Fin 3) :
    0 ≤ (box.certificate j).exactWeight box p i := by
  have hlower : (0 : ℝ) ≤ (box.weightLower j i : ℝ) := by
    exact_mod_cast h.weight_nonneg j i
  exact hlower.trans (box.weightLower_le_exact hscale hmem j i)

theorem Box.valid_weight_pos (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (j : Fin 4) :
    ∃ i, 0 < (box.certificate j).exactWeight box p i := by
  obtain ⟨i, hi⟩ := h.weight_pos j
  refine ⟨i, ?_⟩
  have hiReal : (0 : ℝ) < (box.weightLower j i : ℝ) := by
    exact_mod_cast hi
  exact hiReal.trans_le (box.weightLower_le_exact hscale hmem j i)

theorem AxisCertificate.exactWeight_abs_le_four (box : Box)
    (cert : AxisCertificate) {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p) (i : Fin 3) :
    |cert.exactWeight box p i| ≤ 4 := by
  have hn := normalizedView3_norm_le_one box p hscale
  fin_cases i
  all_goals
    simp [AxisCertificate.exactWeight, weight]
    rw [linearValue_eq_inner_toLp]
    apply (abs_real_inner_le_norm _ _).trans
    apply (mul_le_mul hn (cross3_norm_le _ _) (norm_nonneg _)
      (by positivity)).trans
    rw [one_mul]
    apply (mul_le_mul (cert.exactEdge_norm_le_two _)
      (cert.exactEdge_norm_le_two _) (norm_nonneg _) (by norm_num)).trans
    norm_num

theorem AxisCertificate.approxWeight_abs_le (box : Box)
    (cert : AxisCertificate) {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p) (i : Fin 3) :
    |cert.approxWeight (AtlasProjectiveView.normalizedView box.root p) i| ≤
      4 + 10 * RationalApprox.κ := by
  have herr := cert.exactWeight_sub_approx_abs_le box hscale i
  have hexact := cert.exactWeight_abs_le_four box hscale i
  calc
    _ ≤ |cert.exactWeight box p i| +
        |cert.exactWeight box p i - cert.approxWeight
          (AtlasProjectiveView.normalizedView box.root p) i| := by
      have htriangle := abs_add_le (cert.exactWeight box p i)
        (cert.approxWeight (AtlasProjectiveView.normalizedView box.root p) i -
          cert.exactWeight box p i)
      rw [add_sub_cancel] at htriangle
      simpa [abs_sub_comm] using htriangle
    _ ≤ 4 + 10 * RationalApprox.κ := add_le_add hexact herr

noncomputable def AxisCertificate.exactLift (box : Box)
    (cert : AxisCertificate) (p : AtlasPose ℝ) (i : Fin 3) : ℝ³ :=
  cross3 (normalizedView3 box p) (cert.exactEdge i)

noncomputable def AxisCertificate.approxLift (box : Box)
    (cert : AxisCertificate) (p : AtlasPose ℝ) (i : Fin 3) : ℝ³ :=
  cross3 (normalizedView3 box p) (cert.approxEdge i)

theorem AxisCertificate.exactLift_sub_approx_eq (box : Box)
    (cert : AxisCertificate) (p : AtlasPose ℝ) (i : Fin 3) :
    cert.exactLift box p i - cert.approxLift box p i =
      cross3 (normalizedView3 box p)
        (cert.exactEdge i - cert.approxEdge i) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [AxisCertificate.exactLift, AxisCertificate.approxLift,
      cross3, cross_apply] <;> ring

theorem AxisCertificate.exactLift_sub_approx_norm_le (box : Box)
    (cert : AxisCertificate) {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p) (i : Fin 3) :
    ‖cert.exactLift box p i - cert.approxLift box p i‖ ≤
      2 * RationalApprox.κ := by
  rw [cert.exactLift_sub_approx_eq]
  exact (cross3_norm_le _ _).trans
    ((mul_le_mul (normalizedView3_norm_le_one box p hscale)
      (cert.exactEdge_sub_approx_norm_le i) (norm_nonneg _)
      (by norm_num [RationalApprox.κ])).trans (by ring_nf; rfl))

theorem AxisCertificate.exactLift_norm_le_two (box : Box)
    (cert : AxisCertificate) {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p) (i : Fin 3) :
    ‖cert.exactLift box p i‖ ≤ 2 := by
  unfold AxisCertificate.exactLift
  exact (cross3_norm_le _ _).trans
    ((mul_le_mul (normalizedView3_norm_le_one box p hscale)
      (cert.exactEdge_norm_le_two i) (norm_nonneg _)
      (by positivity)).trans (by norm_num))

theorem AxisCertificate.approxLift_norm_le (box : Box)
    (cert : AxisCertificate) {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p) (i : Fin 3) :
    ‖cert.approxLift box p i‖ ≤ 2 * (1 + RationalApprox.κ) := by
  unfold AxisCertificate.approxLift
  exact (cross3_norm_le _ _).trans
    ((mul_le_mul (normalizedView3_norm_le_one box p hscale)
      (cert.approxEdge_norm_le i) (norm_nonneg _)
      (by norm_num [RationalApprox.κ])).trans (by ring_nf; rfl))

noncomputable def AxisCertificate.exactCross (box : Box)
    (cert : AxisCertificate) (p : AtlasPose ℝ) (i : Fin 3) : ℝ³ :=
  cross3 (cert.exactSelectedVertex box i) (cert.exactLift box p i)

noncomputable def AxisCertificate.approxCross (box : Box)
    (cert : AxisCertificate) (p : AtlasPose ℝ) (i : Fin 3) : ℝ³ :=
  cross3 (cert.approxSelectedVertex box i) (cert.approxLift box p i)

theorem AxisCertificate.exactCross_norm_le_two (box : Box)
    (cert : AxisCertificate) {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p) (i : Fin 3) :
    ‖cert.exactCross box p i‖ ≤ 2 := by
  unfold AxisCertificate.exactCross
  exact (cross3_norm_le _ _).trans
    ((mul_le_mul (cert.exactSelectedVertex_norm_le_one box i)
      (cert.exactLift_norm_le_two box hscale i) (norm_nonneg _)
      (by positivity)).trans (by norm_num))

theorem AxisCertificate.exactCross_sub_approx_norm_le (box : Box)
    (cert : AxisCertificate) {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p) (i : Fin 3) :
    ‖cert.exactCross box p i - cert.approxCross box p i‖ ≤
      5 * RationalApprox.κ := by
  have hdecomp : cert.exactCross box p i - cert.approxCross box p i =
      cross3 (cert.exactSelectedVertex box i)
          (cert.exactLift box p i - cert.approxLift box p i) +
        cross3 (cert.exactSelectedVertex box i -
            cert.approxSelectedVertex box i)
          (cert.approxLift box p i) := by
    unfold AxisCertificate.exactCross AxisCertificate.approxCross
    rw [cross3_sub_cross3]
  rw [hdecomp]
  calc
    _ ≤ ‖cross3 (cert.exactSelectedVertex box i)
          (cert.exactLift box p i - cert.approxLift box p i)‖ +
        ‖cross3 (cert.exactSelectedVertex box i -
            cert.approxSelectedVertex box i)
          (cert.approxLift box p i)‖ := norm_add_le _ _
    _ ≤ 1 * (2 * RationalApprox.κ) +
        RationalApprox.κ * (2 * (1 + RationalApprox.κ)) := by
      exact add_le_add
        ((cross3_norm_le _ _).trans (mul_le_mul
          (cert.exactSelectedVertex_norm_le_one box i)
          (cert.exactLift_sub_approx_norm_le box hscale i)
          (norm_nonneg _) (by norm_num [RationalApprox.κ])))
        ((cross3_norm_le _ _).trans (mul_le_mul
          (cert.exactSelectedVertex_sub_approx_norm_le box i)
          (cert.approxLift_norm_le box hscale i)
          (norm_nonneg _) (by norm_num [RationalApprox.κ])))
    _ ≤ 5 * RationalApprox.κ := by
      norm_num [RationalApprox.κ]

theorem AxisCertificate.approxVariation_eq_sum_approxCross (box : Box)
    (cert : AxisCertificate) (p : AtlasPose ℝ) :
    cert.approxVariation box
        (AtlasProjectiveView.normalizedView box.root p) =
      ∑ i, cert.approxWeight
          (AtlasProjectiveView.normalizedView box.root p) i •
        cert.approxCross box p i := by
  unfold AxisCertificate.approxVariation AxisCertificate.approxWeight
  unfold AxisCertificate.approxCross AxisCertificate.approxLift
  rfl

theorem AxisCertificate.variation_error (box : Box)
    (cert : AxisCertificate) {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p) :
    ‖variationVector box.root p (fun i => cert.exactEdge i)
          (fun i => cert.exactSelectedVertex box i) -
        cert.approxVariation box
          (AtlasProjectiveView.normalizedView box.root p)‖ ≤
      (variationError : ℝ) := by
  rw [cert.approxVariation_eq_sum_approxCross]
  unfold variationVector
  change ‖(∑ i, cert.exactWeight box p i • cert.exactCross box p i) -
      ∑ i, cert.approxWeight
          (AtlasProjectiveView.normalizedView box.root p) i •
        cert.approxCross box p i‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    ∑ i, ‖cert.exactWeight box p i • cert.exactCross box p i -
        cert.approxWeight
            (AtlasProjectiveView.normalizedView box.root p) i •
          cert.approxCross box p i‖ ≤
        ∑ _i : Fin 3, 50 * RationalApprox.κ := by
      apply Finset.sum_le_sum
      intro i _
      have hdecomp :
          cert.exactWeight box p i • cert.exactCross box p i -
              cert.approxWeight
                  (AtlasProjectiveView.normalizedView box.root p) i •
                cert.approxCross box p i =
            (cert.exactWeight box p i - cert.approxWeight
                (AtlasProjectiveView.normalizedView box.root p) i) •
              cert.exactCross box p i +
            cert.approxWeight
                (AtlasProjectiveView.normalizedView box.root p) i •
              (cert.exactCross box p i - cert.approxCross box p i) := by
        module
      rw [hdecomp]
      calc
        _ ≤ ‖(cert.exactWeight box p i - cert.approxWeight
                (AtlasProjectiveView.normalizedView box.root p) i) •
              cert.exactCross box p i‖ +
            ‖cert.approxWeight
                (AtlasProjectiveView.normalizedView box.root p) i •
              (cert.exactCross box p i - cert.approxCross box p i)‖ :=
          norm_add_le _ _
        _ ≤ (10 * RationalApprox.κ) * 2 +
            (4 + 10 * RationalApprox.κ) *
              (5 * RationalApprox.κ) := by
          simp only [norm_smul, Real.norm_eq_abs]
          exact add_le_add
            (mul_le_mul
              (cert.exactWeight_sub_approx_abs_le box hscale i)
              (cert.exactCross_norm_le_two box hscale i)
              (norm_nonneg _) (by norm_num [RationalApprox.κ]))
            (mul_le_mul
              (cert.approxWeight_abs_le box hscale i)
              (cert.exactCross_sub_approx_norm_le box hscale i)
              (norm_nonneg _) (by norm_num [RationalApprox.κ]))
        _ ≤ 50 * RationalApprox.κ := by
          norm_num [RationalApprox.κ]
    _ = (variationError : ℝ) := by
      simp [Fin.sum_univ_three, variationError]
      norm_num [RationalApprox.κ, RationalApprox.κℚ]

def Box.variationCenterQ (box : Box) (j : Fin 4) : VectorQ :=
  fun coordinate => (box.variationBall j coordinate).center

noncomputable def Box.variationCenter (box : Box) (j : Fin 4) : ℝ³ :=
  toR3 (box.variationCenterQ j)

theorem Box.exactVariation_coordinate_error (box : Box)
    {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (j : Fin 4) (coordinate : Fin 3) :
    |variationVector box.root p
          (fun i => (box.certificate j).exactEdge i)
          (fun i => (box.certificate j).exactSelectedVertex box i) coordinate -
        box.variationCenter j coordinate| ≤
      ((box.variationBall j coordinate).radius : ℝ) +
        (variationError : ℝ) := by
  let cert := box.certificate j
  let exact := variationVector box.root p (fun i => cert.exactEdge i)
    (fun i => cert.exactSelectedVertex box i)
  let approx := cert.approxVariation box
    (AtlasProjectiveView.normalizedView box.root p)
  have hvariation := cert.variation_error box hscale
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
    _ = _ := by ring

theorem Box.exactVariation_sub_center_norm_le (box : Box)
    {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (j : Fin 4) :
    ‖variationVector box.root p
          (fun i => (box.certificate j).exactEdge i)
          (fun i => (box.certificate j).exactSelectedVertex box i) -
        box.variationCenter j‖ ≤
      (box.variationRadiusSum j : ℝ) + 3 * (variationError : ℝ) := by
  let diff := variationVector box.root p
      (fun i => (box.certificate j).exactEdge i)
      (fun i => (box.certificate j).exactSelectedVertex box i) -
    box.variationCenter j
  apply (Noperthedron.SnubCube.ProjectiveLocalCertificate.norm_le_sum_abs_coordinates
    diff).trans
  have h0 := box.exactVariation_coordinate_error hscale hmem j 0
  have h1 := box.exactVariation_coordinate_error hscale hmem j 1
  have h2 := box.exactVariation_coordinate_error hscale hmem j 2
  change |diff 0| ≤ ((box.variationBall j 0).radius : ℝ) +
    (variationError : ℝ) at h0
  change |diff 1| ≤ ((box.variationBall j 1).radius : ℝ) +
    (variationError : ℝ) at h1
  change |diff 2| ≤ ((box.variationBall j 2).radius : ℝ) +
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
    {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (j : Fin 4) :
    ‖normalizedVariation box.root p
          (fun j i => (box.certificate j).exactEdge i)
          (fun j i => (box.certificate j).index i)
          box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) j -
        toR3 (box.approxNormalizedCenter j)‖ ≤ (box.δ : ℝ) := by
  have hBpos : (0 : ℝ) < ((box.certificate j).B : ℝ) := by
    exact_mod_cast h.B_pos j
  have hBne := hBpos.ne'
  have hraw := box.exactVariation_sub_center_norm_le hscale hmem j
  have hchecked :
      (box.variationRadiusSum j : ℝ) + 3 * (variationError : ℝ) ≤
        ((box.certificate j).B : ℝ) * (box.δ : ℝ) := by
    exact_mod_cast h.variation j
  rw [normalizedVariation, box.toR3_approxNormalizedCenter h j,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hBpos]
  calc
    ((box.certificate j).B : ℝ)⁻¹ *
        ‖variationVector box.root p
            (fun i => (box.certificate j).exactEdge i)
            (fun i => exactVertex (symmetryAction box.symmetryIndex
              ((box.certificate j).index i))) -
          box.variationCenter j‖ ≤
      ((box.certificate j).B : ℝ)⁻¹ *
        ((box.variationRadiusSum j : ℝ) +
          3 * (variationError : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hBpos.le)
      simpa [AxisCertificate.exactSelectedVertex,
        AxisCertificate.supportIndex] using hraw
    _ ≤ ((box.certificate j).B : ℝ)⁻¹ *
        (((box.certificate j).B : ℝ) * (box.δ : ℝ)) :=
      mul_le_mul_of_nonneg_left hchecked (inv_nonneg.mpr hBpos.le)
    _ = (box.δ : ℝ) := by field_simp [hBne]

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
        (7 / 4 * (((box.c + box.δ : ℚ) : ℝ))) • xAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_zero]
      ext i; fin_cases i <;> norm_num [xAxis3, toR3]
    rw [← heq]
    exact box.barycentric_mem_convexHull h 0
  · have heq : toR3 (box.octahedronTarget 1) =
        (-(7 / 4 * (((box.c + box.δ : ℚ) : ℝ)))) • xAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_one]
      ext i; fin_cases i <;> norm_num [xAxis3, toR3]
    rw [← heq]
    exact box.barycentric_mem_convexHull h 1
  · have heq : toR3 (box.octahedronTarget 2) =
        (7 / 4 * (((box.c + box.δ : ℚ) : ℝ))) • yAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_two]
      ext i; fin_cases i <;> norm_num [yAxis3, toR3]
    rw [← heq]
    exact box.barycentric_mem_convexHull h 2
  · have heq : toR3 (box.octahedronTarget 3) =
        (-(7 / 4 * (((box.c + box.δ : ℚ) : ℝ)))) • yAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_three]
      ext i; fin_cases i <;> norm_num [yAxis3, toR3]
    rw [← heq]
    exact box.barycentric_mem_convexHull h 3
  · have heq : toR3 (box.octahedronTarget 4) =
        (7 / 4 * (((box.c + box.δ : ℚ) : ℝ))) • zAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_four]
      ext i; fin_cases i <;> norm_num [zAxis3, toR3]
    rw [← heq]
    exact box.barycentric_mem_convexHull h 4
  · have heq : toR3 (box.octahedronTarget 5) =
        (-(7 / 4 * (((box.c + box.δ : ℚ) : ℝ)))) • zAxis3 := by
      rw [Box.octahedronTarget, LocalCertificate.octahedronAxis_five]
      ext i; fin_cases i <;> norm_num [zAxis3, toR3]
    rw [← heq]
    exact box.barycentric_mem_convexHull h 5
  · exact haxis

theorem Box.valid_axis_cover (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (axis : ℝ³) (haxis : ‖axis‖ = 1) :
    ∃ j, (box.c : ℝ) ≤ inner ℝ axis
      (normalizedVariation box.root p
        (fun j i => (box.certificate j).exactEdge i)
        (fun j i => (box.certificate j).index i)
        box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) j) := by
  obtain ⟨j, hcenter⟩ := box.valid_center_axis_cover h axis haxis
  refine ⟨j, ?_⟩
  have hmove := box.valid_normalizedVariation_move h hscale hmem j
  have hinner := abs_real_inner_le_norm axis
    (normalizedVariation box.root p
      (fun j i => (box.certificate j).exactEdge i)
      (fun j i => (box.certificate j).index i)
      box.symmetryIndex (fun j => ((box.certificate j).B : ℝ)) j -
        toR3 (box.approxNormalizedCenter j))
  rw [haxis, one_mul, inner_sub_right] at hinner
  have hdelta : (0 : ℝ) ≤ (box.δ : ℝ) := by exact_mod_cast h.delta_nonneg
  push_cast at hcenter
  rw [abs_le] at hinner
  linarith

theorem AxisCertificate.direction_norm_le_two (box : Box)
    (cert : AxisCertificate) {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p) (i : Fin 3) :
    ‖direction box.root p (cert.exactEdge i)‖ ≤ 2 := by
  have hscalePos : 0 < viewScale box.root p :=
    lt_of_lt_of_le (by norm_num) hscale
  have hinv : (viewScale box.root p)⁻¹ ≤ 1 :=
    (inv_le_one₀ hscalePos).2 hscale
  have hrot : ‖rotM p.θ p.φ (cert.exactEdge i)‖ ≤ 2 := by
    calc
      _ ≤ ‖rotM p.θ p.φ‖ * ‖cert.exactEdge i‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖cert.exactEdge i‖ := by
        rw [Bounding.rotM_norm_one, one_mul]
      _ ≤ 2 := cert.exactEdge_norm_le_two i
  rw [direction, norm_smul,
    Noperthedron.SnubCube.ProjectiveLocalCertificate.norm_quarterTurn,
    Real.norm_eq_abs, abs_inv, abs_of_pos hscalePos]
  exact (mul_le_mul hinv hrot (norm_nonneg _) (by norm_num)).trans
    (by norm_num)

theorem Box.valid_budget (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (j : Fin 4) :
    ∑ i, (box.certificate j).exactWeight box p i *
      (‖direction box.root p ((box.certificate j).exactEdge i)‖ *
        ‖exactVertex ((box.certificate j).supportIndex box i)‖) ≤
      ((box.certificate j).B : ℝ) := by
  let cert := box.certificate j
  have hsum :
      ∑ i, cert.exactWeight box p i *
          (‖direction box.root p (cert.exactEdge i)‖ *
            ‖exactVertex (cert.supportIndex box i)‖) ≤
        ∑ i, (box.weightUpper j i : ℝ) * 2 := by
    apply Finset.sum_le_sum
    intro i _
    have hw0 := box.valid_weight_nonneg h hscale hmem j i
    have hwUpper := box.exactWeight_le_upper hscale hmem j i
    have hfactor : ‖direction box.root p (cert.exactEdge i)‖ *
        ‖exactVertex (cert.supportIndex box i)‖ ≤ 2 := by
      calc
        _ ≤ 2 * 1 := mul_le_mul
          (cert.direction_norm_le_two box hscale i)
          (exactVertex_norm_le_one (cert.supportIndex box i))
          (norm_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    calc
      _ ≤ cert.exactWeight box p i * 2 :=
        mul_le_mul_of_nonneg_left hfactor hw0
      _ ≤ (box.weightUpper j i : ℝ) * 2 :=
        mul_le_mul_of_nonneg_right hwUpper (by norm_num)
  apply hsum.trans
  rw [← Finset.sum_mul]
  have hchecked : (2 * ∑ i, box.weightUpper j i : ℝ) ≤
      ((box.certificate j).B : ℝ) := by exact_mod_cast h.budget j
  simpa [mul_comm] using hchecked

theorem Box.valid_mismatch_bound (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²) :
    ‖Noperthedron.SnubCube.so3CLM
        (p.matrixPoseWithOffset box.chart offset).innerRot -
      Noperthedron.SnubCube.so3CLM
        ((p.matrixPoseWithOffset box.chart offset).outerRot *
          symmetry box.symmetryIndex)‖ ≤ (box.r : ℝ) := by
  have heq :
      Noperthedron.SnubCube.so3CLM
          (p.matrixPoseWithOffset box.chart offset).innerRot -
        Noperthedron.SnubCube.so3CLM
          ((p.matrixPoseWithOffset box.chart offset).outerRot *
            symmetry box.symmetryIndex) =
        Noperthedron.SnubCube.so3CLM
            (p.matrixPoseWithOffset box.chart offset).outerRot ∘L
          box.mismatchShell.exactRelativeMismatchCLM p := by
    simpa [Box.mismatchShell] using
      box.mismatchShell.poseMismatch_eq_outer_comp p offset
  rw [heq]
  calc
    _ ≤ ‖Noperthedron.SnubCube.so3CLM
          (p.matrixPoseWithOffset box.chart offset).outerRot‖ *
        ‖box.mismatchShell.exactRelativeMismatchCLM p‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖box.mismatchShell.exactRelativeMismatchCLM p‖ := by
      rw [Noperthedron.SnubCube.so3CLM_norm, one_mul]
    _ ≤ (box.mismatchRadius : ℝ) :=
      box.mismatchShell.exactRelativeMismatchCLM_norm_le hp
    _ ≤ (box.r : ℝ) := by exact_mod_cast h.mismatch_bound

theorem Box.valid_axisAngle_ratio (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (a : AxisAngle
      (Noperthedron.SnubCube.so3CLM
        (relativeRotationAtSymmetry
          (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex))) :
    1 - Real.cos a.angle ≤ |Real.sin a.angle| * (box.c : ℝ) := by
  apply Noperthedron.Nopert214.AxisAngle.ratio_of_inner_mismatch_bound
    (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex a
    (box.c : ℝ) (box.r : ℝ)
  · exact_mod_cast h.c_nonneg
  · exact_mod_cast h.r_nonneg
  · exact box.valid_mismatch_bound h hp offset
  · exact_mod_cast h.angle_bound

/-- A valid projective-local row rules out every translated pose in its
atlas interval and signed projective viewing triangle. -/
theorem Box.valid_imp_not_translated_rupert (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset)
      exactPolyhedron.hull := by
  apply not_rupertPose_of_projective_local_certificates
    (root := box.root) (p := p) (chart := box.chart) (offset := offset)
    (g := box.symmetryIndex)
    (edge := fun j i => (box.certificate j).exactEdge i)
    (index := fun j i => (box.certificate j).index i)
    (B := fun j => ((box.certificate j).B : ℝ))
    (c := (box.c : ℝ))
  · exact (lt_of_lt_of_le (by norm_num) hscale).ne'
  · intro j
    exact_mod_cast h.B_pos j
  · exact box.valid_axis_cover h hscale hmem
  · intro j
    simpa [AxisCertificate.exactWeight, AxisCertificate.supportIndex,
      AxisCertificate.exactSelectedVertex] using
      box.valid_budget h hscale hmem j
  · exact box.valid_axisAngle_ratio h hp offset
  · exact box.valid_direction_nonzero h offset hscale hmem
  · intro j i
    simpa [AxisCertificate.exactWeight] using
      box.valid_weight_nonneg h hscale hmem j i
  · intro j
    simpa [AxisCertificate.exactWeight] using
      box.valid_weight_pos h hscale hmem j
  · intro j i k
    simpa [AxisCertificate.supportIndex] using
      box.valid_support h offset hscale hmem j i k

theorem Box.valid_imp_no_translated_rupert_in_region
    (box : Box) (h : box.Valid) :
    ¬ ∃ p ∈ box.interval.toReal, ∃ offset : ℝ²,
      1 ≤ viewScale box.root p ∧
      InTriangle (toReal box.triangle)
        (AtlasProjectiveView.normalizedView box.root p) ∧
      RupertPose (p.matrixPoseWithOffset box.chart offset)
        exactPolyhedron.hull := by
  rintro ⟨p, hp, offset, hscale, hmem, hrupert⟩
  exact box.valid_imp_not_translated_rupert h hp offset hscale hmem hrupert

end Noperthedron.Nopert214.AtlasProjectiveLocalCertificate

end
