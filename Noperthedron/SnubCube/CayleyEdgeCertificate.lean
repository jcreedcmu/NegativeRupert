module

public import Noperthedron.BalancedSupport.Cycle
public import Noperthedron.Checker.RatQuadratic3
public import Noperthedron.Checker.RatTrigBall
public import Noperthedron.SnubCube.CayleyGlobalCertificate

@[expose] public section


/-!
# Pose-dependent projected-edge certificates in Cayley coordinates

A row stores a cyclic list of outer vertices and one selected inner vertex
per edge.  The clockwise projected edge normals balance by telescoping for
every outer view.  Support defects allow a row to cross silhouette changes,
while a normalized quadratic enclosure retains algebraic cancellation among
all edge contacts before interval radii are introduced.
-/

namespace Noperthedron.SnubCube.CayleyEdgeCertificate

open scoped RealInnerProductSpace Matrix
open Noperthedron.Checker
open Noperthedron.BalancedSupport
open RationalApprox

/-- `edgePred + 1` is the number of edges, hence is nonzero by construction. -/
structure Box where
  interval : CayleyInterval ℚ
  edgePred : ℕ
  outerIndex : Fin (edgePred + 1) → VertexIndex
  innerIndex : Fin (edgePred + 1) → VertexIndex
  nonzeroWitness : Fin (edgePred + 1) → VertexIndex

def Box.next (box : Box) : Fin (box.edgePred + 1) ≃ Fin (box.edgePred + 1) :=
  cycleNext box.edgePred

def Box.edgeQ (box : Box) (i : Fin (box.edgePred + 1)) : Fin 3 → ℚ :=
  normalizedRationalVertex (box.outerIndex i) -
    normalizedRationalVertex (box.outerIndex (box.next i))

def Box.deltaQ (box : Box) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) : Fin 3 → ℚ :=
  normalizedRationalVertex k - normalizedRationalVertex (box.outerIndex i)

def crossQ (a b : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![a 1*b 2-a 2*b 1, a 2*b 0-a 0*b 2, a 0*b 1-a 1*b 0]

theorem toR3_crossQ (a b : Fin 3 → ℚ) :
    toR3 (crossQ a b) = cross3 (toR3 a) (toR3 b) := by
  ext c
  fin_cases c <;> simp [crossQ, cross3, cross_apply, toR3]

noncomputable def Box.exactEdge (box : Box)
    (i : Fin (box.edgePred + 1)) : ℝ³ :=
  normalizedExactVertex (box.outerIndex i) -
    normalizedExactVertex (box.outerIndex (box.next i))

noncomputable def Box.exactDelta (box : Box)
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) : ℝ³ :=
  normalizedExactVertex k - normalizedExactVertex (box.outerIndex i)

noncomputable def Box.approxEdge (box : Box)
    (i : Fin (box.edgePred + 1)) : ℝ³ := toR3 (box.edgeQ i)

noncomputable def Box.approxDelta (box : Box)
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) : ℝ³ :=
  toR3 (box.deltaQ i k)

theorem Box.approxEdge_eq (box : Box) (i : Fin (box.edgePred + 1)) :
    box.approxEdge i =
      toR3 (normalizedRationalVertex (box.outerIndex i)) -
        toR3 (normalizedRationalVertex (box.outerIndex (box.next i))) := by
  ext c
  simp [Box.approxEdge, Box.edgeQ, toR3]

theorem Box.approxDelta_eq (box : Box) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) :
    box.approxDelta i k = toR3 (normalizedRationalVertex k) -
      toR3 (normalizedRationalVertex (box.outerIndex i)) := by
  ext c
  simp [Box.approxDelta, Box.deltaQ, toR3]

/-- Unit viewing vector: the cross product of the two rows of `rotM`. -/
noncomputable def viewVector (p : CayleyPose ℝ) : ℝ³ :=
  WithLp.toLp 2 ![Real.cos p.θ * Real.sin p.φ,
    Real.sin p.θ * Real.sin p.φ, Real.cos p.φ]

/-- Scalar-triple-product form of a projected clockwise edge normal. -/
theorem inner_quarterTurn_rotM_eq (p : CayleyPose ℝ) (a b : ℝ³) :
    ⟪quarterTurn (rotM p.θ p.φ a), rotM p.θ p.φ b⟫ =
      ∑ c, viewVector p c * cross3 a b c := by
  simp [quarterTurn, rotM, rotM_mat, viewVector, cross3, cross_apply,
    Matrix.toLpLin_apply, dotProduct,
    Fin.sum_univ_two, Fin.sum_univ_three, PiLp.inner_apply]
  have htrig := Real.sin_sq_add_cos_sq p.θ
  linear_combination
    (Real.cos p.φ * (b 1 * a 0 - b 0 * a 1)) * htrig

def Box.angleBall (box : Box) (i : Fin 2) : RatBall :=
  box.interval.coordinateBall ⟨i, by omega⟩

def Box.viewBalls (box : Box) : Fin 3 → RatBall :=
  let st := (box.angleBall 0).sin
  let ct := (box.angleBall 0).cos
  let sp := (box.angleBall 1).sin
  let cp := (box.angleBall 1).cos
  ![RatBall.mul ct sp, RatBall.mul st sp, cp]

def dotConstBalls (a : Fin 3 → ℚ) (b : Fin 3 → RatBall) : RatBall :=
  RatBall.add (RatBall.add (RatBall.scale (a 0) (b 0))
    (RatBall.scale (a 1) (b 1))) (RatBall.scale (a 2) (b 2))

theorem dotConstBalls_holds {a : Fin 3 → ℚ} {b : Fin 3 → RatBall}
    {v : Fin 3 → ℝ} (hb : ∀ c, (b c).Holds (v c)) :
    (dotConstBalls a b).Holds
      ((a 0 : ℝ) * v 0 + (a 1 : ℝ) * v 1 + (a 2 : ℝ) * v 2) := by
  exact RatBall.holds_add
    (RatBall.holds_add
      (RatBall.holds_scale (a 0) (hb 0))
      (RatBall.holds_scale (a 1) (hb 1)))
    (RatBall.holds_scale (a 2) (hb 2))

/-- Rational approximation of one outer support value
`⟨edgeNormal, outer(k-Q)⟩`. -/
def Box.supportBall (box : Box) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) : RatBall :=
  dotConstBalls (crossQ (box.edgeQ i) (box.deltaQ i k)) box.viewBalls

noncomputable def Box.approxSupportValue (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) : ℝ :=
  ⟪viewVector p, cross3 (box.approxEdge i) (box.approxDelta i k)⟫

/-- Universal exact-vertex allowance for one bilinear support value. -/
def supportError : ℚ := 10 * κℚ

def Box.supportUpper (box : Box) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) : ℚ :=
  (box.supportBall i k).center + (box.supportBall i k).radius + supportError

/-- Certified support defect for one moving edge normal. -/
def Box.defect (box : Box) (i : Fin (box.edgePred + 1)) : ℚ :=
  (Finset.image (box.supportUpper i) Finset.univ).max' (by
    simp only [Finset.image_nonempty]
    exact Finset.univ_nonempty)

def Box.totalDefect (box : Box) : ℚ := ∑ i, box.defect i

/-! ## Normalized Cayley quadratics -/

def qOne : RatQuadratic3 := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def qx : RatQuadratic3 := ⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩
def qy : RatQuadratic3 := ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩
def qz : RatQuadratic3 := ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩
def qxx : RatQuadratic3 := ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩
def qxy : RatQuadratic3 := ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩
def qxz : RatQuadratic3 := ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩
def qyy : RatQuadratic3 := ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩
def qyz : RatQuadratic3 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩
def qzz : RatQuadratic3 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩

def denomQuadratic : RatQuadratic3 := qOne + qxx + qyy + qzz

def numeratorQuadratic : Matrix (Fin 3) (Fin 3) RatQuadratic3 :=
  !![qOne + qxx - qyy - qzz,
      RatQuadratic3.scale 2 (qxy - qz),
      RatQuadratic3.scale 2 (qxz + qy);
     RatQuadratic3.scale 2 (qxy + qz),
      qOne - qxx + qyy - qzz,
      RatQuadratic3.scale 2 (qyz - qx);
     RatQuadratic3.scale 2 (qxz - qy),
      RatQuadratic3.scale 2 (qyz + qx),
     qOne - qxx - qyy + qzz]

theorem eval_denomQuadratic (x y z : ℝ) :
    denomQuadratic.evalReal x y z = cayleyDenom x y z := by
  simp only [denomQuadratic, RatQuadratic3.evalReal_add]
  simp [qOne, qxx, qyy, qzz, RatQuadratic3.evalReal, cayleyDenom]
  ring

theorem eval_numeratorQuadratic (c j : Fin 3) (x y z : ℝ) :
    (numeratorQuadratic c j).evalReal x y z =
      cayleyNumeratorMatrix x y z c j := by
  fin_cases c <;> fin_cases j <;>
    simp only [numeratorQuadratic] <;>
    simp [qOne, qx, qy, qz, qxx, qxy, qxz, qyy, qyz, qzz,
      RatQuadratic3.evalReal, cayleyNumeratorMatrix] <;> ring

def sum3Q (f : Fin 3 → RatQuadratic3) : RatQuadratic3 :=
  f 0 + f 1 + f 2

def Box.displacementQuadratic (box : Box)
    (i : Fin (box.edgePred + 1)) (c : Fin 3) : RatQuadratic3 :=
  (sum3Q fun j => RatQuadratic3.scale
      (normalizedRationalVertex (box.innerIndex i) j)
      (numeratorQuadratic c j)) -
    RatQuadratic3.scale (normalizedRationalVertex (box.outerIndex i) c)
      denomQuadratic

def Box.contactQuadratic (box : Box)
    (i : Fin (box.edgePred + 1)) : Fin 3 → RatQuadratic3 :=
  let edge := box.edgeQ i
  let d := box.displacementQuadratic i
  ![RatQuadratic3.scale (edge 1) (d 2) - RatQuadratic3.scale (edge 2) (d 1),
    RatQuadratic3.scale (edge 2) (d 0) - RatQuadratic3.scale (edge 0) (d 2),
    RatQuadratic3.scale (edge 0) (d 1) - RatQuadratic3.scale (edge 1) (d 0)]

/-- Sum coefficients first, preserving all cross-edge cancellations. -/
def Box.totalQuadratic (box : Box) (c : Fin 3) : RatQuadratic3 :=
  let f := fun i => box.contactQuadratic i c
  { c0 := ∑ i, (f i).c0
    cx := ∑ i, (f i).cx
    cy := ∑ i, (f i).cy
    cz := ∑ i, (f i).cz
    cxx := ∑ i, (f i).cxx
    cxy := ∑ i, (f i).cxy
    cxz := ∑ i, (f i).cxz
    cyy := ∑ i, (f i).cyy
    cyz := ∑ i, (f i).cyz
    czz := ∑ i, (f i).czz }

noncomputable def Box.approxDisplacementVector (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1)) : ℝ³ :=
  (cayleyNumeratorMatrix p.x p.y p.z).toEuclideanLin
      (toR3 (normalizedRationalVertex (box.innerIndex i))) -
    cayleyDenom p.x p.y p.z •
      toR3 (normalizedRationalVertex (box.outerIndex i))

noncomputable def Box.approxContactVector (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1)) : ℝ³ :=
  cross3 (box.approxEdge i) (box.approxDisplacementVector p i)

noncomputable def Box.approxTotalVector (box : Box)
    (p : CayleyPose ℝ) : ℝ³ := ∑ i, box.approxContactVector p i

noncomputable def Box.approxClearedDisplacement (box : Box)
    (p : CayleyPose ℝ) : ℝ :=
  ⟪viewVector p, box.approxTotalVector p⟫

noncomputable def Box.exactDisplacementVector (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1)) : ℝ³ :=
  (cayleyNumeratorMatrix p.x p.y p.z).toEuclideanLin
      (normalizedExactVertex (box.innerIndex i)) -
    cayleyDenom p.x p.y p.z •
      normalizedExactVertex (box.outerIndex i)

noncomputable def Box.exactContactVector (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1)) : ℝ³ :=
  cross3 (box.exactEdge i) (box.exactDisplacementVector p i)

noncomputable def Box.exactTotalVector (box : Box)
    (p : CayleyPose ℝ) : ℝ³ := ∑ i, box.exactContactVector p i

noncomputable def Box.exactClearedDisplacement (box : Box)
    (p : CayleyPose ℝ) : ℝ :=
  ⟪viewVector p, box.exactTotalVector p⟫

noncomputable def Box.actualDisplacementVector (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1)) : ℝ³ :=
  (cayleyMatrix p.x p.y p.z).toEuclideanLin
      (normalizedExactVertex (box.innerIndex i)) -
    normalizedExactVertex (box.outerIndex i)

noncomputable def Box.actualContactVector (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1)) : ℝ³ :=
  cross3 (box.exactEdge i) (box.actualDisplacementVector p i)

noncomputable def Box.actualTotalVector (box : Box)
    (p : CayleyPose ℝ) : ℝ³ := ∑ i, box.actualContactVector p i

noncomputable def Box.actualDisplacement (box : Box)
    (p : CayleyPose ℝ) : ℝ :=
  ⟪viewVector p, box.actualTotalVector p⟫

theorem Box.exactDisplacementVector_eq_denom_smul (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1)) :
    box.exactDisplacementVector p i =
      cayleyDenom p.x p.y p.z • box.actualDisplacementVector p i := by
  have happ :
      (cayleyNumeratorMatrix p.x p.y p.z).toEuclideanLin
          (normalizedExactVertex (box.innerIndex i)) =
        cayleyDenom p.x p.y p.z •
          (cayleyMatrix p.x p.y p.z).toEuclideanLin
            (normalizedExactVertex (box.innerIndex i)) := by
    rw [cayleyNumeratorMatrix_eq_denom_smul]
    ext c
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, mul_add]
  unfold Box.exactDisplacementVector Box.actualDisplacementVector
  rw [happ, ← smul_sub]

theorem Box.exactContactVector_eq_denom_smul (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1)) :
    box.exactContactVector p i =
      cayleyDenom p.x p.y p.z • box.actualContactVector p i := by
  unfold Box.exactContactVector Box.actualContactVector
  rw [box.exactDisplacementVector_eq_denom_smul,
    cross3_smul_right]

theorem Box.exactTotalVector_eq_denom_smul (box : Box)
    (p : CayleyPose ℝ) :
    box.exactTotalVector p =
      cayleyDenom p.x p.y p.z • box.actualTotalVector p := by
  unfold Box.exactTotalVector Box.actualTotalVector
  simp_rw [box.exactContactVector_eq_denom_smul]
  exact (Finset.smul_sum).symm

theorem Box.exactClearedDisplacement_eq_denom_mul (box : Box)
    (p : CayleyPose ℝ) :
    box.exactClearedDisplacement p =
      cayleyDenom p.x p.y p.z * box.actualDisplacement p := by
  unfold Box.exactClearedDisplacement Box.actualDisplacement
  rw [box.exactTotalVector_eq_denom_smul, inner_smul_right]

theorem Box.eval_displacementQuadratic (box : Box)
    (i : Fin (box.edgePred + 1)) (c : Fin 3) (x y z : ℝ) :
    (box.displacementQuadratic i c).evalReal x y z =
      (box.approxDisplacementVector ⟨0, 0, x, y, z⟩ i) c := by
  simp only [Box.displacementQuadratic, sum3Q,
    RatQuadratic3.evalReal_sub, RatQuadratic3.evalReal_add,
    RatQuadratic3.evalReal_scale, eval_numeratorQuadratic,
    eval_denomQuadratic]
  simp [Box.approxDisplacementVector, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, toR3]
  ring

theorem Box.eval_contactQuadratic (box : Box)
    (i : Fin (box.edgePred + 1)) (c : Fin 3) (x y z : ℝ) :
    (box.contactQuadratic i c).evalReal x y z =
      (box.approxContactVector ⟨0, 0, x, y, z⟩ i) c := by
  fin_cases c <;>
    simp [Box.contactQuadratic, Box.approxContactVector,
      cross3, cross_apply, box.eval_displacementQuadratic,
      Box.approxEdge, toR3]

theorem Box.eval_totalQuadratic (box : Box) (c : Fin 3)
    (x y z : ℝ) :
    (box.totalQuadratic c).evalReal x y z =
      (box.approxTotalVector ⟨0, 0, x, y, z⟩) c := by
  have hcoeff :
      (box.totalQuadratic c).evalReal x y z =
        ∑ i, (box.contactQuadratic i c).evalReal x y z := by
    simp [Box.totalQuadratic, RatQuadratic3.evalReal,
      Finset.sum_add_distrib, Finset.sum_mul]
  rw [hcoeff]
  simp_rw [box.eval_contactQuadratic]
  simp [Box.approxTotalVector]

theorem Box.eval_totalQuadratic_pose (box : Box) (c : Fin 3)
    (p : CayleyPose ℝ) :
    (box.totalQuadratic c).evalReal p.x p.y p.z =
      (box.approxTotalVector p) c := by
  simpa [Box.approxTotalVector, Box.approxContactVector,
    Box.approxDisplacementVector] using
    box.eval_totalQuadratic c p.x p.y p.z

def Box.variableBalls (box : Box) : Fin 3 → RatBall :=
  ![box.interval.coordinateBall 2,
    box.interval.coordinateBall 3,
    box.interval.coordinateBall 4]

def Box.displacementComponents (box : Box) : Fin 3 → RatBall :=
  fun c => RatQuadratic3.evalBall box.variableBalls (box.totalQuadratic c)

def dotBalls (a b : Fin 3 → RatBall) : RatBall :=
  RatBall.add (RatBall.add (RatBall.mul (a 0) (b 0))
    (RatBall.mul (a 1) (b 1))) (RatBall.mul (a 2) (b 2))

theorem dotBalls_holds {a b : Fin 3 → RatBall}
    {u v : Fin 3 → ℝ} (ha : ∀ c, (a c).Holds (u c))
    (hb : ∀ c, (b c).Holds (v c)) :
    (dotBalls a b).Holds
      (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) := by
  exact RatBall.holds_add
    (RatBall.holds_add
      (RatBall.holds_mul (ha 0) (hb 0))
      (RatBall.holds_mul (ha 1) (hb 1)))
    (RatBall.holds_mul (ha 2) (hb 2))

def Box.displacementBall (box : Box) : RatBall :=
  dotBalls box.viewBalls box.displacementComponents

private theorem Box.earlyApproxEdgeNorm (box : Box)
    (i : Fin (box.edgePred + 1)) :
    ‖box.approxEdge i‖ ≤ 2 * (1 + RationalApprox.κ) := by
  rw [box.approxEdge_eq]
  exact (norm_sub_le _ _).trans (by
    linarith [CayleyGlobalCertificate.norm_normalizedRationalVertex_le
        (box.outerIndex i),
      CayleyGlobalCertificate.norm_normalizedRationalVertex_le
        (box.outerIndex (box.next i))])

private theorem Box.earlyExactEdgeError (box : Box)
    (i : Fin (box.edgePred + 1)) :
    ‖box.exactEdge i - box.approxEdge i‖ ≤ 2 * RationalApprox.κ := by
  rw [box.approxEdge_eq]
  have hrearrange :
      box.exactEdge i -
          (toR3 (normalizedRationalVertex (box.outerIndex i)) -
            toR3 (normalizedRationalVertex (box.outerIndex (box.next i)))) =
        (normalizedExactVertex (box.outerIndex i) -
            toR3 (normalizedRationalVertex (box.outerIndex i))) -
          (normalizedExactVertex (box.outerIndex (box.next i)) -
            toR3 (normalizedRationalVertex (box.outerIndex (box.next i)))) := by
    unfold Box.exactEdge
    abel
  rw [hrearrange]
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ RationalApprox.κ + RationalApprox.κ := add_le_add
      (normalizedApproximation.approx (box.outerIndex i))
      (normalizedApproximation.approx (box.outerIndex (box.next i)))
    _ = 2 * RationalApprox.κ := by ring

def Box.dBound (box : Box) : ℚ :=
  1 + CayleyLocalCertificate.endpointAbsBound
      box.interval.min.x box.interval.max.x ^ 2 +
    CayleyLocalCertificate.endpointAbsBound
      box.interval.min.y box.interval.max.y ^ 2 +
    CayleyLocalCertificate.endpointAbsBound
      box.interval.min.z box.interval.max.z ^ 2

/-- Summed exact-vertex allowance for the denominator-cleared displacement. -/
def Box.displacementError (box : Box) : ℚ :=
  (box.edgePred + 1) * 10 * box.dBound * κℚ

/-- A geometry-free shell used only to reuse the exact interval radius lemma. -/
def Box.localShell (box : Box) : CayleyLocalCertificate.Box where
  interval := box.interval
  certificate := fun _ => { contact := fun _ => {
    index := VertexIndex.ofFin24 0
    direction := 0 } }
  c := 0
  r := 0

theorem Box.denom_le_dBound (box : Box) {p : CayleyPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    cayleyDenom p.x p.y p.z ≤ (box.dBound : ℝ) := by
  have hs := box.localShell.sq_sum_le_radiusSq hp
  change 1 + p.x ^ 2 + p.y ^ 2 + p.z ^ 2 ≤ _
  simp only [Box.dBound]
  push_cast
  simp only [Box.localShell, CayleyLocalCertificate.Box.radiusSq] at hs
  push_cast at hs
  linarith

theorem Box.exactDisplacement_sub_approx_norm_le (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1)) :
    ‖box.exactDisplacementVector p i - box.approxDisplacementVector p i‖ ≤
      2 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by
  have hrearrange :
      box.exactDisplacementVector p i - box.approxDisplacementVector p i =
        (cayleyNumeratorMatrix p.x p.y p.z).toEuclideanLin
          (normalizedExactVertex (box.innerIndex i) -
            toR3 (normalizedRationalVertex (box.innerIndex i))) -
        cayleyDenom p.x p.y p.z •
          (normalizedExactVertex (box.outerIndex i) -
            toR3 (normalizedRationalVertex (box.outerIndex i))) := by
    unfold Box.exactDisplacementVector Box.approxDisplacementVector
    rw [map_sub]
    module
  rw [hrearrange]
  calc
    _ ≤ ‖(cayleyNumeratorMatrix p.x p.y p.z).toEuclideanLin
          (normalizedExactVertex (box.innerIndex i) -
            toR3 (normalizedRationalVertex (box.innerIndex i)))‖ +
        ‖cayleyDenom p.x p.y p.z •
          (normalizedExactVertex (box.outerIndex i) -
            toR3 (normalizedRationalVertex (box.outerIndex i)))‖ :=
      norm_sub_le _ _
    _ ≤ cayleyDenom p.x p.y p.z * RationalApprox.κ +
        cayleyDenom p.x p.y p.z * RationalApprox.κ := by
      apply add_le_add
      · exact (norm_cayleyNumeratorMatrix_apply_le p.x p.y p.z _).trans
          (mul_le_mul_of_nonneg_left
            (normalizedApproximation.approx (box.innerIndex i))
            (cayleyDenom_pos p.x p.y p.z).le)
      · rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (cayleyDenom_pos p.x p.y p.z)]
        exact mul_le_mul_of_nonneg_left
          (normalizedApproximation.approx (box.outerIndex i))
          (cayleyDenom_pos p.x p.y p.z).le
    _ = 2 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by ring

theorem Box.exactDisplacementVector_norm_le (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1)) :
    ‖box.exactDisplacementVector p i‖ ≤
      2 * cayleyDenom p.x p.y p.z := by
  unfold Box.exactDisplacementVector
  calc
    _ ≤ ‖(cayleyNumeratorMatrix p.x p.y p.z).toEuclideanLin
          (normalizedExactVertex (box.innerIndex i))‖ +
        ‖cayleyDenom p.x p.y p.z •
          normalizedExactVertex (box.outerIndex i)‖ := norm_sub_le _ _
    _ ≤ cayleyDenom p.x p.y p.z + cayleyDenom p.x p.y p.z := by
      apply add_le_add
      · exact (norm_cayleyNumeratorMatrix_apply_le p.x p.y p.z _).trans
          ((mul_le_mul_of_nonneg_left
            (normalizedExactVertex_norm_le_one (box.innerIndex i))
            (cayleyDenom_pos p.x p.y p.z).le).trans_eq (mul_one _))
      · rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (cayleyDenom_pos p.x p.y p.z)]
        exact (mul_le_mul_of_nonneg_left
          (normalizedExactVertex_norm_le_one (box.outerIndex i))
          (cayleyDenom_pos p.x p.y p.z).le).trans_eq (mul_one _)
    _ = 2 * cayleyDenom p.x p.y p.z := by ring

theorem Box.exactContact_sub_approx_norm_le (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1)) :
    ‖box.exactContactVector p i - box.approxContactVector p i‖ ≤
      10 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by
  have hdecomp :
      box.exactContactVector p i - box.approxContactVector p i =
        cross3 (box.exactEdge i - box.approxEdge i)
          (box.exactDisplacementVector p i) +
        cross3 (box.approxEdge i)
          (box.exactDisplacementVector p i -
            box.approxDisplacementVector p i) := by
    ext c
    fin_cases c <;>
      simp [Box.exactContactVector, Box.approxContactVector,
        cross3, cross_apply] <;> ring
  rw [hdecomp]
  calc
    _ ≤ ‖cross3 (box.exactEdge i - box.approxEdge i)
          (box.exactDisplacementVector p i)‖ +
        ‖cross3 (box.approxEdge i)
          (box.exactDisplacementVector p i -
            box.approxDisplacementVector p i)‖ := norm_add_le _ _
    _ ≤ (2 * RationalApprox.κ) *
          (2 * cayleyDenom p.x p.y p.z) +
        (2 * (1 + RationalApprox.κ)) *
          (2 * cayleyDenom p.x p.y p.z * RationalApprox.κ) := by
      exact add_le_add
        ((cross3_norm_le _ _).trans (mul_le_mul
          (box.earlyExactEdgeError i)
          (box.exactDisplacementVector_norm_le p i)
          (norm_nonneg _) (by norm_num [RationalApprox.κ])))
        ((cross3_norm_le _ _).trans (mul_le_mul
          (box.earlyApproxEdgeNorm i)
          (box.exactDisplacement_sub_approx_norm_le p i)
          (norm_nonneg _) (by norm_num [RationalApprox.κ])))
    _ ≤ 10 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by
      have hd := (cayleyDenom_pos p.x p.y p.z).le
      have hk : 0 ≤ RationalApprox.κ := by norm_num [RationalApprox.κ]
      have hfactor : 4 + 4 * (1 + RationalApprox.κ) ≤ (10 : ℝ) := by
        norm_num [RationalApprox.κ]
      calc
        _ = cayleyDenom p.x p.y p.z * RationalApprox.κ *
            (4 + 4 * (1 + RationalApprox.κ)) := by ring
        _ ≤ cayleyDenom p.x p.y p.z * RationalApprox.κ * 10 :=
          mul_le_mul_of_nonneg_left hfactor (mul_nonneg hd hk)
        _ = 10 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by ring

theorem Box.exactContact_sub_approx_norm_le_error (box : Box)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal)
    (i : Fin (box.edgePred + 1)) :
    ‖box.exactContactVector p i - box.approxContactVector p i‖ ≤
      10 * (box.dBound : ℝ) * RationalApprox.κ := by
  exact (box.exactContact_sub_approx_norm_le p i).trans (by
    have hk : 0 ≤ RationalApprox.κ := by norm_num [RationalApprox.κ]
    nlinarith [box.denom_le_dBound hp])

theorem Box.exactTotal_sub_approx_norm_le_error (box : Box)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal) :
    ‖box.exactTotalVector p - box.approxTotalVector p‖ ≤
      (box.edgePred + 1 : ℝ) * 10 * (box.dBound : ℝ) *
        RationalApprox.κ := by
  have hsum : box.exactTotalVector p - box.approxTotalVector p =
      ∑ i, (box.exactContactVector p i - box.approxContactVector p i) := by
    unfold Box.exactTotalVector Box.approxTotalVector
    rw [Finset.sum_sub_distrib]
  rw [hsum]
  apply (norm_sum_le _ _).trans
  calc
    ∑ i, ‖box.exactContactVector p i - box.approxContactVector p i‖ ≤
        ∑ _ : Fin (box.edgePred + 1),
          10 * (box.dBound : ℝ) * RationalApprox.κ := by
      apply Finset.sum_le_sum
      intro i _
      exact box.exactContact_sub_approx_norm_le_error hp i
    _ = (box.edgePred + 1 : ℝ) * 10 * (box.dBound : ℝ) *
        RationalApprox.κ := by simp; ring

theorem Box.clearedDisplacement_error (box : Box)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal) :
    |box.exactClearedDisplacement p - box.approxClearedDisplacement p| ≤
      (box.displacementError : ℝ) := by
  have hrearrange :
      box.exactClearedDisplacement p - box.approxClearedDisplacement p =
        ⟪viewVector p, box.exactTotalVector p - box.approxTotalVector p⟫ := by
    unfold Box.exactClearedDisplacement Box.approxClearedDisplacement
    rw [inner_sub_right]
  rw [hrearrange]
  calc
    _ ≤ ‖viewVector p‖ *
        ‖box.exactTotalVector p - box.approxTotalVector p‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (box.edgePred + 1 : ℝ) * 10 * (box.dBound : ℝ) *
        RationalApprox.κ := by
      rw [show ‖viewVector p‖ = 1 by
        simpa [viewVector, vecX] using Bounding.vecX_norm_one p.θ p.φ,
        one_mul]
      exact box.exactTotal_sub_approx_norm_le_error hp
    _ = (box.displacementError : ℝ) := by
      simp [Box.displacementError, RationalApprox.κ,
        RationalApprox.κℚ]

def Box.centerInFour (box : Box) : Prop :=
  (box.angleBall 0).center ∈ Set.Icc (-4 : ℚ) 4 ∧
    (box.angleBall 1).center ∈ Set.Icc (-4 : ℚ) 4

theorem Box.viewBalls_holds (box : Box) {p : CayleyPose ℝ}
    (hp : p ∈ box.interval.toReal) (hcenter : box.centerInFour) :
    ∀ c, (box.viewBalls c).Holds (viewVector p c) := by
  have hθ := box.interval.coordinateBall_holds hp 0
  have hφ := box.interval.coordinateBall_holds hp 1
  have hθcenter : ((box.angleBall 0).center : ℝ) ∈ Set.Icc (-4) 4 := by
    constructor
    · exact_mod_cast hcenter.1.1
    · exact_mod_cast hcenter.1.2
  have hφcenter : ((box.angleBall 1).center : ℝ) ∈ Set.Icc (-4) 4 := by
    constructor
    · exact_mod_cast hcenter.2.1
    · exact_mod_cast hcenter.2.2
  have hsθ := RatBall.sin_holds
    (by simpa [Box.angleBall] using hθcenter) hθ
  have hcθ := RatBall.cos_holds
    (by simpa [Box.angleBall] using hθcenter) hθ
  have hsφ := RatBall.sin_holds
    (by simpa [Box.angleBall] using hφcenter) hφ
  have hcφ := RatBall.cos_holds
    (by simpa [Box.angleBall] using hφcenter) hφ
  intro c
  fin_cases c
  · exact RatBall.holds_mul hcθ hsφ
  · exact RatBall.holds_mul hsθ hsφ
  · exact hcφ

theorem Box.displacementBall_holds (box : Box) {p : CayleyPose ℝ}
    (hp : p ∈ box.interval.toReal) (hcenter : box.centerInFour) :
    box.displacementBall.Holds (box.approxClearedDisplacement p) := by
  have hvars : ∀ c : Fin 3,
      (box.variableBalls c).Holds (![p.x, p.y, p.z] c) := by
    intro c
    fin_cases c
    · exact box.interval.coordinateBall_holds hp 2
    · exact box.interval.coordinateBall_holds hp 3
    · exact box.interval.coordinateBall_holds hp 4
  have hcomponents : ∀ c,
      (box.displacementComponents c).Holds (box.approxTotalVector p c) := by
    intro c
    have hc := RatQuadratic3.evalBall_holds hvars (box.totalQuadratic c)
    rw [box.eval_totalQuadratic_pose] at hc
    exact hc
  have hdot := dotBalls_holds (box.viewBalls_holds hp hcenter) hcomponents
  simpa [Box.displacementBall, Box.approxClearedDisplacement,
    PiLp.inner_apply, Fin.sum_univ_three, mul_comm] using hdot

theorem Box.supportBall_holds (box : Box) {p : CayleyPose ℝ}
    (hp : p ∈ box.interval.toReal) (hcenter : box.centerInFour)
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    (box.supportBall i k).Holds (box.approxSupportValue p i k) := by
  have h := dotConstBalls_holds (a := crossQ (box.edgeQ i) (box.deltaQ i k))
    (box.viewBalls_holds hp hcenter)
  rw [Box.approxSupportValue, Box.approxEdge, Box.approxDelta,
    ← toR3_crossQ]
  simpa [Box.supportBall, PiLp.inner_apply, Fin.sum_univ_three, toR3,
    mul_comm] using h

theorem viewVector_norm (p : CayleyPose ℝ) : ‖viewVector p‖ = 1 := by
  simpa [viewVector, vecX] using Bounding.vecX_norm_one p.θ p.φ

theorem Box.exactEdge_norm_le_two (box : Box)
    (i : Fin (box.edgePred + 1)) : ‖box.exactEdge i‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans (by
    linarith [normalizedExactVertex_norm_le_one (box.outerIndex i),
      normalizedExactVertex_norm_le_one (box.outerIndex (box.next i))])

theorem Box.exactDelta_norm_le_two (box : Box)
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    ‖box.exactDelta i k‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans (by
    linarith [normalizedExactVertex_norm_le_one k,
      normalizedExactVertex_norm_le_one (box.outerIndex i)])

theorem Box.approxEdge_norm_le (box : Box)
    (i : Fin (box.edgePred + 1)) :
    ‖box.approxEdge i‖ ≤ 2 * (1 + RationalApprox.κ) := by
  rw [box.approxEdge_eq]
  exact (norm_sub_le _ _).trans (by
    linarith [CayleyGlobalCertificate.norm_normalizedRationalVertex_le
        (box.outerIndex i),
      CayleyGlobalCertificate.norm_normalizedRationalVertex_le
        (box.outerIndex (box.next i))])

theorem Box.approxDelta_norm_le (box : Box)
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    ‖box.approxDelta i k‖ ≤ 2 * (1 + RationalApprox.κ) := by
  rw [box.approxDelta_eq]
  exact (norm_sub_le _ _).trans (by
    linarith [CayleyGlobalCertificate.norm_normalizedRationalVertex_le k,
      CayleyGlobalCertificate.norm_normalizedRationalVertex_le
        (box.outerIndex i)])

theorem Box.exactEdge_sub_approx_norm_le (box : Box)
    (i : Fin (box.edgePred + 1)) :
    ‖box.exactEdge i - box.approxEdge i‖ ≤ 2 * RationalApprox.κ := by
  rw [box.approxEdge_eq]
  have hrearrange :
      box.exactEdge i -
          (toR3 (normalizedRationalVertex (box.outerIndex i)) -
            toR3 (normalizedRationalVertex (box.outerIndex (box.next i)))) =
        (normalizedExactVertex (box.outerIndex i) -
            toR3 (normalizedRationalVertex (box.outerIndex i))) -
          (normalizedExactVertex (box.outerIndex (box.next i)) -
            toR3 (normalizedRationalVertex (box.outerIndex (box.next i)))) := by
    unfold Box.exactEdge
    abel
  rw [hrearrange]
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ RationalApprox.κ + RationalApprox.κ := add_le_add
      (normalizedApproximation.approx (box.outerIndex i))
      (normalizedApproximation.approx (box.outerIndex (box.next i)))
    _ = 2 * RationalApprox.κ := by ring

theorem Box.exactDelta_sub_approx_norm_le (box : Box)
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    ‖box.exactDelta i k - box.approxDelta i k‖ ≤
      2 * RationalApprox.κ := by
  rw [box.approxDelta_eq]
  have hrearrange :
      box.exactDelta i k -
          (toR3 (normalizedRationalVertex k) -
            toR3 (normalizedRationalVertex (box.outerIndex i))) =
        (normalizedExactVertex k - toR3 (normalizedRationalVertex k)) -
          (normalizedExactVertex (box.outerIndex i) -
            toR3 (normalizedRationalVertex (box.outerIndex i))) := by
    unfold Box.exactDelta
    abel
  rw [hrearrange]
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ RationalApprox.κ + RationalApprox.κ := add_le_add
      (normalizedApproximation.approx k)
      (normalizedApproximation.approx (box.outerIndex i))
    _ = 2 * RationalApprox.κ := by ring

theorem Box.cross_error (box : Box) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) :
    ‖cross3 (box.exactEdge i) (box.exactDelta i k) -
        cross3 (box.approxEdge i) (box.approxDelta i k)‖ ≤
      10 * RationalApprox.κ := by
  have hdecomp :
      cross3 (box.exactEdge i) (box.exactDelta i k) -
          cross3 (box.approxEdge i) (box.approxDelta i k) =
        cross3 (box.exactEdge i - box.approxEdge i) (box.exactDelta i k) +
          cross3 (box.approxEdge i)
            (box.exactDelta i k - box.approxDelta i k) := by
    ext c
    fin_cases c <;> simp [cross3, cross_apply] <;> ring
  rw [hdecomp]
  calc
    ‖cross3 (box.exactEdge i - box.approxEdge i) (box.exactDelta i k) +
        cross3 (box.approxEdge i)
          (box.exactDelta i k - box.approxDelta i k)‖ ≤
      ‖cross3 (box.exactEdge i - box.approxEdge i) (box.exactDelta i k)‖ +
        ‖cross3 (box.approxEdge i)
          (box.exactDelta i k - box.approxDelta i k)‖ := norm_add_le _ _
    _ ≤ (2 * RationalApprox.κ) * 2 +
        (2 * (1 + RationalApprox.κ)) * (2 * RationalApprox.κ) := by
      exact add_le_add
        ((cross3_norm_le _ _).trans (mul_le_mul
          (box.exactEdge_sub_approx_norm_le i)
          (box.exactDelta_norm_le_two i k) (norm_nonneg _)
          (by norm_num [RationalApprox.κ])))
        ((cross3_norm_le _ _).trans (mul_le_mul
          (box.approxEdge_norm_le i)
          (box.exactDelta_sub_approx_norm_le i k)
          (norm_nonneg _) (by norm_num [RationalApprox.κ])))
    _ ≤ 10 * RationalApprox.κ := by
      norm_num [RationalApprox.κ]

noncomputable def Box.exactSupportValue (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) : ℝ :=
  ⟪viewVector p, cross3 (box.exactEdge i) (box.exactDelta i k)⟫

theorem Box.supportValue_error (box : Box) (p : CayleyPose ℝ)
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    |box.exactSupportValue p i k - box.approxSupportValue p i k| ≤
      (supportError : ℝ) := by
  rw [Box.exactSupportValue, Box.approxSupportValue, ← inner_sub_right]
  calc
    |⟪viewVector p,
        cross3 (box.exactEdge i) (box.exactDelta i k) -
          cross3 (box.approxEdge i) (box.approxDelta i k)⟫| ≤
      ‖viewVector p‖ *
        ‖cross3 (box.exactEdge i) (box.exactDelta i k) -
          cross3 (box.approxEdge i) (box.approxDelta i k)‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ 10 * RationalApprox.κ := by
      rw [viewVector_norm, one_mul]
      exact box.cross_error i k
    _ = (supportError : ℝ) := by
      norm_num [supportError, RationalApprox.κ, RationalApprox.κℚ]

theorem Box.cycleDirection_eq (box : Box) (p : CayleyPose ℝ)
    (offset : ℝ²) (i : Fin (box.edgePred + 1)) :
    cycleDirection (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron box.outerIndex i =
      quarterTurn (rotM p.θ p.φ (box.exactEdge i)) := by
  change quarterTurn (outerProjectionLinear (p.matrixPoseWithOffset offset)
      (normalizedExactVertex (box.outerIndex i) -
        normalizedExactVertex (box.outerIndex (box.next i)))) = _
  rw [show outerProjectionLinear (p.matrixPoseWithOffset offset)
      (normalizedExactVertex (box.outerIndex i) -
        normalizedExactVertex (box.outerIndex (box.next i))) =
      rotM p.θ p.φ
        (normalizedExactVertex (box.outerIndex i) -
          normalizedExactVertex (box.outerIndex (box.next i))) by
    simpa [outerProjectionLinear] using
      CayleyPose.matrixPoseWithOffset_outer_rotation_project p offset
        (normalizedExactVertex (box.outerIndex i) -
          normalizedExactVertex (box.outerIndex (box.next i)))]
  rfl

theorem Box.exactSupportValue_eq (box : Box) (p : CayleyPose ℝ)
    (offset : ℝ²) (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    box.exactSupportValue p i k =
      ⟪cycleDirection (p.matrixPoseWithOffset offset)
          normalizedExactPolyhedron box.outerIndex i,
        outerProjectionLinear (p.matrixPoseWithOffset offset)
          (normalizedExactVertex k -
            normalizedExactVertex (box.outerIndex i))⟫ := by
  rw [box.cycleDirection_eq p offset i]
  rw [show outerProjectionLinear (p.matrixPoseWithOffset offset)
      (normalizedExactVertex k -
        normalizedExactVertex (box.outerIndex i)) =
      rotM p.θ p.φ
        (normalizedExactVertex k -
          normalizedExactVertex (box.outerIndex i)) by
    simpa [outerProjectionLinear] using
      CayleyPose.matrixPoseWithOffset_outer_rotation_project p offset
        (normalizedExactVertex k -
          normalizedExactVertex (box.outerIndex i))]
  rw [inner_quarterTurn_rotM_eq]
  simp [Box.exactSupportValue, Box.exactEdge, Box.exactDelta,
    PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem Box.actualContactValue_eq (box : Box) (p : CayleyPose ℝ)
    (offset : ℝ²) (i : Fin (box.edgePred + 1)) :
    ⟪viewVector p, box.actualContactVector p i⟫ =
      ⟪cycleDirection (p.matrixPoseWithOffset offset)
          normalizedExactPolyhedron box.outerIndex i,
        proj_xyL ((p.matrixPoseWithOffset offset).innerRot.val.toEuclideanLin
          (normalizedExactVertex (box.innerIndex i))) -
        proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin
          (normalizedExactVertex (box.outerIndex i)))⟫ := by
  rw [box.cycleDirection_eq p offset i,
    CayleyPose.matrixPoseWithOffset_inner_rotation_project,
    CayleyPose.matrixPoseWithOffset_outer_rotation_project, ← map_sub]
  rw [inner_quarterTurn_rotM_eq]
  simp [Box.actualContactVector, Box.actualDisplacementVector,
    Box.exactEdge, PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem Box.actualDisplacement_eq_sum (box : Box) (p : CayleyPose ℝ)
    (offset : ℝ²) :
    box.actualDisplacement p =
      ∑ i, ⟪cycleDirection (p.matrixPoseWithOffset offset)
          normalizedExactPolyhedron box.outerIndex i,
        proj_xyL ((p.matrixPoseWithOffset offset).innerRot.val.toEuclideanLin
          (normalizedExactVertex (box.innerIndex i))) -
        proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin
          (normalizedExactVertex (box.outerIndex i)))⟫ := by
  have hsum : box.actualDisplacement p =
      ∑ i, ⟪viewVector p, box.actualContactVector p i⟫ := by
    unfold Box.actualDisplacement Box.actualTotalVector
    simp [PiLp.inner_apply, Finset.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  exact box.actualContactValue_eq p offset i

theorem Box.exactSupportValue_le_supportUpper (box : Box)
    (hcenter : box.centerInFour) {p : CayleyPose ℝ}
    (hp : p ∈ box.interval.toReal) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) :
    box.exactSupportValue p i k ≤ (box.supportUpper i k : ℝ) := by
  have hball := box.supportBall_holds hp hcenter i k
  have happrox : box.approxSupportValue p i k ≤
      ((box.supportBall i k).center + (box.supportBall i k).radius : ℚ) := by
    unfold RatBall.Holds at hball
    push_cast
    rw [abs_le] at hball
    linarith
  push_cast at happrox
  have herr := box.supportValue_error p i k
  rw [abs_le] at herr
  calc
    box.exactSupportValue p i k ≤
        box.approxSupportValue p i k + (supportError : ℝ) := by linarith
    _ ≤ (((box.supportBall i k).center +
        (box.supportBall i k).radius + supportError : ℚ) : ℝ) := by
      push_cast
      linarith
    _ = (box.supportUpper i k : ℝ) := by rfl

theorem Box.supportUpper_le_defect (box : Box)
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    box.supportUpper i k ≤ box.defect i := by
  unfold Box.defect
  exact Finset.le_max' _ _
    (Finset.mem_image_of_mem (box.supportUpper i) (Finset.mem_univ k))

theorem Box.supportUpper_self_nonneg (box : Box)
    (i : Fin (box.edgePred + 1)) :
    0 ≤ box.supportUpper i (box.outerIndex i) := by
  simp [Box.supportUpper, Box.supportBall, Box.deltaQ, crossQ,
    dotConstBalls, RatBall.scale, RatBall.add, supportError,
    RationalApprox.κℚ]

theorem Box.defect_nonneg (box : Box) (i : Fin (box.edgePred + 1)) :
    0 ≤ box.defect i :=
  (box.supportUpper_self_nonneg i).trans
    (box.supportUpper_le_defect i (box.outerIndex i))

theorem Box.totalDefect_nonneg (box : Box) : 0 ≤ box.totalDefect := by
  exact Finset.sum_nonneg fun i _ => box.defect_nonneg i

instance (box : Box) : Decidable box.centerInFour := by
  unfold Box.centerInFour
  infer_instance

@[mk_iff]
structure Box.Valid (box : Box) : Prop where
  center_in_four : box.centerInFour
  direction_nonzero : ∀ i,
    (box.supportBall i (box.nonzeroWitness i)).center +
      (box.supportBall i (box.nonzeroWitness i)).radius + supportError < 0
  displacement :
    box.dBound * box.totalDefect + box.displacementError ≤
      box.displacementBall.center - box.displacementBall.radius

instance (box : Box) : Decidable box.Valid :=
  decidable_of_iff _ (Box.valid_iff box).symm

theorem Box.valid_direction_nonzero (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (i : Fin (box.edgePred + 1)) :
    cycleDirection (p.matrixPoseWithOffset offset)
      normalizedExactPolyhedron box.outerIndex i ≠ 0 := by
  have hupper := box.exactSupportValue_le_supportUpper
    h.center_in_four hp i (box.nonzeroWitness i)
  have hneg : box.exactSupportValue p i (box.nonzeroWitness i) < 0 := by
    have hchecked := h.direction_nonzero i
    change box.supportUpper i (box.nonzeroWitness i) < 0 at hchecked
    exact lt_of_le_of_lt hupper (by exact_mod_cast hchecked)
  intro hzero
  have heq := box.exactSupportValue_eq p offset i (box.nonzeroWitness i)
  rw [hzero] at heq
  simp at heq
  linarith

theorem Box.valid_support (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    ⟪cycleDirection (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron box.outerIndex i,
      outerProjectionLinear (p.matrixPoseWithOffset offset)
        (normalizedExactVertex k -
          normalizedExactVertex (box.outerIndex i))⟫ ≤
      (box.defect i : ℝ) := by
  rw [← box.exactSupportValue_eq p offset i k]
  exact (box.exactSupportValue_le_supportUpper
    h.center_in_four hp i k).trans (by
      exact_mod_cast box.supportUpper_le_defect i k)

theorem Box.valid_exactClearedDisplacement (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal) :
    (box.dBound : ℝ) * (box.totalDefect : ℝ) ≤
      box.exactClearedDisplacement p := by
  have hball := box.displacementBall_holds hp h.center_in_four
  have hlower := RatBall.lower_le_of_holds hball
  change (box.displacementBall.center - box.displacementBall.radius : ℚ) ≤
    box.approxClearedDisplacement p at hlower
  push_cast at hlower
  have hchecked :
      (box.dBound : ℝ) * (box.totalDefect : ℝ) +
          (box.displacementError : ℝ) ≤
        box.approxClearedDisplacement p := by
    have hc :
        (box.dBound : ℝ) * (box.totalDefect : ℝ) +
            (box.displacementError : ℝ) ≤
          (box.displacementBall.center : ℝ) -
            (box.displacementBall.radius : ℝ) := by
      exact_mod_cast h.displacement
    exact hc.trans hlower
  have herr := box.clearedDisplacement_error hp
  rw [abs_le] at herr
  linarith

theorem Box.valid_actualDisplacement (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal) :
    (box.totalDefect : ℝ) ≤ box.actualDisplacement p := by
  have hcleared := box.valid_exactClearedDisplacement h hp
  rw [box.exactClearedDisplacement_eq_denom_mul] at hcleared
  have hcharge :
      cayleyDenom p.x p.y p.z * (box.totalDefect : ℝ) ≤
        (box.dBound : ℝ) * (box.totalDefect : ℝ) :=
    mul_le_mul_of_nonneg_right (box.denom_le_dBound hp)
      (by exact_mod_cast box.totalDefect_nonneg)
  exact le_of_mul_le_mul_left (hcharge.trans hcleared)
    (cayleyDenom_pos p.x p.y p.z)

theorem Box.valid_imp_not_translated_rupert (box : Box) (h : box.Valid) :
    ∀ p ∈ box.interval.toReal, ∀ offset : ℝ²,
      ¬ RupertPose (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull := by
  intro p hp offset
  apply not_rupertPose_of_cycle_support_with_defect
    normalizedExactPolyhedron (p.matrixPoseWithOffset offset)
    box.innerIndex box.outerIndex (fun i => (box.defect i : ℝ))
  · exact box.valid_direction_nonzero h hp offset
  · intro i k
    simpa [normalizedExactPolyhedron] using
      box.valid_support h hp offset i k
  · have hactual := box.valid_actualDisplacement h hp
    rw [box.actualDisplacement_eq_sum p offset] at hactual
    simpa [Box.totalDefect, normalizedExactPolyhedron] using hactual

theorem Box.valid_imp_no_translated_rupert_in_interval
    (box : Box) (h : box.Valid) :
    ¬ ∃ p ∈ box.interval.toReal, ∃ offset : ℝ²,
      RupertPose (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull := by
  rintro ⟨p, hp, offset, hrupert⟩
  exact box.valid_imp_not_translated_rupert h p hp offset hrupert

end Noperthedron.SnubCube.CayleyEdgeCertificate

end
