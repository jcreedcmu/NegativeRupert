module

public import Noperthedron.Nopert214.AtlasProjectiveGlobalRigidity
public import Noperthedron.Nopert214.AtlasProjectiveLocalCertificate

@[expose] public section

/-!
# Rational projective balanced-triple certificates for Nopert #214

This checker fills the gap between a full silhouette-cycle certificate and
the symmetry-local theorem.  Three cone-interior moving support directions
balance by determinant weights.  Their direct weighted displacement is a
quadratic in the projective view and a quadratic in the relative Cayley
coordinates, enclosed by nested rational interval arithmetic.
-/

namespace Noperthedron.Nopert214.AtlasProjectiveGlobalCertificate

open Noperthedron.Checker Noperthedron.BalancedSupport
open Noperthedron.SnubCube.ProjectiveView
open AtlasProjectiveView AtlasProjectiveEdgeCertificate
open AtlasProjectiveLocalRigidity
open AtlasProjectiveLocalCertificate

abbrev VectorQ := Fin 3 → ℚ

structure Box where
  interval : AtlasInterval ℚ
  root : Fin 8
  triangle : AtlasProjectiveView.Triangle ℚ
  chart : CayleyAtlas.ChartIndex
  certificate : AxisCertificate
  innerIndex : Fin 3 → VertexIndex
deriving DecidableEq

/-- A local-checker shell lets the global checker reuse the already proved
support, weight, and rational-approximation bounds.  The local-only fields
are irrelevant here. -/
def Box.localShell (box : Box) : AtlasProjectiveLocalCertificate.Box where
  interval := box.interval
  root := box.root
  triangle := box.triangle
  chart := box.chart
  symmetryIndex := 0
  certificate := fun _ => box.certificate
  c := 0
  δ := 0
  r := 0

def Box.supportUpper (box : Box) (i : Fin 3) (k : VertexIndex) : ℚ :=
  box.localShell.supportUpper 0 i k

def Box.weightLower (box : Box) (i : Fin 3) : ℚ :=
  box.localShell.weightLower 0 i

def Box.weightUpper (box : Box) (i : Fin 3) : ℚ :=
  box.localShell.weightUpper 0 i

def Box.contactQuadratic (box : Box) (i c : Fin 3) : RatQuadratic3 :=
  let edge := box.certificate.edgeQ i
  let d := AtlasQuadratic.displacementQuadratic box.chart
    (box.innerIndex i) (box.certificate.index i)
  match c with
  | 0 => RatQuadratic3.scale (edge 1) (d 2) -
      RatQuadratic3.scale (edge 2) (d 1)
  | 1 => RatQuadratic3.scale (edge 2) (d 0) -
      RatQuadratic3.scale (edge 0) (d 2)
  | 2 => RatQuadratic3.scale (edge 0) (d 1) -
      RatQuadratic3.scale (edge 1) (d 0)

/-- For one coefficient of the relative Cayley quadratic, collect the whole
quadratic dependence on the normalized projective view before evaluating an
interval. -/
def Box.viewCoefficientQuadratic (box : Box)
    (coefficient : RatQuadratic3 → ℚ) : RatQuadratic3 :=
  let f := fun i =>
    Noperthedron.SnubCube.ProjectiveLocalCertificate.mulLinear
      (box.certificate.weightCoefficient i)
      (fun c => coefficient (box.contactQuadratic i c))
  f 0 + f 1 + f 2

def Box.coefficientBall (box : Box)
    (coefficient : RatQuadratic3 → ℚ) : RatBall :=
  RatQuadratic3.evalBall box.localShell.triangleBalls
    (box.viewCoefficientQuadratic coefficient)

def Box.relativeBalls (box : Box) : Fin 3 → RatBall :=
  ![box.interval.coordinateBall 2, box.interval.coordinateBall 3,
    box.interval.coordinateBall 4]

def Box.displacementBall (box : Box) : RatBall :=
  let b0 := box.coefficientBall RatQuadratic3.c0
  let bx := box.coefficientBall RatQuadratic3.cx
  let b_y := box.coefficientBall RatQuadratic3.cy
  let bz := box.coefficientBall RatQuadratic3.cz
  let bxx := box.coefficientBall RatQuadratic3.cxx
  let bxy := box.coefficientBall RatQuadratic3.cxy
  let bxz := box.coefficientBall RatQuadratic3.cxz
  let byy := box.coefficientBall RatQuadratic3.cyy
  let byz := box.coefficientBall RatQuadratic3.cyz
  let bzz := box.coefficientBall RatQuadratic3.czz
  let x := box.relativeBalls 0
  let y := box.relativeBalls 1
  let z := box.relativeBalls 2
  RatBall.add
    (RatBall.add
      (RatBall.add
        (RatBall.add
          (RatBall.add
            (RatBall.add
              (RatBall.add
                (RatBall.add
                  (RatBall.add b0 (RatBall.mul bx x))
                  (RatBall.mul b_y y))
                (RatBall.mul bz z))
              (RatBall.mul bxx (RatBall.mul x x)))
            (RatBall.mul bxy (RatBall.mul x y)))
          (RatBall.mul bxz (RatBall.mul x z)))
        (RatBall.mul byy (RatBall.mul y y)))
      (RatBall.mul byz (RatBall.mul y z)))
    (RatBall.mul bzz (RatBall.mul z z))

def Box.dBound (box : Box) : ℚ :=
  1 + AtlasEdgeCertificate.endpointAbsBound
        box.interval.min.x box.interval.max.x ^ 2 +
      AtlasEdgeCertificate.endpointAbsBound
        box.interval.min.y box.interval.max.y ^ 2 +
      AtlasEdgeCertificate.endpointAbsBound
        box.interval.min.z box.interval.max.z ^ 2

def Box.displacementError (box : Box) : ℚ :=
  300 * box.dBound * RationalApprox.κℚ

@[mk_iff]
structure Box.Valid (box : Box) : Prop where
  triangle_valid : SignedTriangleValid box.root box.triangle
  weight_nonneg : ∀ i, 0 ≤ box.weightLower i
  weight_pos : ∃ i, 0 < box.weightLower i
  support : ∀ i k, box.supportUpper i k ≤ 0
  direction_nonzero : ∀ i,
    box.supportUpper i (box.certificate.nonzeroWitness i) < 0
  displacement : box.displacementError ≤
    box.displacementBall.center - box.displacementBall.radius

instance (box : Box) : Decidable box.Valid :=
  decidable_of_iff _ (Box.valid_iff box).symm

@[simp] theorem Box.localShell_supportIndex (box : Box) (i : Fin 3) :
    box.certificate.supportIndex box.localShell i = box.certificate.index i := by
  unfold AxisCertificate.supportIndex Box.localShell symmetryAction
  have horbit :
      (⟨((orbitIndex (box.certificate.index i)).val + (0 : Fin 5).val) % 5,
        Nat.mod_lt _ (by omega)⟩ : OrbitIndex) =
        orbitIndex (box.certificate.index i) := by
    apply Fin.ext
    simp
  rw [horbit]
  exact indexEquiv.symm_apply_apply (box.certificate.index i)

theorem Box.valid_weight_nonneg (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) (i : Fin 3) :
    0 ≤ box.certificate.exactWeight box.localShell p i := by
  have hlower : (0 : ℝ) ≤ (box.weightLower i : ℝ) := by
    exact_mod_cast h.weight_nonneg i
  apply hlower.trans
  exact box.localShell.weightLower_le_exact hscale hmem 0 i

theorem Box.valid_weight_pos (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    ∃ i, 0 < box.certificate.exactWeight box.localShell p i := by
  obtain ⟨i, hi⟩ := h.weight_pos
  refine ⟨i, ?_⟩
  have hiReal : (0 : ℝ) < (box.weightLower i : ℝ) := by exact_mod_cast hi
  exact hiReal.trans_le
    (box.localShell.weightLower_le_exact hscale hmem 0 i)

theorem Box.valid_support (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (i : Fin 3) (k : VertexIndex) :
    inner ℝ (direction box.root p (box.certificate.exactEdge i))
        (outerProjectionLinear (p.matrixPoseWithOffset box.chart offset)
          (exactVertex k)) ≤
      inner ℝ (direction box.root p (box.certificate.exactEdge i))
        (outerProjectionLinear (p.matrixPoseWithOffset box.chart offset)
          (exactVertex (box.certificate.index i))) := by
  have hscaleNe :=
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hscale).ne'
  have hupper := box.localShell.exactSupport_le_upper
    hscale hmem 0 i k
  have hchecked := h.support i k
  have hsigned : box.certificate.exactSupport box.localShell p i k ≤ 0 := by
    apply hupper.trans
    exact_mod_cast hchecked
  have hdiff :
      inner ℝ (direction box.root p (box.certificate.exactEdge i))
          ((outerProjectionLinear (p.matrixPoseWithOffset box.chart offset))
              (exactVertex k) -
            (outerProjectionLinear (p.matrixPoseWithOffset box.chart offset))
              (exactVertex (box.certificate.index i))) =
        box.certificate.exactSupport box.localShell p i k := by
    rw [← map_sub,
      inner_direction_outerProjection_eq_support box.root p box.chart offset
        _ _ hscaleNe]
    unfold AxisCertificate.exactSupport
    congr 2
    simp [AxisCertificate.exactDelta,
      AxisCertificate.exactSelectedVertex]
  rw [inner_sub_right] at hdiff
  linarith

theorem Box.valid_direction_nonzero (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) (i : Fin 3) :
    direction box.root p (box.certificate.exactEdge i) ≠ 0 := by
  intro hzero
  let k := box.certificate.nonzeroWitness i
  have hupper := box.localShell.exactSupport_le_upper hscale hmem 0 i k
  have hstrict : (box.supportUpper i k : ℝ) < 0 := by
    exact_mod_cast h.direction_nonzero i
  have hexact : box.certificate.exactSupport box.localShell p i k < 0 :=
    hupper.trans_lt hstrict
  have hscaleNe :=
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hscale).ne'
  have heq := inner_direction_outerProjection_eq_support box.root p
    box.chart offset (box.certificate.exactEdge i)
    (box.certificate.exactDelta box.localShell i k) hscaleNe
  rw [hzero, inner_zero_left] at heq
  change linearValue (AtlasProjectiveView.normalizedView box.root p)
    (cross3 (box.certificate.exactEdge i)
      (box.certificate.exactDelta box.localShell i k)) < 0 at hexact
  rw [← heq] at hexact
  linarith

noncomputable def Box.approxDisplacementVector (box : Box)
    (p : AtlasPose ℝ) (i : Fin 3) : ℝ³ :=
  AtlasQuadratic.approxDisplacementVector box.chart
    (box.innerIndex i) (box.certificate.index i) p.x p.y p.z

noncomputable def Box.exactDisplacementVector (box : Box)
    (p : AtlasPose ℝ) (i : Fin 3) : ℝ³ :=
  (CayleyAtlas.chartMatrix box.chart *
      cayleyNumeratorMatrix p.x p.y p.z).toEuclideanLin
        (exactVertex (box.innerIndex i)) -
    cayleyDenom p.x p.y p.z • exactVertex (box.certificate.index i)

noncomputable def Box.approxContactVector (box : Box)
    (p : AtlasPose ℝ) (i : Fin 3) : ℝ³ :=
  cross3 (box.certificate.approxEdge i) (box.approxDisplacementVector p i)

noncomputable def Box.exactContactVector (box : Box)
    (p : AtlasPose ℝ) (i : Fin 3) : ℝ³ :=
  cross3 (box.certificate.exactEdge i) (box.exactDisplacementVector p i)

noncomputable def Box.approxClearedDisplacement (box : Box)
    (p : AtlasPose ℝ) : ℝ :=
  ∑ i, box.certificate.approxWeight
      (AtlasProjectiveView.normalizedView box.root p) i *
    linearValue (AtlasProjectiveView.normalizedView box.root p)
      (box.approxContactVector p i)

noncomputable def Box.exactClearedDisplacement (box : Box)
    (p : AtlasPose ℝ) : ℝ :=
  ∑ i, box.certificate.exactWeight box.localShell p i *
    linearValue (AtlasProjectiveView.normalizedView box.root p)
      (box.exactContactVector p i)

theorem Box.eval_contactQuadratic (box : Box) (p : AtlasPose ℝ)
    (i c : Fin 3) :
    (box.contactQuadratic i c).evalReal p.x p.y p.z =
      box.approxContactVector p i c := by
  fin_cases c <;>
    simp [Box.contactQuadratic, Box.approxContactVector,
      Box.approxDisplacementVector, AxisCertificate.approxEdge,
      toR3,
      RatQuadratic3.evalReal_sub,
      RatQuadratic3.evalReal_scale,
      AtlasQuadratic.eval_displacementQuadratic_eq_apply,
      cross3, cross_apply]

theorem Box.eval_viewCoefficientQuadratic (box : Box)
    (coefficient : RatQuadratic3 → ℚ) (n : Fin 3 → ℝ) :
    (box.viewCoefficientQuadratic coefficient).evalReal (n 0) (n 1) (n 2) =
      ∑ i, box.certificate.approxWeight n i *
        linearValue n (fun c => (coefficient (box.contactQuadratic i c) : ℝ)) := by
  simp [Box.viewCoefficientQuadratic, Fin.sum_univ_three,
    Noperthedron.SnubCube.ProjectiveLocalCertificate.evalReal_mulLinear,
    AxisCertificate.approxWeight, linearValue]

theorem Box.coefficientBall_holds (box : Box)
    {n : Fin 3 → ℝ}
    (hmem : InTriangle (toReal box.triangle) n)
    (coefficient : RatQuadratic3 → ℚ) :
    (box.coefficientBall coefficient).Holds
      ((box.viewCoefficientQuadratic coefficient).evalReal (n 0) (n 1) (n 2)) := by
  have hvars : ∀ i, (box.localShell.triangleBalls i).Holds (![n 0, n 1, n 2] i) := by
    intro i
    fin_cases i
    · simpa using box.localShell.triangleBalls_hold hmem 0
    · simpa using box.localShell.triangleBalls_hold hmem 1
    · simpa using box.localShell.triangleBalls_hold hmem 2
  exact RatQuadratic3.evalBall_holds hvars _

theorem Box.relativeBalls_hold (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    ∀ i, (box.relativeBalls i).Holds (![p.x, p.y, p.z] i) := by
  have hmem := AtlasInterval.mem_toReal_iff.mp hp
  intro i
  fin_cases i
  · exact box.interval.coordinateBall_holds hp 2
  · exact box.interval.coordinateBall_holds hp 3
  · exact box.interval.coordinateBall_holds hp 4

noncomputable def Box.reconstructedDisplacement (box : Box)
    (n : Fin 3 → ℝ) (x y z : ℝ) : ℝ :=
  let value := fun coefficient =>
    (box.viewCoefficientQuadratic coefficient).evalReal (n 0) (n 1) (n 2)
  value RatQuadratic3.c0 + value RatQuadratic3.cx*x +
    value RatQuadratic3.cy*y + value RatQuadratic3.cz*z +
    value RatQuadratic3.cxx*(x*x) + value RatQuadratic3.cxy*(x*y) +
    value RatQuadratic3.cxz*(x*z) + value RatQuadratic3.cyy*(y*y) +
    value RatQuadratic3.cyz*(y*z) + value RatQuadratic3.czz*(z*z)

theorem Box.displacementBall_holds_reconstructed (box : Box)
    {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    box.displacementBall.Holds
      (box.reconstructedDisplacement
        (AtlasProjectiveView.normalizedView box.root p) p.x p.y p.z) := by
  let n := AtlasProjectiveView.normalizedView box.root p
  let value := fun coefficient =>
    (box.viewCoefficientQuadratic coefficient).evalReal (n 0) (n 1) (n 2)
  have hc (coefficient : RatQuadratic3 → ℚ) :
      (box.coefficientBall coefficient).Holds (value coefficient) :=
    box.coefficientBall_holds hmem coefficient
  have hx : (box.relativeBalls 0).Holds p.x :=
    box.relativeBalls_hold hp 0
  have hy : (box.relativeBalls 1).Holds p.y :=
    box.relativeBalls_hold hp 1
  have hz : (box.relativeBalls 2).Holds p.z :=
    box.relativeBalls_hold hp 2
  have h0 := hc RatQuadratic3.c0
  have h1 := RatBall.holds_mul (hc RatQuadratic3.cx) hx
  have h2 := RatBall.holds_mul (hc RatQuadratic3.cy) hy
  have h3 := RatBall.holds_mul (hc RatQuadratic3.cz) hz
  have h4 := RatBall.holds_mul (hc RatQuadratic3.cxx)
    (RatBall.holds_mul hx hx)
  have h5 := RatBall.holds_mul (hc RatQuadratic3.cxy)
    (RatBall.holds_mul hx hy)
  have h6 := RatBall.holds_mul (hc RatQuadratic3.cxz)
    (RatBall.holds_mul hx hz)
  have h7 := RatBall.holds_mul (hc RatQuadratic3.cyy)
    (RatBall.holds_mul hy hy)
  have h8 := RatBall.holds_mul (hc RatQuadratic3.cyz)
    (RatBall.holds_mul hy hz)
  have h9 := RatBall.holds_mul (hc RatQuadratic3.czz)
    (RatBall.holds_mul hz hz)
  have hsum := RatBall.holds_add
    (RatBall.holds_add
      (RatBall.holds_add
        (RatBall.holds_add
          (RatBall.holds_add
            (RatBall.holds_add
              (RatBall.holds_add
                (RatBall.holds_add (RatBall.holds_add h0 h1) h2) h3) h4) h5)
            h6) h7) h8) h9
  simpa only [Box.displacementBall, Box.reconstructedDisplacement, value, n]
    using hsum

theorem Box.reconstructedDisplacement_eq_approx (box : Box)
    (p : AtlasPose ℝ) :
    box.reconstructedDisplacement
        (AtlasProjectiveView.normalizedView box.root p) p.x p.y p.z =
      box.approxClearedDisplacement p := by
  simp only [Box.reconstructedDisplacement]
  unfold Box.approxClearedDisplacement
  rw [box.eval_viewCoefficientQuadratic RatQuadratic3.c0,
    box.eval_viewCoefficientQuadratic RatQuadratic3.cx,
    box.eval_viewCoefficientQuadratic RatQuadratic3.cy,
    box.eval_viewCoefficientQuadratic RatQuadratic3.cz,
    box.eval_viewCoefficientQuadratic RatQuadratic3.cxx,
    box.eval_viewCoefficientQuadratic RatQuadratic3.cxy,
    box.eval_viewCoefficientQuadratic RatQuadratic3.cxz,
    box.eval_viewCoefficientQuadratic RatQuadratic3.cyy,
    box.eval_viewCoefficientQuadratic RatQuadratic3.cyz,
    box.eval_viewCoefficientQuadratic RatQuadratic3.czz]
  simp only [Fin.sum_univ_three, linearValue]
  rw [← box.eval_contactQuadratic p 0 0,
    ← box.eval_contactQuadratic p 0 1,
    ← box.eval_contactQuadratic p 0 2,
    ← box.eval_contactQuadratic p 1 0,
    ← box.eval_contactQuadratic p 1 1,
    ← box.eval_contactQuadratic p 1 2,
    ← box.eval_contactQuadratic p 2 0,
    ← box.eval_contactQuadratic p 2 1,
    ← box.eval_contactQuadratic p 2 2]
  simp only [RatQuadratic3.evalReal]
  ring

theorem Box.displacementBall_holds (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    box.displacementBall.Holds (box.approxClearedDisplacement p) := by
  rw [← box.reconstructedDisplacement_eq_approx p]
  exact box.displacementBall_holds_reconstructed hp hmem

private theorem abs_le_endpointAbsBound {lo hi : ℚ} {x : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ)) :
    |x| ≤ (AtlasEdgeCertificate.endpointAbsBound lo hi : ℚ) := by
  rw [abs_le]
  constructor
  · have hlo : -(|lo| : ℚ) ≤ lo := neg_abs_le lo
    have hmax : |lo| ≤ AtlasEdgeCertificate.endpointAbsBound lo hi :=
      le_max_left _ _
    have hrat : -(AtlasEdgeCertificate.endpointAbsBound lo hi) ≤ lo := by
      linarith
    have hreal :
        (-(AtlasEdgeCertificate.endpointAbsBound lo hi : ℚ) : ℝ) ≤
          (lo : ℝ) := by
      exact_mod_cast hrat
    exact hreal.trans hx.1
  · have hhi : hi ≤ |hi| := le_abs_self hi
    have hmax : |hi| ≤ AtlasEdgeCertificate.endpointAbsBound lo hi :=
      le_max_right _ _
    exact hx.2.trans (by exact_mod_cast hhi.trans hmax)

theorem Box.denom_le_dBound (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    cayleyDenom p.x p.y p.z ≤ (box.dBound : ℝ) := by
  have hmem := AtlasInterval.mem_toReal_iff.mp hp
  have hx := abs_le_endpointAbsBound (hmem 2)
  have hy := abs_le_endpointAbsBound (hmem 3)
  have hz := abs_le_endpointAbsBound (hmem 4)
  have hx0 : 0 ≤ (AtlasEdgeCertificate.endpointAbsBound
      box.interval.min.x box.interval.max.x : ℝ) := by
    exact_mod_cast (abs_nonneg box.interval.min.x |>.trans (le_max_left _ _))
  have hy0 : 0 ≤ (AtlasEdgeCertificate.endpointAbsBound
      box.interval.min.y box.interval.max.y : ℝ) := by
    exact_mod_cast (abs_nonneg box.interval.min.y |>.trans (le_max_left _ _))
  have hz0 : 0 ≤ (AtlasEdgeCertificate.endpointAbsBound
      box.interval.min.z box.interval.max.z : ℝ) := by
    exact_mod_cast (abs_nonneg box.interval.min.z |>.trans (le_max_left _ _))
  simp only [Box.dBound]
  push_cast
  have hxsq := (sq_le_sq₀ (abs_nonneg p.x) hx0).2 hx
  have hysq := (sq_le_sq₀ (abs_nonneg p.y) hy0).2 hy
  have hzsq := (sq_le_sq₀ (abs_nonneg p.z) hz0).2 hz
  simp only [cayleyDenom, sq_abs] at ⊢ hxsq hysq hzsq
  linarith

theorem Box.exactDisplacement_sub_approx_norm_le (box : Box)
    (p : AtlasPose ℝ) (i : Fin 3) :
    ‖box.exactDisplacementVector p i - box.approxDisplacementVector p i‖ ≤
      2 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by
  have hrearrange :
      box.exactDisplacementVector p i - box.approxDisplacementVector p i =
        (CayleyAtlas.chartMatrix box.chart *
            cayleyNumeratorMatrix p.x p.y p.z).toEuclideanLin
          (exactVertex (box.innerIndex i) -
            toR3 (rationalVertex (box.innerIndex i))) -
        cayleyDenom p.x p.y p.z •
          (exactVertex (box.certificate.index i) -
            toR3 (rationalVertex (box.certificate.index i))) := by
    unfold Box.exactDisplacementVector Box.approxDisplacementVector
    unfold AtlasQuadratic.approxDisplacementVector
    rw [map_sub]
    module
  rw [hrearrange]
  calc
    _ ≤ ‖(CayleyAtlas.chartMatrix box.chart *
          cayleyNumeratorMatrix p.x p.y p.z).toEuclideanLin
          (exactVertex (box.innerIndex i) -
            toR3 (rationalVertex (box.innerIndex i)))‖ +
        ‖cayleyDenom p.x p.y p.z •
          (exactVertex (box.certificate.index i) -
            toR3 (rationalVertex (box.certificate.index i)))‖ :=
      norm_sub_le _ _
    _ ≤ cayleyDenom p.x p.y p.z * RationalApprox.κ +
        cayleyDenom p.x p.y p.z * RationalApprox.κ := by
      apply add_le_add
      · exact (AtlasEdgeCertificate.norm_chartNumerator_apply_le
          box.chart p.x p.y p.z _).trans
          (mul_le_mul_of_nonneg_left
            (exactApproximation.approx (box.innerIndex i))
            (cayleyDenom_pos p.x p.y p.z).le)
      · rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (cayleyDenom_pos p.x p.y p.z)]
        exact mul_le_mul_of_nonneg_left
          (exactApproximation.approx (box.certificate.index i))
          (cayleyDenom_pos p.x p.y p.z).le
    _ = 2 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by ring

theorem Box.exactDisplacementVector_norm_le (box : Box)
    (p : AtlasPose ℝ) (i : Fin 3) :
    ‖box.exactDisplacementVector p i‖ ≤
      2 * cayleyDenom p.x p.y p.z := by
  unfold Box.exactDisplacementVector
  calc
    _ ≤ ‖(CayleyAtlas.chartMatrix box.chart *
          cayleyNumeratorMatrix p.x p.y p.z).toEuclideanLin
          (exactVertex (box.innerIndex i))‖ +
        ‖cayleyDenom p.x p.y p.z •
          exactVertex (box.certificate.index i)‖ := norm_sub_le _ _
    _ ≤ cayleyDenom p.x p.y p.z + cayleyDenom p.x p.y p.z := by
      apply add_le_add
      · exact (AtlasEdgeCertificate.norm_chartNumerator_apply_le
          box.chart p.x p.y p.z _).trans
          ((mul_le_mul_of_nonneg_left
            (exactVertex_norm_le_one (box.innerIndex i))
            (cayleyDenom_pos p.x p.y p.z).le).trans_eq (mul_one _))
      · rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (cayleyDenom_pos p.x p.y p.z)]
        exact (mul_le_mul_of_nonneg_left
          (exactVertex_norm_le_one (box.certificate.index i))
          (cayleyDenom_pos p.x p.y p.z).le).trans_eq (mul_one _)
    _ = 2 * cayleyDenom p.x p.y p.z := by ring

theorem Box.exactContact_sub_approx_norm_le (box : Box)
    (p : AtlasPose ℝ) (i : Fin 3) :
    ‖box.exactContactVector p i - box.approxContactVector p i‖ ≤
      10 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by
  have hdecomp :
      box.exactContactVector p i - box.approxContactVector p i =
        cross3 (box.certificate.exactEdge i - box.certificate.approxEdge i)
          (box.exactDisplacementVector p i) +
        cross3 (box.certificate.approxEdge i)
          (box.exactDisplacementVector p i -
            box.approxDisplacementVector p i) := by
    ext c
    fin_cases c <;>
      simp [Box.exactContactVector, Box.approxContactVector,
        cross3, cross_apply] <;> ring
  rw [hdecomp]
  calc
    _ ≤ ‖cross3
          (box.certificate.exactEdge i - box.certificate.approxEdge i)
          (box.exactDisplacementVector p i)‖ +
        ‖cross3 (box.certificate.approxEdge i)
          (box.exactDisplacementVector p i -
            box.approxDisplacementVector p i)‖ := norm_add_le _ _
    _ ≤ (2 * RationalApprox.κ) *
          (2 * cayleyDenom p.x p.y p.z) +
        (2 * (1 + RationalApprox.κ)) *
          (2 * cayleyDenom p.x p.y p.z * RationalApprox.κ) := by
      exact add_le_add
        ((cross3_norm_le _ _).trans (mul_le_mul
          (box.certificate.exactEdge_sub_approx_norm_le i)
          (box.exactDisplacementVector_norm_le p i)
          (norm_nonneg _) (by norm_num [RationalApprox.κ])))
        ((cross3_norm_le _ _).trans (mul_le_mul
          (box.certificate.approxEdge_norm_le i)
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

theorem Box.exactContactVector_norm_le (box : Box)
    (p : AtlasPose ℝ) (i : Fin 3) :
    ‖box.exactContactVector p i‖ ≤
      4 * cayleyDenom p.x p.y p.z := by
  unfold Box.exactContactVector
  exact (cross3_norm_le _ _).trans
    ((mul_le_mul (box.certificate.exactEdge_norm_le_two i)
      (box.exactDisplacementVector_norm_le p i) (norm_nonneg _)
      (by positivity)).trans (by ring_nf; rfl))

theorem Box.exactContactValue_abs_le (box : Box)
    {p : AtlasPose ℝ} (hscale : 1 ≤ viewScale box.root p) (i : Fin 3) :
    |linearValue (AtlasProjectiveView.normalizedView box.root p)
        (box.exactContactVector p i)| ≤
      4 * cayleyDenom p.x p.y p.z := by
  rw [linearValue_eq_inner_toLp]
  calc
    _ ≤ ‖normalizedView3 box.localShell p‖ *
        ‖box.exactContactVector p i‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * (4 * cayleyDenom p.x p.y p.z) :=
      mul_le_mul (normalizedView3_norm_le_one box.localShell p hscale)
        (box.exactContactVector_norm_le p i) (norm_nonneg _)
        (by positivity)
    _ = 4 * cayleyDenom p.x p.y p.z := by ring

theorem Box.contactValue_error (box : Box)
    {p : AtlasPose ℝ} (hscale : 1 ≤ viewScale box.root p) (i : Fin 3) :
    |linearValue (AtlasProjectiveView.normalizedView box.root p)
          (box.exactContactVector p i) -
        linearValue (AtlasProjectiveView.normalizedView box.root p)
          (box.approxContactVector p i)| ≤
      10 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by
  rw [linearValue_eq_inner_toLp, linearValue_eq_inner_toLp,
    ← inner_sub_right]
  calc
    _ ≤ ‖normalizedView3 box.localShell p‖ *
        ‖box.exactContactVector p i - box.approxContactVector p i‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ 1 * (10 * cayleyDenom p.x p.y p.z * RationalApprox.κ) :=
      mul_le_mul (normalizedView3_norm_le_one box.localShell p hscale)
        (box.exactContact_sub_approx_norm_le p i) (norm_nonneg _)
        (by positivity)
    _ = 10 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by ring

theorem Box.weightedContact_error (box : Box)
    {p : AtlasPose ℝ} (hscale : 1 ≤ viewScale box.root p) (i : Fin 3) :
    |box.certificate.exactWeight box.localShell p i *
          linearValue (AtlasProjectiveView.normalizedView box.root p)
            (box.exactContactVector p i) -
        box.certificate.approxWeight
            (AtlasProjectiveView.normalizedView box.root p) i *
          linearValue (AtlasProjectiveView.normalizedView box.root p)
            (box.approxContactVector p i)| ≤
      100 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by
  let exactWeight := box.certificate.exactWeight box.localShell p i
  let approxWeight := box.certificate.approxWeight
    (AtlasProjectiveView.normalizedView box.root p) i
  let exactContact := linearValue
    (AtlasProjectiveView.normalizedView box.root p)
    (box.exactContactVector p i)
  let approxContact := linearValue
    (AtlasProjectiveView.normalizedView box.root p)
    (box.approxContactVector p i)
  have hdecomp :
      exactWeight * exactContact - approxWeight * approxContact =
        (exactWeight - approxWeight) * exactContact +
          approxWeight * (exactContact - approxContact) := by ring
  rw [hdecomp]
  calc
    _ ≤ |(exactWeight - approxWeight) * exactContact| +
        |approxWeight * (exactContact - approxContact)| := abs_add_le _ _
    _ = |exactWeight - approxWeight| * |exactContact| +
        |approxWeight| * |exactContact - approxContact| := by
      rw [abs_mul, abs_mul]
    _ ≤ (10 * RationalApprox.κ) *
          (4 * cayleyDenom p.x p.y p.z) +
        (4 + 10 * RationalApprox.κ) *
          (10 * cayleyDenom p.x p.y p.z * RationalApprox.κ) := by
      exact add_le_add
        (mul_le_mul
          (box.certificate.exactWeight_sub_approx_abs_le
            box.localShell hscale i)
          (box.exactContactValue_abs_le hscale i)
          (abs_nonneg _) (by norm_num [RationalApprox.κ]))
        (mul_le_mul
          (box.certificate.approxWeight_abs_le box.localShell hscale i)
          (box.contactValue_error hscale i)
          (abs_nonneg _) (by norm_num [RationalApprox.κ]))
    _ ≤ 100 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by
      have hd := (cayleyDenom_pos p.x p.y p.z).le
      have hk : 0 ≤ RationalApprox.κ := by norm_num [RationalApprox.κ]
      have hfactor : 80 + 100 * RationalApprox.κ ≤ (100 : ℝ) := by
        norm_num [RationalApprox.κ]
      calc
        _ = cayleyDenom p.x p.y p.z * RationalApprox.κ *
            (80 + 100 * RationalApprox.κ) := by ring
        _ ≤ cayleyDenom p.x p.y p.z * RationalApprox.κ * 100 :=
          mul_le_mul_of_nonneg_left hfactor (mul_nonneg hd hk)
        _ = 100 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by ring

theorem Box.clearedDisplacement_error (box : Box)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal)
    (hscale : 1 ≤ viewScale box.root p) :
    |box.exactClearedDisplacement p - box.approxClearedDisplacement p| ≤
      (box.displacementError : ℝ) := by
  have hsum :
      box.exactClearedDisplacement p - box.approxClearedDisplacement p =
        ∑ i, (box.certificate.exactWeight box.localShell p i *
            linearValue (AtlasProjectiveView.normalizedView box.root p)
              (box.exactContactVector p i) -
          box.certificate.approxWeight
              (AtlasProjectiveView.normalizedView box.root p) i *
            linearValue (AtlasProjectiveView.normalizedView box.root p)
              (box.approxContactVector p i)) := by
    unfold Box.exactClearedDisplacement Box.approxClearedDisplacement
    rw [Finset.sum_sub_distrib]
  rw [hsum]
  calc
    _ ≤ ∑ i, |box.certificate.exactWeight box.localShell p i *
            linearValue (AtlasProjectiveView.normalizedView box.root p)
              (box.exactContactVector p i) -
          box.certificate.approxWeight
              (AtlasProjectiveView.normalizedView box.root p) i *
            linearValue (AtlasProjectiveView.normalizedView box.root p)
              (box.approxContactVector p i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3,
        100 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by
      apply Finset.sum_le_sum
      intro i _
      exact box.weightedContact_error hscale i
    _ = 300 * cayleyDenom p.x p.y p.z * RationalApprox.κ := by
      simp
      ring
    _ ≤ 300 * (box.dBound : ℝ) * RationalApprox.κ := by
      have hk : 0 ≤ RationalApprox.κ := by norm_num [RationalApprox.κ]
      nlinarith [box.denom_le_dBound hp]
    _ = (box.displacementError : ℝ) := by
      simp [Box.displacementError, RationalApprox.κ, RationalApprox.κℚ]

noncomputable def Box.actualDisplacementVector (box : Box)
    (p : AtlasPose ℝ) (i : Fin 3) : ℝ³ :=
  (CayleyAtlas.chartMatrix box.chart *
      cayleyMatrix p.x p.y p.z).toEuclideanLin
        (exactVertex (box.innerIndex i)) -
    exactVertex (box.certificate.index i)

noncomputable def Box.actualClearedDisplacement (box : Box)
    (p : AtlasPose ℝ) : ℝ :=
  ∑ i, box.certificate.exactWeight box.localShell p i *
    linearValue (AtlasProjectiveView.normalizedView box.root p)
      (cross3 (box.certificate.exactEdge i)
        (box.actualDisplacementVector p i))

theorem Box.exactDisplacementVector_eq_denom_smul (box : Box)
    (p : AtlasPose ℝ) (i : Fin 3) :
    box.exactDisplacementVector p i =
      cayleyDenom p.x p.y p.z • box.actualDisplacementVector p i := by
  unfold Box.exactDisplacementVector Box.actualDisplacementVector
  rw [AtlasEdgeCertificate.chart_numerator_apply_eq_denom_smul, ← smul_sub]

theorem Box.exactContactVector_eq_denom_smul (box : Box)
    (p : AtlasPose ℝ) (i : Fin 3) :
    box.exactContactVector p i =
      cayleyDenom p.x p.y p.z •
        cross3 (box.certificate.exactEdge i)
          (box.actualDisplacementVector p i) := by
  unfold Box.exactContactVector
  rw [box.exactDisplacementVector_eq_denom_smul, cross3_smul_right]

theorem Box.exactClearedDisplacement_eq_denom_mul (box : Box)
    (p : AtlasPose ℝ) :
    box.exactClearedDisplacement p =
      cayleyDenom p.x p.y p.z * box.actualClearedDisplacement p := by
  unfold Box.exactClearedDisplacement Box.actualClearedDisplacement
  simp_rw [box.exactContactVector_eq_denom_smul]
  simp only [linearValue, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem Box.actualContactValue_eq_pose (box : Box)
    {p : AtlasPose ℝ} (offset : ℝ²)
    (hscale : viewScale box.root p ≠ 0) (i : Fin 3) :
    linearValue (AtlasProjectiveView.normalizedView box.root p)
        (cross3 (box.certificate.exactEdge i)
          (box.actualDisplacementVector p i)) =
      inner ℝ (direction box.root p (box.certificate.exactEdge i))
        (proj_xyL
            ((p.matrixPoseWithOffset box.chart offset).innerRot.val.toEuclideanLin
              (exactVertex (box.innerIndex i))) -
          outerProjectionLinear (p.matrixPoseWithOffset box.chart offset)
            (exactVertex (box.certificate.index i))) := by
  rw [← inner_direction_outerProjection_eq_support box.root p box.chart offset
    (box.certificate.exactEdge i) (box.actualDisplacementVector p i) hscale]
  congr 2
  unfold Box.actualDisplacementVector
  rw [map_sub]
  have hrelative :
      outerProjectionLinear (p.matrixPoseWithOffset box.chart offset)
          ((CayleyAtlas.chartMatrix box.chart *
              cayleyMatrix p.x p.y p.z).toEuclideanLin
            (exactVertex (box.innerIndex i))) =
        rotM p.θ p.φ
          ((CayleyAtlas.chartMatrix box.chart *
              cayleyMatrix p.x p.y p.z).toEuclideanLin
            (exactVertex (box.innerIndex i))) := by
    simpa [outerProjectionLinear, ContinuousLinearMap.comp_apply] using
      p.matrixPoseWithOffset_outer_rotation_project box.chart offset
        ((CayleyAtlas.chartMatrix box.chart *
            cayleyMatrix p.x p.y p.z).toEuclideanLin
          (exactVertex (box.innerIndex i)))
  rw [hrelative,
    ← p.matrixPoseWithOffset_inner_rotation_project box.chart offset
      (exactVertex (box.innerIndex i))]

theorem Box.actualClearedDisplacement_eq_pose (box : Box)
    {p : AtlasPose ℝ} (offset : ℝ²)
    (hscale : viewScale box.root p ≠ 0) :
    box.actualClearedDisplacement p =
      ∑ i, box.certificate.exactWeight box.localShell p i *
        inner ℝ (direction box.root p (box.certificate.exactEdge i))
          (proj_xyL
              ((p.matrixPoseWithOffset box.chart offset).innerRot.val.toEuclideanLin
                (exactVertex (box.innerIndex i))) -
            outerProjectionLinear (p.matrixPoseWithOffset box.chart offset)
              (exactVertex (box.certificate.index i))) := by
  unfold Box.actualClearedDisplacement
  apply Finset.sum_congr rfl
  intro i _
  rw [box.actualContactValue_eq_pose offset hscale i]

theorem Box.valid_exactClearedDisplacement (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    0 ≤ box.exactClearedDisplacement p := by
  have hball := box.displacementBall_holds hp hmem
  have hlower := RatBall.lower_le_of_holds hball
  change (box.displacementBall.center - box.displacementBall.radius : ℚ) ≤
    box.approxClearedDisplacement p at hlower
  push_cast at hlower
  have hchecked : (box.displacementError : ℝ) ≤
      (box.displacementBall.center : ℝ) -
        (box.displacementBall.radius : ℝ) := by
    exact_mod_cast h.displacement
  have herr := box.clearedDisplacement_error hp hscale
  rw [abs_le] at herr
  linarith

theorem Box.valid_actualClearedDisplacement (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    0 ≤ box.actualClearedDisplacement p := by
  have hexact := box.valid_exactClearedDisplacement h hp hscale hmem
  rw [box.exactClearedDisplacement_eq_denom_mul] at hexact
  exact nonneg_of_mul_nonneg_right hexact (cayleyDenom_pos p.x p.y p.z)

theorem Box.valid_imp_not_translated_rupert (box : Box) (h : box.Valid) :
    ∀ p ∈ box.interval.toReal,
      1 ≤ viewScale box.root p →
      InTriangle (toReal box.triangle)
        (AtlasProjectiveView.normalizedView box.root p) →
      ∀ offset : ℝ²,
        ¬ RupertPose (p.matrixPoseWithOffset box.chart offset)
          exactPolyhedron.hull := by
  intro p hp hscale hmem offset
  have hscaleNe : viewScale box.root p ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hscale).ne'
  apply AtlasProjectiveGlobalRigidity.not_rupertPose_of_projective_global_certificate
    box.root p box.chart offset (fun i => box.certificate.exactEdge i)
    box.innerIndex box.certificate.index hscaleNe
  · exact box.valid_direction_nonzero h offset hscale hmem
  · intro i
    simpa [AxisCertificate.exactWeight, Box.localShell] using
      box.valid_weight_nonneg h hscale hmem i
  · obtain ⟨i, hi⟩ := box.valid_weight_pos h hscale hmem
    exact ⟨i, by simpa [AxisCertificate.exactWeight, Box.localShell] using hi⟩
  · exact box.valid_support h offset hscale hmem
  · have hactual := box.valid_actualClearedDisplacement h hp hscale hmem
    rw [box.actualClearedDisplacement_eq_pose offset hscaleNe] at hactual
    simpa [AxisCertificate.exactWeight, Box.localShell] using hactual

theorem Box.valid_imp_no_translated_rupert_in_interval
    (box : Box) (h : box.Valid) :
    ¬ ∃ p ∈ box.interval.toReal,
      1 ≤ viewScale box.root p ∧
      InTriangle (toReal box.triangle)
        (AtlasProjectiveView.normalizedView box.root p) ∧
      ∃ offset : ℝ²,
        RupertPose (p.matrixPoseWithOffset box.chart offset)
          exactPolyhedron.hull := by
  rintro ⟨p, hp, hscale, hmem, offset, hrupert⟩
  exact box.valid_imp_not_translated_rupert h p hp hscale hmem offset hrupert

end Noperthedron.Nopert214.AtlasProjectiveGlobalCertificate

end
