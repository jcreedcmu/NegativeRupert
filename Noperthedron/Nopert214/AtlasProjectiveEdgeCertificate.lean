module

public import Noperthedron.Nopert214.AtlasProjectiveView

@[expose] public section

/-!
# Projective edge-cycle certificates for the Nopert #214 atlas

The two outer viewing angles are replaced by a signed rational projective
triangle.  Support and denominator-cleared displacement are linear in the
normalized viewing vector, so their extrema occur at triangle corners.
-/

namespace Noperthedron.Nopert214.AtlasProjectiveEdgeCertificate

open scoped RealInnerProductSpace
open Noperthedron.Checker
open Noperthedron.BalancedSupport
open Noperthedron.SnubCube.ProjectiveView
open AtlasEdgeCertificate AtlasProjectiveView
open CayleyAtlas

def max3 (f : Fin 3 → ℚ) : ℚ := max (f 0) (max (f 1) (f 2))
def min3 (f : Fin 3 → ℚ) : ℚ := min (f 0) (min (f 1) (f 2))

theorem le_max3 (f : Fin 3 → ℚ) (i : Fin 3) : f i ≤ max3 f := by
  fin_cases i <;> simp [max3]

theorem min3_le (f : Fin 3 → ℚ) (i : Fin 3) : min3 f ≤ f i := by
  fin_cases i <;> simp [min3]

def dotQ (a b : Fin 3 → ℚ) : ℚ :=
  a 0*b 0 + a 1*b 1 + a 2*b 2

def SignedTriangleValid (root : Fin 8)
    (triangle : AtlasProjectiveView.Triangle ℚ) : Prop :=
  ∀ i, (∀ c, 0 ≤ rootSign root c * triangle i c) ∧
    (∑ c, rootSign root c * triangle i c) = 1

instance (root : Fin 8) (triangle : AtlasProjectiveView.Triangle ℚ) :
    Decidable (SignedTriangleValid root triangle) := by
  unfold SignedTriangleValid
  infer_instance

def SignedPointValid (root : Fin 8)
    (point : AtlasProjectiveView.Vector ℚ) : Prop :=
  (∀ c, 0 ≤ rootSign root c * point c) ∧
    (∑ c, rootSign root c * point c) = 1

theorem signedPointValid_midpoint {root : Fin 8}
    {a b : AtlasProjectiveView.Vector ℚ}
    (ha : SignedPointValid root a) (hb : SignedPointValid root b) :
    SignedPointValid root
      (Noperthedron.SnubCube.ProjectiveView.midpoint a b) := by
  constructor
  · intro c
    simp only [Noperthedron.SnubCube.ProjectiveView.midpoint]
    nlinarith [ha.1 c, hb.1 c]
  · simp only [Noperthedron.SnubCube.ProjectiveView.midpoint,
      Fin.sum_univ_three]
    have ha' := ha.2
    have hb' := hb.2
    simp only [Fin.sum_univ_three] at ha' hb'
    linear_combination (ha' + hb') / 2

theorem rootTriangle_valid (root : Fin 8) :
    SignedTriangleValid root (rootTriangle root) := by
  intro i
  constructor
  · intro c
    by_cases h : i = c
    · subst c
      simp only [rootTriangle, signedBasis, if_pos]
      exact mul_self_nonneg _
    · simp [rootTriangle, signedBasis, h]
  · fin_cases i
    · simp [rootTriangle, signedBasis]
      nlinarith [rootSign_sq root 0]
    · simp [rootTriangle, signedBasis]
      nlinarith [rootSign_sq root 1]
    · simp [rootTriangle, signedBasis]
      nlinarith [rootSign_sq root 2]

theorem SignedTriangleValid.split {root : Fin 8}
    {triangle : AtlasProjectiveView.Triangle ℚ}
    (h : SignedTriangleValid root triangle) (child : Fin 4) :
    SignedTriangleValid root
      (Noperthedron.SnubCube.ProjectiveView.split triangle child) := by
  have hp (i : Fin 3) : SignedPointValid root (triangle i) := h i
  intro i
  change SignedPointValid root
    (Noperthedron.SnubCube.ProjectiveView.split triangle child i)
  fin_cases child
  · fin_cases i
    · simpa [Noperthedron.SnubCube.ProjectiveView.split] using hp 0
    · simpa [Noperthedron.SnubCube.ProjectiveView.split] using
        signedPointValid_midpoint (hp 0) (hp 1)
    · simpa [Noperthedron.SnubCube.ProjectiveView.split] using
        signedPointValid_midpoint (hp 0) (hp 2)
  · fin_cases i
    · simpa [Noperthedron.SnubCube.ProjectiveView.split] using
        signedPointValid_midpoint (hp 0) (hp 1)
    · simpa [Noperthedron.SnubCube.ProjectiveView.split] using hp 1
    · simpa [Noperthedron.SnubCube.ProjectiveView.split] using
        signedPointValid_midpoint (hp 1) (hp 2)
  · fin_cases i
    · simpa [Noperthedron.SnubCube.ProjectiveView.split] using
        signedPointValid_midpoint (hp 0) (hp 2)
    · simpa [Noperthedron.SnubCube.ProjectiveView.split] using
        signedPointValid_midpoint (hp 1) (hp 2)
    · simpa [Noperthedron.SnubCube.ProjectiveView.split] using hp 2
  · fin_cases i
    · simpa [Noperthedron.SnubCube.ProjectiveView.split] using
        signedPointValid_midpoint (hp 0) (hp 1)
    · simpa [Noperthedron.SnubCube.ProjectiveView.split] using
        signedPointValid_midpoint (hp 1) (hp 2)
    · have hm : Noperthedron.SnubCube.ProjectiveView.midpoint
          (triangle 0) (triangle 2) =
          Noperthedron.SnubCube.ProjectiveView.midpoint
            (triangle 2) (triangle 0) := by
        funext c
        simp [Noperthedron.SnubCube.ProjectiveView.midpoint, add_comm]
      change SignedPointValid root
        (Noperthedron.SnubCube.ProjectiveView.midpoint
          (triangle 2) (triangle 0))
      rw [← hm]
      exact signedPointValid_midpoint (hp 0) (hp 2)

structure Box where
  interval : AtlasInterval ℚ
  root : Fin 8
  triangle : AtlasProjectiveView.Triangle ℚ
  chart : CayleyAtlas.ChartIndex
  edgePred : ℕ
  outerIndex : Fin (edgePred + 1) → VertexIndex
  innerIndex : Fin (edgePred + 1) → VertexIndex
  nonzeroWitness : Fin (edgePred + 1) → VertexIndex

def Box.edgeShell (box : Box) : AtlasEdgeCertificate.Box where
  interval := box.interval
  chart := box.chart
  edgePred := box.edgePred
  outerIndex := box.outerIndex
  innerIndex := box.innerIndex
  nonzeroWitness := box.nonzeroWitness

def Box.supportAt (box : Box) (j : Fin 3)
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) : ℚ :=
  dotQ (box.triangle j)
    (crossQ (box.edgeShell.edgeQ i) (box.edgeShell.deltaQ i k))

def Box.supportUpper (box : Box) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) : ℚ :=
  max3 (fun j => box.supportAt j i k) + supportError

def Box.defect (box : Box) (i : Fin (box.edgePred + 1)) : ℚ :=
  (Finset.image (box.supportUpper i) Finset.univ).max' (by
    simp only [Finset.image_nonempty]
    exact Finset.univ_nonempty)

def Box.totalDefect (box : Box) : ℚ := ∑ i, box.defect i

def Box.displacementAt (box : Box) (j : Fin 3) : RatBall :=
  dotConstBalls (box.triangle j) box.edgeShell.displacementComponents

def Box.displacementLower (box : Box) : ℚ :=
  min3 fun j => (box.displacementAt j).center - (box.displacementAt j).radius

@[mk_iff]
structure Box.Valid (box : Box) : Prop where
  triangle_valid : SignedTriangleValid box.root box.triangle
  direction_nonzero : ∀ i,
    box.supportUpper i (box.nonzeroWitness i) < 0
  displacement :
    box.edgeShell.dBound * box.totalDefect +
      box.edgeShell.displacementError ≤ box.displacementLower

instance (box : Box) : Decidable box.Valid :=
  decidable_of_iff _ (Box.valid_iff box).symm

noncomputable def Box.projectiveApproxSupport (box : Box)
    (p : AtlasPose ℝ) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) : ℝ :=
  linearValue (AtlasProjectiveView.normalizedView box.root p)
    (cross3 (box.edgeShell.approxEdge i) (box.edgeShell.approxDelta i k))

noncomputable def Box.projectiveApproxDisplacement (box : Box)
    (p : AtlasPose ℝ) : ℝ :=
  linearValue (AtlasProjectiveView.normalizedView box.root p)
    (box.edgeShell.approxTotalVector p)

theorem Box.approxSupport_eq_viewScale_mul (box : Box)
    (p : AtlasPose ℝ) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) (hscale : viewScale box.root p ≠ 0) :
    box.edgeShell.approxSupportValue p i k =
      viewScale box.root p * box.projectiveApproxSupport p i k := by
  simp [Box.projectiveApproxSupport, linearValue,
    AtlasProjectiveView.normalizedView,
    AtlasEdgeCertificate.Box.approxSupportValue,
    PiLp.inner_apply, Fin.sum_univ_three]
  field_simp [hscale]

theorem Box.approxDisplacement_eq_viewScale_mul (box : Box)
    (p : AtlasPose ℝ) (hscale : viewScale box.root p ≠ 0) :
    box.edgeShell.approxClearedDisplacement p =
      viewScale box.root p * box.projectiveApproxDisplacement p := by
  simp [Box.projectiveApproxDisplacement, linearValue,
    AtlasProjectiveView.normalizedView,
    AtlasEdgeCertificate.Box.approxClearedDisplacement,
    PiLp.inner_apply, Fin.sum_univ_three]
  field_simp [hscale]

theorem Box.supportAt_cast (box : Box) (j : Fin 3)
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    (box.supportAt j i k : ℝ) =
      linearValue (toReal box.triangle j)
        (cross3 (box.edgeShell.approxEdge i)
          (box.edgeShell.approxDelta i k)) := by
  simp [Box.supportAt, dotQ, linearValue, toReal,
    AtlasEdgeCertificate.Box.approxEdge,
    AtlasEdgeCertificate.Box.approxDelta, toR3, crossQ, cross3,
    cross_apply]

theorem Box.projectiveApproxSupport_le (box : Box) {p : AtlasPose ℝ}
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    box.projectiveApproxSupport p i k ≤
      (max3 (fun j => box.supportAt j i k) : ℝ) := by
  unfold Box.projectiveApproxSupport
  apply linearValue_le_of_mem hmem
  intro j
  rw [← box.supportAt_cast j i k]
  exact_mod_cast le_max3 (fun j => box.supportAt j i k) j

theorem Box.displacementAt_holds (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) (j : Fin 3) :
    (box.displacementAt j).Holds
      (linearValue (toReal box.triangle j)
        (box.edgeShell.approxTotalVector p)) := by
  have hvars : ∀ c : Fin 3,
      (box.edgeShell.variableBalls c).Holds (![p.x, p.y, p.z] c) := by
    intro c
    fin_cases c
    · exact box.interval.coordinateBall_holds hp 2
    · exact box.interval.coordinateBall_holds hp 3
    · exact box.interval.coordinateBall_holds hp 4
  have hcomponents : ∀ c,
      (box.edgeShell.displacementComponents c).Holds
        (box.edgeShell.approxTotalVector p c) := by
    intro c
    have hc := RatQuadratic3.evalBall_holds hvars
      (box.edgeShell.totalQuadratic c)
    rw [box.edgeShell.eval_totalQuadratic_pose] at hc
    exact hc
  have hdot := dotConstBalls_holds (a := box.triangle j) hcomponents
  simpa [Box.displacementAt, linearValue, toReal,
    Fin.sum_univ_three, mul_comm] using hdot

theorem Box.displacementLower_le_projectiveApprox (box : Box)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    (box.displacementLower : ℝ) ≤ box.projectiveApproxDisplacement p := by
  unfold Box.projectiveApproxDisplacement
  apply le_linearValue_of_mem hmem
  intro j
  have hball := box.displacementAt_holds hp j
  have hlower := RatBall.lower_le_of_holds hball
  have hmin := min3_le
    (fun j => (box.displacementAt j).center -
      (box.displacementAt j).radius) j
  change (box.displacementLower : ℝ) ≤ _
  have hminReal : (box.displacementLower : ℝ) ≤
      (((box.displacementAt j).center -
        (box.displacementAt j).radius : ℚ) : ℝ) := by
    exact_mod_cast hmin
  exact hminReal.trans hlower

theorem Box.supportUpper_le_defect (box : Box)
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    box.supportUpper i k ≤ box.defect i := by
  unfold Box.defect
  exact Finset.le_max' _ _
    (Finset.mem_image_of_mem (box.supportUpper i) (Finset.mem_univ k))

theorem Box.supportUpper_self_nonneg (box : Box)
    (i : Fin (box.edgePred + 1)) :
    0 ≤ box.supportUpper i (box.outerIndex i) := by
  simp [Box.supportUpper, Box.supportAt, Box.edgeShell,
    AtlasEdgeCertificate.Box.deltaQ, crossQ, dotQ, max3,
    supportError, RationalApprox.κℚ]

theorem Box.defect_nonneg (box : Box) (i : Fin (box.edgePred + 1)) :
    0 ≤ box.defect i :=
  (box.supportUpper_self_nonneg i).trans
    (box.supportUpper_le_defect i (box.outerIndex i))

theorem Box.totalDefect_nonneg (box : Box) : 0 ≤ box.totalDefect :=
  Finset.sum_nonneg fun i _ => box.defect_nonneg i

theorem Box.exactSupport_le_scaledUpper (box : Box)
    {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    box.edgeShell.exactSupportValue p i k ≤
      viewScale box.root p * (box.supportUpper i k : ℝ) := by
  have hscalePos : 0 < viewScale box.root p :=
    lt_of_lt_of_le (by norm_num) hscale
  have hprojective := box.projectiveApproxSupport_le hmem i k
  have happroxEq := box.approxSupport_eq_viewScale_mul
    p i k hscalePos.ne'
  have happrox : box.edgeShell.approxSupportValue p i k ≤
      viewScale box.root p *
        (max3 (fun j => box.supportAt j i k) : ℝ) := by
    rw [happroxEq]
    exact mul_le_mul_of_nonneg_left hprojective hscalePos.le
  have herr := box.edgeShell.supportValue_error p i k
  rw [abs_le] at herr
  have herrorNonneg : (0 : ℝ) ≤ (supportError : ℝ) := by
    norm_num [supportError, RationalApprox.κℚ]
  have herrorScaled : (supportError : ℝ) ≤
      viewScale box.root p * (supportError : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hscale herrorNonneg
  calc
    box.edgeShell.exactSupportValue p i k ≤
        box.edgeShell.approxSupportValue p i k +
          (supportError : ℝ) := by linarith [herr.2]
    _ ≤ viewScale box.root p *
          (max3 (fun j => box.supportAt j i k) : ℝ) +
        viewScale box.root p * (supportError : ℝ) :=
      add_le_add happrox herrorScaled
    _ = viewScale box.root p * (box.supportUpper i k : ℝ) := by
      unfold Box.supportUpper
      push_cast
      ring

theorem Box.valid_direction_nonzero (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (i : Fin (box.edgePred + 1)) :
    cycleDirection (p.matrixPoseWithOffset box.chart offset)
      exactPolyhedron box.outerIndex i ≠ 0 := by
  have hupper := box.exactSupport_le_scaledUpper hscale hmem i
    (box.nonzeroWitness i)
  have hupperNeg : (box.supportUpper i (box.nonzeroWitness i) : ℝ) < 0 := by
    exact_mod_cast h.direction_nonzero i
  have hscalePos : 0 < viewScale box.root p :=
    lt_of_lt_of_le (by norm_num) hscale
  have hexactNeg : box.edgeShell.exactSupportValue p i
      (box.nonzeroWitness i) < 0 :=
    lt_of_le_of_lt hupper (mul_neg_of_pos_of_neg hscalePos hupperNeg)
  intro hzero
  have heq := box.edgeShell.exactSupportValue_eq p offset i
    (box.nonzeroWitness i)
  have hzeroShell : cycleDirection
      (p.matrixPoseWithOffset box.edgeShell.chart offset)
      exactPolyhedron box.edgeShell.outerIndex i = 0 := by
    simpa [Box.edgeShell] using hzero
  rw [hzeroShell] at heq
  simp at heq
  exact (ne_of_lt hexactNeg) heq

theorem Box.valid_support (box : Box) (_h : box.Valid)
    {p : AtlasPose ℝ} (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p))
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    ⟪cycleDirection (p.matrixPoseWithOffset box.chart offset)
        exactPolyhedron box.outerIndex i,
      outerProjectionLinear (p.matrixPoseWithOffset box.chart offset)
        (exactVertex k - exactVertex (box.outerIndex i))⟫ ≤
      viewScale box.root p * (box.defect i : ℝ) := by
  have heq := box.edgeShell.exactSupportValue_eq p offset i k
  simp only [Box.edgeShell] at heq
  rw [← heq]
  exact (box.exactSupport_le_scaledUpper hscale hmem i k).trans
    (mul_le_mul_of_nonneg_left
      (by exact_mod_cast box.supportUpper_le_defect i k)
      (le_trans (by norm_num) hscale))

theorem Box.valid_exactClearedDisplacement (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    viewScale box.root p * (box.edgeShell.dBound : ℝ) *
        (box.totalDefect : ℝ) ≤
      box.edgeShell.exactClearedDisplacement p := by
  have hscalePos : 0 < viewScale box.root p :=
    lt_of_lt_of_le (by norm_num) hscale
  have hprojective := box.displacementLower_le_projectiveApprox hp hmem
  have happroxEq := box.approxDisplacement_eq_viewScale_mul p hscalePos.ne'
  have happroxLower : viewScale box.root p *
      (box.displacementLower : ℝ) ≤
      box.edgeShell.approxClearedDisplacement p := by
    calc
      _ ≤ viewScale box.root p * box.projectiveApproxDisplacement p :=
        mul_le_mul_of_nonneg_left hprojective hscalePos.le
      _ = box.edgeShell.approxClearedDisplacement p := happroxEq.symm
  have hchecked : (box.edgeShell.dBound : ℝ) *
        (box.totalDefect : ℝ) +
        (box.edgeShell.displacementError : ℝ) ≤
      (box.displacementLower : ℝ) := by
    exact_mod_cast h.displacement
  have hcharged : viewScale box.root p *
        ((box.edgeShell.dBound : ℝ) * (box.totalDefect : ℝ) +
          (box.edgeShell.displacementError : ℝ)) ≤
      box.edgeShell.approxClearedDisplacement p :=
    (mul_le_mul_of_nonneg_left hchecked hscalePos.le).trans happroxLower
  have herr := box.edgeShell.clearedDisplacement_error hp
  rw [abs_le] at herr
  have herrorNonneg : (0 : ℝ) ≤
      (box.edgeShell.displacementError : ℝ) := by
    have hq : (0 : ℚ) ≤ box.edgeShell.displacementError := by
      have hd : (0 : ℚ) ≤ box.edgeShell.dBound := by
        unfold AtlasEdgeCertificate.Box.dBound
        positivity
      unfold AtlasEdgeCertificate.Box.displacementError
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) (by norm_num)) hd)
        (by norm_num [RationalApprox.κℚ])
    exact_mod_cast hq
  have herrorScaled : (box.edgeShell.displacementError : ℝ) ≤
      viewScale box.root p * (box.edgeShell.displacementError : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hscale herrorNonneg
  nlinarith [herr.1]

theorem Box.valid_actualDisplacement (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    viewScale box.root p * (box.totalDefect : ℝ) ≤
      box.edgeShell.actualDisplacement p := by
  have hcleared := box.valid_exactClearedDisplacement h hp hscale hmem
  rw [box.edgeShell.exactClearedDisplacement_eq_denom_mul] at hcleared
  have hcharge : viewScale box.root p *
      (cayleyDenom p.x p.y p.z * (box.totalDefect : ℝ)) ≤
      viewScale box.root p *
        ((box.edgeShell.dBound : ℝ) * (box.totalDefect : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (le_trans (by norm_num) hscale)
    exact mul_le_mul_of_nonneg_right (box.edgeShell.denom_le_dBound hp)
      (by exact_mod_cast box.totalDefect_nonneg)
  have hmul : cayleyDenom p.x p.y p.z *
      (viewScale box.root p * (box.totalDefect : ℝ)) ≤
      cayleyDenom p.x p.y p.z * box.edgeShell.actualDisplacement p := by
    calc
      _ = viewScale box.root p *
          (cayleyDenom p.x p.y p.z * (box.totalDefect : ℝ)) := by ring
      _ ≤ viewScale box.root p *
          ((box.edgeShell.dBound : ℝ) * (box.totalDefect : ℝ)) := hcharge
      _ ≤ cayleyDenom p.x p.y p.z *
          box.edgeShell.actualDisplacement p := by simpa [mul_assoc] using hcleared
  exact le_of_mul_le_mul_left hmul (cayleyDenom_pos p.x p.y p.z)

theorem Box.valid_imp_not_translated_rupert (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset)
      exactPolyhedron.hull := by
  apply not_rupertPose_of_cycle_support_with_defect
    exactPolyhedron (p.matrixPoseWithOffset box.chart offset)
    box.innerIndex box.outerIndex
    (fun i => viewScale box.root p * (box.defect i : ℝ))
  · exact box.valid_direction_nonzero h offset hscale hmem
  · intro i k
    simpa [exactPolyhedron] using box.valid_support h offset hscale hmem i k
  · have hactual := box.valid_actualDisplacement h hp hscale hmem
    rw [box.edgeShell.actualDisplacement_eq_sum p offset] at hactual
    rw [Box.totalDefect] at hactual
    push_cast at hactual
    rw [Finset.mul_sum] at hactual
    convert hactual using 1
    all_goals simp [Box.edgeShell]
    all_goals rfl

end Noperthedron.Nopert214.AtlasProjectiveEdgeCertificate

end
