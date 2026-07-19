module

public import Noperthedron.SnubCube.ProjectiveView

@[expose] public section


/-!
# Edge-cycle certificates over projective view triangles

The outer viewing vector is normalized by the sum of its positive
coordinates.  Support and denominator-cleared displacement are linear in
that normalized vector, so an entire rational view triangle is controlled by
its three vertices.  The remaining Cayley dependence is the same exact
quadratic arithmetic as `CayleyEdgeCertificate`.
-/

namespace Noperthedron.SnubCube.ProjectiveEdgeCertificate

open scoped RealInnerProductSpace
open Noperthedron.Checker
open Noperthedron.BalancedSupport
open CayleyEdgeCertificate
open ProjectiveView

def TriangleValid (triangle : Triangle ℚ) : Prop :=
  ∀ i, (∀ c, 0 ≤ triangle i c) ∧ (∑ c, triangle i c) = 1

instance (triangle : Triangle ℚ) : Decidable (TriangleValid triangle) := by
  unfold TriangleValid
  infer_instance

def max3 (f : Fin 3 → ℚ) : ℚ := max (f 0) (max (f 1) (f 2))
def min3 (f : Fin 3 → ℚ) : ℚ := min (f 0) (min (f 1) (f 2))

theorem le_max3 (f : Fin 3 → ℚ) (i : Fin 3) : f i ≤ max3 f := by
  fin_cases i <;> simp [max3]

theorem min3_le (f : Fin 3 → ℚ) (i : Fin 3) : min3 f ≤ f i := by
  fin_cases i <;> simp [min3]

def dotQ (a b : Fin 3 → ℚ) : ℚ := a 0*b 0 + a 1*b 1 + a 2*b 2

structure Box where
  interval : CayleyInterval ℚ
  triangle : Triangle ℚ
  edgePred : ℕ
  outerIndex : Fin (edgePred + 1) → VertexIndex
  innerIndex : Fin (edgePred + 1) → VertexIndex
  nonzeroWitness : Fin (edgePred + 1) → VertexIndex

def Box.edgeShell (box : Box) : CayleyEdgeCertificate.Box where
  interval := box.interval
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

structure Box.Valid (box : Box) : Prop where
  triangle_valid : TriangleValid box.triangle
  direction_nonzero : ∀ i,
    max3 (fun j => box.supportAt j i (box.nonzeroWitness i)) +
      supportError < 0
  displacement :
    box.edgeShell.dBound * box.totalDefect +
      box.edgeShell.displacementError ≤ box.displacementLower

theorem Box.valid_iff (box : Box) : box.Valid ↔
    TriangleValid box.triangle ∧
    (∀ i, max3 (fun j => box.supportAt j i (box.nonzeroWitness i)) +
      supportError < 0) ∧
    box.edgeShell.dBound * box.totalDefect +
      box.edgeShell.displacementError ≤ box.displacementLower := by
  constructor
  · rintro ⟨htriangle, hnonzero, hdisplacement⟩
    exact ⟨htriangle, hnonzero, hdisplacement⟩
  · rintro ⟨htriangle, hnonzero, hdisplacement⟩
    exact ⟨htriangle, hnonzero, hdisplacement⟩

instance (box : Box) : Decidable box.Valid :=
  decidable_of_iff _ (box.valid_iff).symm

noncomputable def Box.projectiveApproxSupport (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) : ℝ :=
  linearValue (normalizedView p)
    (cross3 (box.edgeShell.approxEdge i) (box.edgeShell.approxDelta i k))

noncomputable def Box.projectiveApproxDisplacement (box : Box)
    (p : CayleyPose ℝ) : ℝ :=
  linearValue (normalizedView p) (box.edgeShell.approxTotalVector p)

theorem Box.approxSupport_eq_viewSum_mul (box : Box)
    (p : CayleyPose ℝ) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) (hsum : viewSum p ≠ 0) :
    box.edgeShell.approxSupportValue p i k =
      viewSum p * box.projectiveApproxSupport p i k := by
  simp [Box.projectiveApproxSupport, ProjectiveView.linearValue,
    ProjectiveView.normalizedView, CayleyEdgeCertificate.Box.approxSupportValue,
    PiLp.inner_apply, Fin.sum_univ_three]
  field_simp [hsum]

theorem Box.approxDisplacement_eq_viewSum_mul (box : Box)
    (p : CayleyPose ℝ) (hsum : viewSum p ≠ 0) :
    box.edgeShell.approxClearedDisplacement p =
      viewSum p * box.projectiveApproxDisplacement p := by
  simp [Box.projectiveApproxDisplacement, ProjectiveView.linearValue,
    ProjectiveView.normalizedView,
    CayleyEdgeCertificate.Box.approxClearedDisplacement,
    PiLp.inner_apply, Fin.sum_univ_three]
  field_simp [hsum]

theorem Box.supportAt_cast (box : Box) (j : Fin 3)
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    (box.supportAt j i k : ℝ) =
      linearValue (toReal box.triangle j)
        (cross3 (box.edgeShell.approxEdge i)
          (box.edgeShell.approxDelta i k)) := by
  simp [Box.supportAt, dotQ, ProjectiveView.linearValue,
    ProjectiveView.toReal, CayleyEdgeCertificate.Box.approxEdge,
    CayleyEdgeCertificate.Box.approxDelta, toR3, crossQ, cross3,
    cross_apply]

theorem Box.projectiveApproxSupport_le (box : Box) {p : CayleyPose ℝ}
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    box.projectiveApproxSupport p i k ≤
      (max3 (fun j => box.supportAt j i k) : ℝ) := by
  unfold Box.projectiveApproxSupport
  apply linearValue_le_of_mem hmem
  intro j
  rw [← box.supportAt_cast j i k]
  exact_mod_cast le_max3 (fun j => box.supportAt j i k) j

theorem Box.displacementAt_holds (box : Box) {p : CayleyPose ℝ}
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
  have hdot := dotConstBalls_holds
    (a := box.triangle j) hcomponents
  simpa [Box.displacementAt, ProjectiveView.linearValue,
    ProjectiveView.toReal, Fin.sum_univ_three, mul_comm] using hdot

theorem Box.displacementLower_le_projectiveApprox (box : Box)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p)) :
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
    CayleyEdgeCertificate.Box.deltaQ, crossQ, dotQ, max3,
    supportError, RationalApprox.κℚ]

theorem Box.defect_nonneg (box : Box) (i : Fin (box.edgePred + 1)) :
    0 ≤ box.defect i :=
  (box.supportUpper_self_nonneg i).trans
    (box.supportUpper_le_defect i (box.outerIndex i))

theorem Box.totalDefect_nonneg (box : Box) : 0 ≤ box.totalDefect :=
  Finset.sum_nonneg fun i _ => box.defect_nonneg i

theorem Box.exactSupport_le_scaledUpper (box : Box)
    {p : CayleyPose ℝ} {offset : ℝ²}
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    box.edgeShell.exactSupportValue p i k ≤
      viewSum p * (box.supportUpper i k : ℝ) := by
  have hsumPos := viewSum_pos hchamber
  have hsumOne := one_le_viewSum hchamber
  have hprojective := box.projectiveApproxSupport_le hmem i k
  have happroxEq := box.approxSupport_eq_viewSum_mul p i k hsumPos.ne'
  have happrox : box.edgeShell.approxSupportValue p i k ≤
      viewSum p * (max3 (fun j => box.supportAt j i k) : ℝ) := by
    rw [happroxEq]
    exact mul_le_mul_of_nonneg_left hprojective hsumPos.le
  have herr := box.edgeShell.supportValue_error p i k
  rw [abs_le] at herr
  have herrorNonneg : (0 : ℝ) ≤ (supportError : ℝ) := by
    norm_num [supportError, RationalApprox.κℚ]
  have herrorScaled : (supportError : ℝ) ≤
      viewSum p * (supportError : ℝ) := by
    have := mul_le_mul_of_nonneg_right hsumOne herrorNonneg
    simpa using this
  calc
    box.edgeShell.exactSupportValue p i k ≤
        box.edgeShell.approxSupportValue p i k +
          (supportError : ℝ) := by linarith [herr.2]
    _ ≤ viewSum p * (max3 (fun j => box.supportAt j i k) : ℝ) +
        viewSum p * (supportError : ℝ) :=
      add_le_add happrox herrorScaled
    _ = viewSum p * (box.supportUpper i k : ℝ) := by
      unfold Box.supportUpper
      push_cast
      ring

theorem Box.valid_direction_nonzero (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (offset : ℝ²)
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (i : Fin (box.edgePred + 1)) :
    cycleDirection (p.matrixPoseWithOffset offset)
      normalizedExactPolyhedron box.outerIndex i ≠ 0 := by
  have hupper := box.exactSupport_le_scaledUpper hchamber hmem i
    (box.nonzeroWitness i)
  have hchecked := h.direction_nonzero i
  have hupperNeg : (box.supportUpper i (box.nonzeroWitness i) : ℝ) < 0 := by
    change max3 (fun j => box.supportAt j i (box.nonzeroWitness i)) +
      supportError < 0 at hchecked
    exact_mod_cast hchecked
  have hexactNeg : box.edgeShell.exactSupportValue p i
      (box.nonzeroWitness i) < 0 :=
    lt_of_le_of_lt hupper
      (mul_neg_of_pos_of_neg (viewSum_pos hchamber) hupperNeg)
  intro hzero
  have heq := box.edgeShell.exactSupportValue_eq p offset i
    (box.nonzeroWitness i)
  have hzeroShell : cycleDirection (p.matrixPoseWithOffset offset)
      normalizedExactPolyhedron box.edgeShell.outerIndex i = 0 := by
    simpa [Box.edgeShell] using hzero
  rw [hzeroShell] at heq
  simp at heq
  linarith

theorem Box.valid_support (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (offset : ℝ²)
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p))
    (i : Fin (box.edgePred + 1)) (k : VertexIndex) :
    ⟪cycleDirection (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron box.outerIndex i,
      outerProjectionLinear (p.matrixPoseWithOffset offset)
        (normalizedExactVertex k -
          normalizedExactVertex (box.outerIndex i))⟫ ≤
      viewSum p * (box.defect i : ℝ) := by
  change ⟪cycleDirection (p.matrixPoseWithOffset offset)
      normalizedExactPolyhedron box.edgeShell.outerIndex i,
    outerProjectionLinear (p.matrixPoseWithOffset offset)
      (normalizedExactVertex k -
        normalizedExactVertex (box.edgeShell.outerIndex i))⟫ ≤ _
  rw [← box.edgeShell.exactSupportValue_eq p offset i k]
  exact (box.exactSupport_le_scaledUpper hchamber hmem i k).trans
    (mul_le_mul_of_nonneg_left
      (by exact_mod_cast box.supportUpper_le_defect i k)
      (viewSum_pos hchamber).le)

theorem Box.valid_exactClearedDisplacement (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p)) :
    viewSum p * (box.edgeShell.dBound : ℝ) *
        (box.totalDefect : ℝ) ≤
      box.edgeShell.exactClearedDisplacement p := by
  have hsumPos := viewSum_pos hchamber
  have hsumOne := one_le_viewSum hchamber
  have hprojective := box.displacementLower_le_projectiveApprox hp hmem
  have happroxEq := box.approxDisplacement_eq_viewSum_mul p hsumPos.ne'
  have happroxLower : viewSum p * (box.displacementLower : ℝ) ≤
      box.edgeShell.approxClearedDisplacement p := by
    calc
      _ ≤ viewSum p * box.projectiveApproxDisplacement p :=
        mul_le_mul_of_nonneg_left hprojective hsumPos.le
      _ = box.edgeShell.approxClearedDisplacement p := happroxEq.symm
  have hchecked : (box.edgeShell.dBound : ℝ) *
        (box.totalDefect : ℝ) +
        (box.edgeShell.displacementError : ℝ) ≤
      (box.displacementLower : ℝ) := by
    exact_mod_cast h.displacement
  have hscaledChecked :=
    mul_le_mul_of_nonneg_left hchecked hsumPos.le
  have hcharged : viewSum p *
        ((box.edgeShell.dBound : ℝ) * (box.totalDefect : ℝ) +
          (box.edgeShell.displacementError : ℝ)) ≤
      box.edgeShell.approxClearedDisplacement p :=
    hscaledChecked.trans happroxLower
  have herr := box.edgeShell.clearedDisplacement_error hp
  rw [abs_le] at herr
  have herrorNonneg : (0 : ℝ) ≤
      (box.edgeShell.displacementError : ℝ) := by
    have hq : (0 : ℚ) ≤ box.edgeShell.displacementError := by
      have hd : (0 : ℚ) ≤ box.edgeShell.dBound := by
        unfold CayleyEdgeCertificate.Box.dBound
        positivity
      unfold CayleyEdgeCertificate.Box.displacementError
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) (by norm_num)) hd)
        (by norm_num [RationalApprox.κℚ])
    exact_mod_cast hq
  have herrorScaled : (box.edgeShell.displacementError : ℝ) ≤
      viewSum p * (box.edgeShell.displacementError : ℝ) := by
    have := mul_le_mul_of_nonneg_right hsumOne herrorNonneg
    simpa using this
  nlinarith [herr.1]

theorem Box.valid_actualDisplacement (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p)) :
    viewSum p * (box.totalDefect : ℝ) ≤
      box.edgeShell.actualDisplacement p := by
  have hcleared := box.valid_exactClearedDisplacement h hp offset
    hchamber hmem
  have hfactorNonneg : 0 ≤ viewSum p * (box.totalDefect : ℝ) :=
    mul_nonneg (viewSum_pos hchamber).le
      (by exact_mod_cast box.totalDefect_nonneg)
  have hdenomCharge : cayleyDenom p.x p.y p.z *
        (viewSum p * (box.totalDefect : ℝ)) ≤
      (box.edgeShell.dBound : ℝ) *
        (viewSum p * (box.totalDefect : ℝ)) :=
    mul_le_mul_of_nonneg_right (box.edgeShell.denom_le_dBound hp)
      hfactorNonneg
  have htarget : cayleyDenom p.x p.y p.z *
        (viewSum p * (box.totalDefect : ℝ)) ≤
      box.edgeShell.exactClearedDisplacement p := by
    apply hdenomCharge.trans
    nlinarith
  rw [box.edgeShell.exactClearedDisplacement_eq_denom_mul] at htarget
  exact le_of_mul_le_mul_left htarget (cayleyDenom_pos p.x p.y p.z)

theorem Box.valid_imp_not_translated_rupert (box : Box) (h : box.Valid)
    (p : CayleyPose ℝ) (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (hchamber : (p.matrixPoseWithOffset offset).InOuterViewChamber)
    (hmem : InTriangle (toReal box.triangle) (normalizedView p)) :
    ¬ RupertPose (p.matrixPoseWithOffset offset)
      normalizedExactPolyhedron.hull := by
  apply not_rupertPose_of_cycle_support_with_defect
    normalizedExactPolyhedron (p.matrixPoseWithOffset offset)
    box.innerIndex box.outerIndex
    (fun i => viewSum p * (box.defect i : ℝ))
  · exact box.valid_direction_nonzero h offset hchamber hmem
  · intro i k
    simpa [normalizedExactPolyhedron] using
      box.valid_support h offset hchamber hmem i k
  · have hactual := box.valid_actualDisplacement h hp offset hchamber hmem
    rw [box.edgeShell.actualDisplacement_eq_sum p offset] at hactual
    simp only [Box.totalDefect, Box.edgeShell] at hactual
    push_cast at hactual
    rw [Finset.mul_sum] at hactual
    simp [normalizedExactPolyhedron] at hactual ⊢
    convert hactual using 1 <;> rfl

end Noperthedron.SnubCube.ProjectiveEdgeCertificate

end
