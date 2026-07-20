module

public import Noperthedron.SnubCube.ProjectiveTransitionBox
public import Noperthedron.SnubCube.ProjectiveLocalRigidity

@[expose] public section


/-!
# Geometric semantics of projective transition boxes

The transition checker works with exact sparse polynomials in the blown-up
chart.  This file identifies those polynomials with the moving support
directions, determinant weights, and Cayley displacement appearing in the
balanced-support theorem.
-/

namespace Noperthedron.SnubCube.ProjectiveTransitionGeometry

open scoped RealInnerProductSpace
open Noperthedron.BalancedSupport
open ProjectiveView ProjectiveLocalRigidity
open ProjectiveTransitionBlowup
open ProjectiveTransitionCertificate
open SparseTribonacciPolynomial
open ProjectiveTransitionBox

abbrev vi (index : Fin 24) : VertexIndex := VertexIndex.ofFin24 index

noncomputable def realEdge (family : Family) (i : Fin 3) : ℝ³ :=
  normalizedExactVertex (vi (family.edgeStart i)) -
    normalizedExactVertex (vi (family.edgeFinish i))

noncomputable def realSupport (family : Family) (i : Fin 3) : ℝ³ :=
  normalizedExactVertex (vi (family.supportVertex i))

noncomputable def realOuterSupport (family : Family) (i : Fin 3) : ℝ³ :=
  normalizedExactVertex (vi (family.outerVertex i))

noncomputable def realOfExact
    (q : ProjectiveTransitionBlowup.ExactVector) : ℝ³ :=
  WithLp.toLp 2 fun c => (q c).eval

@[simp] theorem realOfExact_apply
    (q : ProjectiveTransitionBlowup.ExactVector) (c : Fin 3) :
    realOfExact q c = (q c).eval := rfl

theorem eval_exactSelectedVertex (index : Fin 24) (c : Fin 3) :
    (exactSelectedVertex index c).eval =
      normalizedExactVertex (vi index) c := by
  exact eval_normalizedSymbolicVertex (vi index) c

theorem eval_exactEdge (start finish : Fin 24) (c : Fin 3) :
    (exactEdge start finish c).eval =
      (normalizedExactVertex (vi start) -
        normalizedExactVertex (vi finish)) c := by
  simp [exactEdge, ProjectiveTransitionCertificate.vi,
    symbolicVertexDifference, eval_normalizedSymbolicVertex, vi]

theorem eval_family_edge (family : Family) (i : Fin 3) (c : Fin 3) :
    (family.edge i c).eval = realEdge family i c := by
  exact eval_exactEdge _ _ c

theorem eval_family_support (family : Family) (i : Fin 3) (c : Fin 3) :
    (family.support i c).eval = realSupport family i c := by
  exact eval_exactSelectedVertex _ c

theorem eval_family_outerSupport (family : Family) (i : Fin 3) (c : Fin 3) :
    (family.outerSupport i c).eval = realOuterSupport family i c := by
  exact eval_exactSelectedVertex _ c

theorem realOfExact_family_support (family : Family) (i : Fin 3) :
    realOfExact (family.support i) = realSupport family i := by
  ext c
  exact eval_family_support family i c

theorem realOfExact_family_outerSupport (family : Family) (i : Fin 3) :
    realOfExact (family.outerSupport i) = realOuterSupport family i := by
  ext c
  exact eval_family_outerSupport family i c

/-- The exact chart view is the normalized projective view of the pose. -/
def ChartView (values : Fin 5 → ℝ) (p : CayleyPose ℝ) : Prop :=
  ∀ c, evalReal values (viewPolynomial c) = normalizedView p c

/-- The exact chart Cayley vector is the pose's relative rotation vector. -/
def ChartCayley (values : Fin 5 → ℝ) (p : CayleyPose ℝ) : Prop :=
  ∀ c, evalReal values (cayleyPolynomial c) = ![p.x, p.y, p.z] c

theorem eval_cayleyDenominator {values : Fin 5 → ℝ} {p : CayleyPose ℝ}
    (hcayley : ChartCayley values p) :
    evalReal values cayleyDenominator = cayleyDenom p.x p.y p.z := by
  unfold ChartCayley at hcayley
  simp only [cayleyDenominator, evalReal_add_op, evalReal_mul_op,
    evalReal_one]
  rw [hcayley 0, hcayley 1, hcayley 2]
  simp [cayleyDenom]
  ring

theorem eval_family_weight {values : Fin 5 → ℝ} {p : CayleyPose ℝ}
    (hview : ChartView values p) (family : Family) (i : Fin 3) :
    evalReal values (family.weightPolynomial i) =
      weight p (realEdge family) i := by
  unfold ChartView at hview
  fin_cases i <;>
    simp [Family.weightPolynomial, ProjectiveTransitionBlowup.dotPolyExact,
      weight, linearValue, cross3, cross_apply,
      hview, eval_symbolicCross, eval_family_edge]

theorem eval_family_supportPolynomial
    {values : Fin 5 → ℝ} {p : CayleyPose ℝ}
    (hview : ChartView values p) (family : Family)
    (i : Fin 3) (vertex : Fin 24) :
    evalReal values (family.supportPolynomial i vertex) =
      linearValue (normalizedView p)
        (cross3 (realEdge family i)
          (normalizedExactVertex (vi vertex) - realOuterSupport family i)) := by
  unfold ChartView at hview
  simp [Family.supportPolynomial, ProjectiveTransitionBlowup.dotPolyExact,
    linearValue,
    symbolicCross, cross3, cross_apply, hview, eval_family_edge,
    eval_exactSelectedVertex, eval_family_outerSupport]

theorem eval_family_defectPolynomial
    {values : Fin 5 → ℝ} {p : CayleyPose ℝ}
    (hview : ChartView values p) (family : Family) (i : Fin 3) :
    evalReal values (family.defectPolynomial i) =
      linearValue (normalizedView p)
        (cross3 (realEdge family i)
          (normalizedExactVertex (vi (family.supportCompetitor i)) -
            realOuterSupport family i)) := by
  exact eval_family_supportPolynomial hview family i _

theorem eval_selfDisplacementPolynomial
    {values : Fin 5 → ℝ} {p : CayleyPose ℝ}
    (hcayley : ChartCayley values p)
    (q : ProjectiveTransitionBlowup.ExactVector) (c : Fin 3) :
    evalReal values (selfDisplacementPolynomial q c) =
      ((cayleyNumeratorMatrix p.x p.y p.z).toEuclideanLin
          (realOfExact q) -
        cayleyDenom p.x p.y p.z • realOfExact q) c := by
  unfold ChartCayley at hcayley
  fin_cases c <;>
    simp [selfDisplacementPolynomial, Matrix.toLpLin_apply,
      dotProduct, Fin.sum_univ_three,
      cayleyNumeratorMatrix, cayleyDenom, hcayley] <;>
    ring

theorem eval_family_displacementPolynomial
    {values : Fin 5 → ℝ} {p : CayleyPose ℝ}
    (hcayley : ChartCayley values p) (family : Family)
    (i : Fin 3) (c : Fin 3) :
    evalReal values (family.displacementPolynomial i c) =
      ((cayleyNumeratorMatrix p.x p.y p.z).toEuclideanLin
          (realSupport family i) -
        cayleyDenom p.x p.y p.z • realOuterSupport family i) c := by
  rw [Family.displacementPolynomial, evalReal_add_op,
    eval_selfDisplacementPolynomial hcayley,
    evalReal_mul_op, eval_cayleyDenominator hcayley,
    evalReal_const]
  rw [realOfExact_family_support]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [TribonacciExpr.eval_sub, eval_family_support,
    eval_family_outerSupport]
  ring

theorem eval_family_displacementPolynomial_eq_denom_mul
    {values : Fin 5 → ℝ} {p : CayleyPose ℝ}
    (hcayley : ChartCayley values p) (family : Family)
    (i : Fin 3) (c : Fin 3) :
    evalReal values (family.displacementPolynomial i c) =
      cayleyDenom p.x p.y p.z *
        ((cayleyMatrix p.x p.y p.z).toEuclideanLin
          (realSupport family i) - realOuterSupport family i) c := by
  rw [eval_family_displacementPolynomial hcayley]
  fin_cases c <;>
    simp [cayleyNumeratorMatrix, cayleyMatrix, cayleyDenom,
      Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three] <;>
    field_simp

theorem eval_family_contactPolynomial_eq_denom_mul
    {values : Fin 5 → ℝ} {p : CayleyPose ℝ}
    (hview : ChartView values p) (hcayley : ChartCayley values p)
    (family : Family) (i : Fin 3) :
    evalReal values (family.contactPolynomial i) =
      cayleyDenom p.x p.y p.z *
        linearValue (normalizedView p)
          (cross3 (realEdge family i)
            ((cayleyMatrix p.x p.y p.z).toEuclideanLin
              (realSupport family i) - realOuterSupport family i)) := by
  unfold ChartView at hview
  simp [Family.contactPolynomial, ProjectiveTransitionBlowup.dotPoly,
    ProjectiveTransitionBlowup.crossExactPoly, linearValue,
    cross3, cross_apply, hview, eval_family_edge,
    eval_family_displacementPolynomial_eq_denom_mul hcayley]
  ring

theorem projected_displacement_eq
    (p : CayleyPose ℝ) (offset : ℝ²) (inner outer : ℝ³) :
    proj_xyL ((p.matrixPoseWithOffset offset).innerRot.val.toEuclideanLin
        inner) -
      proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin
        outer) =
      outerProjectionLinear (p.matrixPoseWithOffset offset)
        ((cayleyMatrix p.x p.y p.z).toEuclideanLin inner - outer) := by
  rw [CayleyPose.matrixPoseWithOffset_inner_rotation_project,
    CayleyPose.matrixPoseWithOffset_outer_rotation_project]
  have houter : outerProjectionLinear (p.matrixPoseWithOffset offset)
      ((cayleyMatrix p.x p.y p.z).toEuclideanLin inner - outer) =
      rotM p.θ p.φ
        ((cayleyMatrix p.x p.y p.z).toEuclideanLin inner - outer) := by
    simpa [outerProjectionLinear, ContinuousLinearMap.comp_apply] using
      p.matrixPoseWithOffset_outer_rotation_project offset
        ((cayleyMatrix p.x p.y p.z).toEuclideanLin inner - outer)
  rw [houter, map_sub]

theorem eval_family_contactPolynomial
    {values : Fin 5 → ℝ} {p : CayleyPose ℝ}
    (hview : ChartView values p) (hcayley : ChartCayley values p)
    (offset : ℝ²) (hsum : viewSum p ≠ 0)
    (family : Family) (i : Fin 3) :
    evalReal values (family.contactPolynomial i) =
      cayleyDenom p.x p.y p.z *
        ⟪direction p (realEdge family i),
          proj_xyL ((p.matrixPoseWithOffset offset).innerRot.val.toEuclideanLin
            (realSupport family i)) -
          proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin
            (realOuterSupport family i))⟫ := by
  rw [eval_family_contactPolynomial_eq_denom_mul hview hcayley]
  rw [projected_displacement_eq]
  rw [inner_direction_outerProjection_eq_support p offset _ _ hsum]

noncomputable def actualContact (p : CayleyPose ℝ) (offset : ℝ²)
    (family : Family) (i : Fin 3) : ℝ :=
  ⟪direction p (realEdge family i),
    proj_xyL ((p.matrixPoseWithOffset offset).innerRot.val.toEuclideanLin
      (realSupport family i)) -
    proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin
      (realOuterSupport family i))⟫

noncomputable def actualDefect (values : Fin 5 → ℝ)
    (family : Family) (i : Fin 3) : ℝ :=
  evalReal values (family.defectPolynomial i)

theorem eval_family_supportPolynomial_eq_inner
    {values : Fin 5 → ℝ} {p : CayleyPose ℝ}
    (hview : ChartView values p) (offset : ℝ²)
    (hsum : viewSum p ≠ 0) (family : Family)
    (i : Fin 3) (vertex : Fin 24) :
    evalReal values (family.supportPolynomial i vertex) =
      ⟪direction p (realEdge family i),
        proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin
          (normalizedExactVertex (vi vertex))) -
        proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin
          (realOuterSupport family i))⟫ := by
  rw [eval_family_supportPolynomial hview]
  rw [← inner_direction_outerProjection_eq_support p offset _ _ hsum]
  congr 2
  simp [outerProjectionLinear, ContinuousLinearMap.comp_apply, map_sub]

/-- The exact obstruction polynomial is the positive Cayley denominator
times the physical weighted displacement after charging support defects. -/
theorem eval_family_obstruction
    {values : Fin 5 → ℝ} {p : CayleyPose ℝ}
    (hview : ChartView values p) (hcayley : ChartCayley values p)
    (offset : ℝ²) (hsum : viewSum p ≠ 0) (family : Family) :
    evalReal values family.obstruction =
      cayleyDenom p.x p.y p.z *
        (∑ i, weight p (realEdge family) i *
          (actualContact p offset family i - actualDefect values family i)) := by
  simp only [Family.obstruction, evalReal_add_op, evalReal_mul_op,
    evalReal_sub_op]
  rw [eval_family_weight hview family 0,
    eval_family_weight hview family 1,
    eval_family_weight hview family 2,
    eval_family_contactPolynomial hview hcayley offset hsum family 0,
    eval_family_contactPolynomial hview hcayley offset hsum family 1,
    eval_family_contactPolynomial hview hcayley offset hsum family 2,
    eval_cayleyDenominator hcayley]
  simp only [actualContact, actualDefect, Fin.sum_univ_three]
  ring

theorem ofFin24_toFin24 (index : VertexIndex) :
    VertexIndex.ofFin24 index.toFin24 = index := by
  obtain ⟨permutation, signs⟩ := index
  fin_cases permutation <;> fin_cases signs <;> decide

theorem direction_nonzero_of_weights_positive
    (p : CayleyPose ℝ) (edge : EdgeTriple) (hsum : viewSum p ≠ 0)
    (hweight : ∀ i, 0 < weight p edge i) (i : Fin 3) :
    direction p (edge i) ≠ 0 := by
  intro hzero
  fin_cases i
  · change direction p (edge 0) = 0 at hzero
    have hpositive := hweight 1
    rw [weight_eq_viewSum_mul_determinantWeights p edge hsum 1] at hpositive
    simp [determinantWeights, hzero, det2] at hpositive
  · change direction p (edge 1) = 0 at hzero
    have hpositive := hweight 2
    rw [weight_eq_viewSum_mul_determinantWeights p edge hsum 2] at hpositive
    simp [determinantWeights, hzero, det2] at hpositive
  · change direction p (edge 2) = 0 at hzero
    have hpositive := hweight 0
    rw [weight_eq_viewSum_mul_determinantWeights p edge hsum 0] at hpositive
    simp [determinantWeights, hzero, det2] at hpositive

theorem direction_nonzero_of_other_weight_positive
    (p : CayleyPose ℝ) (edge : EdgeTriple) (hsum : viewSum p ≠ 0)
    (i j : Fin 3) (hji : j ≠ i) (hpositive : 0 < weight p edge j) :
    direction p (edge i) ≠ 0 := by
  intro hzero
  rw [weight_eq_viewSum_mul_determinantWeights p edge hsum j] at hpositive
  fin_cases i <;> fin_cases j <;>
    simp_all [determinantWeights, det2]

/-- A checked transition leaf rules out every planar translation of every
pose represented by its exact blown-up chart box. -/
theorem Box.valid_imp_not_translated_rupert
    (box : Box) (hvalid : box.Valid)
    {values : Fin 5 → ℝ}
    (hvalues : ∀ i, (box.variableBalls i).Holds (values i))
    (p : CayleyPose ℝ) (offset : ℝ²)
    (hview : ChartView values p) (hcayley : ChartCayley values p)
    (hsum : viewSum p ≠ 0) :
    ¬ RupertPose (p.matrixPoseWithOffset offset)
      normalizedExactPolyhedron.hull := by
  let family := box.family
  let edge : EdgeTriple := realEdge family
  let μ : Fin 3 → ℝ := weight p edge
  let u : Fin 3 → ℝ² := fun i => direction p (edge i)
  let defect : Fin 3 → ℝ := actualDefect values family
  have hμnonneg : ∀ i, 0 ≤ μ i := by
    intro i
    change 0 ≤ weight p (realEdge box.family) i
    rw [← eval_family_weight hview]
    exact box.weight_nonnegative hvalid hvalues i
  have hμwitness : ∀ i, ∃ j, j ≠ i ∧ 0 < μ j := by
    intro i
    obtain ⟨j, hji, hj⟩ := box.direction_weight_witness hvalid hvalues i
    refine ⟨j, hji, ?_⟩
    change 0 < weight p (realEdge box.family) j
    rw [← eval_family_weight hview]
    exact hj
  apply Noperthedron.BalancedSupport.not_rupertPose_of_balanced_support_with_defect
    normalizedExactPolyhedron (p.matrixPoseWithOffset offset)
    (fun i => vi (family.supportVertex i))
    (fun i => vi (family.outerVertex i)) μ u defect
  · intro i
    obtain ⟨j, hji, hj⟩ := hμwitness i
    exact direction_nonzero_of_other_weight_positive p edge hsum i j hji hj
  · intro i
    exact hμnonneg i
  · obtain ⟨j, _, hj⟩ := hμwitness 0
    exact ⟨j, hj⟩
  · exact weight_balance p edge hsum
  · intro i y hy
    obtain ⟨v, ⟨j, rfl⟩, rfl⟩ := hy
    let vertex : Fin 24 := j.toFin24
    have hsupport := box.support_le_defect hvalid hvalues i vertex
    rw [eval_family_supportPolynomial_eq_inner hview offset hsum] at hsupport
    have hj : vi vertex = j := ofFin24_toFin24 j
    rw [hj] at hsupport
    change
      ⟪u i,
        proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin
          (normalizedExactVertex j))⟫ ≤
      ⟪u i,
        proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin
          (normalizedExactVertex (vi (family.outerVertex i))))⟫ + defect i
    change
      ⟪direction p (realEdge family i),
        proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin
          (normalizedExactVertex j))⟫ ≤ _
    rw [inner_sub_right] at hsupport
    simpa [family, u, defect, actualDefect, realOuterSupport, add_comm] using
      (sub_le_iff_le_add.mp hsupport)
  · have hobstruction := box.obstruction_nonnegative hvalid hvalues
    rw [eval_family_obstruction hview hcayley offset hsum] at hobstruction
    have hphysical :
        0 ≤ ∑ i, μ i * (actualContact p offset family i - defect i) :=
      nonneg_of_mul_nonneg_right hobstruction
        (cayleyDenom_pos p.x p.y p.z)
    have hseparate :
        (∑ i, μ i * (actualContact p offset family i - defect i)) =
          (∑ i, μ i * actualContact p offset family i) -
            ∑ i, μ i * defect i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hseparate] at hphysical
    change ∑ i, μ i * defect i ≤
      ∑ i, μ i *
        ⟪u i,
          proj_xyL ((p.matrixPoseWithOffset offset).innerRot.val.toEuclideanLin
            (normalizedExactVertex (vi (family.supportVertex i)))) -
          proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin
            (normalizedExactVertex (vi (family.outerVertex i))))⟫
    simpa [actualContact, u, edge, realSupport, realOuterSupport] using
      (sub_nonneg.mp hphysical)

end Noperthedron.SnubCube.ProjectiveTransitionGeometry

end
