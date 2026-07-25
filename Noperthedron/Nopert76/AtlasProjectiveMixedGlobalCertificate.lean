module

public import Noperthedron.Nopert76.AtlasProjectiveGlobalCertificate

@[expose] public section

/-!
# Convex mixtures of projective global certificates

A single balanced-support axis can have a negative uniform bound even when a
small collection of axes covers the entire parameter box.  This checker takes
a convex combination of four ordinary global-certificate polynomials.  A
positive lower bound for the mixture implies that at least one component is a
valid pointwise obstruction.
-/

namespace Noperthedron.Nopert76.AtlasProjectiveMixedGlobalCertificate

open Noperthedron.Checker Noperthedron.BalancedSupport
open CayleyAtlas AtlasProjectiveView
open AtlasProjectiveGlobalCertificate
open AtlasProjectiveLocalCertificate
open Noperthedron.SnubCube.ProjectiveView

structure Component where
  certificate : AxisCertificate
  innerIndex : Fin 3 → VertexIndex
  ballMultiplier : ℚ
deriving DecidableEq

structure Box where
  interval : AtlasInterval ℚ
  root : Fin 8
  triangle : AtlasProjectiveView.Triangle ℚ
  chart : CayleyAtlas.ChartIndex
  component : Fin 4 → Component
  weight : Fin 4 → ℚ
deriving DecidableEq

def Box.componentBox (box : Box) (k : Fin 4) :
    AtlasProjectiveGlobalCertificate.Box where
  interval := box.interval
  root := box.root
  triangle := box.triangle
  chart := box.chart
  certificate := (box.component k).certificate
  innerIndex := (box.component k).innerIndex
  ballMultiplier := (box.component k).ballMultiplier

def Box.relativeBalls (box : Box) : Fin 3 → RatBall :=
  (box.componentBox 0).relativeBalls

def Box.viewControlQuadratic (box : Box) (i j : Fin 3) : RatQuadratic3 :=
  RatQuadratic3.scale (box.weight 0)
      ((box.componentBox 0).viewControlQuadratic i j) +
    RatQuadratic3.scale (box.weight 1)
      ((box.componentBox 1).viewControlQuadratic i j) +
    RatQuadratic3.scale (box.weight 2)
      ((box.componentBox 2).viewControlQuadratic i j) +
    RatQuadratic3.scale (box.weight 3)
      ((box.componentBox 3).viewControlQuadratic i j)

def Box.bernsteinDisplacementLower (box : Box) : ℚ :=
  QuadraticBernstein.min3 fun i => QuadraticBernstein.min3 fun j =>
    QuadraticBernstein.lower box.relativeBalls
      (box.viewControlQuadratic i j)

def Box.weightedDefectUpper (box : Box) : ℚ :=
  ∑ k, box.weight k * (box.componentBox k).weightedDefectUpper

def Box.dBound (box : Box) : ℚ :=
  (box.componentBox 0).dBound

def Box.displacementError (box : Box) : ℚ :=
  (box.componentBox 0).displacementError

@[mk_iff]
structure Box.Valid (box : Box) : Prop where
  weight_nonneg : ∀ k, 0 ≤ box.weight k
  weight_sum : ∑ k, box.weight k = 1
  component_admissible : ∀ k, (box.componentBox k).Admissible
  displacement : box.displacementError ≤
    box.bernsteinDisplacementLower - box.dBound * box.weightedDefectUpper

instance (box : Box) : Decidable box.Valid :=
  decidable_of_iff _ (Box.valid_iff box).symm

theorem Box.bernsteinDisplacementLower_le_control (box : Box)
    (i j : Fin 3) :
    box.bernsteinDisplacementLower ≤
      QuadraticBernstein.lower box.relativeBalls
        (box.viewControlQuadratic i j) := by
  exact (QuadraticBernstein.min3_le
    (fun i => QuadraticBernstein.min3 fun j =>
      QuadraticBernstein.lower box.relativeBalls
        (box.viewControlQuadratic i j)) i).trans
    (QuadraticBernstein.min3_le
      (fun j => QuadraticBernstein.lower box.relativeBalls
        (box.viewControlQuadratic i j)) j)

theorem Box.relativeBalls_hold (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    ∀ i, (box.relativeBalls i).Holds (![p.x, p.y, p.z] i) := by
  simpa [Box.relativeBalls, Box.componentBox] using
    (box.componentBox 0).relativeBalls_hold hp

theorem Box.viewControlQuadratic_eval (box : Box) (i j : Fin 3)
    (x y z : ℝ) :
    (box.viewControlQuadratic i j).evalReal x y z =
      ∑ k, (box.weight k : ℝ) *
        ((box.componentBox k).viewControlQuadratic i j).evalReal x y z := by
  simp [Box.viewControlQuadratic, Fin.sum_univ_four,
    RatQuadratic3.evalReal_add, RatQuadratic3.evalReal_scale]

theorem Box.viewControl_sum (box : Box) (viewWeight : Fin 3 → ℝ)
    (hsum : ∑ i, viewWeight i = 1) (x y z : ℝ) :
    (∑ i, ∑ j, viewWeight i * viewWeight j *
        (box.viewControlQuadratic i j).evalReal x y z) =
      ∑ k, (box.weight k : ℝ) *
        ((box.componentBox k).viewDisplacementValue
            (affinePoint (toReal box.triangle) viewWeight) x y z +
          ((box.component k).ballMultiplier : ℝ) *
            (x ^ 2 + y ^ 2 + z ^ 2 - 3)) := by
  simp_rw [box.viewControlQuadratic_eval]
  calc
    _ = ∑ k, (box.weight k : ℝ) *
        (∑ i, ∑ j, viewWeight i * viewWeight j *
          ((box.componentBox k).viewControlQuadratic i j).evalReal x y z) := by
      simp [Fin.sum_univ_three, Fin.sum_univ_four]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [(box.componentBox k).viewControl_sum viewWeight hsum x y z]
      simp [Box.componentBox]

private theorem lower_le_weighted_sum {ι : Type} [Fintype ι]
    (weight value : ι → ℝ) (lower : ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (hlower : ∀ i, lower ≤ value i) :
    lower ≤ ∑ i, weight i * value i := by
  calc
    lower = ∑ i, weight i * lower := by
      rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ i, weight i * value i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hlower i) (hweight i)

private theorem weighted_sum_le_upper {ι : Type} [Fintype ι]
    (weight value : ι → ℝ) (upper : ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (hupper : ∀ i, value i ≤ upper) :
    ∑ i, weight i * value i ≤ upper := by
  calc
    _ ≤ ∑ i, weight i * upper := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hupper i) (hweight i)
    _ = upper := by rw [← Finset.sum_mul, hsum, one_mul]

theorem Box.bernsteinDisplacementLower_le_adjusted (box : Box)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    (box.bernsteinDisplacementLower : ℝ) ≤
      ∑ k, (box.weight k : ℝ) *
        ((box.componentBox k).approxClearedDisplacement p +
          ((box.component k).ballMultiplier : ℝ) *
            (p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - 3)) := by
  obtain ⟨viewWeight, hweight, hsum, hpoint⟩ := hmem
  have hcontrol (i j : Fin 3) :
      (box.bernsteinDisplacementLower : ℝ) ≤
        (box.viewControlQuadratic i j).evalReal p.x p.y p.z := by
    have hmin : (box.bernsteinDisplacementLower : ℝ) ≤
        (QuadraticBernstein.lower box.relativeBalls
          (box.viewControlQuadratic i j) : ℚ) := by
      exact_mod_cast box.bernsteinDisplacementLower_le_control i j
    exact hmin.trans (QuadraticBernstein.lower_le_evalReal
      (box.relativeBalls_hold hp) (box.viewControlQuadratic i j))
  have hweighted :
      (box.bernsteinDisplacementLower : ℝ) ≤
        ∑ i, ∑ j, viewWeight i * viewWeight j *
          (box.viewControlQuadratic i j).evalReal p.x p.y p.z := by
    have houter := lower_le_weighted_sum viewWeight
      (fun i => ∑ j, viewWeight j *
        (box.viewControlQuadratic i j).evalReal p.x p.y p.z)
      (box.bernsteinDisplacementLower : ℝ) hweight hsum (fun i =>
        lower_le_weighted_sum viewWeight
          (fun j => (box.viewControlQuadratic i j).evalReal p.x p.y p.z)
          (box.bernsteinDisplacementLower : ℝ) hweight hsum
          (hcontrol i))
    simpa only [Finset.mul_sum, mul_assoc] using houter
  rw [box.viewControl_sum viewWeight hsum p.x p.y p.z] at hweighted
  rw [← hpoint] at hweighted
  have hreconstructed (k : Fin 4) :
      (box.componentBox k).viewDisplacementValue
          (AtlasProjectiveView.normalizedView box.root p) p.x p.y p.z =
        (box.componentBox k).approxClearedDisplacement p := by
    rw [← (box.componentBox k).reconstructedDisplacement_eq_viewValue]
    simpa [Box.componentBox] using
      (box.componentBox k).reconstructedDisplacement_eq_approx p
  simpa only [hreconstructed] using hweighted

theorem Box.weightedDefectUpper_nonneg (box : Box) (h : box.Valid) :
    0 ≤ box.weightedDefectUpper := by
  unfold Box.weightedDefectUpper
  exact Finset.sum_nonneg fun k _ => mul_nonneg (h.weight_nonneg k)
    (box.componentBox k).weightedDefectUpper_nonneg

theorem Box.valid_exactWeightedDisplacement (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal)
    (hbounded : p.CayleyBounded)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    (box.dBound : ℝ) * (box.weightedDefectUpper : ℝ) ≤
      ∑ k, (box.weight k : ℝ) *
        (box.componentBox k).exactClearedDisplacement p := by
  have hbernstein := box.bernsteinDisplacementLower_le_adjusted hp hmem
  have hconstraint : p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - 3 ≤ 0 := by
    unfold AtlasPose.CayleyBounded at hbounded
    linarith
  have hadjustment (k : Fin 4) :
      ((box.component k).ballMultiplier : ℝ) *
        (p.x ^ 2 + p.y ^ 2 + p.z ^ 2 - 3) ≤ 0 := by
    have hlambda : 0 ≤ ((box.component k).ballMultiplier : ℝ) := by
      exact_mod_cast (h.component_admissible k).ball_multiplier_nonneg
    exact mul_nonpos_of_nonneg_of_nonpos hlambda hconstraint
  have hlower_approx : (box.bernsteinDisplacementLower : ℝ) ≤
      ∑ k, (box.weight k : ℝ) *
        (box.componentBox k).approxClearedDisplacement p :=
    hbernstein.trans (by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _
        (by exact_mod_cast h.weight_nonneg k)
      linarith [hadjustment k])
  have herror (k : Fin 4) :
      (box.componentBox k).approxClearedDisplacement p -
          (box.displacementError : ℝ) ≤
        (box.componentBox k).exactClearedDisplacement p := by
    have herr := (box.componentBox k).clearedDisplacement_error hp hscale
    rw [abs_le] at herr
    have heq : (box.componentBox k).displacementError =
        box.displacementError := by
      rfl
    rw [heq] at herr
    linarith
  have hweightedError :
      ∑ k, (box.weight k : ℝ) *
          ((box.componentBox k).approxClearedDisplacement p -
            (box.displacementError : ℝ)) ≤
        ∑ k, (box.weight k : ℝ) *
          (box.componentBox k).exactClearedDisplacement p := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (herror k)
      (by exact_mod_cast h.weight_nonneg k)
  have hweightSum : ∑ k, (box.weight k : ℝ) = 1 := by
    exact_mod_cast h.weight_sum
  have happrox_exact :
      (∑ k, (box.weight k : ℝ) *
          (box.componentBox k).approxClearedDisplacement p) -
          (box.displacementError : ℝ) ≤
        ∑ k, (box.weight k : ℝ) *
          (box.componentBox k).exactClearedDisplacement p := by
    calc
      _ = ∑ k, (box.weight k : ℝ) *
          ((box.componentBox k).approxClearedDisplacement p -
            (box.displacementError : ℝ)) := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hweightSum, one_mul]
      _ ≤ _ := hweightedError
  have hchecked : (box.displacementError : ℝ) ≤
      (box.bernsteinDisplacementLower : ℝ) -
        (box.dBound : ℝ) * (box.weightedDefectUpper : ℝ) := by
    exact_mod_cast h.displacement
  linarith

theorem Box.valid_actualWeightedDisplacement (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal)
    (hbounded : p.CayleyBounded)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    (box.weightedDefectUpper : ℝ) ≤
      ∑ k, (box.weight k : ℝ) *
        (box.componentBox k).actualClearedDisplacement p := by
  have hexact := box.valid_exactWeightedDisplacement
    h hp hbounded hscale hmem
  have hexactEq :
      (∑ k, (box.weight k : ℝ) *
          (box.componentBox k).exactClearedDisplacement p) =
        cayleyDenom p.x p.y p.z *
          ∑ k, (box.weight k : ℝ) *
            (box.componentBox k).actualClearedDisplacement p := by
    simp_rw [(box.componentBox _).exactClearedDisplacement_eq_denom_mul]
    simp [Fin.sum_univ_four]
    ring
  rw [hexactEq] at hexact
  have hcharge : cayleyDenom p.x p.y p.z *
      (box.weightedDefectUpper : ℝ) ≤
      (box.dBound : ℝ) * (box.weightedDefectUpper : ℝ) :=
    mul_le_mul_of_nonneg_right
      ((box.componentBox 0).denom_le_dBound hp)
      (by exact_mod_cast box.weightedDefectUpper_nonneg h)
  have hmul : cayleyDenom p.x p.y p.z *
      (box.weightedDefectUpper : ℝ) ≤
      cayleyDenom p.x p.y p.z *
        ∑ k, (box.weight k : ℝ) *
          (box.componentBox k).actualClearedDisplacement p :=
    hcharge.trans hexact
  exact le_of_mul_le_mul_left hmul (cayleyDenom_pos p.x p.y p.z)

theorem Box.valid_weightedActualDefect_le (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ}
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    (∑ k, (box.weight k : ℝ) *
      (∑ i, (box.componentBox k).certificate.exactWeight
          (box.componentBox k).localShell p i *
        (box.componentBox k).actualDefect p i)) ≤
      (box.weightedDefectUpper : ℝ) := by
  unfold Box.weightedDefectUpper
  push_cast
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast h.weight_nonneg k)
  have hscale' : 1 ≤ viewScale (box.componentBox k).root p := by
    simpa [Box.componentBox] using hscale
  have hmem' : InTriangle (toReal (box.componentBox k).triangle)
      (AtlasProjectiveView.normalizedView (box.componentBox k).root p) := by
    simpa [Box.componentBox] using hmem
  exact (box.componentBox k).exactWeightedActualDefect_le
    (h.component_admissible k) hscale' hmem'

theorem Box.exists_component_displacement (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal)
    (hbounded : p.CayleyBounded)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal box.triangle)
      (AtlasProjectiveView.normalizedView box.root p)) :
    ∃ k, (∑ i, (box.componentBox k).certificate.exactWeight
          (box.componentBox k).localShell p i *
        (box.componentBox k).actualDefect p i) ≤
      (box.componentBox k).actualClearedDisplacement p := by
  classical
  let actual := fun k : Fin 4 =>
    (box.componentBox k).actualClearedDisplacement p
  let defect := fun k : Fin 4 =>
    ∑ i, (box.componentBox k).certificate.exactWeight
        (box.componentBox k).localShell p i *
      (box.componentBox k).actualDefect p i
  let gap := fun k : Fin 4 => actual k - defect k
  have hdefect := box.valid_weightedActualDefect_le h hscale hmem
  have hdisplacement := box.valid_actualWeightedDisplacement
    h hp hbounded hscale hmem
  have havg : 0 ≤ ∑ k, (box.weight k : ℝ) * gap k := by
    have horder :
        (∑ k, (box.weight k : ℝ) * defect k) ≤
          ∑ k, (box.weight k : ℝ) * actual k :=
      hdefect.trans hdisplacement
    calc
      0 ≤ (∑ k, (box.weight k : ℝ) * actual k) -
          ∑ k, (box.weight k : ℝ) * defect k := sub_nonneg.mpr horder
      _ = ∑ k, (box.weight k : ℝ) * gap k := by
        simp_rw [gap, mul_sub]
        rw [Finset.sum_sub_distrib]
  let upper := max (gap 0) (max (gap 1) (max (gap 2) (gap 3)))
  have hweightReal (k : Fin 4) : 0 ≤ (box.weight k : ℝ) := by
    exact_mod_cast h.weight_nonneg k
  have hweightSum : ∑ k, (box.weight k : ℝ) = 1 := by
    exact_mod_cast h.weight_sum
  have hgapUpper (k : Fin 4) : gap k ≤ upper := by
    fin_cases k <;> simp [upper]
  have havgUpper : (∑ k, (box.weight k : ℝ) * gap k) ≤ upper :=
    weighted_sum_le_upper (fun k => (box.weight k : ℝ)) gap upper
      hweightReal hweightSum hgapUpper
  have hupper : 0 ≤ upper := havg.trans havgUpper
  dsimp [upper] at hupper
  rcases (le_max_iff.mp hupper) with h0 | hrest
  · refine ⟨0, ?_⟩
    exact sub_nonneg.mp h0
  · rcases (le_max_iff.mp hrest) with h1 | hrest
    · refine ⟨1, ?_⟩
      exact sub_nonneg.mp h1
    · rcases (le_max_iff.mp hrest) with h2 | h3
      · refine ⟨2, ?_⟩
        exact sub_nonneg.mp h2
      · refine ⟨3, ?_⟩
        exact sub_nonneg.mp h3

theorem Box.valid_imp_not_translated_rupert (box : Box) (h : box.Valid) :
    ∀ p ∈ box.interval.toReal,
      p.CayleyBounded →
      1 ≤ viewScale box.root p →
      InTriangle (toReal box.triangle)
        (AtlasProjectiveView.normalizedView box.root p) →
      ∀ offset : ℝ²,
        ¬ RupertPose (p.matrixPoseWithOffset box.chart offset)
          exactPolyhedron.hull := by
  intro p hp hbounded hscale hmem offset
  obtain ⟨k, hactual⟩ := box.exists_component_displacement
    h hp hbounded hscale hmem
  let component := box.componentBox k
  have hadmissible : component.Admissible := h.component_admissible k
  have hscale' : 1 ≤ viewScale component.root p := by
    simpa [component, Box.componentBox] using hscale
  have hmem' : InTriangle (toReal component.triangle)
      (AtlasProjectiveView.normalizedView component.root p) := by
    simpa [component, Box.componentBox] using hmem
  have hscaleNe : viewScale component.root p ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hscale').ne'
  rw [component.actualClearedDisplacement_eq_pose offset hscaleNe] at hactual
  apply AtlasProjectiveGlobalRigidity.not_rupertPose_of_projective_global_certificate_with_defect
    component.root p component.chart offset
    (fun i => component.certificate.exactEdge i)
    component.innerIndex component.certificate.index
    (component.actualDefect p) hscaleNe
  · exact component.valid_direction_nonzero hadmissible offset hscale' hmem'
  · intro i
    simpa [AxisCertificate.exactWeight,
      AtlasProjectiveGlobalCertificate.Box.localShell, component] using
      component.valid_weight_nonneg hadmissible hscale' hmem' i
  · obtain ⟨i, hi⟩ := component.valid_weight_pos
      hadmissible hscale' hmem'
    exact ⟨i, by
      simpa [AxisCertificate.exactWeight,
        AtlasProjectiveGlobalCertificate.Box.localShell, component] using hi⟩
  · exact component.valid_support_with_actualDefect
      hadmissible offset hscale' hmem'
  · simpa [AxisCertificate.exactWeight,
      AtlasProjectiveGlobalCertificate.Box.localShell, component] using hactual

theorem Box.valid_imp_no_translated_rupert_in_interval
    (box : Box) (h : box.Valid) :
    ¬ ∃ p ∈ box.interval.toReal,
      p.CayleyBounded ∧
      1 ≤ viewScale box.root p ∧
      InTriangle (toReal box.triangle)
        (AtlasProjectiveView.normalizedView box.root p) ∧
      ∃ offset : ℝ²,
        RupertPose (p.matrixPoseWithOffset box.chart offset)
          exactPolyhedron.hull := by
  rintro ⟨p, hp, hbounded, hscale, hmem, offset, hrupert⟩
  exact box.valid_imp_not_translated_rupert h p hp hbounded hscale hmem
    offset hrupert

end Noperthedron.Nopert76.AtlasProjectiveMixedGlobalCertificate

end
