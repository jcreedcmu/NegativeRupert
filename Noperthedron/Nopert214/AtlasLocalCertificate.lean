module

public import Noperthedron.Nopert214.AtlasQuadratic
public import Noperthedron.Nopert214.LocalCertificate

@[expose] public section

/-!
# Symmetry-local certificates in the bounded Cayley atlas

The outer support geometry is inherited from the established Euler local
certificate on the equality stratum.  Proximity of the relative rotation to
one of the five exact symmetries is checked directly in Cayley coordinates:
each entry of the denominator-cleared mismatch is a rational quadratic.
-/

namespace Noperthedron.Nopert214.AtlasLocalCertificate

open scoped Matrix RealInnerProductSpace
open Noperthedron.Checker
open Noperthedron.Nopert214.CayleyAtlas
open Noperthedron.SnubCube.CayleyEdgeCertificate

structure Box where
  interval : AtlasInterval ℚ
  chart : ChartIndex
  symmetryIndex : OrbitIndex
  certificate : Fin 4 → LocalCertificate.AxisCertificate
  c : ℚ
  r : ℚ
deriving DecidableEq

/-- The equality-stratum Euler pose with the same outer view. -/
def outerPose {R : Type} [Zero R] (p : AtlasPose R) : Pose R where
  θ₁ := p.θ
  θ₂ := p.θ
  φ₁ := p.φ
  φ₂ := p.φ
  α := 0

@[simp] theorem outerPose_toReal (p : AtlasPose ℚ) :
    (outerPose p).toReal = outerPose p.toReal := by
  cases p
  simp [outerPose, Pose.toReal, AtlasPose.toReal]

def Box.outerCenter (box : Box) : Pose ℚ :=
  outerPose
    { θ := box.interval.midpoint 0
      φ := box.interval.midpoint 1
      x := 0, y := 0, z := 0 }

def Box.eulerInterval (box : Box) : PoseInterval ℚ :=
  PoseInterval.mk (outerPose box.interval.min) (outerPose box.interval.max) (by
    rw [Pose.le_iff]
    obtain ⟨hθ, hφ, -, -, -⟩ :=
      (AtlasPose.le_iff _ _).mp box.interval.min_le_max
    exact ⟨hθ, hθ, hφ, hφ, le_rfl⟩)

/-- The mature equality-stratum support and axis-cover checker. -/
def Box.eulerBox (box : Box) : LocalCertificate.Box where
  interval := box.eulerInterval
  center := box.outerCenter
  symmetryIndex := box.symmetryIndex
  certificate := box.certificate
  c := box.c
  r := box.r

/-- Denominator-cleared difference from the rational symmetry
approximation. -/
def Box.mismatchQuadratic (box : Box) (i j : Fin 3) : RatQuadratic3 :=
  AtlasQuadratic.numeratorQuadratic box.chart i j -
    RatQuadratic3.scale (LocalCertificate.symmetryMatrixQ box.symmetryIndex i j)
      denomQuadratic

def Box.variableBalls (box : Box) : Fin 3 → RatBall :=
  ![box.interval.coordinateBall 2,
    box.interval.coordinateBall 3,
    box.interval.coordinateBall 4]

def Box.mismatchBall (box : Box) (i j : Fin 3) : RatBall :=
  RatQuadratic3.evalBall box.variableBalls (box.mismatchQuadratic i j)

def Box.entryAbsUpper (box : Box) (i j : Fin 3) : ℚ :=
  |(box.mismatchBall i j).center| + (box.mismatchBall i j).radius

def Box.mismatchFrobeniusSqUpper (box : Box) : ℚ :=
  ∑ i, ∑ j, box.entryAbsUpper i j ^ 2

def Box.mismatchRadius (box : Box) : ℚ :=
  RationalApprox.sqrtℚUp16 box.mismatchFrobeniusSqUpper +
    LocalCertificate.symmetryError

@[mk_iff]
structure Box.Valid (box : Box) : Prop where
  geometry : box.eulerBox.GeometricValid
  r_nonneg : 0 ≤ box.r
  mismatch_bound : box.mismatchRadius ≤ box.r
  angle_bound : box.r ^ 2 * (1 + box.c ^ 2) ≤ 4 * box.c ^ 2

instance (box : Box) : Decidable box.Valid :=
  decidable_of_iff _ (Box.valid_iff box).symm

theorem Box.outerPose_mem_eulerRealInterval (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    outerPose p ∈ box.eulerBox.realInterval := by
  have hmem := AtlasInterval.mem_toReal_iff.mp hp
  rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff]
  simp only [Box.eulerBox, Box.eulerInterval, PoseInterval.mk,
    PoseInterval.min, PoseInterval.max, LocalCertificate.Box.realInterval,
    outerPose, Pose.toReal_θ₁, Pose.toReal_θ₂,
    Pose.toReal_φ₁, Pose.toReal_φ₂, Pose.toReal_α]
  exact ⟨
    ⟨(hmem 0).1, (hmem 0).1, (hmem 1).1, (hmem 1).1, by norm_num⟩,
    ⟨(hmem 0).2, (hmem 0).2, (hmem 1).2, (hmem 1).2, by norm_num⟩⟩

theorem Box.variableBalls_hold (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    ∀ c, (box.variableBalls c).Holds (![p.x, p.y, p.z] c) := by
  intro c
  fin_cases c
  · exact box.interval.coordinateBall_holds hp 2
  · exact box.interval.coordinateBall_holds hp 3
  · exact box.interval.coordinateBall_holds hp 4

theorem Box.mismatchBall_holds (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) (i j : Fin 3) :
    (box.mismatchBall i j).Holds
      ((box.mismatchQuadratic i j).evalReal p.x p.y p.z) := by
  exact RatQuadratic3.evalBall_holds (box.variableBalls_hold hp)
    (box.mismatchQuadratic i j)

theorem Box.eval_mismatchQuadratic (box : Box) (p : AtlasPose ℝ)
    (i j : Fin 3) :
    (box.mismatchQuadratic i j).evalReal p.x p.y p.z =
      (chartMatrix box.chart * cayleyNumeratorMatrix p.x p.y p.z) i j -
        cayleyDenom p.x p.y p.z *
          (LocalCertificate.symmetryMatrixQ box.symmetryIndex i j : ℝ) := by
  simp only [Box.mismatchQuadratic, RatQuadratic3.evalReal_sub,
    RatQuadratic3.evalReal_scale,
    AtlasQuadratic.eval_numeratorQuadratic,
    Noperthedron.SnubCube.CayleyEdgeCertificate.eval_denomQuadratic]
  push_cast
  ring

private theorem abs_le_center_abs_add_radius {b : RatBall} {x : ℝ}
    (h : b.Holds x) : |x| ≤ (|b.center| + b.radius : ℚ) := by
  calc
    |x| = |(b.center : ℝ) + (x - (b.center : ℝ))| := by ring_nf
    _ ≤ |(b.center : ℝ)| + |x - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ |(b.center : ℝ)| + (b.radius : ℝ) :=
      add_le_add (le_refl _) h
    _ = (|b.center| + b.radius : ℚ) := by push_cast; rfl

theorem Box.eval_mismatch_abs_le (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) (i j : Fin 3) :
    |(box.mismatchQuadratic i j).evalReal p.x p.y p.z| ≤
      (box.entryAbsUpper i j : ℝ) := by
  exact abs_le_center_abs_add_radius (box.mismatchBall_holds hp i j)

theorem Box.eval_mismatch_sum_sq_le (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    (∑ i, ∑ j,
      (box.mismatchQuadratic i j).evalReal p.x p.y p.z ^ 2) ≤
      (box.mismatchFrobeniusSqUpper : ℝ) := by
  rw [show (box.mismatchFrobeniusSqUpper : ℝ) =
      ∑ i, ∑ j, (box.entryAbsUpper i j : ℝ) ^ 2 by
    unfold Box.mismatchFrobeniusSqUpper
    push_cast
    rfl]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h := box.eval_mismatch_abs_le hp i j
  have hu : 0 ≤ (box.entryAbsUpper i j : ℝ) :=
    (abs_nonneg _).trans h
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) hu).2 h

noncomputable def Box.clearedMismatchMatrix (box : Box)
    (p : AtlasPose ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (box.mismatchQuadratic i j).evalReal p.x p.y p.z

noncomputable def Box.clearedMismatchCLM (box : Box)
    (p : AtlasPose ℝ) : ℝ³ →L[ℝ] ℝ³ :=
  (box.clearedMismatchMatrix p).toEuclideanLin.toContinuousLinearMap

private theorem mismatchFrobeniusSqUpper_nonneg (box : Box) :
    0 ≤ box.mismatchFrobeniusSqUpper := by
  unfold Box.mismatchFrobeniusSqUpper
  positivity

theorem Box.clearedMismatchCLM_norm_le (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    ‖box.clearedMismatchCLM p‖ ≤
      (RationalApprox.sqrtℚUp16 box.mismatchFrobeniusSqUpper : ℝ) := by
  apply Noperthedron.BalancedSupport.matrix_opNorm_le_of_sum_sq_le
  · exact_mod_cast RationalApprox.sqrtℚUp16_nonneg
      box.mismatchFrobeniusSqUpper
  · have hsq := RationalApprox.le_mul_self_sqrtℚUp16
      (mismatchFrobeniusSqUpper_nonneg box)
    apply (box.eval_mismatch_sum_sq_le hp).trans
    exact_mod_cast (by simpa [pow_two] using hsq)

noncomputable def Box.approxSymmetryMatrix (box : Box) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (LocalCertificate.symmetryMatrixQ box.symmetryIndex).map fun q => (q : ℝ)

noncomputable def Box.rationalRelativeMismatchMatrix (box : Box)
    (p : AtlasPose ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  chartMatrix box.chart * cayleyMatrix p.x p.y p.z -
    box.approxSymmetryMatrix

noncomputable def Box.rationalRelativeMismatchCLM (box : Box)
    (p : AtlasPose ℝ) : ℝ³ →L[ℝ] ℝ³ :=
  (box.rationalRelativeMismatchMatrix p).toEuclideanLin.toContinuousLinearMap

theorem Box.clearedMismatchMatrix_eq (box : Box) (p : AtlasPose ℝ) :
    box.clearedMismatchMatrix p =
      cayleyDenom p.x p.y p.z • box.rationalRelativeMismatchMatrix p := by
  calc
    box.clearedMismatchMatrix p =
        chartMatrix box.chart * cayleyNumeratorMatrix p.x p.y p.z -
          cayleyDenom p.x p.y p.z • box.approxSymmetryMatrix := by
      ext i j
      rw [Box.clearedMismatchMatrix, box.eval_mismatchQuadratic]
      simp [Box.approxSymmetryMatrix]
    _ = chartMatrix box.chart *
          (cayleyDenom p.x p.y p.z • cayleyMatrix p.x p.y p.z) -
          cayleyDenom p.x p.y p.z • box.approxSymmetryMatrix := by
      rw [cayleyNumeratorMatrix_eq_denom_smul]
    _ = cayleyDenom p.x p.y p.z •
          (chartMatrix box.chart * cayleyMatrix p.x p.y p.z) -
          cayleyDenom p.x p.y p.z • box.approxSymmetryMatrix := by
      rw [Matrix.mul_smul]
    _ = cayleyDenom p.x p.y p.z •
          (chartMatrix box.chart * cayleyMatrix p.x p.y p.z -
            box.approxSymmetryMatrix) := by rw [smul_sub]
    _ = _ := rfl

theorem Box.rationalRelativeMismatchMatrix_eq_inv_smul (box : Box)
    (p : AtlasPose ℝ) :
    box.rationalRelativeMismatchMatrix p =
      (cayleyDenom p.x p.y p.z)⁻¹ • box.clearedMismatchMatrix p := by
  rw [box.clearedMismatchMatrix_eq]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp [cayleyDenom_ne]

theorem Box.rationalRelativeMismatchCLM_eq_inv_smul (box : Box)
    (p : AtlasPose ℝ) :
    box.rationalRelativeMismatchCLM p =
      (cayleyDenom p.x p.y p.z)⁻¹ • box.clearedMismatchCLM p := by
  rw [Box.rationalRelativeMismatchCLM, Box.clearedMismatchCLM,
    box.rationalRelativeMismatchMatrix_eq_inv_smul]
  ext v i
  simp [Matrix.toLpLin_apply]

theorem cayleyDenom_one_le (x y z : ℝ) : 1 ≤ cayleyDenom x y z := by
  unfold cayleyDenom
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]

theorem Box.rationalRelativeMismatchCLM_norm_le (box : Box)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) :
    ‖box.rationalRelativeMismatchCLM p‖ ≤
      (RationalApprox.sqrtℚUp16 box.mismatchFrobeniusSqUpper : ℝ) := by
  rw [box.rationalRelativeMismatchCLM_eq_inv_smul, norm_smul]
  have hd : 1 ≤ cayleyDenom p.x p.y p.z := cayleyDenom_one_le _ _ _
  have hinv : |(cayleyDenom p.x p.y p.z)⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr (cayleyDenom_pos _ _ _))]
    exact (inv_le_one₀ (cayleyDenom_pos _ _ _)).mpr hd
  calc
    |(cayleyDenom p.x p.y p.z)⁻¹| * ‖box.clearedMismatchCLM p‖ ≤
        1 * ‖box.clearedMismatchCLM p‖ :=
      mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
    _ ≤ _ := by simpa using box.clearedMismatchCLM_norm_le hp

noncomputable def Box.relativeCLM (box : Box) (p : AtlasPose ℝ) :
    ℝ³ →L[ℝ] ℝ³ :=
  (chartMatrix box.chart * cayleyMatrix p.x p.y p.z).toEuclideanLin
    |>.toContinuousLinearMap

noncomputable def Box.exactRelativeMismatchCLM (box : Box)
    (p : AtlasPose ℝ) : ℝ³ →L[ℝ] ℝ³ :=
  box.relativeCLM p -
    Noperthedron.SnubCube.so3CLM (symmetry box.symmetryIndex)

theorem Box.rationalRelativeMismatchCLM_eq (box : Box)
    (p : AtlasPose ℝ) :
    box.rationalRelativeMismatchCLM p =
      box.relativeCLM p - LocalCertificate.symmetryQCLM box.symmetryIndex := by
  ext v
  simp only [Box.rationalRelativeMismatchCLM,
    Box.rationalRelativeMismatchMatrix, Box.relativeCLM,
    Box.approxSymmetryMatrix, LocalCertificate.symmetryQCLM,
    ContinuousLinearMap.sub_apply, LinearMap.coe_toContinuousLinearMap',
    Matrix.toEuclideanLin_apply, Matrix.sub_mulVec]
  rfl

theorem Box.exactRelativeMismatchCLM_norm_le (box : Box)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) :
    ‖box.exactRelativeMismatchCLM p‖ ≤ (box.mismatchRadius : ℝ) := by
  have hrat := box.rationalRelativeMismatchCLM_norm_le hp
  have hsym :=
    LocalCertificate.symmetryQCLM_difference_norm_bounded box.symmetryIndex
  have hdecomp : box.exactRelativeMismatchCLM p =
      box.rationalRelativeMismatchCLM p +
        (LocalCertificate.symmetryQCLM box.symmetryIndex -
          Noperthedron.SnubCube.so3CLM (symmetry box.symmetryIndex)) := by
    rw [box.rationalRelativeMismatchCLM_eq]
    unfold Box.exactRelativeMismatchCLM
    abel
  rw [hdecomp]
  calc
    _ ≤ ‖box.rationalRelativeMismatchCLM p‖ +
        ‖LocalCertificate.symmetryQCLM box.symmetryIndex -
          Noperthedron.SnubCube.so3CLM (symmetry box.symmetryIndex)‖ :=
      norm_add_le _ _
    _ ≤ (RationalApprox.sqrtℚUp16 box.mismatchFrobeniusSqUpper : ℝ) +
        (LocalCertificate.symmetryError : ℝ) := by
      apply add_le_add hrat
      simpa only [norm_sub_rev] using hsym
    _ = (box.mismatchRadius : ℝ) := by
      unfold Box.mismatchRadius
      push_cast
      rfl

theorem Box.relativeCLM_eq_so3CLM (box : Box) (p : AtlasPose ℝ) :
    box.relativeCLM p =
      Noperthedron.SnubCube.so3CLM
        (chartSO3 box.chart * cayleySO3 p.x p.y p.z) := by
  ext v
  simp [Box.relativeCLM, Noperthedron.SnubCube.so3CLM,
    chartSO3, cayleySO3, Matrix.mulVec_mulVec]

theorem Box.poseMismatch_eq_outer_comp (box : Box) (p : AtlasPose ℝ)
    (offset : ℝ²) :
    Noperthedron.SnubCube.so3CLM
        (p.matrixPoseWithOffset box.chart offset).innerRot -
      Noperthedron.SnubCube.so3CLM
        ((p.matrixPoseWithOffset box.chart offset).outerRot *
          symmetry box.symmetryIndex) =
      Noperthedron.SnubCube.so3CLM
          (p.matrixPoseWithOffset box.chart offset).outerRot ∘L
        box.exactRelativeMismatchCLM p := by
  let pose := p.matrixPoseWithOffset box.chart offset
  have hinner : pose.innerRot =
      pose.outerRot * (chartSO3 box.chart * cayleySO3 p.x p.y p.z) := by
    change p.outerSO3 * chartSO3 box.chart * cayleySO3 p.x p.y p.z =
      p.outerSO3 * (chartSO3 box.chart * cayleySO3 p.x p.y p.z)
    rw [mul_assoc]
  rw [hinner,
    Noperthedron.SnubCube.so3CLM_mul pose.outerRot
      (chartSO3 box.chart * cayleySO3 p.x p.y p.z),
    Noperthedron.SnubCube.so3CLM_mul pose.outerRot
      (symmetry box.symmetryIndex),
    ← box.relativeCLM_eq_so3CLM]
  unfold Box.exactRelativeMismatchCLM
  ext v
  simp [pose]

theorem Box.valid_mismatch_bound (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²) :
    ‖Noperthedron.SnubCube.so3CLM
        (p.matrixPoseWithOffset box.chart offset).innerRot -
      Noperthedron.SnubCube.so3CLM
        ((p.matrixPoseWithOffset box.chart offset).outerRot *
          symmetry box.symmetryIndex)‖ ≤ (box.r : ℝ) := by
  rw [box.poseMismatch_eq_outer_comp]
  calc
    _ ≤ ‖Noperthedron.SnubCube.so3CLM
          (p.matrixPoseWithOffset box.chart offset).outerRot‖ *
        ‖box.exactRelativeMismatchCLM p‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖box.exactRelativeMismatchCLM p‖ := by
      rw [Noperthedron.SnubCube.so3CLM_norm, one_mul]
    _ ≤ (box.mismatchRadius : ℝ) := box.exactRelativeMismatchCLM_norm_le hp
    _ ≤ (box.r : ℝ) := by exact_mod_cast h.mismatch_bound

theorem Box.valid_axisAngle_ratio (box : Box) (h : box.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ box.interval.toReal) (offset : ℝ²)
    (a : Noperthedron.BalancedSupport.AxisAngle
      (Noperthedron.SnubCube.so3CLM
        (relativeRotationAtSymmetry
          (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex))) :
    1 - Real.cos a.angle ≤ |Real.sin a.angle| * (box.c : ℝ) := by
  apply Noperthedron.Nopert214.AxisAngle.ratio_of_inner_mismatch_bound
    (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex a
    (box.c : ℝ) (box.r : ℝ)
  · exact_mod_cast h.geometry.c_nonneg
  · exact_mod_cast h.r_nonneg
  · exact box.valid_mismatch_bound h hp offset
  · exact_mod_cast h.angle_bound

/-- A valid atlas-local row excludes every translated pose in its full
five-dimensional atlas box, independently of the projective view region. -/
theorem Box.valid_imp_not_translated_rupert (box : Box) (h : box.Valid) :
    ∀ p ∈ box.interval.toReal, ∀ offset : ℝ²,
      ¬ RupertPose (p.matrixPoseWithOffset box.chart offset)
        exactPolyhedron.hull := by
  intro p hp offset
  let ebox := box.eulerBox
  let q := outerPose p
  have hqmem : q ∈ ebox.realInterval :=
    box.outerPose_mem_eulerRealInterval hp
  have hqnear := ebox.near_center_of_mem_realInterval hqmem
  let relative := relativeRotationAtSymmetry
    (p.matrixPoseWithOffset box.chart offset) box.symmetryIndex
  obtain ⟨a⟩ := Noperthedron.BalancedSupport.exists_axisAngle
    relative.val relative.property
  apply
    Noperthedron.Nopert214.not_rupertPose_of_axisFree_symmetry_certificates_of_cover_perturbation
      (p := p.matrixPoseWithOffset box.chart offset)
      (g := box.symmetryIndex) (a := a)
      (index := fun j i => (ebox.certificate j).contact i |>.index)
      (weight := fun j => (ebox.certificate j).realWeight)
      (direction := fun j => (ebox.certificate j).realDirection)
      (A := fun j => Noperthedron.SnubCube.firstVariationVector
        (p.matrixPoseWithOffset box.chart offset)
        (ebox.certificate j).realWeight
        (ebox.certificate j).realDirection
        (LocalCertificate.AxisCertificate.realVertex ebox
          (ebox.certificate j)))
      (normalizedA := fun j =>
        (ebox.certificate j).normalizedAAt ebox q offset)
      (centerNormalizedA := fun j => toR3 (ebox.approxNormalizedA j))
      (B := fun j => ((ebox.certificate j).B : ℝ))
      (c := (ebox.c : ℝ)) (δ := (ebox.axisPerturbation : ℝ))
  · intro j
    exact_mod_cast LocalCertificate.AxisCertificate.B_pos ebox h.geometry j
  · intro j
    simpa [ebox, q, Noperthedron.SnubCube.firstVariationVector,
      Noperthedron.SnubCube.outerLift, Noperthedron.SnubCube.outerFrame,
      outerPose, AtlasPose.outerSO3, AtlasPose.matrixPoseWithOffset,
      Pose.matrixPoseWithOffset,
      Pose.matrixPoseOfPose] using
      (LocalCertificate.AxisCertificate.firstVariation_eq_B_smul_normalizedAAt
        ebox h.geometry j q offset)
  · intro axis haxis
    simpa only [Rat.cast_add] using
      LocalCertificate.valid_center_axis_cover ebox h.geometry axis haxis
  · exact LocalCertificate.valid_normalizedA_move
      ebox h.geometry hqnear offset
  · intro j
    rfl
  · exact LocalCertificate.AxisCertificate.real_remainder_le_B
      ebox h.geometry
  · exact box.valid_axisAngle_ratio h hp offset a
  · intro j i hdirection
    have hnorm :=
      LocalCertificate.AxisCertificate.realDirection_norm ebox h.geometry j i
    rw [hdirection, norm_zero] at hnorm
    norm_num at hnorm
  · exact LocalCertificate.AxisCertificate.realWeight_nonneg ebox h.geometry
  · intro j
    refine ⟨0, ?_⟩
    change (0 : ℝ) < ((ebox.certificate j).weight 0 : ℝ)
    exact_mod_cast h.geometry.weight_pos j 0
  · exact LocalCertificate.AxisCertificate.real_balance ebox h.geometry
  · intro j i k
    simpa [ebox, q, Box.eulerBox,
      LocalCertificate.AxisCertificate.realDirection,
      Noperthedron.BalancedSupport.outerProjectionLinear, outerPose,
      AtlasPose.outerSO3, AtlasPose.matrixPoseWithOffset,
      Pose.matrixPoseWithOffset,
      Pose.matrixPoseOfPose] using
      (LocalCertificate.valid_contact_support_matrixPose
        ebox h.geometry hqnear offset j i k)

theorem Box.valid_imp_no_translated_rupert_in_interval
    (box : Box) (h : box.Valid) :
    ¬ ∃ p ∈ box.interval.toReal, ∃ offset : ℝ²,
      RupertPose (p.matrixPoseWithOffset box.chart offset)
        exactPolyhedron.hull := by
  rintro ⟨p, hp, offset, hrupert⟩
  exact box.valid_imp_not_translated_rupert h p hp offset hrupert

end Noperthedron.Nopert214.AtlasLocalCertificate

end
