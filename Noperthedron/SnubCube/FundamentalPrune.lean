module

public import Noperthedron.SnubCube.FundamentalDomain
public import Noperthedron.SnubCube.LocalCertificate

@[expose] public section


/-!
# Exact pruning certificates for the snub-cube fundamental domain

A pruning row exhibits a symmetry whose trace score is uniformly better than
the identity score throughout a rational Euler box.  Such a box contains no
pose in the Dirichlet fundamental domain.  The checked arithmetic is entirely
rational; Taylor approximation and an operator-norm Lipschitz estimate provide
the semantic bridge.
-/

namespace Noperthedron.SnubCube.FundamentalPrune

open scoped Matrix RealInnerProductSpace

private lemma abs_matrix_entry_le_opNorm
    (A : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    |A i j| ≤ ‖A.toEuclideanLin.toContinuousLinearMap‖ := by
  let e : ℝ³ := WithLp.toLp 2 (Pi.single j 1)
  let L := A.toEuclideanLin.toContinuousLinearMap
  have hcoord := PiLp.norm_apply_le (L e) i
  have happ := L.le_opNorm e
  have he : ‖e‖ = 1 := by
    simp [e]
  have hentry : ‖(L e) i‖ = |A i j| := by
    simp [L, e, Matrix.toLpLin_apply]
  rw [hentry] at hcoord
  rw [he, mul_one] at happ
  exact hcoord.trans happ

private lemma matrix_sub_clm (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    (A - B).toEuclideanLin.toContinuousLinearMap =
      A.toEuclideanLin.toContinuousLinearMap -
        B.toEuclideanLin.toContinuousLinearMap := by
  ext v
  simp [Matrix.toLpLin_apply]

private lemma abs_trace_mul_le_eighteen_opNorm
    (A H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ∀ i j, |H i j| ≤ 2) :
    |Matrix.trace (A * H)| ≤
      18 * ‖A.toEuclideanLin.toContinuousLinearMap‖ := by
  rw [Matrix.trace]
  calc
    |∑ i, ∑ j, A i j * H j i| ≤ ∑ i, |∑ j, A i j * H j i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j * H j i| :=
      Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3,
        ‖A.toEuclideanLin.toContinuousLinearMap‖ * 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (abs_matrix_entry_le_opNorm A i j) (hH j i)
        (abs_nonneg _) (norm_nonneg _)
    _ = 18 * ‖A.toEuclideanLin.toContinuousLinearMap‖ := by
      simp
      ring

private lemma symmetry_sub_one_entry_le_two (g : VertexIndex) (i j : Fin 3) :
    |(symmetryMatrix g - 1) i j| ≤ 2 := by
  change |(symmetryMatrixInt g i j : ℝ) - (if i = j then 1 else 0)| ≤ 2
  have hz : |symmetryMatrixInt g i j - (if i = j then 1 else 0)| ≤
      (2 : ℤ) := by
    obtain ⟨p, s⟩ := g
    fin_cases p <;> fin_cases s <;> fin_cases i <;> fin_cases j <;>
      decide +kernel
  exact_mod_cast hz

/-- Trace improvement of symmetry `g` over the identity representative. -/
def traceAdvantage (R : Matrix (Fin 3) (Fin 3) ℝ) (g : VertexIndex) : ℝ :=
  Matrix.trace (R * (symmetryMatrix g - 1))

private theorem traceAdvantage_sub (R S : Matrix (Fin 3) (Fin 3) ℝ)
    (g : VertexIndex) :
    traceAdvantage R g - traceAdvantage S g =
      Matrix.trace ((R - S) * (symmetryMatrix g - 1)) := by
  simp only [traceAdvantage, Matrix.sub_mul, Matrix.trace_sub]

theorem abs_traceAdvantage_sub_le
    (R S : Matrix (Fin 3) (Fin 3) ℝ) (g : VertexIndex) :
    |traceAdvantage R g - traceAdvantage S g| ≤
      18 * ‖(R - S).toEuclideanLin.toContinuousLinearMap‖ := by
  rw [traceAdvantage_sub]
  exact abs_trace_mul_le_eighteen_opNorm _ _
    (symmetry_sub_one_entry_le_two g)

theorem traceAdvantage_pos_not_inFundamentalDomain
    {R : Matrix (Fin 3) (Fin 3) ℝ} {g : VertexIndex}
    (h : 0 < traceAdvantage R g) :
    ¬ InFundamentalDomain R := by
  intro hfund
  have hg := hfund g
  unfold traceAdvantage at h
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub] at h
  linarith

structure Box where
  interval : PoseInterval ℚ
  symmetryIndex : VertexIndex
deriving DecidableEq

def Box.center (box : Box) : Pose ℚ where
  θ₁ := (box.interval.min.θ₁ + box.interval.max.θ₁) / 2
  θ₂ := (box.interval.min.θ₂ + box.interval.max.θ₂) / 2
  φ₁ := (box.interval.min.φ₁ + box.interval.max.φ₁) / 2
  φ₂ := (box.interval.min.φ₂ + box.interval.max.φ₂) / 2
  α := (box.interval.min.α + box.interval.max.α) / 2

abbrev Box.εθ₁ (box : Box) : ℚ :=
  (box.interval.max.θ₁ - box.interval.min.θ₁) / 2
abbrev Box.εφ₁ (box : Box) : ℚ :=
  (box.interval.max.φ₁ - box.interval.min.φ₁) / 2
abbrev Box.εθ₂ (box : Box) : ℚ :=
  (box.interval.max.θ₂ - box.interval.min.θ₂) / 2
abbrev Box.εφ₂ (box : Box) : ℚ :=
  (box.interval.max.φ₂ - box.interval.min.φ₂) / 2
abbrev Box.εα (box : Box) : ℚ :=
  (box.interval.max.α - box.interval.min.α) / 2

def Box.eulerRadius (box : Box) : ℚ :=
  box.εα + box.εφ₁ + box.εθ₁ + box.εφ₂ + box.εθ₂

def centerApproxRadius : ℚ :=
  2 * LocalCertificate.rotationError + LocalCertificate.rotationError ^ 2

def Box.approxRelative (box : Box) : Matrix (Fin 3) (Fin 3) ℚ :=
  (LocalCertificate.rotRMQ box.center.θ₂ box.center.φ₂ 0)ᵀ *
    LocalCertificate.rotRMQ box.center.θ₁ box.center.φ₁ box.center.α

def Box.approxAdvantage (box : Box) : ℚ :=
  Matrix.trace (box.approxRelative *
    (LocalCertificate.symmetryMatrixQ box.symmetryIndex - 1))

def Box.Valid (box : Box) : Prop :=
  box.center ∈ fourInterval ℚ ∧
    18 * (centerApproxRadius + box.eulerRadius) < box.approxAdvantage

instance (box : Box) : Decidable box.Valid := by
  unfold Box.Valid
  infer_instance

noncomputable def Box.approxRelativeCLM (box : Box) : ℝ³ →L[ℝ] ℝ³ :=
  ((box.approxRelative).map fun x => (x : ℝ)).toEuclideanLin.toContinuousLinearMap

private theorem Box.approxRelativeCLM_eq (box : Box) :
    box.approxRelativeCLM =
      (LocalCertificate.rotRMQCLM box.center.θ₂ box.center.φ₂ 0).adjoint ∘L
        LocalCertificate.rotRMQCLM
          box.center.θ₁ box.center.φ₁ box.center.α := by
  let O := (LocalCertificate.rotRMQ
    box.center.θ₂ box.center.φ₂ 0).map fun x => (x : ℝ)
  let I := (LocalCertificate.rotRMQ
    box.center.θ₁ box.center.φ₁ box.center.α).map fun x => (x : ℝ)
  have hmap : (box.approxRelative.map fun x => (x : ℝ)) = Oᵀ * I := by
    ext i j
    simp only [Box.approxRelative, O, I, Matrix.map_apply,
      Matrix.mul_apply, Matrix.transpose_apply]
    push_cast
    rfl
  rw [Box.approxRelativeCLM, hmap]
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial (A := O)]
  change (O.conjTranspose * I).toEuclideanLin.toContinuousLinearMap =
    O.toEuclideanLin.toContinuousLinearMap.adjoint ∘L
      I.toEuclideanLin.toContinuousLinearMap
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  ext v
  simp only [ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, Matrix.mulVec_mulVec]

private theorem relativeRotationCLM_eq (p : MatrixPose) :
    p.relativeRotation.toEuclideanLin.toContinuousLinearMap =
      (Noperthedron.SnubCube.so3CLM p.outerRot).adjoint ∘L
        Noperthedron.SnubCube.so3CLM p.innerRot := by
  simp only [MatrixPose.relativeRotation,
    Noperthedron.SnubCube.so3CLM]
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial
      (A := p.outerRot.val),
    ← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  ext v
  simp only [ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, Matrix.mulVec_mulVec]

private theorem relativeRotationCLM_eq_SO3 (p : MatrixPose) :
    p.relativeRotation.toEuclideanLin.toContinuousLinearMap =
      Noperthedron.SnubCube.so3CLM
        (Noperthedron.BalancedSupport.relativeRotation p) := by
  unfold MatrixPose.relativeRotation
    Noperthedron.BalancedSupport.relativeRotation
    Noperthedron.SnubCube.so3CLM
  rfl

theorem Box.center_relative_approx (box : Box) (h : box.Valid) :
    ‖(box.center.toReal.matrixPoseWithOffset 0).relativeRotation.toEuclideanLin.toContinuousLinearMap -
        box.approxRelativeCLM‖ ≤ (centerApproxRadius : ℝ) := by
  obtain ⟨hθ₁, hθ₂, hφ₁, hφ₂, hα⟩ :=
    PoseInterval.contains_iff_components.mp h.1
  have hθ₁' := RationalApprox.cast_Icc4_mem ⟨box.center.θ₁, hθ₁⟩
  have hθ₂' := RationalApprox.cast_Icc4_mem ⟨box.center.θ₂, hθ₂⟩
  have hφ₁' := RationalApprox.cast_Icc4_mem ⟨box.center.φ₁, hφ₁⟩
  have hφ₂' := RationalApprox.cast_Icc4_mem ⟨box.center.φ₂, hφ₂⟩
  have hα' := RationalApprox.cast_Icc4_mem ⟨box.center.α, hα⟩
  have hin := LocalCertificate.rotRMQ_difference_norm_bounded
    box.center.θ₁ box.center.φ₁ box.center.α hθ₁' hφ₁' hα'
  have hout := LocalCertificate.rotRMQ_difference_norm_bounded
    box.center.θ₂ box.center.φ₂ 0 hθ₂' hφ₂' (by norm_num)
  have hinReal :
      ‖rotRM box.center.toReal.θ₁ box.center.toReal.φ₁ box.center.toReal.α -
        LocalCertificate.rotRMQCLM
          box.center.θ₁ box.center.φ₁ box.center.α‖ ≤
        (LocalCertificate.rotationError : ℝ) := by
    simpa only [Pose.toReal_θ₁, Pose.toReal_φ₁,
      Pose.toReal_α] using hin
  have houtReal :
      ‖rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0 -
        LocalCertificate.rotRMQCLM box.center.θ₂ box.center.φ₂ 0‖ ≤
          (LocalCertificate.rotationError : ℝ) := by
    norm_num at hout ⊢
    simpa only [Pose.toReal_θ₂, Pose.toReal_φ₂] using hout
  have herrnonneg : (0 : ℝ) ≤ (LocalCertificate.rotationError : ℝ) := by
    exact_mod_cast LocalCertificate.rotationError_nonneg
  have hinnerNorm :
      ‖rotRM box.center.toReal.θ₁ box.center.toReal.φ₁
        box.center.toReal.α‖ = 1 := by
    simp only [rotRM]
    rw [Bounding.Rz_preserves_op_norm, Bounding.Rz_preserves_op_norm,
      Bounding.Ry_preserves_op_norm, Bounding.Rz_norm_one]
  have houterNorm :
      ‖rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0‖ = 1 := by
    simp only [rotRM]
    rw [Bounding.Rz_preserves_op_norm, Bounding.Rz_preserves_op_norm,
      Bounding.Ry_preserves_op_norm, Bounding.Rz_norm_one]
  have hinnerApprox :
      ‖LocalCertificate.rotRMQCLM
        box.center.θ₁ box.center.φ₁ box.center.α‖ ≤
          1 + (LocalCertificate.rotationError : ℝ) :=
    calc
      ‖LocalCertificate.rotRMQCLM
          box.center.θ₁ box.center.φ₁ box.center.α‖ ≤
        ‖rotRM box.center.toReal.θ₁ box.center.toReal.φ₁
          box.center.toReal.α‖ +
        ‖rotRM box.center.toReal.θ₁ box.center.toReal.φ₁
            box.center.toReal.α -
          LocalCertificate.rotRMQCLM
            box.center.θ₁ box.center.φ₁ box.center.α‖ :=
        norm_le_insert _ _
      _ ≤ 1 + (LocalCertificate.rotationError : ℝ) := by
        rw [hinnerNorm]
        gcongr
  rw [box.approxRelativeCLM_eq]
  rw [relativeRotationCLM_eq]
  simp only [Pose.matrixPoseWithOffset, Pose.matrixPoseOfPose,
    Noperthedron.SnubCube.so3CLM]
  rw [← rotRM_eq_rotRM_mat, ← rotRM_eq_rotRM_mat]
  have hdecomp :
      (rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0).adjoint ∘L
          rotRM box.center.toReal.θ₁ box.center.toReal.φ₁ box.center.toReal.α -
        (LocalCertificate.rotRMQCLM box.center.θ₂ box.center.φ₂ 0).adjoint ∘L
          LocalCertificate.rotRMQCLM box.center.θ₁ box.center.φ₁ box.center.α =
      (rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0).adjoint ∘L
          (rotRM box.center.toReal.θ₁ box.center.toReal.φ₁ box.center.toReal.α -
            LocalCertificate.rotRMQCLM
              box.center.θ₁ box.center.φ₁ box.center.α) +
        ((rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0).adjoint -
          (LocalCertificate.rotRMQCLM
            box.center.θ₂ box.center.φ₂ 0).adjoint) ∘L
          LocalCertificate.rotRMQCLM
            box.center.θ₁ box.center.φ₁ box.center.α := by
    ext v
    simp
  have houtAdjoint :
      ‖(rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0).adjoint -
        (LocalCertificate.rotRMQCLM box.center.θ₂ box.center.φ₂ 0).adjoint‖ ≤
          (LocalCertificate.rotationError : ℝ) := by
    simpa only [← map_sub, ContinuousLinearMap.adjoint.norm_map] using houtReal
  rw [hdecomp]
  calc
    ‖(rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0).adjoint ∘L
          (rotRM box.center.toReal.θ₁ box.center.toReal.φ₁ box.center.toReal.α -
            LocalCertificate.rotRMQCLM
              box.center.θ₁ box.center.φ₁ box.center.α) +
        ((rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0).adjoint -
          (LocalCertificate.rotRMQCLM box.center.θ₂ box.center.φ₂ 0).adjoint) ∘L
            LocalCertificate.rotRMQCLM
              box.center.θ₁ box.center.φ₁ box.center.α‖ ≤
      ‖(rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0).adjoint ∘L
          (rotRM box.center.toReal.θ₁ box.center.toReal.φ₁ box.center.toReal.α -
            LocalCertificate.rotRMQCLM
              box.center.θ₁ box.center.φ₁ box.center.α)‖ +
        ‖((rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0).adjoint -
          (LocalCertificate.rotRMQCLM box.center.θ₂ box.center.φ₂ 0).adjoint) ∘L
            LocalCertificate.rotRMQCLM
              box.center.θ₁ box.center.φ₁ box.center.α‖ := norm_add_le _ _
    _ ≤ ‖(rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0).adjoint‖ *
          ‖rotRM box.center.toReal.θ₁ box.center.toReal.φ₁ box.center.toReal.α -
            LocalCertificate.rotRMQCLM
              box.center.θ₁ box.center.φ₁ box.center.α‖ +
        ‖(rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0).adjoint -
          (LocalCertificate.rotRMQCLM box.center.θ₂ box.center.φ₂ 0).adjoint‖ *
          ‖LocalCertificate.rotRMQCLM
            box.center.θ₁ box.center.φ₁ box.center.α‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        (ContinuousLinearMap.opNorm_comp_le _ _)
    _ =
    1 * ‖rotRM box.center.toReal.θ₁ box.center.toReal.φ₁ box.center.toReal.α -
        LocalCertificate.rotRMQCLM box.center.θ₁ box.center.φ₁ box.center.α‖ +
      ‖(rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0).adjoint -
        (LocalCertificate.rotRMQCLM box.center.θ₂ box.center.φ₂ 0).adjoint‖ *
          ‖LocalCertificate.rotRMQCLM
            box.center.θ₁ box.center.φ₁ box.center.α‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map, houterNorm]
    _ ≤
      1 * (LocalCertificate.rotationError : ℝ) +
        (LocalCertificate.rotationError : ℝ) *
          (1 + (LocalCertificate.rotationError : ℝ)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hinReal zero_le_one)
        (mul_le_mul houtAdjoint hinnerApprox (norm_nonneg _) herrnonneg)
    _ = (centerApproxRadius : ℝ) := by
      norm_num [centerApproxRadius]
      ring

private theorem symmetryMatrixQ_cast (g : VertexIndex) :
    (LocalCertificate.symmetryMatrixQ g).map (fun x => (x : ℝ)) =
      symmetryMatrix g := by
  unfold LocalCertificate.symmetryMatrixQ symmetryMatrix
  ext i j
  simp

theorem Box.approxAdvantage_cast (box : Box) :
    (box.approxAdvantage : ℝ) =
      traceAdvantage
        (box.approxRelative.map (fun x => (x : ℝ))) box.symmetryIndex := by
  unfold Box.approxAdvantage traceAdvantage
  have hmap :
      ((box.approxRelative *
          (LocalCertificate.symmetryMatrixQ box.symmetryIndex - 1)).map
        (fun x => (x : ℝ))) =
      box.approxRelative.map (fun x => (x : ℝ)) *
        (symmetryMatrix box.symmetryIndex - 1) := by
    rw [← symmetryMatrixQ_cast box.symmetryIndex]
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.one_apply]
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = j <;> simp [hx]
  rw [← hmap]
  simp [Matrix.trace]

def Box.realInterval (box : Box) : PoseInterval ℝ :=
  PoseInterval.mk box.interval.min.toReal box.interval.max.toReal (by
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      (Pose.le_iff _ _).mp box.interval.min_le_max
    rw [Pose.le_iff]
    simp only [Pose.toReal_θ₁, Pose.toReal_θ₂, Pose.toReal_φ₁,
      Pose.toReal_φ₂, Pose.toReal_α]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2,
      by exact_mod_cast h3, by exact_mod_cast h4,
      by exact_mod_cast h5⟩)

theorem Box.near_center_of_mem_realInterval (box : Box) {q : Pose ℝ}
    (hq : q ∈ box.realInterval) :
    Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q := by
  rw [NonemptyInterval.mem_def] at hq
  obtain ⟨hlo, hhi⟩ := hq
  rw [Pose.le_iff] at hlo hhi
  obtain ⟨l1, l2, l3, l4, l5⟩ := hlo
  obtain ⟨u1, u2, u3, u4, u5⟩ := hhi
  simp only [Box.realInterval, PoseInterval.mk, PoseInterval.min,
    PoseInterval.max, Pose.toReal_θ₁, Pose.toReal_θ₂,
    Pose.toReal_φ₁, Pose.toReal_φ₂, Pose.toReal_α] at l1 l2 l3 l4 l5 u1 u2 u3 u4 u5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [Box.center, Pose.toReal_θ₁, Pose.toReal_θ₂,
      Pose.toReal_φ₁, Pose.toReal_φ₂, Pose.toReal_α,
      Box.εθ₁, Box.εφ₁, Box.εθ₂, Box.εφ₂, Box.εα]
    rw [abs_sub_le_iff]
    push_cast
    constructor <;> linarith

/-- A valid rational prune box contains no translated Euler pose in the
relative-rotation fundamental domain. -/
theorem Box.valid_imp_not_inFundamentalDomain
    (box : Box) (h : box.Valid) {q : Pose ℝ}
    (hq : q ∈ box.realInterval) (offset : ℝ²) :
    ¬ (q.matrixPoseWithOffset offset).InSnubFundamentalDomain := by
  let p := q.matrixPoseWithOffset offset
  let centerPose := box.center.toReal.matrixPoseWithOffset 0
  let approxR := box.approxRelative.map (fun x => (x : ℝ))
  have hnear := box.near_center_of_mem_realInterval hq
  obtain ⟨hθ₁, hφ₁, hθ₂, hφ₂, hα⟩ := hnear
  have hrotSO3 := norm_relativeRotation_matrixPoseWithOffset_sub_le
    q box.center.toReal offset 0
  have hrot :
      ‖(p.relativeRotation - centerPose.relativeRotation).toEuclideanLin.toContinuousLinearMap‖ ≤
        (box.eulerRadius : ℝ) := by
    have hclm :
        (p.relativeRotation - centerPose.relativeRotation).toEuclideanLin.toContinuousLinearMap =
          Noperthedron.SnubCube.so3CLM
              (Noperthedron.BalancedSupport.relativeRotation p) -
            Noperthedron.SnubCube.so3CLM
              (Noperthedron.BalancedSupport.relativeRotation centerPose) := by
      rw [matrix_sub_clm]
      rw [relativeRotationCLM_eq_SO3, relativeRotationCLM_eq_SO3]
    rw [hclm]
    apply hrotSO3.trans
    rw [show (box.eulerRadius : ℝ) =
      (box.εα : ℝ) + (box.εφ₁ : ℝ) + (box.εθ₁ : ℝ) +
        (box.εφ₂ : ℝ) + (box.εθ₂ : ℝ) by
      norm_num [Box.eulerRadius]]
    linarith
  have hmove := abs_traceAdvantage_sub_le
    p.relativeRotation centerPose.relativeRotation box.symmetryIndex
  have hmove' :
      |traceAdvantage p.relativeRotation box.symmetryIndex -
          traceAdvantage centerPose.relativeRotation box.symmetryIndex| ≤
        18 * (box.eulerRadius : ℝ) :=
    hmove.trans (mul_le_mul_of_nonneg_left hrot (by norm_num))
  have hcenterNorm := box.center_relative_approx h
  have hcenterAbs := abs_traceAdvantage_sub_le
    centerPose.relativeRotation approxR box.symmetryIndex
  have hcenterAbs' :
      |traceAdvantage centerPose.relativeRotation box.symmetryIndex -
          traceAdvantage approxR box.symmetryIndex| ≤
        18 * (centerApproxRadius : ℝ) := by
    apply hcenterAbs.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [matrix_sub_clm]
    simpa only [approxR, Box.approxRelativeCLM, centerPose] using hcenterNorm
  have hadvantage :
      18 * ((centerApproxRadius : ℝ) + (box.eulerRadius : ℝ)) <
        traceAdvantage approxR box.symmetryIndex := by
    have hadvantageQ := h.2
    have hadvantageR :
        (18 * (centerApproxRadius + box.eulerRadius) : ℚ) <
          box.approxAdvantage := hadvantageQ
    have hcast :
        ((18 * (centerApproxRadius + box.eulerRadius) : ℚ) : ℝ) <
          (box.approxAdvantage : ℝ) := by exact_mod_cast hadvantageR
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_add,
      box.approxAdvantage_cast, approxR] using hcast
  have hpos : 0 < traceAdvantage p.relativeRotation box.symmetryIndex := by
    have hm := (abs_le.mp hmove').1
    have hc := (abs_le.mp hcenterAbs').1
    linarith
  exact traceAdvantage_pos_not_inFundamentalDomain hpos

/-- Interval form consumed by the fundamental-domain solution tree. -/
theorem Box.valid_imp_no_fundamental_pose_in_interval
    (box : Box) (h : box.Valid) :
    ¬ ∃ q ∈ box.realInterval, ∃ offset : ℝ²,
      (q.matrixPoseWithOffset offset).InSnubFundamentalDomain := by
  rintro ⟨q, hq, offset, hfund⟩
  exact box.valid_imp_not_inFundamentalDomain h hq offset hfund

end Noperthedron.SnubCube.FundamentalPrune

end
