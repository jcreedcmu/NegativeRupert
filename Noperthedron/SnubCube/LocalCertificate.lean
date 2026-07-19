module

public import Noperthedron.Checker.SqrtFixed
public import Noperthedron.SnubCube.Certificate
public import Noperthedron.SnubCube.LocalRigidity

@[expose] public section


/-!
# Rational local certificates for the snub cube

A row contains four balanced three-contact obstructions.  Six rational
barycentric combinations certify an octahedron inside their rationalized
first-variation vectors.  The remaining checks are support inequalities and
a Frobenius bound on distance from one of the 24 symmetry strata.
-/

namespace Noperthedron.SnubCube.LocalCertificate

open scoped Matrix RealInnerProductSpace
open RationalApprox GlobalTheorem

structure Contact where
  index : VertexIndex
  direction : Fin 2 → ℚ
deriving DecidableEq, Repr

structure AxisCertificate where
  contact : Fin 3 → Contact
deriving DecidableEq, Repr

structure Box where
  interval : PoseInterval ℚ
  symmetryIndex : VertexIndex
  certificate : Fin 4 → AxisCertificate
  c : ℚ
  r : ℚ
deriving DecidableEq

def Box.center (box : Box) : Pose ℚ where
  θ₁ := (box.interval.min.θ₁ + box.interval.max.θ₁) / 2
  θ₂ := (box.interval.min.θ₂ + box.interval.max.θ₂) / 2
  φ₁ := (box.interval.min.φ₁ + box.interval.max.φ₁) / 2
  φ₂ := (box.interval.min.φ₂ + box.interval.max.φ₂) / 2
  α := (box.interval.min.α + box.interval.max.α) / 2

abbrev Box.εθ₁ (box : Box) : ℚ := (box.interval.max.θ₁ - box.interval.min.θ₁) / 2
abbrev Box.εφ₁ (box : Box) : ℚ := (box.interval.max.φ₁ - box.interval.min.φ₁) / 2
abbrev Box.εθ₂ (box : Box) : ℚ := (box.interval.max.θ₂ - box.interval.min.θ₂) / 2
abbrev Box.εφ₂ (box : Box) : ℚ := (box.interval.max.φ₂ - box.interval.min.φ₂) / 2
abbrev Box.εα (box : Box) : ℚ := (box.interval.max.α - box.interval.min.α) / 2

def det2 (u v : Fin 2 → ℚ) : ℚ := u 0 * v 1 - u 1 * v 0

/-- Determinant weights automatically balance three planar directions. -/
def AxisCertificate.weight (cert : AxisCertificate) : Fin 3 → ℚ :=
  ![det2 (cert.contact 1).direction (cert.contact 2).direction,
    det2 (cert.contact 2).direction (cert.contact 0).direction,
    det2 (cert.contact 0).direction (cert.contact 1).direction]

def AxisCertificate.B (cert : AxisCertificate) : ℚ := ∑ i, cert.weight i

def directionUnit (u : Fin 2 → ℚ) : Prop := u 0 ^ 2 + u 1 ^ 2 = 1

instance (u : Fin 2 → ℚ) : Decidable (directionUnit u) := by
  unfold directionUnit
  infer_instance

private theorem direction_norm_eq_one {u : Fin 2 → ℚ} (h : directionUnit u) :
    ‖toR2 u‖ = 1 := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_one]
  congr 1
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, toR2,
    WithLp.ofLp_toLp]
  exact_mod_cast h

def crossQ (u v : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

private theorem toR3_crossQ (u v : Fin 3 → ℚ) :
    toR3 (crossQ u v) =
      Noperthedron.BalancedSupport.cross3 (toR3 u) (toR3 v) := by
  ext i
  fin_cases i <;>
    simp [crossQ, Noperthedron.BalancedSupport.cross3, cross_apply, toR3]

private theorem toR3_sum {ι : Type} [Fintype ι]
    (f : ι → Fin 3 → ℚ) :
    toR3 (∑ i, f i) = ∑ i, toR3 (f i) := by
  ext c
  simp [toR3]

private theorem toR3_smul (a : ℚ) (v : Fin 3 → ℚ) :
    toR3 (a • v) = (a : ℝ) • toR3 v := by
  ext c
  simp [toR3]

private theorem toR3_rotMℚ_transpose_mulVec
    (theta phi : ℚ) (u : Fin 2 → ℚ) :
    toR3 ((RationalApprox.rotMℚ_mat theta phi)ᵀ *ᵥ u) =
      (RationalApprox.rotMℚℝ (theta : ℝ) (phi : ℝ)).adjoint (toR2 u) := by
  have hcast : (RationalApprox.rotMℚ_mat (theta : ℝ) (phi : ℝ))ᵀ =
      ((RationalApprox.rotMℚ_mat theta phi)ᵀ).map (fun x => (x : ℝ)) := by
    rw [RationalApprox.rotMℚ_mat_castℝ]
    rfl
  unfold toR3 toR2
  rw [RationalApprox.toLp_cast_mulVec hcast]
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial
      (A := RationalApprox.rotMℚ_mat (theta : ℝ) (phi : ℝ)),
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint
      (A := RationalApprox.rotMℚ_mat (theta : ℝ) (phi : ℝ))]
  rfl

/-- Rational frame whose first two rows approximate the outer projection and
whose last row approximates the viewing normal. -/
def frameQ (theta phi : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-sinℚ theta, cosℚ theta, 0;
     -cosℚ theta * cosℚ phi, -sinℚ theta * cosℚ phi, sinℚ phi;
      cosℚ theta * sinℚ phi,  sinℚ theta * sinℚ phi, cosℚ phi]

def rzQ (alpha : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![cosℚ alpha, -sinℚ alpha, 0;
     sinℚ alpha,  cosℚ alpha, 0;
     0, 0, 1]

def frameApprox : Matrix (Fin 3) (Fin 3)
    RationalApprox.DistLeKappaEntry :=
  !![(.msin, .one), (.cos, .one), (.zero, .zero);
     (.mcos, .cos), (.msin, .cos), (.one, .sin);
     (.cos, .sin), (.sin, .sin), (.one, .cos)]

def rz3Approx : Matrix (Fin 3) (Fin 3)
    RationalApprox.DistLeKappaEntry :=
  !![(.one, .cos), (.one, .msin), (.zero, .zero);
     (.one, .sin), (.one, .cos), (.zero, .zero);
     (.zero, .zero), (.zero, .zero), (.one, .one)]

noncomputable def frameQCLM (theta phi : ℚ) : ℝ³ →L[ℝ] ℝ³ :=
  ((frameQ theta phi).map fun x => (x : ℝ)).toEuclideanLin.toContinuousLinearMap

noncomputable def rzQCLM (alpha : ℚ) : ℝ³ →L[ℝ] ℝ³ :=
  ((rzQ alpha).map fun x => (x : ℝ)).toEuclideanLin.toContinuousLinearMap

private theorem frameQ_difference_norm_bounded
    (theta phi : ℚ) (hθ : (theta : ℝ) ∈ Set.Icc (-4 : ℝ) 4)
    (hφ : (phi : ℝ) ∈ Set.Icc (-4 : ℝ) 4) :
    ‖rotRM (theta : ℝ) (phi : ℝ) 0 - frameQCLM theta phi‖ ≤
      RationalApprox.κ := by
  let θ4 : Set.Icc (-4 : ℝ) 4 := ⟨theta, hθ⟩
  let φ4 : Set.Icc (-4 : ℝ) 4 := ⟨phi, hφ⟩
  have hactual : rotRM (theta : ℝ) (phi : ℝ) 0 =
      RationalApprox.clinActual frameApprox θ4 φ4 := by
    rw [rotRM_eq_rotRM_mat]
    unfold RationalApprox.clinActual
    apply congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      M.toEuclideanLin.toContinuousLinearMap)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotRM_mat, Rz_mat, Ry_mat, frameApprox, θ4, φ4,
        Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  have happrox : frameQCLM theta phi =
      RationalApprox.clinApprox frameApprox θ4 φ4 := by
    unfold frameQCLM RationalApprox.clinApprox
    apply congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      M.toEuclideanLin.toContinuousLinearMap)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [frameQ, frameApprox, θ4, φ4, sinℚ_match, cosℚ_match]
  rw [hactual, happrox]
  exact RationalApprox.norm_matrix_actual_approx_le_kappa
    (m := ⟨3, by norm_num⟩) (n := ⟨3, by norm_num⟩)
    frameApprox θ4 φ4

private theorem rzQ_difference_norm_bounded
    (alpha : ℚ) (hα : (alpha : ℝ) ∈ Set.Icc (-4 : ℝ) 4) :
    ‖RzL (alpha : ℝ) - rzQCLM alpha‖ ≤ RationalApprox.κ := by
  let z4 : Set.Icc (-4 : ℝ) 4 := ⟨0, by norm_num⟩
  let α4 : Set.Icc (-4 : ℝ) 4 := ⟨alpha, hα⟩
  have hactual : RzL (alpha : ℝ) =
      RationalApprox.clinActual rz3Approx z4 α4 := by
    unfold RzL RationalApprox.clinActual
    apply congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      M.toEuclideanLin.toContinuousLinearMap)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Rz_mat, rz3Approx, z4, α4]
  have happrox : rzQCLM alpha =
      RationalApprox.clinApprox rz3Approx z4 α4 := by
    unfold rzQCLM RationalApprox.clinApprox
    apply congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      M.toEuclideanLin.toContinuousLinearMap)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rzQ, rz3Approx, z4, α4, sinℚ_match, cosℚ_match]
  rw [hactual, happrox]
  exact RationalApprox.norm_matrix_actual_approx_le_kappa
    (m := ⟨3, by norm_num⟩) (n := ⟨3, by norm_num⟩)
    rz3Approx z4 α4

/-- Conservative full-rotation approximation error. -/
def rotationError : ℚ := 3 * κℚ + κℚ ^ 2

def rotRMQ (theta phi alpha : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  rzQ alpha * frameQ theta phi

noncomputable def rotRMQCLM (theta phi alpha : ℚ) : ℝ³ →L[ℝ] ℝ³ :=
  ((rotRMQ theta phi alpha).map fun x => (x : ℝ)).toEuclideanLin.toContinuousLinearMap

private theorem rotRM_eq_rz_comp (theta phi alpha : ℝ) :
    rotRM theta phi alpha = RzL alpha ∘L rotRM theta phi 0 := by
  have hmat : rotRM_mat theta phi alpha =
      Rz_mat alpha * rotRM_mat theta phi 0 := by
    simp only [rotRM_mat]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Bounding.Rz_mat_mul_Rz_mat, Bounding.Rz_mat_mul_Rz_mat]
    rw [add_comm]
    simp only [add_zero]
    rw [Bounding.Rz_mat_mul_Rz_mat]
  rw [rotRM_eq_rotRM_mat, rotRM_eq_rotRM_mat]
  ext v
  simp only [ContinuousLinearMap.comp_apply, RzL,
    LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply]
  rw [hmat, Matrix.mulVec_mulVec]

private theorem rotRMQCLM_eq_comp (theta phi alpha : ℚ) :
    rotRMQCLM theta phi alpha = rzQCLM alpha ∘L frameQCLM theta phi := by
  have hmap : ((rotRMQ theta phi alpha).map fun x => (x : ℝ)) =
      ((rzQ alpha).map fun x => (x : ℝ)) *
        ((frameQ theta phi).map fun x => (x : ℝ)) := by
    ext i j
    simp only [rotRMQ, Matrix.map_apply, Matrix.mul_apply]
    push_cast
    rfl
  ext v
  simp only [rotRMQCLM, rzQCLM, frameQCLM,
    ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
    Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  rw [hmap, Matrix.mulVec_mulVec]

theorem rotRMQ_difference_norm_bounded
    (theta phi alpha : ℚ)
    (hθ : (theta : ℝ) ∈ Set.Icc (-4 : ℝ) 4)
    (hφ : (phi : ℝ) ∈ Set.Icc (-4 : ℝ) 4)
    (hα : (alpha : ℝ) ∈ Set.Icc (-4 : ℝ) 4) :
    ‖rotRM (theta : ℝ) (phi : ℝ) (alpha : ℝ) -
        rotRMQCLM theta phi alpha‖ ≤ (rotationError : ℝ) := by
  have hframe := frameQ_difference_norm_bounded theta phi hθ hφ
  have hrz := rzQ_difference_norm_bounded alpha hα
  have hexactFrame : ‖rotRM (theta : ℝ) (phi : ℝ) 0‖ = 1 := by
    simp only [rotRM]
    rw [Bounding.Rz_preserves_op_norm, Bounding.Rz_preserves_op_norm,
      Bounding.Ry_preserves_op_norm, Bounding.Rz_norm_one]
  have hframeNorm : ‖frameQCLM theta phi‖ ≤ 1 + RationalApprox.κ :=
    RationalApprox.approx_norm_le hexactFrame.le hframe
  rw [rotRM_eq_rz_comp, rotRMQCLM_eq_comp]
  have hdecomp :
      RzL (alpha : ℝ) ∘L rotRM (theta : ℝ) (phi : ℝ) 0 -
          rzQCLM alpha ∘L frameQCLM theta phi =
        RzL (alpha : ℝ) ∘L
            (rotRM (theta : ℝ) (phi : ℝ) 0 - frameQCLM theta phi) +
          (RzL (alpha : ℝ) - rzQCLM alpha) ∘L frameQCLM theta phi := by
    ext v
    simp
  rw [hdecomp]
  calc
    ‖RzL (alpha : ℝ) ∘L
          (rotRM (theta : ℝ) (phi : ℝ) 0 - frameQCLM theta phi) +
        (RzL (alpha : ℝ) - rzQCLM alpha) ∘L frameQCLM theta phi‖ ≤
      ‖RzL (alpha : ℝ) ∘L
          (rotRM (theta : ℝ) (phi : ℝ) 0 - frameQCLM theta phi)‖ +
        ‖(RzL (alpha : ℝ) - rzQCLM alpha) ∘L frameQCLM theta phi‖ :=
      norm_add_le _ _
    _ ≤ 1 * RationalApprox.κ +
        RationalApprox.κ * (1 + RationalApprox.κ) := by
      apply add_le_add
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (le_of_eq (Bounding.Rz_norm_one _)) hframe
            (norm_nonneg _) (by norm_num))
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hrz hframeNorm (norm_nonneg _) (by
            unfold RationalApprox.κ
            norm_num))
    _ ≤ (rotationError : ℝ) := by
      norm_num [rotationError, RationalApprox.κ, RationalApprox.κℚ]

def symmetryMatrixQ (g : VertexIndex) : Matrix (Fin 3) (Fin 3) ℚ :=
  (symmetryMatrixInt g).map fun z => (z : ℚ)

noncomputable def symmetryQCLM (g : VertexIndex) : ℝ³ →L[ℝ] ℝ³ :=
  ((symmetryMatrixQ g).map fun x => (x : ℝ)).toEuclideanLin.toContinuousLinearMap

private theorem symmetryQCLM_eq_so3CLM (g : VertexIndex) :
    symmetryQCLM g = Noperthedron.SnubCube.so3CLM (symmetry g) := by
  unfold symmetryQCLM symmetryMatrixQ Noperthedron.SnubCube.so3CLM
    symmetry symmetryMatrix
  apply congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
    M.toEuclideanLin.toContinuousLinearMap)
  ext i j
  simp

def Box.mismatchMatrix (box : Box) : Matrix (Fin 3) (Fin 3) ℚ :=
  rotRMQ box.center.θ₁ box.center.φ₁ box.center.α -
    rotRMQ box.center.θ₂ box.center.φ₂ 0 * symmetryMatrixQ box.symmetryIndex

def Box.mismatchFrobeniusSq (box : Box) : ℚ :=
  ∑ i, ∑ j, box.mismatchMatrix i j ^ 2

noncomputable def Box.mismatchQCLM (box : Box) : ℝ³ →L[ℝ] ℝ³ :=
  ((box.mismatchMatrix).map fun x => (x : ℝ)).toEuclideanLin.toContinuousLinearMap

noncomputable def Box.centerMismatchCLM (box : Box) : ℝ³ →L[ℝ] ℝ³ :=
  rotRM box.center.toReal.θ₁ box.center.toReal.φ₁ box.center.toReal.α -
    rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0 ∘L
      Noperthedron.SnubCube.so3CLM (symmetry box.symmetryIndex)

private theorem Box.mismatchQCLM_eq (box : Box) :
    box.mismatchQCLM =
      rotRMQCLM box.center.θ₁ box.center.φ₁ box.center.α -
        rotRMQCLM box.center.θ₂ box.center.φ₂ 0 ∘L
          Noperthedron.SnubCube.so3CLM (symmetry box.symmetryIndex) := by
  rw [← symmetryQCLM_eq_so3CLM]
  have hmat : (box.mismatchMatrix.map fun x => (x : ℝ)) =
      (rotRMQ box.center.θ₁ box.center.φ₁ box.center.α).map (fun x => (x : ℝ)) -
        (rotRMQ box.center.θ₂ box.center.φ₂ 0).map (fun x => (x : ℝ)) *
          (symmetryMatrixQ box.symmetryIndex).map (fun x => (x : ℝ)) := by
    ext i j
    simp only [Box.mismatchMatrix, Matrix.map_apply, Matrix.sub_apply,
      Matrix.mul_apply]
    push_cast
    rfl
  ext v
  simp only [Box.mismatchQCLM, rotRMQCLM, symmetryQCLM,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, Matrix.toLpLin_apply]
  rw [hmat, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  rfl

private theorem mismatchFrobeniusSq_nonneg (box : Box) :
    0 ≤ box.mismatchFrobeniusSq := by
  unfold Box.mismatchFrobeniusSq
  positivity

theorem Box.mismatchQCLM_norm_le_sqrt (box : Box) :
    ‖box.mismatchQCLM‖ ≤ (sqrtℚUp16 box.mismatchFrobeniusSq : ℝ) := by
  apply Noperthedron.BalancedSupport.matrix_opNorm_le_of_sum_sq_le
  · exact_mod_cast sqrtℚUp16_nonneg box.mismatchFrobeniusSq
  · have hsq := le_mul_self_sqrtℚUp16 (mismatchFrobeniusSq_nonneg box)
    have hcast :
        ∑ i, ∑ j, (box.mismatchMatrix.map (fun x => (x : ℝ))) i j ^ 2 =
          (box.mismatchFrobeniusSq : ℝ) := by
      unfold Box.mismatchFrobeniusSq
      push_cast
      rfl
    rw [hcast]
    exact_mod_cast (by simpa [pow_two] using hsq)

def Box.eulerRadius (box : Box) : ℚ :=
  box.εα + box.εφ₁ + box.εθ₁ + box.εφ₂ + box.εθ₂

def Box.mismatchRadius (box : Box) : ℚ :=
  sqrtℚUp16 box.mismatchFrobeniusSq + 2 * rotationError + box.eulerRadius

def Box.outerRadius (box : Box) : ℚ := box.εφ₂ + box.εθ₂

def centerVectorError : ℚ := 2 * κℚ + κℚ ^ 2

def Box.axisPerturbation (box : Box) : ℚ := box.outerRadius + centerVectorError

def AxisCertificate.approxLift (box : Box) (cert : AxisCertificate) (i : Fin 3) :
    Fin 3 → ℚ :=
  (RationalApprox.rotMℚ_mat box.center.θ₂ box.center.φ₂)ᵀ *ᵥ
    (cert.contact i).direction

def AxisCertificate.approxA (box : Box) (cert : AxisCertificate) : Fin 3 → ℚ :=
  ∑ i, cert.weight i • crossQ
    (normalizedRationalVertex
      (symmetryAction box.symmetryIndex (cert.contact i).index))
    (cert.approxLift box i)

def AxisCertificate.approxNormalizedA (box : Box) (cert : AxisCertificate) :
    Fin 3 → ℚ :=
  fun k => cert.approxA box k / cert.B

def Box.approxNormalizedA (box : Box) (j : Fin 4) : Fin 3 → ℚ :=
  (box.certificate j).approxNormalizedA box

def sub3Q (u v : Fin 3 → ℚ) : Fin 3 → ℚ := fun i => u i - v i

def det3Q (u v w : Fin 3 → ℚ) : ℚ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) -
    u 1 * (v 0 * w 2 - v 2 * w 0) +
      u 2 * (v 0 * w 1 - v 1 * w 0)

def tetraDetQ (p : Fin 4 → Fin 3 → ℚ) : ℚ :=
  det3Q (sub3Q (p 0) (p 3)) (sub3Q (p 1) (p 3))
    (sub3Q (p 2) (p 3))

/-- Canonical exact barycentric coordinates in a nondegenerate rational
tetrahedron.  Computing these in the checker avoids storing the generally
large Cramer-rule fractions in every local row. -/
def tetraBarycentricQ (p : Fin 4 → Fin 3 → ℚ) (target : Fin 3 → ℚ) :
    Fin 4 → ℚ :=
  let a := sub3Q (p 0) (p 3)
  let b := sub3Q (p 1) (p 3)
  let c := sub3Q (p 2) (p 3)
  let y := sub3Q target (p 3)
  let D := det3Q a b c
  let l0 := det3Q y b c / D
  let l1 := det3Q a y c / D
  let l2 := det3Q a b y / D
  ![l0, l1, l2, 1 - l0 - l1 - l2]

private theorem tetraBarycentricQ_sum (p : Fin 4 → Fin 3 → ℚ)
    (target : Fin 3 → ℚ) :
    ∑ j, tetraBarycentricQ p target j = 1 := by
  simp [tetraBarycentricQ, Fin.sum_univ_four]

private theorem tetraBarycentricQ_combination (p : Fin 4 → Fin 3 → ℚ)
    (target : Fin 3 → ℚ) (hdet : tetraDetQ p ≠ 0) :
    ∑ j, tetraBarycentricQ p target j • p j = target := by
  simp only [tetraDetQ] at hdet
  funext coordinate
  fin_cases coordinate <;>
    simp [tetraBarycentricQ, Fin.sum_univ_four, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] <;>
    field_simp [hdet] <;>
    simp [det3Q, sub3Q] <;> ring

lemma AxisCertificate.toR3_approxLift (box : Box)
    (cert : AxisCertificate) (i : Fin 3) :
    toR3 (cert.approxLift box i) =
      (RationalApprox.rotMℚℝ (box.center.θ₂ : ℝ)
        (box.center.φ₂ : ℝ)).adjoint
          (toR2 (cert.contact i).direction) := by
  exact toR3_rotMℚ_transpose_mulVec _ _ _

lemma AxisCertificate.toR3_approxA (box : Box)
    (cert : AxisCertificate) :
    toR3 (cert.approxA box) =
      ∑ i, (cert.weight i : ℝ) •
        Noperthedron.BalancedSupport.cross3
          (toR3 (normalizedRationalVertex
            (symmetryAction box.symmetryIndex (cert.contact i).index)))
          ((RationalApprox.rotMℚℝ (box.center.θ₂ : ℝ)
            (box.center.φ₂ : ℝ)).adjoint
              (toR2 (cert.contact i).direction)) := by
  rw [AxisCertificate.approxA, toR3_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [toR3_smul, toR3_crossQ, cert.toR3_approxLift]

def octahedronAxis : Fin 6 → Fin 3 → ℚ := ![
  ![1, 0, 0], ![-1, 0, 0], ![0, 1, 0],
  ![0, -1, 0], ![0, 0, 1], ![0, 0, -1]]

@[simp] lemma octahedronAxis_zero : octahedronAxis 0 = ![1, 0, 0] := by decide
@[simp] lemma octahedronAxis_one : octahedronAxis 1 = ![-1, 0, 0] := by decide
@[simp] lemma octahedronAxis_two : octahedronAxis 2 = ![0, 1, 0] := by decide
@[simp] lemma octahedronAxis_three : octahedronAxis 3 = ![0, -1, 0] := by decide
@[simp] lemma octahedronAxis_four : octahedronAxis 4 = ![0, 0, 1] := by decide
@[simp] lemma octahedronAxis_five : octahedronAxis 5 = ![0, 0, -1] := by decide

def Box.octahedronTarget (box : Box) (k : Fin 6) : Fin 3 → ℚ :=
  (7 / 4 * (box.c + box.axisPerturbation)) • octahedronAxis k

def outerAsInner (p : Pose ℚ) : Pose ℚ where
  θ₁ := p.θ₂
  φ₁ := p.φ₂
  α := 0
  θ₂ := p.θ₂
  φ₂ := p.φ₂

private noncomputable def outerAsInnerReal (p : Pose ℝ) : Pose ℝ where
  θ₁ := p.θ₂
  φ₁ := p.φ₂
  α := 0
  θ₂ := p.θ₂
  φ₂ := p.φ₂

@[simp] private theorem outerAsInner_toReal (p : Pose ℚ) :
    (outerAsInner p).toReal = outerAsInnerReal p.toReal := by
  simp [outerAsInner, outerAsInnerReal, Pose.toReal]

def Contact.supported (box : Box) (contact : Contact) : Prop :=
  let selected := symmetryAction box.symmetryIndex contact.index
  ∀ k : VertexIndex,
    k = selected ∨
      Hℚ box.center box.εθ₂ box.εφ₂ contact.direction
          (normalizedRationalVertex k) ≤
        Gℚ (outerAsInner box.center) 0 box.εθ₂ box.εφ₂
          (normalizedRationalVertex selected) contact.direction

instance (box : Box) (contact : Contact) : Decidable (contact.supported box) := by
  unfold Contact.supported
  infer_instance

def AxisCertificate.balanced (cert : AxisCertificate) : Prop :=
  ∑ i, cert.weight i • (cert.contact i).direction = 0

instance (cert : AxisCertificate) : Decidable cert.balanced := by
  unfold AxisCertificate.balanced
  infer_instance

def Box.barycentric (box : Box) (k : Fin 6) : Fin 4 → ℚ :=
  tetraBarycentricQ box.approxNormalizedA (box.octahedronTarget k)

def Box.barycentricValid (box : Box) : Prop :=
  tetraDetQ box.approxNormalizedA ≠ 0 ∧
    ∀ k j, 0 ≤ box.barycentric k j

instance (box : Box) : Decidable box.barycentricValid := by
  unfold Box.barycentricValid
  infer_instance

/-- The support and axis-cover portion of a local certificate.  These are
exactly the hypotheses used on an equality stratum, where the relative
rotation is controlled separately and the generic Euler mismatch bound is
irrelevant. -/
@[mk_iff]
structure Box.GeometricValid (box : Box) : Prop where
  center_in_four : box.center ∈ fourInterval ℚ
  c_nonneg : 0 ≤ box.c
  direction_unit : ∀ j i, directionUnit ((box.certificate j).contact i).direction
  weight_pos : ∀ j i, 0 < (box.certificate j).weight i
  balanced : ∀ j, (box.certificate j).balanced
  supported : ∀ j i, ((box.certificate j).contact i).supported box
  barycentric : box.barycentricValid

instance (box : Box) : Decidable box.GeometricValid :=
  decidable_of_iff _ (Box.geometricValid_iff box).symm

@[mk_iff]
structure Box.Valid (box : Box) : Prop where
  center_in_four : box.center ∈ fourInterval ℚ
  c_nonneg : 0 ≤ box.c
  r_nonneg : 0 ≤ box.r
  direction_unit : ∀ j i, directionUnit ((box.certificate j).contact i).direction
  weight_pos : ∀ j i, 0 < (box.certificate j).weight i
  balanced : ∀ j, (box.certificate j).balanced
  supported : ∀ j i, ((box.certificate j).contact i).supported box
  barycentric : box.barycentricValid
  mismatch_bound : box.mismatchRadius ≤ box.r
  angle_bound : box.r ^ 2 * (1 + box.c ^ 2) ≤ 4 * box.c ^ 2

instance (box : Box) : Decidable box.Valid :=
  decidable_of_iff _ (Box.valid_iff box).symm

theorem Box.Valid.geometric {box : Box} (h : box.Valid) : box.GeometricValid where
  center_in_four := h.center_in_four
  c_nonneg := h.c_nonneg
  direction_unit := h.direction_unit
  weight_pos := h.weight_pos
  balanced := h.balanced
  supported := h.supported
  barycentric := h.barycentric

def AxisCertificate.realWeight (cert : AxisCertificate) (i : Fin 3) : ℝ :=
  (cert.weight i : ℝ)

noncomputable def AxisCertificate.realDirection
    (cert : AxisCertificate) (i : Fin 3) : ℝ² :=
  toR2 (cert.contact i).direction

noncomputable def AxisCertificate.realVertex
    (box : Box) (cert : AxisCertificate) (i : Fin 3) : ℝ³ :=
  normalizedExactVertex
    (symmetryAction box.symmetryIndex (cert.contact i).index)

lemma AxisCertificate.B_pos (box : Box) (h : box.GeometricValid) (j : Fin 4) :
    0 < (box.certificate j).B := by
  unfold AxisCertificate.B
  apply Finset.sum_pos
  · intro i _
    exact h.weight_pos j i
  · exact Finset.univ_nonempty

lemma AxisCertificate.realWeight_nonneg (box : Box) (h : box.GeometricValid)
    (j : Fin 4) (i : Fin 3) :
    0 ≤ (box.certificate j).realWeight i := by
  change (0 : ℝ) ≤ ((box.certificate j).weight i : ℝ)
  exact_mod_cast (h.weight_pos j i).le

lemma AxisCertificate.realDirection_norm (box : Box) (h : box.GeometricValid)
    (j : Fin 4) (i : Fin 3) :
    ‖(box.certificate j).realDirection i‖ = 1 :=
  direction_norm_eq_one (h.direction_unit j i)

lemma AxisCertificate.real_remainder_le_B (box : Box) (h : box.GeometricValid)
    (j : Fin 4) :
    ∑ i, (box.certificate j).realWeight i *
        (‖(box.certificate j).realDirection i‖ *
          ‖(box.certificate j).realVertex box i‖) ≤
      ((box.certificate j).B : ℝ) := by
  calc
    ∑ i, (box.certificate j).realWeight i *
        (‖(box.certificate j).realDirection i‖ *
          ‖(box.certificate j).realVertex box i‖) ≤
        ∑ i, (box.certificate j).realWeight i := by
      apply Finset.sum_le_sum
      intro i _
      rw [AxisCertificate.realDirection_norm box h j i, one_mul]
      exact mul_le_of_le_one_right
        (AxisCertificate.realWeight_nonneg box h j i)
        (normalizedExactVertex_norm_le_one _)
    _ = ((box.certificate j).B : ℝ) := by
      unfold AxisCertificate.B AxisCertificate.realWeight
      push_cast
      rfl

lemma AxisCertificate.real_balance (box : Box) (h : box.GeometricValid)
    (j : Fin 4) :
    ∑ i, (box.certificate j).realWeight i •
        (box.certificate j).realDirection i = 0 := by
  ext c
  have hb := congrFun (h.balanced j) c
  simp only [AxisCertificate.balanced, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply] at hb
  simp only [AxisCertificate.realWeight, AxisCertificate.realDirection,
    WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero, Finset.sum_apply,
    Pi.smul_apply, Pi.zero_apply, toR2, smul_eq_mul]
  exact_mod_cast hb

lemma AxisCertificate.toR3_approxA_eq_smul (box : Box) (h : box.GeometricValid)
    (j : Fin 4) :
    toR3 ((box.certificate j).approxA box) =
      ((box.certificate j).B : ℝ) •
        toR3 (box.approxNormalizedA j) := by
  ext c
  change (((box.certificate j).approxA box c : ℚ) : ℝ) =
    ((box.certificate j).B : ℝ) *
      ((((box.certificate j).approxA box c /
        (box.certificate j).B : ℚ) : ℝ))
  push_cast
  field_simp [ne_of_gt (AxisCertificate.B_pos box h j)]

/-- The exact normalized first-variation vector associated with a rational
certificate at an arbitrary outer pose. -/
noncomputable def AxisCertificate.normalizedAAt
    (box : Box) (cert : AxisCertificate) (q : Pose ℝ) (offset : ℝ²) : ℝ³ :=
  ((cert.B : ℝ)⁻¹) •
    Noperthedron.SnubCube.firstVariationVector
      (q.matrixPoseWithOffset offset) cert.realWeight cert.realDirection
      (cert.realVertex box)

lemma AxisCertificate.firstVariation_eq_B_smul_normalizedAAt
    (box : Box) (h : box.GeometricValid) (j : Fin 4) (q : Pose ℝ)
    (offset : ℝ²) :
    Noperthedron.SnubCube.firstVariationVector
        (q.matrixPoseWithOffset offset) (box.certificate j).realWeight
        (box.certificate j).realDirection
        ((box.certificate j).realVertex box) =
      ((box.certificate j).B : ℝ) •
        (box.certificate j).normalizedAAt box q offset := by
  rw [AxisCertificate.normalizedAAt, smul_smul]
  simp [ne_of_gt (AxisCertificate.B_pos box h j)]

private lemma halfWidth_nonneg {lo hi : ℚ} (h : lo ≤ hi) :
    0 ≤ (hi - lo) / 2 := div_nonneg (sub_nonneg.mpr h) (by norm_num)

lemma Box.εθ₁_nonneg (box : Box) : 0 ≤ box.εθ₁ :=
  halfWidth_nonneg ((Pose.le_iff _ _).mp box.interval.min_le_max).1

lemma Box.εφ₁_nonneg (box : Box) : 0 ≤ box.εφ₁ :=
  halfWidth_nonneg ((Pose.le_iff _ _).mp box.interval.min_le_max).2.2.1

lemma Box.εθ₂_nonneg (box : Box) : 0 ≤ box.εθ₂ :=
  halfWidth_nonneg ((Pose.le_iff _ _).mp box.interval.min_le_max).2.1

lemma Box.εφ₂_nonneg (box : Box) : 0 ≤ box.εφ₂ :=
  halfWidth_nonneg ((Pose.le_iff _ _).mp box.interval.min_le_max).2.2.2.1

lemma Box.εα_nonneg (box : Box) : 0 ≤ box.εα :=
  halfWidth_nonneg ((Pose.le_iff _ _).mp box.interval.min_le_max).2.2.2.2

lemma centerVectorError_nonneg : 0 ≤ centerVectorError := by
  norm_num [centerVectorError, κℚ]

lemma rotationError_nonneg : 0 ≤ rotationError := by
  norm_num [rotationError, κℚ]

lemma Box.axisPerturbation_nonneg (box : Box) : 0 ≤ box.axisPerturbation := by
  unfold Box.axisPerturbation Box.outerRadius
  exact add_nonneg (add_nonneg box.εφ₂_nonneg box.εθ₂_nonneg)
    centerVectorError_nonneg

private theorem outerAsInner_mem_four {p : Pose ℚ}
    (hp : p ∈ fourInterval ℚ) : outerAsInner p ∈ fourInterval ℚ := by
  obtain ⟨hθ₁, hθ₂, hφ₁, hφ₂, hα⟩ :=
    PoseInterval.contains_iff_components.mp hp
  apply PoseInterval.contains_iff_components.mpr
  simpa [outerAsInner] using
    (show p.θ₂ ∈ Set.Icc (-4 : ℚ) 4 ∧
        p.θ₂ ∈ Set.Icc (-4 : ℚ) 4 ∧
        p.φ₂ ∈ Set.Icc (-4 : ℚ) 4 ∧
        p.φ₂ ∈ Set.Icc (-4 : ℚ) 4 ∧
        (0 : ℚ) ∈ Set.Icc (-4 : ℚ) 4 by
      exact ⟨hθ₂, hθ₂, hφ₂, hφ₂, by norm_num⟩)

private theorem outerAsInnerReal_near {pbar q : Pose ℝ}
    {εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ}
    (hq : Pose.near pbar εα εθ₁ εφ₁ εθ₂ εφ₂ q) :
    Pose.near (outerAsInnerReal pbar) 0 εθ₂ εφ₂ εθ₂ εφ₂
      (outerAsInnerReal q) := by
  obtain ⟨-, -, hθ, hφ, -⟩ := hq
  exact ⟨hθ, hφ, hθ, hφ, by simp [outerAsInnerReal]⟩

private theorem outerAsInnerReal_inner_eq_outer (p : Pose ℝ) :
    Pose.inner (outerAsInnerReal p) = Pose.outer p := rfl

theorem valid_center_mismatch_bound (box : Box) (h : box.Valid) :
    ‖box.centerMismatchCLM‖ ≤
      (sqrtℚUp16 box.mismatchFrobeniusSq : ℝ) +
        2 * (rotationError : ℝ) := by
  obtain ⟨hθ₁q, hθ₂q, hφ₁q, hφ₂q, hαq⟩ :=
    PoseInterval.contains_iff_components.mp h.center_in_four
  have hθ₁ := RationalApprox.cast_Icc4_mem
    ⟨box.center.θ₁, hθ₁q⟩
  have hφ₁ := RationalApprox.cast_Icc4_mem
    ⟨box.center.φ₁, hφ₁q⟩
  have hα := RationalApprox.cast_Icc4_mem
    ⟨box.center.α, hαq⟩
  have hθ₂ := RationalApprox.cast_Icc4_mem
    ⟨box.center.θ₂, hθ₂q⟩
  have hφ₂ := RationalApprox.cast_Icc4_mem
    ⟨box.center.φ₂, hφ₂q⟩
  have hin := rotRMQ_difference_norm_bounded
    box.center.θ₁ box.center.φ₁ box.center.α hθ₁ hφ₁ hα
  have hout := rotRMQ_difference_norm_bounded
    box.center.θ₂ box.center.φ₂ 0 hθ₂ hφ₂ (by norm_num)
  have hdecomp : box.centerMismatchCLM - box.mismatchQCLM =
      (rotRM box.center.toReal.θ₁ box.center.toReal.φ₁ box.center.toReal.α -
        rotRMQCLM box.center.θ₁ box.center.φ₁ box.center.α) -
      (rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0 -
        rotRMQCLM box.center.θ₂ box.center.φ₂ 0) ∘L
          Noperthedron.SnubCube.so3CLM (symmetry box.symmetryIndex) := by
    rw [box.mismatchQCLM_eq]
    ext v
    simp [Box.centerMismatchCLM]
    ring
  have hdiff : ‖box.centerMismatchCLM - box.mismatchQCLM‖ ≤
      2 * (rotationError : ℝ) := by
    have hout' :
        ‖rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0 -
          rotRMQCLM box.center.θ₂ box.center.φ₂ 0‖ ≤
            (rotationError : ℝ) := by simpa using hout
    rw [hdecomp]
    calc
      ‖(rotRM box.center.toReal.θ₁ box.center.toReal.φ₁ box.center.toReal.α -
          rotRMQCLM box.center.θ₁ box.center.φ₁ box.center.α) -
        (rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0 -
          rotRMQCLM box.center.θ₂ box.center.φ₂ 0) ∘L
            Noperthedron.SnubCube.so3CLM (symmetry box.symmetryIndex)‖ ≤
        ‖rotRM box.center.toReal.θ₁ box.center.toReal.φ₁ box.center.toReal.α -
          rotRMQCLM box.center.θ₁ box.center.φ₁ box.center.α‖ +
        ‖(rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0 -
          rotRMQCLM box.center.θ₂ box.center.φ₂ 0) ∘L
            Noperthedron.SnubCube.so3CLM (symmetry box.symmetryIndex)‖ :=
          norm_sub_le _ _
      _ ≤ (rotationError : ℝ) + (rotationError : ℝ) * 1 := by
        apply add_le_add hin
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hout'
            (le_of_eq (Noperthedron.SnubCube.so3CLM_norm _))
            (norm_nonneg _) (by exact_mod_cast rotationError_nonneg))
      _ = 2 * (rotationError : ℝ) := by ring
  calc
    ‖box.centerMismatchCLM‖ =
        ‖box.mismatchQCLM +
          (box.centerMismatchCLM - box.mismatchQCLM)‖ := by congr 1 <;> abel
    _ ≤ ‖box.mismatchQCLM‖ +
        ‖box.centerMismatchCLM - box.mismatchQCLM‖ := norm_add_le _ _
    _ ≤ (sqrtℚUp16 box.mismatchFrobeniusSq : ℝ) +
        2 * (rotationError : ℝ) :=
      add_le_add box.mismatchQCLM_norm_le_sqrt hdiff

private theorem poseMismatch_eq (q : Pose ℝ) (offset : ℝ²)
    (g : VertexIndex) :
    Noperthedron.SnubCube.so3CLM (q.matrixPoseWithOffset offset).innerRot -
        Noperthedron.SnubCube.so3CLM
          ((q.matrixPoseWithOffset offset).outerRot * symmetry g) =
      rotRM q.θ₁ q.φ₁ q.α -
        rotRM q.θ₂ q.φ₂ 0 ∘L
          Noperthedron.SnubCube.so3CLM (symmetry g) := by
  rw [Noperthedron.SnubCube.so3CLM_mul]
  simp only [Pose.matrixPoseWithOffset, Pose.matrixPoseOfPose,
    Noperthedron.SnubCube.so3CLM]
  rw [← rotRM_eq_rotRM_mat, ← rotRM_eq_rotRM_mat]

theorem valid_mismatch_bound (box : Box) (h : box.Valid)
    {q : Pose ℝ}
    (hq : Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q)
    (offset : ℝ²) :
    ‖Noperthedron.SnubCube.so3CLM
          (q.matrixPoseWithOffset offset).innerRot -
        Noperthedron.SnubCube.so3CLM
          ((q.matrixPoseWithOffset offset).outerRot *
            symmetry box.symmetryIndex)‖ ≤ (box.r : ℝ) := by
  rw [poseMismatch_eq]
  let current : ℝ³ →L[ℝ] ℝ³ :=
    rotRM q.θ₁ q.φ₁ q.α - rotRM q.θ₂ q.φ₂ 0 ∘L
      Noperthedron.SnubCube.so3CLM (symmetry box.symmetryIndex)
  have hin := Noperthedron.BalancedSupport.norm_rotRM_sub_le
    q.θ₁ q.φ₁ q.α box.center.toReal.θ₁ box.center.toReal.φ₁
      box.center.toReal.α
  have hout := Noperthedron.BalancedSupport.norm_rotRM_sub_le
    q.θ₂ q.φ₂ 0 box.center.toReal.θ₂ box.center.toReal.φ₂ 0
  norm_num at hout
  have hdecomp : current - box.centerMismatchCLM =
      (rotRM q.θ₁ q.φ₁ q.α -
        rotRM box.center.toReal.θ₁ box.center.toReal.φ₁ box.center.toReal.α) -
      (rotRM q.θ₂ q.φ₂ 0 -
        rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0) ∘L
          Noperthedron.SnubCube.so3CLM (symmetry box.symmetryIndex) := by
    ext v
    simp [current, Box.centerMismatchCLM]
    ring
  have hdiff : ‖current - box.centerMismatchCLM‖ ≤
      (box.eulerRadius : ℝ) := by
    rw [hdecomp]
    calc
      ‖(rotRM q.θ₁ q.φ₁ q.α -
          rotRM box.center.toReal.θ₁ box.center.toReal.φ₁ box.center.toReal.α) -
        (rotRM q.θ₂ q.φ₂ 0 -
          rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0) ∘L
            Noperthedron.SnubCube.so3CLM (symmetry box.symmetryIndex)‖ ≤
        ‖rotRM q.θ₁ q.φ₁ q.α -
          rotRM box.center.toReal.θ₁ box.center.toReal.φ₁ box.center.toReal.α‖ +
        ‖(rotRM q.θ₂ q.φ₂ 0 -
          rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0) ∘L
            Noperthedron.SnubCube.so3CLM (symmetry box.symmetryIndex)‖ :=
        norm_sub_le _ _
      _ ≤ (|q.α - box.center.toReal.α| +
          |q.φ₁ - box.center.toReal.φ₁| +
          |q.θ₁ - box.center.toReal.θ₁|) +
        (|q.φ₂ - box.center.toReal.φ₂| +
          |q.θ₂ - box.center.toReal.θ₂|) := by
        apply add_le_add hin
        calc
          ‖(rotRM q.θ₂ q.φ₂ 0 -
              rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0) ∘L
                Noperthedron.SnubCube.so3CLM (symmetry box.symmetryIndex)‖ ≤
            ‖rotRM q.θ₂ q.φ₂ 0 -
              rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0‖ *
                ‖Noperthedron.SnubCube.so3CLM
                  (symmetry box.symmetryIndex)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ = ‖rotRM q.θ₂ q.φ₂ 0 -
              rotRM box.center.toReal.θ₂ box.center.toReal.φ₂ 0‖ := by
            rw [Noperthedron.SnubCube.so3CLM_norm, mul_one]
          _ ≤ |q.φ₂ - box.center.toReal.φ₂| +
              |q.θ₂ - box.center.toReal.θ₂| := by
            simpa using hout
      _ ≤ (box.eulerRadius : ℝ) := by
        rw [show (box.eulerRadius : ℝ) =
          (box.εα : ℝ) + (box.εφ₁ : ℝ) + (box.εθ₁ : ℝ) +
            (box.εφ₂ : ℝ) + (box.εθ₂ : ℝ) by
          simp [Box.eulerRadius]]
        linarith [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1,
          hq.2.2.2.2]
  have hcenter := valid_center_mismatch_bound box h
  have hcurrent : ‖current‖ ≤
      (sqrtℚUp16 box.mismatchFrobeniusSq : ℝ) +
        2 * (rotationError : ℝ) + (box.eulerRadius : ℝ) := by
    calc
      ‖current‖ = ‖box.centerMismatchCLM +
          (current - box.centerMismatchCLM)‖ := by congr 1 <;> abel
      _ ≤ ‖box.centerMismatchCLM‖ +
          ‖current - box.centerMismatchCLM‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hcenter hdiff
  change ‖current‖ ≤ (box.r : ℝ)
  exact hcurrent.trans (by
    exact_mod_cast h.mismatch_bound)

theorem valid_axisAngle_ratio (box : Box) (h : box.Valid)
    {q : Pose ℝ}
    (hq : Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q)
    (offset : ℝ²)
    (a : Noperthedron.BalancedSupport.AxisAngle
      (Noperthedron.SnubCube.so3CLM
        (Noperthedron.SnubCube.relativeRotationAtSymmetry
          (q.matrixPoseWithOffset offset) box.symmetryIndex))) :
    1 - Real.cos a.angle ≤ |Real.sin a.angle| * (box.c : ℝ) := by
  apply Noperthedron.SnubCube.AxisAngle.ratio_of_inner_mismatch_bound
    (q.matrixPoseWithOffset offset) box.symmetryIndex a
    (box.c : ℝ) (box.r : ℝ)
  · exact_mod_cast h.c_nonneg
  · exact_mod_cast h.r_nonneg
  · exact valid_mismatch_bound box h hq offset
  · exact_mod_cast h.angle_bound

/-- The rational first-variation vector in a valid row approximates the
exact normalized vector at the box center with the universal `2κ + κ²`
error budget. -/
theorem valid_center_normalizedA_approx (box : Box) (h : box.GeometricValid)
    (j : Fin 4) :
    ‖(box.certificate j).normalizedAAt box box.center.toReal 0 -
        toR3 (box.approxNormalizedA j)‖ ≤
      ((centerVectorError : ℚ) : ℝ) := by
  let cert := box.certificate j
  let approxVertex : Fin 3 → ℝ³ := fun i =>
    toR3 (normalizedRationalVertex
      (symmetryAction box.symmetryIndex (cert.contact i).index))
  let exactLift : Fin 3 → ℝ³ := fun i =>
    Noperthedron.SnubCube.outerLift
      (box.center.toReal.matrixPoseWithOffset 0) (cert.realDirection i)
  let approxLift : Fin 3 → ℝ³ := fun i => toR3 (cert.approxLift box i)
  have hbound := Noperthedron.SnubCube.norm_normalizedWeightedCross_approx_sub_le
    cert.realWeight (cert.realVertex box) approxVertex exactLift approxLift
    (cert.normalizedAAt box box.center.toReal 0)
    (toR3 (box.approxNormalizedA j)) (cert.B : ℝ) RationalApprox.κ
    (by unfold RationalApprox.κ; norm_num)
    (fun i => by
      change (0 : ℝ) ≤ (cert.weight i : ℝ)
      exact_mod_cast (h.weight_pos j i).le)
    (by exact_mod_cast AxisCertificate.B_pos box h j)
    (by
      unfold AxisCertificate.B AxisCertificate.realWeight
      push_cast
      rfl)
    (fun i => normalizedExactVertex_norm_le_one _)
    (fun i => by
      have happ := normalizedApproximation.approx
        (symmetryAction box.symmetryIndex (cert.contact i).index)
      change ‖normalizedExactVertex
          (symmetryAction box.symmetryIndex (cert.contact i).index) -
        toR3 (normalizedRationalVertex
          (symmetryAction box.symmetryIndex (cert.contact i).index))‖ ≤
            RationalApprox.κ at happ
      simpa [AxisCertificate.realVertex, approxVertex] using happ)
    (fun i => by
      have hlift := norm_outerLift_rationalApprox_sub_le box.center
        h.center_in_four (0 : ℝ²) (cert.realDirection i)
        (direction_norm_eq_one (h.direction_unit j i))
      simpa [exactLift, approxLift, AxisCertificate.realDirection,
        cert.toR3_approxLift] using hlift)
    (fun i => by
      have hlift := norm_rationalApprox_outerLift_le box.center
        h.center_in_four (cert.realDirection i)
        (direction_norm_eq_one (h.direction_unit j i))
      simpa [approxLift, AxisCertificate.realDirection,
        cert.toR3_approxLift] using hlift)
    (by
      simpa [Noperthedron.SnubCube.firstVariationVector, exactLift,
        AxisCertificate.realWeight, AxisCertificate.realDirection,
        AxisCertificate.realVertex, cert] using
          (AxisCertificate.firstVariation_eq_B_smul_normalizedAAt
            box h j box.center.toReal (0 : ℝ²)))
    (by
      dsimp [AxisCertificate.realWeight, approxVertex, approxLift]
      simp_rw [cert.toR3_approxLift]
      rw [← cert.toR3_approxA box]
      exact AxisCertificate.toR3_approxA_eq_smul box h j)
  calc
    ‖(box.certificate j).normalizedAAt box box.center.toReal 0 -
        toR3 (box.approxNormalizedA j)‖ ≤
        2 * RationalApprox.κ + RationalApprox.κ ^ 2 := by
      simpa [cert] using hbound
    _ = ((centerVectorError : ℚ) : ℝ) := by
      norm_num [centerVectorError, RationalApprox.κ, RationalApprox.κℚ]

/-- Throughout the box, each exact normalized first-variation vector stays
within the rational row's declared perturbation budget. -/
theorem valid_normalizedA_move (box : Box) (h : box.GeometricValid)
    {q : Pose ℝ}
    (hq : Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q)
    (offset : ℝ²) (j : Fin 4) :
    ‖(box.certificate j).normalizedAAt box q offset -
        toR3 (box.approxNormalizedA j)‖ ≤
      ((box.axisPerturbation : ℚ) : ℝ) := by
  let cert := box.certificate j
  have hweight : ∀ i, 0 ≤ cert.realWeight i := by
    intro i
    change (0 : ℝ) ≤ (cert.weight i : ℝ)
    exact_mod_cast (h.weight_pos j i).le
  have hbudget :
      ∑ i, cert.realWeight i *
          (‖cert.realDirection i‖ * ‖cert.realVertex box i‖) ≤
        (cert.B : ℝ) := by
    calc
      ∑ i, cert.realWeight i *
          (‖cert.realDirection i‖ * ‖cert.realVertex box i‖) ≤
          ∑ i, cert.realWeight i := by
        apply Finset.sum_le_sum
        intro i _
        rw [show ‖cert.realDirection i‖ = 1 by
          exact direction_norm_eq_one (h.direction_unit j i), one_mul]
        exact mul_le_of_le_one_right (hweight i)
          (normalizedExactVertex_norm_le_one _)
      _ = (cert.B : ℝ) := by
        unfold AxisCertificate.B AxisCertificate.realWeight
        push_cast
        rfl
  have hcenterMove :=
    Noperthedron.SnubCube.norm_normalizedFirstVariation_matrixPoseWithOffset_sub_le_of_budget_bound
      q box.center.toReal offset 0 cert.realWeight cert.realDirection
      (cert.realVertex box) (cert.normalizedAAt box q offset)
      (cert.normalizedAAt box box.center.toReal 0) (cert.B : ℝ)
      hweight (by exact_mod_cast AxisCertificate.B_pos box h j) hbudget
      (AxisCertificate.firstVariation_eq_B_smul_normalizedAAt box h j q offset)
      (AxisCertificate.firstVariation_eq_B_smul_normalizedAAt
        box h j box.center.toReal 0)
  have hcenterMove' :
      ‖cert.normalizedAAt box q offset -
          cert.normalizedAAt box box.center.toReal 0‖ ≤
        (box.outerRadius : ℝ) := by
    apply hcenterMove.trans
    rw [show (box.outerRadius : ℝ) =
      (box.εφ₂ : ℝ) + (box.εθ₂ : ℝ) by simp [Box.outerRadius]]
    exact add_le_add hq.2.2.2.1 hq.2.2.1
  have happrox := valid_center_normalizedA_approx box h j
  calc
    ‖(box.certificate j).normalizedAAt box q offset -
        toR3 (box.approxNormalizedA j)‖ ≤
      ‖cert.normalizedAAt box q offset -
          cert.normalizedAAt box box.center.toReal 0‖ +
        ‖cert.normalizedAAt box box.center.toReal 0 -
          toR3 (box.approxNormalizedA j)‖ := by
      dsimp [cert]
      rw [show (box.certificate j).normalizedAAt box q offset -
          toR3 (box.approxNormalizedA j) =
        ((box.certificate j).normalizedAAt box q offset -
            (box.certificate j).normalizedAAt box box.center.toReal 0) +
          ((box.certificate j).normalizedAAt box box.center.toReal 0 -
            toR3 (box.approxNormalizedA j)) by abel]
      exact norm_add_le _ _
    _ ≤ (box.outerRadius : ℝ) + (centerVectorError : ℝ) :=
      add_le_add hcenterMove' happrox
    _ = ((box.axisPerturbation : ℚ) : ℝ) := by
      simp [Box.axisPerturbation]

/-- A checked contact remains an exact supporting outer vertex throughout
its outer-view box.  This is the semantic bridge from the rational Taylor
inequality stored in a row to the support hypothesis of local rigidity. -/
theorem contact_support_pose (box : Box) (contact : Contact)
    (hcenter : box.center ∈ fourInterval ℚ)
    (hdirection : directionUnit contact.direction)
    (hsupported : contact.supported box)
    {q : Pose ℝ}
    (hq : Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q)
    (k : VertexIndex) :
    ⟪toR2 contact.direction,
        q.outer (normalizedExactVertex k)⟫ ≤
      ⟪toR2 contact.direction,
        q.outer (normalizedExactVertex
          (symmetryAction box.symmetryIndex
            contact.index))⟫ := by
  let selected := symmetryAction box.symmetryIndex contact.index
  let qouter := outerAsInnerReal q
  let pbar := (outerAsInner box.center).toReal
  let pc : _root_.GlobalTheorem.GlobalContact normalizedGoodPoly pbar
      (0 : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) := {
    Si := selected
    w := toR2 contact.direction
    w_unit := direction_norm_eq_one hdirection
  }
  have hnear : Pose.near pbar 0 (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) qouter := by
    dsimp [pbar, qouter]
    rw [outerAsInner_toReal]
    exact outerAsInnerReal_near hq
  by_cases hk : k = selected
  · subst k
    exact le_rfl
  have houter := _root_.GlobalTheorem.global_theorem_outer_le_H
    pbar qouter (0 : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (by exact_mod_cast box.εθ₂_nonneg)
      (by exact_mod_cast box.εφ₂_nonneg) hnear normalizedGoodPoly pc k
  have hH :
      _root_.GlobalTheorem.H pbar (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
          pc.w (normalizedExactVertex k) ≤
        ((Hℚ box.center box.εθ₂ box.εφ₂ contact.direction
          (normalizedRationalVertex k) : ℚ) : ℝ) := by
    change _root_.GlobalTheorem.H box.center.toReal
        (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) (toR2 contact.direction)
          (normalizedExactVertex k) ≤ _
    exact H_le_Hℚ box.εθ₂_nonneg box.εφ₂_nonneg
      (normalizedExactVertex_norm_le_one k)
      (normalizedApproximation.approx k)
      (direction_norm_eq_one hdirection) hcenter
  have hchecked :
      ((Hℚ box.center box.εθ₂ box.εφ₂ contact.direction
          (normalizedRationalVertex k) : ℚ) : ℝ) ≤
        ((Gℚ (outerAsInner box.center) 0 box.εθ₂ box.εφ₂
          (normalizedRationalVertex selected) contact.direction : ℚ) : ℝ) := by
    exact_mod_cast hsupported k |>.resolve_left (by
      simpa [selected] using hk)
  have hG :
      ((Gℚ (outerAsInner box.center) 0 box.εθ₂ box.εφ₂
          (normalizedRationalVertex selected) contact.direction : ℚ) : ℝ) ≤
        _root_.GlobalTheorem.G pbar 0 (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
          (normalizedExactVertex selected) (toR2 contact.direction) := by
    simpa [pbar, normalizedApproximation,
      normalizedRationalPolyhedron] using
      (Gℚ_le_G (p_ := outerAsInner box.center) (εα := (0 : ℚ))
        (εθ := box.εθ₂) (εφ := box.εφ₂)
        (by norm_num) box.εθ₂_nonneg box.εφ₂_nonneg
        (normalizedExactVertex_norm_le_one selected)
        (normalizedApproximation.approx selected)
        (direction_norm_eq_one hdirection)
        (outerAsInner_mem_four hcenter))
  have hinner := _root_.GlobalTheorem.global_theorem_inequality_ii
    pbar qouter (0 : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (by norm_num) (by exact_mod_cast box.εθ₂_nonneg)
      (by exact_mod_cast box.εφ₂_nonneg) hnear normalizedGoodPoly pc
  simp only [_root_.GlobalTheorem.GlobalContact.S,
    _root_.GlobalTheorem.GlobalContact.Sval] at hinner
  dsimp [pc] at houter hinner
  dsimp [qouter] at houter hinner
  rw [outerAsInnerReal_inner_eq_outer] at hinner
  dsimp [qouter, selected, pbar] at houter hH hchecked hG hinner ⊢
  exact houter.trans (hH.trans (hchecked.trans (hG.trans hinner)))

theorem contact_support_matrixPose (box : Box) (contact : Contact)
    (hcenter : box.center ∈ fourInterval ℚ)
    (hdirection : directionUnit contact.direction)
    (hsupported : contact.supported box)
    {q : Pose ℝ}
    (hq : Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q)
    (offset : ℝ²) (k : VertexIndex) :
    ⟪toR2 contact.direction,
        Noperthedron.BalancedSupport.outerProjectionLinear
          (q.matrixPoseWithOffset offset) (normalizedExactVertex k)⟫ ≤
      ⟪toR2 contact.direction,
        Noperthedron.BalancedSupport.outerProjectionLinear
          (q.matrixPoseWithOffset offset)
          (normalizedExactVertex
            (symmetryAction box.symmetryIndex
              contact.index))⟫ := by
  simpa [Noperthedron.BalancedSupport.outerProjectionLinear,
    Noperthedron.BalancedSupport.matrixPoseWithOffset_outer_rotation_project] using
    contact_support_pose box contact hcenter hdirection hsupported hq k

theorem valid_contact_support_pose (box : Box) (h : box.GeometricValid)
    {q : Pose ℝ}
    (hq : Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q)
    (j : Fin 4) (i : Fin 3) (k : VertexIndex) :
    ⟪toR2 ((box.certificate j).contact i).direction,
        q.outer (normalizedExactVertex k)⟫ ≤
      ⟪toR2 ((box.certificate j).contact i).direction,
        q.outer (normalizedExactVertex
          (symmetryAction box.symmetryIndex
            ((box.certificate j).contact i).index))⟫ :=
  contact_support_pose box ((box.certificate j).contact i)
    h.center_in_four (h.direction_unit j i) (h.supported j i) hq k

theorem valid_contact_support_matrixPose (box : Box) (h : box.GeometricValid)
    {q : Pose ℝ}
    (hq : Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q)
    (offset : ℝ²) (j : Fin 4) (i : Fin 3) (k : VertexIndex) :
    ⟪toR2 ((box.certificate j).contact i).direction,
        Noperthedron.BalancedSupport.outerProjectionLinear
          (q.matrixPoseWithOffset offset) (normalizedExactVertex k)⟫ ≤
      ⟪toR2 ((box.certificate j).contact i).direction,
        Noperthedron.BalancedSupport.outerProjectionLinear
          (q.matrixPoseWithOffset offset)
          (normalizedExactVertex
            (symmetryAction box.symmetryIndex
              ((box.certificate j).contact i).index))⟫ :=
  contact_support_matrixPose box ((box.certificate j).contact i)
    h.center_in_four (h.direction_unit j i) (h.supported j i) hq offset k

private theorem barycentric_mem_convexHull (box : Box)
    (h : box.GeometricValid) (k : Fin 6) :
    toR3 (box.octahedronTarget k) ∈
      convexHull ℝ {toR3 (box.approxNormalizedA j) | j} := by
  apply Noperthedron.BalancedSupport.mem_convexHull_of_barycentric
    (fun j => toR3 (box.approxNormalizedA j))
    (fun j => (box.barycentric k j : ℝ))
  · intro j
    exact_mod_cast h.barycentric.2 k j
  · exact_mod_cast tetraBarycentricQ_sum
      box.approxNormalizedA (box.octahedronTarget k)
  · ext coordinate
    have hcoordinate := congrFun
      (tetraBarycentricQ_combination box.approxNormalizedA
        (box.octahedronTarget k) h.barycentric.1) coordinate
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toR3,
      WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_toLp]
    exact_mod_cast hcoordinate

/-- The six checked rational barycentric identities imply the real center
axis-cover property required by the perturbation theorem. -/
theorem valid_center_axis_cover (box : Box) (h : box.GeometricValid)
    (axis : ℝ³) (haxis : ‖axis‖ = 1) :
    ∃ j, ((box.c + box.axisPerturbation : ℚ) : ℝ) ≤
      ⟪axis, toR3 (box.approxNormalizedA j)⟫ := by
  apply Noperthedron.BalancedSupport.octahedral_axis_cover
    (fun j => toR3 (box.approxNormalizedA j))
    ((box.c + box.axisPerturbation : ℚ) : ℝ)
  · exact_mod_cast add_nonneg h.c_nonneg box.axisPerturbation_nonneg
  · have heq : toR3 (box.octahedronTarget 0) =
        (7 / 4 * (((box.c + box.axisPerturbation : ℚ) : ℝ))) •
          Noperthedron.BalancedSupport.xAxis3 := by
      rw [Box.octahedronTarget, octahedronAxis_zero]
      ext i
      fin_cases i <;> norm_num [Noperthedron.BalancedSupport.xAxis3, toR3]
    rw [← heq]
    exact barycentric_mem_convexHull box h 0
  · have heq : toR3 (box.octahedronTarget 1) =
        (- (7 / 4 * (((box.c + box.axisPerturbation : ℚ) : ℝ)))) •
          Noperthedron.BalancedSupport.xAxis3 := by
      rw [Box.octahedronTarget, octahedronAxis_one]
      ext i
      fin_cases i <;> norm_num [Noperthedron.BalancedSupport.xAxis3, toR3]
    rw [← heq]
    exact barycentric_mem_convexHull box h 1
  · have heq : toR3 (box.octahedronTarget 2) =
        (7 / 4 * (((box.c + box.axisPerturbation : ℚ) : ℝ))) •
          Noperthedron.BalancedSupport.yAxis3 := by
      rw [Box.octahedronTarget, octahedronAxis_two]
      ext i
      fin_cases i <;> norm_num [Noperthedron.BalancedSupport.yAxis3, toR3]
    rw [← heq]
    exact barycentric_mem_convexHull box h 2
  · have heq : toR3 (box.octahedronTarget 3) =
        (- (7 / 4 * (((box.c + box.axisPerturbation : ℚ) : ℝ)))) •
          Noperthedron.BalancedSupport.yAxis3 := by
      rw [Box.octahedronTarget, octahedronAxis_three]
      ext i
      fin_cases i <;> norm_num [Noperthedron.BalancedSupport.yAxis3, toR3]
    rw [← heq]
    exact barycentric_mem_convexHull box h 3
  · have heq : toR3 (box.octahedronTarget 4) =
        (7 / 4 * (((box.c + box.axisPerturbation : ℚ) : ℝ))) •
          Noperthedron.BalancedSupport.zAxis3 := by
      rw [Box.octahedronTarget, octahedronAxis_four]
      ext i
      fin_cases i <;> norm_num [Noperthedron.BalancedSupport.zAxis3, toR3]
    rw [← heq]
    exact barycentric_mem_convexHull box h 4
  · have heq : toR3 (box.octahedronTarget 5) =
        (- (7 / 4 * (((box.c + box.axisPerturbation : ℚ) : ℝ)))) •
          Noperthedron.BalancedSupport.zAxis3 := by
      rw [Box.octahedronTarget, octahedronAxis_five]
      ext i
      fin_cases i <;> norm_num [Noperthedron.BalancedSupport.zAxis3, toR3]
    rw [← heq]
    exact barycentric_mem_convexHull box h 5
  · exact haxis

/-- A valid rational local row rules out every translated pose in its
five-dimensional Euler box. -/
theorem valid_imp_not_translated_rupert (box : Box) (h : box.Valid) :
    ∀ q, Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
        (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q →
      ∀ offset : ℝ²,
        ¬ RupertPose (q.matrixPoseWithOffset offset)
          normalizedExactPolyhedron.hull := by
  intro q hq offset
  let hg := h.geometric
  let relative := Noperthedron.SnubCube.relativeRotationAtSymmetry
    (q.matrixPoseWithOffset offset) box.symmetryIndex
  obtain ⟨a⟩ := Noperthedron.BalancedSupport.exists_axisAngle
    relative.val relative.property
  apply
    Noperthedron.SnubCube.not_rupertPose_of_axisFree_geometric_certificates_of_cover_perturbation
      (p := q.matrixPoseWithOffset offset)
      (g := box.symmetryIndex) (a := a)
      (index := fun j i => (box.certificate j).contact i |>.index)
      (weight := fun j => (box.certificate j).realWeight)
      (direction := fun j => (box.certificate j).realDirection)
      (A := fun j => Noperthedron.SnubCube.firstVariationVector
        (q.matrixPoseWithOffset offset) (box.certificate j).realWeight
        (box.certificate j).realDirection
        (AxisCertificate.realVertex box (box.certificate j)))
      (normalizedA := fun j =>
        (box.certificate j).normalizedAAt box q offset)
      (centerNormalizedA := fun j => toR3 (box.approxNormalizedA j))
      (B := fun j => ((box.certificate j).B : ℝ))
      (c := (box.c : ℝ)) (δ := (box.axisPerturbation : ℝ))
  · intro j
    exact_mod_cast AxisCertificate.B_pos box hg j
  · intro j
    exact AxisCertificate.firstVariation_eq_B_smul_normalizedAAt box hg j q offset
  · intro axis haxis
    simpa only [Rat.cast_add] using valid_center_axis_cover box hg axis haxis
  · exact valid_normalizedA_move box hg hq offset
  · intro j
    rfl
  · exact AxisCertificate.real_remainder_le_B box hg
  · exact valid_axisAngle_ratio box h hq offset a
  · intro j i hdirection
    have hnorm := AxisCertificate.realDirection_norm box hg j i
    rw [hdirection, norm_zero] at hnorm
    norm_num at hnorm
  · exact AxisCertificate.realWeight_nonneg box hg
  · intro j
    refine ⟨0, ?_⟩
    change (0 : ℝ) < ((box.certificate j).weight 0 : ℝ)
    exact_mod_cast h.weight_pos j 0
  · exact AxisCertificate.real_balance box hg
  · exact valid_contact_support_matrixPose box hg hq offset

def Box.realInterval (box : Box) : PoseInterval ℝ :=
  PoseInterval.mk box.interval.min.toReal box.interval.max.toReal (by
    obtain ⟨h1, h2, h3, h4, h5⟩ := (Pose.le_iff _ _).mp box.interval.min_le_max
    rw [Pose.le_iff]
    simp only [Pose.toReal_θ₁, Pose.toReal_θ₂, Pose.toReal_φ₁,
      Pose.toReal_φ₂, Pose.toReal_α]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3,
      by exact_mod_cast h4, by exact_mod_cast h5⟩)

theorem Box.near_center_of_mem_realInterval (box : Box) {q : Pose ℝ}
    (hq : q ∈ box.realInterval) :
    Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q := by
  rw [NonemptyInterval.mem_def] at hq
  obtain ⟨hlo, hhi⟩ := hq
  rw [Pose.le_iff] at hlo hhi
  obtain ⟨l1, l2, l3, l4, l5⟩ := hlo
  obtain ⟨u1, u2, u3, u4, u5⟩ := hhi
  simp only [Box.realInterval, PoseInterval.mk, PoseInterval.min, PoseInterval.max,
    Pose.toReal_θ₁, Pose.toReal_θ₂, Pose.toReal_φ₁, Pose.toReal_φ₂,
    Pose.toReal_α] at l1 l2 l3 l4 l5 u1 u2 u3 u4 u5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [Box.center, Pose.toReal_θ₁, Pose.toReal_θ₂,
      Pose.toReal_φ₁, Pose.toReal_φ₂, Pose.toReal_α,
      Box.εθ₁, Box.εφ₁, Box.εθ₂, Box.εφ₂, Box.εα]
    rw [abs_sub_le_iff]
    push_cast
    constructor <;> linarith

/-- Interval form consumed by the local/global solution-tree induction. -/
theorem valid_imp_no_translated_rupert_in_interval (box : Box) (h : box.Valid) :
    ¬ ∃ q ∈ box.realInterval, ∃ offset : ℝ²,
      RupertPose (q.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull := by
  rintro ⟨q, hq, offset, hrupert⟩
  exact valid_imp_not_translated_rupert box h q
    (box.near_center_of_mem_realInterval hq) offset hrupert

end Noperthedron.SnubCube.LocalCertificate

end
