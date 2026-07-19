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
  barycentric : Fin 6 → Fin 4 → ℚ
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

def rotRMQ (theta phi alpha : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  rzQ alpha * frameQ theta phi

def symmetryMatrixQ (g : VertexIndex) : Matrix (Fin 3) (Fin 3) ℚ :=
  (symmetryMatrixInt g).map fun z => (z : ℚ)

def Box.mismatchMatrix (box : Box) : Matrix (Fin 3) (Fin 3) ℚ :=
  rotRMQ box.center.θ₁ box.center.φ₁ box.center.α -
    rotRMQ box.center.θ₂ box.center.φ₂ 0 * symmetryMatrixQ box.symmetryIndex

def Box.mismatchFrobeniusSq (box : Box) : ℚ :=
  ∑ i, ∑ j, box.mismatchMatrix i j ^ 2

/-- Conservative full-rotation approximation error. -/
def rotationError : ℚ := 3 * κℚ + κℚ ^ 2

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
  maxHℚ box.center normalizedRationalPolyhedron box.εθ₂ box.εφ₂
      contact.direction ≤
    Gℚ (outerAsInner box.center) 0 box.εθ₂ box.εφ₂
      (normalizedRationalVertex
        (symmetryAction box.symmetryIndex contact.index)) contact.direction

instance (box : Box) (contact : Contact) : Decidable (contact.supported box) := by
  unfold Contact.supported
  infer_instance

def AxisCertificate.balanced (cert : AxisCertificate) : Prop :=
  ∑ i, cert.weight i • (cert.contact i).direction = 0

instance (cert : AxisCertificate) : Decidable cert.balanced := by
  unfold AxisCertificate.balanced
  infer_instance

def Box.barycentricValid (box : Box) : Prop :=
  ∀ k,
    (∀ j, 0 ≤ box.barycentric k j) ∧
    ∑ j, box.barycentric k j = 1 ∧
    ∑ j, box.barycentric k j • box.approxNormalizedA j = box.octahedronTarget k

instance (box : Box) : Decidable box.barycentricValid := by
  unfold Box.barycentricValid
  infer_instance

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

/-- A checked contact remains an exact supporting outer vertex throughout
its outer-view box.  This is the semantic bridge from the rational Taylor
inequality stored in a row to the support hypothesis of local rigidity. -/
theorem valid_contact_support_pose (box : Box) (h : box.Valid)
    {q : Pose ℝ}
    (hq : Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q)
    (j : Fin 4) (i : Fin 3) (k : VertexIndex) :
    ⟪toR2 ((box.certificate j).contact i).direction,
        q.outer (normalizedExactVertex k)⟫ ≤
      ⟪toR2 ((box.certificate j).contact i).direction,
        q.outer (normalizedExactVertex
          (symmetryAction box.symmetryIndex
            ((box.certificate j).contact i).index))⟫ := by
  let contact := (box.certificate j).contact i
  let selected := symmetryAction box.symmetryIndex contact.index
  let qouter := outerAsInnerReal q
  let pbar := (outerAsInner box.center).toReal
  let pc : _root_.GlobalTheorem.GlobalContact normalizedGoodPoly pbar
      (0 : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) := {
    Si := selected
    w := toR2 contact.direction
    w_unit := direction_norm_eq_one (h.direction_unit j i)
  }
  have hnear : Pose.near pbar 0 (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) qouter := by
    dsimp [pbar, qouter]
    rw [outerAsInner_toReal]
    exact outerAsInnerReal_near hq
  have hpoint :
      ⟪pc.w, qouter.outer (normalizedExactVertex k)⟫ ≤
        _root_.GlobalTheorem.maxOuter qouter normalizedGoodPoly pc.w := by
    unfold _root_.GlobalTheorem.maxOuter _root_.GlobalTheorem.imgOuter
    apply Finset.le_max'
    simp only [Finset.mem_image]
    exact ⟨normalizedExactVertex k,
      ⟨k, Finset.mem_univ k, rfl⟩, rfl⟩
  have houter := _root_.GlobalTheorem.global_theorem_inequality_iv
    pbar qouter (0 : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (by exact_mod_cast box.εθ₂_nonneg)
      (by exact_mod_cast box.εφ₂_nonneg) hnear normalizedGoodPoly pc
  have hmax :
      _root_.GlobalTheorem.maxH pbar normalizedGoodPoly
          (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) pc.w ≤
        ((maxHℚ box.center normalizedRationalPolyhedron
          box.εθ₂ box.εφ₂ contact.direction : ℚ) : ℝ) := by
    change _root_.GlobalTheorem.maxH box.center.toReal normalizedGoodPoly
        (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) (toR2 contact.direction) ≤ _
    exact maxH_le_maxHℚ box.εθ₂_nonneg box.εφ₂_nonneg
      normalizedGoodPoly normalizedRationalPolyhedron normalizedApproximation
      (direction_norm_eq_one (h.direction_unit j i)) h.center_in_four
  have hchecked :
      ((maxHℚ box.center normalizedRationalPolyhedron
          box.εθ₂ box.εφ₂ contact.direction : ℚ) : ℝ) ≤
        ((Gℚ (outerAsInner box.center) 0 box.εθ₂ box.εφ₂
          (normalizedRationalVertex selected) contact.direction : ℚ) : ℝ) := by
    exact_mod_cast h.supported j i
  have hG :
      ((Gℚ (outerAsInner box.center) 0 box.εθ₂ box.εφ₂
          (normalizedRationalVertex selected) contact.direction : ℚ) : ℝ) ≤
        _root_.GlobalTheorem.G pbar 0 (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
          (normalizedExactVertex selected) (toR2 contact.direction) := by
    simpa [pbar, contact, normalizedApproximation,
      normalizedRationalPolyhedron] using
      (Gℚ_le_G (p_ := outerAsInner box.center) (εα := (0 : ℚ))
        (εθ := box.εθ₂) (εφ := box.εφ₂)
        (by norm_num) box.εθ₂_nonneg box.εφ₂_nonneg
        (normalizedExactVertex_norm_le_one selected)
        (normalizedApproximation.approx selected)
        (direction_norm_eq_one (h.direction_unit j i))
        (outerAsInner_mem_four h.center_in_four))
  have hinner := _root_.GlobalTheorem.global_theorem_inequality_ii
    pbar qouter (0 : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (by norm_num) (by exact_mod_cast box.εθ₂_nonneg)
      (by exact_mod_cast box.εφ₂_nonneg) hnear normalizedGoodPoly pc
  simp only [_root_.GlobalTheorem.GlobalContact.S,
    _root_.GlobalTheorem.GlobalContact.Sval] at hinner
  dsimp [pc] at hpoint houter hmax hinner
  dsimp [qouter] at hpoint hinner
  rw [outerAsInnerReal_inner_eq_outer] at hinner
  dsimp [qouter, selected, contact, pbar] at hpoint houter hmax hchecked hG hinner ⊢
  exact hpoint.trans (houter.trans (hmax.trans (hchecked.trans (hG.trans hinner))))

theorem valid_contact_support_matrixPose (box : Box) (h : box.Valid)
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
              ((box.certificate j).contact i).index))⟫ := by
  simpa [Noperthedron.BalancedSupport.outerProjectionLinear,
    Noperthedron.BalancedSupport.matrixPoseWithOffset_outer_rotation_project] using
    valid_contact_support_pose box h hq j i k

private theorem barycentric_mem_convexHull (box : Box) (h : box.Valid) (k : Fin 6) :
    toR3 (box.octahedronTarget k) ∈
      convexHull ℝ {toR3 (box.approxNormalizedA j) | j} := by
  apply Noperthedron.BalancedSupport.mem_convexHull_of_barycentric
    (fun j => toR3 (box.approxNormalizedA j))
    (fun j => (box.barycentric k j : ℝ))
  · intro j
    exact_mod_cast (h.barycentric k).1 j
  · exact_mod_cast (h.barycentric k).2.1
  · ext coordinate
    have hcoordinate := congrFun (h.barycentric k).2.2 coordinate
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toR3,
      WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_toLp]
    exact_mod_cast hcoordinate

/-- The six checked rational barycentric identities imply the real center
axis-cover property required by the perturbation theorem. -/
theorem valid_center_axis_cover (box : Box) (h : box.Valid)
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

end Noperthedron.SnubCube.LocalCertificate

end
