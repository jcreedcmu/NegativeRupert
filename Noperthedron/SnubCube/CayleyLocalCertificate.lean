module

public import Noperthedron.SnubCube.CayleyInterval
public import Noperthedron.SnubCube.CayleyLocalRigidity
public import Noperthedron.SnubCube.LocalCertificate

@[expose] public section


/-!
# Rational local certificates for Cayley boxes

The existing local certificate supplies the outer support geometry and the
axis cover at the equality stratum.  The three relative Cayley coordinates
are checked separately by an exact squared-radius bound, so the semantic
proof uses the exact Cayley ratio rather than an Euler mismatch estimate.
-/

namespace Noperthedron.SnubCube.CayleyLocalCertificate

open scoped Matrix RealInnerProductSpace
open Noperthedron.BalancedSupport

/-- A Cayley local row: outer-angle geometry plus a relative-coordinate box. -/
structure Box where
  interval : CayleyInterval ℚ
  certificate : Fin 4 → LocalCertificate.AxisCertificate
  c : ℚ
  r : ℚ
deriving DecidableEq

/-- The equality-stratum Euler pose having the same outer view. -/
def outerPose {R : Type} [Zero R] (p : CayleyPose R) : Pose R where
  θ₁ := p.θ
  θ₂ := p.θ
  φ₁ := p.φ
  φ₂ := p.φ
  α := 0

@[simp] theorem outerPose_toReal (p : CayleyPose ℚ) :
    (outerPose p).toReal = outerPose p.toReal := by
  cases p
  simp [outerPose, Pose.toReal, CayleyPose.toReal]

/-- The outer-angle part of a Cayley interval, embedded in the equality
stratum of the old Euler parameterization. -/
def Box.eulerInterval (box : Box) : PoseInterval ℚ :=
  PoseInterval.mk (outerPose box.interval.min) (outerPose box.interval.max) (by
    rw [Pose.le_iff]
    obtain ⟨hθ, hφ, -, -, -⟩ :=
      (CayleyPose.le_iff _ _).mp box.interval.min_le_max
    exact ⟨hθ, hθ, hφ, hφ, le_rfl⟩)

/-- Reuse the mature rational support and axis-cover checker at equality. -/
def Box.eulerBox (box : Box) : LocalCertificate.Box where
  interval := box.eulerInterval
  symmetryIndex := VertexIndex.ofFin24 0
  certificate := box.certificate
  c := box.c
  r := box.r

def endpointAbsBound (lo hi : ℚ) : ℚ := max |lo| |hi|

/-- Exact rational upper bound on `x²+y²+z²` throughout the row. -/
def Box.radiusSq (box : Box) : ℚ :=
  endpointAbsBound box.interval.min.x box.interval.max.x ^ 2 +
    endpointAbsBound box.interval.min.y box.interval.max.y ^ 2 +
    endpointAbsBound box.interval.min.z box.interval.max.z ^ 2

@[mk_iff]
structure Box.Valid (box : Box) : Prop where
  euler : box.eulerBox.Valid
  radius : box.radiusSq ≤ box.c ^ 2

instance (box : Box) : Decidable box.Valid :=
  decidable_of_iff _ (Box.valid_iff box).symm

private theorem abs_le_endpointAbsBound {lo hi : ℚ} {x : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ)) :
    |x| ≤ (endpointAbsBound lo hi : ℚ) := by
  rw [abs_le]
  constructor
  · have hlo : -(|lo| : ℚ) ≤ lo := neg_abs_le lo
    have hmax : |lo| ≤ endpointAbsBound lo hi := le_max_left _ _
    have hrat : (-(endpointAbsBound lo hi) : ℚ) ≤ lo := by linarith
    have hreal : (-(endpointAbsBound lo hi : ℚ) : ℝ) ≤ (lo : ℝ) := by
      exact_mod_cast hrat
    exact hreal.trans hx.1
  · have hhi : hi ≤ |hi| := le_abs_self hi
    have hmax : |hi| ≤ endpointAbsBound lo hi := le_max_right _ _
    exact hx.2.trans (by exact_mod_cast hhi.trans hmax)

theorem Box.sq_sum_le_radiusSq (box : Box) {p : CayleyPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    p.x ^ 2 + p.y ^ 2 + p.z ^ 2 ≤ (box.radiusSq : ℝ) := by
  have hmem := CayleyInterval.mem_toReal_iff.mp hp
  have hx : |p.x| ≤
      (endpointAbsBound box.interval.min.x box.interval.max.x : ℝ) := by
    simpa using abs_le_endpointAbsBound (hmem 2)
  have hy : |p.y| ≤
      (endpointAbsBound box.interval.min.y box.interval.max.y : ℝ) := by
    simpa using abs_le_endpointAbsBound (hmem 3)
  have hz : |p.z| ≤
      (endpointAbsBound box.interval.min.z box.interval.max.z : ℝ) := by
    simpa using abs_le_endpointAbsBound (hmem 4)
  have hxsq : p.x ^ 2 ≤
      (endpointAbsBound box.interval.min.x box.interval.max.x : ℝ) ^ 2 := by
    have hb : 0 ≤
        (endpointAbsBound box.interval.min.x box.interval.max.x : ℝ) := by
      exact_mod_cast (abs_nonneg box.interval.min.x |>.trans (le_max_left _ _))
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg p.x) hb).2 hx
  have hysq : p.y ^ 2 ≤
      (endpointAbsBound box.interval.min.y box.interval.max.y : ℝ) ^ 2 := by
    have hb : 0 ≤
        (endpointAbsBound box.interval.min.y box.interval.max.y : ℝ) := by
      exact_mod_cast (abs_nonneg box.interval.min.y |>.trans (le_max_left _ _))
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg p.y) hb).2 hy
  have hzsq : p.z ^ 2 ≤
      (endpointAbsBound box.interval.min.z box.interval.max.z : ℝ) ^ 2 := by
    have hb : 0 ≤
        (endpointAbsBound box.interval.min.z box.interval.max.z : ℝ) := by
      exact_mod_cast (abs_nonneg box.interval.min.z |>.trans (le_max_left _ _))
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg p.z) hb).2 hz
  simp only [Box.radiusSq]
  push_cast
  linarith

theorem Box.radius_le (box : Box) (h : box.Valid) {p : CayleyPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    Real.sqrt (p.x ^ 2 + p.y ^ 2 + p.z ^ 2) ≤ (box.c : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact_mod_cast h.euler.c_nonneg
  · exact (box.sq_sum_le_radiusSq hp).trans (by exact_mod_cast h.radius)

theorem Box.outerPose_mem_eulerRealInterval (box : Box) {p : CayleyPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    outerPose p ∈ box.eulerBox.realInterval := by
  have hmem := CayleyInterval.mem_toReal_iff.mp hp
  rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff]
  simp only [Box.eulerBox, Box.eulerInterval, PoseInterval.mk,
    PoseInterval.min, PoseInterval.max, LocalCertificate.Box.realInterval,
    outerPose, Pose.toReal_θ₁, Pose.toReal_θ₂,
    Pose.toReal_φ₁, Pose.toReal_φ₂, Pose.toReal_α]
  exact ⟨
    ⟨(hmem 0).1, (hmem 0).1, (hmem 1).1, (hmem 1).1, by norm_num⟩,
    ⟨(hmem 0).2, (hmem 0).2, (hmem 1).2, (hmem 1).2, by norm_num⟩⟩

/-- A valid Cayley row rules out every translated pose in its five-dimensional
box.  All geometric witnesses are inherited from the equality-stratum Euler
row; only the exact relative-rotation ratio is new. -/
theorem Box.valid_imp_not_translated_rupert (box : Box) (h : box.Valid) :
    ∀ p ∈ box.interval.toReal, ∀ offset : ℝ²,
      ¬ RupertPose (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull := by
  intro p hp offset
  let ebox := box.eulerBox
  let q := outerPose p
  have hqmem : q ∈ ebox.realInterval :=
    box.outerPose_mem_eulerRealInterval hp
  have hqnear := ebox.near_center_of_mem_realInterval hqmem
  let relative := relativeRotationAtSymmetry
    (p.matrixPoseWithOffset offset) (VertexIndex.ofFin24 0)
  obtain ⟨a⟩ := exists_axisAngle relative.val relative.property
  apply
    Noperthedron.SnubCube.not_rupertPose_of_axisFree_geometric_certificates_of_cover_perturbation
      (p := p.matrixPoseWithOffset offset)
      (g := VertexIndex.ofFin24 0) (a := a)
      (index := fun j i => (ebox.certificate j).contact i |>.index)
      (weight := fun j => (ebox.certificate j).realWeight)
      (direction := fun j => (ebox.certificate j).realDirection)
      (A := fun j => Noperthedron.SnubCube.firstVariationVector
        (p.matrixPoseWithOffset offset) (ebox.certificate j).realWeight
        (ebox.certificate j).realDirection
        (LocalCertificate.AxisCertificate.realVertex ebox
          (ebox.certificate j)))
      (normalizedA := fun j =>
        (ebox.certificate j).normalizedAAt ebox q offset)
      (centerNormalizedA := fun j => toR3 (ebox.approxNormalizedA j))
      (B := fun j => ((ebox.certificate j).B : ℝ))
      (c := (ebox.c : ℝ)) (δ := (ebox.axisPerturbation : ℝ))
  · intro j
    exact_mod_cast LocalCertificate.AxisCertificate.B_pos ebox h.euler j
  · intro j
    simpa [ebox, q, Noperthedron.SnubCube.firstVariationVector,
      Noperthedron.SnubCube.outerLift, Noperthedron.SnubCube.outerFrame,
      outerPose, CayleyPose.matrixPoseWithOffset, Pose.matrixPoseWithOffset,
      Pose.matrixPoseOfPose] using
      (LocalCertificate.AxisCertificate.firstVariation_eq_B_smul_normalizedAAt
        ebox h.euler j q offset)
  · intro axis haxis
    simpa only [Rat.cast_add] using
      LocalCertificate.valid_center_axis_cover ebox h.euler axis haxis
  · exact LocalCertificate.valid_normalizedA_move ebox h.euler hqnear offset
  · intro j
    rfl
  · exact LocalCertificate.AxisCertificate.real_remainder_le_B ebox h.euler
  · exact p.axisAngle_ratio_le offset a (ebox.c : ℝ) (box.radius_le h hp)
  · intro j i hdirection
    have hnorm :=
      LocalCertificate.AxisCertificate.realDirection_norm ebox h.euler j i
    rw [hdirection, norm_zero] at hnorm
    norm_num at hnorm
  · exact LocalCertificate.AxisCertificate.realWeight_nonneg ebox h.euler
  · intro j
    refine ⟨0, ?_⟩
    change (0 : ℝ) < ((ebox.certificate j).weight 0 : ℝ)
    exact_mod_cast h.euler.weight_pos j 0
  · exact LocalCertificate.AxisCertificate.real_balance ebox h.euler
  · intro j i k
    simpa [ebox, q, Box.eulerBox,
      LocalCertificate.AxisCertificate.realDirection,
      outerProjectionLinear, outerPose,
      CayleyPose.matrixPoseWithOffset, Pose.matrixPoseWithOffset,
      Pose.matrixPoseOfPose] using
      (LocalCertificate.valid_contact_support_matrixPose
        ebox h.euler hqnear offset j i k)

/-- Existential form consumed by the mixed Cayley solution-tree checker. -/
theorem Box.valid_imp_no_translated_rupert_in_interval
    (box : Box) (h : box.Valid) :
    ¬ ∃ p ∈ box.interval.toReal, ∃ offset : ℝ²,
      RupertPose (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull := by
  rintro ⟨p, hp, offset, hrupert⟩
  exact box.valid_imp_not_translated_rupert h p hp offset hrupert

end Noperthedron.SnubCube.CayleyLocalCertificate

end
