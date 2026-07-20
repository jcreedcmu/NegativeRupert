module

public import Noperthedron.BalancedSupport.IdentityAxisFree
public import Noperthedron.Nopert214.Certificate

@[expose] public section


/-!
# Rational identity-local certificates for Nopert #214

A row carries its own equality-stratum center, independently of the midpoint
of the tree interval it covers.  This is important for adaptive subdivision:
any rational leaf contained in the certified neighborhood may use the row.
-/

namespace Noperthedron.Nopert214.LocalCertificate

open RationalApprox GlobalTheorem
open scoped Matrix RealInnerProductSpace

structure Contact where
  index : VertexIndex
  direction : Fin 2 → ℚ
deriving DecidableEq, Repr

structure AxisCertificate where
  contact : Fin 3 → Contact
deriving DecidableEq, Repr

structure Box where
  interval : PoseInterval ℚ
  center : Pose ℚ
  certificate : Fin 4 → AxisCertificate
  c : ℚ
  r : ℚ
deriving DecidableEq

def det2 (u v : Fin 2 → ℚ) : ℚ := u 0 * v 1 - u 1 * v 0

def AxisCertificate.weight (cert : AxisCertificate) : Fin 3 → ℚ :=
  ![det2 (cert.contact 1).direction (cert.contact 2).direction,
    det2 (cert.contact 2).direction (cert.contact 0).direction,
    det2 (cert.contact 0).direction (cert.contact 1).direction]

def AxisCertificate.B (cert : AxisCertificate) : ℚ := ∑ i, cert.weight i

def directionUnit (u : Fin 2 → ℚ) : Prop := u 0 ^ 2 + u 1 ^ 2 = 1

instance (u : Fin 2 → ℚ) : Decidable (directionUnit u) := by
  unfold directionUnit
  infer_instance

def crossQ (u v : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

def endpointRadius (lo hi center : ℚ) : ℚ :=
  max |lo - center| |hi - center|

def Box.εθ₁ (box : Box) : ℚ :=
  endpointRadius box.interval.min.θ₁ box.interval.max.θ₁ box.center.θ₁

def Box.εφ₁ (box : Box) : ℚ :=
  endpointRadius box.interval.min.φ₁ box.interval.max.φ₁ box.center.φ₁

def Box.εθ₂ (box : Box) : ℚ :=
  endpointRadius box.interval.min.θ₂ box.interval.max.θ₂ box.center.θ₂

def Box.εφ₂ (box : Box) : ℚ :=
  endpointRadius box.interval.min.φ₂ box.interval.max.φ₂ box.center.φ₂

def Box.εα (box : Box) : ℚ :=
  endpointRadius box.interval.min.α box.interval.max.α box.center.α

def Box.mismatchRadius (box : Box) : ℚ :=
  box.εα + box.εφ₁ + box.εθ₁ + box.εφ₂ + box.εθ₂

def Box.outerRadius (box : Box) : ℚ := box.εφ₂ + box.εθ₂

def centerVectorError : ℚ := 2 * κℚ + κℚ ^ 2

def Box.axisPerturbation (box : Box) : ℚ :=
  box.outerRadius + centerVectorError

def AxisCertificate.approxLift (box : Box) (cert : AxisCertificate)
    (i : Fin 3) : Fin 3 → ℚ :=
  (RationalApprox.rotMℚ_mat box.center.θ₂ box.center.φ₂)ᵀ *ᵥ
    (cert.contact i).direction

def AxisCertificate.approxA (box : Box) (cert : AxisCertificate) :
    Fin 3 → ℚ :=
  ∑ i, cert.weight i •
    crossQ (rationalVertex (cert.contact i).index) (cert.approxLift box i)

def AxisCertificate.approxNormalizedA (box : Box)
    (cert : AxisCertificate) : Fin 3 → ℚ :=
  fun coordinate => cert.approxA box coordinate / cert.B

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

theorem tetraBarycentricQ_sum (p : Fin 4 → Fin 3 → ℚ)
    (target : Fin 3 → ℚ) :
    ∑ j, tetraBarycentricQ p target j = 1 := by
  simp [tetraBarycentricQ, Fin.sum_univ_four]

theorem tetraBarycentricQ_combination (p : Fin 4 → Fin 3 → ℚ)
    (target : Fin 3 → ℚ) (hdet : tetraDetQ p ≠ 0) :
    ∑ j, tetraBarycentricQ p target j • p j = target := by
  simp only [tetraDetQ] at hdet
  funext coordinate
  fin_cases coordinate <;>
    simp [tetraBarycentricQ, Fin.sum_univ_four, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] <;>
    field_simp [hdet] <;>
    simp [det3Q, sub3Q] <;> ring

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

def Contact.supported (box : Box) (contact : Contact) : Prop :=
  ∀ k : VertexIndex,
    k = contact.index ∨
      Hℚ box.center box.εθ₂ box.εφ₂ contact.direction
          (rationalVertex k) ≤
        Gℚ box.center 0 box.εθ₂ box.εφ₂
          (rationalVertex contact.index) contact.direction

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

def Box.equalityCenter (box : Box) : Prop :=
  box.center.θ₁ = box.center.θ₂ ∧
    box.center.φ₁ = box.center.φ₂ ∧ box.center.α = 0

instance (box : Box) : Decidable box.equalityCenter := by
  unfold Box.equalityCenter
  infer_instance

@[mk_iff]
structure Box.GeometricValid (box : Box) : Prop where
  center_in_four : box.center ∈ fourInterval ℚ
  equality_center : box.equalityCenter
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
  equality_center : box.equalityCenter
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
  equality_center := h.equality_center
  c_nonneg := h.c_nonneg
  direction_unit := h.direction_unit
  weight_pos := h.weight_pos
  balanced := h.balanced
  supported := h.supported
  barycentric := h.barycentric

def Box.realInterval (box : Box) : PoseInterval ℝ :=
  PoseInterval.mk box.interval.min.toReal box.interval.max.toReal (by
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      (Pose.le_iff _ _).mp box.interval.min_le_max
    rw [Pose.le_iff]
    simp only [Pose.toReal_θ₁, Pose.toReal_θ₂, Pose.toReal_φ₁,
      Pose.toReal_φ₂, Pose.toReal_α]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2,
      by exact_mod_cast h3, by exact_mod_cast h4, by exact_mod_cast h5⟩)

private theorem endpointRadius_nonneg (lo hi center : ℚ) :
    0 ≤ endpointRadius lo hi center :=
  (abs_nonneg (lo - center)).trans (le_max_left _ _)

theorem Box.εθ₁_nonneg (box : Box) : 0 ≤ box.εθ₁ :=
  endpointRadius_nonneg _ _ _

theorem Box.εφ₁_nonneg (box : Box) : 0 ≤ box.εφ₁ :=
  endpointRadius_nonneg _ _ _

theorem Box.εθ₂_nonneg (box : Box) : 0 ≤ box.εθ₂ :=
  endpointRadius_nonneg _ _ _

theorem Box.εφ₂_nonneg (box : Box) : 0 ≤ box.εφ₂ :=
  endpointRadius_nonneg _ _ _

theorem Box.εα_nonneg (box : Box) : 0 ≤ box.εα :=
  endpointRadius_nonneg _ _ _

private theorem abs_sub_center_le_endpointRadius
    {lo hi center : ℚ} {x : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ)) :
    |x - (center : ℝ)| ≤ (endpointRadius lo hi center : ℚ) := by
  obtain ⟨hxlo, hxhi⟩ := hx
  let radius := endpointRadius lo hi center
  have hlo : |lo - center| ≤ radius := le_max_left _ _
  have hhi : |hi - center| ≤ radius := le_max_right _ _
  have hlo' : (center : ℝ) - (radius : ℝ) ≤ (lo : ℝ) := by
    have := (neg_le_of_abs_le hlo)
    exact_mod_cast (by linarith : center - radius ≤ lo)
  have hhi' : (hi : ℝ) ≤ (center : ℝ) + (radius : ℝ) := by
    have := (le_of_abs_le hhi)
    exact_mod_cast (by linarith : hi ≤ center + radius)
  rw [abs_le]
  change -(radius : ℝ) ≤ x - (center : ℝ) ∧
    x - (center : ℝ) ≤ (radius : ℝ)
  constructor <;> linarith

theorem Box.near_center_of_mem_realInterval (box : Box)
    {q : Pose ℝ} (hq : q ∈ box.realInterval) :
    Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q := by
  rw [NonemptyInterval.mem_def] at hq
  obtain ⟨hlo, hhi⟩ := hq
  rw [Pose.le_iff] at hlo hhi
  obtain ⟨l1, l2, l3, l4, l5⟩ := hlo
  obtain ⟨u1, u2, u3, u4, u5⟩ := hhi
  simp only [Box.realInterval, PoseInterval.mk, PoseInterval.min,
    PoseInterval.max, Pose.toReal_θ₁, Pose.toReal_θ₂, Pose.toReal_φ₁,
    Pose.toReal_φ₂, Pose.toReal_α] at l1 l2 l3 l4 l5 u1 u2 u3 u4 u5
  exact ⟨
    abs_sub_center_le_endpointRadius ⟨l1, u1⟩,
    abs_sub_center_le_endpointRadius ⟨l3, u3⟩,
    abs_sub_center_le_endpointRadius ⟨l2, u2⟩,
    abs_sub_center_le_endpointRadius ⟨l4, u4⟩,
    abs_sub_center_le_endpointRadius ⟨l5, u5⟩⟩

private theorem direction_norm_eq_one {u : Fin 2 → ℚ} (h : directionUnit u) :
    ‖toR2 u‖ = 1 := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_one]
  congr 1
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, toR2,
    WithLp.ofLp_toLp]
  exact_mod_cast h

def AxisCertificate.realWeight (cert : AxisCertificate) (i : Fin 3) : ℝ :=
  (cert.weight i : ℝ)

noncomputable def AxisCertificate.realDirection
    (cert : AxisCertificate) (i : Fin 3) : ℝ² :=
  toR2 (cert.contact i).direction

noncomputable def AxisCertificate.realVertex
    (cert : AxisCertificate) (i : Fin 3) : ℝ³ :=
  exactVertex (cert.contact i).index

lemma AxisCertificate.B_pos (box : Box) (h : box.GeometricValid)
    (j : Fin 4) : 0 < (box.certificate j).B := by
  unfold AxisCertificate.B
  apply Finset.sum_pos
  · intro i _
    exact h.weight_pos j i
  · exact Finset.univ_nonempty

lemma AxisCertificate.realWeight_nonneg (box : Box) (h : box.GeometricValid)
    (j : Fin 4) (i : Fin 3) :
    0 ≤ (box.certificate j).realWeight i := by
  unfold AxisCertificate.realWeight
  exact_mod_cast (h.weight_pos j i).le

lemma AxisCertificate.realDirection_norm (box : Box) (h : box.GeometricValid)
    (j : Fin 4) (i : Fin 3) :
    ‖(box.certificate j).realDirection i‖ = 1 :=
  direction_norm_eq_one (h.direction_unit j i)

lemma AxisCertificate.real_remainder_le_B (box : Box) (h : box.GeometricValid)
    (j : Fin 4) :
    ∑ i, (box.certificate j).realWeight i *
        (‖(box.certificate j).realDirection i‖ *
          ‖(box.certificate j).realVertex i‖) ≤
      ((box.certificate j).B : ℝ) := by
  calc
    ∑ i, (box.certificate j).realWeight i *
        (‖(box.certificate j).realDirection i‖ *
          ‖(box.certificate j).realVertex i‖) ≤
        ∑ i, (box.certificate j).realWeight i := by
      apply Finset.sum_le_sum
      intro i _
      rw [AxisCertificate.realDirection_norm box h j i, one_mul]
      exact mul_le_of_le_one_right
        (AxisCertificate.realWeight_nonneg box h j i)
        (exactVertex_norm_le_one _)
    _ = ((box.certificate j).B : ℝ) := by
      unfold AxisCertificate.B AxisCertificate.realWeight
      push_cast
      rfl

lemma AxisCertificate.real_balance (box : Box) (h : box.GeometricValid)
    (j : Fin 4) :
    ∑ i, (box.certificate j).realWeight i •
        (box.certificate j).realDirection i = 0 := by
  ext coordinate
  have hb := congrFun (h.balanced j) coordinate
  simp only [Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply] at hb
  simp only [AxisCertificate.realWeight, AxisCertificate.realDirection,
    WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero, Finset.sum_apply,
    Pi.smul_apply, Pi.zero_apply, toR2, smul_eq_mul]
  exact_mod_cast hb

noncomputable def AxisCertificate.normalizedAAt
    (cert : AxisCertificate) (q : Pose ℝ) (offset : ℝ²) : ℝ³ :=
  ((cert.B : ℝ)⁻¹) •
    Noperthedron.SnubCube.firstVariationVector
      (q.matrixPoseWithOffset offset) cert.realWeight cert.realDirection
      cert.realVertex

lemma AxisCertificate.firstVariation_eq_B_smul_normalizedAAt
    (box : Box) (h : box.GeometricValid) (j : Fin 4)
    (q : Pose ℝ) (offset : ℝ²) :
    Noperthedron.SnubCube.firstVariationVector
        (q.matrixPoseWithOffset offset) (box.certificate j).realWeight
        (box.certificate j).realDirection (box.certificate j).realVertex =
      ((box.certificate j).B : ℝ) •
        (box.certificate j).normalizedAAt q offset := by
  rw [AxisCertificate.normalizedAAt, smul_smul]
  simp [ne_of_gt (AxisCertificate.B_pos box h j)]

private theorem equalityCenter_relativeRotation (box : Box)
    (h : box.equalityCenter) :
    Noperthedron.BalancedSupport.relativeRotation
      (box.center.toReal.matrixPoseWithOffset 0) = 1 := by
  obtain ⟨hθ, hφ, hα⟩ := h
  have hθr : (box.center.θ₁ : ℝ) = (box.center.θ₂ : ℝ) := by
    exact_mod_cast hθ
  have hφr : (box.center.φ₁ : ℝ) = (box.center.φ₂ : ℝ) := by
    exact_mod_cast hφ
  have hαr : (box.center.α : ℝ) = 0 := by
    exact_mod_cast hα
  have hrot :
      (box.center.toReal.matrixPoseWithOffset 0).innerRot =
        (box.center.toReal.matrixPoseWithOffset 0).outerRot := by
    apply Subtype.ext
    simp only [Pose.matrixPoseWithOffset, Pose.matrixPoseOfPose,
      Pose.toReal_θ₁, Pose.toReal_θ₂, Pose.toReal_φ₁, Pose.toReal_φ₂,
      Pose.toReal_α]
    rw [hθr, hφr, hαr]
  unfold Noperthedron.BalancedSupport.relativeRotation
  rw [hrot]
  simp

theorem valid_axisAngle_ratio (box : Box) (h : box.Valid)
    {q : Pose ℝ}
    (hq : Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q)
    (offset : ℝ²)
    (a : Noperthedron.BalancedSupport.AxisAngle
      ((Noperthedron.BalancedSupport.relativeRotation
        (q.matrixPoseWithOffset offset)).val.toEuclideanLin.toContinuousLinearMap)) :
    1 - Real.cos a.angle ≤ |Real.sin a.angle| * (box.c : ℝ) := by
  apply Noperthedron.BalancedSupport.AxisAngle.ratio_of_identity_pose_box
    q box.center.toReal offset 0 a (box.c : ℝ) (box.r : ℝ)
  · exact_mod_cast h.c_nonneg
  · exact_mod_cast h.r_nonneg
  · exact equalityCenter_relativeRotation box h.equality_center
  · apply (add_le_add (add_le_add (add_le_add hq.2.2.2.2 hq.2.1) hq.1)
      (add_le_add hq.2.2.2.1 hq.2.2.1)).trans
    have hm : (box.εα : ℝ) + (box.εφ₁ : ℝ) + (box.εθ₁ : ℝ) +
        (box.εφ₂ : ℝ) + (box.εθ₂ : ℝ) ≤ (box.r : ℝ) := by
      exact_mod_cast h.mismatch_bound
    linarith
  · exact_mod_cast h.angle_bound

private theorem toR3_crossQ (u v : Fin 3 → ℚ) :
    toR3 (crossQ u v) =
      Noperthedron.BalancedSupport.cross3 (toR3 u) (toR3 v) := by
  ext i
  fin_cases i <;>
    simp [crossQ, Noperthedron.BalancedSupport.cross3, cross_apply, toR3]

private theorem toR3_sum {ι : Type} [Fintype ι] (f : ι → Fin 3 → ℚ) :
    toR3 (∑ i, f i) = ∑ i, toR3 (f i) := by
  ext coordinate
  simp [toR3]

private theorem toR3_smul (a : ℚ) (v : Fin 3 → ℚ) :
    toR3 (a • v) = (a : ℝ) • toR3 v := by
  ext coordinate
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

lemma AxisCertificate.toR3_approxLift (box : Box)
    (cert : AxisCertificate) (i : Fin 3) :
    toR3 (cert.approxLift box i) =
      (RationalApprox.rotMℚℝ (box.center.θ₂ : ℝ)
        (box.center.φ₂ : ℝ)).adjoint (toR2 (cert.contact i).direction) := by
  exact toR3_rotMℚ_transpose_mulVec _ _ _

lemma AxisCertificate.toR3_approxA (box : Box) (cert : AxisCertificate) :
    toR3 (cert.approxA box) =
      ∑ i, (cert.weight i : ℝ) •
        Noperthedron.BalancedSupport.cross3
          (toR3 (rationalVertex (cert.contact i).index))
          ((RationalApprox.rotMℚℝ (box.center.θ₂ : ℝ)
            (box.center.φ₂ : ℝ)).adjoint
              (toR2 (cert.contact i).direction)) := by
  rw [AxisCertificate.approxA, toR3_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [toR3_smul, toR3_crossQ, cert.toR3_approxLift]

lemma AxisCertificate.toR3_approxA_eq_smul (box : Box)
    (h : box.GeometricValid) (j : Fin 4) :
    toR3 ((box.certificate j).approxA box) =
      ((box.certificate j).B : ℝ) •
        toR3 (box.approxNormalizedA j) := by
  ext coordinate
  change ((((box.certificate j).approxA box coordinate : ℚ) : ℝ)) =
    ((box.certificate j).B : ℝ) *
      (((((box.certificate j).approxA box coordinate /
        (box.certificate j).B : ℚ) : ℝ)))
  push_cast
  field_simp [ne_of_gt (AxisCertificate.B_pos box h j)]

theorem valid_center_normalizedA_approx (box : Box)
    (h : box.GeometricValid) (j : Fin 4) :
    ‖(box.certificate j).normalizedAAt box.center.toReal 0 -
        toR3 (box.approxNormalizedA j)‖ ≤
      ((centerVectorError : ℚ) : ℝ) := by
  let cert := box.certificate j
  let approxVertex : Fin 3 → ℝ³ := fun i =>
    toR3 (rationalVertex (cert.contact i).index)
  let exactLift : Fin 3 → ℝ³ := fun i =>
    Noperthedron.SnubCube.outerLift
      (box.center.toReal.matrixPoseWithOffset 0) (cert.realDirection i)
  let approxLift : Fin 3 → ℝ³ := fun i => toR3 (cert.approxLift box i)
  have hbound := Noperthedron.SnubCube.norm_normalizedWeightedCross_approx_sub_le
    cert.realWeight cert.realVertex approxVertex exactLift approxLift
    (cert.normalizedAAt box.center.toReal 0)
    (toR3 (box.approxNormalizedA j)) (cert.B : ℝ) RationalApprox.κ
    (by unfold RationalApprox.κ; norm_num)
    (fun i => by
      unfold AxisCertificate.realWeight
      exact_mod_cast (h.weight_pos j i).le)
    (by exact_mod_cast AxisCertificate.B_pos box h j)
    (by
      unfold AxisCertificate.B AxisCertificate.realWeight
      push_cast
      rfl)
    (fun i => exactVertex_norm_le_one _)
    (fun i => by
      change ‖exactVertex (cert.contact i).index -
        toR3 (rationalVertex (cert.contact i).index)‖ ≤ RationalApprox.κ
      simp [exactVertex, RationalApprox.κ])
    (fun i => by
      have hlift := Noperthedron.SnubCube.norm_outerLift_rationalApprox_sub_le
        box.center h.center_in_four (0 : ℝ²) (cert.realDirection i)
        (direction_norm_eq_one (h.direction_unit j i))
      simpa [exactLift, approxLift, AxisCertificate.realDirection,
        cert.toR3_approxLift] using hlift)
    (fun i => by
      have hlift := Noperthedron.SnubCube.norm_rationalApprox_outerLift_le
        box.center h.center_in_four (cert.realDirection i)
        (direction_norm_eq_one (h.direction_unit j i))
      simpa [approxLift, AxisCertificate.realDirection,
        cert.toR3_approxLift] using hlift)
    (by
      simpa [Noperthedron.SnubCube.firstVariationVector, exactLift,
        AxisCertificate.realWeight, AxisCertificate.realDirection,
        AxisCertificate.realVertex, exactVertex, approxVertex, cert] using
          (AxisCertificate.firstVariation_eq_B_smul_normalizedAAt
            box h j box.center.toReal (0 : ℝ²)))
    (by
      dsimp [AxisCertificate.realWeight, approxVertex, approxLift]
      simp_rw [cert.toR3_approxLift]
      rw [← cert.toR3_approxA box]
      exact AxisCertificate.toR3_approxA_eq_smul box h j)
  calc
    ‖(box.certificate j).normalizedAAt box.center.toReal 0 -
        toR3 (box.approxNormalizedA j)‖ ≤
        2 * RationalApprox.κ + RationalApprox.κ ^ 2 := by
      simpa [cert] using hbound
    _ = ((centerVectorError : ℚ) : ℝ) := by
      norm_num [centerVectorError, RationalApprox.κ, RationalApprox.κℚ]

theorem valid_normalizedA_move (box : Box) (h : box.GeometricValid)
    {q : Pose ℝ}
    (hq : Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q)
    (offset : ℝ²) (j : Fin 4) :
    ‖(box.certificate j).normalizedAAt q offset -
        toR3 (box.approxNormalizedA j)‖ ≤
      ((box.axisPerturbation : ℚ) : ℝ) := by
  let cert := box.certificate j
  have hweight : ∀ i, 0 ≤ cert.realWeight i := by
    intro i
    unfold AxisCertificate.realWeight
    exact_mod_cast (h.weight_pos j i).le
  have hbudget :
      ∑ i, cert.realWeight i *
          (‖cert.realDirection i‖ * ‖cert.realVertex i‖) ≤ (cert.B : ℝ) :=
    AxisCertificate.real_remainder_le_B box h j
  have hcenterMove :=
    Noperthedron.SnubCube.norm_normalizedFirstVariation_matrixPoseWithOffset_sub_le_of_budget_bound
      q box.center.toReal offset 0 cert.realWeight cert.realDirection
      cert.realVertex (cert.normalizedAAt q offset)
      (cert.normalizedAAt box.center.toReal 0) (cert.B : ℝ)
      hweight (by exact_mod_cast AxisCertificate.B_pos box h j) hbudget
      (AxisCertificate.firstVariation_eq_B_smul_normalizedAAt box h j q offset)
      (AxisCertificate.firstVariation_eq_B_smul_normalizedAAt
        box h j box.center.toReal 0)
  have hcenterMove' :
      ‖cert.normalizedAAt q offset -
          cert.normalizedAAt box.center.toReal 0‖ ≤ (box.outerRadius : ℝ) := by
    apply hcenterMove.trans
    rw [show (box.outerRadius : ℝ) =
      (box.εφ₂ : ℝ) + (box.εθ₂ : ℝ) by simp [Box.outerRadius]]
    exact add_le_add hq.2.2.2.1 hq.2.2.1
  have happrox := valid_center_normalizedA_approx box h j
  calc
    ‖(box.certificate j).normalizedAAt q offset -
        toR3 (box.approxNormalizedA j)‖ ≤
      ‖cert.normalizedAAt q offset - cert.normalizedAAt box.center.toReal 0‖ +
        ‖cert.normalizedAAt box.center.toReal 0 -
          toR3 (box.approxNormalizedA j)‖ := by
      dsimp [cert]
      rw [show (box.certificate j).normalizedAAt q offset -
          toR3 (box.approxNormalizedA j) =
        ((box.certificate j).normalizedAAt q offset -
            (box.certificate j).normalizedAAt box.center.toReal 0) +
          ((box.certificate j).normalizedAAt box.center.toReal 0 -
            toR3 (box.approxNormalizedA j)) by abel]
      exact norm_add_le _ _
    _ ≤ (box.outerRadius : ℝ) + (centerVectorError : ℝ) :=
      add_le_add hcenterMove' happrox
    _ = ((box.axisPerturbation : ℚ) : ℝ) := by
      simp [Box.axisPerturbation]

private noncomputable def outerAsInnerReal (p : Pose ℝ) : Pose ℝ where
  θ₁ := p.θ₂
  θ₂ := p.θ₂
  φ₁ := p.φ₂
  φ₂ := p.φ₂
  α := 0

private theorem outerAsInnerReal_inner_eq_outer (p : Pose ℝ) :
    Pose.inner (outerAsInnerReal p) = Pose.outer p := rfl

private theorem outerAsInnerReal_outer_eq_outer (p : Pose ℝ) :
    Pose.outer (outerAsInnerReal p) = Pose.outer p := rfl

private theorem outerAsInnerReal_near (box : Box) (h : box.equalityCenter)
    {q : Pose ℝ}
    (hq : Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q) :
    Pose.near box.center.toReal 0 (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) (outerAsInnerReal q) := by
  obtain ⟨hθ, hφ, hα⟩ := h
  have hθr : (box.center.θ₁ : ℝ) = (box.center.θ₂ : ℝ) := by
    exact_mod_cast hθ
  have hφr : (box.center.φ₁ : ℝ) = (box.center.φ₂ : ℝ) := by
    exact_mod_cast hφ
  have hαr : (box.center.α : ℝ) = 0 := by
    exact_mod_cast hα
  change
    |(outerAsInnerReal q).θ₁ - box.center.toReal.θ₁| ≤ (box.εθ₂ : ℝ) ∧
    |(outerAsInnerReal q).φ₁ - box.center.toReal.φ₁| ≤ (box.εφ₂ : ℝ) ∧
    |(outerAsInnerReal q).θ₂ - box.center.toReal.θ₂| ≤ (box.εθ₂ : ℝ) ∧
    |(outerAsInnerReal q).φ₂ - box.center.toReal.φ₂| ≤ (box.εφ₂ : ℝ) ∧
    |(outerAsInnerReal q).α - box.center.toReal.α| ≤ 0
  dsimp [outerAsInnerReal]
  rw [hθr, hφr, hαr]
  exact ⟨hq.2.2.1, hq.2.2.2.1, hq.2.2.1, hq.2.2.2.1, by simp⟩

/-- A rational Taylor support check remains a true support inequality
throughout the row's outer-view interval. -/
theorem contact_support_pose (box : Box) (contact : Contact)
    (hcenter : box.center ∈ fourInterval ℚ)
    (hequality : box.equalityCenter)
    (hdirection : directionUnit contact.direction)
    (hsupported : contact.supported box)
    {q : Pose ℝ}
    (hq : Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q)
    (k : VertexIndex) :
    ⟪toR2 contact.direction, q.outer (exactVertex k)⟫ ≤
      ⟪toR2 contact.direction, q.outer (exactVertex contact.index)⟫ := by
  let qouter := outerAsInnerReal q
  let pbar := box.center.toReal
  let pc : _root_.GlobalTheorem.GlobalContact exactGoodPoly pbar
      (0 : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) := {
    Si := contact.index
    w := toR2 contact.direction
    w_unit := direction_norm_eq_one hdirection
  }
  have hnear : Pose.near pbar 0 (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) qouter := by
    dsimp [pbar, qouter]
    exact outerAsInnerReal_near box hequality hq
  by_cases hk : k = contact.index
  · subst k
    exact le_rfl
  have houter := _root_.GlobalTheorem.global_theorem_outer_le_H
    pbar qouter (0 : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (by exact_mod_cast box.εθ₂_nonneg)
      (by exact_mod_cast box.εφ₂_nonneg) hnear exactGoodPoly pc k
  have hH :
      _root_.GlobalTheorem.H pbar (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
          pc.w (exactVertex k) ≤
        ((Hℚ box.center box.εθ₂ box.εφ₂ contact.direction
          (rationalVertex k) : ℚ) : ℝ) := by
    change _root_.GlobalTheorem.H box.center.toReal
        (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) (toR2 contact.direction)
          (exactVertex k) ≤ _
    exact H_le_Hℚ box.εθ₂_nonneg box.εφ₂_nonneg
      (exactVertex_norm_le_one k) (exactApproximation.approx k)
      (direction_norm_eq_one hdirection) hcenter
  have hchecked :
      ((Hℚ box.center box.εθ₂ box.εφ₂ contact.direction
          (rationalVertex k) : ℚ) : ℝ) ≤
        ((Gℚ box.center 0 box.εθ₂ box.εφ₂
          (rationalVertex contact.index) contact.direction : ℚ) : ℝ) := by
    exact_mod_cast hsupported k |>.resolve_left hk
  have hG :
      ((Gℚ box.center 0 box.εθ₂ box.εφ₂
          (rationalVertex contact.index) contact.direction : ℚ) : ℝ) ≤
        _root_.GlobalTheorem.G pbar 0 (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
          (exactVertex contact.index) (toR2 contact.direction) := by
    simpa [pbar, exactApproximation, rationalPolyhedron] using
      (Gℚ_le_G (p_ := box.center) (εα := (0 : ℚ))
        (εθ := box.εθ₂) (εφ := box.εφ₂)
        (by norm_num) box.εθ₂_nonneg box.εφ₂_nonneg
        (exactVertex_norm_le_one contact.index)
        (exactApproximation.approx contact.index)
        (direction_norm_eq_one hdirection) hcenter)
  have hinner := _root_.GlobalTheorem.global_theorem_inequality_ii
    pbar qouter (0 : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (box.εθ₂ : ℝ) (box.εφ₂ : ℝ)
      (by norm_num) (by exact_mod_cast box.εθ₂_nonneg)
      (by exact_mod_cast box.εφ₂_nonneg) hnear exactGoodPoly pc
  simp only [_root_.GlobalTheorem.GlobalContact.S,
    _root_.GlobalTheorem.GlobalContact.Sval] at hinner
  dsimp [pc] at houter hinner
  rw [outerAsInnerReal_inner_eq_outer] at hinner
  rw [outerAsInnerReal_outer_eq_outer] at houter
  dsimp [qouter, pbar] at houter hH hchecked hG hinner ⊢
  exact houter.trans (hH.trans (hchecked.trans (hG.trans hinner)))

theorem contact_support_matrixPose (box : Box) (contact : Contact)
    (hcenter : box.center ∈ fourInterval ℚ)
    (hequality : box.equalityCenter)
    (hdirection : directionUnit contact.direction)
    (hsupported : contact.supported box)
    {q : Pose ℝ}
    (hq : Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q)
    (offset : ℝ²) (k : VertexIndex) :
    ⟪toR2 contact.direction,
        Noperthedron.BalancedSupport.outerProjectionLinear
          (q.matrixPoseWithOffset offset) (exactVertex k)⟫ ≤
      ⟪toR2 contact.direction,
        Noperthedron.BalancedSupport.outerProjectionLinear
          (q.matrixPoseWithOffset offset) (exactVertex contact.index)⟫ := by
  simpa [Noperthedron.BalancedSupport.outerProjectionLinear,
    Noperthedron.BalancedSupport.matrixPoseWithOffset_outer_rotation_project] using
    contact_support_pose box contact hcenter hequality hdirection hsupported hq k

theorem valid_contact_support_matrixPose (box : Box) (h : box.GeometricValid)
    {q : Pose ℝ}
    (hq : Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
      (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q)
    (offset : ℝ²) (j : Fin 4) (i : Fin 3) (k : VertexIndex) :
    ⟪toR2 ((box.certificate j).contact i).direction,
        Noperthedron.BalancedSupport.outerProjectionLinear
          (q.matrixPoseWithOffset offset) (exactVertex k)⟫ ≤
      ⟪toR2 ((box.certificate j).contact i).direction,
        Noperthedron.BalancedSupport.outerProjectionLinear
          (q.matrixPoseWithOffset offset)
          (exactVertex ((box.certificate j).contact i).index)⟫ :=
  contact_support_matrixPose box ((box.certificate j).contact i)
    h.center_in_four h.equality_center (h.direction_unit j i)
    (h.supported j i) hq offset k

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

theorem valid_center_axis_cover (box : Box) (h : box.GeometricValid)
    (axis : ℝ³) (haxis : ‖axis‖ = 1) :
    ∃ j, ((box.c + box.axisPerturbation : ℚ) : ℝ) ≤
      ⟪axis, toR3 (box.approxNormalizedA j)⟫ := by
  apply Noperthedron.BalancedSupport.octahedral_axis_cover
    (fun j => toR3 (box.approxNormalizedA j))
    ((box.c + box.axisPerturbation : ℚ) : ℝ)
  · exact_mod_cast add_nonneg h.c_nonneg
      (add_nonneg (add_nonneg box.εφ₂_nonneg box.εθ₂_nonneg)
        (by norm_num [centerVectorError, RationalApprox.κℚ]))
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

/-- A valid local row rules out every translated pose in its Euler interval. -/
theorem Box.valid_imp_not_translated_rupert (box : Box) (h : box.Valid) :
    ∀ q, Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
        (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q →
      ∀ offset : ℝ²,
        ¬ RupertPose (q.matrixPoseWithOffset offset) exactGoodPoly.hull := by
  intro q hq offset
  let hg := h.geometric
  let relative := Noperthedron.BalancedSupport.relativeRotation
    (q.matrixPoseWithOffset offset)
  obtain ⟨a⟩ := Noperthedron.BalancedSupport.exists_axisAngle
    relative.val relative.property
  apply
    Noperthedron.BalancedSupport.not_rupertPose_of_identity_axisFree_certificates_of_cover_perturbation
      (poly := exactPolyhedron) (p := q.matrixPoseWithOffset offset) (a := a)
      (index := fun j i => (box.certificate j).contact i |>.index)
      (weight := fun j => (box.certificate j).realWeight)
      (direction := fun j => (box.certificate j).realDirection)
      (A := fun j => Noperthedron.SnubCube.firstVariationVector
        (q.matrixPoseWithOffset offset) (box.certificate j).realWeight
        (box.certificate j).realDirection (box.certificate j).realVertex)
      (normalizedA := fun j => (box.certificate j).normalizedAAt q offset)
      (centerNormalizedA := fun j => toR3 (box.approxNormalizedA j))
      (B := fun j => ((box.certificate j).B : ℝ))
      (c := (box.c : ℝ)) (δ := (box.axisPerturbation : ℝ))
  · intro j
    exact_mod_cast AxisCertificate.B_pos box hg j
  · intro j
    exact AxisCertificate.firstVariation_eq_B_smul_normalizedAAt
      box hg j q offset
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
    unfold AxisCertificate.realWeight
    exact_mod_cast h.weight_pos j 0
  · exact AxisCertificate.real_balance box hg
  · intro j i k
    change ⟪toR2 ((box.certificate j).contact i).direction,
        Noperthedron.BalancedSupport.outerProjectionLinear
          (q.matrixPoseWithOffset offset) (exactVertex k)⟫ ≤
      ⟪toR2 ((box.certificate j).contact i).direction,
        Noperthedron.BalancedSupport.outerProjectionLinear
          (q.matrixPoseWithOffset offset)
          (exactVertex ((box.certificate j).contact i).index)⟫
    exact valid_contact_support_matrixPose box hg hq offset j i k

theorem Box.valid_imp_no_translated_rupert_in_interval
    (box : Box) (h : box.Valid) :
    ¬ ∃ q ∈ box.realInterval, ∃ offset : ℝ²,
      RupertPose (q.matrixPoseWithOffset offset) exactGoodPoly.hull := by
  rintro ⟨q, hq, offset, hrupert⟩
  exact box.valid_imp_not_translated_rupert h q
    (box.near_center_of_mem_realInterval hq) offset hrupert

end Noperthedron.Nopert214.LocalCertificate

end
