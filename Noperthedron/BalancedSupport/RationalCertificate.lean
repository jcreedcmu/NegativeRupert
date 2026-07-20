module

public import Noperthedron.RationalApprox.RationalBalancedGlobal

@[expose] public section


/-!
# Generic decidable balanced-global box certificates

This is the polyhedron-parameterized form of the rational checker first used
for the snub cube.  A box stores three rational contacts.  Exact unit length,
nonnegative weights, balance, and the aggregate Taylor inequality are all
decidable over `ℚ`; the soundness theorem accepts any real/rational
polyhedron pair connected by `κApproxPoly`.
-/

namespace Noperthedron.BalancedSupport.RationalCertificate

open RationalApprox.GlobalTheorem

structure Contact (ι : Type) where
  innerIndex : ι
  outerIndex : ι
  direction : Fin 2 → ℚ
  weight : ℚ
deriving DecidableEq, Repr

structure Box (ι : Type) where
  interval : PoseInterval ℚ
  contact : Fin 3 → Contact ι
deriving DecidableEq

def Box.center {ι : Type} (box : Box ι) : Pose ℚ where
  θ₁ := (box.interval.min.θ₁ + box.interval.max.θ₁) / 2
  θ₂ := (box.interval.min.θ₂ + box.interval.max.θ₂) / 2
  φ₁ := (box.interval.min.φ₁ + box.interval.max.φ₁) / 2
  φ₂ := (box.interval.min.φ₂ + box.interval.max.φ₂) / 2
  α := (box.interval.min.α + box.interval.max.α) / 2

abbrev Box.εθ₁ {ι : Type} (box : Box ι) : ℚ :=
  (box.interval.max.θ₁ - box.interval.min.θ₁) / 2
abbrev Box.εφ₁ {ι : Type} (box : Box ι) : ℚ :=
  (box.interval.max.φ₁ - box.interval.min.φ₁) / 2
abbrev Box.εθ₂ {ι : Type} (box : Box ι) : ℚ :=
  (box.interval.max.θ₂ - box.interval.min.θ₂) / 2
abbrev Box.εφ₂ {ι : Type} (box : Box ι) : ℚ :=
  (box.interval.max.φ₂ - box.interval.min.φ₂) / 2
abbrev Box.εα {ι : Type} (box : Box ι) : ℚ :=
  (box.interval.max.α - box.interval.min.α) / 2

def Contact.unit {ι : Type} (contact : Contact ι) : Prop :=
  contact.direction 0 ^ 2 + contact.direction 1 ^ 2 = 1

instance {ι : Type} (contact : Contact ι) : Decidable contact.unit := by
  unfold Contact.unit
  infer_instance

def Box.balanced {ι : Type} (box : Box ι) : Prop :=
  ∑ k, (box.contact k).weight • (box.contact k).direction = 0

instance {ι : Type} (box : Box ι) : Decidable box.balanced := by
  unfold Box.balanced
  infer_instance

def Box.dominates {ι : Type} [Fintype ι] [Nonempty ι]
    (polyQ : Polyhedron ι (Fin 3 → ℚ)) (box : Box ι) : Prop :=
  ∑ k, (box.contact k).weight *
      maxHℚ box.center polyQ box.εθ₂ box.εφ₂
        (box.contact k).direction ≤
    ∑ k, (box.contact k).weight *
      Gℚ box.center box.εα box.εθ₁ box.εφ₁
        (polyQ.v (box.contact k).innerIndex)
        (box.contact k).direction

instance {ι : Type} [Fintype ι] [Nonempty ι]
    (polyQ : Polyhedron ι (Fin 3 → ℚ)) (box : Box ι) :
    Decidable (box.dominates polyQ) := by
  unfold Box.dominates
  infer_instance

@[mk_iff]
structure Box.Valid {ι : Type} [Fintype ι] [Nonempty ι]
    (polyQ : Polyhedron ι (Fin 3 → ℚ)) (box : Box ι) : Prop where
  center_in_four : box.center ∈ fourInterval ℚ
  direction_unit : ∀ k, (box.contact k).unit
  weight_nonneg : ∀ k, 0 ≤ (box.contact k).weight
  weight_pos : ∃ k, 0 < (box.contact k).weight
  balanced : box.balanced
  dominates : box.dominates polyQ

instance {ι : Type} [Fintype ι] [Nonempty ι]
    (polyQ : Polyhedron ι (Fin 3 → ℚ)) (box : Box ι) :
    Decidable (box.Valid polyQ) :=
  decidable_of_iff _ (Box.valid_iff polyQ box).symm

private theorem direction_norm_eq_one {ι : Type} {contact : Contact ι}
    (h : contact.unit) : ‖toR2 contact.direction‖ = 1 := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_one]
  congr 1
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, toR2,
    WithLp.ofLp_toLp]
  exact_mod_cast h

lemma Box.εθ₁_nonneg {ι : Type} (box : Box ι) : 0 ≤ box.εθ₁ :=
  div_nonneg
    (sub_nonneg.mpr ((Pose.le_iff _ _).mp box.interval.min_le_max).1)
    (by norm_num)

lemma Box.εφ₁_nonneg {ι : Type} (box : Box ι) : 0 ≤ box.εφ₁ :=
  div_nonneg
    (sub_nonneg.mpr ((Pose.le_iff _ _).mp box.interval.min_le_max).2.2.1)
    (by norm_num)

lemma Box.εθ₂_nonneg {ι : Type} (box : Box ι) : 0 ≤ box.εθ₂ :=
  div_nonneg
    (sub_nonneg.mpr ((Pose.le_iff _ _).mp box.interval.min_le_max).2.1)
    (by norm_num)

lemma Box.εφ₂_nonneg {ι : Type} (box : Box ι) : 0 ≤ box.εφ₂ :=
  div_nonneg
    (sub_nonneg.mpr ((Pose.le_iff _ _).mp box.interval.min_le_max).2.2.2.1)
    (by norm_num)

lemma Box.εα_nonneg {ι : Type} (box : Box ι) : 0 ≤ box.εα :=
  div_nonneg
    (sub_nonneg.mpr ((Pose.le_iff _ _).mp box.interval.min_le_max).2.2.2.2)
    (by norm_num)

def Box.realInterval {ι : Type} (box : Box ι) : PoseInterval ℝ :=
  PoseInterval.mk box.interval.min.toReal box.interval.max.toReal (by
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      (Pose.le_iff _ _).mp box.interval.min_le_max
    rw [Pose.le_iff]
    simp only [Pose.toReal_θ₁, Pose.toReal_θ₂, Pose.toReal_φ₁,
      Pose.toReal_φ₂, Pose.toReal_α]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2,
      by exact_mod_cast h3, by exact_mod_cast h4, by exact_mod_cast h5⟩)

theorem Box.near_center_of_mem_realInterval {ι : Type} (box : Box ι)
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [Box.center, Pose.toReal_θ₁, Pose.toReal_θ₂,
      Pose.toReal_φ₁, Pose.toReal_φ₂, Pose.toReal_α,
      Box.εθ₁, Box.εφ₁, Box.εθ₂, Box.εφ₂, Box.εα]
    rw [abs_sub_le_iff]
    push_cast
    constructor <;> linarith

/-- A valid generic box excludes every planar translation throughout it. -/
theorem Box.valid_imp_not_translated_rupert
    {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (polyQ : Polyhedron ι (Fin 3 → ℚ))
    (approx : RationalApprox.κApproxPoly poly.vertices polyQ)
    (box : Box ι) (h : box.Valid polyQ) :
    ∀ q, Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
        (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q →
      ∀ offset : ℝ²,
        ¬ RupertPose (q.matrixPoseWithOffset offset) poly.hull := by
  let pc : RationalBalancedGlobalPrecondition
      poly polyQ approx box.center box.εα box.εθ₁ box.εφ₁ box.εθ₂ box.εφ₂ := {
    innerIndex := fun k => (box.contact k).innerIndex
    outerIndex := fun k => (box.contact k).outerIndex
    direction := fun k => (box.contact k).direction
    direction_unit := fun k => direction_norm_eq_one (h.direction_unit k)
    weight := fun k => (box.contact k).weight
    weight_nonneg := h.weight_nonneg
    weight_pos := h.weight_pos
    balance := h.balanced
    p_in_4 := h.center_in_four
    dominates := h.dominates
  }
  exact rational_balanced_global box.center box.εα box.εθ₁ box.εφ₁
    box.εθ₂ box.εφ₂ box.εα_nonneg box.εθ₁_nonneg box.εφ₁_nonneg
    box.εθ₂_nonneg box.εφ₂_nonneg poly polyQ approx pc

theorem Box.valid_imp_no_translated_rupert_in_interval
    {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (polyQ : Polyhedron ι (Fin 3 → ℚ))
    (approx : RationalApprox.κApproxPoly poly.vertices polyQ)
    (box : Box ι) (h : box.Valid polyQ) :
    ¬ ∃ q ∈ box.realInterval, ∃ offset : ℝ²,
      RupertPose (q.matrixPoseWithOffset offset) poly.hull := by
  rintro ⟨q, hq, offset, hrupert⟩
  exact box.valid_imp_not_translated_rupert poly polyQ approx h q
    (box.near_center_of_mem_realInterval hq) offset hrupert

end Noperthedron.BalancedSupport.RationalCertificate

end
