module

public import Noperthedron.RationalApprox.RationalBalancedGlobal
public import Noperthedron.SnubCube.Normalized

@[expose] public section


/-!
# Decidable snub-cube box certificates

The computational certificate uses exactly three contacts.  Directions and
weights are stored as rationals; unit length, nonnegativity, exact balance,
and the aggregate global inequality are all decidable rational statements.
The same `Valid` proposition is intended to be consumed by both `decide
+kernel` and `native_decide`.
-/

namespace Noperthedron.SnubCube.Certificate

open RationalApprox.GlobalTheorem

structure Contact where
  innerIndex : VertexIndex
  outerIndex : VertexIndex
  direction : Fin 2 → ℚ
  weight : ℚ
deriving DecidableEq, Repr

structure Box where
  interval : PoseInterval ℚ
  contact : Fin 3 → Contact

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

def Contact.unit (c : Contact) : Prop :=
  c.direction 0 ^ 2 + c.direction 1 ^ 2 = 1

instance (c : Contact) : Decidable c.unit := by
  unfold Contact.unit
  infer_instance

def Box.balanced (box : Box) : Prop :=
  ∑ k, (box.contact k).weight • (box.contact k).direction = 0

instance (box : Box) : Decidable box.balanced := by
  unfold Box.balanced
  infer_instance

def Box.dominates (box : Box) : Prop :=
  ∑ k, (box.contact k).weight *
      maxHℚ box.center normalizedRationalPolyhedron box.εθ₂ box.εφ₂
        (box.contact k).direction ≤
    ∑ k, (box.contact k).weight *
      Gℚ box.center box.εα box.εθ₁ box.εφ₁
        (normalizedRationalVertex (box.contact k).innerIndex)
        (box.contact k).direction

instance (box : Box) : Decidable box.dominates := by
  unfold Box.dominates
  infer_instance

@[mk_iff]
structure Box.Valid (box : Box) : Prop where
  center_in_four : box.center ∈ fourInterval ℚ
  direction_unit : ∀ k, (box.contact k).unit
  weight_nonneg : ∀ k, 0 ≤ (box.contact k).weight
  weight_pos : ∃ k, 0 < (box.contact k).weight
  balanced : box.balanced
  dominates : box.dominates

instance (box : Box) : Decidable box.Valid :=
  decidable_of_iff _ (Box.valid_iff box).symm

private theorem direction_norm_eq_one {c : Contact} (h : c.unit) :
    ‖toR2 c.direction‖ = 1 := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_one]
  congr 1
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, toR2,
    WithLp.ofLp_toLp]
  exact_mod_cast h

lemma Box.εθ₁_nonneg (box : Box) : 0 ≤ box.εθ₁ :=
  div_nonneg (sub_nonneg.mpr ((Pose.le_iff _ _).mp box.interval.min_le_max).1) (by norm_num)

lemma Box.εφ₁_nonneg (box : Box) : 0 ≤ box.εφ₁ :=
  div_nonneg (sub_nonneg.mpr ((Pose.le_iff _ _).mp box.interval.min_le_max).2.2.1) (by norm_num)

lemma Box.εθ₂_nonneg (box : Box) : 0 ≤ box.εθ₂ :=
  div_nonneg (sub_nonneg.mpr ((Pose.le_iff _ _).mp box.interval.min_le_max).2.1) (by norm_num)

lemma Box.εφ₂_nonneg (box : Box) : 0 ≤ box.εφ₂ :=
  div_nonneg (sub_nonneg.mpr ((Pose.le_iff _ _).mp box.interval.min_le_max).2.2.2.1) (by norm_num)

lemma Box.εα_nonneg (box : Box) : 0 ≤ box.εα :=
  div_nonneg (sub_nonneg.mpr ((Pose.le_iff _ _).mp box.interval.min_le_max).2.2.2.2) (by norm_num)

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

/-- A valid decidable box certificate rules out every translated Euler pose in
the represented interval. -/
theorem valid_imp_not_translated_rupert (box : Box) (h : box.Valid) :
    ∀ q, Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
        (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q →
      ∀ offset : ℝ²,
        ¬ RupertPose (q.matrixPoseWithOffset offset) normalizedGoodPoly.hull := by
  let pc : RationalBalancedGlobalPrecondition
      normalizedGoodPoly normalizedRationalPolyhedron normalizedApproximation
      box.center (box.εα) (box.εθ₁) (box.εφ₁) (box.εθ₂) (box.εφ₂) := {
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
  exact rational_balanced_global box.center box.εα box.εθ₁ box.εφ₁ box.εθ₂ box.εφ₂
    box.εα_nonneg box.εθ₁_nonneg box.εφ₁_nonneg box.εθ₂_nonneg box.εφ₂_nonneg
    normalizedGoodPoly normalizedRationalPolyhedron normalizedApproximation pc

/-- Interval form consumed by the solution-tree induction. -/
theorem valid_imp_no_translated_rupert_in_interval (box : Box) (h : box.Valid) :
    ¬ ∃ q ∈ box.realInterval, ∃ offset : ℝ²,
      RupertPose (q.matrixPoseWithOffset offset) normalizedGoodPoly.hull := by
  rintro ⟨q, hq, offset, hrupert⟩
  exact valid_imp_not_translated_rupert box h q
    (box.near_center_of_mem_realInterval hq) offset hrupert

end Noperthedron.SnubCube.Certificate

end
