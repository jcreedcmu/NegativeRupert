module

public import Noperthedron.BalancedSupport.FiniteRotation

@[expose] public section


/-!
# Eliminating the rotation axis

A finite family of normalized first-variation vectors covers every rotation
axis when its convex hull contains a ball centered at the origin.
-/

namespace Noperthedron.BalancedSupport

open scoped RealInnerProductSpace

/-- Ball containment in a finite convex hull supplies a vector with a large
inner product in every unit direction. -/
theorem exists_inner_ge_of_ball_subset_convexHull
    {J : Type} [Fintype J] [Nonempty J]
    (a : J → ℝ³) (c : ℝ) (hc : 0 ≤ c)
    (hball : Metric.closedBall (0 : ℝ³) c ⊆ convexHull ℝ {a j | j})
    (ω : ℝ³) (hω : ‖ω‖ = 1) :
    ∃ j, c ≤ ⟪ω, a j⟫ := by
  by_contra h
  push Not at h
  have hpoint : c • ω ∈ Metric.closedBall (0 : ℝ³) c := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hω, mul_one,
      Real.norm_eq_abs, abs_of_nonneg hc]
  have hhull : c • ω ∈ convexHull ℝ {a j | j} := hball hpoint
  have hopen : convexHull ℝ {a j | j} ⊆ {x : ℝ³ | ⟪ω, x⟫ < c} := by
    refine convexHull_min ?_ (convex_halfSpace_lt (innerSL ℝ ω).toLinearMap.isLinear c)
    rintro x ⟨j, rfl⟩
    exact h j
  have hlt := hopen hhull
  simp only [Set.mem_setOf_eq, real_inner_smul_right, real_inner_self_eq_norm_sq, hω,
    one_pow, mul_one] at hlt
  exact (lt_irrefl c) hlt

/-- Version with unnormalized vectors `A j = B j • a j`. -/
theorem exists_scaled_inner_ge_of_ball_subset_convexHull
    {J : Type} [Fintype J] [Nonempty J]
    (a A : J → ℝ³) (B : J → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hB : ∀ j, 0 < B j) (hA : ∀ j, A j = B j • a j)
    (hball : Metric.closedBall (0 : ℝ³) c ⊆ convexHull ℝ {a j | j})
    (ω : ℝ³) (hω : ‖ω‖ = 1) :
    ∃ j, c * B j ≤ ⟪ω, A j⟫ := by
  obtain ⟨j, hj⟩ := exists_inner_ge_of_ball_subset_convexHull a c hc hball ω hω
  refine ⟨j, ?_⟩
  rw [hA j, real_inner_smul_right]
  nlinarith [hB j]

/-- If the bend/first coefficient ratio is at most the ball radius, the
axis-free family contains a certificate whose first term dominates its
remainder budget. -/
theorem exists_axis_certificate_dominating_remainder
    {J : Type} [Fintype J] [Nonempty J]
    (a A : J → ℝ³) (B : J → ℝ) (c sinCoeff bendCoeff : ℝ)
    (hc : 0 ≤ c) (hsin : 0 ≤ sinCoeff) (hB : ∀ j, 0 < B j)
    (hA : ∀ j, A j = B j • a j)
    (hball : Metric.closedBall (0 : ℝ³) c ⊆ convexHull ℝ {a j | j})
    (hratio : bendCoeff ≤ sinCoeff * c)
    (ω : ℝ³) (hω : ‖ω‖ = 1) :
    ∃ j, bendCoeff * B j ≤ sinCoeff * ⟪ω, A j⟫ := by
  obtain ⟨j, hj⟩ :=
    exists_scaled_inner_ge_of_ball_subset_convexHull a A B c hc hB hA hball ω hω
  refine ⟨j, ?_⟩
  have hratioB : bendCoeff * B j ≤ sinCoeff * c * B j :=
    mul_le_mul_of_nonneg_right hratio (hB j).le
  have hj' : sinCoeff * (c * B j) ≤ sinCoeff * ⟪ω, A j⟫ :=
    mul_le_mul_of_nonneg_left hj hsin
  linarith

end Noperthedron.BalancedSupport

end
