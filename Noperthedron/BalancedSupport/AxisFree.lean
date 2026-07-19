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

noncomputable def xAxis3 : ℝ³ := !₂[1, 0, 0]
noncomputable def yAxis3 : ℝ³ := !₂[0, 1, 0]
noncomputable def zAxis3 : ℝ³ := !₂[0, 0, 1]

/-- A linear functional on a finite convex hull is no larger than its value
at some generating point. -/
theorem exists_inner_ge_of_mem_convexHull
    {J : Type} [Fintype J] [Nonempty J]
    (a : J → ℝ³) (x ω : ℝ³)
    (hx : x ∈ convexHull ℝ {a j | j}) :
    ∃ j, ⟪ω, x⟫ ≤ ⟪ω, a j⟫ := by
  by_contra h
  push Not at h
  have hopen : convexHull ℝ {a j | j} ⊆ {y : ℝ³ | ⟪ω, y⟫ < ⟪ω, x⟫} := by
    refine convexHull_min ?_
      (convex_halfSpace_lt (innerSL ℝ ω).toLinearMap.isLinear ⟪ω, x⟫)
    rintro y ⟨j, rfl⟩
    exact h j
  exact (lt_irrefl ⟪ω, x⟫) (hopen hx)

/-- Explicit barycentric coordinates give a compact finite convex-hull
certificate. -/
theorem mem_convexHull_of_barycentric
    {J : Type} [Fintype J] [Nonempty J]
    (a : J → ℝ³) (weight : J → ℝ) (x : ℝ³)
    (hweight : ∀ j, 0 ≤ weight j) (hsum : ∑ j, weight j = 1)
    (hpoint : ∑ j, weight j • a j = x) :
    x ∈ convexHull ℝ {a j | j} := by
  have hcenter := Finset.univ.centerMass_mem_convexHull
    (s := {a j | j}) (w := weight) (z := a)
    (fun j _ => hweight j) (by simp [hsum]) (fun j _ => ⟨j, rfl⟩)
  rw [Finset.centerMass_eq_of_sum_1 _ _ hsum] at hcenter
  exact hpoint ▸ hcenter

private theorem unit_has_large_coordinate (axis : ℝ³) (haxis : ‖axis‖ = 1) :
    (4 / 7 : ℝ) ≤ |axis 0| ∨ (4 / 7 : ℝ) ≤ |axis 1| ∨
      (4 / 7 : ℝ) ≤ |axis 2| := by
  have hsq : axis 0 ^ 2 + axis 1 ^ 2 + axis 2 ^ 2 = 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2) haxis
    simpa [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three] using h
  by_contra h
  push Not at h
  obtain ⟨h0, h1, h2⟩ := h
  have hsq0 : axis 0 ^ 2 < (4 / 7 : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).2 h0
  have hsq1 : axis 1 ^ 2 < (4 / 7 : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).2 h1
  have hsq2 : axis 2 ^ 2 < (4 / 7 : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).2 h2
  nlinarith

/-- Six rational convex-hull witnesses certify axis coverage.  The constant
`7/4` is a rational upper bound for `√3`; its slack is only `1/49` after
squaring. -/
theorem octahedral_axis_cover
    {J : Type} [Fintype J] [Nonempty J]
    (a : J → ℝ³) (c : ℝ) (hc : 0 ≤ c)
    (hxp : (7 / 4 * c) • xAxis3 ∈ convexHull ℝ {a j | j})
    (hxn : (- (7 / 4 * c)) • xAxis3 ∈ convexHull ℝ {a j | j})
    (hyp : (7 / 4 * c) • yAxis3 ∈ convexHull ℝ {a j | j})
    (hyn : (- (7 / 4 * c)) • yAxis3 ∈ convexHull ℝ {a j | j})
    (hzp : (7 / 4 * c) • zAxis3 ∈ convexHull ℝ {a j | j})
    (hzn : (- (7 / 4 * c)) • zAxis3 ∈ convexHull ℝ {a j | j})
    (axis : ℝ³) (haxis : ‖axis‖ = 1) :
    ∃ j, c ≤ ⟪axis, a j⟫ := by
  rcases unit_has_large_coordinate axis haxis with hx | hy | hz
  · by_cases hs : 0 ≤ axis 0
    · obtain ⟨j, hj⟩ := exists_inner_ge_of_mem_convexHull a _ axis hxp
      refine ⟨j, ?_⟩
      rw [abs_of_nonneg hs] at hx
      have hpoint : c ≤ ⟪axis, (7 / 4 * c) • xAxis3⟫ := by
        simp [xAxis3, PiLp.inner_apply, Fin.sum_univ_three]
        nlinarith
      exact hpoint.trans hj
    · obtain ⟨j, hj⟩ := exists_inner_ge_of_mem_convexHull a _ axis hxn
      refine ⟨j, ?_⟩
      rw [abs_of_nonpos (le_of_not_ge hs)] at hx
      have hpoint : c ≤ ⟪axis, (- (7 / 4 * c)) • xAxis3⟫ := by
        simp [xAxis3, PiLp.inner_apply, Fin.sum_univ_three]
        nlinarith
      exact hpoint.trans hj
  · by_cases hs : 0 ≤ axis 1
    · obtain ⟨j, hj⟩ := exists_inner_ge_of_mem_convexHull a _ axis hyp
      refine ⟨j, ?_⟩
      rw [abs_of_nonneg hs] at hy
      have hpoint : c ≤ ⟪axis, (7 / 4 * c) • yAxis3⟫ := by
        simp [yAxis3, PiLp.inner_apply, Fin.sum_univ_three]
        nlinarith
      exact hpoint.trans hj
    · obtain ⟨j, hj⟩ := exists_inner_ge_of_mem_convexHull a _ axis hyn
      refine ⟨j, ?_⟩
      rw [abs_of_nonpos (le_of_not_ge hs)] at hy
      have hpoint : c ≤ ⟪axis, (- (7 / 4 * c)) • yAxis3⟫ := by
        simp [yAxis3, PiLp.inner_apply, Fin.sum_univ_three]
        nlinarith
      exact hpoint.trans hj
  · by_cases hs : 0 ≤ axis 2
    · obtain ⟨j, hj⟩ := exists_inner_ge_of_mem_convexHull a _ axis hzp
      refine ⟨j, ?_⟩
      rw [abs_of_nonneg hs] at hz
      have hpoint : c ≤ ⟪axis, (7 / 4 * c) • zAxis3⟫ := by
        simp [zAxis3, PiLp.inner_apply, Fin.sum_univ_three]
        nlinarith
      exact hpoint.trans hj
    · obtain ⟨j, hj⟩ := exists_inner_ge_of_mem_convexHull a _ axis hzn
      refine ⟨j, ?_⟩
      rw [abs_of_nonpos (le_of_not_ge hs)] at hz
      have hpoint : c ≤ ⟪axis, (- (7 / 4 * c)) • zAxis3⟫ := by
        simp [zAxis3, PiLp.inner_apply, Fin.sum_univ_three]
        nlinarith
      exact hpoint.trans hj

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

/-- Pointwise axis coverage transfers under a uniform perturbation. -/
theorem exists_inner_ge_of_cover_of_perturbation
    {J : Type} [Fintype J] [Nonempty J]
    (center current : J → ℝ³) (c δ : ℝ)
    (hcover : ∀ ω : ℝ³, ‖ω‖ = 1 → ∃ j, c + δ ≤ ⟪ω, center j⟫)
    (hmove : ∀ j, ‖current j - center j‖ ≤ δ)
    (ω : ℝ³) (hω : ‖ω‖ = 1) :
    ∃ j, c ≤ ⟪ω, current j⟫ := by
  obtain ⟨j, hj⟩ := hcover ω hω
  have hinner := abs_real_inner_le_norm ω (current j - center j)
  rw [hω, one_mul] at hinner
  have hlower : -δ ≤ ⟪ω, current j - center j⟫ := by
    have habs : |⟪ω, current j - center j⟫| ≤ δ := hinner.trans (hmove j)
    exact (abs_le.mp habs).1
  refine ⟨j, ?_⟩
  rw [inner_sub_right] at hlower
  linarith

/-- Axis coverage is stable under pointwise perturbation.  It is enough that
the center vectors contain a slightly larger ball; no set-containment result
for the perturbed convex hull is needed. -/
theorem exists_inner_ge_of_ball_subset_convexHull_of_perturbation
    {J : Type} [Fintype J] [Nonempty J]
    (center current : J → ℝ³) (c δ : ℝ) (hcδ : 0 ≤ c + δ)
    (hball : Metric.closedBall (0 : ℝ³) (c + δ) ⊆
      convexHull ℝ {center j | j})
    (hmove : ∀ j, ‖current j - center j‖ ≤ δ)
    (ω : ℝ³) (hω : ‖ω‖ = 1) :
    ∃ j, c ≤ ⟪ω, current j⟫ := by
  apply exists_inner_ge_of_cover_of_perturbation center current c δ
    (fun axis haxis => exists_inner_ge_of_ball_subset_convexHull
      center (c + δ) hcδ hball axis haxis) hmove ω hω

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

/-- Perturbation-stable version of axis-free certificate selection.  The
larger ball is checked only once at the center configuration, while each
current normalized first-variation vector merely needs a norm error bound. -/
theorem exists_axis_certificate_dominating_remainder_of_perturbation
    {J : Type} [Fintype J] [Nonempty J]
    (center a A : J → ℝ³) (B : J → ℝ) (c δ sinCoeff bendCoeff : ℝ)
    (hcδ : 0 ≤ c + δ) (hsin : 0 ≤ sinCoeff) (hB : ∀ j, 0 < B j)
    (hA : ∀ j, A j = B j • a j)
    (hball : Metric.closedBall (0 : ℝ³) (c + δ) ⊆
      convexHull ℝ {center j | j})
    (hmove : ∀ j, ‖a j - center j‖ ≤ δ)
    (hratio : bendCoeff ≤ sinCoeff * c)
    (ω : ℝ³) (hω : ‖ω‖ = 1) :
    ∃ j, bendCoeff * B j ≤ sinCoeff * ⟪ω, A j⟫ := by
  obtain ⟨j, hj⟩ :=
    exists_inner_ge_of_ball_subset_convexHull_of_perturbation
      center a c δ hcδ hball hmove ω hω
  have hscaled : c * B j ≤ ⟪ω, A j⟫ := by
    rw [hA j, real_inner_smul_right]
    nlinarith [hB j]
  refine ⟨j, ?_⟩
  have hratioB : bendCoeff * B j ≤ sinCoeff * c * B j :=
    mul_le_mul_of_nonneg_right hratio (hB j).le
  have hscaled' : sinCoeff * (c * B j) ≤ sinCoeff * ⟪ω, A j⟫ :=
    mul_le_mul_of_nonneg_left hscaled hsin
  linarith

/-- Version driven by a direct center axis-coverage certificate. -/
theorem exists_axis_certificate_dominating_remainder_of_cover_perturbation
    {J : Type} [Fintype J] [Nonempty J]
    (center a A : J → ℝ³) (B : J → ℝ) (c δ sinCoeff bendCoeff : ℝ)
    (hsin : 0 ≤ sinCoeff) (hB : ∀ j, 0 < B j)
    (hA : ∀ j, A j = B j • a j)
    (hcover : ∀ axis : ℝ³, ‖axis‖ = 1 →
      ∃ j, c + δ ≤ ⟪axis, center j⟫)
    (hmove : ∀ j, ‖a j - center j‖ ≤ δ)
    (hratio : bendCoeff ≤ sinCoeff * c)
    (ω : ℝ³) (hω : ‖ω‖ = 1) :
    ∃ j, bendCoeff * B j ≤ sinCoeff * ⟪ω, A j⟫ := by
  obtain ⟨j, hj⟩ := exists_inner_ge_of_cover_of_perturbation
    center a c δ hcover hmove ω hω
  have hscaled : c * B j ≤ ⟪ω, A j⟫ := by
    rw [hA j, real_inner_smul_right]
    nlinarith [hB j]
  refine ⟨j, ?_⟩
  have hratioB : bendCoeff * B j ≤ sinCoeff * c * B j :=
    mul_le_mul_of_nonneg_right hratio (hB j).le
  have hscaled' : sinCoeff * (c * B j) ≤ sinCoeff * ⟪ω, A j⟫ :=
    mul_le_mul_of_nonneg_left hscaled hsin
  linarith

end Noperthedron.BalancedSupport

end
