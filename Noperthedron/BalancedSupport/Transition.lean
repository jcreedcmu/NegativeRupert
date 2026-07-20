module

public import Noperthedron.BalancedSupport.AxisFree

@[expose] public section


/-!
# Scale-invariant transition estimates

Near a silhouette transition, let `d` bound distance of the view from the
transition and let `x = tan(s / 2)` measure relative rotation.  A regular
exact-support certificate handles `x ≤ k d`.  In the complementary wedge a
defect certificate has normalized displacement

`2 x (c - x) / (1 + x²) - D d`.

The lemma below gives a denominator-free finite check ensuring that this
second expression is nonnegative throughout a bounded transition chart.
-/

namespace Noperthedron.BalancedSupport

open scoped RealInnerProductSpace

/-- Finite-rotation estimate with a nonzero support-defect target.  This is
the ordered-algebra core of a transition certificate: the favorable first
variation must pay both the Rodrigues remainder and the support deficit. -/
theorem weighted_displacement_ge_defect_of_first_remainder
    {κ : Type} [Fintype κ]
    (μ displacement first remainder bound : κ → ℝ)
    (sinCoeff bendCoeff totalDefect : ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hbend : 0 ≤ bendCoeff)
    (hdecomp : ∀ i,
      displacement i = sinCoeff * first i + bendCoeff * remainder i)
    (hremainder : ∀ i, -bound i ≤ remainder i)
    (hdominates : bendCoeff * (∑ i, μ i * bound i) + totalDefect ≤
      sinCoeff * (∑ i, μ i * first i)) :
    totalDefect ≤ ∑ i, μ i * displacement i := by
  have hrem := weighted_remainder_lower_bound μ remainder bound hμ hremainder
  have hrem' :
      -(bendCoeff * ∑ i, μ i * bound i) ≤
        bendCoeff * ∑ i, μ i * remainder i := by
    calc
      -(bendCoeff * ∑ i, μ i * bound i) =
          bendCoeff * (-(∑ i, μ i * bound i)) := by ring
      _ ≤ bendCoeff * ∑ i, μ i * remainder i :=
        mul_le_mul_of_nonneg_left hrem hbend
  have heq :
      ∑ i, μ i * displacement i =
        sinCoeff * (∑ i, μ i * first i) +
          bendCoeff * (∑ i, μ i * remainder i) := by
    calc
      ∑ i, μ i * displacement i =
          ∑ i, (sinCoeff * (μ i * first i) +
            bendCoeff * (μ i * remainder i)) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hdecomp i]
              ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [heq]
  linarith

/-- Axis-free selection with a support-defect allowance.  Compared with the
ordinary local theorem, each candidate's first variation now pays an
additional generated bound `defect j`. -/
theorem exists_axis_certificate_dominating_remainder_and_defect
    {J : Type} [Fintype J] [Nonempty J]
    (center current A : J → ℝ³) (B defect : J → ℝ)
    (c δ sinCoeff bendCoeff : ℝ)
    (hsin : 0 ≤ sinCoeff) (hB : ∀ j, 0 < B j)
    (hA : ∀ j, A j = B j • current j)
    (hcover : ∀ axis : ℝ³, ‖axis‖ = 1 →
      ∃ j, c + δ ≤ ⟪axis, center j⟫)
    (hmove : ∀ j, ‖current j - center j‖ ≤ δ)
    (hbudget : ∀ j,
      bendCoeff * B j + defect j ≤ sinCoeff * c * B j)
    (axis : ℝ³) (haxis : ‖axis‖ = 1) :
    ∃ j, bendCoeff * B j + defect j ≤ sinCoeff * ⟪axis, A j⟫ := by
  obtain ⟨j, hj⟩ := exists_inner_ge_of_cover_of_perturbation
    center current c δ hcover hmove axis haxis
  have hscaled : c * B j ≤ ⟪axis, A j⟫ := by
    rw [hA j, real_inner_smul_right]
    nlinarith [hB j]
  refine ⟨j, (hbudget j).trans ?_⟩
  calc
    sinCoeff * c * B j = sinCoeff * (c * B j) := by ring
    _ ≤ sinCoeff * ⟪axis, A j⟫ :=
      mul_le_mul_of_nonneg_left hscaled hsin

/-- The Cayley/Rodrigues gain per unit rotation decreases as the rotation
parameter grows on `[0, 1]`.  This fact is stated in the form needed by the
transition overlap estimate. -/
theorem cayley_gain_ratio_anti
    {c x r : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hxr : x ≤ r) (hr : r ≤ 1) :
    (c - r) / (1 + r ^ 2) ≤ (c - x) / (1 + x ^ 2) := by
  have hr0 : 0 ≤ r := hx.trans hxr
  have hrx : r * x ≤ 1 := by
    calc
      r * x ≤ r * r := mul_le_mul_of_nonneg_left hxr hr0
      _ ≤ 1 := by nlinarith [sq_nonneg (1 - r)]
  have hfactor : 0 ≤ 1 + c * (r + x) - r * x := by
    have hcrx : 0 ≤ c * (r + x) :=
      mul_nonneg hc (add_nonneg hr0 hx)
    linarith
  have hproduct : 0 ≤ (r - x) * (1 + c * (r + x) - r * x) :=
    mul_nonneg (sub_nonneg.mpr hxr) hfactor
  have hcross :
      (c - r) * (1 + x ^ 2) ≤ (c - x) * (1 + r ^ 2) := by
    nlinarith
  exact (div_le_div_iff₀ (by positivity : 0 < 1 + r ^ 2)
    (by positivity : 0 < 1 + x ^ 2)).2 hcross

/-- Sufficient overlap condition for a defect certificate in the
complementary transition wedge `k d ≤ x`.

The hypothesis `D * (1 + r²) ≤ 2 k (c-r)` is rational-polynomial when all
chart constants are rational, so it is suitable for an executable generated
certificate. -/
theorem defect_dominated_in_transition_wedge
    {c r D k d x : ℝ}
    (hc : 0 ≤ c) (hr1 : r ≤ 1)
    (hD : 0 ≤ D) (hk : 0 < k) (hd : 0 ≤ d)
    (hx : 0 ≤ x) (hxr : x ≤ r) (hwedge : k * d ≤ x)
    (hoverlap : D * (1 + r ^ 2) ≤ 2 * k * (c - r)) :
    D * d ≤ 2 * x * (c - x) / (1 + x ^ 2) := by
  have hcr : 0 ≤ c - r := by
    have hleft : 0 ≤ D * (1 + r ^ 2) :=
      mul_nonneg hD (by positivity)
    have hright : 0 ≤ 2 * k * (c - r) := hleft.trans hoverlap
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hoverlap hd
  have hwedgeScaled :
      (k * d) * (2 * (c - r)) ≤ x * (2 * (c - r)) :=
    mul_le_mul_of_nonneg_right hwedge
      (mul_nonneg (by norm_num) hcr)
  have hcoarse :
      D * d ≤ 2 * x * (c - r) / (1 + r ^ 2) := by
    rw [le_div_iff₀ (by positivity : 0 < 1 + r ^ 2)]
    nlinarith
  have hratio := cayley_gain_ratio_anti hc hx hxr hr1
  have hgain :
      (2 * x) * ((c - r) / (1 + r ^ 2)) ≤
        (2 * x) * ((c - x) / (1 + x ^ 2)) :=
    mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) hx)
  calc
    D * d ≤ 2 * x * (c - r) / (1 + r ^ 2) := hcoarse
    _ = (2 * x) * ((c - r) / (1 + r ^ 2)) := by ring
    _ ≤ (2 * x) * ((c - x) / (1 + x ^ 2)) := hgain
    _ = 2 * x * (c - x) / (1 + x ^ 2) := by ring

/-- Once the regular and defect wedges overlap at `k d`, every point in the
transition chart is handled by one of the two obstruction arguments. -/
theorem transition_wedge_cases {d x k : ℝ} (regular defect : Prop)
    (hregular : x ≤ k * d → regular)
    (hdefect : k * d ≤ x → defect) :
    regular ∨ defect := by
  rcases le_total x (k * d) with h | h
  · exact Or.inl (hregular h)
  · exact Or.inr (hdefect h)

end Noperthedron.BalancedSupport

end
