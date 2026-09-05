module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Noperthedron.PoseInterval
public import Noperthedron.Global.Basic

@[expose] public section


/- [SY25] Lemma 20 -/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

-- FIXME: the fact that I can't find exactly this lemma with loogle on "sum" and EuclideanSpace.single
-- makes me think there's probably some nearby lemma that uses different tools, maybe?
lemma vector_rep {n : ℕ} (v : E n) : v = ∑ x, v.ofLp x • EuclideanSpace.single x 1 := by
  ext i; simp [Finset.sum_apply, Pi.single_apply]

lemma nth_partial_def {n : ℕ} (f : E n → ℝ) (v w : E n) :
    fderiv ℝ f w v = ∑ i, v i * nth_partial i f w := by
  unfold nth_partial
  rw [show ∑ i, v.ofLp i * (fderiv ℝ f w) (EuclideanSpace.single i 1)
         = (fderiv ℝ f w) (∑ x, v.ofLp x • EuclideanSpace.single x 1)
      by simp]
  congr
  exact vector_rep v

noncomputable
def interpolator {n : ℕ} (x y : E n) (t : ℝ) : E n :=
  (1 - t) • x + t • y

private theorem interpolator_has_deriv {n : ℕ} (x y : E n) (t : ℝ) :
    HasDerivAt (interpolator x y) (y - x) t := by
  convert! (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)) using 1
  ext1 t
  exact (AffineMap.lineMap_apply_module x y t).symm

noncomputable
def interpolated {n : ℕ} (x y : E n) (f : E n → ℝ) : ℝ → ℝ  :=
  f ∘ interpolator x y

noncomputable
def interpolated_deriv {n : ℕ} (x y : E n) (f : E n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, (y i - x i) * nth_partial i f ((1 - t) • x + t • y)

noncomputable
def interpolated_deriv2 {n : ℕ} (x y : E n) (f : E n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, (y i - x i) * (y j - x j) * (nth_partial i <| nth_partial j f) ((1 - t) • x + t • y)

lemma c2_imp_partials_differentiable {n : ℕ} {f : E n → ℝ} {i : Fin n} (fc : ContDiff ℝ 2 f) :
      Differentiable ℝ (nth_partial i f) := by
  have h_deriv : Differentiable ℝ (fderiv ℝ f) :=
    ContDiff.differentiable (n := 1) (by fun_prop) one_ne_zero
  exact h_deriv.clm_apply (differentiable_const _)

lemma c2_imp_partials_c1 {n : ℕ} {f : E n → ℝ} {j : Fin n} (fc : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (nth_partial j f) := by
  (apply ContDiff.fderiv_apply <;> try fun_prop); norm_num

/-- The chain rule along a segment: apply the differential to its direction `y - x`. -/
private theorem interpolated_has_deriv_of_differentiableAt {n : ℕ} (x y : E n)
    (f : E n → ℝ) (t : ℝ) (hf : DifferentiableAt ℝ f (interpolator x y t)) :
    HasDerivAt (interpolated x y f) (interpolated_deriv x y f t) t := by
  convert! hf.hasFDerivAt.comp_hasDerivAt t (interpolator_has_deriv x y t) using 1
  rw [nth_partial_def]
  rfl

theorem interpolated_has_deriv {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 2 f) (t : ℝ) :
    HasDerivAt (interpolated x y f) (interpolated_deriv x y f t) t :=
  interpolated_has_deriv_of_differentiableAt x y f t
    (fc.differentiable (by norm_num)).differentiableAt

theorem interpolated_has_deriv2 {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 2 f) (t : ℝ) :
    HasDerivAt (interpolated_deriv x y f) (interpolated_deriv2 x y f t) t := by
  have hd (i : Fin n) := interpolated_has_deriv_of_differentiableAt x y (nth_partial i f) t
    (c2_imp_partials_differentiable fc).differentiableAt
  convert! HasDerivAt.fun_sum fun i _ => (hd i).const_mul (y i - x i) using 1
  simp only [interpolated_deriv, interpolated_deriv2, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  ring

theorem deriv_interpolated {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 2 f) :
    deriv (interpolated x y f) = interpolated_deriv x y f := by
  ext t
  exact (interpolated_has_deriv x y f fc t).deriv

theorem deriv_interpolated2 {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 2 f) :
    deriv (interpolated_deriv x y f) = interpolated_deriv2 x y f := by
  ext t
  exact (interpolated_has_deriv2 x y f fc t).deriv

lemma c3_imp_partials_c2 {n : ℕ} {f : E n → ℝ} {j : Fin n} (fc : ContDiff ℝ 3 f) :
    ContDiff ℝ 2 (nth_partial j f) := by
  (apply ContDiff.fderiv_apply <;> try fun_prop); norm_num

lemma c3_imp_partials2_c1 {n : ℕ} {f : E n → ℝ} {i j : Fin n} (fc : ContDiff ℝ 3 f) :
    ContDiff ℝ 1 (nth_partial i (nth_partial j f)) :=
  c2_imp_partials_c1 (c3_imp_partials_c2 fc)

lemma c3_imp_partials2_differentiable {n : ℕ} {f : E n → ℝ} {i j : Fin n}
    (fc : ContDiff ℝ 3 f) : Differentiable ℝ (nth_partial i (nth_partial j f)) :=
  c2_imp_partials_differentiable (c3_imp_partials_c2 fc)

noncomputable
def interpolated_deriv3 {n : ℕ} (x y : E n) (f : E n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, (y i - x i) * (y j - x j) * (y k - x k) *
    (nth_partial i <| nth_partial j <| nth_partial k f) ((1 - t) • x + t • y)

private
lemma sum_pow_three {n : ℕ} (ε : Fin n → ℝ) :
    (∑ i, ε i) ^ 3 = ∑ i, ∑ j, ∑ k, ε i * ε j * ε k := by
  rw [pow_succ, pow_two, Finset.sum_mul_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

private
lemma interpolated_deriv3_bound {n : ℕ} (x y : E n) {f : E n → ℝ} {M : ℝ}
    (tpb : third_partials_bounded f M) {ε : Fin n → ℝ} (hε : ∀ i, 0 ≤ ε i)
    (hdiff : (i : Fin n) → |x i - y i| ≤ ε i) (t : ℝ) :
    |interpolated_deriv3 x y f t| ≤ M * (∑ i, ε i)^3 := by
  calc |interpolated_deriv3 x y f t|
  _ ≤ ∑ i, |∑ j, ∑ k, (y i - x i) * (y j - x j) * (y k - x k) *
      nth_partial i (nth_partial j (nth_partial k f)) ((1 - t) • x + t • y)| := by
    apply Finset.abs_sum_le_sum_abs
  _ ≤ ∑ i, ∑ j, |∑ k, (y i - x i) * (y j - x j) * (y k - x k) *
      nth_partial i (nth_partial j (nth_partial k f)) ((1 - t) • x + t • y)| := by
    refine Finset.sum_le_sum ?_; intro i hi;
    apply Finset.abs_sum_le_sum_abs
  _ ≤ ∑ i, ∑ j, ∑ k, |(y i - x i) * (y j - x j) * (y k - x k) *
      nth_partial i (nth_partial j (nth_partial k f)) ((1 - t) • x + t • y)| := by
    refine Finset.sum_le_sum ?_; intro i hi;
    refine Finset.sum_le_sum ?_; intro j hj;
    apply Finset.abs_sum_le_sum_abs
  _ = ∑ i, ∑ j, ∑ k, |(y i - x i)| * |(y j - x j)| * |(y k - x k)| *
      |nth_partial i (nth_partial j (nth_partial k f)) ((1 - t) • x + t • y)| := by
    conv => enter [1, 2, i, 2, j, 2, k]; repeat rw [abs_mul];
  _ ≤ ∑ i, ∑ j, ∑ k, ε i * ε j * ε k * M := by
    refine Finset.sum_le_sum ?_; intro i hi;
    refine Finset.sum_le_sum ?_; intro j hj;
    refine Finset.sum_le_sum ?_; intro k hk;
    have hεi := hε i
    have hεj := hε j
    have hεk := hε k
    rw [abs_sub_comm]; grw [hdiff i]
    rw [abs_sub_comm]; grw [hdiff j]
    rw [abs_sub_comm]; grw [hdiff k]
    unfold third_partials_bounded at tpb; grw [tpb]
  _ = M * (∑ i, ε i)^3 := by
    simp only [← Finset.sum_mul, sum_pow_three ε]
    ring

theorem interpolated_has_deriv3 {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 3 f) (t : ℝ) :
    HasDerivAt (interpolated_deriv2 x y f) (interpolated_deriv3 x y f t) t := by
  have hd (i j : Fin n) :=
    interpolated_has_deriv_of_differentiableAt x y (nth_partial i (nth_partial j f)) t
      (c3_imp_partials2_differentiable fc).differentiableAt
  convert! HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
    (hd i j).const_mul ((y i - x i) * (y j - x j)) using 1
  simp only [interpolated_deriv, interpolated_deriv3, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro k hk
  ring

theorem deriv_interpolated3 {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 3 f) :
    deriv (interpolated_deriv2 x y f) = interpolated_deriv3 x y f := by
  ext t
  exact (interpolated_has_deriv3 x y f fc t).deriv

theorem differentiable_deriv_interpolated2 {n : ℕ} (x y : E n) (f : E n → ℝ)
    (fc : ContDiff ℝ 3 f) : Differentiable ℝ (interpolated_deriv2 x y f) := by
  exact fun t => (interpolated_has_deriv3 x y f fc t).differentiableAt

theorem bounded_partials_control_difference2 {n : ℕ} (f : E n → ℝ)
    (fc : ContDiff ℝ 3 f) (x y : E n)
    (ε : Fin n → ℝ) (hε : ∀ i, 0 ≤ ε i) (hdiff : (i : Fin n) → |x i - y i| ≤ ε i)
    {M : ℝ} (tpb : third_partials_bounded f M) :
    |f x - f y| ≤ ∑ i, ε i * |nth_partial i f x|
      + (1/2) * ∑ i, ∑ j, ε i * ε j * |nth_partial i (nth_partial j f) x|
      + M * (∑ i, ε i)^3 / 6 := by
  let g := interpolated x y f
  let g' := interpolated_deriv x y f
  let g'' := interpolated_deriv2 x y f
  let g''' := interpolated_deriv3 x y f

  have fc2 : ContDiff ℝ 2 f := fc.of_le (by norm_num)
  have g_c3 : ContDiff ℝ 3 g := fc.comp (by unfold interpolator; fun_prop)

  have deriv_g_eq_g' : deriv g = g' := deriv_interpolated x y f fc2
  have deriv_g'_eq_g'' : deriv g' = g'' := deriv_interpolated2 x y f fc2
  have deriv_g''_eq_g''' : deriv g'' = g''' := deriv_interpolated3 x y f fc

  -- Taylor's theorem supplies the ordinary third derivative directly.
  obtain ⟨c, hc, htay⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := g) (x₀ := 0) (x := 1) (n := 2) (by norm_num) g_c3.contDiffOn
  have h_tay0 : taylorWithinEval g 2 (Set.uIcc 0 1) 0 1 = g 0 + g' 0 + g'' 0 / 2 := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_zero]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc zero_ne_one)
          (g_c3.of_le (by norm_num)).contDiffAt Set.left_mem_uIcc,
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc zero_ne_one)
          (g_c3.of_le (by norm_num)).contDiffAt Set.left_mem_uIcc,
        iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one,
        deriv_g_eq_g', deriv_g'_eq_g'']
    norm_num [Nat.factorial]
    ring
  rw [h_tay0, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
    deriv_g_eq_g', deriv_g'_eq_g'', deriv_g''_eq_g'''] at htay
  norm_num [Nat.factorial] at htay
  -- htay : g 1 - (g 0 + g' 0 + g'' 0 / 2) = g''' c / 6

  have bound1 : |g' 0| ≤ ∑ i, ε i * |nth_partial i f x| := by
    calc |g' 0|
    _ = |∑ i, (y i - x i) * nth_partial i f x| := by simp [g', interpolated_deriv]
    _ ≤ ∑ i, |(y i - x i) * nth_partial i f x| := by apply Finset.abs_sum_le_sum_abs
    _ = ∑ i, |(y i - x i)| * |nth_partial i f x| := by
      conv => enter [1, 2, i]; rw [abs_mul]
    _ = ∑ i, |(x i - y i)| * |nth_partial i f x| := by
      conv => enter [1, 2, i, 1]; rw [abs_sub_comm]
    _ ≤ ∑ i, ε i * |nth_partial i f x| := by
      refine Finset.sum_le_sum ?_; intro i hi; grw [hdiff i]

  have bound2 : |g'' 0| ≤ ∑ i, ∑ j, ε i * ε j * |nth_partial i (nth_partial j f) x| := by
    calc |g'' 0|
    _ = |∑ i, ∑ j, (y i - x i) * (y j - x j) * nth_partial i (nth_partial j f) x| := by
      simp [g'', interpolated_deriv2]
    _ ≤ ∑ i, |∑ j, (y i - x i) * (y j - x j) * nth_partial i (nth_partial j f) x| := by
      apply Finset.abs_sum_le_sum_abs
    _ ≤ ∑ i, ∑ j, |(y i - x i) * (y j - x j) * nth_partial i (nth_partial j f) x| := by
      refine Finset.sum_le_sum ?_; intro i hi;
      apply Finset.abs_sum_le_sum_abs
    _ = ∑ i, ∑ j, |(y i - x i)| * |(y j - x j)| * |nth_partial i (nth_partial j f) x| := by
      conv => enter [1, 2, i, 2, j]; repeat rw [abs_mul];
    _ ≤ ∑ i, ∑ j, ε i * ε j * |nth_partial i (nth_partial j f) x| := by
      refine Finset.sum_le_sum ?_; intro i hi;
      refine Finset.sum_le_sum ?_; intro j hj;
      have hεi := hε i
      rw [abs_sub_comm]; grw [hdiff i]
      rw [abs_sub_comm]; grw [hdiff j]

  have bound3 : |g''' c| ≤ M * (∑ i, ε i)^3 := interpolated_deriv3_bound x y tpb hε hdiff c

  calc |f x - f y|
  _ = |g 0 - g 1| := by
    rw [show g 0 = f x by simp[g, interpolated, interpolator]]
    rw [show g 1 = f y by simp[g, interpolated, interpolator]]
  _ = |g' 0 + g'' 0 / 2 + g''' c / 6| := by rw [abs_sub_comm]; congr 1; linarith
  _ ≤ |g' 0| + |g'' 0 / 2| + |g''' c / 6| := abs_add_three _ _ _
  _ = |g' 0| + |g'' 0| / 2 + |g''' c| / 6 := by
    rw [abs_div, abs_div]; norm_num
  _ ≤ ∑ i, ε i * |nth_partial i f x|
      + (∑ i, ∑ j, ε i * ε j * |nth_partial i (nth_partial j f) x|) / 2
      + M * (∑ i, ε i)^3 / 6 := by grw [bound1, bound2, bound3]
  _ = ∑ i, ε i * |nth_partial i f x|
      + (1/2) * ∑ i, ∑ j, ε i * ε j * |nth_partial i (nth_partial j f) x|
      + M * (∑ i, ε i)^3 / 6 := by ring

/-- Second-order control of the variation of a **vector-valued** function,
by scalarizing along the unit direction of the difference: bounds on the
directional projections' partials at `x` (uniform in the direction `u`)
control `‖v x - v y‖` to second order with a cubic remainder.  This is the
engine behind the second-order local certificate's `Δ`-terms, instantiated
with `b1`/`b2` the norms of the (rotation-family) partial vectors at `x`. -/
theorem norm_sub_control_difference2 {n m : ℕ} (v : E n → E m)
    (x y : E n) (ε : Fin n → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (hdiff : (i : Fin n) → |x i - y i| ≤ ε i)
    {M : ℝ} (b1 : Fin n → ℝ) (b2 : Fin n → Fin n → ℝ)
    (hb1 : ∀ i, 0 ≤ b1 i) (hb2 : ∀ i j, 0 ≤ b2 i j) (hM : 0 ≤ M)
    (h : ∀ u : E m, ‖u‖ = 1 →
      ContDiff ℝ 3 (fun z => ⟪v z, u⟫) ∧
      third_partials_bounded (fun z => ⟪v z, u⟫) M ∧
      (∀ i, |nth_partial i (fun z => ⟪v z, u⟫) x| ≤ b1 i) ∧
      (∀ i j, |nth_partial i (nth_partial j (fun z => ⟪v z, u⟫)) x| ≤ b2 i j)) :
    ‖v x - v y‖ ≤ ∑ i, ε i * b1 i
      + (1/2) * ∑ i, ∑ j, ε i * ε j * b2 i j
      + M * (∑ i, ε i)^3 / 6 := by
  rcases eq_or_ne (v x) (v y) with heq | hne
  · rw [heq, sub_self, norm_zero]
    have h1 : (0:ℝ) ≤ ∑ i, ε i * b1 i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hε i) (hb1 i)
    have h2 : (0:ℝ) ≤ ∑ i, ∑ j, ε i * ε j * b2 i j :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (hε i) (hε j)) (hb2 i j)
    have h3 : (0:ℝ) ≤ (∑ i, ε i)^3 :=
      pow_nonneg (Finset.sum_nonneg fun i _ => hε i) 3
    positivity
  · set u : E m := ‖v x - v y‖⁻¹ • (v x - v y) with hu_def
    have hu : ‖u‖ = 1 := norm_smul_inv_norm (sub_ne_zero.mpr hne)
    obtain ⟨hc, htpb, hb1', hb2'⟩ := h u hu
    have key := bounded_partials_control_difference2 _ hc x y ε hε hdiff htpb
    have hval : ⟪v x - v y, u⟫ = ‖v x - v y‖ := by
      rw [hu_def, real_inner_smul_right, real_inner_self_eq_norm_mul_norm]
      have hn : ‖v x - v y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
      field_simp
    calc ‖v x - v y‖
        = ⟪v x - v y, u⟫ := hval.symm
      _ = (fun z => ⟪v z, u⟫) x - (fun z => ⟪v z, u⟫) y := by
          simp [inner_sub_left]
      _ ≤ |(fun z => ⟪v z, u⟫) x - (fun z => ⟪v z, u⟫) y| := le_abs_self _
      _ ≤ ∑ i, ε i * |nth_partial i (fun z => ⟪v z, u⟫) x|
            + (1/2) * ∑ i, ∑ j, ε i * ε j *
                |nth_partial i (nth_partial j (fun z => ⟪v z, u⟫)) x|
            + M * (∑ i, ε i)^3 / 6 := key
      _ ≤ ∑ i, ε i * b1 i + (1/2) * ∑ i, ∑ j, ε i * ε j * b2 i j
            + M * (∑ i, ε i)^3 / 6 := by
          gcongr with i _ i _ j _
          · exact hε i
          · exact hb1' i
          · exact mul_nonneg (hε i) (hε j)
          · exact hb2' i j

end GlobalTheorem
end
