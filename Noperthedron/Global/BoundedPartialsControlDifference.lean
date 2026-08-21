module

public import Mathlib.Analysis.Calculus.Taylor
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

noncomputable
def interpolator' {n : ℕ} (x y : E n) : ℝ →L[ℝ] E n :=
  ContinuousLinearMap.toSpanSingleton ℝ (y - x)

private
theorem interpolator_has_deriv {n : ℕ} (x y : E n) (t : ℝ) :
    HasFDerivAt (interpolator x y) (interpolator' x y) t := by
  unfold interpolator'
  rw [← hasDerivAt_iff_hasFDerivAt]
  unfold interpolator
  -- I don't really like this proof, I'd prefer something that more incrementally
  -- "discovers" the derivative of interpolator instead of building it all up and then
  -- `convert`ing it to the desired form.
  convert! ((hasDerivAt_id t).const_sub 1).smul_const x |>.add ((hasDerivAt_id t).smul_const y) using 1
  module

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

open ContinuousLinearMap in
theorem interpolated_has_deriv {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 2 f) (t : ℝ) :
    HasDerivAt (interpolated x y f) (interpolated_deriv x y f t) t := by
  unfold interpolated interpolated_deriv
  rw [hasDerivAt_iff_hasFDerivAt]
  have hfd : HasFDerivAt f (fderiv ℝ f (interpolator x y t)) (interpolator x y t) :=
    fc.differentiable (by norm_num) |>.differentiableAt.hasFDerivAt

  have : (toSpanSingleton ℝ (∑ i, (y.ofLp i - x.ofLp i) * nth_partial i f ((1 - t) • x + t • y)))
      = ((fderiv ℝ f (interpolator x y t)).comp (interpolator' x y)) := by
    unfold interpolator' interpolator
    ext
    simp only [toSpanSingleton_apply, smul_eq_mul, one_mul, coe_comp, Function.comp_apply,
      one_smul]
    rw [nth_partial_def f]
    congr
  rw [this]
  exact HasFDerivAt.comp t hfd (interpolator_has_deriv x y t)

open ContinuousLinearMap in
theorem interpolated_has_deriv2 {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 2 f) (t : ℝ) :
    HasDerivAt (interpolated_deriv x y f) (interpolated_deriv2 x y f t) t := by
  unfold interpolated_deriv interpolated_deriv2
  rw [hasDerivAt_iff_hasFDerivAt]
  have hd (i : Fin n) : HasDerivAt (fun t => nth_partial i f (interpolator x y t))
      (∑ j, (y j - x j) * nth_partial j (nth_partial i f) (interpolator x y t)) t := by
    convert! HasFDerivAt.comp_hasDerivAt t (c2_imp_partials_c1 fc |>.differentiable_one _ |>.hasFDerivAt)
      (interpolator_has_deriv x y t)
    rw [nth_partial_def]
    rfl
  convert! HasFDerivAt.sum fun i _ => (HasDerivAt.hasFDerivAt (HasDerivAt.const_mul (y i - x i) (hd i)))
  all_goals try unfold interpolator
  · rw [Finset.sum_fn]
  · ext
    simp only [toSpanSingleton_apply, smul_eq_mul, Finset.mul_sum, one_mul, FunLike.coe_sum, Finset.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    ring_nf

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

open ContinuousLinearMap in
theorem interpolated_has_deriv3 {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 3 f) (t : ℝ) :
    HasDerivAt (interpolated_deriv2 x y f) (interpolated_deriv3 x y f t) t := by
  unfold interpolated_deriv2 interpolated_deriv3
  rw [hasDerivAt_iff_hasFDerivAt]
  have hd (i j : Fin n) :
      HasDerivAt (fun t => (nth_partial i <| nth_partial j f) (interpolator x y t))
      (∑ k, (y k - x k) * nth_partial k (nth_partial i (nth_partial j f))
        (interpolator x y t)) t := by
    convert! HasFDerivAt.comp_hasDerivAt t
      (c3_imp_partials2_c1 fc |>.differentiable_one _ |>.hasFDerivAt)
      (interpolator_has_deriv x y t)
    rw [nth_partial_def]
    rfl
  convert! HasFDerivAt.sum fun i _ => HasDerivAt.hasFDerivAt <|
    HasDerivAt.fun_sum fun j _ =>
      HasDerivAt.const_mul ((y i - x i) * (y j - x j)) (hd i j)
  all_goals try unfold interpolator
  · rw [Finset.sum_fn]
  · ext
    simp only [toSpanSingleton_apply, smul_eq_mul, Finset.mul_sum, one_mul, FunLike.coe_sum,
      Finset.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j hj
    apply Finset.sum_congr rfl; intro k hk
    ring_nf

theorem deriv_interpolated3 {n : ℕ} (x y : E n) (f : E n → ℝ) (fc : ContDiff ℝ 3 f) :
    deriv (interpolated_deriv2 x y f) = interpolated_deriv3 x y f := by
  ext t
  exact (interpolated_has_deriv3 x y f fc t).deriv

theorem differentiable_deriv_interpolated2 {n : ℕ} (x y : E n) (f : E n → ℝ)
    (fc : ContDiff ℝ 3 f) : Differentiable ℝ (interpolated_deriv2 x y f) := by
  unfold interpolated_deriv2
  refine Differentiable.fun_sum ?_; intro i hi
  refine Differentiable.fun_sum ?_; intro j hj
  refine Differentiable.mul (by fun_prop) ?_
  change Differentiable ℝ
    ((fun v ↦ (nth_partial i <| nth_partial j f) v) ∘ (fun t ↦ (1 - t) • x + t • y))
  refine Differentiable.comp ?_ (by fun_prop)
  exact c3_imp_partials2_differentiable fc

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
  have g''_diff : Differentiable ℝ g'' := differentiable_deriv_interpolated2 x y f fc

  have deriv_g_eq_g' : deriv g = g' := deriv_interpolated x y f fc2
  have deriv_g'_eq_g'' : deriv g' = g'' := deriv_interpolated2 x y f fc2
  have deriv_g''_eq_g''' : deriv g'' = g''' := deriv_interpolated3 x y f fc

  have huIcc : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hud : UniqueDiffOn ℝ (Set.uIcc (0:ℝ) 1) := huIcc ▸ uniqueDiffOn_Icc zero_lt_one

  -- since `g` is C³ on all of ℝ, the `Within` iterated derivatives on `uIcc 0 1`
  -- agree with the global ones at every point of `uIcc 0 1`
  have hg1 : ∀ t ∈ Set.uIcc (0:ℝ) 1, iteratedDerivWithin 1 g (Set.uIcc 0 1) t = g' t :=
    fun t ht => by
      rw [iteratedDerivWithin_eq_iteratedDeriv hud (g_c3.of_le (by norm_num)).contDiffAt ht,
        iteratedDeriv_one, deriv_g_eq_g']
  have hg2 : ∀ t ∈ Set.uIcc (0:ℝ) 1, iteratedDerivWithin 2 g (Set.uIcc 0 1) t = g'' t :=
    fun t ht => by
      rw [iteratedDerivWithin_eq_iteratedDeriv hud (g_c3.of_le (by norm_num)).contDiffAt ht,
        iteratedDeriv_succ, iteratedDeriv_one, deriv_g_eq_g', deriv_g'_eq_g'']

  -- second-order Taylor with the Lagrange remainder:
  -- `g 1 - (g 0 + g' 0 + g'' 0 / 2) = g''' c / 6` for some `c` between `0` and `1`
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin 2 g (Set.uIcc 0 1)) (Set.uIoo 0 1) :=
    g''_diff.differentiableOn.congr fun t ht => hg2 t (Set.uIoo_subset_uIcc_self ht)
  obtain ⟨c, hc, htay⟩ := taylor_mean_remainder_lagrange (f := g) (x₀ := 0) (x := 1) (n := 2)
    (by norm_num) (g_c3.of_le (by norm_num)).contDiffOn hf'
  have h_tay0 : taylorWithinEval g 2 (Set.uIcc 0 1) 0 1 = g 0 + g' 0 + g'' 0 / 2 := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_zero]
    rw [hg1 0 Set.left_mem_uIcc, hg2 0 Set.left_mem_uIcc]
    norm_num [Nat.factorial]
    ring
  rw [h_tay0, iteratedDerivWithin_eq_iteratedDeriv hud g_c3.contDiffAt
        (Set.uIoo_subset_uIcc_self hc),
      iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
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

end GlobalTheorem
end
