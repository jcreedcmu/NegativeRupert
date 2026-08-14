module

public import Mathlib.Algebra.Lie.OfAssociative
public import Noperthedron.PointSym
public import Noperthedron.PoseInterval
public import Noperthedron.RationalApprox.Basic
public import Noperthedron.RationalApprox.BoundsKappa3
public import Noperthedron.RationalApprox.Cast

@[expose] public section


open scoped RealInnerProductSpace

namespace RationalApprox

variable (P Q P_ Q_ : ℝ³) (θ φ : Set.Icc (-4 : ℝ) 4) (ε : ℝ)

/-!
[SY25] Corollary 51
-/

noncomputable
def bounds_kappa4_A := (⟪rotM θ φ P, rotM θ φ (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)) /
  ((‖rotM θ φ P‖ + √2 * ε) * (‖rotM θ φ (P - Q)‖ + 2 * √2 * ε))

/-- The rational counterpart of `bounds_kappa4_A`. The applied vectors are the
*rounded* `p.rotM₂Rℚ` ones actually computed by the checker (see
`Pose.rotM₂Rℚ`); the rounding perturbation is absorbed into the `10κ`/`3κ`/`6κ`
terms by `bounds_kappa4` below. -/
noncomputable
def bounds_kappa4_Aℚ (P_ Q_ : Fin 3 → ℚ) (p : Pose ℚ) (ε : ℝ) (s : UpperSqrt) : ℝ :=
  (((p.rotM₂Rℚ P_ ⬝ᵥ p.rotM₂Rℚ (P_ - Q_) : ℚ) : ℝ) - 10 * κ -
      2 * ε * (‖toR3 (P_ - Q_)‖ + 2 * κ) * (√2 + ε)) /
  ((↑(s.norm (p.rotM₂Rℚ P_)) + √2 * ε + 3 * κ) *
    (↑(s.norm (p.rotM₂Rℚ (P_ - Q_))) + 2 * √2 * ε + 6 * κ))

/-- An `UpperSqrt` overestimates the Euclidean norm of a rational vector cast to `ℝ`. -/
lemma UpperSqrt_norm_le {n : ℕ} (s : UpperSqrt) (v : Fin n → ℚ) :
    ‖WithLp.toLp 2 (fun i => (v i : ℝ))‖ ≤ ↑(s.norm v) := by
  unfold UpperSqrt.norm
  have h_norm_sq := toLp_norm_sq_eq_dotProduct v
  have h_dot_nn : (0 : ℝ) ≤ ((v ⬝ᵥ v : ℚ) : ℝ) := by
    rw [← h_norm_sq]; exact sq_nonneg _
  have h_dot_nn_ℚ : (0 : ℚ) ≤ v ⬝ᵥ v := mod_cast h_dot_nn
  calc ‖WithLp.toLp 2 (fun i => (v i : ℝ))‖
      = √(‖WithLp.toLp 2 (fun i => (v i : ℝ))‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
    _ = √(((v ⬝ᵥ v : ℚ) : ℝ)) := by rw [h_norm_sq]
    _ ≤ ↑(s.f (v ⬝ᵥ v)) := s.bound _ h_dot_nn_ℚ

/-- A `LowerSqrt` underestimates the Euclidean norm of a rational vector cast to `ℝ`. -/
lemma LowerSqrt_norm_ge {n : ℕ} (s : LowerSqrt) (v : Fin n → ℚ) :
    ↑(s.norm v) ≤ ‖WithLp.toLp 2 (fun i => (v i : ℝ))‖ := by
  unfold LowerSqrt.norm
  have h_norm_sq := toLp_norm_sq_eq_dotProduct v
  have h_dot_nn : (0 : ℝ) ≤ ((v ⬝ᵥ v : ℚ) : ℝ) := by
    rw [← h_norm_sq]; exact sq_nonneg _
  have h_dot_nn_ℚ : (0 : ℚ) ≤ v ⬝ᵥ v := mod_cast h_dot_nn
  calc (↑(s.f (v ⬝ᵥ v)) : ℝ)
      ≤ √(((v ⬝ᵥ v : ℚ) : ℝ)) := s.bound _ h_dot_nn_ℚ
    _ = √(‖WithLp.toLp 2 (fun i => (v i : ℝ))‖ ^ 2) := by rw [h_norm_sq]
    _ = ‖WithLp.toLp 2 (fun i => (v i : ℝ))‖ := Real.sqrt_sq (norm_nonneg _)

/-! ### `round13v` rounding absorption

The local checker rounds the applied vectors `p.rotM₂ℚ v` down componentwise to
multiples of `10⁻¹³` (`Pose.rotM₂Rℚ`) so that its per-vertex-pair dot products
and `UpperSqrt` norms run on small denominators. The lemmas below bound the
perturbation, which `bounds_kappa4` absorbs into its `κ`-scale budgets. -/

/-- The coordinates of the `toR2` cast of a rational 2-vector are bounded by its norm. -/
private lemma abs_coord_le_norm_toR2 (v : Fin 2 → ℚ) (i : Fin 2) :
    |(v i : ℝ)| ≤ ‖toR2 v‖ := by
  have h := PiLp.norm_apply_le (toR2 v) i
  simpa only [toR2, WithLp.ofLp_toLp, Real.norm_eq_abs] using h

/-- `round13v` moves the `toR2` cast of a rational 2-vector by at most `2/10¹³`. -/
private lemma norm_toR2_round13v_sub_le (v : Fin 2 → ℚ) :
    ‖toR2 (round13v v) - toR2 v‖ ≤ 2 / 10 ^ 13 := by
  rw [← toR2_sub]
  have hterm : ∀ i : Fin 2, (round13v v - v) i * (round13v v - v) i ≤ 1 / 10 ^ 26 := by
    intro i
    have habs : |(round13v v - v) i| ≤ 1 / 10 ^ 13 := by
      simpa only [Pi.sub_apply, round13v] using abs_round13_sub_le (v i)
    calc (round13v v - v) i * (round13v v - v) i
        = |(round13v v - v) i| * |(round13v v - v) i| := (abs_mul_abs_self _).symm
      _ ≤ (1 / 10 ^ 13) * (1 / 10 ^ 13) :=
          mul_le_mul habs habs (abs_nonneg _) (by norm_num)
      _ = 1 / 10 ^ 26 := by norm_num
  have hdot : ((round13v v - v) ⬝ᵥ (round13v v - v) : ℚ) ≤ 2 / 10 ^ 26 := by
    simp only [dotProduct, Fin.sum_univ_two]
    linarith [hterm 0, hterm 1]
  calc ‖toR2 (round13v v - v)‖
      = √(‖toR2 (round13v v - v)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = √((((round13v v - v) ⬝ᵥ (round13v v - v) : ℚ) : ℝ)) := by
        rw [show ‖toR2 (round13v v - v)‖ ^ 2 =
          (((round13v v - v) ⬝ᵥ (round13v v - v) : ℚ) : ℝ) from
          toLp_norm_sq_eq_dotProduct _]
    _ ≤ √((2 / 10 ^ 13) ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc ((((round13v v - v) ⬝ᵥ (round13v v - v) : ℚ)) : ℝ)
            ≤ ((2 / 10 ^ 26 : ℚ) : ℝ) := by exact_mod_cast hdot
          _ ≤ (2 / 10 ^ 13) ^ 2 := by norm_num
    _ = 2 / 10 ^ 13 := Real.sqrt_sq (by norm_num)

/-- The `UpperSqrt` norm of the rounded vector plus `2/10¹³` still dominates
the cast norm of the unrounded vector. -/
private lemma norm_le_round13v_upper (s : UpperSqrt) (v : Fin 2 → ℚ) :
    ‖toR2 v‖ ≤ ↑(s.norm (round13v v)) + 2 / 10 ^ 13 := by
  have h1 : ‖toR2 v‖ ≤ ‖toR2 (round13v v)‖ + ‖toR2 (round13v v) - toR2 v‖ :=
    norm_le_insert _ _
  have h2 : ‖toR2 (round13v v)‖ ≤ ↑(s.norm (round13v v)) := UpperSqrt_norm_le s _
  linarith [norm_toR2_round13v_sub_le v]

/-- The `LowerSqrt` norm of the rounded vector is at most the cast norm of the
unrounded vector plus `2/10¹³`. Absorbs the `Pose.rotM₂Rℚ` rounding of
`BoundRℚ` into its `3κℚ` term (see `rational_local`). -/
lemma LowerSqrt_norm_round13v_le (s : LowerSqrt) (v : Fin 2 → ℚ) :
    ((s.norm (round13v v) : ℚ) : ℝ) ≤ ‖toR2 v‖ + 2 / 10 ^ 13 := by
  have h1 : ((s.norm (round13v v) : ℚ) : ℝ) ≤ ‖toR2 (round13v v)‖ :=
    LowerSqrt_norm_ge s _
  have h2 : ‖toR2 (round13v v)‖ ≤ ‖toR2 v‖ + ‖toR2 (round13v v) - toR2 v‖ :=
    norm_le_insert' _ _
  linarith [norm_toR2_round13v_sub_le v]

/-- Rounding both applied vectors perturbs their dot product by at most
`2/10¹²`, given (generous) norm bounds on the unrounded vectors. -/
private lemma round_dot_error {u₁ u₂ : Fin 2 → ℚ}
    (h₁ : ‖toR2 u₁‖ ≤ 2) (h₂ : ‖toR2 u₂‖ ≤ 3) :
    |((round13v u₁ ⬝ᵥ round13v u₂ : ℚ) : ℝ) - ((u₁ ⬝ᵥ u₂ : ℚ) : ℝ)| ≤ 2 / 10 ^ 12 := by
  have hq := abs_round13v_dot_round13v_sub_le u₁ u₂
  have hsum₁ : (∑ i, |u₁ i|) ≤ (4 : ℚ) := by
    have hc : ∀ i, |u₁ i| ≤ (2 : ℚ) := by
      intro i
      have h := (abs_coord_le_norm_toR2 u₁ i).trans h₁
      exact_mod_cast h
    rw [Fin.sum_univ_two]
    linarith [hc 0, hc 1]
  have hsum₂ : (∑ i, |round13v u₂ i|) ≤ (7 : ℚ) := by
    have hc : ∀ i, |round13v u₂ i| ≤ (3 : ℚ) + 1 / 10 ^ 13 := by
      intro i
      have hcoord : |u₂ i| ≤ (3 : ℚ) := by
        have h := (abs_coord_le_norm_toR2 u₂ i).trans h₂
        exact_mod_cast h
      have hdiff : |round13v u₂ i - u₂ i| ≤ 1 / 10 ^ 13 := abs_round13_sub_le (u₂ i)
      calc |round13v u₂ i| = |u₂ i + (round13v u₂ i - u₂ i)| := by congr 1; ring
        _ ≤ |u₂ i| + |round13v u₂ i - u₂ i| := abs_add_le _ _
        _ ≤ 3 + 1 / 10 ^ 13 := add_le_add hcoord hdiff
    rw [Fin.sum_univ_two]
    linarith [hc 0, hc 1]
  have hbound : |round13v u₁ ⬝ᵥ round13v u₂ - u₁ ⬝ᵥ u₂| ≤ (2 / 10 ^ 12 : ℚ) := by
    calc |round13v u₁ ⬝ᵥ round13v u₂ - u₁ ⬝ᵥ u₂|
        ≤ ((∑ i, |round13v u₂ i|) + ∑ i, |u₁ i|) / 10 ^ 13 := hq
      _ ≤ (7 + 4) / 10 ^ 13 := by gcongr
      _ ≤ 2 / 10 ^ 12 := by norm_num
  have h : ((|round13v u₁ ⬝ᵥ round13v u₂ - u₁ ⬝ᵥ u₂| : ℚ) : ℝ) ≤ ((2 / 10 ^ 12 : ℚ) : ℝ) :=
    Rat.cast_le.mpr hbound
  rw [Rat.cast_abs, Rat.cast_sub] at h
  calc |((round13v u₁ ⬝ᵥ round13v u₂ : ℚ) : ℝ) - ((u₁ ⬝ᵥ u₂ : ℚ) : ℝ)|
      ≤ ((2 / 10 ^ 12 : ℚ) : ℝ) := h
    _ = 2 / 10 ^ 12 := by norm_num

/-- The inner product bound for `rotM`/`rotMℚ` when the second vector has norm ≤ 2.
This generalises the `|⟪MP, MQ⟫ − ⟪M_ℚP̃, M_ℚQ̃⟫| ≤ 5κ` bound of [SY25]
Lemma 49 (which requires ‖Q‖ ≤ 1) to handle `P − Q`.
The constant is kept at `9κ` (not the `10κ` used downstream) to leave room for
the `round13v` rounding perturbation. -/
lemma inner_product_bound_9kappa
    {P Q P_ Q_ : ℝ³} {θ φ : Set.Icc (-4 : ℝ) 4}
    (hP : ‖P‖ ≤ 1) (hR : ‖Q‖ ≤ 2)
    (Papprox : ‖P - P_‖ ≤ κ) (Qapprox : ‖Q - Q_‖ ≤ 2 * κ) :
    |⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) Q⟫ - ⟪(rotMℚℝ ↑θ ↑φ) P_, (rotMℚℝ ↑θ ↑φ) Q_⟫| ≤ 9 * κ := by
  have hMdiff : ‖rotM (θ : ℝ) (φ : ℝ) - rotMℚℝ (θ : ℝ) (φ : ℝ)‖ ≤ κ :=
    M_difference_norm_bounded _ _ (θ.property) (φ.property)
  have hMℚnorm : ‖rotMℚℝ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ :=
    Mℚ_norm_bounded (θ.property) (φ.property)
  -- Decompose: ⟪rotM P, rotM Q⟫ - ⟪rotMℚ P_, rotMℚ Q_⟫
  --   = ⟪rotM P - rotMℚ P_, rotM Q⟫ + ⟪rotMℚ P_, rotM Q - rotMℚ Q_⟫
  have decomp : ⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) Q⟫ - ⟪(rotMℚℝ ↑θ ↑φ) P_, (rotMℚℝ ↑θ ↑φ) Q_⟫ =
      ⟪(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫ +
      ⟪(rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_⟫ := by
    simp [inner_sub_left, inner_sub_right]
  rw [decomp]
  -- Bound ‖rotM P - rotMℚ P_‖
  have hAP : ‖(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub hMdiff hMℚnorm hP Papprox
  -- Bound ‖rotM Q - rotMℚ Q_‖ (with ‖Q‖ ≤ 2 and ‖Q - Q_‖ ≤ 2κ)
  have hBQ : ‖(rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_‖ ≤ 4 * κ + 2 * κ ^ 2 :=
    clm_approx_apply_sub₂ hMdiff hMℚnorm hR Qapprox
  -- Bound ‖rotM Q‖
  have hMQ : ‖(rotM ↑θ ↑φ) Q‖ ≤ 2 := by
    have := ContinuousLinearMap.le_opNorm (rotM ↑θ ↑φ) Q
    rw [Bounding.rotM_norm_one, one_mul] at this; linarith
  -- Bound ‖rotMℚ P_‖
  have hMℚP_ : ‖(rotMℚℝ ↑θ ↑φ) P_‖ ≤ (1 + κ) * (1 + κ) :=
    approx_image_norm_le hMℚnorm hP Papprox
  calc |⟪(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫ +
        ⟪(rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_⟫|
    _ ≤ |⟪(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q⟫| +
        |⟪(rotMℚℝ ↑θ ↑φ) P_, (rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_⟫| := abs_add_le _ _
    _ ≤ ‖(rotM ↑θ ↑φ) P - (rotMℚℝ ↑θ ↑φ) P_‖ * ‖(rotM ↑θ ↑φ) Q‖ +
        ‖(rotMℚℝ ↑θ ↑φ) P_‖ * ‖(rotM ↑θ ↑φ) Q - (rotMℚℝ ↑θ ↑φ) Q_‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (2 * κ + κ ^ 2) * 2 + (1 + κ) * (1 + κ) * (4 * κ + 2 * κ ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_right hAP (norm_nonneg _) |>.trans
            (mul_le_mul_of_nonneg_left hMQ (by norm_num [κ])))
          (mul_le_mul hMℚP_ hBQ (norm_nonneg _) (by norm_num [κ]))
    _ ≤ 9 * κ := by unfold κ; norm_num

/-- Real inner product vs the checker's *rounded* rational dot product
(`Pose.rotM₂Rℚ`): the `9κ` approximation bound plus the `2/10¹²` rounding
perturbation stays within `10κ`. -/
lemma inner_product_bound_round_10kappa
    {P Q : ℝ³} {P_ Q_ : Fin 3 → ℚ} {p : Pose ℚ}
    {θ φ : Set.Icc (-4 : ℝ) 4}
    (hθ : (θ : ℝ) = (p.θ₂ : ℝ)) (hφ : (φ : ℝ) = (p.φ₂ : ℝ))
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (Papprox : ‖P - toR3 P_‖ ≤ κ) (Qapprox : ‖Q - toR3 Q_‖ ≤ κ) :
    |⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) (P - Q)⟫ -
      ((p.rotM₂Rℚ P_ ⬝ᵥ p.rotM₂Rℚ (P_ - Q_) : ℚ) : ℝ)| ≤ 10 * κ := by
  have hPQ_norm : ‖P - Q‖ ≤ 2 := by
    calc ‖P - Q‖ ≤ ‖P‖ + ‖Q‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hP hQ
      _ = 2 := by norm_num
  have hPQ_approx : ‖(P - Q) - (toR3 P_ - toR3 Q_)‖ ≤ 2 * κ := by
    calc ‖(P - Q) - (toR3 P_ - toR3 Q_)‖
        = ‖(P - toR3 P_) - (Q - toR3 Q_)‖ := by congr 1; abel
      _ ≤ ‖P - toR3 P_‖ + ‖Q - toR3 Q_‖ := norm_sub_le _ _
      _ ≤ κ + κ := add_le_add Papprox Qapprox
      _ = 2 * κ := by ring
  have h9 : |⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) (P - Q)⟫ -
      ⟪(rotMℚℝ ↑θ ↑φ) (toR3 P_), (rotMℚℝ ↑θ ↑φ) (toR3 P_ - toR3 Q_)⟫| ≤ 9 * κ :=
    inner_product_bound_9kappa hP hPQ_norm Papprox hPQ_approx
  -- bridge the unrounded rational dot to the real inner product
  have h_bridge : ⟪(rotMℚℝ ↑θ ↑φ) (toR3 P_), (rotMℚℝ ↑θ ↑φ) (toR3 P_ - toR3 Q_)⟫ =
      ((p.rotM₂ℚ P_ ⬝ᵥ p.rotM₂ℚ (P_ - Q_) : ℚ) : ℝ) := by
    rw [hθ, hφ, ← toR2_rotM₂ℚ, ← toR3_sub, ← toR2_rotM₂ℚ, inner_toR2]
  rw [h_bridge] at h9
  -- norm bounds on the unrounded applied vectors, for the rounding perturbation
  have hMℚnorm : ‖rotMℚℝ (↑θ : ℝ) ↑φ‖ ≤ 1 + κ := Mℚ_norm_bounded θ.property φ.property
  have h_u₁ : ‖toR2 (p.rotM₂ℚ P_)‖ ≤ 2 := by
    rw [toR2_rotM₂ℚ, ← hθ, ← hφ]
    exact (approx_image_norm_le hMℚnorm hP Papprox).trans (by unfold κ; norm_num)
  have h_u₂ : ‖toR2 (p.rotM₂ℚ (P_ - Q_))‖ ≤ 3 := by
    have h_norm : ‖toR3 P_ - toR3 Q_‖ ≤ 2 + 2 * κ := by
      have h := norm_le_insert (P - Q) (toR3 P_ - toR3 Q_)
      linarith
    rw [toR2_rotM₂ℚ, ← hθ, ← hφ, toR3_sub]
    calc ‖(rotMℚℝ ↑θ ↑φ) (toR3 P_ - toR3 Q_)‖
        ≤ ‖rotMℚℝ (↑θ : ℝ) ↑φ‖ * ‖toR3 P_ - toR3 Q_‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 + κ) * (2 + 2 * κ) :=
          mul_le_mul hMℚnorm h_norm (norm_nonneg _) (by unfold κ; norm_num)
      _ ≤ 3 := by unfold κ; norm_num
  have h_round : |((p.rotM₂Rℚ P_ ⬝ᵥ p.rotM₂Rℚ (P_ - Q_) : ℚ) : ℝ) -
      ((p.rotM₂ℚ P_ ⬝ᵥ p.rotM₂ℚ (P_ - Q_) : ℚ) : ℝ)| ≤ 2 / 10 ^ 12 :=
    round_dot_error h_u₁ h_u₂
  calc |⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) (P - Q)⟫ -
        ((p.rotM₂Rℚ P_ ⬝ᵥ p.rotM₂Rℚ (P_ - Q_) : ℚ) : ℝ)|
      ≤ |⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) (P - Q)⟫ -
          ((p.rotM₂ℚ P_ ⬝ᵥ p.rotM₂ℚ (P_ - Q_) : ℚ) : ℝ)| +
        |((p.rotM₂ℚ P_ ⬝ᵥ p.rotM₂ℚ (P_ - Q_) : ℚ) : ℝ) -
          ((p.rotM₂Rℚ P_ ⬝ᵥ p.rotM₂Rℚ (P_ - Q_) : ℚ) : ℝ)| := abs_sub_le _ _ _
    _ ≤ 9 * κ + 2 / 10 ^ 12 := add_le_add h9 (by rw [abs_sub_comm]; exact h_round)
    _ ≤ 10 * κ := by unfold κ; norm_num

/-- [SY25] Corollary 51 -/
lemma bounds_kappa4 (P Q : ℝ³) (P_ Q_ : Fin 3 → ℚ) (p : Pose ℚ)
    (hθBound : (p.θ₂ : ℝ) ∈ Set.Icc (-4 : ℝ) 4)
    (hφBound : (p.φ₂ : ℝ) ∈ Set.Icc (-4 : ℝ) 4)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (Papprox : ‖P - toR3 P_‖ ≤ κ) (Qapprox : ‖Q - toR3 Q_‖ ≤ κ)
    (ε : ℝ) (hε : 0 < ε) (s : UpperSqrt)
    (hA_nonneg : 0 ≤ ⟪rotM (p.θ₂ : ℝ) (p.φ₂ : ℝ) P,
        rotM (p.θ₂ : ℝ) (p.φ₂ : ℝ) (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)) :
    bounds_kappa4_Aℚ P_ Q_ p ε s ≤
      bounds_kappa4_A P Q ⟨(p.θ₂ : ℝ), hθBound⟩ ⟨(p.φ₂ : ℝ), hφBound⟩ ε := by
  set θ : Set.Icc (-4 : ℝ) 4 := ⟨(p.θ₂ : ℝ), hθBound⟩
  set φ : Set.Icc (-4 : ℝ) 4 := ⟨(p.φ₂ : ℝ), hφBound⟩
  -- Bridges: the rounded `UpperSqrt` norms dominate the real norms up to `2/10¹³`.
  have h_norm_bridge_P : ‖(rotMℚℝ ↑θ ↑φ) (toR3 P_)‖ ≤
      ↑(s.norm (p.rotM₂Rℚ P_)) + 2 / 10 ^ 13 := by
    rw [← toR2_rotM₂ℚ]
    exact norm_le_round13v_upper s _
  have h_norm_bridge_PQ : ‖(rotMℚℝ ↑θ ↑φ) (toR3 P_ - toR3 Q_)‖ ≤
      ↑(s.norm (p.rotM₂Rℚ (P_ - Q_))) + 2 / 10 ^ 13 := by
    rw [← toR3_sub, ← toR2_rotM₂ℚ]
    exact norm_le_round13v_upper s _
  -- Nonnegativity of the rounded `UpperSqrt` norms (for positivity below).
  have h_snorm_P_nn : (0 : ℝ) ≤ ↑(s.norm (p.rotM₂Rℚ P_)) :=
    le_trans (norm_nonneg (toR2 (p.rotM₂Rℚ P_))) (UpperSqrt_norm_le s _)
  have h_snorm_PQ_nn : (0 : ℝ) ≤ ↑(s.norm (p.rotM₂Rℚ (P_ - Q_))) :=
    le_trans (norm_nonneg (toR2 (p.rotM₂Rℚ (P_ - Q_)))) (UpperSqrt_norm_le s _)
  -- Abbreviate the numerators and denominators
  set numA := ⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)
  set numAℚ := ((p.rotM₂Rℚ P_ ⬝ᵥ p.rotM₂Rℚ (P_ - Q_) : ℚ) : ℝ) - 10 * κ -
    2 * ε * (‖toR3 (P_ - Q_)‖ + 2 * κ) * (√2 + ε)
  set denA := (‖(rotM ↑θ ↑φ) P‖ + √2 * ε) * (‖(rotM ↑θ ↑φ) (P - Q)‖ + 2 * √2 * ε)
  set denAℚ := (↑(s.norm (p.rotM₂Rℚ P_)) + √2 * ε + 3 * κ) *
    (↑(s.norm (p.rotM₂Rℚ (P_ - Q_))) + 2 * √2 * ε + 6 * κ)
  change numAℚ / denAℚ ≤ numA / denA
  have hPQ_norm : ‖P - Q‖ ≤ 2 := by
    calc ‖P - Q‖ ≤ ‖P‖ + ‖Q‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hP hQ
      _ = 2 := by ring
  have hPQ_approx : ‖(P - Q) - (toR3 P_ - toR3 Q_)‖ ≤ 2 * κ := by
    calc ‖(P - Q) - (toR3 P_ - toR3 Q_)‖
        = ‖(P - toR3 P_) - (Q - toR3 Q_)‖ := by congr 1; abel
      _ ≤ ‖P - toR3 P_‖ + ‖Q - toR3 Q_‖ := norm_sub_le _ _
      _ ≤ κ + κ := add_le_add Papprox Qapprox
      _ = 2 * κ := by ring
  -- Step 1: numAℚ ≤ numA
  have h_numAℚ_le : numAℚ ≤ numA := by
    have h_inner : |⟪(rotM ↑θ ↑φ) P, (rotM ↑θ ↑φ) (P - Q)⟫ -
        ((p.rotM₂Rℚ P_ ⬝ᵥ p.rotM₂Rℚ (P_ - Q_) : ℚ) : ℝ)| ≤ 10 * κ :=
      inner_product_bound_round_10kappa rfl rfl hP hQ Papprox Qapprox
    replace h_inner := sub_le_of_abs_sub_le_left h_inner
    have h_norm_PQ : ‖P - Q‖ ≤ ‖toR3 (P_ - Q_)‖ + 2 * κ := by
      rw [toR3_sub]
      calc ‖P - Q‖
        _ ≤ ‖toR3 P_ - toR3 Q_‖ + ‖(P - Q) - (toR3 P_ - toR3 Q_)‖ := norm_le_insert' _ _
        _ ≤ ‖toR3 P_ - toR3 Q_‖ + 2 * κ := by grw [hPQ_approx]
    refine tsub_le_tsub h_inner ?_
    exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h_norm_PQ (by linarith)) (by positivity)
  -- Step 2: denA ≤ denAℚ
  have h_denA_le : denA ≤ denAℚ := by
    have hMdiff : ‖rotM (θ : ℝ) (φ : ℝ) - rotMℚℝ (θ : ℝ) (φ : ℝ)‖ ≤ κ :=
      M_difference_norm_bounded _ _ (θ.property) (φ.property)
    have hMℚnorm : ‖rotMℚℝ (θ : ℝ) (φ : ℝ)‖ ≤ 1 + κ :=
      Mℚ_norm_bounded (θ.property) (φ.property)
    have h_f1 : ‖(rotM ↑θ ↑φ) P‖ + √2 * ε ≤
        ↑(s.norm (p.rotM₂Rℚ P_)) + √2 * ε + 3 * κ := by
      have h1 : ‖(rotM ↑θ ↑φ) P‖ ≤ ‖(rotMℚℝ ↑θ ↑φ) (toR3 P_)‖ + (2 * κ + κ ^ 2) := by
        have h := clm_approx_apply_sub hMdiff hMℚnorm hP Papprox
        linarith [norm_le_insert' ((rotM ↑θ ↑φ) P) ((rotMℚℝ ↑θ ↑φ) (toR3 P_))]
      have habsorb : (2 * κ + κ ^ 2) + 2 / 10 ^ 13 ≤ 3 * κ := by unfold κ; norm_num
      linarith [h_norm_bridge_P]
    have h_f2 : ‖(rotM ↑θ ↑φ) (P - Q)‖ + 2 * √2 * ε ≤
        ↑(s.norm (p.rotM₂Rℚ (P_ - Q_))) + 2 * √2 * ε + 6 * κ := by
      have h2 : ‖(rotM ↑θ ↑φ) (P - Q)‖ ≤
          ‖(rotMℚℝ ↑θ ↑φ) (toR3 P_ - toR3 Q_)‖ + (4 * κ + 2 * κ ^ 2) := by
        have h := clm_approx_apply_sub₂ hMdiff hMℚnorm hPQ_norm hPQ_approx
        linarith [norm_le_insert' ((rotM ↑θ ↑φ) (P - Q))
          ((rotMℚℝ ↑θ ↑φ) (toR3 P_ - toR3 Q_))]
      have habsorb : (4 * κ + 2 * κ ^ 2) + 2 / 10 ^ 13 ≤ 6 * κ := by unfold κ; norm_num
      linarith [h_norm_bridge_PQ]
    exact mul_le_mul h_f1 h_f2 (by positivity) (le_trans (by positivity) h_f1)
  exact div_le_div₀ hA_nonneg h_numAℚ_le (by positivity) h_denA_le

end RationalApprox
end
