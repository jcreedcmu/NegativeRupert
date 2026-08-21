module

public import Noperthedron.Local
public import Noperthedron.RationalApprox.RationalLocal
public import Noperthedron.RationalApprox.SecondOrderXBounds

@[expose] public section


/-!
# The second-order Rational Local Theorem — budgets

Rational upper bounds for the variation budgets of `local_theorem₂`
(`ΔrotM`, `ΔrotRM`, `ΔvecX`, `ΔprodMM`), each atom computed from the
rational family matrices on the κ-approximated vertex with an explicit
κ-slack, and the domination lemmas `Δ… ≤ (Δ…ℚ : ℝ)` that feed the
`rational_local₂` bridges.
-/

open Local (Triangle)
open scoped RealInnerProductSpace Real
open scoped Matrix

open RationalApprox (κ κℚ UpperSqrt LowerSqrt)

namespace RationalApprox

/-! ## Family application casts -/

lemma toR2_rotMθℚ_mat_mulVec (θ φ : ℚ) (v : Fin 3 → ℚ) :
    toR2 (rotMθℚ_mat θ φ *ᵥ v) = rotMθℚℝ (θ : ℝ) (φ : ℝ) (toR3 v) :=
  toLp_cast_mulVec (rotMθℚ_mat_castℝ θ φ) v

lemma toR2_rotMφℚ_mat_mulVec (θ φ : ℚ) (v : Fin 3 → ℚ) :
    toR2 (rotMφℚ_mat θ φ *ᵥ v) = rotMφℚℝ (θ : ℝ) (φ : ℝ) (toR3 v) :=
  toLp_cast_mulVec (rotMφℚ_mat_castℝ θ φ) v

lemma toR2_rotMθθℚ_mat_mulVec (θ φ : ℚ) (v : Fin 3 → ℚ) :
    toR2 (rotMθθℚ_mat θ φ *ᵥ v) = rotMθθℚℝ (θ : ℝ) (φ : ℝ) (toR3 v) :=
  toLp_cast_mulVec (rotMθθℚ_mat_castℝ θ φ) v

lemma toR2_rotMθφℚ_mat_mulVec (θ φ : ℚ) (v : Fin 3 → ℚ) :
    toR2 (rotMθφℚ_mat θ φ *ᵥ v) = rotMθφℚℝ (θ : ℝ) (φ : ℝ) (toR3 v) :=
  toLp_cast_mulVec (rotMθφℚ_mat_castℝ θ φ) v

lemma toR2_rotMφφℚ_mat_mulVec (θ φ : ℚ) (v : Fin 3 → ℚ) :
    toR2 (rotMφφℚ_mat θ φ *ᵥ v) = rotMφφℚℝ (θ : ℝ) (φ : ℝ) (toR3 v) :=
  toLp_cast_mulVec (rotMφφℚ_mat_castℝ θ φ) v

/-! ## Norm atoms

An applied family norm at the real pose/vertex is dominated by the
`UpperSqrt` norm of the rational applied vector plus `3κ` (unit vertices)
or `5κ` (difference vertices, `‖·‖ ≤ 2`). -/

/-- Generic norm atom: `‖A P‖ ≤ su.norm (rational application) + 3κ`. -/
private lemma norm_apply_le_ℚ {A Aq : ℝ³ →L[ℝ] ℝ²} {P : ℝ³} {P_ : Fin 3 → ℚ}
    (su : UpperSqrt) {vℚ : Fin 2 → ℚ}
    (hcast : toR2 vℚ = Aq (toR3 P_))
    (hAdiff : ‖A - Aq‖ ≤ κ) (hAℚnorm : ‖Aq‖ ≤ 1 + κ)
    (hP : ‖P‖ ≤ 1) (hPapprox : ‖P - toR3 P_‖ ≤ κ) :
    ‖A P‖ ≤ (su.norm vℚ : ℝ) + 3 * κ := by
  have h1 : ‖A P - Aq (toR3 P_)‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub hAdiff hAℚnorm hP hPapprox
  have h2 : ‖Aq (toR3 P_)‖ ≤ (su.norm vℚ : ℝ) := by
    rw [← hcast]; exact UpperSqrt_norm_le su vℚ
  have h3 : ‖A P‖ ≤ ‖Aq (toR3 P_)‖ + (2 * κ + κ ^ 2) := by
    linarith [norm_le_insert' (A P) (Aq (toR3 P_))]
  have habsorb : (2 : ℝ) * κ + κ ^ 2 ≤ 3 * κ := by unfold κ; norm_num
  linarith

/-- Generic norm atom at difference scale: `‖P‖ ≤ 2`, `‖P − P_‖ ≤ 2κ` give
`‖A P‖ ≤ su.norm (rational application) + 5κ`. -/
private lemma norm_apply_le_ℚ₂ {A Aq : ℝ³ →L[ℝ] ℝ²} {P : ℝ³} {P_ : Fin 3 → ℚ}
    (su : UpperSqrt) {vℚ : Fin 2 → ℚ}
    (hcast : toR2 vℚ = Aq (toR3 P_))
    (hAdiff : ‖A - Aq‖ ≤ κ) (hAℚnorm : ‖Aq‖ ≤ 1 + κ)
    (hP : ‖P‖ ≤ 2) (hPapprox : ‖P - toR3 P_‖ ≤ 2 * κ) :
    ‖A P‖ ≤ (su.norm vℚ : ℝ) + 5 * κ := by
  have h1 : ‖A P - Aq (toR3 P_)‖ ≤ 4 * κ + 2 * κ ^ 2 :=
    clm_approx_apply_sub₂ hAdiff hAℚnorm hP hPapprox
  have h2 : ‖Aq (toR3 P_)‖ ≤ (su.norm vℚ : ℝ) := by
    rw [← hcast]; exact UpperSqrt_norm_le su vℚ
  have h3 : ‖A P‖ ≤ ‖Aq (toR3 P_)‖ + (4 * κ + 2 * κ ^ 2) := by
    linarith [norm_le_insert' (A P) (Aq (toR3 P_))]
  have habsorb : (4 : ℝ) * κ + 2 * κ ^ 2 ≤ 5 * κ := by unfold κ; norm_num
  linarith

/-! ## `ΔrotMℚ` and `ΔrotRMℚ` -/

/-- Rational upper bound for the outer variation budget `ΔrotM` at a
κ-approximated unit vertex (the `c·κℚ` slack per atom absorbs both the trig
approximation and the vertex approximation; the cubic remainder charges
`‖P‖ ≤ 1`).  `c = 3` at unit scale, `c = 5` at difference scale — the
caller picks via `slack`. -/
def ΔrotMℚs (su : UpperSqrt) (slack θ φ : ℚ) (P_ : Fin 3 → ℚ) (εθ εφ scale : ℚ) : ℚ :=
  εθ * (su.norm (rotMθℚ_mat θ φ *ᵥ P_) + slack)
  + εφ * (su.norm (rotMφℚ_mat θ φ *ᵥ P_) + slack)
  + (1/2) * (εθ^2 * (su.norm (rotMθθℚ_mat θ φ *ᵥ P_) + slack)
      + 2*(εθ*εφ) * (su.norm (rotMθφℚ_mat θ φ *ᵥ P_) + slack)
      + εφ^2 * (su.norm (rotMφφℚ_mat θ φ *ᵥ P_) + slack))
  + scale * (εθ + εφ)^3 / 6

/-- `ΔrotMℚ` at unit-vertex scale. -/
def ΔrotMℚ (su : UpperSqrt) (θ φ : ℚ) (P_ : Fin 3 → ℚ) (εθ εφ : ℚ) : ℚ :=
  ΔrotMℚs su (3 * κℚ) θ φ P_ εθ εφ 1

/-- `ΔrotMℚ` at difference scale (`‖P‖ ≤ 2`, `‖P − P_‖ ≤ 2κ`). -/
def ΔrotMℚ₂ (su : UpperSqrt) (θ φ : ℚ) (P_ : Fin 3 → ℚ) (εθ εφ : ℚ) : ℚ :=
  ΔrotMℚs su (5 * κℚ) θ φ P_ εθ εφ 2

/-- Rational upper bound for the inner variation budget `ΔrotRM` at a
κ-approximated unit vertex. -/
def ΔrotRMℚ (su : UpperSqrt) (θ φ : ℚ) (P_ : Fin 3 → ℚ) (εα εθ εφ : ℚ) : ℚ :=
  εα * (su.norm (rotMℚ_mat θ φ *ᵥ P_) + 3 * κℚ)
  + εθ * (su.norm (rotMθℚ_mat θ φ *ᵥ P_) + 3 * κℚ)
  + εφ * (su.norm (rotMφℚ_mat θ φ *ᵥ P_) + 3 * κℚ)
  + (1/2) * (εα^2 * (su.norm (rotMℚ_mat θ φ *ᵥ P_) + 3 * κℚ)
      + 2*(εα*εθ) * (su.norm (rotMθℚ_mat θ φ *ᵥ P_) + 3 * κℚ)
      + 2*(εα*εφ) * (su.norm (rotMφℚ_mat θ φ *ᵥ P_) + 3 * κℚ)
      + εθ^2 * (su.norm (rotMθθℚ_mat θ φ *ᵥ P_) + 3 * κℚ)
      + 2*(εθ*εφ) * (su.norm (rotMθφℚ_mat θ φ *ᵥ P_) + 3 * κℚ)
      + εφ^2 * (su.norm (rotMφφℚ_mat θ φ *ᵥ P_) + 3 * κℚ))
  + (εα + εθ + εφ)^3 / 6

section BudgetBridges

variable {P : ℝ³} {P_ : Fin 3 → ℚ} {θℚ φℚ : ℚ} {εθ εφ εα : ℚ} (su : UpperSqrt)

/-- Domination of the real outer budget by `ΔrotMℚ`, unit-vertex scale. -/
theorem ΔrotM_le_ℚ
    (hθ : ((θℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ : ((φℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hP : ‖P‖ ≤ 1) (hPapprox : ‖P - toR3 P_‖ ≤ κ)
    (hεθ : 0 ≤ (εθ : ℝ)) (hεφ : 0 ≤ (εφ : ℝ)) :
    GlobalTheorem.ΔrotM P εθ εφ (θℚ : ℝ) (φℚ : ℝ) ≤ ((ΔrotMℚ su θℚ φℚ P_ εθ εφ : ℚ) : ℝ) := by
  have hθ' := norm_apply_le_ℚ su (toR2_rotMθℚ_mat_mulVec θℚ φℚ P_)
    (Mθ_difference_norm_bounded _ _ hθ hφ) (Mθℚ_norm_bounded hθ hφ) hP hPapprox
  have hφ' := norm_apply_le_ℚ su (toR2_rotMφℚ_mat_mulVec θℚ φℚ P_)
    (Mφ_difference_norm_bounded _ _ hθ hφ) (Mφℚ_norm_bounded hθ hφ) hP hPapprox
  have hθθ' := norm_apply_le_ℚ su (toR2_rotMθθℚ_mat_mulVec θℚ φℚ P_)
    (Mθθ_difference_norm_bounded _ _ hθ hφ) (Mθθℚ_norm_bounded hθ hφ) hP hPapprox
  have hθφ' := norm_apply_le_ℚ su (toR2_rotMθφℚ_mat_mulVec θℚ φℚ P_)
    (Mθφ_difference_norm_bounded _ _ hθ hφ) (Mθφℚ_norm_bounded hθ hφ) hP hPapprox
  have hφφ' := norm_apply_le_ℚ su (toR2_rotMφφℚ_mat_mulVec θℚ φℚ P_)
    (Mφφ_difference_norm_bounded _ _ hθ hφ) (Mφφℚ_norm_bounded hθ hφ) hP hPapprox
  have h1 := mul_le_mul_of_nonneg_left hθ' hεθ
  have h2 := mul_le_mul_of_nonneg_left hφ' hεφ
  have h3 := mul_le_mul_of_nonneg_left hθθ' (sq_nonneg (εθ : ℝ))
  have h4 := mul_le_mul_of_nonneg_left hθφ' (mul_nonneg hεθ hεφ)
  have h5 := mul_le_mul_of_nonneg_left hφφ' (sq_nonneg (εφ : ℝ))
  have hE3 : (0 : ℝ) ≤ ((εθ : ℝ) + εφ)^3 := pow_nonneg (by linarith) 3
  have hrem : ‖P‖ * ((εθ : ℝ) + εφ)^3 / 6 ≤ ((εθ : ℝ) + εφ)^3 / 6 := by
    have := mul_le_mul_of_nonneg_right hP hE3
    linarith
  unfold GlobalTheorem.ΔrotM ΔrotMℚ ΔrotMℚs
  push_cast [cast_κℚ]
  linarith

/-- Domination of the real outer budget by `ΔrotMℚ₂`, difference scale. -/
theorem ΔrotM_le_ℚ₂
    (hθ : ((θℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ : ((φℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hP : ‖P‖ ≤ 2) (hPapprox : ‖P - toR3 P_‖ ≤ 2 * κ)
    (hεθ : 0 ≤ (εθ : ℝ)) (hεφ : 0 ≤ (εφ : ℝ)) :
    GlobalTheorem.ΔrotM P εθ εφ (θℚ : ℝ) (φℚ : ℝ) ≤ ((ΔrotMℚ₂ su θℚ φℚ P_ εθ εφ : ℚ) : ℝ) := by
  have hθ' := norm_apply_le_ℚ₂ su (toR2_rotMθℚ_mat_mulVec θℚ φℚ P_)
    (Mθ_difference_norm_bounded _ _ hθ hφ) (Mθℚ_norm_bounded hθ hφ) hP hPapprox
  have hφ' := norm_apply_le_ℚ₂ su (toR2_rotMφℚ_mat_mulVec θℚ φℚ P_)
    (Mφ_difference_norm_bounded _ _ hθ hφ) (Mφℚ_norm_bounded hθ hφ) hP hPapprox
  have hθθ' := norm_apply_le_ℚ₂ su (toR2_rotMθθℚ_mat_mulVec θℚ φℚ P_)
    (Mθθ_difference_norm_bounded _ _ hθ hφ) (Mθθℚ_norm_bounded hθ hφ) hP hPapprox
  have hθφ' := norm_apply_le_ℚ₂ su (toR2_rotMθφℚ_mat_mulVec θℚ φℚ P_)
    (Mθφ_difference_norm_bounded _ _ hθ hφ) (Mθφℚ_norm_bounded hθ hφ) hP hPapprox
  have hφφ' := norm_apply_le_ℚ₂ su (toR2_rotMφφℚ_mat_mulVec θℚ φℚ P_)
    (Mφφ_difference_norm_bounded _ _ hθ hφ) (Mφφℚ_norm_bounded hθ hφ) hP hPapprox
  have h1 := mul_le_mul_of_nonneg_left hθ' hεθ
  have h2 := mul_le_mul_of_nonneg_left hφ' hεφ
  have h3 := mul_le_mul_of_nonneg_left hθθ' (sq_nonneg (εθ : ℝ))
  have h4 := mul_le_mul_of_nonneg_left hθφ' (mul_nonneg hεθ hεφ)
  have h5 := mul_le_mul_of_nonneg_left hφφ' (sq_nonneg (εφ : ℝ))
  have hE3 : (0 : ℝ) ≤ ((εθ : ℝ) + εφ)^3 := pow_nonneg (by linarith) 3
  have hrem : ‖P‖ * ((εθ : ℝ) + εφ)^3 / 6 ≤ 2 * ((εθ : ℝ) + εφ)^3 / 6 := by
    have := mul_le_mul_of_nonneg_right hP hE3
    linarith
  unfold GlobalTheorem.ΔrotM ΔrotMℚ₂ ΔrotMℚs
  push_cast [cast_κℚ]
  linarith

/-- Domination of the real inner budget by `ΔrotRMℚ`. -/
theorem ΔrotRM_le_ℚ
    (hθ : ((θℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ : ((φℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hP : ‖P‖ ≤ 1) (hPapprox : ‖P - toR3 P_‖ ≤ κ)
    (hεα : 0 ≤ (εα : ℝ)) (hεθ : 0 ≤ (εθ : ℝ)) (hεφ : 0 ≤ (εφ : ℝ)) :
    GlobalTheorem.ΔrotRM P εα εθ εφ (θℚ : ℝ) (φℚ : ℝ)
      ≤ ((ΔrotRMℚ su θℚ φℚ P_ εα εθ εφ : ℚ) : ℝ) := by
  have h0' := norm_apply_le_ℚ su (toR2_rotMℚ_mat_mulVec θℚ φℚ P_)
    (M_difference_norm_bounded _ _ hθ hφ) (Mℚ_norm_bounded hθ hφ) hP hPapprox
  have hθ' := norm_apply_le_ℚ su (toR2_rotMθℚ_mat_mulVec θℚ φℚ P_)
    (Mθ_difference_norm_bounded _ _ hθ hφ) (Mθℚ_norm_bounded hθ hφ) hP hPapprox
  have hφ' := norm_apply_le_ℚ su (toR2_rotMφℚ_mat_mulVec θℚ φℚ P_)
    (Mφ_difference_norm_bounded _ _ hθ hφ) (Mφℚ_norm_bounded hθ hφ) hP hPapprox
  have hθθ' := norm_apply_le_ℚ su (toR2_rotMθθℚ_mat_mulVec θℚ φℚ P_)
    (Mθθ_difference_norm_bounded _ _ hθ hφ) (Mθθℚ_norm_bounded hθ hφ) hP hPapprox
  have hθφ' := norm_apply_le_ℚ su (toR2_rotMθφℚ_mat_mulVec θℚ φℚ P_)
    (Mθφ_difference_norm_bounded _ _ hθ hφ) (Mθφℚ_norm_bounded hθ hφ) hP hPapprox
  have hφφ' := norm_apply_le_ℚ su (toR2_rotMφφℚ_mat_mulVec θℚ φℚ P_)
    (Mφφ_difference_norm_bounded _ _ hθ hφ) (Mφφℚ_norm_bounded hθ hφ) hP hPapprox
  have h1 := mul_le_mul_of_nonneg_left h0' hεα
  have h2 := mul_le_mul_of_nonneg_left hθ' hεθ
  have h3 := mul_le_mul_of_nonneg_left hφ' hεφ
  have h4 := mul_le_mul_of_nonneg_left h0' (sq_nonneg (εα : ℝ))
  have h5 := mul_le_mul_of_nonneg_left hθ' (mul_nonneg hεα hεθ)
  have h6 := mul_le_mul_of_nonneg_left hφ' (mul_nonneg hεα hεφ)
  have h7 := mul_le_mul_of_nonneg_left hθθ' (sq_nonneg (εθ : ℝ))
  have h8 := mul_le_mul_of_nonneg_left hθφ' (mul_nonneg hεθ hεφ)
  have h9 := mul_le_mul_of_nonneg_left hφφ' (sq_nonneg (εφ : ℝ))
  have hE3 : (0 : ℝ) ≤ ((εα : ℝ) + εθ + εφ)^3 := pow_nonneg (by linarith) 3
  have hrem : ‖P‖ * ((εα : ℝ) + εθ + εφ)^3 / 6 ≤ ((εα : ℝ) + εθ + εφ)^3 / 6 := by
    have := mul_le_mul_of_nonneg_right hP hE3
    linarith
  unfold GlobalTheorem.ΔrotRM ΔrotRMℚ
  push_cast [cast_κℚ]
  linarith

end BudgetBridges

/-! ## `BoundR₂ℚ` and `BoundDelta₂ℚ` -/

namespace LocalTheorem

/-- The second-order condition on r, rational side: the `3κℚ` absorbs the
rounding of `rotM₂Rℚ` and the real-vs-rational center norm gap. -/
def BoundR₂ℚ (r : ℚ) (p : Pose ℚ) (Q_ : Local.TriangleQ) (εθ εφ : ℚ)
    (approx : Approx) : Prop :=
  ∀ i : Fin 3, approx.lower_sqrt.norm (p.rotM₂Rℚ (Q_ i))
    > r + ΔrotMℚ approx.upper_sqrt p.θ₂ p.φ₂ (Q_ i) εθ εφ + 3 * κℚ

/-- The second-order condition on δ, rational side: center distance via
`UpperSqrt` plus `6κℚ` for the κ-approximations, plus both rational
variation budgets, strictly under `2δ`. -/
def BoundDelta₂ℚ (δ : ℚ) (p : Pose ℚ) (P_ Q_ : Local.TriangleQ)
    (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ) (approx : Approx) : Prop :=
  ∀ i : Fin 3,
    approx.upper_sqrt.norm (p.rotRℚ (p.rotM₁ℚ (P_ i)) - p.rotM₂ℚ (Q_ i)) + 6 * κℚ
      + ΔrotRMℚ approx.upper_sqrt p.θ₁ p.φ₁ (P_ i) εα εθ₁ εφ₁
      + ΔrotMℚ approx.upper_sqrt p.θ₂ p.φ₂ (Q_ i) εθ₂ εφ₂ < 2 * δ

/-- Bridge `BoundR₂ℚ` to the real `BoundR₂`. -/
private lemma boundR₂_bridge {p_ℚ : Pose ℚ} {r εθ εφ : ℚ} {approx : Approx}
    (T : Local.TriangleQ) (R : Triangle)
    (hθ : ((p_ℚ.θ₂ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ : ((p_ℚ.φ₂ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hRnorm : ∀ i : Fin 3, ‖R i‖ ≤ 1)
    (hRapprox : ∀ i : Fin 3, ‖R i - toR3 (T i)‖ ≤ κ)
    (hεθ : 0 ≤ (εθ : ℝ)) (hεφ : 0 ≤ (εφ : ℝ))
    (hr₁ : BoundR₂ℚ r p_ℚ T εθ εφ approx) :
    Local.BoundR₂ r εθ εφ p_ℚ.toReal R := by
  intro i
  set θ₂ : Set.Icc (-4 : ℝ) 4 := ⟨(p_ℚ.θ₂ : ℝ), hθ⟩
  set φ₂ : Set.Icc (-4 : ℝ) 4 := ⟨(p_ℚ.φ₂ : ℝ), hφ⟩
  have h_toR2_eq : (rotMℚℝ ↑θ₂ ↑φ₂) (toR3 (T i)) = toR2 (p_ℚ.rotM₂ℚ (T i)) :=
    (toR2_pose_rotM₂ℚ _ _).symm
  have hsl : (approx.lower_sqrt.norm (p_ℚ.rotM₂Rℚ (T i)) : ℝ) ≤
      ‖(rotMℚℝ ↑θ₂ ↑φ₂) (toR3 (T i))‖ + 2 / 10 ^ 13 := by
    rw [h_toR2_eq]; exact LowerSqrt_norm_round13v_le approx.lower_sqrt _
  have hMQ : |(‖(rotM ↑θ₂ ↑φ₂) (R i)‖ - ‖(rotMℚℝ ↑θ₂ ↑φ₂) (toR3 (T i))‖)| ≤ 2 * κ + κ ^ 2 :=
    (abs_norm_sub_norm_le _ _).trans
      (clm_approx_apply_sub (M_difference_norm_bounded _ _ θ₂.property φ₂.property)
        (Mℚ_norm_bounded θ₂.property φ₂.property) (hRnorm i) (hRapprox i))
  have hΔ : GlobalTheorem.ΔrotM (R i) εθ εφ ↑θ₂ ↑φ₂ ≤
      ((ΔrotMℚ approx.upper_sqrt p_ℚ.θ₂ p_ℚ.φ₂ (T i) εθ εφ : ℚ) : ℝ) :=
    ΔrotM_le_ℚ approx.upper_sqrt hθ hφ (hRnorm i) (hRapprox i) hεθ hεφ
  show r + GlobalTheorem.ΔrotM (R i) εθ εφ (↑θ₂ : ℝ) ↑φ₂ < ‖(rotM ↑θ₂ ↑φ₂) (R i)‖
  have hr₁i : (approx.lower_sqrt.norm (p_ℚ.rotM₂Rℚ (T i)) : ℝ) >
      (r : ℝ) + ((ΔrotMℚ approx.upper_sqrt p_ℚ.θ₂ p_ℚ.φ₂ (T i) εθ εφ : ℚ) : ℝ) + 3 * κ := by
    have hcast : ((approx.lower_sqrt.norm (p_ℚ.rotM₂Rℚ (T i)) : ℚ) : ℝ) >
        ((r + ΔrotMℚ approx.upper_sqrt p_ℚ.θ₂ p_ℚ.φ₂ (T i) εθ εφ + 3 * κℚ : ℚ) : ℝ) :=
      mod_cast hr₁ i
    push_cast [cast_κℚ] at hcast
    linarith
  rw [abs_le] at hMQ
  have hκabsorb : 2 / 10 ^ 13 + (2 * κ + κ ^ 2) ≤ 3 * κ := by unfold κ; norm_num
  linarith [hMQ.1]

/-- Bridge `BoundDelta₂ℚ` to the real `BoundDelta₂`. -/
private lemma boundDelta₂_bridge {p_ℚ : Pose ℚ} {δ εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ} {approx : Approx}
    (T_P T_Q : Local.TriangleQ) (P Q : Triangle)
    (hθ₁b : ((p_ℚ.θ₁ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ₁b : ((p_ℚ.φ₁ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hθ₂b : ((p_ℚ.θ₂ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ₂b : ((p_ℚ.φ₂ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hαb : ((p_ℚ.α : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hPnorm : ∀ i : Fin 3, ‖P i‖ ≤ 1) (hQnorm : ∀ i : Fin 3, ‖Q i‖ ≤ 1)
    (hPapprox : ∀ i : Fin 3, ‖P i - toR3 (T_P i)‖ ≤ κ)
    (hQapprox : ∀ i : Fin 3, ‖Q i - toR3 (T_Q i)‖ ≤ κ)
    (hεα : 0 ≤ (εα : ℝ)) (hεθ₁ : 0 ≤ (εθ₁ : ℝ)) (hεφ₁ : 0 ≤ (εφ₁ : ℝ))
    (hεθ₂ : 0 ≤ (εθ₂ : ℝ)) (hεφ₂ : 0 ≤ (εφ₂ : ℝ))
    (hδ : BoundDelta₂ℚ δ p_ℚ T_P T_Q εα εθ₁ εφ₁ εθ₂ εφ₂ approx) :
    Local.BoundDelta₂ δ εα εθ₁ εφ₁ εθ₂ εφ₂ p_ℚ.toReal P Q := by
  set p_ := p_ℚ.toReal with hp_def
  set P_ := T_P.toReal with hP_def
  set Q_ := T_Q.toReal with hQ_def
  set θ₁ : Set.Icc (-4 : ℝ) 4 := ⟨(p_ℚ.θ₁ : ℝ), hθ₁b⟩
  set φ₁ : Set.Icc (-4 : ℝ) 4 := ⟨(p_ℚ.φ₁ : ℝ), hφ₁b⟩
  set θ₂ : Set.Icc (-4 : ℝ) 4 := ⟨(p_ℚ.θ₂ : ℝ), hθ₂b⟩
  set φ₂ : Set.Icc (-4 : ℝ) 4 := ⟨(p_ℚ.φ₂ : ℝ), hφ₂b⟩
  intro i
  have hδi := hδ i
  -- The center-distance chain, exactly as in the first-order `boundDelta_bridge`.
  have h_eq_real :
      toR2 (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ (T_P i)) - p_ℚ.rotM₂ℚ (T_Q i)) =
      p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i) := by
    rw [toR2_sub, toR2_pose_rotRℚ, toR2_pose_rotM₁ℚ, toR2_pose_rotM₂ℚ]; rfl
  have hsu : ‖p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ ≤
      (approx.upper_sqrt.norm (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ (T_P i)) -
          p_ℚ.rotM₂ℚ (T_Q i)) : ℝ) := by
    rw [← h_eq_real]; exact UpperSqrt_norm_le approx.upper_sqrt _
  have h_rotRdiff : ‖p_.rotR - p_.rotRℚℝ‖ ≤ κ := R_difference_norm_bounded p_.α hαb
  have h_rotM₁ℚ_norm : ‖p_.rotM₁ℚℝ (P_ i)‖ ≤ (1 + κ) * (1 + κ) :=
    approx_image_norm_le (Mℚ_norm_bounded θ₁.property φ₁.property) (hPnorm i) (hPapprox i)
  have h_rotR_diff_apply : ‖p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i))‖ ≤
      κ * ((1 + κ) * (1 + κ)) := by
    have := ContinuousLinearMap.le_opNorm (p_.rotR - p_.rotRℚℝ) (p_.rotM₁ℚℝ (P_ i))
    simp only [sub_apply] at this
    exact this.trans (mul_le_mul h_rotRdiff h_rotM₁ℚ_norm (norm_nonneg _) (by norm_num [κ]))
  have h₁ : ‖(rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub (M_difference_norm_bounded _ _ θ₁.property φ₁.property)
      (Mℚ_norm_bounded θ₁.property φ₁.property) (hPnorm i) (hPapprox i)
  have h₂ : ‖(rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖ ≤ 2 * κ + κ ^ 2 :=
    clm_approx_apply_sub (M_difference_norm_bounded _ _ θ₂.property φ₂.property)
      (Mℚ_norm_bounded θ₂.property φ₂.property) (hQnorm i) (hQapprox i)
  have hdiff : ‖(p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i)) -
      (p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i))‖ ≤ 4 * κ + 2 * κ ^ 2 := by
    show ‖(rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i)) - (rotM ↑θ₂ ↑φ₂) (Q i)) -
          (rotR p_.α ((rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i))‖ ≤ _
    have hrw : rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i)) - (rotM ↑θ₂ ↑φ₂) (Q i) -
          (rotR p_.α ((rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)) =
          rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)) -
          ((rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)) := by
      simp [map_sub]; abel
    rw [hrw]
    calc ‖rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)) -
            ((rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i))‖
      _ ≤ ‖rotR p_.α ((rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i))‖ +
          ‖(rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖ := norm_sub_le _ _
      _ = ‖(rotM ↑θ₁ ↑φ₁) (P i) - (rotMℚℝ ↑θ₁ ↑φ₁) (P_ i)‖ +
          ‖(rotM ↑θ₂ ↑φ₂) (Q i) - (rotMℚℝ ↑θ₂ ↑φ₂) (Q_ i)‖ := by
        rw [Bounding.rotR_preserves_norm]
      _ ≤ (2 * κ + κ ^ 2) + (2 * κ + κ ^ 2) := add_le_add h₁ h₂
      _ = 4 * κ + 2 * κ ^ 2 := by ring
  have hnorm_le : ‖p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i)‖ ≤
      ‖p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ + (4 * κ + 2 * κ ^ 2) := by
    linarith [norm_le_insert' (p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i))
      (p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i))]
  have h_rotR_to_rotRℚℝ : ‖p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ ≤
      ‖p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ + κ * ((1 + κ) * (1 + κ)) := by
    have h_diff_eq : p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i) =
        (p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)) +
        (p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i))) := by abel
    rw [h_diff_eq]
    calc ‖(p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)) +
          (p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)))‖
      _ ≤ ‖p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ +
          ‖p_.rotR (p_.rotM₁ℚℝ (P_ i)) - p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i))‖ := norm_add_le _ _
      _ ≤ ‖p_.rotRℚℝ (p_.rotM₁ℚℝ (P_ i)) - p_.rotM₂ℚℝ (Q_ i)‖ + κ * ((1 + κ) * (1 + κ)) := by
          linarith [h_rotR_diff_apply]
  have h_total_slack : κ * ((1 + κ) * (1 + κ)) + (4 * κ + 2 * κ ^ 2) ≤ 6 * κ := by
    unfold κ; norm_num
  have h_chain : ‖p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i)‖ ≤
      (approx.upper_sqrt.norm (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ (T_P i)) -
          p_ℚ.rotM₂ℚ (T_Q i)) : ℝ) + 6 * κ := by
    linarith [hsu, hnorm_le, h_rotR_to_rotRℚℝ, h_total_slack]
  -- The two budget dominations.
  have hΔRM : GlobalTheorem.ΔrotRM (P i) εα εθ₁ εφ₁ ↑θ₁ ↑φ₁ ≤
      ((ΔrotRMℚ approx.upper_sqrt p_ℚ.θ₁ p_ℚ.φ₁ (T_P i) εα εθ₁ εφ₁ : ℚ) : ℝ) :=
    ΔrotRM_le_ℚ approx.upper_sqrt hθ₁b hφ₁b (hPnorm i) (hPapprox i) hεα hεθ₁ hεφ₁
  have hΔM : GlobalTheorem.ΔrotM (Q i) εθ₂ εφ₂ ↑θ₂ ↑φ₂ ≤
      ((ΔrotMℚ approx.upper_sqrt p_ℚ.θ₂ p_ℚ.φ₂ (T_Q i) εθ₂ εφ₂ : ℚ) : ℝ) :=
    ΔrotM_le_ℚ approx.upper_sqrt hθ₂b hφ₂b (hQnorm i) (hQapprox i) hεθ₂ hεφ₂
  show ‖p_.rotR (p_.rotM₁ (P i)) - p_.rotM₂ (Q i)‖
      + GlobalTheorem.ΔrotRM (P i) εα εθ₁ εφ₁ ↑θ₁ ↑φ₁
      + GlobalTheorem.ΔrotM (Q i) εθ₂ εφ₂ ↑θ₂ ↑φ₂ < 2 * (δ : ℝ)
  have hδiℝ : ((approx.upper_sqrt.norm (p_ℚ.rotRℚ (p_ℚ.rotM₁ℚ (T_P i)) -
        p_ℚ.rotM₂ℚ (T_Q i)) : ℚ) : ℝ) + 6 * κ
      + ((ΔrotRMℚ approx.upper_sqrt p_ℚ.θ₁ p_ℚ.φ₁ (T_P i) εα εθ₁ εφ₁ : ℚ) : ℝ)
      + ((ΔrotMℚ approx.upper_sqrt p_ℚ.θ₂ p_ℚ.φ₂ (T_Q i) εθ₂ εφ₂ : ℚ) : ℝ) < 2 * (δ : ℝ) := by
    have hcast := (Rat.cast_lt (K := ℝ)).mpr hδi
    push_cast [cast_κℚ] at hcast
    linarith
  linarith [h_chain, hΔRM, hΔM, hδiℝ]

end LocalTheorem

/-! ## `ΔvecXℚ` and `Aε₂ℚ` -/

/-- Rational upper bound for the axis-vector budget `ΔvecX` at a
κ-approximated unit vertex. -/
def ΔvecXℚ (θ φ : ℚ) (P_ : Fin 3 → ℚ) (εθ εφ : ℚ) : ℚ :=
  εθ * (|vecXθℚ θ φ ⬝ᵥ P_| + 3 * κℚ) + εφ * (|vecXφℚ θ φ ⬝ᵥ P_| + 3 * κℚ)
  + (1/2) * (εθ^2 * (|vecXθθℚ θ φ ⬝ᵥ P_| + 3 * κℚ)
      + 2*(εθ*εφ) * (|vecXθφℚ θ φ ⬝ᵥ P_| + 3 * κℚ)
      + εφ^2 * (|vecXℚ θ φ ⬝ᵥ P_| + 3 * κℚ))
  + (εθ + εφ)^3/6

/-- Condition `Aε₂ℚ` at a fixed sign, second-order: the trailing `3κℚ`
covers the real-vs-rational gap of the center inner product. -/
def _root_.Local.TriangleQ.Aε₂ℚσ (θ φ : ℚ) (P_ : Local.TriangleQ) (εθ εφ : ℚ)
    (σ : ℕ) : Prop :=
  ∀ i : Fin 3, ΔvecXℚ θ φ (P_ i) εθ εφ + 3 * κℚ < (-1)^σ * (vecXℚ θ φ ⬝ᵥ P_ i)

/-- Condition `A_ε²ℚ` from the second-order rational local theorem. -/
def _root_.Local.TriangleQ.Aε₂ℚ (θ φ : ℚ) (P_ : Local.TriangleQ) (εθ εφ : ℚ) : Prop :=
  ∃ σ : ℕ, Local.TriangleQ.Aε₂ℚσ θ φ P_ εθ εφ σ

section AB2Bridges

variable {R : ℝ³} {T : Fin 3 → ℚ} {θℚ φℚ : ℚ} {εθ εφ : ℚ}

/-- An absolute inner product against the real axis-family vector is
dominated by the rational dot's absolute value plus `3κ`. -/
private lemma abs_inner_le_of_bound {x xq : ℝ³} {q : ℚ}
    (hcast : ⟪xq, toR3 T⟫ = ((q : ℚ) : ℝ))
    (hbound : |⟪x, R⟫ - ⟪xq, toR3 T⟫| ≤ 3 * κ) :
    |⟪x, R⟫| ≤ |((q : ℚ) : ℝ)| + 3 * κ := by
  have h := abs_sub_abs_le_abs_sub ⟪x, R⟫ ⟪xq, toR3 T⟫
  rw [hcast] at h hbound
  linarith

/-- Domination of the real axis budget by `ΔvecXℚ`. -/
theorem ΔvecX_le_ℚ
    (hθ : ((θℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ : ((φℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hR : ‖R‖ ≤ 1) (hRapprox : ‖R - toR3 T‖ ≤ κ)
    (hεθ : 0 ≤ (εθ : ℝ)) (hεφ : 0 ≤ (εφ : ℝ)) :
    GlobalTheorem.ΔvecX R εθ εφ (θℚ : ℝ) (φℚ : ℝ) ≤ ((ΔvecXℚ θℚ φℚ T εθ εφ : ℚ) : ℝ) := by
  set θs : Set.Icc (-4 : ℝ) 4 := ⟨(θℚ : ℝ), hθ⟩
  set φs : Set.Icc (-4 : ℝ) 4 := ⟨(φℚ : ℝ), hφ⟩
  have hθc : ⟪vecXθℚℝ (↑θℚ : ℝ) ↑φℚ, toR3 T⟫ = ((vecXθℚ θℚ φℚ ⬝ᵥ T : ℚ) : ℝ) := by
    rw [← toR3_vecXθℚ]; exact inner_toR3 _ _
  have hφc : ⟪vecXφℚℝ (↑θℚ : ℝ) ↑φℚ, toR3 T⟫ = ((vecXφℚ θℚ φℚ ⬝ᵥ T : ℚ) : ℝ) := by
    rw [← toR3_vecXφℚ]; exact inner_toR3 _ _
  have hθθc : ⟪vecXθθℚℝ (↑θℚ : ℝ) ↑φℚ, toR3 T⟫ = ((vecXθθℚ θℚ φℚ ⬝ᵥ T : ℚ) : ℝ) := by
    rw [← toR3_vecXθθℚ]; exact inner_toR3 _ _
  have hθφc : ⟪vecXθφℚℝ (↑θℚ : ℝ) ↑φℚ, toR3 T⟫ = ((vecXθφℚ θℚ φℚ ⬝ᵥ T : ℚ) : ℝ) := by
    rw [← toR3_vecXθφℚ]; exact inner_toR3 _ _
  have hXc : ⟪vecXℚℝ (↑θℚ : ℝ) ↑φℚ, toR3 T⟫ = ((vecXℚ θℚ φℚ ⬝ᵥ T : ℚ) : ℝ) := by
    rw [← toR3_vecXℚ]; exact inner_toR3 _ _
  have hθ' := abs_inner_le_of_bound hθc (bounds_kappa3_Xθ (θ := θs) (φ := φs) hR hRapprox)
  have hφ' := abs_inner_le_of_bound hφc (bounds_kappa3_Xφ (θ := θs) (φ := φs) hR hRapprox)
  have hθθ' := abs_inner_le_of_bound hθθc (bounds_kappa3_Xθθ (θ := θs) (φ := φs) hR hRapprox)
  have hθφ' := abs_inner_le_of_bound hθφc (bounds_kappa3_Xθφ (θ := θs) (φ := φs) hR hRapprox)
  have hX' : |⟪vecX ↑θℚ ↑φℚ, R⟫| ≤ |((vecXℚ θℚ φℚ ⬝ᵥ T : ℚ) : ℝ)| + 3 * κ := by
    refine abs_inner_le_of_bound hXc ?_
    have := bounds_kappa3_X (θ := θs) (φ := φs) hR hRapprox
    rwa [Real.norm_eq_abs] at this
  have h1 := mul_le_mul_of_nonneg_left hθ' hεθ
  have h2 := mul_le_mul_of_nonneg_left hφ' hεφ
  have h3 := mul_le_mul_of_nonneg_left hθθ' (sq_nonneg (εθ : ℝ))
  have h4 := mul_le_mul_of_nonneg_left hθφ' (mul_nonneg hεθ hεφ)
  have h5 := mul_le_mul_of_nonneg_left hX' (sq_nonneg (εφ : ℝ))
  unfold GlobalTheorem.ΔvecX ΔvecXℚ
  push_cast [cast_κℚ]
  linarith

/-- Bridge `Aε₂ℚ` (rational side) to `Aε₂` (real side). -/
lemma aε₂_bridge (T : Local.TriangleQ) (R : Triangle)
    (hθ : ((θℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ : ((φℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hRnorm : ∀ i : Fin 3, ‖R i‖ ≤ 1)
    (hRapprox : ∀ i : Fin 3, ‖R i - toR3 (T i)‖ ≤ κ)
    (hεθ : 0 ≤ (εθ : ℝ)) (hεφ : 0 ≤ (εφ : ℝ))
    (hAε : T.Aε₂ℚ θℚ φℚ εθ εφ) :
    R.Aε₂ (θℚ : ℝ) (φℚ : ℝ) εθ εφ := by
  obtain ⟨σ, hσ⟩ := hAε
  refine ⟨σ, fun i => ?_⟩
  set θs : Set.Icc (-4 : ℝ) 4 := ⟨(θℚ : ℝ), hθ⟩
  set φs : Set.Icc (-4 : ℝ) 4 := ⟨(φℚ : ℝ), hφ⟩
  have hΔ : GlobalTheorem.ΔvecX (R i) εθ εφ ↑θℚ ↑φℚ ≤
      ((ΔvecXℚ θℚ φℚ (T i) εθ εφ : ℚ) : ℝ) :=
    ΔvecX_le_ℚ hθ hφ (hRnorm i) (hRapprox i) hεθ hεφ
  -- Signed center inner product: within 3κ of the rational dot.
  have hX : |⟪vecX ↑θℚ ↑φℚ, R i⟫ - ((vecXℚ θℚ φℚ ⬝ᵥ T i : ℚ) : ℝ)| ≤ 3 * κ := by
    have h := bounds_kappa3_X (θ := θs) (φ := φs) (hRnorm i) (hRapprox i)
    rw [Real.norm_eq_abs] at h
    rwa [show ⟪vecXℚℝ (↑θℚ : ℝ) ↑φℚ, toR3 (T i)⟫ = ((vecXℚ θℚ φℚ ⬝ᵥ T i : ℚ) : ℝ) from by
      rw [← toR3_vecXℚ]; exact inner_toR3 _ _] at h
  have hsigned : (-1 : ℝ)^σ * ((vecXℚ θℚ φℚ ⬝ᵥ T i : ℚ) : ℝ) - 3 * κ ≤
      (-1 : ℝ)^σ * ⟪vecX ↑θℚ ↑φℚ, R i⟫ := by
    have habs : |(-1 : ℝ)^σ * (⟪vecX ↑θℚ ↑φℚ, R i⟫ - ((vecXℚ θℚ φℚ ⬝ᵥ T i : ℚ) : ℝ))|
        ≤ 3 * κ := by
      rw [abs_mul, abs_neg_one_pow, one_mul]; exact hX
    rw [abs_le] at habs
    linarith [habs.1, mul_sub ((-1 : ℝ)^σ) ⟪vecX ↑θℚ ↑φℚ, R i⟫
      ((vecXℚ θℚ φℚ ⬝ᵥ T i : ℚ) : ℝ)]
  have hσi : ((ΔvecXℚ θℚ φℚ (T i) εθ εφ : ℚ) : ℝ) + 3 * κ <
      (-1 : ℝ)^σ * ((vecXℚ θℚ φℚ ⬝ᵥ T i : ℚ) : ℝ) := by
    have hcast := (Rat.cast_lt (K := ℝ)).mpr (hσ i)
    push_cast [cast_κℚ] at hcast
    linarith [hcast]
  linarith

end AB2Bridges

end RationalApprox
end
