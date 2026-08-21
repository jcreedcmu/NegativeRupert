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

/-- `ΔrotMℚ` at difference scale (`‖P‖ ≤ 2`, `‖P − P_‖ ≤ 2κ`); `nrm` is a
rational upper bound for `‖P‖`, used only in the cubic remainder. -/
def ΔrotMℚ₂ (su : UpperSqrt) (θ φ : ℚ) (P_ : Fin 3 → ℚ) (εθ εφ nrm : ℚ) : ℚ :=
  ΔrotMℚs su (5 * κℚ) θ φ P_ εθ εφ nrm

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
theorem ΔrotM_le_ℚ₂ {nrm : ℚ}
    (hθ : ((θℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ : ((φℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hP : ‖P‖ ≤ 2) (hPapprox : ‖P - toR3 P_‖ ≤ 2 * κ) (hnrm : ‖P‖ ≤ ((nrm : ℚ) : ℝ))
    (hεθ : 0 ≤ (εθ : ℝ)) (hεφ : 0 ≤ (εφ : ℝ)) :
    GlobalTheorem.ΔrotM P εθ εφ (θℚ : ℝ) (φℚ : ℝ)
      ≤ ((ΔrotMℚ₂ su θℚ φℚ P_ εθ εφ nrm : ℚ) : ℝ) := by
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
  have hrem : ‖P‖ * ((εθ : ℝ) + εφ)^3 / 6 ≤ ((nrm : ℚ) : ℝ) * ((εθ : ℝ) + εφ)^3 / 6 := by
    have := mul_le_mul_of_nonneg_right hnrm hE3
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
deriving Decidable

/-- The second-order condition on δ, rational side: center distance via
`UpperSqrt` plus `6κℚ` for the κ-approximations, plus both rational
variation budgets, strictly under `2δ`. -/
def BoundDelta₂ℚ (δ : ℚ) (p : Pose ℚ) (P_ Q_ : Local.TriangleQ)
    (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ) (approx : Approx) : Prop :=
  ∀ i : Fin 3,
    approx.upper_sqrt.norm (p.rotRℚ (p.rotM₁ℚ (P_ i)) - p.rotM₂ℚ (Q_ i)) + 6 * κℚ
      + ΔrotRMℚ approx.upper_sqrt p.θ₁ p.φ₁ (P_ i) εα εθ₁ εφ₁
      + ΔrotMℚ approx.upper_sqrt p.θ₂ p.φ₂ (Q_ i) εθ₂ εφ₂ < 2 * δ
deriving Decidable

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
deriving Decidable

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

/-! ## Product atoms and `ΔprodMMℚ` -/

/-- The exact rational 90° rotation (the real `rotR (π/2)`). -/
def rot90ℚ : Matrix (Fin 2) (Fin 2) ℚ := !![0, -1; 1, 0]

/-- A `T`-twisted product of two family applications, rationally. -/
def prodTℚ (Tm : Matrix (Fin 2) (Fin 2) ℚ) (Am Bm : Matrix (Fin 2) (Fin 3) ℚ)
    (v w : Fin 3 → ℚ) : ℚ :=
  (Tm *ᵥ (Am *ᵥ v)) ⬝ᵥ (Bm *ᵥ w)

/-- `rotR (π/2)` is exactly the cast of `rot90ℚ`. -/
lemma rotR_pi_div_two_toR2 (u : Fin 2 → ℚ) :
    rotR (π / 2) (toR2 u) = toR2 (rot90ℚ *ᵥ u) := by
  show (rotR_mat (π / 2)).toEuclideanLin.toContinuousLinearMap (toR2 u) =
       toR2 (rot90ℚ *ᵥ u)
  unfold toR2
  have hLHS : (rotR_mat (π / 2)).toEuclideanLin.toContinuousLinearMap
      (WithLp.toLp 2 (fun i : Fin 2 => (u i : ℝ))) =
      WithLp.toLp 2 ((rotR_mat (π / 2)).mulVec (fun i => (u i : ℝ))) := by simp
  rw [hLHS]
  ext i
  have hpi : Real.cos (π / 2) = 0 ∧ Real.sin (π / 2) = 1 :=
    ⟨Real.cos_pi_div_two, Real.sin_pi_div_two⟩
  fin_cases i
  · show ((rotR_mat (π / 2)).mulVec (fun i => (u i : ℝ))) 0 = ((rot90ℚ *ᵥ u) 0 : ℝ)
    simp [rotR_mat, rot90ℚ, hpi.1, hpi.2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · show ((rotR_mat (π / 2)).mulVec (fun i => (u i : ℝ))) 1 = ((rot90ℚ *ᵥ u) 1 : ℝ)
    simp [rotR_mat, rot90ℚ, hpi.1, hpi.2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The identity is exactly the cast of the identity matrix. -/
lemma id_toR2 (u : Fin 2 → ℚ) :
    (ContinuousLinearMap.id ℝ ℝ²) (toR2 u) = toR2 ((1 : Matrix (Fin 2) (Fin 2) ℚ) *ᵥ u) := by
  rw [Matrix.one_mulVec]; rfl

section ProdBridges

variable {T : ℝ² →L[ℝ] ℝ²} {A Aq B Bq : ℝ³ →L[ℝ] ℝ²} {v w : ℝ³} {v_ w_ : Fin 3 → ℚ}

/-- Product atom, unit scale: `|real − rational| ≤ 5κ`. -/
private lemma inner_T_pair_bridge (hT : ‖T‖ ≤ 1)
    (hAd : ‖A - Aq‖ ≤ κ) (hAn : ‖Aq‖ ≤ 1 + κ)
    (hBd : ‖B - Bq‖ ≤ κ) (hB1 : ‖B‖ ≤ 1) (hBn : ‖Bq‖ ≤ 1 + κ)
    (hv : ‖v‖ ≤ 1) (hva : ‖v - toR3 v_‖ ≤ κ)
    (hw : ‖w‖ ≤ 1) (hwa : ‖w - toR3 w_‖ ≤ κ) :
    |⟪T (A v), B w⟫ - ⟪T (Aq (toR3 v_)), Bq (toR3 w_)⟫| ≤ 5 * κ := by
  have h1 : ‖A v - Aq (toR3 v_)‖ ≤ 2 * κ + κ ^ 2 := clm_approx_apply_sub hAd hAn hv hva
  have h2 : ‖B w - Bq (toR3 w_)‖ ≤ 2 * κ + κ ^ 2 := clm_approx_apply_sub hBd hBn hw hwa
  have hBw : ‖B w‖ ≤ 1 := clm_unit_apply_le hB1 hw
  have hAqv : ‖Aq (toR3 v_)‖ ≤ (1 + κ) * (1 + κ) := approx_image_norm_le hAn hv hva
  have hT1 : ‖T (A v) - T (Aq (toR3 v_))‖ ≤ 2 * κ + κ ^ 2 := by
    rw [← map_sub]
    calc ‖T (A v - Aq (toR3 v_))‖ ≤ ‖T‖ * ‖A v - Aq (toR3 v_)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (2 * κ + κ ^ 2) := mul_le_mul hT h1 (norm_nonneg _) (by norm_num)
      _ = 2 * κ + κ ^ 2 := one_mul _
  have hT2 : ‖T (Aq (toR3 v_))‖ ≤ (1 + κ) * (1 + κ) := by
    calc ‖T (Aq (toR3 v_))‖ ≤ ‖T‖ * ‖Aq (toR3 v_)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ((1 + κ) * (1 + κ)) := mul_le_mul hT hAqv (norm_nonneg _) (by norm_num)
      _ = (1 + κ) * (1 + κ) := one_mul _
  have decomp : ⟪T (A v), B w⟫ - ⟪T (Aq (toR3 v_)), Bq (toR3 w_)⟫ =
      ⟪T (A v) - T (Aq (toR3 v_)), B w⟫ + ⟪T (Aq (toR3 v_)), B w - Bq (toR3 w_)⟫ := by
    simp [inner_sub_left, inner_sub_right]
  rw [decomp]
  calc |⟪T (A v) - T (Aq (toR3 v_)), B w⟫ + ⟪T (Aq (toR3 v_)), B w - Bq (toR3 w_)⟫|
    _ ≤ |⟪T (A v) - T (Aq (toR3 v_)), B w⟫| + |⟪T (Aq (toR3 v_)), B w - Bq (toR3 w_)⟫| :=
        abs_add_le _ _
    _ ≤ ‖T (A v) - T (Aq (toR3 v_))‖ * ‖B w‖ + ‖T (Aq (toR3 v_))‖ * ‖B w - Bq (toR3 w_)‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (2 * κ + κ ^ 2) * 1 + ((1 + κ) * (1 + κ)) * (2 * κ + κ ^ 2) :=
        add_le_add
          (mul_le_mul hT1 hBw (norm_nonneg _) (by norm_num [κ]))
          (mul_le_mul hT2 h2 (norm_nonneg _) (by norm_num [κ]))
    _ ≤ 5 * κ := by unfold κ; norm_num

/-- Product atom, difference scale on the `w` slot: `|real − rational| ≤ 9κ`. -/
private lemma inner_T_pair_bridge₂ (hT : ‖T‖ ≤ 1)
    (hAd : ‖A - Aq‖ ≤ κ) (hAn : ‖Aq‖ ≤ 1 + κ)
    (hBd : ‖B - Bq‖ ≤ κ) (hB1 : ‖B‖ ≤ 1) (hBn : ‖Bq‖ ≤ 1 + κ)
    (hv : ‖v‖ ≤ 1) (hva : ‖v - toR3 v_‖ ≤ κ)
    (hw : ‖w‖ ≤ 2) (hwa : ‖w - toR3 w_‖ ≤ 2 * κ) :
    |⟪T (A v), B w⟫ - ⟪T (Aq (toR3 v_)), Bq (toR3 w_)⟫| ≤ 9 * κ := by
  have h1 : ‖A v - Aq (toR3 v_)‖ ≤ 2 * κ + κ ^ 2 := clm_approx_apply_sub hAd hAn hv hva
  have h2 : ‖B w - Bq (toR3 w_)‖ ≤ 4 * κ + 2 * κ ^ 2 := clm_approx_apply_sub₂ hBd hBn hw hwa
  have hBw : ‖B w‖ ≤ 2 := by
    calc ‖B w‖ ≤ ‖B‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * 2 := mul_le_mul hB1 hw (norm_nonneg _) zero_le_one
      _ = 2 := one_mul _
  have hAqv : ‖Aq (toR3 v_)‖ ≤ (1 + κ) * (1 + κ) := approx_image_norm_le hAn hv hva
  have hT1 : ‖T (A v) - T (Aq (toR3 v_))‖ ≤ 2 * κ + κ ^ 2 := by
    rw [← map_sub]
    calc ‖T (A v - Aq (toR3 v_))‖ ≤ ‖T‖ * ‖A v - Aq (toR3 v_)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (2 * κ + κ ^ 2) := mul_le_mul hT h1 (norm_nonneg _) (by norm_num)
      _ = 2 * κ + κ ^ 2 := one_mul _
  have hT2 : ‖T (Aq (toR3 v_))‖ ≤ (1 + κ) * (1 + κ) := by
    calc ‖T (Aq (toR3 v_))‖ ≤ ‖T‖ * ‖Aq (toR3 v_)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ((1 + κ) * (1 + κ)) := mul_le_mul hT hAqv (norm_nonneg _) (by norm_num)
      _ = (1 + κ) * (1 + κ) := one_mul _
  have decomp : ⟪T (A v), B w⟫ - ⟪T (Aq (toR3 v_)), Bq (toR3 w_)⟫ =
      ⟪T (A v) - T (Aq (toR3 v_)), B w⟫ + ⟪T (Aq (toR3 v_)), B w - Bq (toR3 w_)⟫ := by
    simp [inner_sub_left, inner_sub_right]
  rw [decomp]
  calc |⟪T (A v) - T (Aq (toR3 v_)), B w⟫ + ⟪T (Aq (toR3 v_)), B w - Bq (toR3 w_)⟫|
    _ ≤ |⟪T (A v) - T (Aq (toR3 v_)), B w⟫| + |⟪T (Aq (toR3 v_)), B w - Bq (toR3 w_)⟫| :=
        abs_add_le _ _
    _ ≤ ‖T (A v) - T (Aq (toR3 v_))‖ * ‖B w‖ + ‖T (Aq (toR3 v_))‖ * ‖B w - Bq (toR3 w_)‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (2 * κ + κ ^ 2) * 2 + ((1 + κ) * (1 + κ)) * (4 * κ + 2 * κ ^ 2) :=
        add_le_add
          (mul_le_mul hT1 hBw (norm_nonneg _) (by norm_num [κ]))
          (mul_le_mul hT2 h2 (norm_nonneg _) (by norm_num [κ]))
    _ ≤ 9 * κ := by unfold κ; norm_num

end ProdBridges

/-! ## `ΔprodMMℚ` and `Spanning₂ℚ` -/

/-- Rational upper bound for the product budget `ΔprodMM`: each abs-atom is
the rational value plus its leaf count times the per-product `slack`
(`5κℚ` at unit scale, `9κℚ` at difference scale), and the cubic remainder
charges `8·scale` for `8‖v‖‖w‖`. -/
def ΔprodMMℚ (Tm : Matrix (Fin 2) (Fin 2) ℚ) (slack θ φ : ℚ) (v w : Fin 3 → ℚ)
    (εθ εφ scale : ℚ) : ℚ :=
  εθ * (|prodTℚ Tm (rotMθℚ_mat θ φ) (rotMℚ_mat θ φ) v w
        + prodTℚ Tm (rotMℚ_mat θ φ) (rotMθℚ_mat θ φ) v w| + 2 * slack)
  + εφ * (|prodTℚ Tm (rotMφℚ_mat θ φ) (rotMℚ_mat θ φ) v w
        + prodTℚ Tm (rotMℚ_mat θ φ) (rotMφℚ_mat θ φ) v w| + 2 * slack)
  + (1/2) * (εθ^2 * (|prodTℚ Tm (rotMθθℚ_mat θ φ) (rotMℚ_mat θ φ) v w
          + 2 * prodTℚ Tm (rotMθℚ_mat θ φ) (rotMθℚ_mat θ φ) v w
          + prodTℚ Tm (rotMℚ_mat θ φ) (rotMθθℚ_mat θ φ) v w| + 4 * slack)
      + 2*(εθ*εφ) * (|prodTℚ Tm (rotMθφℚ_mat θ φ) (rotMℚ_mat θ φ) v w
          + prodTℚ Tm (rotMθℚ_mat θ φ) (rotMφℚ_mat θ φ) v w
          + prodTℚ Tm (rotMφℚ_mat θ φ) (rotMθℚ_mat θ φ) v w
          + prodTℚ Tm (rotMℚ_mat θ φ) (rotMθφℚ_mat θ φ) v w| + 4 * slack)
      + εφ^2 * (|prodTℚ Tm (rotMφφℚ_mat θ φ) (rotMℚ_mat θ φ) v w
          + 2 * prodTℚ Tm (rotMφℚ_mat θ φ) (rotMφℚ_mat θ φ) v w
          + prodTℚ Tm (rotMℚ_mat θ φ) (rotMφφℚ_mat θ φ) v w| + 4 * slack))
  + 8 * scale * (εθ + εφ)^3 / 6

section ProdMMBridge

variable {T : ℝ² →L[ℝ] ℝ²} {Tm : Matrix (Fin 2) (Fin 2) ℚ}
variable {v w : ℝ³} {v_ w_ : Fin 3 → ℚ} {θℚ φℚ εθ εφ : ℚ}

/-- Cast a `T`-twisted rational product to the real inner product of the
rationally-applied vectors. -/
private lemma prodT_cast (hTcast : ∀ u : Fin 2 → ℚ, T (toR2 u) = toR2 (Tm *ᵥ u))
    {Aq Bq : ℝ³ →L[ℝ] ℝ²} {Am Bm : Matrix (Fin 2) (Fin 3) ℚ}
    (hA : ∀ x : Fin 3 → ℚ, toR2 (Am *ᵥ x) = Aq (toR3 x))
    (hB : ∀ x : Fin 3 → ℚ, toR2 (Bm *ᵥ x) = Bq (toR3 x)) (v_ w_ : Fin 3 → ℚ) :
    ⟪T (Aq (toR3 v_)), Bq (toR3 w_)⟫ = ((prodTℚ Tm Am Bm v_ w_ : ℚ) : ℝ) := by
  rw [← hA, ← hB, hTcast, inner_toR2]
  rfl

private lemma abs_sum2_le {a1 a2 b1 b2 s : ℝ} (h1 : |a1 - b1| ≤ s) (h2 : |a2 - b2| ≤ s) :
    |a1 + a2| ≤ |b1 + b2| + 2 * s := by
  have h := abs_sub_abs_le_abs_sub (a1 + a2) (b1 + b2)
  have h' : |a1 + a2 - (b1 + b2)| ≤ 2 * s := by
    rw [show a1 + a2 - (b1 + b2) = (a1 - b1) + (a2 - b2) from by ring]
    calc |(a1 - b1) + (a2 - b2)| ≤ |a1 - b1| + |a2 - b2| := abs_add_le _ _
      _ ≤ 2 * s := by linarith
  linarith

private lemma abs_sum3w_le {a1 a2 a3 b1 b2 b3 s : ℝ}
    (h1 : |a1 - b1| ≤ s) (h2 : |a2 - b2| ≤ s) (h3 : |a3 - b3| ≤ s) :
    |a1 + 2 * a2 + a3| ≤ |b1 + 2 * b2 + b3| + 4 * s := by
  have h := abs_sub_abs_le_abs_sub (a1 + 2 * a2 + a3) (b1 + 2 * b2 + b3)
  have h' : |a1 + 2 * a2 + a3 - (b1 + 2 * b2 + b3)| ≤ 4 * s := by
    rw [show a1 + 2 * a2 + a3 - (b1 + 2 * b2 + b3)
        = (a1 - b1) + 2 * (a2 - b2) + (a3 - b3) from by ring]
    have habs2 : |2 * (a2 - b2)| ≤ 2 * s := by
      rw [abs_mul, abs_two]; linarith
    calc |(a1 - b1) + 2 * (a2 - b2) + (a3 - b3)|
        ≤ |(a1 - b1) + 2 * (a2 - b2)| + |a3 - b3| := abs_add_le _ _
      _ ≤ |a1 - b1| + |2 * (a2 - b2)| + |a3 - b3| := by
          linarith [abs_add_le (a1 - b1) (2 * (a2 - b2))]
      _ ≤ 4 * s := by linarith
  linarith

private lemma abs_sum4_le {a1 a2 a3 a4 b1 b2 b3 b4 s : ℝ}
    (h1 : |a1 - b1| ≤ s) (h2 : |a2 - b2| ≤ s) (h3 : |a3 - b3| ≤ s) (h4 : |a4 - b4| ≤ s) :
    |a1 + a2 + a3 + a4| ≤ |b1 + b2 + b3 + b4| + 4 * s := by
  have h := abs_sub_abs_le_abs_sub (a1 + a2 + a3 + a4) (b1 + b2 + b3 + b4)
  have h' : |a1 + a2 + a3 + a4 - (b1 + b2 + b3 + b4)| ≤ 4 * s := by
    rw [show a1 + a2 + a3 + a4 - (b1 + b2 + b3 + b4)
        = (a1 - b1) + (a2 - b2) + (a3 - b3) + (a4 - b4) from by ring]
    calc |(a1 - b1) + (a2 - b2) + (a3 - b3) + (a4 - b4)|
        ≤ |(a1 - b1) + (a2 - b2) + (a3 - b3)| + |a4 - b4| := abs_add_le _ _
      _ ≤ |(a1 - b1) + (a2 - b2)| + |a3 - b3| + |a4 - b4| := by
          linarith [abs_add_le ((a1 - b1) + (a2 - b2)) (a3 - b3)]
      _ ≤ |a1 - b1| + |a2 - b2| + |a3 - b3| + |a4 - b4| := by
          linarith [abs_add_le (a1 - b1) (a2 - b2)]
      _ ≤ 4 * s := by linarith
  linarith

/-- Domination of the real product budget by `ΔprodMMℚ` at unit scale. -/
theorem ΔprodMM_le_ℚ (hT : ‖T‖ ≤ 1)
    (hTcast : ∀ u : Fin 2 → ℚ, T (toR2 u) = toR2 (Tm *ᵥ u))
    (hθ : ((θℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ : ((φℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hv : ‖v‖ ≤ 1) (hva : ‖v - toR3 v_‖ ≤ κ)
    (hw : ‖w‖ ≤ 1) (hwa : ‖w - toR3 w_‖ ≤ κ)
    (hεθ : 0 ≤ (εθ : ℝ)) (hεφ : 0 ≤ (εφ : ℝ)) :
    GlobalTheorem.ΔprodMM T v w εθ εφ (θℚ : ℝ) (φℚ : ℝ)
      ≤ ((ΔprodMMℚ Tm (5 * κℚ) θℚ φℚ v_ w_ εθ εφ 1 : ℚ) : ℝ) := by
  -- Per-family facts.
  have dM := M_difference_norm_bounded _ _ hθ hφ
  have nM := Mℚ_norm_bounded hθ hφ
  have oM : ‖rotM (θℚ : ℝ) (φℚ : ℝ)‖ ≤ 1 := le_of_eq (Bounding.rotM_norm_one _ _)
  have dMθ := Mθ_difference_norm_bounded _ _ hθ hφ
  have nMθ := Mθℚ_norm_bounded hθ hφ
  have oMθ := Bounding.rotMθ_norm_le_one (θℚ : ℝ) (φℚ : ℝ)
  have dMφ := Mφ_difference_norm_bounded _ _ hθ hφ
  have nMφ := Mφℚ_norm_bounded hθ hφ
  have oMφ := Bounding.rotMφ_norm_le_one (θℚ : ℝ) (φℚ : ℝ)
  have dMθθ := Mθθ_difference_norm_bounded _ _ hθ hφ
  have nMθθ := Mθθℚ_norm_bounded hθ hφ
  have dMθφ := Mθφ_difference_norm_bounded _ _ hθ hφ
  have nMθφ := Mθφℚ_norm_bounded hθ hφ
  have dMφφ := Mφφ_difference_norm_bounded _ _ hθ hφ
  have nMφφ := Mφφℚ_norm_bounded hθ hφ
  have cM := fun x => toR2_rotMℚ_mat_mulVec θℚ φℚ x
  have cMθ := fun x => toR2_rotMθℚ_mat_mulVec θℚ φℚ x
  have cMφ := fun x => toR2_rotMφℚ_mat_mulVec θℚ φℚ x
  have cMθθ := fun x => toR2_rotMθθℚ_mat_mulVec θℚ φℚ x
  have cMθφ := fun x => toR2_rotMθφℚ_mat_mulVec θℚ φℚ x
  have cMφφ := fun x => toR2_rotMφφℚ_mat_mulVec θℚ φℚ x
  -- One product atom.
  have atom : ∀ (Ar Aq : ℝ³ →L[ℝ] ℝ²) (Am : Matrix (Fin 2) (Fin 3) ℚ)
      (Br Bq : ℝ³ →L[ℝ] ℝ²) (Bm : Matrix (Fin 2) (Fin 3) ℚ),
      ‖Ar - Aq‖ ≤ κ → ‖Aq‖ ≤ 1 + κ → (∀ x, toR2 (Am *ᵥ x) = Aq (toR3 x)) →
      ‖Br - Bq‖ ≤ κ → ‖Br‖ ≤ 1 → ‖Bq‖ ≤ 1 + κ → (∀ x, toR2 (Bm *ᵥ x) = Bq (toR3 x)) →
      |⟪T (Ar v), Br w⟫ - ((prodTℚ Tm Am Bm v_ w_ : ℚ) : ℝ)| ≤ 5 * κ := by
    intro Ar Aq Am Br Bq Bm hAd hAn hAc hBd hB1 hBn hBc
    rw [← prodT_cast hTcast hAc hBc v_ w_]
    exact inner_T_pair_bridge hT hAd hAn hBd hB1 hBn hv hva hw hwa
  have pθM := atom _ _ _ _ _ _ dMθ nMθ cMθ dM oM nM cM
  have pMθ := atom _ _ _ _ _ _ dM nM cM dMθ oMθ nMθ cMθ
  have pφM := atom _ _ _ _ _ _ dMφ nMφ cMφ dM oM nM cM
  have pMφ := atom _ _ _ _ _ _ dM nM cM dMφ oMφ nMφ cMφ
  have pθθM := atom _ _ _ _ _ _ dMθθ nMθθ cMθθ dM oM nM cM
  have pθθ := atom _ _ _ _ _ _ dMθ nMθ cMθ dMθ oMθ nMθ cMθ
  have pMθθ := atom _ _ _ _ _ _ dM nM cM dMθθ (Bounding.rotMθθ_norm_le_one _ _) nMθθ cMθθ
  have pθφM := atom _ _ _ _ _ _ dMθφ nMθφ cMθφ dM oM nM cM
  have pθφa := atom _ _ _ _ _ _ dMθ nMθ cMθ dMφ oMφ nMφ cMφ
  have pθφb := atom _ _ _ _ _ _ dMφ nMφ cMφ dMθ oMθ nMθ cMθ
  have pMθφ := atom _ _ _ _ _ _ dM nM cM dMθφ (Bounding.rotMθφ_norm_le_one _ _) nMθφ cMθφ
  have pφφM := atom _ _ _ _ _ _ dMφφ nMφφ cMφφ dM oM nM cM
  have pφφ := atom _ _ _ _ _ _ dMφ nMφ cMφ dMφ oMφ nMφ cMφ
  have pMφφ := atom _ _ _ _ _ _ dM nM cM dMφφ (Bounding.rotMφφ_norm_le_one _ _) nMφφ cMφφ
  -- The five abs-atoms.
  have aθ := abs_sum2_le pθM pMθ
  have aφ := abs_sum2_le pφM pMφ
  have aθθ := abs_sum3w_le pθθM pθθ pMθθ
  have aθφ := abs_sum4_le pθφM pθφa pθφb pMθφ
  have aφφ := abs_sum3w_le pφφM pφφ pMφφ
  -- Weight and combine.
  have h1 := mul_le_mul_of_nonneg_left aθ hεθ
  have h2 := mul_le_mul_of_nonneg_left aφ hεφ
  have h3 := mul_le_mul_of_nonneg_left aθθ (sq_nonneg (εθ : ℝ))
  have h4 := mul_le_mul_of_nonneg_left aθφ (mul_nonneg hεθ hεφ)
  have h5 := mul_le_mul_of_nonneg_left aφφ (sq_nonneg (εφ : ℝ))
  have hE3 : (0 : ℝ) ≤ ((εθ : ℝ) + εφ)^3 := pow_nonneg (by linarith) 3
  have hrem : 8 * ‖v‖ * ‖w‖ * ((εθ : ℝ) + εφ)^3 / 6 ≤ 8 * 1 * ((εθ : ℝ) + εφ)^3 / 6 := by
    have hvw : ‖v‖ * ‖w‖ ≤ 1 := by
      calc ‖v‖ * ‖w‖ ≤ 1 * 1 := mul_le_mul hv hw (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _
    have := mul_le_mul_of_nonneg_right hvw hE3
    linarith
  unfold GlobalTheorem.ΔprodMM ΔprodMMℚ
  push_cast [cast_κℚ]
  linarith

/-- Domination of the real product budget by `ΔprodMMℚ` at difference scale
on the `w` slot (`‖w‖ ≤ 2`, `‖w − w_‖ ≤ 2κ`); `nrm` is a rational upper
bound for `‖w‖`, used only in the cubic remainder. -/
theorem ΔprodMM_le_ℚ₂ {nrm : ℚ} (hT : ‖T‖ ≤ 1)
    (hTcast : ∀ u : Fin 2 → ℚ, T (toR2 u) = toR2 (Tm *ᵥ u))
    (hθ : ((θℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ : ((φℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hv : ‖v‖ ≤ 1) (hva : ‖v - toR3 v_‖ ≤ κ)
    (hw : ‖w‖ ≤ 2) (hwa : ‖w - toR3 w_‖ ≤ 2 * κ) (hnrm : ‖w‖ ≤ ((nrm : ℚ) : ℝ))
    (hεθ : 0 ≤ (εθ : ℝ)) (hεφ : 0 ≤ (εφ : ℝ)) :
    GlobalTheorem.ΔprodMM T v w εθ εφ (θℚ : ℝ) (φℚ : ℝ)
      ≤ ((ΔprodMMℚ Tm (9 * κℚ) θℚ φℚ v_ w_ εθ εφ nrm : ℚ) : ℝ) := by
  have dM := M_difference_norm_bounded _ _ hθ hφ
  have nM := Mℚ_norm_bounded hθ hφ
  have oM : ‖rotM (θℚ : ℝ) (φℚ : ℝ)‖ ≤ 1 := le_of_eq (Bounding.rotM_norm_one _ _)
  have dMθ := Mθ_difference_norm_bounded _ _ hθ hφ
  have nMθ := Mθℚ_norm_bounded hθ hφ
  have oMθ := Bounding.rotMθ_norm_le_one (θℚ : ℝ) (φℚ : ℝ)
  have dMφ := Mφ_difference_norm_bounded _ _ hθ hφ
  have nMφ := Mφℚ_norm_bounded hθ hφ
  have oMφ := Bounding.rotMφ_norm_le_one (θℚ : ℝ) (φℚ : ℝ)
  have dMθθ := Mθθ_difference_norm_bounded _ _ hθ hφ
  have nMθθ := Mθθℚ_norm_bounded hθ hφ
  have dMθφ := Mθφ_difference_norm_bounded _ _ hθ hφ
  have nMθφ := Mθφℚ_norm_bounded hθ hφ
  have dMφφ := Mφφ_difference_norm_bounded _ _ hθ hφ
  have nMφφ := Mφφℚ_norm_bounded hθ hφ
  have cM := fun x => toR2_rotMℚ_mat_mulVec θℚ φℚ x
  have cMθ := fun x => toR2_rotMθℚ_mat_mulVec θℚ φℚ x
  have cMφ := fun x => toR2_rotMφℚ_mat_mulVec θℚ φℚ x
  have cMθθ := fun x => toR2_rotMθθℚ_mat_mulVec θℚ φℚ x
  have cMθφ := fun x => toR2_rotMθφℚ_mat_mulVec θℚ φℚ x
  have cMφφ := fun x => toR2_rotMφφℚ_mat_mulVec θℚ φℚ x
  have atom : ∀ (Ar Aq : ℝ³ →L[ℝ] ℝ²) (Am : Matrix (Fin 2) (Fin 3) ℚ)
      (Br Bq : ℝ³ →L[ℝ] ℝ²) (Bm : Matrix (Fin 2) (Fin 3) ℚ),
      ‖Ar - Aq‖ ≤ κ → ‖Aq‖ ≤ 1 + κ → (∀ x, toR2 (Am *ᵥ x) = Aq (toR3 x)) →
      ‖Br - Bq‖ ≤ κ → ‖Br‖ ≤ 1 → ‖Bq‖ ≤ 1 + κ → (∀ x, toR2 (Bm *ᵥ x) = Bq (toR3 x)) →
      |⟪T (Ar v), Br w⟫ - ((prodTℚ Tm Am Bm v_ w_ : ℚ) : ℝ)| ≤ 9 * κ := by
    intro Ar Aq Am Br Bq Bm hAd hAn hAc hBd hB1 hBn hBc
    rw [← prodT_cast hTcast hAc hBc v_ w_]
    exact inner_T_pair_bridge₂ hT hAd hAn hBd hB1 hBn hv hva hw hwa
  have pθM := atom _ _ _ _ _ _ dMθ nMθ cMθ dM oM nM cM
  have pMθ := atom _ _ _ _ _ _ dM nM cM dMθ oMθ nMθ cMθ
  have pφM := atom _ _ _ _ _ _ dMφ nMφ cMφ dM oM nM cM
  have pMφ := atom _ _ _ _ _ _ dM nM cM dMφ oMφ nMφ cMφ
  have pθθM := atom _ _ _ _ _ _ dMθθ nMθθ cMθθ dM oM nM cM
  have pθθ := atom _ _ _ _ _ _ dMθ nMθ cMθ dMθ oMθ nMθ cMθ
  have pMθθ := atom _ _ _ _ _ _ dM nM cM dMθθ (Bounding.rotMθθ_norm_le_one _ _) nMθθ cMθθ
  have pθφM := atom _ _ _ _ _ _ dMθφ nMθφ cMθφ dM oM nM cM
  have pθφa := atom _ _ _ _ _ _ dMθ nMθ cMθ dMφ oMφ nMφ cMφ
  have pθφb := atom _ _ _ _ _ _ dMφ nMφ cMφ dMθ oMθ nMθ cMθ
  have pMθφ := atom _ _ _ _ _ _ dM nM cM dMθφ (Bounding.rotMθφ_norm_le_one _ _) nMθφ cMθφ
  have pφφM := atom _ _ _ _ _ _ dMφφ nMφφ cMφφ dM oM nM cM
  have pφφ := atom _ _ _ _ _ _ dMφ nMφ cMφ dMφ oMφ nMφ cMφ
  have pMφφ := atom _ _ _ _ _ _ dM nM cM dMφφ (Bounding.rotMφφ_norm_le_one _ _) nMφφ cMφφ
  have aθ := abs_sum2_le pθM pMθ
  have aφ := abs_sum2_le pφM pMφ
  have aθθ := abs_sum3w_le pθθM pθθ pMθθ
  have aθφ := abs_sum4_le pθφM pθφa pθφb pMθφ
  have aφφ := abs_sum3w_le pφφM pφφ pMφφ
  have h1 := mul_le_mul_of_nonneg_left aθ hεθ
  have h2 := mul_le_mul_of_nonneg_left aφ hεφ
  have h3 := mul_le_mul_of_nonneg_left aθθ (sq_nonneg (εθ : ℝ))
  have h4 := mul_le_mul_of_nonneg_left aθφ (mul_nonneg hεθ hεφ)
  have h5 := mul_le_mul_of_nonneg_left aφφ (sq_nonneg (εφ : ℝ))
  have hE3 : (0 : ℝ) ≤ ((εθ : ℝ) + εφ)^3 := pow_nonneg (by linarith) 3
  have hrem : 8 * ‖v‖ * ‖w‖ * ((εθ : ℝ) + εφ)^3 / 6
      ≤ 8 * ((nrm : ℚ) : ℝ) * ((εθ : ℝ) + εφ)^3 / 6 := by
    have hvw : ‖v‖ * ‖w‖ ≤ ((nrm : ℚ) : ℝ) := by
      calc ‖v‖ * ‖w‖ ≤ 1 * ((nrm : ℚ) : ℝ) :=
            mul_le_mul hv hnrm (norm_nonneg _) zero_le_one
        _ = ((nrm : ℚ) : ℝ) := one_mul _
    have := mul_le_mul_of_nonneg_right hvw hE3
    linarith
  unfold GlobalTheorem.ΔprodMM ΔprodMMℚ
  push_cast [cast_κℚ]
  linarith

private lemma prodTℚ_one (Am Bm : Matrix (Fin 2) (Fin 3) ℚ) (v w : Fin 3 → ℚ) :
    prodTℚ 1 Am Bm v w = (Am *ᵥ v) ⬝ᵥ (Bm *ᵥ w) := by
  unfold prodTℚ; rw [Matrix.one_mulVec]

end ProdMMBridge

/-- **Second-order spanning condition, rational side**: each consecutive
`rot90`-twisted product at the center exceeds its rational budget plus the
`5κℚ` real-vs-rational gap of the center product itself. -/
def _root_.Local.TriangleQ.Spanning₂ℚ (θ φ : ℚ) (P_ : Local.TriangleQ) (εθ εφ : ℚ) : Prop :=
  ∀ i : Fin 3,
    ΔprodMMℚ rot90ℚ (5 * κℚ) θ φ (P_ i) (P_ (i + 1)) εθ εφ 1 + 5 * κℚ
      < prodTℚ rot90ℚ (rotMℚ_mat θ φ) (rotMℚ_mat θ φ) (P_ i) (P_ (i + 1))
deriving Decidable

/-- Bridge `Spanning₂ℚ` (rational side) to `Spanning₂` (real side). -/
lemma spanning₂_bridge {θℚ φℚ εθ εφ : ℚ} (T : Local.TriangleQ) (R : Triangle)
    (hθ : ((θℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ : ((φℚ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hRnorm : ∀ i : Fin 3, ‖R i‖ ≤ 1)
    (hRapprox : ∀ i : Fin 3, ‖R i - toR3 (T i)‖ ≤ κ)
    (hεθ : 0 ≤ (εθ : ℝ)) (hεφ : 0 ≤ (εφ : ℝ))
    (hspan : T.Spanning₂ℚ θℚ φℚ εθ εφ) :
    R.Spanning₂ (θℚ : ℝ) (φℚ : ℝ) εθ εφ := by
  intro i
  have hT90 : ‖rotR (π/2)‖ ≤ 1 := le_of_eq (Bounding.rotR_norm_one _)
  have hΔ : GlobalTheorem.ΔprodMM (rotR (π/2)) (R i) (R (i + 1)) εθ εφ ↑θℚ ↑φℚ ≤
      ((ΔprodMMℚ rot90ℚ (5 * κℚ) θℚ φℚ (T i) (T (i + 1)) εθ εφ 1 : ℚ) : ℝ) :=
    ΔprodMM_le_ℚ hT90 rotR_pi_div_two_toR2 hθ hφ (hRnorm i) (hRapprox i)
      (hRnorm (i + 1)) (hRapprox (i + 1)) hεθ hεφ
  -- Center product: within 5κ of the rational value.
  have hcenter : |⟪rotR (π/2) (rotM ↑θℚ ↑φℚ (R i)), rotM ↑θℚ ↑φℚ (R (i + 1))⟫
      - ((prodTℚ rot90ℚ (rotMℚ_mat θℚ φℚ) (rotMℚ_mat θℚ φℚ) (T i) (T (i + 1)) : ℚ) : ℝ)|
      ≤ 5 * κ := by
    rw [← prodT_cast rotR_pi_div_two_toR2 (fun x => toR2_rotMℚ_mat_mulVec θℚ φℚ x)
      (fun x => toR2_rotMℚ_mat_mulVec θℚ φℚ x) (T i) (T (i + 1))]
    exact inner_T_pair_bridge hT90 (M_difference_norm_bounded _ _ hθ hφ)
      (Mℚ_norm_bounded hθ hφ) (M_difference_norm_bounded _ _ hθ hφ)
      (le_of_eq (Bounding.rotM_norm_one _ _)) (Mℚ_norm_bounded hθ hφ)
      (hRnorm i) (hRapprox i) (hRnorm (i + 1)) (hRapprox (i + 1))
  have hspani : ((ΔprodMMℚ rot90ℚ (5 * κℚ) θℚ φℚ (T i) (T (i + 1)) εθ εφ 1 : ℚ) : ℝ)
      + 5 * κ
      < ((prodTℚ rot90ℚ (rotMℚ_mat θℚ φℚ) (rotMℚ_mat θℚ φℚ) (T i) (T (i + 1)) : ℚ) : ℝ) := by
    have hcast := (Rat.cast_lt (K := ℝ)).mpr (hspan i)
    push_cast [cast_κℚ] at hcast
    linarith
  rw [abs_le] at hcenter
  linarith [hcenter.1]

/-! ## `Bε₂ℚ` and the second-order rational local theorem -/

/-- The slacked rational numerator of `Bε₂.lhs`: rational center product
minus its `9κℚ` gap minus the (difference-scale) product budget.  Positivity
of this quantity is part of the `Bε₂ℚ` condition. -/
def Bε₂ℚnum (θ φ : ℚ) (v₁ dq : Fin 3 → ℚ) (εθ εφ nrm : ℚ) : ℚ :=
  (rotMℚ_mat θ φ *ᵥ v₁) ⬝ᵥ (rotMℚ_mat θ φ *ᵥ dq) - 9 * κℚ
    - ΔprodMMℚ 1 (9 * κℚ) θ φ v₁ dq εθ εφ nrm

/-- Rational upper bound for the norm of the real vertex difference behind a
κ-approximated `dq`. -/
def dqNrm (su : UpperSqrt) (dq : Fin 3 → ℚ) : ℚ :=
  su.norm dq + 2 * κℚ

/-- The rational left-hand side of the second-order `Bε₂` inequality. -/
def Bε₂ℚlhs (su : UpperSqrt) (v₁ v₂ : Fin 3 → ℚ) (p : Pose ℚ) (εθ εφ : ℚ) : ℚ :=
  Bε₂ℚnum p.θ₂ p.φ₂ v₁ (v₁ - v₂) εθ εφ (dqNrm su (v₁ - v₂))
  / ((su.norm (rotMℚ_mat p.θ₂ p.φ₂ *ᵥ v₁) + 3 * κℚ + ΔrotMℚ su p.θ₂ p.φ₂ v₁ εθ εφ)
     * (su.norm (rotMℚ_mat p.θ₂ p.φ₂ *ᵥ (v₁ - v₂)) + 5 * κℚ
        + ΔrotMℚ₂ su p.θ₂ p.φ₂ (v₁ - v₂) εθ εφ (dqNrm su (v₁ - v₂))))

/-- Condition `B_ε²ℚ` from the second-order rational local theorem. -/
def _root_.Local.TriangleQ.Bε₂ℚ {ι : Type} [Fintype ι] [DecidableEq ι] (Qi : Fin 3 → ι)
    (v_ : ι → Fin 3 → ℚ) (p : Pose ℚ) (εθ εφ δ r : ℚ) (su : UpperSqrt) : Prop :=
  ∀ i : Fin 3, ∀ k : ι, k ≠ Qi i →
    0 < Bε₂ℚnum p.θ₂ p.φ₂ (v_ (Qi i)) (v_ (Qi i) - v_ k) εθ εφ
        (dqNrm su (v_ (Qi i) - v_ k))
    ∧ δ / r < Bε₂ℚlhs su (v_ (Qi i)) (v_ k) p εθ εφ
deriving Decidable

namespace LocalTheorem

/-- Bridge `Bε₂ℚ` (rational side) to `Bε₂` (real side). -/
private lemma bε₂_bridge {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {poly : GoodPoly ι} {poly_ : Polyhedron ι (Fin 3 → ℚ)}
    (hpoly : κApproxPoly poly.vertices poly_)
    (Qi : Fin 3 → ι) {p_ℚ : Pose ℚ} {εθ εφ δ r : ℚ} {approx : Approx}
    (hθ₂b : ((p_ℚ.θ₂ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4) (hφ₂b : ((p_ℚ.φ₂ : ℝ)) ∈ Set.Icc (-4 : ℝ) 4)
    (hεθ : 0 ≤ (εθ : ℝ)) (hεφ : 0 ≤ (εφ : ℝ))
    (be : Local.TriangleQ.Bε₂ℚ Qi (fun k => poly_.v (hpoly.bijection k)) p_ℚ εθ εφ δ r
      approx.upper_sqrt) :
    Local.Bε₂ Qi poly.vertices.v p_ℚ.toReal εθ εφ δ r := by
  set p_ := p_ℚ.toReal with hp_def
  intro i k hne_k
  -- Rational and real data for this pair.
  let Qℚ : Fin 3 → ℚ := poly_.v (hpoly.bijection (Qi i))
  let vℚ : Fin 3 → ℚ := poly_.v (hpoly.bijection k)
  set Qr : ℝ³ := poly.vertices.v (Qi i) with hQr
  set vk : ℝ³ := poly.vertices.v k with hvk
  have hQnorm : ‖Qr‖ ≤ 1 := poly.vertex_radius_le_one (Qi i)
  have hvnorm : ‖vk‖ ≤ 1 := poly.vertex_radius_le_one k
  have hQapprox : ‖Qr - toR3 Qℚ‖ ≤ κ := hpoly.approx (Qi i)
  have hvapprox : ‖vk - toR3 vℚ‖ ≤ κ := hpoly.approx k
  have hdqnorm : ‖Qr - vk‖ ≤ 2 := by
    calc ‖Qr - vk‖ ≤ ‖Qr‖ + ‖vk‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  have hdqapprox : ‖(Qr - vk) - toR3 (Qℚ - vℚ)‖ ≤ 2 * κ := by
    rw [toR3_sub]
    calc ‖(Qr - vk) - (toR3 Qℚ - toR3 vℚ)‖
        = ‖(Qr - toR3 Qℚ) - (vk - toR3 vℚ)‖ := by congr 1; abel
      _ ≤ ‖Qr - toR3 Qℚ‖ + ‖vk - toR3 vℚ‖ := norm_sub_le _ _
      _ ≤ 2 * κ := by linarith
  have hdq_nrm : ‖Qr - vk‖ ≤ ((dqNrm approx.upper_sqrt (Qℚ - vℚ) : ℚ) : ℝ) := by
    have h1 : ‖Qr - vk‖ ≤ ‖toR3 (Qℚ - vℚ)‖ + 2 * κ := by
      linarith [norm_le_insert' (Qr - vk) (toR3 (Qℚ - vℚ)), hdqapprox]
    have h2 : ‖toR3 (Qℚ - vℚ)‖ ≤ ((approx.upper_sqrt.norm (Qℚ - vℚ) : ℚ) : ℝ) :=
      UpperSqrt_norm_le approx.upper_sqrt _
    unfold dqNrm
    push_cast [cast_κℚ]
    linarith
  obtain ⟨hposℚ, hlhsℚ⟩ := be i k hne_k
  -- Center product gap (T = id, difference scale): within 9κ.
  have hid1 : ‖ContinuousLinearMap.id ℝ ℝ²‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hcenter : |⟪rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ Qr, rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ (Qr - vk)⟫
      - (((rotMℚ_mat p_ℚ.θ₂ p_ℚ.φ₂ *ᵥ Qℚ) ⬝ᵥ (rotMℚ_mat p_ℚ.θ₂ p_ℚ.φ₂ *ᵥ (Qℚ - vℚ)) : ℚ)
        : ℝ)| ≤ 9 * κ := by
    have h := inner_T_pair_bridge₂ (T := ContinuousLinearMap.id ℝ ℝ²) hid1
      (M_difference_norm_bounded _ _ hθ₂b hφ₂b) (Mℚ_norm_bounded hθ₂b hφ₂b)
      (M_difference_norm_bounded _ _ hθ₂b hφ₂b)
      (le_of_eq (Bounding.rotM_norm_one _ _)) (Mℚ_norm_bounded hθ₂b hφ₂b)
      hQnorm hQapprox hdqnorm hdqapprox
    rw [prodT_cast (Tm := 1) id_toR2 (fun x => toR2_rotMℚ_mat_mulVec p_ℚ.θ₂ p_ℚ.φ₂ x)
      (fun x => toR2_rotMℚ_mat_mulVec p_ℚ.θ₂ p_ℚ.φ₂ x) Qℚ (Qℚ - vℚ), prodTℚ_one] at h
    simpa using h
  -- Product budget domination (T = id, difference scale).
  have hΔprod : GlobalTheorem.ΔprodMM (ContinuousLinearMap.id ℝ ℝ²) Qr (Qr - vk)
      εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂
      ≤ ((ΔprodMMℚ 1 (9 * κℚ) p_ℚ.θ₂ p_ℚ.φ₂ Qℚ (Qℚ - vℚ) εθ εφ
          (dqNrm approx.upper_sqrt (Qℚ - vℚ)) : ℚ) : ℝ) :=
    ΔprodMM_le_ℚ₂ hid1 id_toR2 hθ₂b hφ₂b hQnorm hQapprox hdqnorm hdqapprox hdq_nrm
      hεθ hεφ
  have hΔprod_nn : 0 ≤ GlobalTheorem.ΔprodMM (ContinuousLinearMap.id ℝ ℝ²) Qr (Qr - vk)
      εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ := GlobalTheorem.ΔprodMM_nonneg hεθ hεφ
  -- The slacked rational numerator, cast.
  have hnumℚpos : (0 : ℝ) < ((Bε₂ℚnum p_ℚ.θ₂ p_ℚ.φ₂ Qℚ (Qℚ - vℚ) εθ εφ
      (dqNrm approx.upper_sqrt (Qℚ - vℚ)) : ℚ) : ℝ) := by
    exact_mod_cast hposℚ
  have hnumcast : ((Bε₂ℚnum p_ℚ.θ₂ p_ℚ.φ₂ Qℚ (Qℚ - vℚ) εθ εφ
      (dqNrm approx.upper_sqrt (Qℚ - vℚ)) : ℚ) : ℝ)
      = (((rotMℚ_mat p_ℚ.θ₂ p_ℚ.φ₂ *ᵥ Qℚ) ⬝ᵥ (rotMℚ_mat p_ℚ.θ₂ p_ℚ.φ₂ *ᵥ (Qℚ - vℚ)) : ℚ) : ℝ)
        - 9 * κ - ((ΔprodMMℚ 1 (9 * κℚ) p_ℚ.θ₂ p_ℚ.φ₂ Qℚ (Qℚ - vℚ) εθ εφ
          (dqNrm approx.upper_sqrt (Qℚ - vℚ)) : ℚ) : ℝ) := by
    unfold Bε₂ℚnum
    push_cast [cast_κℚ]
    ring
  -- Real numerator dominates the cast rational numerator.
  rw [abs_le] at hcenter
  have hRN : ((Bε₂ℚnum p_ℚ.θ₂ p_ℚ.φ₂ Qℚ (Qℚ - vℚ) εθ εφ
      (dqNrm approx.upper_sqrt (Qℚ - vℚ)) : ℚ) : ℝ)
      ≤ ⟪rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ Qr, rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ (Qr - vk)⟫
        - GlobalTheorem.ΔprodMM (ContinuousLinearMap.id ℝ ℝ²) Qr (Qr - vk)
          εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ := by
    rw [hnumcast]
    linarith [hcenter.1, hΔprod]
  -- First conjunct: real numerator positive.
  have hpos_real : 0 < ⟪rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ Qr, rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ (Qr - vk)⟫
      - GlobalTheorem.ΔprodMM (ContinuousLinearMap.id ℝ ℝ²) Qr (Qr - vk)
        εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ := lt_of_lt_of_le hnumℚpos hRN
  refine ⟨hpos_real, ?_⟩
  -- Real center product is positive, so the real norms are positive.
  have hcenter_pos : 0 < ⟪rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ Qr, rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ (Qr - vk)⟫ := by
    linarith [hpos_real, hΔprod_nn]
  have hn1 : 0 < ‖rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ Qr‖ := by
    by_contra hle
    push Not at hle
    have hz : rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ Qr = 0 :=
      norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    rw [show (⟪rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ Qr, rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ (Qr - vk)⟫ : ℝ)
        = ⟪(0 : ℝ²), rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ (Qr - vk)⟫ from by rw [hz],
      inner_zero_left] at hcenter_pos
    exact lt_irrefl 0 hcenter_pos
  have hn2 : 0 < ‖rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ (Qr - vk)‖ := by
    by_contra hle
    push Not at hle
    have hz : rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ (Qr - vk) = 0 :=
      norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    rw [hz, inner_zero_right] at hcenter_pos
    exact lt_irrefl 0 hcenter_pos
  -- Denominator dominations.
  have hD1 : ‖rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ Qr‖ ≤
      ((approx.upper_sqrt.norm (rotMℚ_mat p_ℚ.θ₂ p_ℚ.φ₂ *ᵥ Qℚ) : ℚ) : ℝ) + 3 * κ :=
    norm_apply_le_ℚ approx.upper_sqrt (toR2_rotMℚ_mat_mulVec p_ℚ.θ₂ p_ℚ.φ₂ Qℚ)
      (M_difference_norm_bounded _ _ hθ₂b hφ₂b) (Mℚ_norm_bounded hθ₂b hφ₂b)
      hQnorm hQapprox
  have hD2 : ‖rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ (Qr - vk)‖ ≤
      ((approx.upper_sqrt.norm (rotMℚ_mat p_ℚ.θ₂ p_ℚ.φ₂ *ᵥ (Qℚ - vℚ)) : ℚ) : ℝ) + 5 * κ :=
    norm_apply_le_ℚ₂ approx.upper_sqrt (toR2_rotMℚ_mat_mulVec p_ℚ.θ₂ p_ℚ.φ₂ (Qℚ - vℚ))
      (M_difference_norm_bounded _ _ hθ₂b hφ₂b) (Mℚ_norm_bounded hθ₂b hφ₂b)
      hdqnorm hdqapprox
  have hΔ1 : GlobalTheorem.ΔrotM Qr εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ ≤
      ((ΔrotMℚ approx.upper_sqrt p_ℚ.θ₂ p_ℚ.φ₂ Qℚ εθ εφ : ℚ) : ℝ) :=
    ΔrotM_le_ℚ approx.upper_sqrt hθ₂b hφ₂b hQnorm hQapprox hεθ hεφ
  have hΔ2 : GlobalTheorem.ΔrotM (Qr - vk) εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ ≤
      ((ΔrotMℚ₂ approx.upper_sqrt p_ℚ.θ₂ p_ℚ.φ₂ (Qℚ - vℚ) εθ εφ
        (dqNrm approx.upper_sqrt (Qℚ - vℚ)) : ℚ) : ℝ) :=
    ΔrotM_le_ℚ₂ approx.upper_sqrt hθ₂b hφ₂b hdqnorm hdqapprox hdq_nrm hεθ hεφ
  have hΔ1_nn : 0 ≤ GlobalTheorem.ΔrotM Qr εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ :=
    GlobalTheorem.ΔrotM_nonneg hεθ hεφ
  have hΔ2_nn : 0 ≤ GlobalTheorem.ΔrotM (Qr - vk) εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ :=
    GlobalTheorem.ΔrotM_nonneg hεθ hεφ
  -- Positive real denominators.
  have hd1_pos : 0 < ‖rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ Qr‖
      + GlobalTheorem.ΔrotM Qr εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ := by linarith
  have hd2_pos : 0 < ‖rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ (Qr - vk)‖
      + GlobalTheorem.ΔrotM (Qr - vk) εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ := by linarith
  -- Chain the divisions.
  set N : ℝ := ((Bε₂ℚnum p_ℚ.θ₂ p_ℚ.φ₂ Qℚ (Qℚ - vℚ) εθ εφ
      (dqNrm approx.upper_sqrt (Qℚ - vℚ)) : ℚ) : ℝ) with hNdef
  set D1 : ℝ := ((approx.upper_sqrt.norm (rotMℚ_mat p_ℚ.θ₂ p_ℚ.φ₂ *ᵥ Qℚ) : ℚ) : ℝ)
      + 3 * κ + ((ΔrotMℚ approx.upper_sqrt p_ℚ.θ₂ p_ℚ.φ₂ Qℚ εθ εφ : ℚ) : ℝ) with hD1def
  set D2 : ℝ := ((approx.upper_sqrt.norm (rotMℚ_mat p_ℚ.θ₂ p_ℚ.φ₂ *ᵥ (Qℚ - vℚ)) : ℚ) : ℝ)
      + 5 * κ + ((ΔrotMℚ₂ approx.upper_sqrt p_ℚ.θ₂ p_ℚ.φ₂ (Qℚ - vℚ) εθ εφ
        (dqNrm approx.upper_sqrt (Qℚ - vℚ)) : ℚ) : ℝ)
    with hD2def
  have hlhsℚr : ((δ : ℚ) : ℝ) / r < N / (D1 * D2) := by
    have hcast := (Rat.cast_lt (K := ℝ)).mpr hlhsℚ
    unfold Bε₂ℚlhs at hcast
    rw [hNdef, hD1def, hD2def]
    push_cast [cast_κℚ] at hcast ⊢
    convert hcast using 2
  refine hlhsℚr.trans_le ?_
  unfold Local.Bε₂.lhs
  show N / (D1 * D2) ≤
    (⟪rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ Qr, rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ (Qr - vk)⟫
      - GlobalTheorem.ΔprodMM (ContinuousLinearMap.id ℝ ℝ²) Qr (Qr - vk)
        εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂)
    / ((‖rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ Qr‖ + GlobalTheorem.ΔrotM Qr εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂)
       * (‖rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ (Qr - vk)‖
          + GlobalTheorem.ΔrotM (Qr - vk) εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂))
  refine div_le_div₀ (le_of_lt hpos_real) hRN (mul_pos hd1_pos hd2_pos) ?_
  have hf1 : ‖rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ Qr‖
      + GlobalTheorem.ΔrotM Qr εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ ≤ D1 := by
    rw [hD1def]
    linarith
  have hf2 : ‖rotM ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ (Qr - vk)‖
      + GlobalTheorem.ΔrotM (Qr - vk) εθ εφ ↑p_ℚ.θ₂ ↑p_ℚ.φ₂ ≤ D2 := by
    rw [hD2def]
    linarith
  exact mul_le_mul hf1 hf2 (le_of_lt hd2_pos) (le_of_lt (lt_of_lt_of_le hd1_pos hf1))

/--
The second-order rational local theorem precondition: the per-axis-radii
analog of `RationalLocalTheoremPrecondition`, with every condition in its
second-order rational form.  This is the form the computational checker
produces.
-/
structure RationalLocalTheoremPrecondition₂ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (poly : GoodPoly ι) (poly_ : Polyhedron ι (Fin 3 → ℚ))
    (hpoly : κApproxPoly poly.vertices poly_)
    (p_ : Pose ℚ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ) : Type where
  Pi : Fin 3 → ι
  Qi : Fin 3 → ι
  cong_tri : Triangle.Congruent (poly.vertices.v ∘ Pi) (poly.vertices.v ∘ Qi)
  hp : p_ ∈ fourInterval ℚ
  hεα : 0 ≤ εα
  hεθ₁ : 0 ≤ εθ₁
  hεφ₁ : 0 ≤ εφ₁
  hεθ₂ : 0 ≤ εθ₂
  hεφ₂ : 0 ≤ εφ₂
  δ : ℚ
  r : ℚ
  hr : 0 < r
  approx : Approx
  hr₁ : BoundR₂ℚ r p_ (hpoly.transportTri Qi) εθ₂ εφ₂ approx
  hδ : BoundDelta₂ℚ δ p_ (hpoly.transportTri Pi) (hpoly.transportTri Qi)
    εα εθ₁ εφ₁ εθ₂ εφ₂ approx
  ae₁ : (hpoly.transportTri Pi).Aε₂ℚ p_.θ₁ p_.φ₁ εθ₁ εφ₁
  ae₂ : (hpoly.transportTri Qi).Aε₂ℚ p_.θ₂ p_.φ₂ εθ₂ εφ₂
  span₁ : (hpoly.transportTri Pi).Spanning₂ℚ p_.θ₁ p_.φ₁ εθ₁ εφ₁
  span₂ : (hpoly.transportTri Qi).Spanning₂ℚ p_.θ₂ p_.φ₂ εθ₂ εφ₂
  be : Local.TriangleQ.Bε₂ℚ Qi (fun k => poly_.v (hpoly.bijection k)) p_ εθ₂ εφ₂ δ r
    approx.upper_sqrt

/--
The second-order Rational Local Theorem: the rational precondition rules
out Rupert poses in the whole per-axis box around `p_`.
-/
theorem rational_local₂ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (poly : GoodPoly ι) (poly_ : Polyhedron ι (Fin 3 → ℚ))
    (hpoly : κApproxPoly poly.vertices poly_)
    (p_ : Pose ℚ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ)
    (pc : RationalLocalTheoremPrecondition₂ poly poly_ hpoly p_ εα εθ₁ εφ₁ εθ₂ εφ₂) :
    ¬∃ p, Pose.near p_.toReal εα εθ₁ εφ₁ εθ₂ εφ₂ p ∧ RupertPose p poly.hull := by
  obtain ⟨Pi, Qi, cong_tri, hp, hεα, hεθ₁, hεφ₁, hεθ₂, hεφ₂, δ, r, hr, approx,
          hr₁, hδ, ae₁, ae₂, span₁, span₂, be⟩ := pc
  let p_ℚ : Pose ℚ := p_
  set p_ := p_.toReal
  have hp4 : (fourInterval ℝ).contains p_ := fourInterval_contains_toReal hp
  let P : Triangle := fun i => poly.vertices.v (Pi i)
  let Q : Triangle := fun i => poly.vertices.v (Qi i)
  have hPnorm (i : Fin 3) : ‖P i‖ ≤ 1 := poly.vertex_radius_le_one (Pi i)
  have hQnorm (i : Fin 3) : ‖Q i‖ ≤ 1 := poly.vertex_radius_le_one (Qi i)
  have hPapprox (i : Fin 3) : ‖P i - toR3 (hpoly.transportTri Pi i)‖ ≤ κ := hpoly.approx (Pi i)
  have hQapprox (i : Fin 3) : ‖Q i - toR3 (hpoly.transportTri Qi i)‖ ≤ κ := hpoly.approx (Qi i)
  have hεαr : 0 ≤ (εα : ℝ) := by exact_mod_cast hεα
  have hεθ₁r : 0 ≤ (εθ₁ : ℝ) := by exact_mod_cast hεθ₁
  have hεφ₁r : 0 ≤ (εφ₁ : ℝ) := by exact_mod_cast hεφ₁
  have hεθ₂r : 0 ≤ (εθ₂ : ℝ) := by exact_mod_cast hεθ₂
  have hεφ₂r : 0 ≤ (εφ₂ : ℝ) := by exact_mod_cast hεφ₂
  have hr₁' : Local.BoundR₂ r εθ₂ εφ₂ p_ Q :=
    boundR₂_bridge (hpoly.transportTri Qi) Q hp4.θ₂Bound hp4.φ₂Bound hQnorm hQapprox
      hεθ₂r hεφ₂r hr₁
  have hδ' : Local.BoundDelta₂ δ εα εθ₁ εφ₁ εθ₂ εφ₂ p_ P Q :=
    boundDelta₂_bridge (hpoly.transportTri Pi) (hpoly.transportTri Qi) P Q
      hp4.θ₁Bound hp4.φ₁Bound hp4.θ₂Bound hp4.φ₂Bound hp4.αBound
      hPnorm hQnorm hPapprox hQapprox hεαr hεθ₁r hεφ₁r hεθ₂r hεφ₂r hδ
  have ae₁' : P.Aε₂ p_.θ₁ p_.φ₁ εθ₁ εφ₁ :=
    aε₂_bridge (hpoly.transportTri Pi) P hp4.θ₁Bound hp4.φ₁Bound hPnorm hPapprox
      hεθ₁r hεφ₁r ae₁
  have ae₂' : Q.Aε₂ p_.θ₂ p_.φ₂ εθ₂ εφ₂ :=
    aε₂_bridge (hpoly.transportTri Qi) Q hp4.θ₂Bound hp4.φ₂Bound hQnorm hQapprox
      hεθ₂r hεφ₂r ae₂
  have span₁' : P.Spanning₂ p_.θ₁ p_.φ₁ εθ₁ εφ₁ :=
    spanning₂_bridge (hpoly.transportTri Pi) P hp4.θ₁Bound hp4.φ₁Bound hPnorm hPapprox
      hεθ₁r hεφ₁r span₁
  have span₂' : Q.Spanning₂ p_.θ₂ p_.φ₂ εθ₂ εφ₂ :=
    spanning₂_bridge (hpoly.transportTri Qi) Q hp4.θ₂Bound hp4.φ₂Bound hQnorm hQapprox
      hεθ₂r hεφ₂r span₂
  have be' : Local.Bε₂ Qi poly.vertices.v p_ εθ₂ εφ₂ δ r :=
    bε₂_bridge hpoly Qi hp4.θ₂Bound hp4.φ₂Bound hεθ₂r hεφ₂r be
  exact Local.local_theorem₂ poly p_ εα εθ₁ εφ₁ εθ₂ εφ₂ hεαr hεθ₁r hεφ₁r hεθ₂r hεφ₂r
    { Pi := Pi, Qi := Qi, cong_tri := cong_tri, δ := δ, r := r,
      hr := Rat.cast_pos.mpr hr,
      hr₁ := hr₁', hδ := hδ', ae₁ := ae₁', ae₂ := ae₂',
      span₁ := span₁', span₂ := span₂', be := be' }

end LocalTheorem

end RationalApprox
end
