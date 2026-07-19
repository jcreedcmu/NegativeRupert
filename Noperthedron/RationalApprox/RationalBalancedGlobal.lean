module

public import Noperthedron.BalancedSupport.Global
public import Noperthedron.RationalApprox.RationalGlobal

@[expose] public section


/-!
# Rational balanced global certificates

This is the approximation bridge for translation-cancelling global boxes.
All computational data—directions, weights, vertex indices, and the final
weighted inequality—is rational.  The theorem casts it to the real balanced
global theorem.
-/

namespace RationalApprox.GlobalTheorem

open Noperthedron.BalancedSupport
open GlobalTheorem

/-- Rational data checked for one balanced global box. -/
structure RationalBalancedGlobalPrecondition
    {ι₁ ι₂ κ : Type}
    [Fintype ι₁] [Nonempty ι₁] [Fintype ι₂] [Nonempty ι₂]
    [Fintype κ] [Nonempty κ]
    (poly : GoodPoly ι₁) (poly_ : Polyhedron ι₂ (Fin 3 → ℚ))
    (happrox : κApproxPoly poly.vertices poly_)
    (p : Pose ℚ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ) where
  innerIndex : κ → ι₂
  outerIndex : κ → ι₂
  direction : κ → Fin 2 → ℚ
  direction_unit : ∀ k, ‖toR2 (direction k)‖ = 1
  weight : κ → ℚ
  weight_nonneg : ∀ k, 0 ≤ weight k
  weight_pos : ∃ k, 0 < weight k
  balance : ∑ k, weight k • direction k = 0
  p_in_4 : p ∈ fourInterval ℚ
  dominates :
    ∑ k, weight k * maxHℚ p poly_ εθ₂ εφ₂ (direction k) ≤
      ∑ k, weight k * Gℚ p εα εθ₁ εφ₁
        (poly_.v (innerIndex k)) (direction k)

private theorem cast_balance
    {ι₁ ι₂ κ : Type}
    [Fintype ι₁] [Nonempty ι₁] [Fintype ι₂] [Nonempty ι₂]
    [Fintype κ] [Nonempty κ]
    {poly : GoodPoly ι₁} {poly_ : Polyhedron ι₂ (Fin 3 → ℚ)}
    {happrox : κApproxPoly poly.vertices poly_}
    {p : Pose ℚ} {εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ}
    (pc : RationalBalancedGlobalPrecondition poly poly_ happrox p
      (κ := κ) εα εθ₁ εφ₁ εθ₂ εφ₂) :
    ∑ k, (pc.weight k : ℝ) • toR2 (pc.direction k) = 0 := by
  ext c
  have hb := congrFun pc.balance c
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hb
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero,
    Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, toR2, smul_eq_mul]
  exact_mod_cast hb

/-- Soundness of a rational balanced certificate, uniformly over translation. -/
theorem rational_balanced_global
    {ι₁ ι₂ κ : Type}
    [Fintype ι₁] [Nonempty ι₁] [Fintype ι₂] [Nonempty ι₂]
    [Fintype κ] [Nonempty κ]
    (p : Pose ℚ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ)
    (hεα : 0 ≤ εα) (hεθ₁ : 0 ≤ εθ₁) (hεφ₁ : 0 ≤ εφ₁)
    (hεθ₂ : 0 ≤ εθ₂) (hεφ₂ : 0 ≤ εφ₂)
    (poly : GoodPoly ι₁) (poly_ : Polyhedron ι₂ (Fin 3 → ℚ))
    (happrox : κApproxPoly poly.vertices poly_)
    (pc : RationalBalancedGlobalPrecondition poly poly_ happrox p
      (κ := κ) εα εθ₁ εφ₁ εθ₂ εφ₂) :
    ∀ q, Pose.near p.toReal (εα : ℝ) (εθ₁ : ℝ) (εφ₁ : ℝ)
        (εθ₂ : ℝ) (εφ₂ : ℝ) q →
      ∀ offset : ℝ², ¬ RupertPose (q.matrixPoseWithOffset offset) poly.hull := by
  let realContact : κ → _root_.GlobalTheorem.GlobalContact poly p.toReal
      (εα : ℝ) (εθ₁ : ℝ) (εφ₁ : ℝ) (εθ₂ : ℝ) (εφ₂ : ℝ) :=
    fun k => {
      Si := happrox.bijection.symm (pc.innerIndex k)
      w := toR2 (pc.direction k)
      w_unit := pc.direction_unit k
    }
  let realOuter : κ → ι₁ := fun k => happrox.bijection.symm (pc.outerIndex k)
  let realWeight : κ → ℝ := fun k => (pc.weight k : ℝ)
  have hG (k : κ) :
      ((Gℚ p εα εθ₁ εφ₁ (poly_.v (pc.innerIndex k))
          (pc.direction k) : ℚ) : ℝ) ≤
        _root_.GlobalTheorem.G p.toReal εα εθ₁ εφ₁
          (poly.vertices.v (realContact k).Si) (realContact k).w := by
    have happ := happrox.approx (happrox.bijection.symm (pc.innerIndex k))
    rw [Equiv.apply_symm_apply] at happ
    exact Gℚ_le_G hεα hεθ₁ hεφ₁
      (poly.vertex_radius_le_one _) happ (pc.direction_unit k) pc.p_in_4
  have hH (k : κ) :
      _root_.GlobalTheorem.maxH p.toReal poly εθ₂ εφ₂ (realContact k).w ≤
        ((maxHℚ p poly_ εθ₂ εφ₂ (pc.direction k) : ℚ) : ℝ) :=
    maxH_le_maxHℚ hεθ₂ hεφ₂ poly poly_ happrox
      (pc.direction_unit k) pc.p_in_4
  have hweight_nonneg (k : κ) : 0 ≤ realWeight k := by
    change (0 : ℝ) ≤ (pc.weight k : ℝ)
    exact_mod_cast pc.weight_nonneg k
  have hsumH :
      ∑ k, realWeight k * _root_.GlobalTheorem.maxH p.toReal poly εθ₂ εφ₂ (realContact k).w ≤
        ∑ k, realWeight k *
          ((maxHℚ p poly_ εθ₂ εφ₂ (pc.direction k) : ℚ) : ℝ) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hH k) (hweight_nonneg k)
  have hsumG :
      ∑ k, realWeight k *
          ((Gℚ p εα εθ₁ εφ₁ (poly_.v (pc.innerIndex k))
            (pc.direction k) : ℚ) : ℝ) ≤
        ∑ k, realWeight k *
          _root_.GlobalTheorem.G p.toReal εα εθ₁ εφ₁
            (poly.vertices.v (realContact k).Si) (realContact k).w :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hG k) (hweight_nonneg k)
  have hdominates :
      ∑ k, realWeight k * _root_.GlobalTheorem.maxH p.toReal poly εθ₂ εφ₂ (realContact k).w ≤
        ∑ k, realWeight k *
          _root_.GlobalTheorem.G p.toReal εα εθ₁ εφ₁
            (poly.vertices.v (realContact k).Si) (realContact k).w := by
    have hcast :
        ∑ k, realWeight k *
            ((maxHℚ p poly_ εθ₂ εφ₂ (pc.direction k) : ℚ) : ℝ) ≤
          ∑ k, realWeight k *
            ((Gℚ p εα εθ₁ εφ₁ (poly_.v (pc.innerIndex k))
              (pc.direction k) : ℚ) : ℝ) := by
      dsimp [realWeight]
      exact_mod_cast pc.dominates
    exact hsumH.trans (hcast.trans hsumG)
  apply balanced_global_theorem p.toReal εα εθ₁ εφ₁ εθ₂ εφ₂
    (Rat.cast_nonneg.mpr hεα) (Rat.cast_nonneg.mpr hεθ₁)
    (Rat.cast_nonneg.mpr hεφ₁) (Rat.cast_nonneg.mpr hεθ₂)
    (Rat.cast_nonneg.mpr hεφ₂) poly {
      contact := realContact
      outerIndex := realOuter
      weight := realWeight
      weight_nonneg := hweight_nonneg
      weight_pos := by
        obtain ⟨k, hk⟩ := pc.weight_pos
        refine ⟨k, ?_⟩
        change (0 : ℝ) < (pc.weight k : ℝ)
        exact_mod_cast hk
      balance := cast_balance pc
      dominates := hdominates
    }

end RationalApprox.GlobalTheorem

end
