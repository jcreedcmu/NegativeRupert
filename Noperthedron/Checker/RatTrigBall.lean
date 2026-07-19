module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Noperthedron.Checker.RatBall
public import Noperthedron.RationalApprox.TrigLemmas

@[expose] public section


/-!
# Sine and cosine enclosures of rational center-radius balls
-/

namespace Noperthedron.Checker

open RationalApprox

namespace RatBall

def sin (b : RatBall) : RatBall :=
  ⟨RationalApprox.sinℚ b.center, b.radius + κℚ / 7⟩

def cos (b : RatBall) : RatBall :=
  ⟨RationalApprox.cosℚ b.center, b.radius + κℚ / 7⟩

theorem sin_holds {b : RatBall} {x : ℝ}
    (hcenter : (b.center : ℝ) ∈ Set.Icc (-4) 4)
    (hx : b.Holds x) : b.sin.Holds (Real.sin x) := by
  have hlip := Real.abs_sin_sub_sin_le x (b.center : ℝ)
  have happ := RationalApprox.sinℚ_approx' (b.center : ℝ) hcenter
  unfold Holds at hx ⊢
  unfold sin
  simp only [RationalApprox.sinℚ_match]
  calc
    |Real.sin x - RationalApprox.sinℚ (b.center : ℝ)| ≤
        |Real.sin x - Real.sin (b.center : ℝ)| +
          |Real.sin (b.center : ℝ) -
            RationalApprox.sinℚ (b.center : ℝ)| := abs_sub_le _ _ _
    _ ≤ |x - (b.center : ℝ)| + RationalApprox.κ / 7 :=
      add_le_add hlip happ
    _ ≤ (b.radius : ℝ) + RationalApprox.κ / 7 :=
      by linarith
    _ ≤ ((b.radius + κℚ / 7 : ℚ) : ℝ) := by
      have hκ : (RationalApprox.κ : ℝ) =
          ((RationalApprox.κℚ : ℚ) : ℝ) := by
        norm_num [RationalApprox.κ, RationalApprox.κℚ]
      rw [hκ]
      exact_mod_cast (le_refl (b.radius + RationalApprox.κℚ / 7))

theorem cos_holds {b : RatBall} {x : ℝ}
    (hcenter : (b.center : ℝ) ∈ Set.Icc (-4) 4)
    (hx : b.Holds x) : b.cos.Holds (Real.cos x) := by
  have hlip := Real.abs_cos_sub_cos_le x (b.center : ℝ)
  have happ := RationalApprox.cosℚ_approx' (b.center : ℝ) hcenter
  unfold Holds at hx ⊢
  unfold cos
  simp only [RationalApprox.cosℚ_match]
  calc
    |Real.cos x - RationalApprox.cosℚ (b.center : ℝ)| ≤
        |Real.cos x - Real.cos (b.center : ℝ)| +
          |Real.cos (b.center : ℝ) -
            RationalApprox.cosℚ (b.center : ℝ)| := abs_sub_le _ _ _
    _ ≤ |x - (b.center : ℝ)| + RationalApprox.κ / 7 :=
      add_le_add hlip happ
    _ ≤ (b.radius : ℝ) + RationalApprox.κ / 7 :=
      by linarith
    _ ≤ ((b.radius + κℚ / 7 : ℚ) : ℝ) := by
      have hκ : (RationalApprox.κ : ℝ) =
          ((RationalApprox.κℚ : ℚ) : ℝ) := by
        norm_num [RationalApprox.κ, RationalApprox.κℚ]
      rw [hκ]
      exact_mod_cast (le_refl (b.radius + RationalApprox.κℚ / 7))

end RatBall

end Noperthedron.Checker

end
