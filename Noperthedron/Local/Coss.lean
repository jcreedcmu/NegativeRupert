module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.InnerProductSpace.PiL2

public import Noperthedron.Bounding
public import Noperthedron.Local.Prelims

public section


namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

/-- [SY25] Lemma 33 -/
theorem coss {ε θ θ_ φ φ_ : ℝ} {P Q : Euc(3)}
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hε : 0 < ε) (hθ : |θ - θ_| ≤ ε) (hφ : |φ - φ_| ≤ ε) :
    let M := rotM θ φ
    let M_ := rotM θ_ φ_
    0 < (⟪M_ P, M_ (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)) /
      ((‖M_ P‖ + √2 * ε) * (‖M_ (P - Q)‖ + 2 * √2 * ε)) →
     (⟪M_ P, M_ (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε)) /
      ((‖M_ P‖ + √2 * ε) * (‖M_ (P - Q)‖ + 2 * √2 * ε))
     ≤
      ⟪M P, M (P - Q)⟫ / (‖M P‖ * ‖M (P - Q)‖) := by
  intro M M_ hp
  have hp₁ : 0 < (‖M_ P‖ + √2 * ε) * (‖M_ (P - Q)‖ + 2 * √2 * ε) := by positivity
  have hp₂ : 0 < ⟪M_ P, M_ (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε) :=
    (div_pos_iff_of_pos_right hp₁).mp hp
  -- Bound the numerator from below and the denominator factors from above.
  have hp₃ : ⟪M_ P, M_ (P - Q)⟫ - 2 * ε * ‖P - Q‖ * (√2 + ε) ≤ ⟪M P, M (P - Q)⟫ := by
    -- use lemma 25
    have h₁ := Local.abs_sub_inner_le M M_ P (P - Q)
    grw [hP] at h₁
    rw [one_mul] at h₁
    grw [(Bounding.norm_M_sub_lt hε hθ hφ).le, (Bounding.norm_M_sub_lt hε hθ hφ).le] at h₁
    rw [Bounding.rotM_norm_one, Bounding.rotM_norm_one] at h₁
    have h₂ : ‖P - Q‖ * (√2 * ε) * (1 + 1 + √2 * ε) = 2 * ε * ‖P - Q‖ * (√2 + ε) := by grind
    rw [h₂] at h₁
    exact sub_le_of_abs_sub_le_left h₁
  have hp₄ : 0 < ⟪M P, M (P - Q)⟫ := hp₂.trans_le hp₃
  apply div_le_div₀ hp₄.le hp₃
  · grw [←real_inner_le_norm]
    exact hp₄
  · have hnorm (v : Euc(3)) : ‖M v‖ ≤ ‖M_ v‖ + (√2 * ε) * ‖v‖ := by
      calc
        ‖M v‖ ≤ ‖M_ v‖ + ‖M v - M_ v‖ := norm_le_norm_add_norm_sub' _ _
        _ ≤ ‖M_ v‖ + (√2 * ε) * ‖v‖ := by
          rw [← sub_apply]
          grw [(M - M_).le_opNorm v, (Bounding.norm_M_sub_lt hε hθ hφ).le]
    refine mul_le_mul_of_nonneg ?_ ?_ (by positivity) (by positivity)
    · grw [hnorm P, hP]
      simp
    · grw [hnorm (P - Q), (norm_sub_le P Q).trans (add_le_add hP hQ)]
      ring_nf
      exact le_rfl

end Local
end
