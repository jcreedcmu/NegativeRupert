module

public import Noperthedron.BalancedSupport.Basic

@[expose] public section


/-!
# Finite-rotation remainder bounds

The geometric Rodrigues decomposition is supplied by a later specialization.
This file records the ordered-algebra step once: a favorable first variation
that dominates a rigorously bounded remainder makes the balanced displacement
nonnegative.
-/

namespace Noperthedron.BalancedSupport

/-- Sum a pointwise lower bound on remainder terms with nonnegative weights. -/
theorem weighted_remainder_lower_bound {κ : Type} [Fintype κ]
    (μ remainder bound : κ → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hbound : ∀ i, -bound i ≤ remainder i) :
    -(∑ i, μ i * bound i) ≤ ∑ i, μ i * remainder i := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum ?_
  intro i _
  calc
    -(μ i * bound i) = μ i * (-bound i) := by ring
    _ ≤ μ i * remainder i := mul_le_mul_of_nonneg_left (hbound i) (hμ i)

/-- Abstract finite-rotation estimate.  Here `sinCoeff` and `bendCoeff`
stand for `sin s` and `1 - cos s`; stating the ordered step abstractly also
makes it useful for interval enclosures of those quantities. -/
theorem weighted_displacement_nonneg_of_first_remainder
    {κ : Type} [Fintype κ]
    (μ displacement first remainder bound : κ → ℝ)
    (sinCoeff bendCoeff : ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hbend : 0 ≤ bendCoeff)
    (hdecomp : ∀ i,
      displacement i = sinCoeff * first i + bendCoeff * remainder i)
    (hremainder : ∀ i, -bound i ≤ remainder i)
    (hdominates : bendCoeff * (∑ i, μ i * bound i) ≤
      sinCoeff * (∑ i, μ i * first i)) :
    0 ≤ ∑ i, μ i * displacement i := by
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
          ∑ i, (sinCoeff * (μ i * first i) + bendCoeff * (μ i * remainder i)) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hdecomp]
        ring
      _ = sinCoeff * (∑ i, μ i * first i) +
          bendCoeff * (∑ i, μ i * remainder i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [heq]
  linarith

end Noperthedron.BalancedSupport

end
