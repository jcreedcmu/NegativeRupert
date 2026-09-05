module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Archimedean.Real.Hom

public import Noperthedron.EuclideanSpaceNotation

@[expose] public section


namespace Local

open scoped RealInnerProductSpace Real

/-- The positive cone of a finite collection of vectors -/
def Spanp {n : ℕ} (v : Fin n → Euc(n)) : Set Euc(n) :=
  {w | ∃ c : Fin n → ℝ, (∀ i, 0 < c i) ∧ w = ∑ i, c i • v i }

/-- [SY25] Lemma 23, with the unnecessary assumption `Y ∈ Spanp V` removed.
Only `Z` needs a positive expansion: strict inequalities at every generator would
force `⟪Z, Z⟫ < ⟪Z, Y⟫`, contradicting Cauchy–Schwarz and equality of norms. -/
theorem langles {Y Z : Euc(3)} {V : Fin 3 → Euc(3)} (hYZ : ‖Y‖ = ‖Z‖)
    (hZ : Z ∈ Spanp V) : ∃ i, ⟪V i, Y⟫ ≤ ⟪V i, Z⟫ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hc, hsum⟩ := hZ
  have expand (W : Euc(3)) : ⟪Z, W⟫ = ∑ i, c i * ⟪V i, W⟫ := by
    rw [hsum, sum_inner]
    simp [real_inner_smul_left]
  have hlt_self : ⟪Z, Z⟫ < ⟪Z, Y⟫ := by
    rw [expand Z, expand Y]
    exact Finset.sum_lt_sum_of_nonempty (by simp) fun i _ =>
      mul_lt_mul_of_pos_left (hlt i) (hc i)
  have hle : ⟪Z, Y⟫ ≤ ⟪Z, Z⟫ := by
    calc ⟪Z, Y⟫ ≤ ‖Z‖ * ‖Y‖ := real_inner_le_norm _ _
      _ = ⟪Z, Z⟫ := by rw [hYZ, real_inner_self_eq_norm_mul_norm]
  exact (not_lt_of_ge hle) hlt_self

end Local
end
