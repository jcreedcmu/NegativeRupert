module

public import Noperthedron.Basic

@[expose] public section


/-!
# Balanced supporting directions

This file contains the translation-cancelling core of the balanced-support
method.  It is deliberately stated for arbitrary finite planar point sets;
the rotations and the polyhedron enter only in later bridge lemmas.
-/

namespace Noperthedron.BalancedSupport

open scoped RealInnerProductSpace

/-- An interior point of a convex hull satisfies every nontrivial supporting
inequality strictly. -/
theorem inner_lt_of_mem_interior_convexHull {V : Set ℝ²} {u x : ℝ²} {c : ℝ}
    (hu : u ≠ 0) (hV : ∀ y ∈ V, ⟪u, y⟫ ≤ c)
    (hx : x ∈ interior (convexHull ℝ V)) :
    ⟪u, x⟫ < c := by
  have h_ne : innerSL ℝ u ≠ 0 := fun h0 => hu <| by
    simpa [inner_self_eq_zero] using congrFun (congrArg DFunLike.coe h0) u
  have h_mem : x ∈ interior (innerSL ℝ u ⁻¹' Set.Iic c) :=
    interior_mono
      (convexHull_min hV (convex_halfSpace_le (innerSL ℝ u).toLinearMap.isLinear c)) hx
  rw [← ((innerSL ℝ u).isOpenMap_of_ne_zero h_ne).preimage_interior_eq_interior_preimage
      (innerSL ℝ u).continuous, interior_Iic] at h_mem
  exact h_mem

/-- A balanced weighted family of directions does not see a common
translation of all the points. -/
theorem sum_weighted_inner_add_eq {κ : Type} [Fintype κ]
    (μ : κ → ℝ) (u x : κ → ℝ²) (t : ℝ²)
    (hbalance : ∑ i, μ i • u i = 0) :
    ∑ i, μ i * ⟪u i, x i + t⟫ = ∑ i, μ i * ⟪u i, x i⟫ := by
  simp_rw [inner_add_right, mul_add, Finset.sum_add_distrib]
  suffices htranslation : ∑ i, μ i * ⟪u i, t⟫ = 0 by rw [htranslation, add_zero]
  calc
    ∑ i, μ i * ⟪u i, t⟫ = ⟪∑ i, μ i • u i, t⟫ := by
      simp [sum_inner, real_inner_smul_left]
    _ = 0 := by rw [hbalance]; simp

/-- The algebraic heart of the balanced-support argument.  If all contact
inequalities are strict and their positive weighted normals balance, then the
weighted inner-to-outer displacement must be negative. -/
theorem weighted_displacement_neg {κ : Type} [Fintype κ] [Nonempty κ]
    (μ : κ → ℝ) (u innerPoint outerPoint : κ → ℝ²) (t : ℝ²)
    (hμ : ∀ i, 0 ≤ μ i) (hμpos : ∃ i, 0 < μ i)
    (hbalance : ∑ i, μ i • u i = 0)
    (hstrict : ∀ i, ⟪u i, innerPoint i + t⟫ < ⟪u i, outerPoint i⟫) :
    ∑ i, μ i * ⟪u i, innerPoint i - outerPoint i⟫ < 0 := by
  have hsum :
      ∑ i, μ i * ⟪u i, innerPoint i + t⟫ <
        ∑ i, μ i * ⟪u i, outerPoint i⟫ := by
    refine Finset.sum_lt_sum ?_ ?_
    · intro i _
      exact mul_le_mul_of_nonneg_left (hstrict i).le (hμ i)
    · obtain ⟨i, hi⟩ := hμpos
      exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (hstrict i) hi⟩
  rw [sum_weighted_inner_add_eq μ u innerPoint t hbalance] at hsum
  simp_rw [inner_sub_right, mul_sub, Finset.sum_sub_distrib]
  exact sub_neg.mpr hsum

/-- A finite balanced-support certificate rules out strict containment of the
translated distinguished inner points in the outer convex hull. -/
theorem not_strictly_contained_of_balanced_support
    {κ : Type} [Fintype κ] [Nonempty κ]
    (V : Set ℝ²) (μ : κ → ℝ) (u innerPoint outerPoint : κ → ℝ²) (t : ℝ²)
    (hu : ∀ i, u i ≠ 0)
    (hμ : ∀ i, 0 ≤ μ i) (hμpos : ∃ i, 0 < μ i)
    (hbalance : ∑ i, μ i • u i = 0)
    (hsupport : ∀ i y, y ∈ V → ⟪u i, y⟫ ≤ ⟪u i, outerPoint i⟫)
    (hinner : ∀ i, innerPoint i + t ∈ interior (convexHull ℝ V))
    (hdisplacement : 0 ≤ ∑ i, μ i * ⟪u i, innerPoint i - outerPoint i⟫) :
    False := by
  have hstrict (i : κ) :
      ⟪u i, innerPoint i + t⟫ < ⟪u i, outerPoint i⟫ :=
    inner_lt_of_mem_interior_convexHull (hu i) (hsupport i) (hinner i)
  exact (not_lt_of_ge hdisplacement)
    (weighted_displacement_neg μ u innerPoint outerPoint t hμ hμpos hbalance hstrict)

end Noperthedron.BalancedSupport

end
