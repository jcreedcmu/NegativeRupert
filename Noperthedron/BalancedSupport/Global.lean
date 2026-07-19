module

public import Noperthedron.BalancedSupport.TranslatedPose
public import Noperthedron.Global

@[expose] public section


/-!
# Balanced global box certificates

This combines the existing second-order Taylor bounds contactwise.  The
individual contacts need not prove the old one-direction global theorem:
only their nonnegative weighted sum must have nonnegative displacement.
Because the weighted normals balance, the conclusion holds for every planar
translation of the inner shadow.
-/

namespace Noperthedron.BalancedSupport

open scoped RealInnerProductSpace

open GlobalTheorem

/-- A weighted family of global contacts whose Taylor lower bounds dominate
the corresponding outer-support upper bounds throughout one pose box. -/
structure BalancedGlobalPrecondition
    {ι κ : Type} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (poly : GoodPoly ι) (p : Pose ℝ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ) where
  contact : κ → GlobalContact poly p εα εθ₁ εφ₁ εθ₂ εφ₂
  outerIndex : κ → ι
  weight : κ → ℝ
  weight_nonneg : ∀ k, 0 ≤ weight k
  weight_pos : ∃ k, 0 < weight k
  balance : ∑ k, weight k • (contact k).w = 0
  dominates :
    ∑ k, weight k * maxH p poly εθ₂ εφ₂ (contact k).w ≤
      ∑ k, weight k * G p εα εθ₁ εφ₁
        (poly.vertices.v (contact k).Si) (contact k).w

private theorem contact_direction_ne_zero
    {ι κ : Type} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    {poly : GoodPoly ι} {p : Pose ℝ} {εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ}
    (pc : BalancedGlobalPrecondition (poly := poly) (p := p)
      (κ := κ) εα εθ₁ εφ₁ εθ₂ εφ₂) (k : κ) :
    (pc.contact k).w ≠ 0 := by
  intro h
  have := (pc.contact k).w_unit
  rw [h, norm_zero] at this
  norm_num at this

/-- Soundness of a balanced global certificate for one Euler-coordinate box,
uniformly over the inner-shadow translation. -/
theorem balanced_global_theorem
    {ι κ : Type} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (pbar : Pose ℝ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ)
    (hεα : 0 ≤ εα) (hεθ₁ : 0 ≤ εθ₁) (hεφ₁ : 0 ≤ εφ₁)
    (hεθ₂ : 0 ≤ εθ₂) (hεφ₂ : 0 ≤ εφ₂)
    (poly : GoodPoly ι)
    (pc : BalancedGlobalPrecondition (poly := poly) (p := pbar)
      (κ := κ) εα εθ₁ εφ₁ εθ₂ εφ₂) :
    ∀ q, Pose.near pbar εα εθ₁ εφ₁ εθ₂ εφ₂ q →
      ∀ offset : ℝ², ¬ RupertPose (q.matrixPoseWithOffset offset) poly.hull := by
  intro q hnear offset
  let defect : κ → ℝ := fun k =>
    maxH pbar poly εθ₂ εφ₂ (pc.contact k).w -
      ⟪(pc.contact k).w, q.outer (poly.vertices.v (pc.outerIndex k))⟫
  apply not_translatedPose_of_balanced_support_with_defect
    poly.vertices q offset
    (fun k => (pc.contact k).Si) pc.outerIndex pc.weight
    (fun k => (pc.contact k).w) defect
    (contact_direction_ne_zero pc) pc.weight_nonneg pc.weight_pos pc.balance
  · intro k j
    have hjmax :
        ⟪(pc.contact k).w, q.outer (poly.vertices.v j)⟫ ≤
          maxOuter q poly (pc.contact k).w := by
      unfold maxOuter imgOuter
      apply Finset.le_max'
      simp only [Finset.mem_image]
      exact ⟨poly.vertices.v j, ⟨j, Finset.mem_univ j, rfl⟩, rfl⟩
    have hmaxH : maxOuter q poly (pc.contact k).w ≤
        maxH pbar poly εθ₂ εφ₂ (pc.contact k).w :=
      global_theorem_inequality_iv pbar q εα εθ₁ εφ₁ εθ₂ εφ₂
        hεθ₂ hεφ₂ hnear poly (pc.contact k)
    dsimp [defect]
    linarith
  · have hinner (k : κ) :
        G pbar εα εθ₁ εφ₁
            (poly.vertices.v (pc.contact k).Si) (pc.contact k).w ≤
          ⟪(pc.contact k).w,
            q.inner (poly.vertices.v (pc.contact k).Si)⟫ := by
      simpa [GlobalContact.S, GlobalContact.Sval] using
        global_theorem_inequality_ii pbar q εα εθ₁ εφ₁ εθ₂ εφ₂
          hεα hεθ₁ hεφ₁ hnear poly (pc.contact k)
    have hweighted :
        ∑ k, pc.weight k *
            G pbar εα εθ₁ εφ₁
              (poly.vertices.v (pc.contact k).Si) (pc.contact k).w ≤
          ∑ k, pc.weight k *
            ⟪(pc.contact k).w,
              q.inner (poly.vertices.v (pc.contact k).Si)⟫ := by
      exact Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left (hinner k) (pc.weight_nonneg k)
    dsimp [defect]
    simp_rw [inner_sub_right, mul_sub, Finset.sum_sub_distrib]
    linarith [pc.dominates, hweighted]

end Noperthedron.BalancedSupport

end
