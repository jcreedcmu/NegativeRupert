module

public import Noperthedron.Nopert214.Symmetry
public import Noperthedron.BalancedSupport.UniversalDomain

@[expose] public section

/-!
# A symmetry-reduced pose domain for Nopert #214

Both azimuths can be reduced modulo `2π/5`.  We retain the shape-independent
bounds for the other three Euler parameters.  The resulting rational box is
the domain that the certificate tree must cover.
-/

namespace Noperthedron.Nopert214

open Real
open Noperthedron.BalancedSupport

noncomputable def tightPoseInterval : PoseInterval ℝ :=
  PoseInterval.mk
    { θ₁ := 0, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := -4 }
    { θ₁ := 8 / 5, θ₂ := 8 / 5, φ₁ := 4, φ₂ := 4, α := 4 }
    (by rw [Pose.le_iff]; norm_num)

private theorem translated_innerShadow_eq (p : Pose ℝ) (offset : ℝ²)
    (S : Set ℝ³) :
    innerShadow (p.matrixPoseWithOffset offset) S =
      (fun x : ℝ² => x + offset) '' (p.inner '' S) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨p.inner v, ⟨v, hv, rfl⟩, ?_⟩
    rw [Noperthedron.BalancedSupport.project_inner_apply,
      matrixPoseWithOffset_inner_rotation_project]
    rfl
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨v, hv, ?_⟩
    rw [Noperthedron.BalancedSupport.project_inner_apply,
      matrixPoseWithOffset_inner_rotation_project]
    rfl

private theorem translated_outerShadow_eq (p : Pose ℝ) (offset : ℝ²)
    (S : Set ℝ³) :
    outerShadow (p.matrixPoseWithOffset offset) S = p.outer '' S := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (matrixPoseWithOffset_outer_project p offset v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, matrixPoseWithOffset_outer_project p offset v⟩

private theorem translated_rupert_iff_of_images {p q : Pose ℝ}
    (offset : ℝ²)
    (hinner : p.inner '' exactPolyhedron.hull =
      q.inner '' exactPolyhedron.hull)
    (houter : p.outer '' exactPolyhedron.hull =
      q.outer '' exactPolyhedron.hull) :
    RupertPose (p.matrixPoseWithOffset offset) exactPolyhedron.hull ↔
      RupertPose (q.matrixPoseWithOffset offset) exactPolyhedron.hull := by
  unfold RupertPose
  rw [translated_innerShadow_eq, translated_innerShadow_eq,
    translated_outerShadow_eq, translated_outerShadow_eq,
    hinner, houter]

/-- Reduce both azimuths modulo the exact fivefold symmetry. -/
theorem tighten_theta (p : Pose ℝ) :
    ∃ q : Pose ℝ,
      q.θ₁ ∈ Set.Ico 0 (2 * π / 5) ∧
      q.θ₂ ∈ Set.Ico 0 (2 * π / 5) ∧
      q.φ₁ = p.φ₁ ∧ q.φ₂ = p.φ₂ ∧ q.α = p.α ∧
      p.inner '' exactPolyhedron.hull = q.inner '' exactPolyhedron.hull ∧
      p.outer '' exactPolyhedron.hull = q.outer '' exactPolyhedron.hull := by
  have hperiod : 0 < 2 * π / 5 := div_pos two_pi_pos (by norm_num)
  let θ₁ := Real.emod p.θ₁ (2 * π / 5)
  let θ₂ := Real.emod p.θ₂ (2 * π / 5)
  obtain ⟨k₁, hk₁⟩ :=
    Real.emod_exists_multiple p.θ₁ (2 * π / 5) hperiod
  obtain ⟨k₂, hk₂⟩ :=
    Real.emod_exists_multiple p.θ₂ (2 * π / 5) hperiod
  let q : Pose ℝ := {p with θ₁ := θ₁, θ₂ := θ₂}
  refine ⟨q, Real.emod_in_interval hperiod,
    Real.emod_in_interval hperiod, rfl, rfl, rfl, ?_, ?_⟩
  · calc
      p.inner '' exactPolyhedron.hull =
          (p.rotR ∘ p.rotM₁) '' exactPolyhedron.hull := by
            rw [Pose.inner_eq_RM]
      _ = p.rotR '' (p.rotM₁ '' exactPolyhedron.hull) := by
            rw [Set.image_comp]
      _ = p.rotR '' (rotM p.θ₁ p.φ₁ '' exactPolyhedron.hull) := rfl
      _ = p.rotR '' (rotM (p.θ₁ + k₁ * (2 * π / 5)) p.φ₁ ''
          exactPolyhedron.hull) := by
            rw [rotM_add_fifth_iterated k₁]
      _ = p.rotR '' (rotM θ₁ p.φ₁ '' exactPolyhedron.hull) := by rw [← hk₁]
      _ = (q.rotR ∘ q.rotM₁) '' exactPolyhedron.hull := by
            rw [Set.image_comp]
            rfl
      _ = q.inner '' exactPolyhedron.hull := by rw [Pose.inner_eq_RM]
  · calc
      p.outer '' exactPolyhedron.hull =
          p.rotM₂ '' exactPolyhedron.hull := by rw [Pose.outer_eq_M]
      _ = rotM p.θ₂ p.φ₂ '' exactPolyhedron.hull := rfl
      _ = rotM (p.θ₂ + k₂ * (2 * π / 5)) p.φ₂ ''
          exactPolyhedron.hull := by rw [rotM_add_fifth_iterated k₂]
      _ = rotM θ₂ p.φ₂ '' exactPolyhedron.hull := by rw [← hk₂]
      _ = q.rotM₂ '' exactPolyhedron.hull := rfl
      _ = q.outer '' exactPolyhedron.hull := by rw [Pose.outer_eq_M]

private theorem period_lt_root_upper : 2 * π / 5 < (8 / 5 : ℝ) := by
  nlinarith [Real.pi_lt_four]

/-- Every full matrix pose has an equivalent translated representative in
the symmetry-reduced rational root box. -/
theorem exists_tight_translated_pose (p : MatrixPose) :
    ∃ δ : ℝ, ∃ q : Pose ℝ, ∃ offset : ℝ²,
      q ∈ tightPoseInterval ∧
      (RupertPose (q.matrixPoseWithOffset offset) exactPolyhedron.hull ↔
        RupertPose (p.rotateBy δ) exactPolyhedron.hull) := by
  obtain ⟨δ, p0, offset, hp0, heq⟩ :=
    Noperthedron.BalancedSupport.exists_universal_translated_pose p
  obtain ⟨q, hθ₁, hθ₂, hφ₁, hφ₂, hα, hinner, houter⟩ := tighten_theta p0
  have hq : q ∈ tightPoseInterval := by
    rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff]
    rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff] at hp0
    dsimp [tightPoseInterval, universalPoseInterval] at hp0 ⊢
    rcases hp0 with ⟨hlo, hhi⟩
    exact ⟨
      ⟨hθ₁.1, hθ₂.1, hφ₁.symm ▸ hlo.2.2.1,
        hφ₂.symm ▸ hlo.2.2.2.1, hα.symm ▸ hlo.2.2.2.2⟩,
      ⟨hθ₁.2.le.trans period_lt_root_upper.le,
        hθ₂.2.le.trans period_lt_root_upper.le,
        hφ₁.symm ▸ hhi.2.2.1, hφ₂.symm ▸ hhi.2.2.2.1,
        hα.symm ▸ hhi.2.2.2.2⟩⟩
  refine ⟨δ, q, offset, hq, ?_⟩
  rw [← heq]
  exact (translated_rupert_iff_of_images offset hinner houter).symm

/-- Excluding the reduced rational root box excludes every matrix pose. -/
theorem no_matrixPose_of_no_tight_translated_pose
    (h : ¬ ∃ q ∈ tightPoseInterval, ∃ offset : ℝ²,
      RupertPose (q.matrixPoseWithOffset offset) exactPolyhedron.hull) :
    ¬ ∃ p : MatrixPose, RupertPose p exactPolyhedron.hull := by
  rintro ⟨p, hp⟩
  obtain ⟨δ, q, offset, hq, heq⟩ := exists_tight_translated_pose p
  have hrot : RupertPose (p.rotateBy δ) exactPolyhedron.hull :=
    (MatrixPose.RupertPose_rotateBy_iff p δ exactPolyhedron.hull).mpr hp
  exact h ⟨q, hq, offset, heq.mpr hrot⟩

end Noperthedron.Nopert214

end
