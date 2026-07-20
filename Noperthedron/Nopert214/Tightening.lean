module

public import Noperthedron.Nopert214.Symmetry
public import Noperthedron.BalancedSupport.UniversalDomain
public import Noperthedron.BalancedSupport.ViewAntipode

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
    { θ₁ := -4 / 5, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := -4 }
    { θ₁ := 12 / 5, θ₂ := 8 / 5, φ₁ := 4, φ₂ := 4, α := 4 }
    (by rw [Pose.le_iff]; norm_num)

/-- The rational superset of the closest-representative condition.  Its
width is strictly smaller than one fivefold period, so no symmetry seam is
present inside the domain that the certificate tree must cover. -/
def InTightPoseRegion (q : Pose ℝ) : Prop :=
  q ∈ tightPoseInterval ∧ q.θ₁ - q.θ₂ ∈ Set.Icc (-(2 / 3)) (2 / 3)

/-- The exact angular wedge retained by the fivefold symmetry reduction.
Unlike the rational root box, these sharp bounds preserve the signs of the
first two outer viewing coordinates. -/
def InViewWedge (q : Pose ℝ) : Prop :=
  q.θ₂ ∈ Set.Icc 0 (2 * π / 5) ∧ q.φ₂ ∈ Set.Icc 0 π

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

/-- Reduce the outer azimuth modulo the exact fivefold symmetry, then choose
the inner representative closest to it.  Thus the only coincident-rotation
stratum in the reduced domain is `θ₁ = θ₂` (rather than an additional seam
at opposite ends of a fundamental interval). -/
theorem tighten_theta (p : Pose ℝ) :
    ∃ q : Pose ℝ,
      q.θ₂ ∈ Set.Ico 0 (2 * π / 5) ∧
      q.θ₁ - q.θ₂ ∈ Set.Ico (-(π / 5)) (π / 5) ∧
      q.φ₁ = p.φ₁ ∧ q.φ₂ = p.φ₂ ∧ q.α = p.α ∧
      p.inner '' exactPolyhedron.hull = q.inner '' exactPolyhedron.hull ∧
      p.outer '' exactPolyhedron.hull = q.outer '' exactPolyhedron.hull := by
  have hperiod : 0 < 2 * π / 5 := div_pos two_pi_pos (by norm_num)
  let θ₂ := Real.emod p.θ₂ (2 * π / 5)
  obtain ⟨k₂, hk₂⟩ :=
    Real.emod_exists_multiple p.θ₂ (2 * π / 5) hperiod
  let d := Real.emod (p.θ₁ - p.θ₂ + π / 5) (2 * π / 5) - π / 5
  let θ₁ := θ₂ + d
  obtain ⟨kd, hkd⟩ := Real.emod_exists_multiple
    (p.θ₁ - p.θ₂ + π / 5) (2 * π / 5) hperiod
  have hd : d ∈ Set.Ico (-(π / 5)) (π / 5) := by
    have h := Real.emod_in_interval
      (a := p.θ₁ - p.θ₂ + π / 5) hperiod
    dsimp [d]
    rcases h with ⟨hl, hu⟩
    constructor <;> linarith
  have hθ₁ : θ₁ = p.θ₁ + (k₂ + kd) * (2 * π / 5) := by
    dsimp [θ₁, θ₂, d]
    rw [hk₂, hkd]
    ring
  let q : Pose ℝ := {p with θ₁ := θ₁, θ₂ := θ₂}
  refine ⟨q, Real.emod_in_interval hperiod, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · simpa [q, θ₁] using hd
  · calc
      p.inner '' exactPolyhedron.hull =
          (p.rotR ∘ p.rotM₁) '' exactPolyhedron.hull := by
            rw [Pose.inner_eq_RM]
      _ = p.rotR '' (p.rotM₁ '' exactPolyhedron.hull) := by
            rw [Set.image_comp]
      _ = p.rotR '' (rotM p.θ₁ p.φ₁ '' exactPolyhedron.hull) := rfl
      _ = p.rotR '' (rotM (p.θ₁ + (k₂ + kd) * (2 * π / 5)) p.φ₁ ''
          exactPolyhedron.hull) := by
            have hs := rotM_add_fifth_iterated
              (θ := p.θ₁) (φ := p.φ₁) (k₂ + kd)
            push_cast at hs
            rw [hs]
      _ = p.rotR '' (rotM θ₁ p.φ₁ '' exactPolyhedron.hull) := by rw [hθ₁]
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
      InTightPoseRegion q ∧
      InViewWedge q ∧
      (RupertPose (q.matrixPoseWithOffset offset) exactPolyhedron.hull ↔
        RupertPose (p.rotateBy δ) exactPolyhedron.hull) := by
  obtain ⟨δ, p0, offset, hp0, _hθ0, hφ0, heq⟩ :=
    Noperthedron.BalancedSupport.exists_universal_translated_pose p
  obtain ⟨q, hθ₂, hdiff, hφ₁, hφ₂, hα, hinner, houter⟩ := tighten_theta p0
  have hq : q ∈ tightPoseInterval := by
    rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff]
    rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff] at hp0
    dsimp [tightPoseInterval, universalPoseInterval] at hp0 ⊢
    rcases hp0 with ⟨hlo, hhi⟩
    exact ⟨
      ⟨by nlinarith [hθ₂.1, hdiff.1, Real.pi_lt_four],
        hθ₂.1, hφ₁.symm ▸ hlo.2.2.1,
        hφ₂.symm ▸ hlo.2.2.2.1, hα.symm ▸ hlo.2.2.2.2⟩,
      ⟨by nlinarith [hθ₂.2, hdiff.2, Real.pi_lt_four],
        hθ₂.2.le.trans period_lt_root_upper.le,
        hφ₁.symm ▸ hhi.2.2.1, hφ₂.symm ▸ hhi.2.2.2.1,
        hα.symm ▸ hhi.2.2.2.2⟩⟩
  have hrelative : q.θ₁ - q.θ₂ ∈ Set.Icc (-(2 / 3)) (2 / 3) := by
    constructor <;> nlinarith [hdiff.1, hdiff.2, Real.pi_lt_d20]
  have hview : InViewWedge q := by
    constructor
    · exact ⟨hθ₂.1, hθ₂.2.le⟩
    · rw [hφ₂]
      exact hφ0
  refine ⟨δ, q, offset, ⟨hq, hrelative⟩, hview, ?_⟩
  rw [← heq]
  exact (translated_rupert_iff_of_images offset hinner houter).symm

/-- The oriented viewing normal may be chosen in the upper hemisphere.  The
extra choice is shape-independent: reversing the normal reflects both planar
shadows and hence preserves Rupert containment. -/
theorem exists_upper_tight_translated_pose (p : MatrixPose) :
    ∃ q : Pose ℝ, ∃ offset : ℝ²,
      InTightPoseRegion q ∧
      InViewWedge q ∧ q.φ₂ ≤ Real.pi / 2 ∧
      (RupertPose (q.matrixPoseWithOffset offset) exactPolyhedron.hull ↔
        RupertPose p exactPolyhedron.hull) := by
  let p' := p.upperViewRepresentative
  have hp' : 0 ≤ p'.outerRot.val 2 2 :=
    MatrixPose.upperViewRepresentative_outer_22_nonneg p
  obtain ⟨δ, p0, offset, hp0, _hθ0, hφ0, heq⟩ :=
    Noperthedron.BalancedSupport.exists_universal_translated_pose p'
  have hcos : 0 ≤ Real.cos p0.φ₂ := by
    have hout22 := congrArg
      (fun pose : MatrixPose ↦ pose.outerRot.val 2 2) heq
    simp only [Pose.matrixPoseWithOffset, Pose.matrixPoseOfPose,
      MatrixPose.rotateBy] at hout22
    simp [rotRM_mat, Matrix.mul_apply, Rz_mat, Ry_mat,
      Fin.sum_univ_three] at hout22
    linarith
  have hφ0Upper : p0.φ₂ ≤ Real.pi / 2 := by
    by_contra h
    have hneg := Real.cos_neg_of_pi_div_two_lt_of_lt
      (lt_of_not_ge h) (hφ0.2.trans_lt (by linarith [Real.pi_pos]))
    linarith
  obtain ⟨q, hθ₂, hdiff, hφ₁, hφ₂, hα, hinner, houter⟩ := tighten_theta p0
  have hq : q ∈ tightPoseInterval := by
    rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff]
    rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff] at hp0
    dsimp [tightPoseInterval, universalPoseInterval] at hp0 ⊢
    rcases hp0 with ⟨hlo, hhi⟩
    exact ⟨
      ⟨by nlinarith [hθ₂.1, hdiff.1, Real.pi_lt_four],
        hθ₂.1, hφ₁.symm ▸ hlo.2.2.1,
        hφ₂.symm ▸ hlo.2.2.2.1, hα.symm ▸ hlo.2.2.2.2⟩,
      ⟨by nlinarith [hθ₂.2, hdiff.2, Real.pi_lt_four],
        hθ₂.2.le.trans period_lt_root_upper.le,
        hφ₁.symm ▸ hhi.2.2.1, hφ₂.symm ▸ hhi.2.2.2.1,
        hα.symm ▸ hhi.2.2.2.2⟩⟩
  have hrelative : q.θ₁ - q.θ₂ ∈ Set.Icc (-(2 / 3)) (2 / 3) := by
    constructor <;> nlinarith [hdiff.1, hdiff.2, Real.pi_lt_d20]
  have hview : InViewWedge q := by
    constructor
    · exact ⟨hθ₂.1, hθ₂.2.le⟩
    · rw [hφ₂]
      exact hφ0
  have hrupert :
      RupertPose (q.matrixPoseWithOffset offset) exactPolyhedron.hull ↔
        RupertPose p exactPolyhedron.hull := by
    calc
      _ ↔ RupertPose (p0.matrixPoseWithOffset offset)
          exactPolyhedron.hull :=
        (translated_rupert_iff_of_images offset hinner houter).symm
      _ ↔ RupertPose (p'.rotateBy δ) exactPolyhedron.hull := by rw [heq]
      _ ↔ RupertPose p' exactPolyhedron.hull :=
        MatrixPose.RupertPose_rotateBy_iff p' δ _
      _ ↔ RupertPose p exactPolyhedron.hull :=
        MatrixPose.RupertPose_upperViewRepresentative_iff p _
  refine ⟨q, offset, ⟨hq, hrelative⟩, hview, ?_, hrupert⟩
  simpa [hφ₂] using hφ0Upper

/-- Excluding the reduced rational root box excludes every matrix pose. -/
theorem no_matrixPose_of_no_tight_translated_pose
    (h : ¬ ∃ q, InTightPoseRegion q ∧ ∃ offset : ℝ²,
      RupertPose (q.matrixPoseWithOffset offset) exactPolyhedron.hull) :
    ¬ ∃ p : MatrixPose, RupertPose p exactPolyhedron.hull := by
  rintro ⟨p, hp⟩
  obtain ⟨δ, q, offset, hq, -, heq⟩ := exists_tight_translated_pose p
  have hrot : RupertPose (p.rotateBy δ) exactPolyhedron.hull :=
    (MatrixPose.RupertPose_rotateBy_iff p δ exactPolyhedron.hull).mpr hp
  exact h ⟨q, hq, offset, heq.mpr hrot⟩

end Noperthedron.Nopert214

end
