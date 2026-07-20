module

public import Noperthedron.BalancedSupport.TranslatedPose
public import Noperthedron.SnubCube.Tightening

@[expose] public section


/-!
# A shape-independent bounded Euler domain

No polyhedron symmetry is needed to make the five Euler parameters compact.
Parameterize both rotations in the standard bounded Euler domain and use a
common screen rotation to set the outer in-plane angle to zero.  The planar
translation rotates with the screen.  This supplies a rational root box for
arbitrary polyhedra, including decimal meshes with no exact symmetry.
-/

namespace Noperthedron.BalancedSupport

open Real
open scoped Matrix

def universalPoseInterval : PoseInterval ℝ :=
  PoseInterval.mk
    { θ₁ := -4, θ₂ := -4, φ₁ := 0, φ₂ := 0, α := -4 }
    { θ₁ := 4, θ₂ := 4, φ₁ := 4, φ₂ := 4, α := 4 }
    (by rw [Pose.le_iff]; norm_num)

private theorem Rz_mul_rotRM_mat (δ θ φ α : ℝ) :
    Rz_mat δ * rotRM_mat θ φ α = rotRM_mat θ φ (δ + α) := by
  simp only [rotRM_mat, ← Matrix.mul_assoc,
    Bounding.Rz_mat_mul_Rz_mat]
  congr 3
  ring

/-- Every full matrix pose has a translated Euler representative in the
shape-independent rational root box. -/
theorem exists_universal_translated_pose (p : MatrixPose) :
    ∃ δ : ℝ, ∃ q : Pose ℝ, ∃ offset : ℝ²,
      q ∈ universalPoseInterval ∧
      q.θ₂ ∈ Set.Ioc (-π) π ∧ q.φ₂ ∈ Set.Icc 0 π ∧
      q.matrixPoseWithOffset offset = p.rotateBy δ := by
  obtain ⟨θi, φi, αi, hθi, hφi, _hαi, hinner⟩ :=
    Noperthedron.SnubCube.SO3_to_bounded_rotRM_params
      p.innerRot.val p.innerRot.property
  obtain ⟨θo, φo, αo, hθo, hφo, _hαo, houter⟩ :=
    Noperthedron.SnubCube.SO3_to_bounded_rotRM_params
      p.outerRot.val p.outerRot.property
  let δ := -αo
  obtain ⟨α, hα, hRzα⟩ := Bounding.Rz_mod_two_pi (δ + αi)
  let q : Pose ℝ := {
    θ₁ := θi, θ₂ := θo, φ₁ := φi, φ₂ := φo, α := α
  }
  let offset := rotR δ p.innerOffset
  have hq : q ∈ universalPoseInterval := by
    rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff]
    dsimp [q, universalPoseInterval]
    have hpi4 := Real.pi_le_four
    exact ⟨
      ⟨by linarith [hθi.1], by linarith [hθo.1], hφi.1, hφo.1,
        by linarith [hα.1]⟩,
      ⟨by linarith [hθi.2], by linarith [hθo.2], hφi.2.trans hpi4,
        hφo.2.trans hpi4, by linarith [hα.2]⟩⟩
  refine ⟨δ, q, offset, hq, by simpa [q] using hθo,
    by simpa [q] using hφo, ?_⟩
  have hin : Rz_mat δ * p.innerRot.val = rotRM_mat θi φi α := by
    rw [hinner, Rz_mul_rotRM_mat]
    unfold rotRM_mat
    rw [hRzα]
  have hout : Rz_mat δ * p.outerRot.val = rotRM_mat θo φo 0 := by
    rw [houter, Rz_mul_rotRM_mat]
    congr 1
    dsimp [δ]
    ring
  simp only [Pose.matrixPoseWithOffset, Pose.matrixPoseOfPose,
    MatrixPose.rotateBy]
  congr 1
  · apply Subtype.ext
    exact hin.symm
  · apply Subtype.ext
    exact hout.symm

/-- Excluding every translated Euler pose in the universal root excludes
every full matrix pose, for any set in three-space. -/
theorem no_matrixPose_of_no_universal_translated_pose {S : Set ℝ³}
    (h : ¬ ∃ q ∈ universalPoseInterval, ∃ offset : ℝ²,
      RupertPose (q.matrixPoseWithOffset offset) S) :
    ¬ ∃ p : MatrixPose, RupertPose p S := by
  rintro ⟨p, hp⟩
  obtain ⟨δ, q, offset, hq, -, -, heq⟩ :=
    exists_universal_translated_pose p
  have hrot : RupertPose (p.rotateBy δ) S :=
    (MatrixPose.RupertPose_rotateBy_iff p δ S).mpr hp
  exact h ⟨q, hq, offset, heq.symm ▸ hrot⟩

end Noperthedron.BalancedSupport

end
