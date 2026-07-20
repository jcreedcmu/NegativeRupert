module

public import Noperthedron.Nopert214.LocalCertificate
public meta import Noperthedron.Nopert214.LocalCertificate

@[expose] public section


/-!
# Positive-radius local-certificate smoke test for Nopert #214

The four exact balanced triples cover a genuine five-dimensional Euler box
around the identity stratum.  Both decision paths evaluate the same complete
local-row predicate.
-/

namespace Noperthedron.Nopert214.LocalCertificateSmoke

open LocalCertificate

def center : Pose ℚ := {
  θ₁ := 0, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := 0
}

def interval : PoseInterval ℚ :=
  PoseInterval.mk
    { θ₁ := -1 / 100000, θ₂ := -1 / 100000
      φ₁ := -1 / 100000, φ₂ := -1 / 100000, α := -1 / 100000 }
    { θ₁ := 1 / 100000, θ₂ := 1 / 100000
      φ₁ := 1 / 100000, φ₂ := 1 / 100000, α := 1 / 100000 }
    (by rw [Pose.le_iff]; norm_num)

def box : Box where
  interval := interval
  center := center
  symmetryIndex := 0
  certificate := ![
    ⟨![
      ⟨14, ![-1, 0]⟩,
      ⟨1, ![4671 / 15329, -14600 / 15329]⟩,
      ⟨9, ![301 / 949, 900 / 949]⟩]⟩,
    ⟨![
      ⟨17, ![-561 / 689, -400 / 689]⟩,
      ⟨2, ![8911 / 11089, -6600 / 11089]⟩,
      ⟨10, ![-8769 / 28769, 27400 / 28769]⟩]⟩,
    ⟨![
      ⟨18, ![-2261 / 7261, -6900 / 7261]⟩,
      ⟨5, ![1, 0]⟩,
      ⟨13, ![-8911 / 11089, 6600 / 11089]⟩]⟩,
    ⟨![
      ⟨1, ![4671 / 15329, -14600 / 15329]⟩,
      ⟨6, ![561 / 689, 400 / 689]⟩,
      ⟨13, ![-8911 / 11089, 6600 / 11089]⟩]⟩
  ]
  c := 1 / 100
  r := 1 / 19000

theorem valid_kernel : box.Valid := by decide +kernel

theorem valid_native : box.Valid := by native_decide

theorem excludes_translated_pose :
    ¬ ∃ q ∈ box.realInterval, ∃ offset : ℝ²,
      RupertPose (q.matrixPoseWithOffset offset) exactGoodPoly.hull :=
  box.valid_imp_no_translated_rupert_in_interval valid_kernel

/-! A nontrivial-symmetry row at the Euler-pole box that defeated the old
identity-coordinate local checker. -/

def poleCenter : Pose ℚ := {
  θ₁ := -287 / 1280, φ₁ := 3 / 2048
  θ₂ := 1 / 1280, φ₂ := 5 / 2048, α := -4093 / 1024
}

def poleInterval : PoseInterval ℚ :=
  PoseInterval.mk
    { θ₁ := -9 / 40, φ₁ := 1 / 1024
      θ₂ := 0, φ₂ := 1 / 512, α := -2047 / 512 }
    { θ₁ := -143 / 640, φ₁ := 1 / 512
      θ₂ := 1 / 640, φ₂ := 3 / 1024, α := -1023 / 256 }
    (by rw [Pose.le_iff]; norm_num)

def poleBox : Box where
  interval := poleInterval
  center := poleCenter
  symmetryIndex := 2
  certificate := ![
    ⟨![
      ⟨6, ![-998631 / 1001369, -74000 / 1001369]⟩,
      ⟨17, ![62211 / 62789, -8500 / 62789]⟩,
      ⟨2, ![-1223081 / 3223081, 2982000 / 3223081]⟩]⟩,
    ⟨![
      ⟨9, ![-15 / 17, -8 / 17]⟩,
      ⟨13, ![299431 / 1700569, -1674000 / 1700569]⟩,
      ⟨18, ![230119 / 269881, 141000 / 269881]⟩]⟩,
    ⟨![
      ⟨10, ![-317009 / 817009, -753000 / 817009]⟩,
      ⟨17, ![62211 / 62789, -8500 / 62789]⟩,
      ⟨5, ![-209599 / 290401, 201000 / 290401]⟩]⟩,
    ⟨![
      ⟨14, ![229551 / 270449, -143000 / 270449]⟩,
      ⟨17, ![62211 / 62789, -8500 / 62789]⟩,
      ⟨5, ![-37399 / 42601, 20400 / 42601]⟩]⟩
  ]
  c := 13233 / 500000
  r := 4712886957 / 500000000000

theorem pole_valid_kernel : poleBox.Valid := by decide +kernel

theorem pole_valid_native : poleBox.Valid := by native_decide

theorem pole_excludes_translated_pose :
    ¬ ∃ q ∈ poleBox.realInterval, ∃ offset : ℝ²,
      RupertPose (q.matrixPoseWithOffset offset) exactGoodPoly.hull :=
  poleBox.valid_imp_no_translated_rupert_in_interval pole_valid_kernel

end Noperthedron.Nopert214.LocalCertificateSmoke

end
