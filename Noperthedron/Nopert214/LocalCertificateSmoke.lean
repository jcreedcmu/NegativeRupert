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
  r := 1 / 20000

theorem valid_kernel : box.Valid := by decide +kernel

theorem valid_native : box.Valid := by native_decide

theorem excludes_translated_pose :
    ¬ ∃ q ∈ box.realInterval, ∃ offset : ℝ²,
      RupertPose (q.matrixPoseWithOffset offset) exactGoodPoly.hull :=
  box.valid_imp_no_translated_rupert_in_interval valid_kernel

end Noperthedron.Nopert214.LocalCertificateSmoke

end
