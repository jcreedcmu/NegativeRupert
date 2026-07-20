module

public import Noperthedron.Nopert214.AtlasLocalCertificate
public import Noperthedron.Nopert214.LocalCertificateSmoke
public meta import Noperthedron.Nopert214.LocalCertificateSmoke
public meta import Noperthedron.Nopert214.AtlasLocalCertificate

@[expose] public section

/-! # Executable smoke test for an atlas-native symmetry-local row -/

namespace Noperthedron.Nopert214.AtlasLocalCertificateSmoke

open AtlasLocalCertificate

def interval : AtlasInterval ℚ :=
  AtlasInterval.mk
    { θ := -1 / 100000, φ := -1 / 100000
      x := -1 / 100000, y := -1 / 100000, z := -1 / 100000 }
    { θ := 1 / 100000, φ := 1 / 100000
      x := 1 / 100000, y := 1 / 100000, z := 1 / 100000 }
    (by rw [AtlasPose.le_iff]; norm_num)

def box : Box where
  interval := interval
  chart := 0
  symmetryIndex := 0
  certificate := LocalCertificateSmoke.box.certificate
  c := 1 / 100
  r := 1 / 19000

theorem valid_kernel : box.Valid := by decide +kernel

theorem valid_native : box.Valid := by native_decide

theorem excludes_translated_pose :
    ¬ ∃ p ∈ box.interval.toReal, ∃ offset : ℝ²,
      RupertPose (p.matrixPoseWithOffset box.chart offset)
        exactPolyhedron.hull :=
  box.valid_imp_no_translated_rupert_in_interval valid_kernel

end Noperthedron.Nopert214.AtlasLocalCertificateSmoke

end
