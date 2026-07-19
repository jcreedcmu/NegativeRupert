module

public import Noperthedron.SnubCube.CayleyLocalCertificate
public import Noperthedron.SnubCube.LocalCertificateSmoke
public meta import Noperthedron.SnubCube.CayleyLocalCertificate
public meta import Noperthedron.SnubCube.LocalCertificateSmoke

@[expose] public section


/-!
# Positive-radius Cayley local-certificate smoke test

This reuses the equality-stratum support geometry of the Euler smoke row,
but covers a genuine three-dimensional cube of relative Cayley rotations.
Both decision paths check the same executable proposition.
-/

namespace Noperthedron.SnubCube.CayleyLocalCertificateSmoke

def smokeInterval : CayleyInterval ℚ :=
  CayleyInterval.mk
    { θ := 29999 / 100000, φ := 109999 / 100000,
      x := -1 / 100, y := -1 / 100, z := -1 / 100 }
    { θ := 30001 / 100000, φ := 110001 / 100000,
      x := 1 / 100, y := 1 / 100, z := 1 / 100 }
    (by rw [CayleyPose.le_iff]; norm_num)

def smokeBox : CayleyLocalCertificate.Box where
  interval := smokeInterval
  certificate := LocalCertificate.smokeBox.certificate
  c := LocalCertificate.smokeBox.c
  r := LocalCertificate.smokeBox.r

theorem smoke_valid_kernel : smokeBox.Valid := by
  decide +kernel

theorem smoke_valid_native : smokeBox.Valid := by
  native_decide

theorem smoke_excludes_translated_pose :
    ¬ ∃ p ∈ smokeInterval.toReal, ∃ offset : ℝ²,
      RupertPose (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull :=
  smokeBox.valid_imp_no_translated_rupert_in_interval smoke_valid_kernel

/-- The equality-stratum checker does not pay the generic Euler mismatch
budget.  Consequently the same geometric witnesses cover a box whose two
outer-angle radii are 500 times larger. -/
def wideInterval : CayleyInterval ℚ :=
  CayleyInterval.mk
    { θ := 59 / 200, φ := 219 / 200,
      x := -1 / 200, y := -1 / 200, z := -1 / 200 }
    { θ := 61 / 200, φ := 221 / 200,
      x := 1 / 200, y := 1 / 200, z := 1 / 200 }
    (by rw [CayleyPose.le_iff]; norm_num)

def wideBox : CayleyLocalCertificate.Box where
  interval := wideInterval
  certificate := LocalCertificate.smokeBox.certificate
  -- Reducing `c` by the increase in outer angular radius leaves the checked
  -- axis-cover target exactly unchanged.
  c := 9907 / 1000000
  r := 0

theorem wide_valid_kernel : wideBox.Valid := by
  decide +kernel

theorem wide_valid_native : wideBox.Valid := by
  native_decide

theorem wide_excludes_translated_pose :
    ¬ ∃ p ∈ wideInterval.toReal, ∃ offset : ℝ²,
      RupertPose (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull :=
  wideBox.valid_imp_no_translated_rupert_in_interval wide_valid_kernel

end Noperthedron.SnubCube.CayleyLocalCertificateSmoke

end
