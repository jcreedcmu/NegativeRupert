module

public import Noperthedron.Nopert214.Certificate
public meta import Noperthedron.Nopert214.Certificate

@[expose] public section


/-!
# Kernel/native smoke test for a Nopert #214 balanced box

The certificate was discovered at the rational pose
`(3/10, 1, -7/10, 7/5, 4/5)`.  Rational unit-circle directions and
determinant weights make unit length and balance exact; the aggregate global
inequality has ample slack.
-/

namespace Noperthedron.Nopert214.CertificateSmoke

open Certificate

def center : Pose ℚ := {
  θ₁ := 3 / 10
  φ₁ := 1
  θ₂ := -7 / 10
  φ₂ := 7 / 5
  α := 4 / 5
}

def pointInterval : PoseInterval ℚ :=
  PoseInterval.mk center center (by rfl)

def box : Box where
  interval := pointInterval
  contact := ![
    { innerIndex := 13
      outerIndex := 14
      direction := ![-38479 / 41521, -15600 / 41521]
      weight := 95185769000 / 902169981329 },
    { innerIndex := 19
      outerIndex := 19
      direction := ![95599 / 1904401, -1902000 / 1904401]
      weight := 17790739400 / 19669701809 },
    { innerIndex := 5
      outerIndex := 4
      direction := ![26271 / 473729, 473000 / 473729]
      weight := 74678402400 / 79072633921 }
  ]

theorem valid_kernel : box.Valid := by decide +kernel

theorem valid_native : box.Valid := by native_decide

end Noperthedron.Nopert214.CertificateSmoke

end
