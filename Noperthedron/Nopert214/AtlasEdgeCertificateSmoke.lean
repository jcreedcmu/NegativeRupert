module

public import Noperthedron.Nopert214.AtlasEdgeCertificate
public meta import Noperthedron.Nopert214.AtlasEdgeCertificate

@[expose] public section

/-! # Dual-evaluator smoke test for a charted edge-cycle row -/

namespace Noperthedron.Nopert214.AtlasEdgeCertificateSmoke

open AtlasEdgeCertificate

def interval : AtlasInterval ℚ :=
  AtlasInterval.mk
    { θ := 79 / 100, φ := 199 / 100,
      x := 49 / 50, y := 49 / 50, z := 49 / 50 }
    { θ := 81 / 100, φ := 201 / 100,
      x := 51 / 50, y := 51 / 50, z := 51 / 50 }
    (by rw [AtlasPose.le_iff]; norm_num)

def box : Box where
  interval := interval
  chart := 0
  edgePred := 8
  outerIndex := fun i => ![17, 18, 19, 15, 11, 6, 5, 4, 0] i
  innerIndex := fun i => ![9, 9, 13, 14, 19, 3, 2, 5, 5] i
  nonzeroWitness := fun i => ![6, 5, 4, 0, 17, 18, 19, 15, 11] i

theorem valid_kernel : box.Valid := by
  decide +kernel

theorem valid_native : box.Valid := by
  native_decide

end Noperthedron.Nopert214.AtlasEdgeCertificateSmoke

end
