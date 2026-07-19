module

public import Noperthedron.SnubCube.FundamentalPrune
public meta import Noperthedron.SnubCube.FundamentalPrune

@[expose] public section


/-!
# Executable smoke test for fundamental-domain pruning

This genuine positive-radius box is rejected from the exact max-trace
fundamental domain by symmetry 14.  The same rational proposition is checked
through both the kernel evaluator and `native_decide`.
-/

namespace Noperthedron.SnubCube.FundamentalPrune

def smokeBox : Box where
  interval := PoseInterval.mk
    { θ₁ := 99 / 100, θ₂ := -1 / 100,
      φ₁ := 99 / 100, φ₂ := -1 / 100, α := -1 / 100 }
    { θ₁ := 101 / 100, θ₂ := 1 / 100,
      φ₁ := 101 / 100, φ₂ := 1 / 100, α := 1 / 100 }
    (by rw [Pose.le_iff]; norm_num)
  symmetryIndex := VertexIndex.ofFin24 14

theorem smokeBox_valid_kernel : smokeBox.Valid := by
  decide +kernel

theorem smokeBox_valid_native : smokeBox.Valid := by
  native_decide

end Noperthedron.SnubCube.FundamentalPrune

end
