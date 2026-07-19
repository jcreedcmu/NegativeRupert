module

public import Noperthedron.SnubCube.Certificate
public meta import Noperthedron.SnubCube.Certificate

@[expose] public section


/-!
# Shared-checker smoke certificate

A zero-radius box with a comfortable width obstruction.  This deliberately
small fixture verifies that the same `Box.Valid` proposition is accepted both
by kernel reduction and by `native_decide` before a generated full tree is
introduced.
-/

namespace Noperthedron.SnubCube.Certificate

def smokePose : Pose ℚ := {
  θ₁ := -2634 / 1000
  φ₁ := 1992 / 1000
  θ₂ := -1527 / 1000
  φ₂ := 1204 / 1000
  α := -381 / 1000
}

def smokeInterval : PoseInterval ℚ :=
  PoseInterval.mk smokePose smokePose (by rfl)

def smokeBox : Box := {
  interval := smokeInterval
  contact := ![
    { innerIndex := VertexIndex.ofFin24 ⟨14, by omega⟩
      outerIndex := VertexIndex.ofFin24 ⟨17, by omega⟩
      direction := ![(1 : ℚ), 0]
      weight := 1 },
    { innerIndex := VertexIndex.ofFin24 ⟨5, by omega⟩
      outerIndex := VertexIndex.ofFin24 ⟨16, by omega⟩
      direction := ![(-1 : ℚ), 0]
      weight := 1 },
    { innerIndex := 0
      outerIndex := 0
      direction := ![(0 : ℚ), 1]
      weight := 0 }
  ]
}

theorem smokeBox_valid_kernel : smokeBox.Valid := by
  decide +kernel

theorem smokeBox_valid_native : smokeBox.Valid := by
  native_decide

end Noperthedron.SnubCube.Certificate

end
