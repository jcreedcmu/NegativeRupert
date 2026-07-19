module

public import Noperthedron.SnubCube.Certificate
public meta import Noperthedron.SnubCube.Certificate

@[expose] public section


/-!
# Shared global-checker smoke certificate

A positive-radius box with a comfortable balanced width obstruction.  It was
produced by `scripts/snub_certificate_search.py global-smoke` and verifies
that the same `Box.Valid` proposition is accepted both by kernel reduction
and by `native_decide` before a generated full tree is introduced.
-/

namespace Noperthedron.SnubCube.Certificate

def smokeInterval : PoseInterval ℚ :=
  PoseInterval.mk
    { θ₁ := -1 / 100, θ₂ := 99 / 100
      φ₁ := -1 / 100, φ₂ := 99 / 100
      α := -1 / 100 }
    { θ₁ := 1 / 100, θ₂ := 101 / 100
      φ₁ := 1 / 100, φ₂ := 101 / 100
      α := 1 / 100 }
    (by norm_num [Pose.le_iff])

def smokeBox : Box := {
  interval := smokeInterval
  contact := ![
    { innerIndex := VertexIndex.ofFin24 18
      outerIndex := 0
      direction := ![-1771 / 3229, -2700 / 3229]
      weight := 20093700 / 39798421 },
    { innerIndex := VertexIndex.ofFin24 5
      outerIndex := 0
      direction := ![8911 / 11089, 6600 / 11089]
      weight := 2034600 / 11588881 },
    { innerIndex := VertexIndex.ofFin24 19
      outerIndex := 0
      direction := ![1411 / 3589, 3300 / 3589]
      weight := 12371100 / 35806381 }
  ]
}

theorem smokeBox_valid_kernel : smokeBox.Valid := by
  decide +kernel

theorem smokeBox_valid_native : smokeBox.Valid := by
  native_decide

end Noperthedron.SnubCube.Certificate

end
