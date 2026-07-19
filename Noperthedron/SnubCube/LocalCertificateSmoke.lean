module

public import Noperthedron.SnubCube.LocalCertificate
public meta import Noperthedron.SnubCube.LocalCertificate

@[expose] public section


/-!
# Shared local-checker smoke certificate

This positive-radius identity-stratum box was produced by
`scripts/snub_certificate_search.py local-smoke`.  It exercises every field
of the local checker, including pointwise support, the computed rational
tetrahedron coordinates, the matrix mismatch bound, and both decision paths.
-/

namespace Noperthedron.SnubCube.LocalCertificate

def smokeInterval : PoseInterval ℚ :=
  PoseInterval.mk
    { θ₁ := 29999 / 100000, θ₂ := 29999 / 100000
      φ₁ := 109999 / 100000, φ₂ := 109999 / 100000
      α := -1 / 100000 }
    { θ₁ := 30001 / 100000, θ₂ := 30001 / 100000
      φ₁ := 110001 / 100000, φ₂ := 110001 / 100000
      α := 1 / 100000 }
    (by norm_num [Pose.le_iff])

def smokeBox : Box := {
  interval := smokeInterval
  symmetryIndex := VertexIndex.ofFin24 0
  certificate := ![
    { contact := ![
        { index := VertexIndex.ofFin24 13, direction := ![429 / 821, -700 / 821] },
        { index := VertexIndex.ofFin24 5, direction := ![2499 / 2501, 100 / 2501] },
        { index := VertexIndex.ofFin24 14, direction := ![-9951 / 10049, 1400 / 10049] }
      ] },
    { contact := ![
        { index := VertexIndex.ofFin24 8, direction := ![-2139 / 2861, -1900 / 2861] },
        { index := VertexIndex.ofFin24 15, direction := ![391 / 409, 120 / 409] },
        { index := VertexIndex.ofFin24 10, direction := ![-3439 / 16561, 16200 / 16561] }
      ] },
    { contact := ![
        { index := VertexIndex.ofFin24 4, direction := ![-8911 / 11089, -6600 / 11089] },
        { index := VertexIndex.ofFin24 13, direction := ![15 / 17, -8 / 17] },
        { index := VertexIndex.ofFin24 10, direction := ![-319 / 481, 360 / 481] }
      ] },
    { contact := ![
        { index := VertexIndex.ofFin24 13, direction := ![429 / 821, -700 / 821] },
        { index := VertexIndex.ofFin24 10, direction := ![-2079 / 17921, 17800 / 17921] },
        { index := VertexIndex.ofFin24 4, direction := ![-9991 / 10009, 600 / 10009] }
      ] }
  ]
  c := 19887 / 1000000
  r := 50000601 / 1000000000000
}

theorem smokeBox_valid_kernel : smokeBox.Valid := by
  decide +kernel

theorem smokeBox_valid_native : smokeBox.Valid := by
  native_decide

end Noperthedron.SnubCube.LocalCertificate

end
