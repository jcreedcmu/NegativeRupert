module

public import Noperthedron.SnubCube.ProjectiveEdgeCertificate
public meta import Noperthedron.SnubCube.ProjectiveEdgeCertificate

@[expose] public section


/-!
# Positive-radius projective edge-certificate smoke test

This row controls a full rational view triangle and a three-dimensional
Cayley box of half-width `1/100`; it contains no trigonometric interval data.
-/

namespace Noperthedron.SnubCube.ProjectiveEdgeCertificateSmoke

open ProjectiveView ProjectiveEdgeCertificate

def smokeInterval : CayleyInterval ℚ :=
  CayleyInterval.mk
    { θ := 0, φ := 0, x := 19 / 100, y := 9 / 100, z := -1 / 100 }
    { θ := 2, φ := 2, x := 21 / 100, y := 11 / 100, z := 1 / 100 }
    (by rw [CayleyPose.le_iff]; norm_num)

def smokeTriangle : Triangle ℚ := ![
  ![13 / 24, 1 / 6, 7 / 24],
  ![7 / 12, 1 / 12, 1 / 3],
  ![17 / 24, 1 / 12, 5 / 24]]

def smokeBox : Box where
  interval := smokeInterval
  triangle := smokeTriangle
  edgePred := 8
  outerIndex := fun i => ![
    VertexIndex.ofFin24 14, VertexIndex.ofFin24 4,
    VertexIndex.ofFin24 8, VertexIndex.ofFin24 1,
    VertexIndex.ofFin24 13, VertexIndex.ofFin24 5,
    VertexIndex.ofFin24 15, VertexIndex.ofFin24 3,
    VertexIndex.ofFin24 10] i
  innerIndex := fun i => ![
    VertexIndex.ofFin24 14, VertexIndex.ofFin24 4,
    VertexIndex.ofFin24 8, VertexIndex.ofFin24 1,
    VertexIndex.ofFin24 13, VertexIndex.ofFin24 5,
    VertexIndex.ofFin24 15, VertexIndex.ofFin24 3,
    VertexIndex.ofFin24 10] i
  nonzeroWitness := fun i => ![
    VertexIndex.ofFin24 5, VertexIndex.ofFin24 15,
    VertexIndex.ofFin24 3, VertexIndex.ofFin24 10,
    VertexIndex.ofFin24 14, VertexIndex.ofFin24 4,
    VertexIndex.ofFin24 8, VertexIndex.ofFin24 1,
    VertexIndex.ofFin24 13] i

theorem smoke_valid_kernel : smokeBox.Valid := by
  decide +kernel

theorem smoke_valid_native : smokeBox.Valid := by
  native_decide

theorem smoke_no_translated_rupert :
    ¬ ∃ p ∈ smokeInterval.toReal, ∃ offset : ℝ²,
      (p.matrixPoseWithOffset offset).InOuterViewChamber ∧
      InTriangle (toReal smokeTriangle) (normalizedView p) ∧
      RupertPose (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull := by
  rintro ⟨p, hp, offset, hchamber, htriangle, hrupert⟩
  exact smokeBox.valid_imp_not_translated_rupert smoke_valid_kernel
    p hp offset hchamber htriangle hrupert

end Noperthedron.SnubCube.ProjectiveEdgeCertificateSmoke

end
