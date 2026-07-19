module

public import Noperthedron.SnubCube.CayleyEdgeCertificate
public meta import Noperthedron.SnubCube.CayleyEdgeCertificate

@[expose] public section


/-!
# Positive-radius projected-edge certificate smoke test

This representative row has radius `1/50` in all five coordinates—an order
of magnitude larger than the corresponding frozen-direction global rows.
-/

namespace Noperthedron.SnubCube.CayleyEdgeCertificateSmoke

open CayleyEdgeCertificate

def smokeInterval : CayleyInterval ℚ :=
  CayleyInterval.mk
    { θ := 7 / 25, φ := 27 / 25,
      x := 9 / 50, y := 2 / 25, z := -1 / 50 }
    { θ := 8 / 25, φ := 28 / 25,
      x := 11 / 50, y := 3 / 25, z := 1 / 50 }
    (by rw [CayleyPose.le_iff]; norm_num)

def smokeBox : Box where
  interval := smokeInterval
  edgePred := 8
  outerIndex := fun i => ![
    VertexIndex.ofFin24 14, VertexIndex.ofFin24 4,
    VertexIndex.ofFin24 8, VertexIndex.ofFin24 1,
    VertexIndex.ofFin24 13, VertexIndex.ofFin24 5,
    VertexIndex.ofFin24 15, VertexIndex.ofFin24 3,
    VertexIndex.ofFin24 10] i
  innerIndex := fun i => ![
    VertexIndex.ofFin24 14, VertexIndex.ofFin24 4,
    VertexIndex.ofFin24 20, VertexIndex.ofFin24 1,
    VertexIndex.ofFin24 13, VertexIndex.ofFin24 5,
    VertexIndex.ofFin24 19, VertexIndex.ofFin24 3,
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
      RupertPose (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull :=
  smokeBox.valid_imp_no_translated_rupert_in_interval smoke_valid_kernel

end Noperthedron.SnubCube.CayleyEdgeCertificateSmoke

end
