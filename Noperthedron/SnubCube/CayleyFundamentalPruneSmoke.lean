module

public import Noperthedron.SnubCube.CayleyFundamentalPrune
public meta import Noperthedron.SnubCube.CayleyFundamentalPrune

@[expose] public section


/-!
# Positive-radius smoke test for polynomial Cayley pruning

The outer-angle coordinates span their entire root ranges; only the three
relative coordinates matter to this leaf.  Both proof modes check the same
rational center-radius computation.
-/

namespace Noperthedron.SnubCube.CayleyFundamentalPruneSmoke

open CayleyFundamentalPrune

def smokeInterval : CayleyInterval ℚ :=
  CayleyInterval.mk
    { θ := 0, φ := 0, x := -1 / 100, y := -1 / 100, z := 99 / 100 }
    { θ := 2, φ := 2, x := 1 / 100, y := 1 / 100, z := 101 / 100 }
    (by rw [CayleyPose.le_iff]; norm_num)

def smokeBox : Box where
  interval := smokeInterval
  symmetryIndex := VertexIndex.ofFin24 9

theorem smoke_valid_kernel : smokeBox.Valid := by
  decide +kernel

theorem smoke_valid_native : smokeBox.Valid := by
  native_decide

theorem smoke_excludes_fundamental_pose :
    ¬ ∃ p ∈ smokeInterval.toReal, ∃ offset : ℝ²,
      (p.matrixPoseWithOffset offset).InSnubFundamentalDomain :=
  smokeBox.valid_imp_no_fundamental_pose smoke_valid_kernel

end Noperthedron.SnubCube.CayleyFundamentalPruneSmoke

end
