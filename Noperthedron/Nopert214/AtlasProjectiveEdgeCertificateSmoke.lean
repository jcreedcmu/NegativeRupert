module

public import Noperthedron.Nopert214.AtlasProjectiveEdgeCertificate
public meta import Noperthedron.Nopert214.AtlasProjectiveEdgeCertificate

@[expose] public section

/-! # Dual-evaluator smoke test for a projective atlas row -/

namespace Noperthedron.Nopert214.AtlasProjectiveEdgeCertificateSmoke

open AtlasProjectiveEdgeCertificate AtlasProjectiveView
open Noperthedron.SnubCube.ProjectiveView

def interval : AtlasInterval ℚ :=
  AtlasInterval.mk
    { θ := 0, φ := 0, x := 99 / 100, y := 99 / 100, z := 99 / 100 }
    { θ := 8 / 5, φ := 4, x := 101 / 100, y := 101 / 100,
      z := 101 / 100 }
    (by rw [AtlasPose.le_iff]; norm_num)

def triangle : AtlasProjectiveView.Triangle ℚ := ![
  ![1 / 4, 3 / 8, 3 / 8],
  ![3 / 8, 1 / 4, 3 / 8],
  ![3 / 8, 3 / 8, 1 / 4]]

def box : Box where
  interval := interval
  root := 0
  triangle := triangle
  chart := 0
  edgePred := 7
  outerIndex := fun i => ![13, 17, 18, 3, 7, 6, 9, 12] i
  innerIndex := fun i => ![9, 9, 12, 17, 18, 3, 7, 6] i
  nonzeroWitness := fun i => ![7, 6, 9, 12, 17, 18, 3, 3] i
  ballMultiplier := fun _ => 1 / 100

theorem valid_kernel : box.Valid := by
  decide +kernel

theorem valid_native : box.Valid := by
  native_decide

theorem excludes_triangle_kernel {p : AtlasPose ℝ}
    (hp : p ∈ interval.toReal) (offset : ℝ²)
    (hbounded : p.CayleyBounded)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal triangle)
      (normalizedView box.root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset)
      exactPolyhedron.hull :=
  box.valid_imp_not_translated_rupert valid_kernel hp hbounded offset hscale hmem

theorem excludes_triangle_native {p : AtlasPose ℝ}
    (hp : p ∈ interval.toReal) (offset : ℝ²)
    (hbounded : p.CayleyBounded)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal triangle)
      (normalizedView box.root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset)
      exactPolyhedron.hull :=
  box.valid_imp_not_translated_rupert valid_native hp hbounded offset hscale hmem

end Noperthedron.Nopert214.AtlasProjectiveEdgeCertificateSmoke

end
