module

public import Noperthedron.Nopert214.AtlasProjectiveGlobalCertificate
public meta import Noperthedron.Nopert214.AtlasProjectiveGlobalCertificate

@[expose] public section

/-!
# Dual-evaluator smoke test for a projective balanced-triple row

This certificate uses three moving cone-interior silhouette directions near
the positive projective view `(1/3, 1/3, 1/3)`.  It covers a relative Cayley
box centered at `(1, 1, 2/3)` and has a direct-displacement margin of about
`0.0794` after interval and exact-vertex approximation errors.
-/

namespace Noperthedron.Nopert214.AtlasProjectiveGlobalCertificateSmoke

open Noperthedron.SnubCube.ProjectiveView
open AtlasProjectiveGlobalCertificate AtlasProjectiveLocalCertificate
  AtlasProjectiveView

def interval : AtlasInterval ℚ :=
  AtlasInterval.mk
    { θ := 0, φ := 0
      x := 999 / 1000, y := 999 / 1000, z := 1997 / 3000 }
    { θ := 0, φ := 0
      x := 1001 / 1000, y := 1001 / 1000, z := 2003 / 3000 }
    (by rw [AtlasPose.le_iff]; norm_num)

def triangle : AtlasProjectiveView.Triangle ℚ := ![
  ![10003 / 30000, 9997 / 30000, 1 / 3],
  ![1 / 3, 10003 / 30000, 9997 / 30000],
  ![9997 / 30000, 1 / 3, 10003 / 30000]]

def certificate : AxisCertificate where
  edgeStart := ![13, 3, 7]
  edgeFinish := ![17, 7, 6]
  edgeStart₂ := ![17, 7, 6]
  edgeFinish₂ := ![18, 6, 9]
  mix := ![800, 800, 200]
  index := ![17, 7, 6]
  nonzeroWitness := ![7, 13, 17]
  B := 1360199623 / 1000000000

def box : AtlasProjectiveGlobalCertificate.Box where
  interval := interval
  root := 0
  triangle := triangle
  chart := 0
  certificate := certificate
  innerIndex := ![9, 17, 3]
  ballMultiplier := 1 / 100

theorem valid_kernel : box.Valid := by decide +kernel

theorem valid_native : box.Valid := by native_decide

theorem excludes_triangle_kernel {p : AtlasPose ℝ}
    (hp : p ∈ interval.toReal) (offset : ℝ²)
    (hbounded : p.CayleyBounded)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal triangle)
      (normalizedView box.root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset)
      exactPolyhedron.hull :=
  box.valid_imp_not_translated_rupert valid_kernel p hp hbounded hscale hmem offset

theorem excludes_triangle_native {p : AtlasPose ℝ}
    (hp : p ∈ interval.toReal) (offset : ℝ²)
    (hbounded : p.CayleyBounded)
    (hscale : 1 ≤ viewScale box.root p)
    (hmem : InTriangle (toReal triangle)
      (normalizedView box.root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset)
      exactPolyhedron.hull :=
  box.valid_imp_not_translated_rupert valid_native p hp hbounded hscale hmem offset

end Noperthedron.Nopert214.AtlasProjectiveGlobalCertificateSmoke

end
