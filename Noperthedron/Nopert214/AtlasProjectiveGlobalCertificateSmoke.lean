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

/-! A substantially larger row which fails the old nested interval bound but
is closed by the view-simplex × relative-box Bernstein bound. -/

def bernsteinInterval : AtlasInterval ℚ :=
  AtlasInterval.mk
    { θ := 0, φ := 0
      x := -5 / 16, y := 71 / 128, z := 97 / 128 }
    { θ := 0, φ := 0
      x := -29 / 96, y := 9 / 16, z := 49 / 64 }
    (by rw [AtlasPose.le_iff]; norm_num)

def bernsteinTriangle : AtlasProjectiveView.Triangle ℚ := ![
  ![265 / 656, 93 / 328, 5 / 16],
  ![37 / 82, 155 / 656, 5 / 16],
  ![153 / 328, 93 / 328, 1 / 4]]

def bernsteinCertificate : AxisCertificate where
  edgeStart := ![3, 5, 17]
  edgeFinish := ![7, 9, 18]
  edgeStart₂ := ![7, 9, 18]
  edgeFinish₂ := ![6, 8, 19]
  mix := ![800, 800, 600]
  index := ![7, 9, 18]
  nonzeroWitness := ![12, 19, 5]
  B := 838405353 / 1000000000

def bernsteinBox : AtlasProjectiveGlobalCertificate.Box where
  interval := bernsteinInterval
  root := 0
  triangle := bernsteinTriangle
  chart := 2
  certificate := bernsteinCertificate
  innerIndex := ![5, 17, 11]
  ballMultiplier := 0

theorem bernstein_old_interval_fails :
    bernsteinBox.adjustedDisplacementBall.center -
      bernsteinBox.adjustedDisplacementBall.radius < 0 := by
  native_decide

theorem bernstein_valid_kernel : bernsteinBox.Valid := by decide +kernel

theorem bernstein_valid_native : bernsteinBox.Valid := by native_decide

/-! A silhouette-transition row where the old product of independent
weight/support maxima loses the positive margin.  The correlated simplex
controls in `weightedDefectUpper` recover it. -/

def weightedInterval : AtlasInterval ℚ :=
  AtlasInterval.mk
    { θ := 0, φ := 0, x := 1 / 4, y := 15 / 16, z := 7 / 8 }
    { θ := 0, φ := 0, x := 1 / 3, y := 1, z := 15 / 16 }
    (by rw [AtlasPose.le_iff]; norm_num)

def weightedTriangle : AtlasProjectiveView.Triangle ℚ := ![
  ![61 / 164, 31 / 82, 1 / 4],
  ![51 / 164, 31 / 164, 1 / 2],
  ![23 / 41, 31 / 164, 1 / 4]]

def weightedCertificate : AxisCertificate where
  edgeStart := ![3, 9, 17]
  edgeFinish := ![7, 12, 18]
  edgeStart₂ := ![7, 12, 18]
  edgeFinish₂ := ![6, 13, 19]
  mix := ![800, 800, 400]
  index := ![7, 12, 18]
  nonzeroWitness := ![12, 3, 9]
  B := 1012059661 / 1000000000

def weightedBox : AtlasProjectiveGlobalCertificate.Box where
  interval := weightedInterval
  root := 0
  triangle := weightedTriangle
  chart := 2
  certificate := weightedCertificate
  innerIndex := ![5, 13, 11]
  ballMultiplier := 0

theorem weighted_triangle_valid :
    AtlasProjectiveEdgeCertificate.SignedTriangleValid
      weightedBox.root weightedBox.triangle := by
  native_decide

theorem weighted_weights_valid :
    (∀ i, 0 ≤ weightedBox.weightLower i) ∧
      (∃ i, 0 < weightedBox.weightLower i) := by
  native_decide

theorem weighted_directions_valid :
    ∀ i, weightedBox.supportUpper i
      (weightedBox.certificate.nonzeroWitness i) < 0 := by
  native_decide

theorem weighted_displacement_valid :
    weightedBox.displacementError ≤
      weightedBox.certifiedDisplacementLower -
        weightedBox.dBound * weightedBox.weightedDefectUpper := by
  native_decide

theorem weighted_old_defect_fails :
    weightedBox.certifiedDisplacementLower -
        weightedBox.dBound * weightedBox.totalDefect <
      weightedBox.displacementError := by
  native_decide

theorem weighted_valid_kernel : weightedBox.Valid := by decide +kernel

theorem weighted_valid_native : weightedBox.Valid := by native_decide

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
