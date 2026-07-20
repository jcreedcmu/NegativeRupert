module

public import Noperthedron.Nopert214.AtlasProjectiveLocalCertificate
public meta import Noperthedron.Nopert214.AtlasProjectiveLocalCertificate

@[expose] public section

/-!
# Executable smoke test for a mixed-edge projective-local row

This exact rational certificate covers a neighborhood of the positive
projective view `(1/3, 1/3, 1/3)` and of the identity relative rotation.
Its moving directions lie strictly inside silhouette vertex cones, as convex
combinations of the two incident edge directions.  Both decision paths check
the same `Box.Valid` proposition.
-/

namespace Noperthedron.Nopert214.AtlasProjectiveLocalCertificateSmoke

open Noperthedron.SnubCube.ProjectiveView
open AtlasProjectiveLocalCertificate AtlasProjectiveView

def interval : AtlasInterval ℚ :=
  AtlasInterval.mk
    { θ := 0, φ := 0
      x := -1 / 1000000, y := -1 / 1000000, z := -1 / 1000000 }
    { θ := 0, φ := 0
      x := 1 / 1000000, y := 1 / 1000000, z := 1 / 1000000 }
    (by rw [AtlasPose.le_iff]; norm_num)

def triangle : AtlasProjectiveView.Triangle ℚ := ![
  ![1000003 / 3000000, 999997 / 3000000, 1 / 3],
  ![1 / 3, 1000003 / 3000000, 999997 / 3000000],
  ![999997 / 3000000, 1 / 3, 1000003 / 3000000]]

def certificates : Fin 4 → AxisCertificate := ![
  { edgeStart := ![13, 3, 13]
    edgeFinish := ![17, 7, 17]
    edgeStart₂ := ![17, 7, 17]
    edgeFinish₂ := ![18, 6, 18]
    mix := ![600, 200, 800]
    index := ![17, 7, 17]
    nonzeroWitness := ![7, 17, 7]
    B := 5445863 / 50000000 },
  { edgeStart := ![13, 17, 7]
    edgeFinish := ![17, 18, 6]
    edgeStart₂ := ![17, 18, 6]
    edgeFinish₂ := ![18, 3, 9]
    mix := ![800, 800, 200]
    index := ![17, 18, 6]
    nonzeroWitness := ![7, 9, 17]
    B := 941187889 / 1000000000 },
  { edgeStart := ![17, 3, 6]
    edgeFinish := ![18, 7, 9]
    edgeStart₂ := ![18, 7, 9]
    edgeFinish₂ := ![3, 6, 12]
    mix := ![200, 800, 400]
    index := ![18, 7, 9]
    nonzeroWitness := ![9, 13, 3]
    B := 1223352527 / 1000000000 },
  { edgeStart := ![18, 7, 9]
    edgeFinish := ![3, 6, 12]
    edgeStart₂ := ![3, 6, 12]
    edgeFinish₂ := ![7, 9, 13]
    mix := ![800, 600, 600]
    index := ![3, 6, 12]
    nonzeroWitness := ![9, 17, 3]
    B := 1558554733 / 1000000000 }]

def box : Box where
  interval := interval
  root := 0
  triangle := triangle
  chart := 0
  symmetryIndex := 0
  certificate := certificates
  c := 1164711 / 250000000
  δ := 307 / 250000000
  r := 49 / 10000000

theorem valid_kernel : box.Valid := by decide +kernel

theorem valid_native : box.Valid := by native_decide

theorem excludes_translated_pose :
    ¬ ∃ p ∈ box.interval.toReal, ∃ offset : ℝ²,
      1 ≤ viewScale box.root p ∧
      InTriangle (toReal box.triangle) (normalizedView box.root p) ∧
      RupertPose (p.matrixPoseWithOffset box.chart offset)
        exactPolyhedron.hull :=
  box.valid_imp_no_translated_rupert_in_region valid_kernel

end Noperthedron.Nopert214.AtlasProjectiveLocalCertificateSmoke

end
