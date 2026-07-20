module

public import Noperthedron.SnubCube.ProjectiveTransitionBox
public meta import Noperthedron.SnubCube.ProjectiveTransitionBox

@[expose] public section


namespace Noperthedron.SnubCube.ProjectiveTransitionBoxSmoke

open Noperthedron.Checker
open ProjectiveTransitionBox

/-- A zero-width exact leaf exercises all parts of the five-dimensional
checker, including all 72 support-dominance comparisons. -/
def pointBox : Box where
  familyIndex := 2
  variableBalls := ![
    RatBall.const (1 / 1000),
    RatBall.const 0,
    RatBall.const 0,
    RatBall.const 0,
    RatBall.const 1]

theorem pointBox_valid_kernel : pointBox.Valid := by
  decide +kernel

theorem pointBox_valid_native : pointBox.Valid := by
  native_decide

/-- A genuine positive-width leaf through the thin gap missed by every
`Pi = Qi` transition family.  This also exercises exact affine recentering. -/
def transverseGapBox : Box where
  familyIndex := 3
  variableBalls := ![
    RatBall.ofEndpoints (1 / 10^9) (1 / 1000),
    RatBall.ofEndpoints 0 (1 / 100),
    RatBall.ofEndpoints (-1) 1,
    RatBall.ofEndpoints (-16) (-15),
    RatBall.ofEndpoints (133 / 20) (27 / 4)]

theorem transverseGapBox_valid_kernel : transverseGapBox.Valid := by
  decide +kernel

theorem transverseGapBox_valid_native : transverseGapBox.Valid := by
  native_decide

/-- The translated-support family found by direct containment duality at the
nested `e = O(d)` transition.  The four earlier families all have negative
obstruction quotient at this exact point. -/
def nestedPointBox : Box where
  familyIndex := 4
  variableBalls := ![
    RatBall.const (1 / 10^6),
    RatBall.const (32 / 10^6),
    RatBall.const 16,
    RatBall.const (-16),
    RatBall.const (67 / 10)]

theorem nestedPointBox_valid_kernel : nestedPointBox.Valid := by
  decide +kernel

theorem nestedPointBox_valid_native : nestedPointBox.Valid := by
  native_decide

/-- A codimension-one width certificate with two positive determinant
weights and one identically zero weight.  Some support quotients have the
wrong sign off the face, but their exact tangential factor vanishes at
`e = 0`. -/
def widthPointBox : Box where
  familyIndex := 5
  variableBalls := ![
    RatBall.const (19 / 20000),
    RatBall.const 0,
    RatBall.const 6,
    RatBall.const (-15),
    RatBall.const (683 / 100)]

theorem widthPointBox_valid_kernel : widthPointBox.Valid := by
  decide +kernel

theorem widthPointBox_valid_native : widthPointBox.Valid := by
  native_decide

end Noperthedron.SnubCube.ProjectiveTransitionBoxSmoke

end
