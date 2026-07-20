module

public import Noperthedron.Nopert214.AtlasProjectiveSolutionTree
public meta import Noperthedron.Nopert214.AtlasProjectiveSolutionTree

@[expose] public section

/-!
# Four-row exclusion of Cayley chart 3

In the fivefold max-trace fundamental domain, chart 3 is empty.  Splitting
once at `z = 0` makes the two adjacent-symmetry advantages uniformly
positive.  The same tiny table is checked by both evaluators without any
array-backed generated data.
-/

namespace Noperthedron.Nopert214.FundamentalChart3

open AtlasProjectiveSolutionTree AtlasProjectiveView
open Noperthedron.SnubCube.ProjectiveView

def root : AtlasProjectiveSolutionTree.Interval := AtlasPose.rootInterval ℚ
def lower : AtlasProjectiveSolutionTree.Interval := root.lowerHalf 4
def upper : AtlasProjectiveSolutionTree.Interval := root.upperHalf 4

def region : AtlasProjectiveSolutionTree.Region :=
  .triangle 0 (rootTriangle 0)

def getRowKernel : ℕ → AtlasProjectiveSolutionTree.Row
  | 0 => .viewRoot 0 1 root
  | 1 => .cayleySplit 1 2 3 4 root region
  | 2 => .fundamentalPrune 2
      { interval := lower, chart := 3, direction := .negative } region
  | 3 => .fundamentalPrune 3
      { interval := upper, chart := 3, direction := .positive } region
  | _ => default

def table : AtlasProjectiveSolutionTree.Table where
  chart := 3
  get := getRowKernel
  size := 4

theorem table_valid_native : table.Valid := by native_decide

theorem table_valid_kernel : table.Valid := by decide +kernel

end Noperthedron.Nopert214.FundamentalChart3

end
