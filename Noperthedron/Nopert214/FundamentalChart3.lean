module

public import Noperthedron.Nopert214.AtlasProjectiveSolutionTree
public meta import Noperthedron.Nopert214.AtlasProjectiveSolutionTree

@[expose] public section

/-!
# Seven-row exclusion of Cayley chart 3

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

def region (i : Fin 2) : AtlasProjectiveSolutionTree.Region :=
  .triangle (wedgeRoot i) (rootTriangle (wedgeRoot i))

def getRowKernel : ℕ → AtlasProjectiveSolutionTree.Row
  | 0 => .viewRoot 0 ![1, 2] root
  | 1 => .cayleySplit 1 5 6 4 root (region 0)
  | 2 => .cayleySplit 2 3 4 4 root (region 1)
  | 3 => .fundamentalPrune 3
      { interval := lower, chart := 3, direction := .negative } (region 1)
  | 4 => .fundamentalPrune 4
      { interval := upper, chart := 3, direction := .positive } (region 1)
  | 5 => .fundamentalPrune 5
      { interval := lower, chart := 3, direction := .negative } (region 0)
  | 6 => .fundamentalPrune 6
      { interval := upper, chart := 3, direction := .positive } (region 0)
  | _ => default

def table : AtlasProjectiveSolutionTree.Table where
  chart := 3
  get := getRowKernel
  size := 7

theorem table_valid_native : table.Valid := by native_decide

theorem table_valid_kernel : table.Valid := by decide +kernel

end Noperthedron.Nopert214.FundamentalChart3

end
