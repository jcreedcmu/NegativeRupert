module

public import Noperthedron.SnubCube.ProjectiveSolutionTree
public import Noperthedron.SnubCube.ProjectiveEdgeCertificateSmoke
public import Noperthedron.SnubCube.ProjectiveLocalCertificateSmoke
public import Noperthedron.SnubCube.CayleyLocalCertificateSmoke
public import Noperthedron.SnubCube.CayleyFundamentalPruneSmoke
public meta import Noperthedron.SnubCube.ProjectiveSolutionTree
public meta import Noperthedron.SnubCube.ProjectiveEdgeCertificateSmoke
public meta import Noperthedron.SnubCube.ProjectiveLocalCertificateSmoke
public meta import Noperthedron.SnubCube.CayleyLocalCertificateSmoke
public meta import Noperthedron.SnubCube.CayleyFundamentalPruneSmoke

@[expose] public section


/-!
# Mixed projective solution-tree smoke test

The table exercises both kinds of subdivision and every leaf constructor.
The reachable root uses projective chamber subdivision followed by two valid
fundamental-domain pruning leaves.  The same finite row proposition is
checked by the kernel evaluator and by native code.
-/

namespace Noperthedron.SnubCube.ProjectiveSolutionTreeSmoke

open ProjectiveView ProjectiveSolutionTree

def lowerPruneBox : CayleyFundamentalPrune.Box := {
  CayleyFundamentalPruneSmoke.smokeBox with
  interval := CayleyFundamentalPruneSmoke.smokeInterval.lowerHalf 2
}

def upperPruneBox : CayleyFundamentalPrune.Box := {
  CayleyFundamentalPruneSmoke.smokeBox with
  interval := CayleyFundamentalPruneSmoke.smokeInterval.upperHalf 2
}

def smokeGet : ℕ → Row
  | 0 => .viewRoot 0 ![1, 2] CayleyFundamentalPruneSmoke.smokeInterval
  | 1 => .prune 1 (.triangle (chamberRoot 0))
      CayleyFundamentalPruneSmoke.smokeBox
  | 2 => .prune 2 (.triangle (chamberRoot 1))
      CayleyFundamentalPruneSmoke.smokeBox
  | 3 => .viewSplit 3 ![4, 5, 6, 7]
      CayleyFundamentalPruneSmoke.smokeInterval (chamberRoot 0)
  | 4 => .prune 4 (.triangle (split (chamberRoot 0) 0))
      CayleyFundamentalPruneSmoke.smokeBox
  | 5 => .prune 5 (.triangle (split (chamberRoot 0) 1))
      CayleyFundamentalPruneSmoke.smokeBox
  | 6 => .prune 6 (.triangle (split (chamberRoot 0) 2))
      CayleyFundamentalPruneSmoke.smokeBox
  | 7 => .prune 7 (.triangle (split (chamberRoot 0) 3))
      CayleyFundamentalPruneSmoke.smokeBox
  | 8 => .cayleySplit 8 9 10 2
      CayleyFundamentalPruneSmoke.smokeInterval .chamber
  | 9 => .prune 9 .chamber lowerPruneBox
  | 10 => .prune 10 .chamber upperPruneBox
  | 11 => .projective 11 ProjectiveEdgeCertificateSmoke.smokeBox
  | 12 => .localLeaf 12 .chamber CayleyLocalCertificateSmoke.smokeBox
  | 13 => .projectiveLocal 13 ProjectiveLocalCertificateSmoke.smokeBox
  | _ => default

theorem smoke_rows_valid_kernel : RowsValidAt smokeGet 14 := by
  decide +kernel

theorem smoke_rows_valid_native : RowsValidAt smokeGet 14 := by
  native_decide

theorem smoke_excludes_chamber_pose :
    NoRupert CayleyFundamentalPruneSmoke.smokeInterval .chamber := by
  simpa [smokeGet, Row.interval, Row.region] using
    valid_imp_noRupert_ix smokeGet 14 smoke_rows_valid_kernel 0 (by norm_num)

end Noperthedron.SnubCube.ProjectiveSolutionTreeSmoke

end
