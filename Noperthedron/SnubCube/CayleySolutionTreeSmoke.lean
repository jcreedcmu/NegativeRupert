module

public import Noperthedron.SnubCube.CayleySolutionTree
public import Noperthedron.SnubCube.CayleyGlobalCertificateSmoke
public import Noperthedron.SnubCube.CayleyLocalCertificateSmoke
public import Noperthedron.SnubCube.CayleyFundamentalPruneSmoke
public meta import Noperthedron.SnubCube.CayleySolutionTree
public meta import Noperthedron.SnubCube.CayleyGlobalCertificateSmoke
public meta import Noperthedron.SnubCube.CayleyLocalCertificateSmoke
public meta import Noperthedron.SnubCube.CayleyFundamentalPruneSmoke

@[expose] public section


/-!
# Mixed Cayley solution-tree smoke test

The reachable three-row subtree bisects a positive-radius global box.  Two
additional checked rows exercise the local and pruning constructors.  The
same finite row-validity proposition is evaluated by the kernel and by
native code, after which the recursive semantic theorem excludes every
translated Rupert pose in the parent box.
-/

namespace Noperthedron.SnubCube.CayleySolutionTreeSmoke

open CayleySolutionTree

def lowerGlobalBox : CayleyGlobalCertificate.Box := {
  CayleyGlobalCertificateSmoke.smokeBox with
  interval := CayleyGlobalCertificateSmoke.smokeInterval.lowerHalf 0
}

def upperGlobalBox : CayleyGlobalCertificate.Box := {
  CayleyGlobalCertificateSmoke.smokeBox with
  interval := CayleyGlobalCertificateSmoke.smokeInterval.upperHalf 0
}

def smokeGet : ℕ → Row
  | 0 => .split 0 1 2 0 CayleyGlobalCertificateSmoke.smokeInterval
  | 1 => .global 1 lowerGlobalBox
  | 2 => .global 2 upperGlobalBox
  | 3 => .localLeaf 3 CayleyLocalCertificateSmoke.smokeBox
  | 4 => .prune 4 CayleyFundamentalPruneSmoke.smokeBox
  | _ => default

theorem smoke_rows_valid_kernel : RowsValidAt smokeGet 5 := by
  decide +kernel

theorem smoke_rows_valid_native : RowsValidAt smokeGet 5 := by
  native_decide

theorem smoke_excludes_translated_pose :
    NoRupert CayleyGlobalCertificateSmoke.smokeInterval := by
  simpa [smokeGet, Row.interval] using
    valid_imp_noRupert_ix smokeGet 5 smoke_rows_valid_kernel 0 (by norm_num)

end Noperthedron.SnubCube.CayleySolutionTreeSmoke

end
