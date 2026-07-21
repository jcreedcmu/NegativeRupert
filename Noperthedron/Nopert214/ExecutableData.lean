module

public import Noperthedron.Nopert214.FundamentalChart3
public import Noperthedron.Nopert214.GeneratedChart0NativeData
public import Noperthedron.Nopert214.GeneratedChart1NativeData
public import Noperthedron.Nopert214.GeneratedChart2NativeData
public import Noperthedron.Nopert214.GeneratedLocalView0SparseNativeData
public import Noperthedron.Nopert214.GeneratedLocalView1SparseNativeData
public import Noperthedron.Nopert214.GeneratedLocalView2SparseNativeData
public import Noperthedron.Nopert214.GeneratedLocalView3SparseNativeData

@[expose] public section

/-!
# Data wiring for the Nopert #214 native executable proof

The imported generated modules contain data only and are deliberately ignored
by Git. Validity is established at runtime by `NativeExecutable.constructProof`.
-/

namespace Noperthedron.Nopert214.ExecutableData

open AtlasProjectiveSolutionTree

def localTables : Fin 4 → AtlasProjectiveLocalViewTree.Table :=
  ![GeneratedLocalView0SparseNativeData.table,
    GeneratedLocalView1SparseNativeData.table,
    GeneratedLocalView2SparseNativeData.table,
    GeneratedLocalView3SparseNativeData.table]

def globalTables (shared : SharedLocalTables) :
    CayleyAtlas.ChartIndex → AtlasProjectiveSolutionTree.Table :=
  ![GeneratedChart0NativeData.table shared,
    GeneratedChart1NativeData.table shared,
    GeneratedChart2NativeData.table shared,
    { FundamentalChart3.table with sharedLocal := shared }]

theorem globalTables_chart (shared : SharedLocalTables) (chart) :
    (globalTables shared chart).chart = chart := by
  fin_cases chart <;> rfl

theorem globalTables_shared (shared : SharedLocalTables) (chart) :
    (globalTables shared chart).sharedLocal = shared := by
  fin_cases chart <;> rfl

end Noperthedron.Nopert214.ExecutableData

end
