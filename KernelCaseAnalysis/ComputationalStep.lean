module

public import Noperthedron.SolutionTable.Assemble
public import KernelCaseAnalysis.Gen.Final

@[expose] public section


/-!
# The expensive computational step, verified kernel-only

Builds the `ValidTable` from the generated chunk tree: the 1,119,311 rows
are loaded as literal 512-row chunks (`Gen/LoadNNN.lean`), served through
the digit-curried getter (`Gen/Dispatch.lean`), validated range-by-range
with `decide +kernel` (`Gen/ValidateNNNN.lean` — the expensive part), and
folded by the `RangeOk` combine chain (`Gen/CombineNN.lean`, `Gen/Final.lean`).

Everything here is checked by the Lean kernel alone: axioms are `propext`,
`Classical.choice`, and `Quot.sound` — no `sorry`, no `ofReduceBool`.

This library is deliberately **not** in `defaultTargets`: building it is the
full kernel verification run (~31 core-hours by the generator's model:
~25k s of globals, ~77k s of second-order locals, ~8k s of splits; local
ranges are singletons with a ~4.7 GB per-decide envelope, so expect
~10-way parallelism on 64 GB — roughly 3 hours wall):

    lake build KernelCaseAnalysis
-/

namespace Noperthedron.KernelCaseAnalysis

open Noperthedron Noperthedron.Solution

/-- The valid solution table, assembled from the generated chunk tree. -/
noncomputable def solutionTable : Solution.ValidTable :=
  Solution.validTableOfGetter getRow 1119311 (by norm_num)
    row0_interval allRows_validIxAt

end Noperthedron.KernelCaseAnalysis

end
