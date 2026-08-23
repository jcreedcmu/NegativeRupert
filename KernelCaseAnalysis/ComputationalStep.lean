module

public import Noperthedron.SolutionTable.Assemble
public import KernelCaseAnalysis.Gen.Final

@[expose] public section


/-!
# The expensive computational step, verified kernel-only

Builds the `ValidTable` from the generated chunk tree: the 975,329 rows
are loaded as literal 512-row chunks (`Gen/LoadNNN.lean`), served through
the digit-curried getter (`Gen/Dispatch.lean`), validated range-by-range
with `decide +kernel` (`Gen/ValidateNNNN.lean` — the expensive part), and
folded by the `RangeOk` combine chain (`Gen/CombineNN.lean`, `Gen/Final.lean`).

Everything here is checked by the Lean kernel alone: axioms are `propext`,
`Classical.choice`, and `Quot.sound` — no `sorry`, no `ofReduceBool`.

This library is deliberately **not** in `defaultTargets`: building it is the
full kernel verification run (~15 core-hours by the generator's model:
~19k s of globals, ~26k s of second-order locals via the `Local2NatOffset`
all-`Nat` tier and the `Local2NatDelta` δ₂ fraction, ~8k s of splits;
local ranges are singletons with a ~2.7 GB per-decide envelope, so full
16-way parallelism fits in 64 GB — roughly 60–80 minutes wall):

    lake build KernelCaseAnalysis
-/

namespace Noperthedron.KernelCaseAnalysis

open Noperthedron Noperthedron.Solution

/-- The valid solution table, assembled from the generated chunk tree. -/
noncomputable def solutionTable : Solution.ValidTable :=
  Solution.validTableOfGetter getRow 975329 (by norm_num)
    row0_interval allRows_validIxAt

end Noperthedron.KernelCaseAnalysis

end
