#!/usr/bin/env python3
"""Generate the KernelCaseAnalysis chunk tree: load modules (literal row chunks),
the dispatch/getter module, validation modules (RangeOk theorems over
adaptively sized spans), the RangeOk.append combine chain, and the final
capstone. Run from the repo root.

Phases (pass as argv[1]):
  load      - KernelCaseAnalysis/Gen/LoadNNN.lean (8192 rows each, 512-row chunks)
  dispatch  - KernelCaseAnalysis/Gen/Dispatch.lean
  validate  - KernelCaseAnalysis/Gen/ValidateNNNN.lean (~S_PER_FILE kernel-seconds each)
  combine   - KernelCaseAnalysis/Gen/CombineNN.lean + Final.lean
  root      - KernelCaseAnalysis.lean (imports of the two capstone modules)
"""
import sys, os

N = 975329
C = 512
ROWS_PER_LOAD = 8192
NCHUNKS = (N + C - 1) // C          # 1905
NLOAD = (N + ROWS_PER_LOAD - 1) // ROWS_PER_LOAD  # 120

os.makedirs('KernelCaseAnalysis/Gen', exist_ok=True)

def gen_load(only=None):
    for i in range(NLOAD):
        if only is not None and i != only:
            continue
        a = i * ROWS_PER_LOAD
        b = min((i + 1) * ROWS_PER_LOAD, N)
        with open(f'KernelCaseAnalysis/Gen/Load{i:03}.lean', 'w') as f:
            f.write(f"""module

public import Noperthedron.SolutionTable.Load
public meta import Noperthedron.SolutionTable.Load

@[expose] public section

/-! GENERATED (scripts/gen_kernel_chunks.py): rows [{a}, {b}) of the solution
tree as literal 512-row chunks. Requires `solution_tree_v8.csv` at the repo
root. -/

namespace Noperthedron.Solution

load_csv_chunks_curried "solution_tree_v8.csv" from {a} to {b} chunkSize {C}

end Noperthedron.Solution

end
""")

def gen_dispatch():
    imports = "\n".join(f"public import KernelCaseAnalysis.Gen.Load{i:03}" for i in range(NLOAD))
    with open('KernelCaseAnalysis/Gen/Dispatch.lean', 'w') as f:
        f.write(f"""module

public import Noperthedron.SolutionTable.Assemble
public meta import Noperthedron.SolutionTable.Load
{imports}

/-! GENERATED (scripts/gen_kernel_chunks.py): the digit-curried dispatch over
all {NCHUNKS} loaded chunks and the row getter for the kernel run. -/

@[expose] public section

namespace Noperthedron.Solution

assemble_row_dispatch_curried tableDispatch rows {N} chunkSize {C}

/-- The full-table row getter: seven `Fin 8` digit levels per access
(`O(log)`), no `List` walk. -/
noncomputable def getRow : ℕ → Row := rowGetterC tableDispatch

end Noperthedron.Solution

end
""")

def read_node_types():
    """Row cost classes: 1 = global, 2 = local, 3 = small split
    (nrChildren < 15), 4 = full split (nrChildren >= 15)."""
    types = []
    with open('solution_tree_v8.csv') as f:
        next(f)
        for line in f:
            parts = line.split(',', 3)
            t = int(parts[1])
            if t == 3 and parts[2] and int(parts[2]) >= 15:
                t = 4
            types.append(t)
    assert len(types) == N, len(types)
    return types

# per-row kernel memory (MB) and time (s) model, recalibrated 2026-08-23 for
# the Local2NatOffset all-Nat tier: globals/splits keep the 2026-07-10
# numbers (unchanged checkers); locals are budgeted at the SECOND-ORDER cost
# (Row.ValidLocal₂ via the beFastO offset tier + the δ₂PairZ integer
# fraction: ~0.92 s per full row, measured at row 71419; peak RSS 2.7 GB).
# The 670 first-order local
# rows (of 17,938) are over-budgeted by this — negligible. COST_MB[2] >
# MB_BUDGET keeps every local row its own decide-range (the committed Gen/
# tree was generated at the 2026-08-22 model and stays VALID — range sizing
# only depends on COST_MB for locals, and globals/splits are unchanged).
COST_MB = {1: 25, 2: 2000, 3: 21, 4: 130}
COST_S  = {1: 0.038, 2: 1.3, 3: 0.018, 4: 0.10}
# MB_BUDGET sets per-decide range length (range rows ~= MB_BUDGET/COST_MB),
# and kernel time per row RISES with range length: the whnf cache accumulated
# across a decide grows the live heap and hurts locality. Measured 2026-07-17
# (same 2175 global rows, single process, startup subtracted):
# 17-row ranges 18.1 ms/row (RSS 2.4 GB), 34 -> 19.0 (2.5 GB),
# 68 -> 20.8 (2.8 GB), 136 -> 22.9 (3.3 GB), 272 -> 24.7 (4.2 GB),
# 1088 -> 30.2 (9.6 GB). MB_BUDGET=1600 (~68-row global ranges) is the
# knee: going lower buys ~7% more speed but doubles the generated line
# count. COST_S was calibrated at this budget, so S_PER_FILE targeting is
# accurate here. ROWS_PER_LOAD is chosen so a Load process (~3.0 GB at
# 8192 rows; ~54 KB/row above a ~2.6 GB floor) matches the Validate
# envelope (~2.8 GB) — one thread count (16-way -> ~48 GB) fits both phases.
MB_BUDGET = 1600      # per-declaration term-cache budget
S_PER_FILE = 750      # target kernel seconds per file
MAX_RANGE = 1000      # never binds at MB_BUDGET=1600 (max range ~76 rows)

def make_ranges(types):
    ranges = []
    a = 0
    while a < N:
        mb = 0.0
        b = a
        while b < N and b - a < MAX_RANGE:
            mb += COST_MB[types[b]]
            if mb > MB_BUDGET and b > a:
                break
            b += 1
        ranges.append((a, b))
        a = b
    return ranges

def make_files(types, ranges):
    files = []
    cur, sec = [], 0.0
    for (a, b) in ranges:
        cost = sum(COST_S[types[i]] for i in range(a, b))
        cur.append((a, b))
        sec += cost
        if sec >= S_PER_FILE:
            files.append(cur)
            cur, sec = [], 0.0
    if cur:
        files.append(cur)
    return files

def gen_validate(only=None):
    types = read_node_types()
    ranges = make_ranges(types)
    files = make_files(types, ranges)
    print(f"{len(ranges)} ranges in {len(files)} files")
    spans = []
    for v, rs in enumerate(files):
        a0, bend = rs[0][0], rs[-1][1]
        spans.append((a0, bend))
        if only is not None and v != only:
            continue
        thms = []
        for (a, b) in rs:
            thms.append(f"private theorem r_{a} : RangeOk getRow {N} {a} {b} := by decide +kernel")
        fold = [f"private theorem s_{rs[0][1]} : RangeOk getRow {N} {a0} {rs[0][1]} := r_{a0}"]
        for (a, b) in rs[1:]:
            prev = fold[-1].split()[2]
            pend = prev.split('_')[1]
            fold.append(f"private theorem s_{b} : RangeOk getRow {N} {a0} {b} := "
                        f"{prev}.append (by norm_num) r_{a}")
        body = "\n".join(thms) + "\n\n" + "\n".join(fold)
        with open(f'KernelCaseAnalysis/Gen/Validate{v:04}.lean', 'w') as f:
            f.write(f"""module

public import KernelCaseAnalysis.Gen.Dispatch

@[expose] public section

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[{a0}, {bend}). -/

namespace Noperthedron.Solution

set_option Elab.async false

{body}

/-- Rows `[{a0}, {bend})` are valid. -/
theorem rangeOk_{a0}_{bend} : RangeOk getRow {N} {a0} {bend} := s_{bend}

end Noperthedron.Solution

end
""")
    return spans

def gen_combine():
    types = read_node_types()
    spans = make_files(types, make_ranges(types))
    spans = [(rs[0][0], rs[-1][1]) for rs in spans]
    PER = 64
    ncomb = (len(spans) + PER - 1) // PER
    for m in range(ncomb):
        batch = spans[m*PER : (m+1)*PER]
        v0 = m * PER
        a0 = 0 if m == 0 else spans[0][0]
        start = spans[m*PER][0]
        imports = "\n".join(f"public import KernelCaseAnalysis.Gen.Validate{v0+i:04}" for i in range(len(batch)))
        prev = (f"public import KernelCaseAnalysis.Gen.Combine{m-1:02}\n" if m > 0 else "")
        steps = []
        if m == 0:
            steps.append(f"private theorem c_{batch[0][1]} : RangeOk getRow {N} 0 {batch[0][1]} := rangeOk_{batch[0][0]}_{batch[0][1]}")
            rest = batch[1:]
        else:
            steps.append(f"private theorem c_{batch[0][1]} : RangeOk getRow {N} 0 {batch[0][1]} :=\n"
                         f"  combined_{start}.append (by norm_num) rangeOk_{batch[0][0]}_{batch[0][1]}")
            rest = batch[1:]
        for (a, b) in rest:
            prev_end = steps[-1].split()[2].split('_')[1]
            steps.append(f"private theorem c_{b} : RangeOk getRow {N} 0 {b} :=\n"
                         f"  c_{prev_end}.append (by norm_num) rangeOk_{a}_{b}")
        endb = batch[-1][1]
        with open(f'KernelCaseAnalysis/Gen/Combine{m:02}.lean', 'w') as f:
            f.write(f"""module

{prev}{imports}

@[expose] public section

/-! GENERATED (scripts/gen_kernel_chunks.py): fold rows [0, {endb}). -/

namespace Noperthedron.Solution

{chr(10).join(steps)}

/-- Rows `[0, {endb})` are valid. -/
theorem combined_{endb} : RangeOk getRow {N} 0 {endb} := c_{endb}

end Noperthedron.Solution

end
""")
    with open('KernelCaseAnalysis/Gen/Final.lean', 'w') as f:
        f.write(f"""module

public import KernelCaseAnalysis.Gen.Combine{ncomb-1:02}

@[expose] public section

/-! GENERATED (scripts/gen_kernel_chunks.py): every index of the full table
satisfies `Row.ValidIxAt`, and row 0 carries `rowZero.interval`. -/

namespace Noperthedron.Solution

theorem allRows_validIxAt : ∀ i : Fin {N}, Row.ValidIxAt getRow {N} i :=
  validIxAt_of_rangeOk combined_{N}

theorem row0_interval : (getRow 0).interval = rowZero.interval := by
  decide +kernel

end Noperthedron.Solution

end
""")

def gen_root():
    # Everything in Gen/ is transitively reachable from ProofOfMainTheorem
    # (ProofOfMainTheorem -> ComputationalStep -> Gen.Final -> Combine* ->
    # Validate* -> Dispatch -> Load*), but CI's `lake exe mk_all --check`
    # requires the root to list every module of the library explicitly, in
    # mk_all's own format — emit exactly that.
    mods = []
    for dirpath, _, files in os.walk('KernelCaseAnalysis'):
        for fn in files:
            if fn.endswith('.lean'):
                rel = os.path.join(dirpath, fn)[:-len('.lean')]
                mods.append(rel.replace(os.sep, '.'))
    with open('KernelCaseAnalysis.lean', 'w') as f:
        f.write("module  -- shake: keep-all --deprecated_module: ignore\n\n")
        for m in sorted(mods):
            f.write(f"public import {m}\n")

phase = sys.argv[1] if len(sys.argv) > 1 else 'all'
only = int(sys.argv[2]) if len(sys.argv) > 2 else None
if phase in ('load', 'all'): gen_load(only)
if phase in ('dispatch', 'all'): gen_dispatch()
if phase in ('validate', 'all'): gen_validate(only)
if phase in ('combine', 'all'): gen_combine()
if phase in ('root', 'all'): gen_root()
print("generated phase:", phase, "only:", only)
