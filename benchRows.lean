import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.Parse

/-! Timing harness for the *live* per-row checks: the production `Decidable`
instances (`Row.ValidGlobal` / `Row.ValidLocal` / `Row.ValidSplitAt`, i.e.
the `fastNatGlobal` / `BεℚPy.fastNat` paths with their ℚ fallbacks), each
tier of the local `Bεℚ` chain in isolation, the ℚ fallbacks the fast paths
would take on rejection, and per-conjunct attribution for local rows.

Samples the row kinds directly from the full solution table:

    lake exe benchRows solution_tree_v6.csv [nGlobal nLocal nSplit]

(defaults 2000 / 300 / 2000; the CSV parse itself takes a few seconds).

These are compiled-code numbers; kernel (`decide +kernel`) costs are very
different — see `KernelCaseAnalysis` and the cost model in
`scripts/gen_kernel_chunks.py`.
-/

open Noperthedron Noperthedron.Solution
open scoped Matrix

def bench (label : String) (rows : Array Row) (f : Row → Bool) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut acc := 0
  for r in rows do
    if f r then acc := acc + 1
  let t1 ← IO.monoNanosNow
  let dt := t1 - t0
  IO.println s!"{label}: rows={rows.size} pass={acc} \
    total={dt / 1000000}ms per-row={dt / rows.size.max 1 / 1000}us"

/-- Deterministic stride sample of the rows with the given `nodeType`. -/
def sample (table : Table) (ty n : ℕ) : Array Row := Id.run do
  let all := table.filter (·.nodeType = ty)
  if all.size ≤ n then return all
  let stride := all.size / n
  let mut out := #[]
  let mut i := 0
  while i < all.size ∧ out.size < n do
    out := out.push all[i]!
    i := i + stride
  return out

/-- Just the ten per-pose ℚ trig partial sums — the per-pose cost floor of
the ℚ fallback checkers. (The `fastNat` paths use the integer Horner cores
instead, so they can come in *below* this.) -/
def trigSum (r : Row) : Bool :=
  let p := r.interval.centerPose
  decide (0 ≤ RationalApprox.sinℚ p.θ₁ + RationalApprox.cosℚ p.θ₁
            + RationalApprox.sinℚ p.φ₁ + RationalApprox.cosℚ p.φ₁
            + RationalApprox.sinℚ p.α + RationalApprox.cosℚ p.α
            + RationalApprox.sinℚ p.θ₂ + RationalApprox.cosℚ p.θ₂
            + RationalApprox.sinℚ p.φ₂ + RationalApprox.cosℚ p.φ₂)

def main (args : List String) : IO Unit := do
  let csvPath := args[0]?.getD "solution_tree_v6.csv"
  let nG := (args[1]?.bind (·.toNat?)).getD 2000
  let nL := (args[2]?.bind (·.toNat?)).getD 300
  let nS := (args[3]?.bind (·.toNat?)).getD 2000
  let csv ← IO.FS.readFile csvPath
  let table ← match parseSolutionTablePar csv 64 with
    | .ok t => pure t
    | .error e => throw (IO.userError s!"parse error: {e}")
  let g := sample table 1 nG
  let l := sample table 2 nL
  let s := sample table 3 nS
  IO.println s!"table {table.size} rows; sampled \
    {g.size} global / {l.size} local / {s.size} split"
  let getRow := fun j => table[j]!
  -- the production paths (what constructValidTable / native_decide run)
  bench "global: ValidGlobal (live) " g (fun r => decide r.ValidGlobal)
  bench "global: fastNat core       " g (·.fastNatGlobal)
  bench "global: ℚ fallback G>maxH  " g (fun r =>
    RationalApprox.GlobalTheorem.Gℚ_gt_maxHℚ_check r.interval.centerPose
      r.εα r.εθ₁ r.εφ₁ r.εθ₂ r.εφ₂ r.S pythonPolyQ r.w)
  bench "global: trig only          " g trigSum
  bench "local:  ValidLocal (live)  " l (fun r => decide r.ValidLocal)
  -- the three tiers of the Bεℚ chain (live = fastNat; the others are the
  -- fallbacks a rejected row would walk through)
  bench "local:  Bεℚ fastNat        " l (fun r =>
    BεℚPy.fastNat r.Qi r.interval.centerPose r.epsilon r.δ r.r)
  bench "local:  Bεℚ checkN (ℤ)     " l (fun r =>
    BεℚPy.checkN r.Qi r.interval.centerPose r.epsilon r.δ r.r)
  bench "local:  Bεℚ check (ℚ)      " l (fun r =>
    BεℚPy.check r.Qi r.interval.centerPose r.epsilon r.δ r.r)
  -- per-conjunct attribution for the ℚ side of ValidLocal
  bench "local:  Row.delta          " l (fun r => decide (0 ≤ r.δ))
  bench "local:  symmetry           " l (fun r =>
    decide (∃ sy : TriangleSymmetry, sy.applicable r.Qi ∧ ∀ i, r.Pi i = sy.apply (r.Qi i)))
  bench "local:  X1 inner           " l (fun r =>
    decide (Local.TriangleQ.Aεℚσ r.X₁ (pythonVertexA ∘ r.Pi) r.epsilon 0
      RationalApprox.sqrtApprox16))
  bench "local:  X2 inner           " l (fun r =>
    decide (Local.TriangleQ.Aεℚσ r.X₂ (pythonVertexA ∘ r.Qi) r.epsilon r.sigma_Q.val
      RationalApprox.sqrtApprox16))
  bench "local:  P spanning         " l (fun r =>
    decide (Spanningℚ r.θ₁ r.φ₁ r.epsilon (pythonVertexA ∘ r.Pi)))
  bench "local:  Q spanning         " l (fun r =>
    decide (Spanningℚ r.θ₂ r.φ₂ r.epsilon (pythonVertexA ∘ r.Qi)))
  bench "local:  r_valid            " l (fun r =>
    decide (RationalApprox.LocalTheorem.BoundRℚ r.r r.epsilon r.interval.centerPose
      (pythonVertexA ∘ r.Qi) RationalApprox.sqrtApprox16))
  bench "local:  trig only          " l trigSum
  bench "split:  ValidSplitAt (live)" s (fun r =>
    decide (r.ValidSplitAt getRow table.size))
