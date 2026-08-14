import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.Parse

/-! Timing harness: per-row cost of the global vs local leaf checks,
with rough attribution (trig evaluation, `Row.δ`). Run:
  lake exe benchRows sample_global.csv sample_local.csv
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
  IO.println s!"{label}: rows={rows.size} pass={acc} total={dt/1000000}ms per-row={dt/rows.size.max 1/1000}us"

def trigSum (r : Row) : Bool :=
  let p := r.interval.centerPose
  decide (0 ≤ RationalApprox.sinℚ p.θ₁ + RationalApprox.cosℚ p.θ₁
            + RationalApprox.sinℚ p.φ₁ + RationalApprox.cosℚ p.φ₁
            + RationalApprox.sinℚ p.α + RationalApprox.cosℚ p.α
            + RationalApprox.sinℚ p.θ₂ + RationalApprox.cosℚ p.θ₂
            + RationalApprox.sinℚ p.φ₂ + RationalApprox.cosℚ p.φ₂)

def main (args : List String) : IO Unit := do
  let gcsv ← IO.FS.readFile args[0]!
  let lcsv ← IO.FS.readFile args[1]!
  let gtable ← match parseSolutionTable gcsv with
    | .ok t => pure t | .error e => throw (IO.userError e)
  let ltable ← match parseSolutionTable lcsv with
    | .ok t => pure t | .error e => throw (IO.userError e)
  IO.println s!"parsed {gtable.size} global rows, {ltable.size} local rows"
  bench "global: ValidGlobal " gtable (fun r => decide r.ValidGlobal)
  bench "global: trig only   " gtable trigSum
  bench "local:  ValidLocal  " ltable (fun r => decide r.ValidLocal)
  bench "local:  trig only   " ltable trigSum
  bench "local:  Row.delta   " ltable (fun r => decide (0 ≤ r.δ))
  bench "local:  B-eps check " ltable (fun r =>
    Local.TriangleQ.Bεℚ.check r.Qi pythonVertex
      r.interval.centerPose r.epsilon r.δ r.r RationalApprox.sqrtApprox)
  bench "local:  B-eps checkPy" ltable (fun r =>
    BεℚPy.check r.Qi r.interval.centerPose r.epsilon r.δ r.r)
  bench "local:  vertex walk " ltable (fun _r =>
    -- cost of just enumerating VertexIndex and reading pythonVertex coords
    decide (∀ k : VertexIndex, pythonVertex k 0 + pythonVertex k 1 + pythonVertex k 2 < 4))
  bench "local:  270 sqrt(dv)" ltable (fun r =>
    -- pose-independent pair norms: 3 x 90 upper_sqrt.norm calls on den ~10^32 inputs
    (List.finRange 3).all fun i =>
      decide (∀ k : VertexIndex,
        RationalApprox.sqrtApprox.upper_sqrt.norm (pythonVertex (r.Qi i) - pythonVertex k) < 4))
  bench "local:  symmetry    " ltable (fun r =>
    decide (∃ s : TriangleSymmetry, s.applicable r.Qi ∧ ∀ i, r.Pi i = s.apply (r.Qi i)))
  bench "local:  X1 inner    " ltable (fun r =>
    decide (Local.TriangleQ.Aεℚσ r.X₁ (pythonVertexA ∘ r.Pi) r.epsilon 0
      RationalApprox.sqrtApprox))
  bench "local:  X2 inner    " ltable (fun r =>
    decide (Local.TriangleQ.Aεℚσ r.X₂ (pythonVertexA ∘ r.Qi) r.epsilon r.sigma_Q.val
      RationalApprox.sqrtApprox))
  bench "local:  P spanning  " ltable (fun r =>
    decide (Spanningℚ r.θ₁ r.φ₁ r.epsilon (pythonVertexA ∘ r.Pi)))
  bench "local:  Q spanning  " ltable (fun r =>
    decide (Spanningℚ r.θ₂ r.φ₂ r.epsilon (pythonVertexA ∘ r.Qi)))
  bench "local:  r_valid     " ltable (fun r =>
    decide (RationalApprox.LocalTheorem.BoundRℚ r.r r.epsilon r.interval.centerPose
      (pythonVertexA ∘ r.Qi) RationalApprox.sqrtApprox))
  bench "local:  center/eps  " ltable (fun r =>
    decide (r.interval.centerPose ∈ fourInterval ℚ ∧ 0 < r.epsilon))
