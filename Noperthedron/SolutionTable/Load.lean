module

public import Lean
public import Noperthedron.SolutionTable.Basic
public import Noperthedron.SolutionTable.Parse
-- Kernel-speed instances: `Load` is consumed only by the kernel pipeline
-- (the generated `KernelCaseAnalysis/Gen` files and `Smoke`), so `leafOk`
-- and everything downstream decide through the `Local2Nat` integer core.
-- The native pipeline imports `Assemble`/`Parse` directly and must NOT
-- acquire this import (see `KernelInstances.lean`).
public import Noperthedron.SolutionTable.KernelInstances
-- The `Load` namespace runs at the meta phase (Expr builders + `elab`
-- commands) and consumes these modules' types/functions there.
public meta import Lean
public meta import Noperthedron.SolutionTable.Basic
public meta import Noperthedron.SolutionTable.Parse

@[expose] public section


/-!
# Elaboration-time CSV ingestion for kernel-only checking

The kernel-only verification route (`KernelCaseAnalysis`) needs the
solution-table rows as Lean *term literals*: in-kernel `String` parsing is
hopeless (~9 s per 300 bytes), and generating literals as `.lean` source files
would push gigabytes through the parser and term elaborator.

This module takes a third route: parse the CSV **during elaboration**. The
`load_csv_rows` command reads the CSV with `IO`, parses a row range with the
existing (untrusted) `parseRowCsv`, builds kernel-friendly `Expr` literals for
the rows directly — no surface syntax, no term elaboration — and adds a single
chunk definition `csvRows_<a>_<b> : List Row` via `addDecl`.

The command only *loads*. Validation is stated separately, as ordinary source
theorems about the loaded definitions proved by `decide +kernel` (so the
kernel performs the whole evaluation — no `ofReduceBool`, no compiler):

* leaf checks, e.g. `csvRows_a_b.all Row.leafOk = true`;
* split checks, stated against whatever table view is in scope (see
  `KernelCaseAnalysis/Smoke.lean` for a small end-to-end demonstration);
* the range combinators and `ValidTable` constructor
  (`SolutionTable/Assemble.lean`).

Nothing here needs to be trusted: the parser and `Expr` builders can be
arbitrarily buggy and the kernel will still only accept true statements about
whatever rows were actually constructed. Faithfulness to the CSV is not part
of the trusted base for the same reason the runtime parser isn't — every
property the final proof needs is checked downstream, on the constructed rows.
-/

namespace Noperthedron.Solution

/-- Leaf-row validity as a `Bool`: global leaves (`nodeType = 1`) must satisfy
`Row.ValidGlobal`, local leaves (`nodeType = 2`) must satisfy `Row.ValidLocal`
or the second-order `Row.ValidLocal₂`, and other rows (structural splits,
checked against the full table elsewhere) pass vacuously. -/
def Row.leafOk (r : Row) : Bool :=
  if r.nodeType = 1 then decide r.ValidGlobal
  else if r.nodeType = 2 then decide r.ValidLocal || decide r.ValidLocal₂
  else true

namespace Load

open Lean Meta Elab

-- Everything in `Load` is elaboration-time machinery (Expr builders + `elab`
-- commands), so it must live at the meta phase under the module system.
meta section

/-- Cached `Expr`s that are shared by every row literal (types, instances, and
the two possible `sigma_Q` values), so per-row construction does no instance
synthesis. -/
structure Ctx where
  poseQ : Expr
  leInst : Expr
  /-- `fun x y : Pose ℚ => (inst : Decidable (x ≤ y))`, applied per interval. -/
  dle : Expr
  sigma0 : Expr
  sigma1 : Expr

def natE (n : ℕ) : Expr := mkRawNatLit n

def intE : ℤ → Expr
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (natE n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (natE n)

/-- A rational literal as `mkRat num den`. The kernel normalizes it with one
(GMP-fast) gcd on first use, memoized within each declaration. -/
def ratE (q : ℚ) : Expr := mkApp2 (mkConst ``mkRat) (intE q.num) (natE q.den)

def reflTrueE : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- `of_decide_eq_true (Eq.refl true) : prop` — the kernel certifies it by
reducing `decide prop` to `true`. -/
def decideProofE (prop inst : Expr) : Expr :=
  mkApp3 (mkConst ``of_decide_eq_true) prop inst reflTrueE

def finE (n v : ℕ) : Expr :=
  let nE := natE n
  let vE := natE v
  let prop := mkApp4 (mkConst ``LT.lt [Level.zero]) (mkConst ``Nat)
    (mkConst ``instLTNat) vE nE
  let inst := mkApp2 (mkConst ``Nat.decLt) vE nE
  mkApp3 (mkConst ``Fin.mk) nE vE (decideProofE prop inst)

def vertexIndexE (vi : VertexIndex) : Expr :=
  mkApp3 (mkConst ``VertexIndex.mk) (finE 15 vi.k) (finE 2 vi.ℓ) (finE 3 vi.i)

def poseE (p : Pose ℚ) : Expr :=
  mkApp6 (mkConst ``Pose.mk) (mkConst ``Rat)
    (ratE p.θ₁) (ratE p.θ₂) (ratE p.φ₁) (ratE p.φ₂) (ratE p.α)

def intervalE (ctx : Ctx) (iv : Interval) : Expr :=
  let pmin := poseE iv.min
  let pmax := poseE iv.max
  let toProd := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
    ctx.poseQ ctx.poseQ pmin pmax
  let prop := mkApp4 (mkConst ``LE.le [Level.zero]) ctx.poseQ ctx.leInst pmin pmax
  let inst := (mkApp2 ctx.dle pmin pmax).headBeta
  mkApp4 (mkConst ``NonemptyInterval.mk [Level.zero]) ctx.poseQ ctx.leInst
    toProd (decideProofE prop inst)

def rowE (ctx : Ctx) (r : Row) : Expr :=
  mkAppN (mkConst ``Row.mk) #[
    natE r.ID, natE r.nodeType, natE r.nrChildren, natE r.IDfirstChild,
    natE r.split,
    intervalE ctx r.interval,
    vertexIndexE r.S_index,
    intE r.wx_numerator, intE r.wy_numerator, natE r.w_denominator,
    vertexIndexE r.P1_index, vertexIndexE r.P2_index, vertexIndexE r.P3_index,
    vertexIndexE r.Q1_index, vertexIndexE r.Q2_index, vertexIndexE r.Q3_index,
    intE r.r',
    if r.sigma_Q.val = 0 then ctx.sigma0 else ctx.sigma1]

def elabSigma (n : ℕ) : TermElabM Expr := do
  let stx ← if n = 0 then `((⟨0, by decide⟩ : Finset.Icc (0:ℕ) 1))
            else `((⟨1, by decide⟩ : Finset.Icc (0:ℕ) 1))
  let e ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

def mkCtx : TermElabM Ctx := do
  let poseQ := mkApp (mkConst ``Pose) (mkConst ``Rat)
  let leInst ← synthInstance (mkApp (mkConst ``LE [Level.zero]) poseQ)
  let dle ← withLocalDeclD `x poseQ fun x => withLocalDeclD `y poseQ fun y => do
    let prop := mkApp4 (mkConst ``LE.le [Level.zero]) poseQ leInst x y
    let inst ← synthInstance (mkApp (mkConst ``Decidable) prop)
    mkLambdaFVars #[x, y] inst
  return { poseQ, leInst, dle, sigma0 := ← elabSigma 0, sigma1 := ← elabSigma 1 }

/-- Read and parse rows `[lo, hi)` of the CSV. -/
def readRows (path : String) (lo hi : ℕ) : Command.CommandElabM (Array Row) := do
  unless lo < hi do throwError "empty row range [{lo}, {hi})"
  let csv ← IO.FS.readFile path
  let lines := (csv.splitOn "\n").toArray
  let mut rows : Array Row := #[]
  for i in [lo:hi] do
    unless i + 1 < lines.size do
      throwError "row {i} out of range (file has {lines.size - 2} rows)"
    match parseRowCsv lines[i + 1]! with
    | .ok r =>
      unless r.ID = i do throwError "row ID mismatch at {i}: parsed ID {r.ID}"
      rows := rows.push r
    | .error e => throwError "parse error at row {i}: {e}"
  return rows

/-- Add `csvRows_<lo>_<hi> : List Row` for the given rows (literal `Expr`s,
`noncomputable`). -/
def addChunk (ctx : Ctx) (ns : Name) (lo hi : ℕ) (rows : Array Row) :
    TermElabM Unit := do
  let rowTy := mkConst ``Row
  let listE := rows.foldr
    (fun r acc => mkApp3 (mkConst ``List.cons [Level.zero]) rowTy (rowE ctx r) acc)
    (mkApp (mkConst ``List.nil [Level.zero]) rowTy)
  let chunkNm := ns ++ Name.mkSimple s!"csvRows_{lo}_{hi}"
  -- Exposed so that importing modules' `decide +kernel` can unfold the chunk
  -- (under the module system only exposed bodies reach an importer's kernel).
  withExporting <| addDecl <| .defnDecl {
    name := chunkNm, levelParams := [],
    type := mkApp (mkConst ``List [Level.zero]) rowTy, value := listE,
    hints := .abbrev, safety := .safe }
  -- No executable code (the kernel route never runs the chunk), so mark
  -- it noncomputable for clean downstream errors.
  modifyEnv (addNoncomputable · chunkNm)

/-- Add `csvRowsC_<lo>_<hi> : Fin 8 → Fin 8 → Fin 8 → Row` for the given
rows (`hi - lo ≤ 512 = 8³`; slots past the end repeat the last row — they
are never evaluated, since every checked index is guarded by `< size`).
Under the kernel an in-chunk access walks at most `3 × 7` `Fin.cons` cells
instead of an `O(offset)` `List` walk. -/
def addChunkCurried (ctx : Ctx) (ns : Name) (lo hi : ℕ) (rows : Array Row) :
    TermElabM Unit := do
  let rowTy := mkConst ``Row
  unless rows.size ≤ 512 ∧ 0 < rows.size do
    throwError "addChunkCurried: chunk size {rows.size} not in (0, 512]"
  let fin8Ty := mkApp (mkConst ``Fin) (natE 8)
  let vecConsE := mkConst ``Matrix.vecCons [Level.zero]
  let vecEmptyE := mkConst ``Matrix.vecEmpty [Level.zero]
  let vec8 : Expr → Array Expr → Expr := fun τ es => Id.run do
    let mut acc := mkApp vecEmptyE τ
    for idx in [0:8] do
      acc := mkApp4 vecConsE τ (natE idx) es[7 - idx]! acc
    return acc
  let pad := rowE ctx rows[rows.size - 1]!
  let mut level : Array Expr := #[]
  for j in [0:512] do
    level := level.push (if h : j < rows.size then rowE ctx rows[j] else pad)
  let mut τ := rowTy
  for _ in [0:3] do
    let mut next : Array Expr := #[]
    for g in [0:level.size / 8] do
      next := next.push (vec8 τ (level.extract (8 * g) (8 * g + 8)))
    level := next
    τ := mkForall `i .default fin8Ty τ
  let chunkNm := ns ++ Name.mkSimple s!"csvRowsC_{lo}_{hi}"
  -- Exposed so that importing modules' `decide +kernel` can unfold the chunk
  -- (under the module system only exposed bodies reach an importer's kernel).
  withExporting <| addDecl <| .defnDecl {
    name := chunkNm, levelParams := [],
    type := τ, value := level[0]!,
    hints := .abbrev, safety := .safe }
  modifyEnv (addNoncomputable · chunkNm)

/-- `load_csv_rows "path.csv" from a to b` reads rows `[a, b)` of the
solution-tree CSV and adds them to the environment as one literal definition
`csvRows_<a>_<b> : List Row`. Loading only — validate the chunk with ordinary
theorems (`by decide +kernel`) about it.

The chunk gets no executable code and is marked `noncomputable`
(the kernel route never runs it; the native route parses at runtime).

Kept alongside `load_csv_chunks_curried` for small probes: the curried
loader pads every chunk to 512 rows, so a 5-row kernel probe through it
would pay ~100× the reduction cost of a 5-row `List` literal. -/
elab "load_csv_rows " path:str " from " a:num " to " b:num : command => do
  let lo := a.getNat
  let hi := b.getNat
  let t0 ← IO.monoMsNow
  let rows ← readRows path.getString lo hi
  let tParse ← IO.monoMsNow
  let ns ← getCurrNamespace
  Command.liftTermElabM do
    let ctx ← mkCtx
    addChunk ctx ns lo hi rows
    let tDefs ← IO.monoMsNow
    logInfo m!"load_csv_rows [{lo}, {hi}): read+parse {tParse - t0} ms, \
      define+check {tDefs - tParse} ms"

/-- `load_csv_chunks_curried "path.csv" from a to b chunkSize 512` reads rows
`[a, b)` in one pass and adds one curried `Fin 8 → Fin 8 → Fin 8 → Row`
literal `csvRowsC_<x>_<min (x+512) b>` per 512-aligned sub-range (`a` should
be a multiple of 512 so the names line up with the global chunk grid of
`assemble_row_dispatch_curried`), for the `O(log)` getter (`rowGetterC`).
`chunkSize` must be 512. -/
elab "load_csv_chunks_curried " path:str " from " a:num " to " b:num
    " chunkSize " c:num : command => do
  let lo := a.getNat
  let hi := b.getNat
  let cs := c.getNat
  unless cs = 512 do throwError "chunkSize must be 512 (= 8³)"
  let t0 ← IO.monoMsNow
  let rows ← readRows path.getString lo hi
  let tParse ← IO.monoMsNow
  let ns ← getCurrNamespace
  Command.liftTermElabM do
    let ctx ← mkCtx
    let mut x := lo
    while x < hi do
      let y := min (x + cs) hi
      addChunkCurried ctx ns x y (rows.extract (x - lo) (y - lo))
      x := y
    let tDefs ← IO.monoMsNow
    logInfo m!"load_csv_chunks_curried [{lo}, {hi}) by {cs}: read+parse \
      {tParse - t0} ms, define+check {tDefs - tParse} ms"

/-- `assemble_row_dispatch_curried d rows N chunkSize 512` defines

    d : Fin 8 → Fin 8 → Fin 8 → Fin 8 → (Fin 8 → Fin 8 → Fin 8 → Row)

as a digit-curried literal dispatching chunk index `k = i / 512` (base-8
digits, big-endian) to the loaded curried chunk constants
`csvRowsC_{k*512}_{min ((k+1)*512) N}`, which must already be in the
environment. Feed it to `rowGetterC d` (see `SolutionTable/Assemble.lean`):
a kernel access walks ≤ 7 `Fin`-digit levels — `O(log)`. Slots beyond
`⌈N/512⌉` repeat the last chunk (never evaluated: every checked index is
guarded by `< size`). Like `load_csv_rows`, the definition is
`noncomputable`. -/
elab "assemble_row_dispatch_curried " name:ident " rows " n:num
    " chunkSize " c:num : command => do
  let N := n.getNat
  let C := c.getNat
  unless C = 512 do throwError "chunkSize must be 512 (= 8³)"
  unless 0 < N do throwError "rows must be positive"
  let slots := (N + C - 1) / C
  unless slots ≤ 4096 do throwError "too many chunks: {slots} > 4096"
  let ns ← getCurrNamespace
  Command.liftTermElabM do
    let rowTy := mkConst ``Row
    let fin8Ty := mkApp (mkConst ``Fin) (natE 8)
    let chunkTy := mkForall `i .default fin8Ty (mkForall `i .default fin8Ty
      (mkForall `i .default fin8Ty rowTy))
    let vecConsE := mkConst ``Matrix.vecCons [Level.zero]
    let vecEmptyE := mkConst ``Matrix.vecEmpty [Level.zero]
    let vec8 : Expr → Array Expr → Expr := fun τ es => Id.run do
      let mut acc := mkApp vecEmptyE τ
      for idx in [0:8] do
        acc := mkApp4 vecConsE τ (natE idx) es[7 - idx]! acc
      return acc
    let lastNm := ns ++ Name.mkSimple
      s!"csvRowsC_{(slots - 1) * C}_{min (slots * C) N}"
    let mut level : Array Expr := #[]
    for k in [0:4096] do
      if k < slots then
        let cn := ns ++ Name.mkSimple s!"csvRowsC_{k * C}_{min ((k + 1) * C) N}"
        unless (← getEnv).contains cn do
          throwError "missing chunk constant {cn} (load it first)"
        level := level.push (mkConst cn)
      else
        level := level.push (mkConst lastNm)
    let mut τ := chunkTy
    for _ in [0:4] do
      let mut next : Array Expr := #[]
      for g in [0:level.size / 8] do
        next := next.push (vec8 τ (level.extract (8 * g) (8 * g + 8)))
      level := next
      τ := mkForall `i .default fin8Ty τ
    let dName := ns ++ name.getId
    -- Exposed so that importing modules' `decide +kernel` can unfold it
    -- (under the module system only exposed bodies reach an importer's kernel).
    withExporting <| addDecl <| .defnDecl {
      name := dName, levelParams := [], type := τ,
      value := level[0]!, hints := .abbrev, safety := .safe }
    modifyEnv (addNoncomputable · dName)

end -- meta section
end Load

end Noperthedron.Solution

end
