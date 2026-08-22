module

public import Noperthedron.SolutionTable.Assemble
public import Noperthedron.Checker.Local2Nat

@[expose] public section

/-!
# Kernel-speed `Decidable` instances for the row-validity chain

The `Local2Nat` integer core makes `decide +kernel` of a second-order local
row ~15× faster (64.5s → ~4.3s), but pulling it into the *native* checker's
call graph is a disaster of a different kind: `native_decide` compiles its
whole call graph in-process on every invocation, and the `Local2Nat`
literal tables (34k-case `sqrtDvCurriedN` etc.) push that fixed cost to
~10 minutes.  `SolutionTable/Basic` therefore deliberately does **not**
import `Local2Nat` — the shared/native instance chain stays on the compiled
ℚ checkers — and this module re-derives the validity chain with the
`Local2Nat` instances in scope, at a priority that beats the `Basic` /
`Assemble` instances.

Import this module (it is reached via `SolutionTable/Load`) only from the
kernel pipeline: the generated `KernelCaseAnalysis/Gen` files and `Smoke`.
`NativeCaseAnalysis` must keep importing `Assemble`/`Parse` only.
-/

namespace Noperthedron.Solution

/-- `Row.ValidAt`, re-derived so the `Row.ValidLocal₂` disjunct routes
through the `Local2Nat` integer instances. -/
instance (priority := 10600) (get : ℕ → Row) (size : ℕ) (row : Row) :
    Decidable (Row.ValidAt get size row) :=
  decidable_of_iff _ (Row.validAt_iff get size row).symm

/-- `Row.ValidIxAt` on top of the kernel-speed `Row.ValidAt` instance. -/
instance (priority := 10600) (get : ℕ → Row) (size i : ℕ) :
    Decidable (Row.ValidIxAt get size i) :=
  decidable_of_iff ((get i).ID = i ∧ (get i).ValidAt get size ∧ i < size)
    (by unfold Row.ValidIxAt; exact Iff.rfl)

/-- `RangeOk` on top of the kernel-speed `Row.ValidIxAt` instance. -/
instance (priority := 10600) (get : ℕ → Row) (size a b : ℕ) :
    Decidable (RangeOk get size a b) :=
  decidable_of_iff
    (∀ j : Fin (b - a), a + j.val < size → Row.ValidIxAt get size (a + j.val))
    (by unfold RangeOk; exact Iff.rfl)

/-!
## The parallel check chain, re-elaborated with these instances

`constructValidTable` is compiled ahead of time, so the call-graph size
that rules `Local2Nat` out of `native_decide` costs it nothing — and the
integer core is ~5× faster per second-order local row than the compiled ℚ
route (7.4ms vs 38ms).  These are verbatim copies of the `Assemble`
definitions, elaborated here so the baked `decide`s route through the
kernel-speed instances, with proofs that they equal the originals
(`decide` is instance-irrelevant), so `validIxAt_of_rowsValidIxAtParB`
carries over.
-/

/-- `validIxAtB` with the kernel-speed instances baked in. -/
def validIxAtBK (get : ℕ → Row) (size i : ℕ) : Bool :=
  if i < size then decide (Row.ValidIxAt get size i) else true

theorem validIxAtBK_eq (get : ℕ → Row) (size i : ℕ) :
    validIxAtBK get size i = validIxAtB get size i := by
  unfold validIxAtBK validIxAtB
  split
  · exact decide_eq_decide.mpr Iff.rfl
  · rfl

/-- `chunkValidIxAtB` over `validIxAtBK`. -/
def chunkValidIxAtBK (get : ℕ → Row) (size start cnt : ℕ) : Bool :=
  Fin.foldl cnt (init := true) fun acc j => acc && validIxAtBK get size (start + j.val)

theorem chunkValidIxAtBK_eq (get : ℕ → Row) (size start cnt : ℕ) :
    chunkValidIxAtBK get size start cnt = chunkValidIxAtB get size start cnt := by
  unfold chunkValidIxAtBK chunkValidIxAtB
  congr 1
  funext acc j
  rw [validIxAtBK_eq]

/-- `rowsValidIxAtChunkedB` over `chunkValidIxAtBK`. -/
def rowsValidIxAtChunkedBK (get : ℕ → Row) (size nTasks chunkSize : ℕ) : Bool :=
  decide (size ≤ nTasks * chunkSize) &&
    (((List.range nTasks).map fun t =>
        Task.spawn fun _ => chunkValidIxAtBK get size (t * chunkSize) chunkSize).all Task.get)

theorem rowsValidIxAtChunkedBK_eq (get : ℕ → Row) (size nTasks chunkSize : ℕ) :
    rowsValidIxAtChunkedBK get size nTasks chunkSize =
      rowsValidIxAtChunkedB get size nTasks chunkSize := by
  unfold rowsValidIxAtChunkedBK rowsValidIxAtChunkedB
  congr 3
  funext t
  congr 1
  funext _
  rw [chunkValidIxAtBK_eq]

/-- `rowsValidIxAtParB` with the kernel-speed instances baked in. -/
def rowsValidIxAtParBK (get : ℕ → Row) (size nTasks : ℕ) : Bool :=
  rowsValidIxAtChunkedBK get size nTasks (size / nTasks + 1)

theorem validIxAt_of_rowsValidIxAtParBK {get : ℕ → Row} {size nTasks : ℕ}
    (h : rowsValidIxAtParBK get size nTasks = true) :
    ∀ i : Fin size, Row.ValidIxAt get size i := by
  apply validIxAt_of_rowsValidIxAtParB (nTasks := nTasks)
  unfold rowsValidIxAtParB
  unfold rowsValidIxAtParBK at h
  rwa [rowsValidIxAtChunkedBK_eq] at h

end Noperthedron.Solution

end
