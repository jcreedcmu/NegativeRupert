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

end Noperthedron.Solution

end
