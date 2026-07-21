module

public import Mathlib.Tactic

@[expose] public section

/-!
# Kernel-specified parallel Boolean loops

`Task.spawn` is definitionally a pure computation, so native executables and
`native_decide` may evaluate independent Boolean chunks concurrently while a
small kernel proof recovers the corresponding pointwise statement.
-/

namespace Noperthedron.ParallelBool

private theorem foldlAndFactor {n : ℕ} (p : Fin n → Bool) (init : Bool) :
    Fin.foldl n (fun acc i => acc && p i) init =
      (init && Fin.foldl n (fun acc i => acc && p i) true) := by
  induction n generalizing init with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ, Fin.foldl_succ,
      ih (fun i => p i.succ) (init && p 0),
      ih (fun i => p i.succ) (true && p 0)]
    simp [Bool.and_assoc]

private theorem foldlAndEqTrueIff {n : ℕ} (p : Fin n → Bool) :
    Fin.foldl n (fun acc i => acc && p i) true = true ↔
      ∀ i, p i = true := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ, foldlAndFactor]
    simp only [Bool.true_and, Bool.and_eq_true]
    rw [ih (fun i => p i.succ), Fin.forall_fin_succ]

private theorem taskGetSpawn {α : Type} (fn : Unit → α)
    (priority : Task.Priority) :
    (Task.spawn fn priority).get = fn () := rfl

/-- Evaluate `predicate` on `[start, start + count)` in a flat loop. -/
def chunkB (predicate : ℕ → Bool) (start count : ℕ) : Bool :=
  Fin.foldl count (init := true) fun acc j =>
    acc && predicate (start + j.val)

theorem chunkB_eq_true_iff (predicate : ℕ → Bool) (start count : ℕ) :
    chunkB predicate start count = true ↔
      ∀ k, start ≤ k → k < start + count → predicate k = true := by
  unfold chunkB
  rw [foldlAndEqTrueIff (fun j => predicate (start + j.val))]
  constructor
  · intro h k hk1 hk2
    have hk := h ⟨k - start, by omega⟩
    rwa [Nat.add_sub_cancel' hk1] at hk
  · intro h j
    exact h (start + j.val) (Nat.le_add_right _ _) (by
      have := j.isLt
      omega)

/-- Split `[0, size)` into `taskCount` independent chunks.  The leading guard
proves that the requested chunks cover every index. -/
def allChunkedB (predicate : ℕ → Bool)
    (size taskCount chunkSize : ℕ) : Bool :=
  decide (size ≤ taskCount * chunkSize) &&
    (((List.range taskCount).map fun task =>
      Task.spawn fun _ => chunkB predicate (task * chunkSize) chunkSize).all
        Task.get)

/-- The tasks used by `allChunkedB`, exposed for progress-reporting native
executables. -/
def chunkTasks (predicate : ℕ → Bool) (taskCount chunkSize : ℕ) :
    List (Task Bool) :=
  (List.range taskCount).map fun task =>
    Task.spawn fun _ => chunkB predicate (task * chunkSize) chunkSize

/-- `allChunkedB` with an already spawned task list. -/
def allWithTasksB (size taskCount chunkSize : ℕ)
    (tasks : List (Task Bool)) : Bool :=
  decide (size ≤ taskCount * chunkSize) && tasks.all Task.get

theorem all_of_chunkedB {predicate : ℕ → Bool}
    {size taskCount chunkSize : ℕ}
    (h : allChunkedB predicate size taskCount chunkSize = true) :
    ∀ i, i < size → predicate i = true := by
  unfold allChunkedB at h
  rw [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true] at h
  obtain ⟨hsize, hall⟩ := h
  intro i hi
  have hchunkPos : 0 < chunkSize := by
    rcases Nat.eq_zero_or_pos chunkSize with hzero | hpos
    · subst hzero
      omega
    · exact hpos
  have htask : i / chunkSize < taskCount :=
    (Nat.div_lt_iff_lt_mul hchunkPos).mpr (lt_of_lt_of_le hi hsize)
  have hchunk : chunkB predicate (i / chunkSize * chunkSize) chunkSize = true := by
    have hmember := hall _ (List.mem_map.mpr
      ⟨i / chunkSize, List.mem_range.mpr htask, rfl⟩)
    rwa [taskGetSpawn] at hmember
  rw [chunkB_eq_true_iff] at hchunk
  have hdivision := Nat.div_add_mod i chunkSize
  have hmod := Nat.mod_lt i hchunkPos
  rw [Nat.mul_comm] at hdivision
  exact hchunk i (by omega) (by omega)

theorem all_of_withTasksB {predicate : ℕ → Bool}
    {size taskCount chunkSize : ℕ}
    (h : allWithTasksB size taskCount chunkSize
      (chunkTasks predicate taskCount chunkSize) = true) :
    ∀ i, i < size → predicate i = true := by
  apply all_of_chunkedB
  exact h

/-- Near-equal chunks suitable for native task scheduling. -/
def allParB (predicate : ℕ → Bool) (size taskCount : ℕ) : Bool :=
  allChunkedB predicate size taskCount (size / taskCount + 1)

theorem all_of_parB {predicate : ℕ → Bool} {size taskCount : ℕ}
    (h : allParB predicate size taskCount = true) :
    ∀ i, i < size → predicate i = true :=
  all_of_chunkedB h

end Noperthedron.ParallelBool

end
