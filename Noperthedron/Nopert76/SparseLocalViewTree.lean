module

public import Noperthedron.Nopert76.AtlasProjectiveLocalViewTree
public import Noperthedron.Nopert76.GeneratedTangentCones

@[expose] public section

/-!
# Sparse validation for projective local-view trees

The semantic tree and its final theorem remain unchanged.  This module only
provides a cheaper decidable predicate for generated certificate rows.  A
proof of the sparse predicate is converted to the original `Table.Valid`
hypothesis using the exact tangent-cone certificates.
-/

namespace Noperthedron.Nopert76.SparseLocalViewTree

open AtlasProjectiveLocalViewTree
open SparseSupport

def SparseRowValidAt (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size : ℕ) : Row → Prop
  | .split id children root triangle => ∀ child,
      id < children child ∧ children child < size ∧
      (get (children child)).root = root ∧
      (get (children child)).triangle =
        Noperthedron.SnubCube.ProjectiveView.split triangle child
  | .certificate _ box =>
      box.symmetryIndex = symmetryIndex ∧ r ≤ box.r ∧
        SparseSupport.Box.SparseViewValid box

instance (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row)
    (size : ℕ) (row : Row) :
    Decidable (SparseRowValidAt symmetryIndex r get size row) := by
  cases row <;> simp only [SparseRowValidAt] <;> infer_instance

def SparseRowsValidAt (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size : ℕ) : Prop :=
  ∀ i : Fin size,
    (get i).id = i ∧ SparseRowValidAt symmetryIndex r get size (get i)

instance (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row)
    (size : ℕ) : Decidable (SparseRowsValidAt symmetryIndex r get size) := by
  unfold SparseRowsValidAt
  infer_instance

def SparseRowsValidRangeAt (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size start count : ℕ) : Prop :=
  start + count ≤ size ∧ ∀ j : Fin count,
    (get (start + j.val)).id = start + j.val ∧
      SparseRowValidAt symmetryIndex r get size (get (start + j.val))

instance (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row)
    (size start count : ℕ) :
    Decidable (SparseRowsValidRangeAt symmetryIndex r get size start count) := by
  unfold SparseRowsValidRangeAt
  infer_instance

theorem sparseRowsValidRange_append {symmetryIndex : OrbitIndex} {r : ℚ}
    {get : ℕ → Row} {size start left right : ℕ}
    (hleft : SparseRowsValidRangeAt symmetryIndex r get size start left)
    (hright : SparseRowsValidRangeAt symmetryIndex r get size
      (start + left) right) :
    SparseRowsValidRangeAt symmetryIndex r get size start (left + right) := by
  unfold SparseRowsValidRangeAt at hleft hright ⊢
  constructor
  · omega
  · intro j
    by_cases hmid : j.val < left
    · simpa using hleft.2 ⟨j.val, hmid⟩
    · have hjright : j.val - left < right := by omega
      have hr := hright.2 ⟨j.val - left, hjright⟩
      have hi : start + left + (j.val - left) = start + j.val := by omega
      simpa [hi] using hr

theorem sparseRowsValidAt_of_range {symmetryIndex : OrbitIndex} {r : ℚ}
    {get : ℕ → Row} {size : ℕ}
    (h : SparseRowsValidRangeAt symmetryIndex r get size 0 size) :
    SparseRowsValidAt symmetryIndex r get size := by
  intro i
  simpa using h.2 ⟨i.val, i.isLt⟩

theorem Row.ValidAt.of_sparse {symmetryIndex : OrbitIndex} {r : ℚ}
    {get : ℕ → Row} {size : ℕ} {row : Row}
    (h : SparseRowValidAt symmetryIndex r get size row) :
    row.ValidAt symmetryIndex r get size := by
  cases row with
  | split => exact h
  | certificate id box =>
      exact ⟨h.1, h.2.1,
        SparseSupport.Box.SparseViewValid.toViewValid h.2.2
          GeneratedTangentCones.table
          GeneratedTangentCones.table_valid_kernel⟩

theorem rowsValidAt_of_sparse {symmetryIndex : OrbitIndex} {r : ℚ}
    {get : ℕ → Row} {size : ℕ}
    (h : SparseRowsValidAt symmetryIndex r get size) :
    RowsValidAt symmetryIndex r get size := by
  intro i
  exact ⟨(h i).1, Row.ValidAt.of_sparse (h i).2⟩

def SparseTableValid (table : Table) : Prop :=
  0 < table.size ∧
    SparseRowsValidAt table.symmetryIndex table.r table.get table.size ∧
    (table.get 0).root = table.root ∧
    (table.get 0).triangle = table.triangle

instance (table : Table) : Decidable (SparseTableValid table) := by
  unfold SparseTableValid
  infer_instance

theorem Table.Valid.of_sparse {table : Table} (h : SparseTableValid table) :
    table.Valid :=
  ⟨h.1, rowsValidAt_of_sparse h.2.1, h.2.2.1, h.2.2.2⟩

/-! ## Parallel executable checker

`native_decide` and standalone executables can evaluate this Boolean checker
with ordinary native worker threads.  `Task.spawn` is definitionally a pure
computation, so the proof below reduces the parallel implementation to the
same sparse row predicate used above.
-/

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

/-- The sparse validity predicate at an index, vacuously true past `size`. -/
def sparseValidIxAtB (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size i : ℕ) : Bool :=
  if i < size then
    decide ((get i).id = i ∧
      SparseRowValidAt symmetryIndex r get size (get i))
  else true

theorem sparseValidIxAtB_eq_true_iff (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size i : ℕ) :
    sparseValidIxAtB symmetryIndex r get size i = true ↔
      (i < size → (get i).id = i ∧
        SparseRowValidAt symmetryIndex r get size (get i)) := by
  unfold sparseValidIxAtB
  split
  · rename_i h
    rw [decide_eq_true_iff]
    exact ⟨fun hv _ => hv, fun hv => hv h⟩
  · rename_i h
    simp only [true_iff]
    exact fun h' => absurd h' h

/-- Check a contiguous index range using a flat native loop. -/
def sparseChunkValidB (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size start count : ℕ) : Bool :=
  Fin.foldl count (init := true) fun acc j =>
    acc && sparseValidIxAtB symmetryIndex r get size (start + j.val)

private theorem sparseChunkValidB_eq_true_iff
    (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row)
    (size start count : ℕ) :
    sparseChunkValidB symmetryIndex r get size start count = true ↔
      ∀ k, start ≤ k → k < start + count →
        sparseValidIxAtB symmetryIndex r get size k = true := by
  unfold sparseChunkValidB
  rw [foldlAndEqTrueIff (fun j =>
    sparseValidIxAtB symmetryIndex r get size (start + j.val))]
  constructor
  · intro h k hk1 hk2
    have hk := h ⟨k - start, by omega⟩
    rwa [Nat.add_sub_cancel' hk1] at hk
  · intro h j
    exact h (start + j.val) (Nat.le_add_right _ _) (by
      have := j.isLt
      omega)

/-- Check all sparse rows in independent native tasks.  The coverage guard
makes this sound for arbitrary task and chunk counts. -/
def sparseRowsValidAtChunkedB (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size taskCount chunkSize : ℕ) : Bool :=
  decide (size ≤ taskCount * chunkSize) &&
    (((List.range taskCount).map fun task =>
      Task.spawn fun _ => sparseChunkValidB symmetryIndex r get size
        (task * chunkSize) chunkSize).all Task.get)

theorem sparseRowsValidAt_of_chunkedB {symmetryIndex : OrbitIndex} {r : ℚ}
    {get : ℕ → Row} {size taskCount chunkSize : ℕ}
    (h : sparseRowsValidAtChunkedB symmetryIndex r get size
      taskCount chunkSize = true) :
    SparseRowsValidAt symmetryIndex r get size := by
  unfold sparseRowsValidAtChunkedB at h
  rw [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true] at h
  obtain ⟨hsize, hall⟩ := h
  intro i
  have hchunkPos : 0 < chunkSize := by
    rcases Nat.eq_zero_or_pos chunkSize with hzero | hpos
    · subst hzero
      have := i.isLt
      omega
    · exact hpos
  have htask : (i : ℕ) / chunkSize < taskCount :=
    (Nat.div_lt_iff_lt_mul hchunkPos).mpr
      (lt_of_lt_of_le i.isLt hsize)
  have hchunk : sparseChunkValidB symmetryIndex r get size
      ((i : ℕ) / chunkSize * chunkSize) chunkSize = true := by
    have hmember := hall _ (List.mem_map.mpr
      ⟨(i : ℕ) / chunkSize, List.mem_range.mpr htask, rfl⟩)
    rwa [taskGetSpawn] at hmember
  rw [sparseChunkValidB_eq_true_iff] at hchunk
  have hindex : sparseValidIxAtB symmetryIndex r get size (i : ℕ) = true := by
    have hdivision := Nat.div_add_mod (i : ℕ) chunkSize
    have hmod := Nat.mod_lt (i : ℕ) hchunkPos
    rw [Nat.mul_comm] at hdivision
    exact hchunk (i : ℕ) (by omega) (by omega)
  rw [sparseValidIxAtB_eq_true_iff] at hindex
  exact hindex i.isLt

/-- Near-equal task chunks for executable load balancing. -/
def sparseRowsValidAtParB (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size taskCount : ℕ) : Bool :=
  sparseRowsValidAtChunkedB symmetryIndex r get size taskCount
    (size / taskCount + 1)

theorem sparseRowsValidAt_of_parB {symmetryIndex : OrbitIndex} {r : ℚ}
    {get : ℕ → Row} {size taskCount : ℕ}
    (h : sparseRowsValidAtParB symmetryIndex r get size taskCount = true) :
    SparseRowsValidAt symmetryIndex r get size :=
  sparseRowsValidAt_of_chunkedB h

/-- Full sparse table checker backed by parallel native row checks. -/
def sparseTableValidParB (table : Table) (taskCount : ℕ) : Bool :=
  decide (0 < table.size ∧
    (table.get 0).root = table.root ∧
    (table.get 0).triangle = table.triangle) &&
  sparseRowsValidAtParB table.symmetryIndex table.r table.get table.size
    taskCount

/-- The native row-checking tasks used by `sparseTableValidParB`, exposed so
an executable can report progress while joining them. -/
def sparseTableTasks (table : Table) (taskCount : ℕ) : List (Task Bool) :=
  let chunkSize := table.size / taskCount + 1
  (List.range taskCount).map fun task =>
    Task.spawn fun _ => sparseChunkValidB table.symmetryIndex table.r
      table.get table.size (task * chunkSize) chunkSize

/-- The same full checker as `sparseTableValidParB`, supplied with its already
spawned row tasks. This lets an executable join each task for progress output
and then reuse the cached `Task.get` results. -/
def sparseTableValidWithTasksB (table : Table) (taskCount : ℕ)
    (tasks : List (Task Bool)) : Bool :=
  let chunkSize := table.size / taskCount + 1
  decide (0 < table.size ∧
    (table.get 0).root = table.root ∧
    (table.get 0).triangle = table.triangle) &&
  (decide (table.size ≤ taskCount * chunkSize) && tasks.all Task.get)

theorem sparseTableValid_of_parB {table : Table} {taskCount : ℕ}
    (h : sparseTableValidParB table taskCount = true) :
    SparseTableValid table := by
  unfold sparseTableValidParB at h
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  exact ⟨h.1.1, sparseRowsValidAt_of_parB h.2, h.1.2.1, h.1.2.2⟩

theorem Table.Valid.of_sparseParB {table : Table} {taskCount : ℕ}
    (h : sparseTableValidParB table taskCount = true) : table.Valid :=
  Table.Valid.of_sparse (sparseTableValid_of_parB h)

theorem Table.Valid.of_sparseWithTasksB {table : Table} {taskCount : ℕ}
    (h : sparseTableValidWithTasksB table taskCount
      (sparseTableTasks table taskCount) = true) : table.Valid := by
  apply Table.Valid.of_sparseParB
  exact h

end Noperthedron.Nopert76.SparseLocalViewTree

end
