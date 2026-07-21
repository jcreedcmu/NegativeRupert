module

public import Noperthedron.Nopert214.AtlasProjectiveLocalViewTree
public import Noperthedron.Nopert214.GeneratedTangentCones

@[expose] public section

/-!
# Sparse validation for projective local-view trees

The semantic tree and its final theorem remain unchanged.  This module only
provides a cheaper decidable predicate for generated certificate rows.  A
proof of the sparse predicate is converted to the original `Table.Valid`
hypothesis using the exact tangent-cone certificates.
-/

namespace Noperthedron.Nopert214.SparseLocalViewTree

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

end Noperthedron.Nopert214.SparseLocalViewTree

end
