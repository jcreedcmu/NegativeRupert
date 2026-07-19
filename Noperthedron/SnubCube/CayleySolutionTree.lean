module

public import Noperthedron.SnubCube.CayleyGlobalCertificate

@[expose] public section


/-!
# Flat mixed solution trees in bounded Cayley coordinates

A row is either a binary midpoint split or one of the three independently
checked leaf types: local rigidity, polynomial balanced support, and
fundamental-domain pruning.  Child identifiers must increase, making the
flat table a well-founded proof tree while retaining an executable validity
predicate suitable for both kernel `decide` and `native_decide`.
-/

namespace Noperthedron.SnubCube.CayleySolutionTree

abbrev Interval := CayleyInterval ℚ

/-- There is no fundamental-domain Rupert pose in this rational box. -/
def NoRupert (iv : Interval) : Prop :=
  ¬ ∃ p ∈ iv.toReal, ∃ offset : ℝ²,
    (p.matrixPoseWithOffset offset).InSnubFundamentalDomain ∧
      RupertPose (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull

theorem noRupert_halves (iv : Interval) (coordinate : Fin 5)
    (hlower : NoRupert (iv.lowerHalf coordinate))
    (hupper : NoRupert (iv.upperHalf coordinate)) :
    NoRupert iv := by
  rintro ⟨p, hp, offset, hfund, hrupert⟩
  rcases CayleyInterval.mem_imp_mem_lowerHalf_or_upperHalf coordinate hp with
    hl | hu
  · exact hlower ⟨p, hl, offset, hfund, hrupert⟩
  · exact hupper ⟨p, hu, offset, hfund, hrupert⟩

/-- One row of a flat, forward-pointing binary proof tree. -/
inductive Row where
  | split (id lowerChild upperChild : ℕ) (coordinate : Fin 5)
      (interval : Interval)
  | global (id : ℕ) (box : CayleyGlobalCertificate.Box)
  | localLeaf (id : ℕ) (box : CayleyLocalCertificate.Box)
  | prune (id : ℕ) (box : CayleyFundamentalPrune.Box)

def Row.id : Row → ℕ
  | .split id .. => id
  | .global id .. => id
  | .localLeaf id .. => id
  | .prune id .. => id

def Row.interval : Row → Interval
  | .split _ _ _ _ interval => interval
  | .global _ box => box.interval
  | .localLeaf _ box => box.interval
  | .prune _ box => box.interval

instance : Inhabited Row where
  default := .split 0 0 0 0 (CayleyPose.rootInterval ℚ)

/-- Executable local validity of one row.  A split checks both its graph
edges and the exact intervals stored by its children. -/
def Row.ValidAt (get : ℕ → Row) (size : ℕ) : Row → Prop
  | .split id lowerChild upperChild coordinate interval =>
      id < lowerChild ∧ id < upperChild ∧
      lowerChild < size ∧ upperChild < size ∧
      (get lowerChild).interval = interval.lowerHalf coordinate ∧
      (get upperChild).interval = interval.upperHalf coordinate
  | .global _ box => box.Valid
  | .localLeaf _ box => box.Valid
  | .prune _ box => box.Valid

instance (get : ℕ → Row) (size : ℕ) (row : Row) :
    Decidable (row.ValidAt get size) := by
  cases row <;> simp only [Row.ValidAt] <;> infer_instance

def RowsValidAt (get : ℕ → Row) (size : ℕ) : Prop :=
  ∀ i : Fin size, (get i).id = i ∧ (get i).ValidAt get size

instance (get : ℕ → Row) (size : ℕ) :
    Decidable (RowsValidAt get size) := by
  unfold RowsValidAt
  infer_instance

/-- Soundness of every reachable row.  The decreasing measure is justified
by the checked forward-child condition. -/
theorem valid_imp_noRupert_ix (get : ℕ → Row) (size : ℕ)
    (rowsValid : RowsValidAt get size) (i : ℕ) (hi : i < size) :
    NoRupert (get i).interval := by
  obtain ⟨hid, hvalid⟩ := rowsValid ⟨i, hi⟩
  generalize hrow : get i = row at hid hvalid ⊢
  cases row with
  | global id box =>
      unfold NoRupert
      rintro ⟨p, hp, offset, -, hrupert⟩
      exact CayleyGlobalCertificate.Box.valid_imp_not_translated_rupert
        box hvalid p hp offset hrupert
  | localLeaf id box =>
      unfold NoRupert
      rintro ⟨p, hp, offset, -, hrupert⟩
      exact CayleyLocalCertificate.Box.valid_imp_not_translated_rupert
        box hvalid p hp offset hrupert
  | prune id box =>
      unfold NoRupert
      rintro ⟨p, hp, offset, hfund, -⟩
      exact CayleyFundamentalPrune.Box.valid_imp_no_fundamental_pose
        box hvalid ⟨p, hp, offset, hfund⟩
  | split id lowerChild upperChild coordinate interval =>
      obtain ⟨hlower, hupper, hlowerSize, hupperSize,
        hlowerInterval, hupperInterval⟩ := hvalid
      apply noRupert_halves interval coordinate
      · rw [← hlowerInterval]
        exact valid_imp_noRupert_ix get size rowsValid lowerChild hlowerSize
      · rw [← hupperInterval]
        exact valid_imp_noRupert_ix get size rowsValid upperChild hupperSize
termination_by size - i
decreasing_by
  · have : id = i := by simpa [Row.id, hrow] using hid
    omega
  · have : id = i := by simpa [Row.id, hrow] using hid
    omega

/-- Data portion of a generated proof table. -/
structure Table where
  get : ℕ → Row
  size : ℕ

/-- A single executable proposition checked by either evaluator. -/
def Table.Valid (table : Table) : Prop :=
  0 < table.size ∧
    RowsValidAt table.get table.size ∧
    (table.get 0).interval = CayleyPose.rootInterval ℚ

instance (table : Table) : Decidable table.Valid := by
  unfold Table.Valid
  infer_instance

theorem Table.valid_imp_no_cayley_translated_pose
    (table : Table) (h : table.Valid) :
    ¬ ∃ p ∈ CayleyPose.rootInterval ℝ, ∃ offset : ℝ²,
      (p.matrixPoseWithOffset offset).InSnubFundamentalDomain ∧
        RupertPose (p.matrixPoseWithOffset offset)
          normalizedExactPolyhedron.hull := by
  obtain ⟨hnonempty, hrows, hroot⟩ := h
  have hchecked := valid_imp_noRupert_ix table.get table.size hrows 0 hnonempty
  rw [hroot, NoRupert, CayleyInterval.rootInterval_toReal] at hchecked
  exact hchecked

/-- A valid complete Cayley table excludes every matrix pose, including
arbitrary planar translations and all rotations. -/
theorem Table.valid_imp_no_matrixPose (table : Table) (h : table.Valid) :
    ¬ ∃ p : MatrixPose,
      RupertPose p normalizedExactPolyhedron.hull :=
  no_matrixPose_of_no_cayley_translated_pose
    (table.valid_imp_no_cayley_translated_pose h)

end Noperthedron.SnubCube.CayleySolutionTree

end
