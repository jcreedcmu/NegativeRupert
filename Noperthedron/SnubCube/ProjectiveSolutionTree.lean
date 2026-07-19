module

public import Noperthedron.SnubCube.ProjectiveEdgeCertificate

@[expose] public section


/-!
# Mixed Cayley/projective-view solution trees

The relative rotation is subdivided by rational Cayley boxes.  Independently,
the normalized outer viewing direction is subdivided by rational triangles.
Leaves may use a projective edge-cycle certificate, a local-rigidity
certificate, or a fundamental-domain pruning certificate.  All child links,
boxes, and view regions are checked by one executable proposition.
-/

namespace Noperthedron.SnubCube.ProjectiveSolutionTree

open ProjectiveView

abbrev Interval := CayleyInterval ℚ
abbrev Triangle := ProjectiveView.Triangle ℚ

/-- A tree node either covers the entire normalized outer chamber or one
rational triangle within it. -/
inductive Region where
  | chamber
  | triangle (value : Triangle)
deriving DecidableEq

def Region.Mem : Region → CayleyPose ℝ → Prop
  | .chamber, p => InChamber (normalizedView p)
  | .triangle value, p =>
      InTriangle (toReal value) (normalizedView p)

/-- There is no chamber-normalized fundamental-domain Rupert pose in this
product of a Cayley interval and a projective-view region. -/
def NoRupert (interval : Interval) (region : Region) : Prop :=
  ¬ ∃ p ∈ interval.toReal, ∃ offset : ℝ²,
    (p.matrixPoseWithOffset offset).InSnubFundamentalDomain ∧
      (p.matrixPoseWithOffset offset).InOuterViewChamber ∧
      region.Mem p ∧
      RupertPose (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull

theorem noRupert_halves (interval : Interval) (region : Region)
    (coordinate : Fin 5)
    (hlower : NoRupert (interval.lowerHalf coordinate) region)
    (hupper : NoRupert (interval.upperHalf coordinate) region) :
    NoRupert interval region := by
  rintro ⟨p, hp, offset, hfund, hchamber, hregion, hrupert⟩
  rcases CayleyInterval.mem_imp_mem_lowerHalf_or_upperHalf coordinate hp with
    hl | hu
  · exact hlower ⟨p, hl, offset, hfund, hchamber, hregion, hrupert⟩
  · exact hupper ⟨p, hu, offset, hfund, hchamber, hregion, hrupert⟩

/-- One row of a flat, forward-pointing mixed proof tree. -/
inductive Row where
  | cayleySplit (id lowerChild upperChild : ℕ) (coordinate : Fin 5)
      (interval : Interval) (region : Region)
  | viewRoot (id : ℕ) (children : Fin 2 → ℕ) (interval : Interval)
  | viewSplit (id : ℕ) (children : Fin 4 → ℕ)
      (interval : Interval) (triangle : Triangle)
  | projective (id : ℕ) (box : ProjectiveEdgeCertificate.Box)
  | localLeaf (id : ℕ) (region : Region)
      (box : CayleyLocalCertificate.Box)
  | prune (id : ℕ) (region : Region)
      (box : CayleyFundamentalPrune.Box)

def Row.id : Row → ℕ
  | .cayleySplit id .. => id
  | .viewRoot id .. => id
  | .viewSplit id .. => id
  | .projective id .. => id
  | .localLeaf id .. => id
  | .prune id .. => id

def Row.interval : Row → Interval
  | .cayleySplit _ _ _ _ interval _ => interval
  | .viewRoot _ _ interval => interval
  | .viewSplit _ _ interval _ => interval
  | .projective _ box => box.interval
  | .localLeaf _ _ box => box.interval
  | .prune _ _ box => box.interval

def Row.region : Row → Region
  | .cayleySplit _ _ _ _ _ region => region
  | .viewRoot .. => .chamber
  | .viewSplit _ _ _ triangle => .triangle triangle
  | .projective _ box => .triangle box.triangle
  | .localLeaf _ region _ => region
  | .prune _ region _ => region

instance : Inhabited Row where
  default := .viewRoot 0 ![0, 0] (CayleyPose.rootInterval ℚ)

/-- Executable local validity.  Split rows check forward graph edges and the
exact interval and view region stored by every child. -/
def Row.ValidAt (get : ℕ → Row) (size : ℕ) : Row → Prop
  | .cayleySplit id lowerChild upperChild coordinate interval region =>
      id < lowerChild ∧ id < upperChild ∧
      lowerChild < size ∧ upperChild < size ∧
      (get lowerChild).interval = interval.lowerHalf coordinate ∧
      (get upperChild).interval = interval.upperHalf coordinate ∧
      (get lowerChild).region = region ∧
      (get upperChild).region = region
  | .viewRoot id children interval => ∀ j,
      id < children j ∧ children j < size ∧
      (get (children j)).interval = interval ∧
      (get (children j)).region = .triangle (chamberRoot j)
  | .viewSplit id children interval triangle => ∀ j,
      id < children j ∧ children j < size ∧
      (get (children j)).interval = interval ∧
      (get (children j)).region = .triangle (split triangle j)
  | .projective _ box => box.Valid
  | .localLeaf _ _ box => box.Valid
  | .prune _ _ box => box.Valid

instance (get : ℕ → Row) (size : ℕ) (row : Row) :
    Decidable (row.ValidAt get size) := by
  cases row <;> simp only [Row.ValidAt] <;> infer_instance

def RowsValidAt (get : ℕ → Row) (size : ℕ) : Prop :=
  ∀ i : Fin size, (get i).id = i ∧ (get i).ValidAt get size

instance (get : ℕ → Row) (size : ℕ) :
    Decidable (RowsValidAt get size) := by
  unfold RowsValidAt
  infer_instance

/-- Soundness of every reachable row, by forward recursion in the flat
table. -/
theorem valid_imp_noRupert_ix (get : ℕ → Row) (size : ℕ)
    (rowsValid : RowsValidAt get size) (i : ℕ) (hi : i < size) :
    NoRupert (get i).interval (get i).region := by
  obtain ⟨hid, hvalid⟩ := rowsValid ⟨i, hi⟩
  generalize hrow : get i = row at hid hvalid ⊢
  cases row with
  | projective id box =>
      unfold NoRupert
      rintro ⟨p, hp, offset, -, hchamber, hregion, hrupert⟩
      exact ProjectiveEdgeCertificate.Box.valid_imp_not_translated_rupert
        box hvalid p hp offset hchamber hregion hrupert
  | localLeaf id region box =>
      unfold NoRupert
      rintro ⟨p, hp, offset, -, -, -, hrupert⟩
      exact CayleyLocalCertificate.Box.valid_imp_not_translated_rupert
        box hvalid p hp offset hrupert
  | prune id region box =>
      unfold NoRupert
      rintro ⟨p, hp, offset, hfund, -, -, -⟩
      exact CayleyFundamentalPrune.Box.valid_imp_no_fundamental_pose
        box hvalid ⟨p, hp, offset, hfund⟩
  | cayleySplit id lowerChild upperChild coordinate interval region =>
      obtain ⟨hlower, hupper, hlowerSize, hupperSize,
        hlowerInterval, hupperInterval, hlowerRegion, hupperRegion⟩ := hvalid
      apply noRupert_halves interval region coordinate
      · rw [← hlowerInterval, ← hlowerRegion]
        exact valid_imp_noRupert_ix get size rowsValid lowerChild hlowerSize
      · rw [← hupperInterval, ← hupperRegion]
        exact valid_imp_noRupert_ix get size rowsValid upperChild hupperSize
  | viewRoot id children interval =>
      unfold NoRupert
      rintro ⟨p, hp, offset, hfund, hchamber, hregion, hrupert⟩
      obtain ⟨child, hchildMem⟩ := mem_chamberRoot hregion
      obtain ⟨hforward, hchildSize, hchildInterval, hchildRegion⟩ :=
        hvalid child
      have hchild := valid_imp_noRupert_ix get size rowsValid
        (children child) hchildSize
      rw [hchildInterval, hchildRegion] at hchild
      exact hchild ⟨p, hp, offset, hfund, hchamber, hchildMem, hrupert⟩
  | viewSplit id children interval triangle =>
      unfold NoRupert
      rintro ⟨p, hp, offset, hfund, hchamber, hregion, hrupert⟩
      obtain ⟨child, hchildMem⟩ := mem_split hregion
      obtain ⟨hforward, hchildSize, hchildInterval, hchildRegion⟩ :=
        hvalid child
      have hchild := valid_imp_noRupert_ix get size rowsValid
        (children child) hchildSize
      rw [hchildInterval, hchildRegion] at hchild
      exact hchild ⟨p, hp, offset, hfund, hchamber, hchildMem, hrupert⟩
termination_by size - i
decreasing_by
  all_goals
    have : id = i := by simpa [Row.id, hrow] using hid
    omega

/-- Data portion of a generated proof table. -/
structure Table where
  get : ℕ → Row
  size : ℕ

/-- A single executable proposition checked by either evaluator. -/
def Table.Valid (table : Table) : Prop :=
  0 < table.size ∧
    RowsValidAt table.get table.size ∧
    (table.get 0).interval = CayleyPose.rootInterval ℚ ∧
    (table.get 0).region = .chamber

instance (table : Table) : Decidable table.Valid := by
  unfold Table.Valid
  infer_instance

theorem Table.valid_imp_no_chamber_cayley_translated_pose
    (table : Table) (h : table.Valid) :
    ¬ ∃ p ∈ CayleyPose.rootInterval ℝ, ∃ offset : ℝ²,
      (p.matrixPoseWithOffset offset).InSnubFundamentalDomain ∧
      (p.matrixPoseWithOffset offset).InOuterViewChamber ∧
      RupertPose (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull := by
  obtain ⟨hnonempty, hrows, hrootInterval, hrootRegion⟩ := h
  have hchecked := valid_imp_noRupert_ix table.get table.size hrows 0 hnonempty
  rw [hrootInterval, hrootRegion, NoRupert,
    CayleyInterval.rootInterval_toReal] at hchecked
  simp only [Region.Mem] at hchecked
  rintro ⟨p, hp, offset, hfund, hchamber, hrupert⟩
  exact hchecked ⟨p, hp, offset, hfund, hchamber,
    normalizedView_inChamber hchamber, hrupert⟩

/-- A valid complete mixed table excludes every matrix pose, including all
rotations and arbitrary planar translations. -/
theorem Table.valid_imp_no_matrixPose (table : Table) (h : table.Valid) :
    ¬ ∃ p : MatrixPose,
      RupertPose p normalizedExactPolyhedron.hull :=
  no_matrixPose_of_no_chamber_cayley_translated_pose
    (table.valid_imp_no_chamber_cayley_translated_pose h)

end Noperthedron.SnubCube.ProjectiveSolutionTree

end
