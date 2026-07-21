module

public import Noperthedron.Nopert214.AtlasProjectiveLocalCertificate

@[expose] public section

/-!
# Shared projective-view atlas for symmetry-local rigidity

The expensive balanced-support geometry depends on the outer view but not on
the Cayley interval or chart.  This tree checks that geometry once.  A small
`Tube` then supplies only the chart-dependent mismatch bound, allowing every
near-symmetry leaf in the main search to reuse the same view atlas.
-/

namespace Noperthedron.Nopert214.AtlasProjectiveLocalViewTree

open AtlasProjectiveView AtlasProjectiveLocalCertificate
open Noperthedron.SnubCube.ProjectiveView

structure Tube where
  interval : AtlasInterval ℚ
  chart : CayleyAtlas.ChartIndex
  symmetryIndex : OrbitIndex
  r : ℚ
deriving DecidableEq

def Tube.shell (tube : Tube) : AtlasLocalCertificate.Box where
  interval := tube.interval
  chart := tube.chart
  symmetryIndex := tube.symmetryIndex
  certificate := fun _ => { contact := fun _ => { index := 0, direction := 0 } }
  c := 0
  r := tube.r

abbrev Tube.mismatchRadius (tube : Tube) : ℚ := tube.shell.mismatchRadius

def Tube.Valid (tube : Tube) : Prop := tube.mismatchRadius ≤ tube.r

instance (tube : Tube) : Decidable tube.Valid := by
  unfold Tube.Valid
  infer_instance

inductive Row where
  | split (id : ℕ) (children : Fin 4 → ℕ)
      (root : Fin 8) (triangle : AtlasProjectiveView.Triangle ℚ)
  | certificate (id : ℕ) (box : AtlasProjectiveLocalCertificate.Box)
deriving DecidableEq

def Row.id : Row → ℕ
  | .split id .. | .certificate id .. => id

def Row.root : Row → Fin 8
  | .split _ _ root _ | .certificate _ { root, .. } => root

def Row.triangle : Row → AtlasProjectiveView.Triangle ℚ
  | .split _ _ _ triangle | .certificate _ { triangle, .. } => triangle

instance : Inhabited Row where
  default := .split 0 (fun _ => 0) 0 upperWedgeTriangle

def Row.ValidAt (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size : ℕ) : Row → Prop
  | .split id children root triangle => ∀ child,
      id < children child ∧ children child < size ∧
      (get (children child)).root = root ∧
      (get (children child)).triangle =
        Noperthedron.SnubCube.ProjectiveView.split triangle child
  | .certificate _ box =>
      box.symmetryIndex = symmetryIndex ∧ box.r = r ∧ box.ViewValid

instance (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row)
    (size : ℕ) (row : Row) :
    Decidable (row.ValidAt symmetryIndex r get size) := by
  cases row <;> simp only [Row.ValidAt] <;> infer_instance

def RowsValidAt (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size : ℕ) : Prop :=
  ∀ i : Fin size,
    (get i).id = i ∧ (get i).ValidAt symmetryIndex r get size

instance (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row)
    (size : ℕ) : Decidable (RowsValidAt symmetryIndex r get size) := by
  unfold RowsValidAt
  infer_instance

/-- A kernel-checkable slice of `RowsValidAt`.  Generated local-view tables
prove small slices independently and join them, so kernel reduction never has
to unfold the entire certificate atlas at once. -/
def RowsValidRangeAt (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size start count : ℕ) : Prop :=
  start + count ≤ size ∧ ∀ j : Fin count,
    (get (start + j.val)).id = start + j.val ∧
      (get (start + j.val)).ValidAt symmetryIndex r get size

instance (symmetryIndex : OrbitIndex) (r : ℚ) (get : ℕ → Row)
    (size start count : ℕ) :
    Decidable (RowsValidRangeAt symmetryIndex r get size start count) := by
  unfold RowsValidRangeAt
  infer_instance

theorem rowsValidRange_append {symmetryIndex : OrbitIndex} {r : ℚ}
    {get : ℕ → Row} {size start left right : ℕ}
    (hleft : RowsValidRangeAt symmetryIndex r get size start left)
    (hright : RowsValidRangeAt symmetryIndex r get size (start + left) right) :
    RowsValidRangeAt symmetryIndex r get size start (left + right) := by
  unfold RowsValidRangeAt at hleft hright ⊢
  constructor
  · omega
  · intro j
    by_cases hmid : j.val < left
    · simpa using hleft.2 ⟨j.val, hmid⟩
    · have hjright : j.val - left < right := by omega
      have hr := hright.2 ⟨j.val - left, hjright⟩
      have hi : start + left + (j.val - left) = start + j.val := by omega
      simpa [hi] using hr

theorem rowsValidAt_of_range {symmetryIndex : OrbitIndex} {r : ℚ}
    {get : ℕ → Row} {size : ℕ}
    (h : RowsValidRangeAt symmetryIndex r get size 0 size) :
    RowsValidAt symmetryIndex r get size := by
  intro i
  simpa using h.2 ⟨i.val, i.isLt⟩

theorem valid_imp_not_rupert_ix (symmetryIndex : OrbitIndex) (r : ℚ)
    (get : ℕ → Row) (size : ℕ)
    (rowsValid : RowsValidAt symmetryIndex r get size)
    (i : ℕ) (hi : i < size) (tube : Tube)
    (htubeSymmetry : tube.symmetryIndex = symmetryIndex)
    (htubeRadius : tube.r = r) (htube : tube.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ tube.interval.toReal) (offset : ℝ²)
    (hscale : 1 ≤ viewScale (get i).root p)
    (hmem : InTriangle (toReal (get i).triangle)
      (normalizedView (get i).root p)) :
    ¬ RupertPose (p.matrixPoseWithOffset tube.chart offset)
      exactPolyhedron.hull := by
  obtain ⟨hid, hvalid⟩ := rowsValid ⟨i, hi⟩
  generalize hrow : get i = row at hid hvalid hscale hmem ⊢
  cases row with
  | split id children root triangle =>
      obtain ⟨child, hchildMem⟩ := mem_split hmem
      obtain ⟨hforward, hchildSize, hchildRoot, hchildTriangle⟩ :=
        hvalid child
      have hchild := valid_imp_not_rupert_ix symmetryIndex r get size
        rowsValid (children child) hchildSize tube htubeSymmetry
        htubeRadius htube hp offset
      rw [hchildRoot, hchildTriangle] at hchild
      exact hchild hscale hchildMem
  | certificate id box =>
      obtain ⟨hboxSymmetry, hboxRadius, hview⟩ := hvalid
      let actual := box.retarget tube.interval tube.chart
      have hactualView : actual.ViewValid :=
        hview.retarget tube.interval tube.chart
      have hmismatch : actual.mismatchRadius ≤ actual.r := by
        have hsym : box.symmetryIndex = tube.symmetryIndex :=
          hboxSymmetry.trans htubeSymmetry.symm
        have hr : box.r = tube.r :=
          hboxRadius.trans htubeRadius.symm
        simpa [actual, Box.retarget, Box.mismatchRadius,
          Box.mismatchShell, Tube.Valid, Tube.mismatchRadius, Tube.shell,
          AtlasLocalCertificate.Box.mismatchRadius,
          AtlasLocalCertificate.Box.mismatchFrobeniusSqUpper,
          AtlasLocalCertificate.Box.entryAbsUpper,
          AtlasLocalCertificate.Box.mismatchBall,
          AtlasLocalCertificate.Box.variableBalls,
          AtlasLocalCertificate.Box.mismatchQuadratic,
          hsym, hr]
          using htube
      have hactual : actual.Valid :=
        Box.Valid.of_viewValid hactualView hmismatch
      exact actual.valid_imp_not_translated_rupert hactual hp offset
        hscale hmem
termination_by size - i
decreasing_by
  all_goals
    have : id = i := by simpa [Row.id, hrow] using hid
    omega

structure Table where
  symmetryIndex : OrbitIndex
  r : ℚ
  get : ℕ → Row
  size : ℕ

def Table.Valid (table : Table) : Prop :=
  0 < table.size ∧
    RowsValidAt table.symmetryIndex table.r table.get table.size ∧
    (table.get 0).root = 0 ∧
    (table.get 0).triangle = upperWedgeTriangle

instance (table : Table) : Decidable table.Valid := by
  unfold Table.Valid
  infer_instance

theorem Table.valid_imp_not_translated_rupert (table : Table)
    (hvalid : table.Valid) (tube : Tube)
    (htubeSymmetry : tube.symmetryIndex = table.symmetryIndex)
    (htubeRadius : tube.r = table.r) (htube : tube.Valid)
    {p : AtlasPose ℝ} (hp : p ∈ tube.interval.toReal)
    (hview : p.InViewWedge) (hupper : p.InUpperView) (offset : ℝ²) :
    ¬ RupertPose (p.matrixPoseWithOffset tube.chart offset)
      exactPolyhedron.hull := by
  obtain ⟨hnonempty, hrows, hroot, htriangle⟩ := hvalid
  obtain ⟨hscale, hmem⟩ := upperView_mem_wedgeTriangle p hview hupper
  have hchecked := valid_imp_not_rupert_ix table.symmetryIndex table.r
    table.get table.size hrows 0 hnonempty tube htubeSymmetry htubeRadius
    htube hp offset
  rw [hroot, htriangle] at hchecked
  exact hchecked hscale hmem

end Noperthedron.Nopert214.AtlasProjectiveLocalViewTree

end
