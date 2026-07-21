module

public import Noperthedron.Nopert214.AtlasProjectiveEdgeCertificate
public import Noperthedron.Nopert214.AtlasFundamentalPrune
public import Noperthedron.Nopert214.AtlasLocalCertificate
public import Noperthedron.Nopert214.AtlasProjectiveLocalCertificate
public import Noperthedron.Nopert214.AtlasProjectiveGlobalCertificate

@[expose] public section

/-!
# Mixed Cayley/projective solution trees for Nopert #214

The relative Cayley box is split along any of its five stored coordinates
(generated trees use only `x,y,z`).  Independently, the outer view is split
from the whole sphere into eight signed roots and then by four-way midpoint
triangle subdivision.  Leaves carry projective edge-cycle certificates.
-/

namespace Noperthedron.Nopert214.AtlasProjectiveSolutionTree

open CayleyAtlas AtlasProjectiveView
open Noperthedron.SnubCube.ProjectiveView

abbrev Interval := AtlasInterval ℚ
abbrev Triangle := AtlasProjectiveView.Triangle ℚ

inductive Region where
  | sphere
  | triangle (root : Fin 8) (value : Triangle)
deriving DecidableEq

def Region.Mem : Region → AtlasPose ℝ → Prop
  | .sphere, _ => True
  | .triangle root value, p =>
      1 ≤ viewScale root p ∧
        InTriangle (toReal value) (normalizedView root p)

def NoRupert (chart : ChartIndex) (interval : Interval)
    (region : Region) : Prop :=
  ¬ ∃ p ∈ interval.toReal, p.CayleyBounded ∧
    p.InFivefoldFundamentalDomain chart ∧ p.InViewWedge ∧
    p.InUpperView ∧
    ∃ offset : ℝ²,
    region.Mem p ∧
      RupertPose (p.matrixPoseWithOffset chart offset)
        exactPolyhedron.hull

theorem noRupert_halves (chart : ChartIndex) (interval : Interval)
    (region : Region) (coordinate : Fin 5)
    (hlower : NoRupert chart (interval.lowerHalf coordinate) region)
    (hupper : NoRupert chart (interval.upperHalf coordinate) region) :
    NoRupert chart interval region := by
  rintro ⟨p, hp, hbounded, hfund, hview, hupperView, offset, hregion, hrupert⟩
  rcases AtlasInterval.mem_imp_mem_lowerHalf_or_upperHalf coordinate hp with
    hl | hu
  · exact hlower ⟨p, hl, hbounded, hfund, hview, hupperView,
      offset, hregion, hrupert⟩
  · exact hupper ⟨p, hu, hbounded, hfund, hview, hupperView,
      offset, hregion, hrupert⟩

def minAbsBound (lo hi : ℚ) : ℚ :=
  if lo ≤ 0 ∧ 0 ≤ hi then 0 else min |lo| |hi|

def Interval.outsideCayleyBall (interval : Interval) : Prop :=
  minAbsBound interval.min.x interval.max.x ^ 2 +
    minAbsBound interval.min.y interval.max.y ^ 2 +
    minAbsBound interval.min.z interval.max.z ^ 2 > 3

instance (interval : Interval) : Decidable interval.outsideCayleyBall := by
  unfold Interval.outsideCayleyBall minAbsBound
  infer_instance

private theorem minAbsBound_le_abs {lo hi : ℚ} {x : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ)) :
    (minAbsBound lo hi : ℚ) ≤ |x| := by
  unfold minAbsBound
  split_ifs with hcross
  · norm_num
  · by_cases hlo : lo ≤ 0
    · have hhi : ¬ 0 ≤ hi := fun hhi => hcross ⟨hlo, hhi⟩
      have hhiQ : hi < 0 := lt_of_not_ge hhi
      have hhiR : (hi : ℝ) < 0 := by exact_mod_cast hhiQ
      have hx0 : x < 0 := hx.2.trans_lt hhiR
      have hmin : min |lo| |hi| ≤ |hi| := min_le_right _ _
      have hminR : ((min |lo| |hi| : ℚ) : ℝ) ≤ ((|hi| : ℚ) : ℝ) := by
        exact_mod_cast hmin
      exact hminR.trans (by
        rw [Rat.cast_abs, abs_of_neg hhiR, abs_of_neg hx0]
        linarith [hx.2])
    · have hloQ : 0 < lo := lt_of_not_ge hlo
      have hloR : (0 : ℝ) < lo := by exact_mod_cast hloQ
      have hx0 : 0 < x := hloR.trans_le hx.1
      have hmin : min |lo| |hi| ≤ |lo| := min_le_left _ _
      have hminR : ((min |lo| |hi| : ℚ) : ℝ) ≤ ((|lo| : ℚ) : ℝ) := by
        exact_mod_cast hmin
      exact hminR.trans (by
        rw [Rat.cast_abs, abs_of_pos hloR, abs_of_pos hx0]
        exact hx.1)

theorem noRupert_of_outsideCayleyBall (chart : ChartIndex)
    (interval : Interval) (region : Region)
    (h : interval.outsideCayleyBall) : NoRupert chart interval region := by
  rintro ⟨p, hp, hbounded, -, -, -, offset, hregion, hrupert⟩
  have hmem := AtlasInterval.mem_toReal_iff.mp hp
  have hx := minAbsBound_le_abs (hmem 2)
  have hy := minAbsBound_le_abs (hmem 3)
  have hz := minAbsBound_le_abs (hmem 4)
  have hx0 : (0 : ℝ) ≤ (minAbsBound interval.min.x interval.max.x : ℚ) := by
    unfold minAbsBound
    split_ifs <;> positivity
  have hy0 : (0 : ℝ) ≤ (minAbsBound interval.min.y interval.max.y : ℚ) := by
    unfold minAbsBound
    split_ifs <;> positivity
  have hz0 : (0 : ℝ) ≤ (minAbsBound interval.min.z interval.max.z : ℚ) := by
    unfold minAbsBound
    split_ifs <;> positivity
  have hxsq := (sq_le_sq₀ hx0 (abs_nonneg p.x)).2 hx
  have hysq := (sq_le_sq₀ hy0 (abs_nonneg p.y)).2 hy
  have hzsq := (sq_le_sq₀ hz0 (abs_nonneg p.z)).2 hz
  simp only [sq_abs] at hxsq hysq hzsq
  have hout : (3 : ℝ) <
      (minAbsBound interval.min.x interval.max.x : ℚ) ^ 2 +
      (minAbsBound interval.min.y interval.max.y : ℚ) ^ 2 +
      (minAbsBound interval.min.z interval.max.z : ℚ) ^ 2 := by
    exact_mod_cast h
  unfold AtlasPose.CayleyBounded at hbounded
  nlinarith

inductive Row where
  | cayleySplit (id lowerChild upperChild : ℕ) (coordinate : Fin 5)
      (interval : Interval) (region : Region)
  | viewRoot (id child : ℕ) (interval : Interval)
  | viewSplit (id : ℕ) (children : Fin 4 → ℕ)
      (interval : Interval) (root : Fin 8) (triangle : Triangle)
  | projective (id : ℕ) (box : AtlasProjectiveEdgeCertificate.Box)
  | projectiveGlobal (id : ℕ)
      (box : AtlasProjectiveGlobalCertificate.Box)
  | symmetryLocal (id : ℕ) (box : AtlasLocalCertificate.Box)
      (region : Region)
  | projectiveLocal (id : ℕ) (box : AtlasProjectiveLocalCertificate.Box)
  | radiusPrune (id : ℕ) (interval : Interval) (region : Region)
  | fundamentalPrune (id : ℕ) (box : AtlasFundamentalPrune.Box)
      (region : Region)

def Row.id : Row → ℕ
  | .cayleySplit id .. | .viewRoot id .. | .viewSplit id .. |
      .projective id .. | .projectiveGlobal id .. |
      .symmetryLocal id .. | .radiusPrune id .. |
      .fundamentalPrune id .. => id
  | .projectiveLocal id .. => id

def Row.interval : Row → Interval
  | .cayleySplit _ _ _ _ interval _ => interval
  | .viewRoot _ _ interval => interval
  | .viewSplit _ _ interval _ _ => interval
  | .projective _ box => box.interval
  | .projectiveGlobal _ box => box.interval
  | .symmetryLocal _ box _ => box.interval
  | .projectiveLocal _ box => box.interval
  | .radiusPrune _ interval _ => interval
  | .fundamentalPrune _ box _ => box.interval

def Row.region : Row → Region
  | .cayleySplit _ _ _ _ _ region => region
  | .viewRoot .. => .sphere
  | .viewSplit _ _ _ root triangle => .triangle root triangle
  | .projective _ box => .triangle box.root box.triangle
  | .projectiveGlobal _ box => .triangle box.root box.triangle
  | .symmetryLocal _ _ region => region
  | .projectiveLocal _ box => .triangle box.root box.triangle
  | .radiusPrune _ _ region => region
  | .fundamentalPrune _ _ region => region

instance : Inhabited Row where
  default := .viewRoot 0 0 (AtlasPose.rootInterval ℚ)

def Row.ValidAt (chart : ChartIndex) (get : ℕ → Row)
    (size : ℕ) : Row → Prop
  | .cayleySplit id lowerChild upperChild coordinate interval region =>
      id < lowerChild ∧ id < upperChild ∧
      lowerChild < size ∧ upperChild < size ∧
      (get lowerChild).interval = interval.lowerHalf coordinate ∧
      (get upperChild).interval = interval.upperHalf coordinate ∧
      (get lowerChild).region = region ∧
      (get upperChild).region = region
  | .viewRoot id child interval =>
      id < child ∧ child < size ∧
      (get child).interval = interval ∧
      (get child).region = .triangle 0 upperWedgeTriangle
  | .viewSplit id children interval root triangle => ∀ child,
      id < children child ∧ children child < size ∧
      (get (children child)).interval = interval ∧
      (get (children child)).region =
        .triangle root (split triangle child)
  | .projective _ box => box.chart = chart ∧ box.Valid
  | .projectiveGlobal _ box => box.chart = chart ∧ box.Valid
  | .symmetryLocal _ box _ => box.chart = chart ∧ box.Valid
  | .projectiveLocal _ box => box.chart = chart ∧ box.Valid
  | .radiusPrune _ interval _ => interval.outsideCayleyBall
  | .fundamentalPrune _ box _ => box.chart = chart ∧ box.Valid

instance (chart : ChartIndex) (get : ℕ → Row) (size : ℕ) (row : Row) :
    Decidable (row.ValidAt chart get size) := by
  cases row <;> simp only [Row.ValidAt] <;> infer_instance

def RowsValidAt (chart : ChartIndex) (get : ℕ → Row)
    (size : ℕ) : Prop :=
  ∀ i : Fin size, (get i).id = i ∧ (get i).ValidAt chart get size

instance (chart : ChartIndex) (get : ℕ → Row) (size : ℕ) :
    Decidable (RowsValidAt chart get size) := by
  unfold RowsValidAt
  infer_instance

/-- A kernel-checkable slice of `RowsValidAt`.  Generated tables prove small
slices independently and join them with `rowsValidRange_append`, avoiding one
enormous reduction in the kernel evaluator. -/
def RowsValidRangeAt (chart : ChartIndex) (get : ℕ → Row) (size start count : ℕ) :
    Prop :=
  start + count ≤ size ∧ ∀ j : Fin count,
    (get (start + j.val)).id = start + j.val ∧
      (get (start + j.val)).ValidAt chart get size

instance (chart : ChartIndex) (get : ℕ → Row) (size start count : ℕ) :
    Decidable (RowsValidRangeAt chart get size start count) := by
  unfold RowsValidRangeAt
  infer_instance

theorem rowsValidRange_append {chart : ChartIndex} {get : ℕ → Row}
    {size start left right : ℕ}
    (hleft : RowsValidRangeAt chart get size start left)
    (hright : RowsValidRangeAt chart get size (start + left) right) :
    RowsValidRangeAt chart get size start (left + right) := by
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

theorem rowsValidAt_of_range {chart : ChartIndex} {get : ℕ → Row} {size : ℕ}
    (h : RowsValidRangeAt chart get size 0 size) :
    RowsValidAt chart get size := by
  intro i
  simpa using h.2 ⟨i.val, i.isLt⟩

theorem valid_imp_noRupert_ix (chart : ChartIndex) (get : ℕ → Row)
    (size : ℕ) (rowsValid : RowsValidAt chart get size)
    (i : ℕ) (hi : i < size) :
    NoRupert chart (get i).interval (get i).region := by
  obtain ⟨hid, hvalid⟩ := rowsValid ⟨i, hi⟩
  generalize hrow : get i = row at hid hvalid ⊢
  cases row with
  | projective id box =>
      unfold NoRupert
      rintro ⟨p, hp, hbounded, -, -, -, offset, hregion, hrupert⟩
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact box.valid_imp_not_translated_rupert hbox hp hbounded offset
        hregion.1 hregion.2 hrupert
  | projectiveGlobal id box =>
      unfold NoRupert
      rintro ⟨p, hp, hbounded, -, -, -, offset, hregion, hrupert⟩
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact box.valid_imp_not_translated_rupert hbox p hp hbounded
        hregion.1 hregion.2 offset hrupert
  | symmetryLocal id box region =>
      unfold NoRupert
      rintro ⟨p, hp, -, -, -, -, offset, -, hrupert⟩
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact box.valid_imp_not_translated_rupert hbox p hp offset hrupert
  | projectiveLocal id box =>
      unfold NoRupert
      rintro ⟨p, hp, -, -, -, -, offset, hregion, hrupert⟩
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact box.valid_imp_not_translated_rupert hbox hp offset
        hregion.1 hregion.2 hrupert
  | cayleySplit id lowerChild upperChild coordinate interval region =>
      obtain ⟨hlower, hupper, hlowerSize, hupperSize,
        hlowerInterval, hupperInterval, hlowerRegion, hupperRegion⟩ := hvalid
      apply noRupert_halves chart interval region coordinate
      · rw [← hlowerInterval, ← hlowerRegion]
        exact valid_imp_noRupert_ix chart get size rowsValid
          lowerChild hlowerSize
      · rw [← hupperInterval, ← hupperRegion]
        exact valid_imp_noRupert_ix chart get size rowsValid
          upperChild hupperSize
  | viewRoot id child interval =>
      unfold NoRupert
      rintro ⟨p, hp, hbounded, hfund, hview, hupper, offset, -, hrupert⟩
      obtain ⟨hscale, hmem⟩ := upperView_mem_wedgeTriangle p hview hupper
      obtain ⟨hforward, hchildSize, hchildInterval, hchildRegion⟩ := hvalid
      have hchild := valid_imp_noRupert_ix chart get size rowsValid
        child hchildSize
      rw [hchildInterval, hchildRegion] at hchild
      exact hchild ⟨p, hp, hbounded, hfund, hview, hupper, offset,
        ⟨hscale, hmem⟩, hrupert⟩
  | viewSplit id children interval root triangle =>
      unfold NoRupert
      rintro ⟨p, hp, hbounded, hfund, hview, hupper, offset, hregion, hrupert⟩
      obtain ⟨child, hchildMem⟩ := mem_split hregion.2
      obtain ⟨hforward, hchildSize, hchildInterval, hchildRegion⟩ :=
        hvalid child
      have hchild := valid_imp_noRupert_ix chart get size rowsValid
        (children child) hchildSize
      rw [hchildInterval, hchildRegion] at hchild
      exact hchild ⟨p, hp, hbounded, hfund, hview, hupper, offset,
        ⟨hregion.1, hchildMem⟩, hrupert⟩
  | radiusPrune id interval region =>
      exact noRupert_of_outsideCayleyBall chart interval region hvalid
  | fundamentalPrune id box region =>
      unfold NoRupert
      rintro ⟨p, hp, hbounded, hfund, -, -, offset, -, hrupert⟩
      obtain ⟨hchart, hbox⟩ := hvalid
      subst hchart
      exact box.valid_imp_not_inFundamentalDomain hbox hp hbounded hfund
termination_by size - i
decreasing_by
  all_goals
    have : id = i := by simpa [Row.id, hrow] using hid
    omega

structure Table where
  chart : ChartIndex
  get : ℕ → Row
  size : ℕ

def Table.Valid (table : Table) : Prop :=
  0 < table.size ∧
    RowsValidAt table.chart table.get table.size ∧
    (table.get 0).interval =
      AtlasFundamentalPrune.restrictedRootInterval table.chart ∧
    (table.get 0).region = .sphere

instance (table : Table) : Decidable table.Valid := by
  unfold Table.Valid
  infer_instance

theorem Table.valid_imp_no_chart_translated_pose
    (table : Table) (h : table.Valid) :
    ¬ ∃ p ∈ AtlasPose.rootInterval ℝ,
      p.CayleyBounded ∧ p.InFivefoldFundamentalDomain table.chart ∧
      p.InViewWedge ∧ p.InUpperView ∧ ∃ offset : ℝ²,
      RupertPose (p.matrixPoseWithOffset table.chart offset)
        exactPolyhedron.hull := by
  obtain ⟨hnonempty, hrows, hrootInterval, hrootRegion⟩ := h
  have hchecked := valid_imp_noRupert_ix table.chart table.get table.size
    hrows 0 hnonempty
  rw [hrootInterval, hrootRegion] at hchecked
  rintro ⟨p, hp, hbounded, hfund, hview, hupper, offset, hrupert⟩
  exact hchecked ⟨p,
    AtlasFundamentalPrune.mem_restrictedRootInterval
      table.chart hp hbounded hfund,
    hbounded, hfund, hview, hupper, offset, trivial, hrupert⟩

/-- Four valid chart tables exclude every matrix pose. -/
theorem no_matrixPose_of_valid_tables
    (table : ChartIndex → Table)
    (hchart : ∀ chart, (table chart).chart = chart)
    (hvalid : ∀ chart, (table chart).Valid) :
    ¬ ∃ p : MatrixPose, RupertPose p exactPolyhedron.hull := by
  rintro ⟨p, hrupert⟩
  obtain ⟨chart, q, offset, hq, hbounded, hview, hupper, hfund, heq⟩ :=
    AtlasFundamentalPrune.exists_fundamental_atlas_translated_pose p
  have hno := (table chart).valid_imp_no_chart_translated_pose (hvalid chart)
  rw [hchart chart] at hno
  exact hno ⟨q, hq, hbounded, hfund, hview, hupper, offset,
    heq.mpr hrupert⟩

end Noperthedron.Nopert214.AtlasProjectiveSolutionTree

end
