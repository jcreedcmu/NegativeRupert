module

public import Noperthedron.SolutionTable.Defs
public import Noperthedron.PoseInterval
public import Noperthedron.Checker.Global
public import Noperthedron.Checker.LocalNat
public import Noperthedron.Checker.LocalFastNat
public import Noperthedron.Checker.Local2

@[expose] public section


namespace Noperthedron.Solution

/-!
## Validity over a row source

The proof-producing kernel checker cannot use a flat `Array`: child lookup in a
two-million-row literal would be linear in the child index.  Runtime checking,
on the other hand, naturally gets rows from an array.  Both routes use the same
validity predicates below, parameterized only by a total row getter and its
logical size.  The bounds in the predicates ensure that out-of-range values of
the total getter are irrelevant.
-/

@[mk_iff]
structure Row.ValidSplitParamAt (get : ℕ → Row) (size : ℕ) (row : Row)
    (param : Param) : Prop where
  id_in_table : row.ID < row.IDfirstChild
  children_in_table : row.IDfirstChild + row.nrChildren ≤ size
  nonzero_children : row.nrChildren ≠ 0
  children_intervals_good : ∀ n : Fin row.nrChildren,
    (get (row.IDfirstChild + n)).interval =
      row.interval.nth_part param row.nrChildren (hN := ⟨nonzero_children⟩) n

instance (get : ℕ → Row) (size : ℕ) (row : Row) (param : Param) :
    Decidable (Row.ValidSplitParamAt get size row param) :=
  decidable_of_iff _ (Row.validSplitParamAt_iff get size row param).symm

/-- The row's `split` code selects a single parameter (via `Param.ofSplitCode?`),
and the row is a valid split of its interval along that parameter. -/
def Row.ValidSingleParamSplitAt (get : ℕ → Row) (size : ℕ) (row : Row) : Prop :=
  ∃ p, Param.ofSplitCode? row.split = some p ∧ row.ValidSplitParamAt get size p

instance (get : ℕ → Row) (size : ℕ) (row : Row) :
    Decidable (row.ValidSingleParamSplitAt get size) := by
  unfold Row.ValidSingleParamSplitAt
  generalize Param.ofSplitCode? row.split = code
  cases code with
  | none => exact .isFalse (by simp)
  | some p => exact decidable_of_iff (row.ValidSplitParamAt get size p) (by simp)

def HasIntervalsAt (get : ℕ → Row) (size start : ℕ) (intervals : List Interval) : Prop :=
  ∀ i : Fin intervals.length,
    start + i.val < size ∧ (get (start + i.val)).interval = intervals[i]
deriving Decidable

def Row.ValidFullSplitAt (get : ℕ → Row) (size : ℕ) (row : Row) : Prop :=
  row.nrChildren = 32 ∧ row.split = 6 ∧ row.IDfirstChild > row.ID ∧
  HasIntervalsAt get size row.IDfirstChild
    (cubeFold [Interval.lower_half, Interval.upper_half] row.interval Param.splitOrder)
deriving Decidable

def Row.ValidSplitAt (get : ℕ → Row) (size : ℕ) (row : Row) : Prop :=
  (row.nodeType = (3 : ℕ)) ∧
    (row.ValidSingleParamSplitAt get size ∨ row.ValidFullSplitAt get size)
deriving Decidable

@[mk_iff]
inductive Row.ValidAt (get : ℕ → Row) (size : ℕ) (row : Row) : Prop where
  | asSplit : row.ValidSplitAt get size → Row.ValidAt get size row
  | asGlobal : row.ValidGlobal → Row.ValidAt get size row
  | asLocal : row.ValidLocal → Row.ValidAt get size row
  | asLocal₂ : row.ValidLocal₂ → Row.ValidAt get size row

instance (get : ℕ → Row) (size : ℕ) (row : Row) : Decidable (Row.ValidAt get size row) :=
  decidable_of_iff _ (Row.validAt_iff get size row).symm

def Row.ValidIxAt (get : ℕ → Row) (size i : ℕ) : Prop :=
  (get i).ID = i ∧ (get i).ValidAt get size ∧ i < size
deriving Decidable

def RowsValidAt (get : ℕ → Row) (size : ℕ) : Prop :=
  ∀ i : Fin size, Row.ValidIxAt get size i

/-- The minimum endpoint of an `Interval`, viewed as a `Pose ℝ` via `Rat.cast`. -/
def Interval.minPose (iv : Interval) : Pose ℝ := iv.min.toReal

/-- The maximum endpoint of an `Interval`, viewed as a `Pose ℝ` via `Rat.cast`. -/
def Interval.maxPose (iv : Interval) : Pose ℝ := iv.max.toReal

lemma Interval.minPose_le_maxPose (iv : Interval) :
    iv.minPose ≤ iv.maxPose := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := (Pose.le_iff iv.min iv.max).mp iv.fst_le_snd
  rw [Pose.le_iff]
  simp only [Interval.minPose, Interval.maxPose, Pose.toReal]
  norm_cast

def Interval.toReal (iv : Interval) : PoseInterval ℝ :=
  PoseInterval.mk iv.minPose iv.maxPose (Interval.minPose_le_maxPose iv)

def Row.toRealInterval (row : Row) : PoseInterval ℝ :=
  row.interval.toReal

/-- Each component of `iv.toReal.center` (real) is the `Rat.cast` of the corresponding
`iv.center` (rational). -/
lemma Interval.toReal_center_getParam (iv : Interval) (p : Param) :
    iv.toReal.center.getParam p = ((iv.center p : ℚ) : ℝ) := by
  cases p <;>
    simp [Interval.toReal, Interval.minPose, Interval.maxPose, Interval.center,
          PoseInterval.center, PoseInterval.min, PoseInterval.max, Pose.getParam]

@[simp] lemma Interval.toReal_center_θ₁ (iv : Interval) :
    iv.toReal.center.θ₁ = ((iv.center .θ₁ : ℚ) : ℝ) := iv.toReal_center_getParam .θ₁
@[simp] lemma Interval.toReal_center_θ₂ (iv : Interval) :
    iv.toReal.center.θ₂ = ((iv.center .θ₂ : ℚ) : ℝ) := iv.toReal_center_getParam .θ₂
@[simp] lemma Interval.toReal_center_φ₁ (iv : Interval) :
    iv.toReal.center.φ₁ = ((iv.center .φ₁ : ℚ) : ℝ) := iv.toReal_center_getParam .φ₁
@[simp] lemma Interval.toReal_center_φ₂ (iv : Interval) :
    iv.toReal.center.φ₂ = ((iv.center .φ₂ : ℚ) : ℝ) := iv.toReal_center_getParam .φ₂
@[simp] lemma Interval.toReal_center_α (iv : Interval) :
    iv.toReal.center.α = ((iv.center .α : ℚ) : ℝ) := iv.toReal_center_getParam .α

/-- The set of poses lying in the rational interval, defined as `Set.Icc` of the
    min/max endpoints; agrees definitionally with `iv.toReal`. -/
noncomputable
instance : Coe Interval (Set (Pose ℝ)) where
  coe iv := Set.Icc iv.minPose iv.maxPose

structure ValidTable : Type where
  get : ℕ → Row
  size : ℕ
  rows_valid : RowsValidAt get size
  nonempty : 0 < size
  contains_tightInterval :
    (tightInterval : Set (Pose ℝ)) ⊆ ((get 0).interval : Set (Pose ℝ))

lemma cube_fold_nonempty_aux {α β : Type} {fs : List (α → β → β)} (hfs : fs ≠ []) (b : β) (as : List α) :
   0 < (cubeFold fs b as).length := by
  match as with
  | [] => simp [cubeFold]
  | h :: tl =>
    simp only [cubeFold, List.length_flatMap]
    have (f : α → β → β) : 0 < (cubeFold fs (f h b) tl).length := by
      exact cube_fold_nonempty_aux hfs (f h b) tl
    refine List.sum_pos _ ?_ (by simpa using hfs)
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨f, hf1, hf2⟩ := hx
    rw [← hf2]
    exact this f

lemma cube_fold_nonempty {α β : Type} {fs : List (α → β → β)} (hfs : fs ≠ []) (b : β) (as : List α) :
   1 ≤ (cubeFold fs b as).length := cube_fold_nonempty_aux hfs b as

lemma cube_fold_halves (h : Param) (tl : List Param) (iv : Interval)
    (lower : Param → Interval → Interval)
    (upper : Param → Interval → Interval) :
    cubeFold [lower, upper] iv (h :: tl) =
      cubeFold [lower, upper] (lower h iv) tl ++
      cubeFold [lower, upper] (upper h iv) tl := by
  simp [cubeFold]

lemma has_intervals_start_in_table (get : ℕ → Row) (size n : ℕ) (ivs : List Interval)
    (hivs : 1 ≤ ivs.length) (hi : HasIntervalsAt get size n ivs) : n < size := by
  unfold HasIntervalsAt at hi
  simpa using (hi ⟨0, Nat.zero_lt_of_lt hivs⟩).1

lemma has_intervals_concat (get : ℕ → Row) (size start : ℕ) (ivs1 ivs2 : List Interval) :
    HasIntervalsAt get size start (ivs1 ++ ivs2) ↔
    HasIntervalsAt get size start ivs1 ∧
      HasIntervalsAt get size (start + ivs1.length) ivs2 := by
  constructor
  · intro hi
    constructor
    · unfold HasIntervalsAt at hi ⊢
      intro i; simpa using hi (Fin.castLE (by simp) i)
    · unfold HasIntervalsAt at hi ⊢
      intro i
      specialize hi ⟨ivs1.length + i, by simp⟩
      simp at hi
      obtain ⟨h, p⟩ := hi
      replace h : start + ivs1.length + (↑i : ℕ) < size :=
        by ring_nf at h ⊢; exact h
      exact ⟨h, by ring_nf at p ⊢; exact p⟩
  · rintro ⟨h1, h2⟩
    unfold HasIntervalsAt at h1 h2 ⊢
    intro i
    if h : i < ivs1.length then
      specialize h1 ⟨i, h⟩
      simp_all
    else
      replace h := Nat.le_of_not_lt h
      have : (i : ℕ) - ivs1.length < ivs2.length := by grind
      specialize h2 ⟨(i : ℕ) - ivs1.length, this⟩
      simp_all

end Noperthedron.Solution
end
