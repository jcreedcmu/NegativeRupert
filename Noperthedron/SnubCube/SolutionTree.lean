module

public import Noperthedron.SnubCube.Certificate
public import Noperthedron.SnubCube.FundamentalPrune
public import Noperthedron.SnubCube.LocalCertificate
public import Noperthedron.SolutionTable.Defs

@[expose] public section


/-!
# Flat checked solution trees for the snub cube

Rows are either binary interval splits or one of three sound certificate
leaf types.  Validity is parameterized by a total row getter, so generated
data can use a fast runtime array for `native_decide` and chunked literal
functions for kernel checking without changing the mathematical theorem.
-/

namespace Noperthedron.SnubCube.SolutionTree

open Noperthedron.Solution

abbrev Interval := PoseInterval ℚ

/-- Realification shared by split rows and both certificate leaf types. -/
def Interval.toReal (iv : Interval) : PoseInterval ℝ :=
  PoseInterval.mk iv.min.toReal iv.max.toReal (by
    obtain ⟨h1, h2, h3, h4, h5⟩ := (Pose.le_iff _ _).mp iv.min_le_max
    rw [Pose.le_iff]
    simp only [Pose.toReal_θ₁, Pose.toReal_θ₂, Pose.toReal_φ₁,
      Pose.toReal_φ₂, Pose.toReal_α]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2,
      by exact_mod_cast h3, by exact_mod_cast h4, by exact_mod_cast h5⟩)

lemma mem_toReal_iff {q : Pose ℝ} {iv : Interval} :
    q ∈ Interval.toReal iv ↔ ∀ p : Param,
      q.getParam p ∈ Set.Icc (iv.min.getParam p : ℝ)
        (iv.max.getParam p : ℝ) := by
  simp only [Interval.toReal, NonemptyInterval.mem_def,
    Pose.le_iff_forall_getParam, Pose.toReal_getParam, Set.mem_Icc,
    ← forall_and]

lemma mem_nth_part (q : Pose ℝ) (iv : Interval) (p : Param)
    (N : ℕ) [hN : NeZero N] (n : Fin N) (hq : q ∈ Interval.toReal iv)
    (bound : q.getParam p ∈ Set.Icc
      (Noperthedron.Solution.Interval.interpolate p iv N n : ℝ)
      (Noperthedron.Solution.Interval.interpolate p iv N (n + 1) : ℝ)) :
    q ∈ Interval.toReal
      (Noperthedron.Solution.Interval.nth_part p iv N n) := by
  rw [mem_toReal_iff] at hq ⊢
  intro p'
  rcases eq_or_ne p' p with rfl | hne
  · simpa [Noperthedron.Solution.Interval.nth_part,
      PoseInterval.min, PoseInterval.max] using bound
  · simpa [Noperthedron.Solution.Interval.nth_part,
      PoseInterval.min, PoseInterval.max, hne] using hq p'

private lemma exists_mem_Icc_consecutive (c : ℕ → ℝ) (M : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (c 0) (c (M + 1))) :
    ∃ n : Fin (M + 1), x ∈ Set.Icc (c n) (c (n + 1)) := by
  induction M with
  | zero => exact ⟨0, hx⟩
  | succ M ih =>
    rcases le_total x (c (M + 1)) with h | h
    · obtain ⟨n, hn⟩ := ih ⟨hx.1, h⟩
      exact ⟨n.castSucc, hn⟩
    · exact ⟨Fin.last (M + 1), h, hx.2⟩

lemma mem_interval_imp_mem_some_part (q : Pose ℝ) (iv : Interval)
    (p : Param) (N : ℕ) [NeZero N] (hq : q ∈ Interval.toReal iv) :
    ∃ n : Fin N,
      q ∈ Interval.toReal
        (Noperthedron.Solution.Interval.nth_part p iv N n) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  have h0 : Noperthedron.Solution.Interval.interpolate p iv (M + 1) 0 =
      iv.min.getParam p := by
    simp [Noperthedron.Solution.Interval.interpolate]
  have h1 : Noperthedron.Solution.Interval.interpolate p iv (M + 1) (M + 1) =
      iv.max.getParam p := by
    simp [Noperthedron.Solution.Interval.interpolate,
      div_self (by positivity : ((M : ℚ) + 1) ≠ 0)]
  obtain ⟨n, hn⟩ := exists_mem_Icc_consecutive
    (fun k => (Noperthedron.Solution.Interval.interpolate p iv (M + 1) k : ℝ)) M
    (by simpa only [h0, h1] using mem_toReal_iff.mp hq p)
  exact ⟨n, mem_nth_part q iv p (M + 1) n hq hn⟩

def NoRupert (iv : Interval) : Prop :=
  ¬ ∃ q ∈ Interval.toReal iv, ∃ offset : ℝ²,
    (q.matrixPoseWithOffset offset).InSnubFundamentalDomain ∧
      RupertPose (q.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull

lemma noRupert_parts (p : Param) (iv : Interval) (N : ℕ) [NeZero N]
    (h : ∀ n : Fin N,
      NoRupert (Noperthedron.Solution.Interval.nth_part p iv N n)) :
    NoRupert iv := by
  rintro ⟨q, hq, offset, hfund, hrupert⟩
  obtain ⟨n, hn⟩ := mem_interval_imp_mem_some_part q iv p N hq
  exact h n ⟨q, hn, offset, hfund, hrupert⟩

lemma noRupert_halves (p : Param) (iv : Interval)
    (hlower : NoRupert (Noperthedron.Solution.Interval.lower_half p iv))
    (hupper : NoRupert (Noperthedron.Solution.Interval.upper_half p iv)) :
    NoRupert iv := by
  apply noRupert_parts p iv 2
  intro n
  fin_cases n
  · simpa [Noperthedron.Solution.Interval.lower_half] using hlower
  · simpa [Noperthedron.Solution.Interval.upper_half] using hupper

inductive Row where
  | split (id lowerChild upperChild : ℕ) (param : Param) (interval : Interval)
  | global (id : ℕ) (box : Certificate.Box)
  | localLeaf (id : ℕ) (box : LocalCertificate.Box)
  | prune (id : ℕ) (box : FundamentalPrune.Box)

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
  default := .split 0 0 0 .θ₁
    (PoseInterval.mk
      { θ₁ := 0, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := 0 }
      { θ₁ := 0, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := 0 } (by rfl))

def Row.ValidAt (get : ℕ → Row) (size : ℕ) : Row → Prop
  | .split id lowerChild upperChild param interval =>
      id < lowerChild ∧ id < upperChild ∧
      lowerChild < size ∧ upperChild < size ∧
      (get lowerChild).interval =
        Noperthedron.Solution.Interval.lower_half param interval ∧
      (get upperChild).interval =
        Noperthedron.Solution.Interval.upper_half param interval
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

private theorem global_realInterval (box : Certificate.Box) :
    box.realInterval = Interval.toReal box.interval := by
  rfl

private theorem local_realInterval (box : LocalCertificate.Box) :
    box.realInterval = Interval.toReal box.interval := by
  rfl

private theorem prune_realInterval (box : FundamentalPrune.Box) :
    box.realInterval = Interval.toReal box.interval := by
  rfl

theorem valid_imp_noRupert_ix (get : ℕ → Row) (size : ℕ)
    (rowsValid : RowsValidAt get size) (i : ℕ) (hi : i < size) :
    NoRupert (get i).interval := by
  obtain ⟨hid, hvalid⟩ := rowsValid ⟨i, hi⟩
  generalize hrow : get i = row at hid hvalid ⊢
  cases row with
  | global id box =>
      unfold NoRupert
      change ¬ ∃ q ∈ Interval.toReal box.interval, ∃ offset : ℝ²,
        (q.matrixPoseWithOffset offset).InSnubFundamentalDomain ∧
          RupertPose (q.matrixPoseWithOffset offset)
            normalizedExactPolyhedron.hull
      rw [← global_realInterval]
      rintro ⟨q, hq, offset, -, hrupert⟩
      exact Certificate.valid_imp_no_translated_rupert_in_interval box hvalid
        ⟨q, hq, offset, hrupert⟩
  | localLeaf id box =>
      unfold NoRupert
      change ¬ ∃ q ∈ Interval.toReal box.interval, ∃ offset : ℝ²,
        (q.matrixPoseWithOffset offset).InSnubFundamentalDomain ∧
          RupertPose (q.matrixPoseWithOffset offset)
            normalizedExactPolyhedron.hull
      rw [← local_realInterval]
      rintro ⟨q, hq, offset, -, hrupert⟩
      exact LocalCertificate.valid_imp_no_translated_rupert_in_interval box hvalid
        ⟨q, hq, offset, hrupert⟩
  | prune id box =>
      unfold NoRupert
      change ¬ ∃ q ∈ Interval.toReal box.interval, ∃ offset : ℝ²,
        (q.matrixPoseWithOffset offset).InSnubFundamentalDomain ∧
          RupertPose (q.matrixPoseWithOffset offset)
            normalizedExactPolyhedron.hull
      rw [← prune_realInterval]
      rintro ⟨q, hq, offset, hfund, -⟩
      exact FundamentalPrune.Box.valid_imp_not_inFundamentalDomain
        box hvalid hq offset hfund
  | split id lowerChild upperChild param interval =>
      obtain ⟨hlower, hupper, hlowerSize, hupperSize,
        hlowerInterval, hupperInterval⟩ := hvalid
      apply noRupert_halves param interval
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

/-- Rational version of the exact fundamental-domain root box. -/
def fundamentalPoseIntervalQ : Interval :=
  PoseInterval.mk
    { θ₁ := -4, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := -4 }
    { θ₁ := 4, θ₂ := 2, φ₁ := 4, φ₂ := 2, α := 4 }
    (by rw [Pose.le_iff]; norm_num)

theorem fundamentalPoseIntervalQ_toReal :
    Interval.toReal fundamentalPoseIntervalQ = fundamentalPoseInterval := by
  ext <;> norm_num [Interval.toReal, fundamentalPoseIntervalQ,
    fundamentalPoseInterval, Pose.toReal]

structure ValidTable where
  get : ℕ → Row
  size : ℕ
  nonempty : 0 < size
  rowsValid : RowsValidAt get size
  root_interval : (get 0).interval = fundamentalPoseIntervalQ

theorem ValidTable.no_fundamental_translated_rupert (table : ValidTable) :
    ¬ ∃ q ∈ fundamentalPoseInterval, ∃ offset : ℝ²,
      (q.matrixPoseWithOffset offset).InSnubFundamentalDomain ∧
        RupertPose (q.matrixPoseWithOffset offset)
          normalizedExactPolyhedron.hull := by
  have hroot := valid_imp_noRupert_ix table.get table.size table.rowsValid 0
    table.nonempty
  rw [table.root_interval, NoRupert, fundamentalPoseIntervalQ_toReal] at hroot
  exact hroot

theorem ValidTable.no_matrixPose (table : ValidTable) :
    ¬ ∃ p : MatrixPose,
      RupertPose p normalizedExactPolyhedron.hull :=
  no_matrixPose_of_no_fundamental_translated_pose
    table.no_fundamental_translated_rupert

end Noperthedron.SnubCube.SolutionTree

end
