module

public import Noperthedron.SolutionTable.Basic
public import Noperthedron.SolutionTable.Local
public import Noperthedron.SolutionTable.Global
public import Noperthedron.Vertices.Exact

public section


namespace Noperthedron.Solution

/-- Membership in the realification of a rational `Interval`, read off one parameter
at a time. This is the single entry point for interval-membership reasoning below. -/
lemma mem_toReal_iff {q : Pose ℝ} {iv : Interval} :
    q ∈ iv.toReal ↔
      ∀ p : Param, q.getParam p ∈ Set.Icc (iv.min.getParam p : ℝ) (iv.max.getParam p : ℝ) := by
  show q ∈ Set.Icc iv.minPose iv.maxPose ↔ _
  simp only [Set.mem_Icc, Pose.le_iff_forall_getParam, Interval.minPose, Interval.maxPose,
    Pose.toReal_getParam, ← forall_and]

lemma mem_nth_part (q : Pose ℝ) (iv : Interval) (p : Param) (N : ℕ) [hN : NeZero N] (n : Fin N)
    (hq : q ∈ iv.toReal)
    (bound : q.getParam p ∈ Set.Icc (iv.interpolate p N n : ℝ) (iv.interpolate p N (n + 1) : ℝ)) :
    q ∈ (iv.nth_part p N n).toReal := by
  rw [mem_toReal_iff] at hq ⊢
  intro p'
  rcases eq_or_ne p' p with rfl | hne
  · simpa [Interval.nth_part, PoseInterval.min, PoseInterval.max] using bound
  · simpa [Interval.nth_part, PoseInterval.min, PoseInterval.max, hne] using hq p'

/-- Discrete intermediate value: a point lying between the first and last terms of a
finite sequence lies between some pair of consecutive terms. (No monotonicity needed.) -/
lemma exists_mem_Icc_consecutive (c : ℕ → ℝ) (M : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (c 0) (c (M + 1))) :
    ∃ n : Fin (M + 1), x ∈ Set.Icc (c n) (c (n + 1)) := by
  induction M with
  | zero => exact ⟨0, hx⟩
  | succ M ih =>
    rcases le_total x (c (M + 1)) with h | h
    · obtain ⟨n, hn⟩ := ih ⟨hx.1, h⟩
      exact ⟨n.castSucc, hn⟩
    · exact ⟨Fin.last (M + 1), h, hx.2⟩

lemma mem_interval_imp_mem_some_part (q : Pose ℝ) (iv : Interval) (p : Param)
     (N : ℕ) [NeZero N] (hq : q ∈ iv.toReal) :
     ∃ n : Fin N, q ∈ (iv.nth_part p N n).toReal := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  have h0 : iv.interpolate p (M + 1) 0 = iv.min.getParam p := by
    simp [Interval.interpolate]
  have h1 : iv.interpolate p (M + 1) (M + 1) = iv.max.getParam p := by
    simp [Interval.interpolate, div_self (by positivity : ((M : ℚ) + 1) ≠ 0)]
  obtain ⟨n, hn⟩ := exists_mem_Icc_consecutive
    (fun k => (iv.interpolate p (M + 1) k : ℝ)) M
    (by simpa only [h0, h1] using mem_toReal_iff.mp hq p)
  exact ⟨n, mem_nth_part q iv p (M + 1) n hq hn⟩

lemma non_rupert_parts_imp_non_rupert (p : Param) {iv : Interval} (N : ℕ) [hN : NeZero N]
    (qq : ∀ n : Fin N, ¬∃ q ∈ (Interval.nth_part p iv N n).toReal, RupertPose q exactPolyhedron.hull) :
    ¬∃ q ∈ iv.toReal, RupertPose q exactPolyhedron.hull := by
  rintro ⟨q, hq1, hq2⟩
  obtain ⟨n, hq1⟩ := mem_interval_imp_mem_some_part q iv p N hq1
  exact qq n ⟨q, hq1, hq2⟩

/-- Since the two halves are `nth_part 2 0` and `nth_part 2 1`, this is
`non_rupert_parts_imp_non_rupert` at `N = 2`. Used in the cube-fold part of the proof below. -/
lemma non_rupert_halves_imp_non_rupert {p : Param} {iv : Interval}
    (q1 : ¬∃ q ∈ (Interval.lower_half p iv).toReal, RupertPose q exactPolyhedron.hull)
    (q2 : ¬∃ q ∈ (Interval.upper_half p iv).toReal, RupertPose q exactPolyhedron.hull) :
    ¬∃ q ∈ iv.toReal, RupertPose q exactPolyhedron.hull := by
  refine non_rupert_parts_imp_non_rupert p 2 fun n => ?_
  fin_cases n
  · exact q1
  · exact q2

/-
This is a decently big mutual induction over several predicates establishing the validity of our interval checking.
-/
mutual

theorem has_intervals_imp_no_rupert (get : ℕ → Row) (size : ℕ)
    (rowsValid : RowsValidAt get size) (n : ℕ) (interval : Interval) (params : List Param)
    (hi : HasIntervalsAt get size n
      (cubeFold [Interval.lower_half, Interval.upper_half] interval params)) :
    ¬ ∃ q ∈ interval.toReal, RupertPose q exactPolyhedron.hull := by
  match params with
  | [] =>
    simp only [cubeFold, HasIntervalsAt] at hi
    specialize hi ⟨0, by simp⟩
    simp only [add_zero, List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta,
      Fin.isValue, Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero] at hi
    obtain ⟨hn, he⟩ := hi
    change ¬∃ q ∈ interval.toReal, RupertPose q exactPolyhedron.hull
    rw [← he]
    exact Row.valid_imp_not_rupert_ix get size rowsValid n hn
  | h::tl =>
    rw [cube_fold_halves, has_intervals_concat] at hi
    obtain ⟨h1, h2⟩ := hi
    obtain q1 := has_intervals_imp_no_rupert get size rowsValid _ _ tl h1
    obtain q2 := has_intervals_imp_no_rupert get size rowsValid _ _ tl h2
    exact non_rupert_halves_imp_non_rupert q1 q2
termination_by (size - n, 4, params.length)
decreasing_by
  · right; left; norm_num
  · right; right; simp only [List.length_cons, lt_add_iff_pos_right, zero_lt_one]
  · left;
    gcongr;
    · refine has_intervals_start_in_table get size n _ ?_ h1
      apply cube_fold_nonempty (hfs := by simp)
    · grw [← cube_fold_nonempty (hfs := by simp)];
      exact lt_add_one n

theorem Row.valid_imp_not_rupert_ix
    (get : ℕ → Row) (size : ℕ) (rowsValid : RowsValidAt get size)
    (i : ℕ) (hi : i < size) :
    ¬ ∃ q ∈ (get i).interval.toReal, RupertPose q exactPolyhedron.hull := by
  obtain ⟨rowID, rowValid, _⟩ := rowsValid ⟨i, hi⟩
  have rowID' : (get i).ID = i := rowID
  have rowLt : (get i).ID < size := by omega
  rcases rowValid with split | global | localRow | localRow₂
  · exact valid_split_imp_no_rupert get size rowsValid (get i) split rowLt
  · exact valid_global_imp_no_rupert (get i) global
  · exact valid_local_imp_no_rupert (get i) localRow
  · exact valid_local₂_imp_no_rupert (get i) localRow₂
termination_by (size - i, 3, 0)
decreasing_by rw [rowID']; grind

theorem valid_split_imp_no_rupert (get : ℕ → Row) (size : ℕ)
    (rowsValid : RowsValidAt get size) (row : Row)
    (hr : row.ValidSplitAt get size) (hlt : row.ID < size) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  obtain ⟨_, hr⟩ := hr
  rcases hr with hr' | ⟨_, _, hgt, hr'⟩
  · exact valid_single_param_split_imp_no_rupert get size rowsValid row hr'
  · exact valid_full_split_imp_no_rupert get size rowsValid row hgt hlt hr'
termination_by (size - row.ID, 2, 0)

theorem valid_single_param_split_imp_no_rupert (get : ℕ → Row) (size : ℕ)
    (rowsValid : RowsValidAt get size) (row : Row)
    (hr : Row.ValidSingleParamSplitAt get size row) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  obtain ⟨p, -, h⟩ := hr
  exact valid_param_split_imp_no_rupert get size rowsValid row p h
termination_by (size - row.ID, 1, 0)

theorem valid_full_split_imp_no_rupert (get : ℕ → Row) (size : ℕ)
    (rowsValid : RowsValidAt get size) (row : Row)
    (_hgt : row.ID < row.IDfirstChild)
    (_hlt : row.ID < size)
    (hi : HasIntervalsAt get size row.IDfirstChild
      (cubeFold [Interval.lower_half, Interval.upper_half] row.interval Param.splitOrder)) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  exact has_intervals_imp_no_rupert get size rowsValid row.IDfirstChild row.interval _ hi
termination_by (size - row.ID, 1, 0)
decreasing_by left; exact Nat.sub_lt_sub_left _hlt _hgt

theorem valid_param_split_imp_no_rupert (get : ℕ → Row) (size : ℕ)
    (rowsValid : RowsValidAt get size) (row : Row)
    (p : Param) (h : Row.ValidSplitParamAt get size row p) :
    ¬∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  obtain ⟨hid, hkids, hnzk, hkiv⟩ := h
  refine non_rupert_parts_imp_non_rupert p row.nrChildren (hN := ⟨hnzk⟩) ?_
  intro n
  rw [← hkiv n]
  clear hkiv hnzk
  refine Row.valid_imp_not_rupert_ix get size rowsValid (row.IDfirstChild + n) ?_
  grind

termination_by (size - row.ID, 0, 0)
decreasing_by all_goals grind

end

theorem Row.valid_imp_not_rupert
    (get : ℕ → Row) (size : ℕ) (rowsValid : RowsValidAt get size)
    (hz : 0 < size) :
    ¬ ∃ q ∈ (get 0).interval.toReal, RupertPose q exactPolyhedron.hull :=
  Row.valid_imp_not_rupert_ix get size rowsValid 0 hz

end Noperthedron.Solution

end
