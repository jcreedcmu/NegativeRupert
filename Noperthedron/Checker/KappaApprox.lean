module

public import Noperthedron.Checker.Global
public import Noperthedron.RationalApprox.Basic
public import Noperthedron.RationalApprox.TrigLemmas
public import Noperthedron.Vertices.Exact
public import Noperthedron.Vertices.Taylor
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section


/-!
# κ-Approximation of Noperthedron Vertices

Proves that the hard-coded rational vertices (`pythonVertex` in
`Noperthedron/Vertices/Python.lean`) are within distance κ = 10⁻¹⁰ of the
real noperthedron vertices (`exactVertex`).
-/

open RationalApprox Noperthedron.Solution Real
open scoped Nat

namespace Noperthedron.KappaApprox

-- Extract concrete rational values of pythonVertex 0
private lemma nlq0_0 : pythonVertex 0 0 = (5861195714524832 : ℚ) / 10000000000000000 := by
  decide +kernel
private lemma nlq0_1 : pythonVertex 0 1 = 0 := by decide +kernel
private lemma nlq0_2 : pythonVertex 0 2 = (8102245663767282 : ℚ) / 10000000000000000 := by
  decide +kernel

/-- The ℝ³ norm of the difference between the first rational vertex
    and C1R is at most κ. -/
lemma first_vertex_close :
    ‖(WithLp.toLp 2 (fun i => (pythonVertex 0 i : ℝ)) : ℝ³) - C1R‖ ≤ κ := by
  have hκ : (0 : ℝ) ≤ κ := by unfold κ; positivity
  rw [EuclideanSpace.norm_eq]
  calc sqrt (∑ i : Fin 3, ‖(WithLp.toLp 2 (fun i => (pythonVertex 0 i : ℝ)) - C1R) i‖ ^ 2)
      ≤ sqrt (κ ^ 2) := by
        apply sqrt_le_sqrt
        simp only [norm_eq_abs, sq_abs, Fin.sum_univ_three]
        show ((↑(pythonVertex 0 0) : ℝ) - C1R 0) ^ 2 +
             ((↑(pythonVertex 0 1) : ℝ) - C1R 1) ^ 2 +
             ((↑(pythonVertex 0 2) : ℝ) - C1R 2) ^ 2 ≤ κ ^ 2
        simp only [nlq0_0, nlq0_1, nlq0_2]
        unfold C1R C1 κ
        simp only [Pi.mul_apply, Matrix.cons_val]
        norm_num
    _ = κ := sqrt_sq hκ

/-! ## General case infrastructure -/

/-- π exceeds our rational approximation. -/
lemma piQ_lt_pi : (piQ : ℝ) < π := pi_gt_d20

/-- π is within 10⁻²⁰ of our rational approximation. -/
lemma pi_sub_piQ_lt : π - (piQ : ℝ) < 1 / 10 ^ 20 := by
  have h := pi_lt_d20  -- π < 3.14159265358979323847
  -- 3.14159265358979323847 = piQ + 1/10^20
  have : (3.14159265358979323847 : ℝ) = (piQ : ℝ) + 1 / 10 ^ 20 := by norm_num [piQ]
  linarith

/-! ## sinQ/cosQ agreement with the raw partial sums

`sinQ`/`cosQ` (Horner form, used for the exact-vertex validation) stay
*unrounded*: they agree with `sin_psum 13`/`cos_psum 13` exactly, not with the
`round13`-rounded `sinℚ`/`cosℚ` used for pose trigonometry. -/

/-- The computable Horner-form `sinQ` agrees with the raw partial sum. -/
theorem sinQ_eq_sin_psum (x : ℚ) : sinQ x = sin_psum 13 x := by
  simp only [sinQ, sin_psum, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- The computable Horner-form `cosQ` agrees with the raw partial sum. -/
theorem cosQ_eq_cos_psum (x : ℚ) : cosQ x = cos_psum 13 x := by
  simp only [cosQ, cos_psum, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- sinQ at a rational x, cast to ℝ, equals the raw partial sum at the cast argument. -/
theorem sinQ_cast (x : ℚ) : (sinQ x : ℝ) = sin_psum 13 (x : ℝ) := by
  rw [sinQ_eq_sin_psum]
  unfold sin_psum; push_cast; rfl

/-- cosQ at a rational x, cast to ℝ, equals the raw partial sum at the cast argument. -/
theorem cosQ_cast (x : ℚ) : (cosQ x : ℝ) = cos_psum 13 (x : ℝ) := by
  rw [cosQ_eq_cos_psum]
  unfold cos_psum; push_cast; rfl

/-- Taylor remainder bound: |sin(x) - ↑(sinQ q)| ≤ |x|^27/27! when x = ↑q. -/
theorem sinQ_approx (q : ℚ) : |Real.sin q - (sinQ q : ℝ)| ≤ |↑q| ^ 27 / 27! := by
  rw [sinQ_cast]; exact sin_psum_approx (q : ℝ) 13

/-- Taylor remainder bound: |cos(x) - ↑(cosQ q)| ≤ |x|^26/26! when x = ↑q. -/
theorem cosQ_approx (q : ℚ) : |Real.cos q - (cosQ q : ℝ)| ≤ |↑q| ^ 26 / 26! := by
  rw [cosQ_cast]; exact cos_psum_approx (q : ℝ) 13

/-! ## Left-leg validation: k > 0 vertex -/

/-- Left-leg squared distance for ALL 90 vertices.
    The hard-coded `pythonVertex` agrees with the Taylor-polynomial
    `taylorVertex` to within squared distance κ² = 10⁻²⁰ per vertex. -/
lemma left_leg_all :
    ∀ j : VertexIndex,
    (pythonVertex j 0 - taylorVertex j 0) ^ 2 +
    (pythonVertex j 1 - taylorVertex j 1) ^ 2 +
    (pythonVertex j 2 - taylorVertex j 2) ^ 2 ≤
    (1 : ℚ) / 10 ^ 28 := by
  decide +kernel

/-! ## Right-leg bound: nopertListℚ vs nopertList -/

/-- The reduced angle index k' satisfies k' ≤ 7. -/
private lemma reduced_le_seven (k : ℕ) (hk : k < 15) :
    (if k ≤ 7 then (k : ℚ) else k - 15) ≤ 7 := by
  norm_cast
  lia

/-- The reduced angle index k' satisfies 0 ≤ k'. -/
private lemma reduced_ge_neg_seven (k : ℕ) :
    -7 ≤ (if k ≤ 7 then (k : ℚ) else k - 15) := by
  norm_cast; lia

/-- The rational angle 2·piQ·k'/15 has absolute value < 3 when k' ≤ 7. -/
private lemma piQ_angle_abs_lt_three (k' : ℚ) (hkn : -7 ≤ k') (hk : k' ≤ 7) :
    |(2 * piQ * k' / 15 : ℚ)| < 3 := by
  rw [abs_lt]
  constructor
  · unfold piQ
    calc (-3 : ℚ) < 2 * 3.14159265358979323846 * (-7) / 15 := by norm_num
                _ ≤ 2 * 3.14159265358979323846 * k' / 15 := by gcongr
  · have : (k' : ℚ) ≤ 7 := by exact_mod_cast hk
    unfold piQ
    calc 2 * 3.14159265358979323846 * (k' : ℚ) / 15
        ≤ 2 * 3.14159265358979323846 * 7 / 15 := by gcongr
      _ < 3 := by norm_num

/-- Combined trig error for cosQ at a reduced rational angle vs cos at the real angle. -/
private lemma cosQ_combined_error (k : Fin 15) :
    |↑(cosQ (2 * piQ * (if k ≤ 7 then (k : ℚ) else k - 15) / 15)) -
       Real.cos (2 * π * k / 15)| ≤ κ / 7 := by
  set k' : ℚ := if k ≤ 7 then k else k - 15 with hk'_def
  have hk'_ge : -7 ≤ k' := reduced_ge_neg_seven k
  have hk'_le : k' ≤ 7 := reduced_le_seven k k.2
  set q : ℚ := 2 * piQ * k' / 15 with hq_def
  have hq_eq : (↑q : ℝ) = 2 * (piQ : ℝ) * (k' : ℝ) / 15 := by
    simp only [hq_def]; push_cast; ring
  have hcos_eq : Real.cos (2 * π * ↑↑k / 15) = Real.cos (2 * π * (k' : ℝ) / 15) := by
    simp only [hk'_def]; split_ifs with h
    · norm_cast
    · push_cast
      rw [show 2 * π * ((↑↑k : ℝ) - 15) / 15 = 2 * π * ↑↑k / 15 - 2 * π from by ring]
      exact (cos_sub_two_pi _).symm
  rw [hcos_eq]
  have taylor := cosQ_approx q
  have mvt : |Real.cos ↑q - Real.cos (2 * π * (k' : ℝ) / 15)| ≤
      |↑q - 2 * π * (k' : ℝ) / 15| := abs_cos_sub_cos_le _ _
  have hpi_pos : 0 ≤ π - (piQ : ℝ) := le_of_lt (sub_pos.mpr piQ_lt_pi)
  have habs : |(↑q : ℝ)| < 3 := mod_cast piQ_angle_abs_lt_three k' hk'_ge hk'_le
  have hk_abs : |(k' : ℝ)| ≤ 7 := by
    rw [abs_le]; exact ⟨mod_cast hk'_ge, mod_cast hk'_le⟩
  have hdiff : |↑q - 2 * π * (k' : ℝ) / 15| ≤ 14 / 15 * (1 / 10 ^ 20) := by
    rw [hq_eq, show 2 * (piQ : ℝ) * (k' : ℝ) / 15 - 2 * π * (k' : ℝ) / 15 =
        -(2 * (k' : ℝ) / 15 * (π - (piQ : ℝ))) from by ring, abs_neg, abs_mul, abs_div, abs_mul]
    rw [abs_of_nonneg hpi_pos]
    grw [hk_abs]
    gcongr <;> (norm_num; try linarith [pi_sub_piQ_lt])
  calc |(↑(cosQ q) : ℝ) - Real.cos (2 * π * (k' : ℝ) / 15)|
      = |(↑(cosQ q) - Real.cos ↑q) + (Real.cos ↑q - Real.cos (2 * π * (k' : ℝ) / 15))| := by
        congr 1; ring
    _ ≤ |↑(cosQ q) - Real.cos ↑q| + |Real.cos ↑q - Real.cos (2 * π * (k' : ℝ) / 15)| :=
        abs_add_le _ _
    _ ≤ |(↑q : ℝ)| ^ 26 / 26! + |↑q - 2 * π * (k' : ℝ) / 15| :=
        add_le_add (by rw [abs_sub_comm]; exact taylor) mvt
    _ ≤ 3 ^ 26 / 26! + (14 / 15 * (1 / 10 ^ 20)) := by gcongr
    _ ≤ κ / 7 := by norm_num [κ]

/-- Same bound for sinQ. -/
private lemma sinQ_combined_error (k : Fin 15) :
    |↑(sinQ (2 * piQ * (if k ≤ 7 then (k : ℚ) else k - 15) / 15)) -
      Real.sin (2 * π * k / 15)| ≤ κ / 7 := by
  set k' : ℚ := if k ≤ 7 then k else k - 15 with hk'_def
  have hk'_ge : -7 ≤ k' := reduced_ge_neg_seven k
  have hk'_le : k' ≤ 7 := reduced_le_seven k k.2
  set q : ℚ := 2 * piQ * k' / 15 with hq_def
  have hq_eq : (↑q : ℝ) = 2 * (piQ : ℝ) * (k' : ℝ) / 15 := by
    simp only [hq_def]; push_cast; ring
  have hsin_eq : Real.sin (2 * π * ↑↑k / 15) = Real.sin (2 * π * (k' : ℝ) / 15) := by
    simp only [hk'_def]; split_ifs with h
    · norm_cast
    · push_cast
      rw [show 2 * π * ((↑↑k : ℝ) - 15) / 15 = 2 * π * ↑↑k / 15 - 2 * π from by ring]
      exact (sin_sub_two_pi _).symm
  rw [hsin_eq]
  have taylor := sinQ_approx q
  have mvt : |Real.sin ↑q - Real.sin (2 * π * (k' : ℝ) / 15)| ≤
      |↑q - 2 * π * (k' : ℝ) / 15| := abs_sin_sub_sin_le _ _
  have hpi_pos : 0 ≤ π - (piQ : ℝ) := le_of_lt (sub_pos.mpr piQ_lt_pi)
  have habs : |(↑q : ℝ)| < 3 := mod_cast piQ_angle_abs_lt_three k' hk'_ge hk'_le
  have hk_abs : |(k' : ℝ)| ≤ 7 := by
    rw [abs_le]; exact ⟨mod_cast hk'_ge, mod_cast hk'_le⟩
  have hdiff : |↑q - 2 * π * (k' : ℝ) / 15| ≤ 14 / 15 * (1 / 10 ^ 20) := by
    rw [hq_eq, show 2 * (piQ : ℝ) * (k' : ℝ) / 15 - 2 * π * (k' : ℝ) / 15 =
        -(2 * (k' : ℝ) / 15 * (π - (piQ : ℝ))) from by ring, abs_neg, abs_mul, abs_div, abs_mul]
    rw [abs_of_nonneg hpi_pos]
    grw [hk_abs]
    gcongr <;> (norm_num; try linarith [pi_sub_piQ_lt])
  calc |(↑(sinQ q) : ℝ) - Real.sin (2 * π * (k' : ℝ) / 15)|
      = |(↑(sinQ q) - Real.sin ↑q) + (Real.sin ↑q - Real.sin (2 * π * (k' : ℝ) / 15))| := by
        congr 1; ring
    _ ≤ |↑(sinQ q) - Real.sin ↑q| + |Real.sin ↑q - Real.sin (2 * π * (k' : ℝ) / 15)| :=
        abs_add_le _ _
    _ ≤ |(↑q : ℝ)| ^ 27 / 27! + |↑q - 2 * π * (k' : ℝ) / 15| :=
        add_le_add (by rw [abs_sub_comm]; exact taylor) mvt
    _ ≤ 3 ^ 27 / 27! + (14 / 15 * (1 / 10 ^ 20)) := by gcongr
    _ ≤ κ / 7 := by norm_num [κ]
/-! ### Helper lemmas for right-leg bound -/

/-- `Cpt i j` (real base vertex coordinate) equals `↑(Crat i j)`. -/
private lemma Cpt_cast (i : Fin 3) (j : Fin 3) : (Cpt i) j = (↑(Crat i j) : ℝ) := by
  fin_cases i <;> fin_cases j <;> simp [Cpt, Crat, C1R, C2R, C3R, C1, C2, C3]

/-- The first two coordinates of each base vertex satisfy x² + y² ≤ 1. -/
private lemma Crat_xy_sq_le_one (i : Fin 3) :
    (↑(Crat i 0) : ℝ) ^ 2 + (↑(Crat i 1) : ℝ) ^ 2 ≤ 1 := by
  fin_cases i <;> simp [Crat, C1, C2, C3, Pi.mul_apply] <;> norm_num

/-- Angle reduction for cos: cos(2πk/15) = cos(2πk'/15) where k' is the reduced index. -/
private lemma cos_reduced_angle (k : ℕ) (hk : k < 15) :
    Real.cos (2 * π * k / 15) = Real.cos (2 * π * (if k ≤ 7 then k else 15 - k) / 15) := by
  split_ifs with h
  · rfl
  · have hk_cast : (k : ℝ) = 15 - ((15 - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : k ≤ 15)]; ring
    rw [hk_cast, show 2 * π * (15 - ↑(15 - k)) / 15 = 2 * π - 2 * π * ↑(15 - k) / 15
        from by ring]
    exact cos_two_pi_sub _

/-- Angle reduction for sin: sin(2πk/15) = ±sin(2πk'/15). -/
private lemma sin_reduced_angle (k : ℕ) (hk : k < 15) :
    Real.sin (2 * π * k / 15) =
    if k ≤ 7 then Real.sin (2 * π * (if k ≤ 7 then k else 15 - k) / 15)
    else -Real.sin (2 * π * (if k ≤ 7 then k else 15 - k) / 15) := by
  split_ifs with h
  · rfl
  · have hk_cast : (k : ℝ) = 15 - ((15 - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : k ≤ 15)]; ring
    rw [hk_cast, show 2 * π * (15 - ↑(15 - k)) / 15 = 2 * π - 2 * π * ↑(15 - k) / 15
        from by ring]
    exact sin_two_pi_sub _

/-- Components of RzL: coordinate 0. -/
private lemma RzL_apply_0 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 0 = cos θ * v 0 - sin θ * v 1 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]; ring

/-- Components of RzL: coordinate 1. -/
private lemma RzL_apply_1 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 1 = sin θ * v 0 + cos θ * v 1 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]

/-- Components of RzL: coordinate 2. -/
private lemma RzL_apply_2 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 2 = v 2 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]

private lemma R3_sub (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ) :
    !₂[x₁, y₁, z₁] - !₂[x₂, y₂, z₂] = !₂[x₁ - x₂, y₁ - y₂, z₁ - z₂] := by
  ext i; fin_cases i <;> simp

/-- The core analytical bound: each taylorVertex is within κ/2 of the corresponding exactVertex.
    Uses Taylor remainder + MVT + π bounds. The actual error is ~10⁻¹⁵, well within κ/2 = 5·10⁻¹¹.
-/
theorem taylorVertex_close (j : VertexIndex) : ‖toR3 (taylorVertex j) - exactVertex j‖ ≤ κ / 2 := by
  let ⟨k, ℓ, i⟩ := j
  -- Set up reduced angle
  set k' : ℚ := if k ≤ 7 then k.val else k.val - 15 with hk'_def
  have hk'_ge : -7 ≤ k' := reduced_ge_neg_seven k
  have hk'_le : k' ≤ 7 := reduced_le_seven k k.2
  -- Trig errors
  set ce := (↑(cosQ (2 * piQ * k' / 15)) : ℝ) - Real.cos (2 * π * k / 15) with hce_def
  set se := (↑(sinQ (2 * piQ * k' / 15)) : ℝ) - Real.sin (2 * π * k / 15) with hse_def
  have hce : |ce| ≤ κ / 7 := cosQ_combined_error k
  have hse : |se| ≤ κ / 7 := sinQ_combined_error k
  -- Base coordinates
  set a := (↑(Crat i 0) : ℝ) with ha_def
  set b := (↑(Crat i 1) : ℝ) with hb_def
  have hab : a ^ 2 + b ^ 2 ≤ 1 := Crat_xy_sq_le_one i
  -- Set up the difference vector
  set d := toR3 (taylorVertex ⟨k, ℓ, i⟩) - exactVertex ⟨k, ℓ, i⟩ with hd_def
  -- z-component is 0 (both sides use the same rational base coord)
  have hz : d 2 = 0 := by
    simp only [hd_def, toR3, taylorVertex, exactVertex]
    simp [RzL_apply_2, Cpt_cast]
  -- x,y squared norm = (ce² + se²)(a² + b²) via rotation algebra identity
  -- Both k ≤ 7 and k > 7 give the same squared norm due to cross-term cancellation
  have hsq : d 0 ^ 2 + d 1 ^ 2 = (ce ^ 2 + se ^ 2) * (a ^ 2 + b ^ 2) := by
    rw [exactVertex_eq_vec, taylorVertex_eq_vec] at hd_def
    generalize hkk : (2 * piQ * k') / 15 = kk at *
    have h₁ : toR3 ((-1) ^ ℓ.val • ![cosQ kk * Crat i 0 - sinQ kk * Crat i 1,
                                  sinQ kk * Crat i 0 + cosQ kk * Crat i 1,
                                  Crat i 2]) =
           (-1) ^ ℓ.val • !₂[cosQ kk * Cpt i 0 - sinQ kk * Cpt i 1,
                             sinQ kk * Cpt i 0 + cosQ kk * Cpt i 1,
                             Cpt i 2] := by
       simp [toR3]
       ext j; fin_cases j <;> simp [Cpt_cast, mul_add]
    rw [h₁] at hd_def; clear h₁
    rw [← smul_sub, R3_sub, sub_self, ← WithLp.toLp_smul, Matrix.smul_vec3, smul_zero] at hd_def
    rw [hd_def]
    simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, zsmul_eq_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [mul_pow, ←pow_mul]
    simp only [even_two, Even.mul_left, Even.neg_pow, one_pow, Fin.isValue, one_mul]
    simp only [hce_def, hse_def, ha_def, hb_def, Cpt_cast]; ring
  -- Norm bound via sqrt
  have hκ2 : (0 : ℝ) ≤ κ / 2 := by unfold κ; positivity
  rw [EuclideanSpace.norm_eq, ← sqrt_sq hκ2]
  apply sqrt_le_sqrt
  simp only [Fin.sum_univ_three, norm_eq_abs, sq_abs]
  -- Goal: d 0^2 + d 1^2 + d 2^2 ≤ (κ/2)^2
  have hz2 : d 2 ^ 2 = 0 := by rw [hz]; ring
  rw [hz2, add_zero, hsq]
  -- Goal: (ce^2 + se^2) * (a^2 + b^2) ≤ (κ/2)^2
  have hce_sq : ce ^ 2 ≤ (κ / 7) ^ 2 := sq_le_sq' (abs_le.mp hce).1 (abs_le.mp hce).2
  have hse_sq : se ^ 2 ≤ (κ / 7) ^ 2 := sq_le_sq' (abs_le.mp hse).1 (abs_le.mp hse).2
  calc (ce ^ 2 + se ^ 2) * (a ^ 2 + b ^ 2)
      ≤ 2 * (κ / 7) ^ 2 * 1 := mul_le_mul (by linarith) hab (by positivity) (by positivity)
    _ ≤ (κ / 2) ^ 2 := by norm_num [κ]

/-! ## Combined bound via triangle inequality -/

/-- Left-leg ℝ³ norm bound derived from the ℚ squared distance bound. -/
theorem left_leg_norm (j : VertexIndex) :
    ‖toR3 (pythonVertex j) - toR3 (taylorVertex j)‖ ≤ κ / 2 := by
  have hκ2 : (0 : ℝ) ≤ κ / 2 := by norm_num [κ]
  rw [EuclideanSpace.norm_eq, ← sqrt_sq hκ2]
  apply sqrt_le_sqrt
  simp only [Fin.sum_univ_three, norm_eq_abs, sq_abs, toR3, PiLp.sub_apply]
  norm_cast
  grw [left_leg_all j]
  norm_num [κ]

/-- The hard-coded rational vertices are within κ of the real vertices,
    for each index in [0, 90). -/
theorem vertex_close_index (j : VertexIndex) :
    ‖toR3 (pythonVertex j) - exactVertex j‖ ≤ κ := by
  calc ‖toR3 (pythonVertex j) - exactVertex j‖
      = ‖(toR3 (pythonVertex j) - toR3 (taylorVertex j)) +
         (toR3 (taylorVertex j) - exactVertex j)‖ := by
        congr 1; abel
    _ ≤ ‖toR3 (pythonVertex j) - toR3 (taylorVertex j)‖ +
        ‖toR3 (taylorVertex j) - exactVertex j‖ :=
        norm_add_le _ _
    _ ≤ κ / 2 + κ / 2 := add_le_add (left_leg_norm j) (taylorVertex_close j)
    _ = κ := by ring

def exact_κApprox_python : κApproxPoly ⟨exactVertex⟩ ⟨pythonVertex⟩ := {
  bijection := Equiv.refl _
  approx a := by
    simp only [Equiv.refl_apply]
    rw [norm_sub_rev]
    exact vertex_close_index a
}

end KappaApprox
end Noperthedron

end
