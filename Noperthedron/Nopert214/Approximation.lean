module

public import Noperthedron.Nopert214.Vertices

@[expose] public section

/-!
# The published coordinates approximate the intended Nopert #214

The exact object has fivefold rotational symmetry.  This file proves that the
decimal vertices from the published STL are within the checker's `κ = 10⁻¹⁰`
budget of that exact object.  A rational Taylor vertex is used as a bridge.
-/

open RationalApprox Real

namespace Noperthedron.Nopert214

private lemma piQ_lt_pi : (Noperthedron.piQ : ℝ) < π := pi_gt_d20

private lemma pi_sub_piQ_lt : π - (Noperthedron.piQ : ℝ) < 1 / 10 ^ 20 := by
  have h := pi_lt_d20
  have : (3.14159265358979323847 : ℝ) =
      (Noperthedron.piQ : ℝ) + 1 / 10 ^ 20 := by
    norm_num [Noperthedron.piQ]
  linarith

def reducedOrbit (k : OrbitIndex) : ℚ :=
  if k.val ≤ 2 then k.val else k.val - 5

private lemma reducedOrbit_abs_le_two (k : OrbitIndex) :
    |(reducedOrbit k : ℝ)| ≤ 2 := by
  fin_cases k <;> norm_num [reducedOrbit]

private lemma rationalAngle_mem (k : OrbitIndex) :
    ((2 * Noperthedron.piQ * reducedOrbit k / 5 : ℚ) : ℝ) ∈ Set.Icc (-4) 4 := by
  fin_cases k <;> norm_num [reducedOrbit, Noperthedron.piQ]

private lemma cos_orbit_reduced (k : OrbitIndex) :
    Real.cos (2 * π * (k : ℝ) / 5) =
      Real.cos (2 * π * (reducedOrbit k : ℝ) / 5) := by
  fin_cases k <;> simp [reducedOrbit]
  · rw [show 2 * π * (3 : ℝ) / 5 = 2 * π * (-2 : ℝ) / 5 + 2 * π by ring]
    convert Real.cos_add_two_pi (2 * π * (-2 : ℝ) / 5) using 1
    all_goals norm_num
  · rw [show 2 * π * (4 : ℝ) / 5 = 2 * π * (-1 : ℝ) / 5 + 2 * π by ring]
    convert Real.cos_add_two_pi (2 * π * (-1 : ℝ) / 5) using 1
    all_goals norm_num

private lemma sin_orbit_reduced (k : OrbitIndex) :
    Real.sin (2 * π * (k : ℝ) / 5) =
      Real.sin (2 * π * (reducedOrbit k : ℝ) / 5) := by
  fin_cases k <;> simp [reducedOrbit]
  · rw [show 2 * π * (3 : ℝ) / 5 = 2 * π * (-2 : ℝ) / 5 + 2 * π by ring]
    convert Real.sin_add_two_pi (2 * π * (-2 : ℝ) / 5) using 1
    all_goals norm_num
  · rw [show 2 * π * (4 : ℝ) / 5 = 2 * π * (-1 : ℝ) / 5 + 2 * π by ring]
    convert Real.sin_add_two_pi (2 * π * (-1 : ℝ) / 5) using 1
    all_goals norm_num

private lemma angle_error (k : OrbitIndex) :
    |((2 * Noperthedron.piQ * reducedOrbit k / 5 : ℚ) : ℝ) -
      2 * π * (reducedOrbit k : ℝ) / 5| ≤ κ / 42 := by
  have hpi : 0 ≤ π - (Noperthedron.piQ : ℝ) :=
    le_of_lt (sub_pos.mpr piQ_lt_pi)
  have hk := reducedOrbit_abs_le_two k
  have hdiff :
      |((2 * Noperthedron.piQ * reducedOrbit k / 5 : ℚ) : ℝ) -
          2 * π * (reducedOrbit k : ℝ) / 5| =
        (2 * |(reducedOrbit k : ℝ)| / 5) *
          (π - (Noperthedron.piQ : ℝ)) := by
    push_cast
    rw [show 2 * (Noperthedron.piQ : ℝ) * (reducedOrbit k : ℝ) / 5 -
        2 * π * (reducedOrbit k : ℝ) / 5 =
        -(2 * (reducedOrbit k : ℝ) / 5 *
          (π - (Noperthedron.piQ : ℝ))) by ring]
    rw [abs_neg, abs_mul, abs_div, abs_mul, abs_of_nonneg hpi]
    norm_num
  rw [hdiff]
  calc
    (2 * |(reducedOrbit k : ℝ)| / 5) *
        (π - (Noperthedron.piQ : ℝ))
      ≤ (4 / 5 : ℝ) * (π - (Noperthedron.piQ : ℝ)) := by
        nlinarith [hk]
    _ ≤ (4 / 5 : ℝ) * (1 / 10 ^ 20) := by
        gcongr
        exact le_of_lt pi_sub_piQ_lt
    _ ≤ κ / 42 := by norm_num [κ]

theorem cos_symmetry_combined_error (k : OrbitIndex) :
    |((RationalApprox.cosℚ
        (2 * Noperthedron.piQ * reducedOrbit k / 5) : ℚ) : ℝ) -
      Real.cos (2 * π * (k : ℝ) / 5)| ≤ κ / 6 := by
  let q : ℚ := 2 * Noperthedron.piQ * reducedOrbit k / 5
  let x : ℝ := 2 * π * (reducedOrbit k : ℝ) / 5
  have ht := RationalApprox.cosℚ_approx' (q : ℝ) (rationalAngle_mem k)
  have hm : |Real.cos (q : ℝ) - Real.cos x| ≤ |(q : ℝ) - x| :=
    Real.abs_cos_sub_cos_le _ _
  have hq : |(q : ℝ) - x| ≤ κ / 42 := angle_error k
  rw [cos_orbit_reduced k]
  rw [← RationalApprox.cosℚ_match q] at ht
  calc
    |((RationalApprox.cosℚ q : ℚ) : ℝ) - Real.cos x|
      ≤ |((RationalApprox.cosℚ q : ℚ) : ℝ) - Real.cos (q : ℝ)| +
          |Real.cos (q : ℝ) - Real.cos x| := by
        exact abs_sub_le
          (((RationalApprox.cosℚ q : ℚ) : ℝ))
          (Real.cos (q : ℝ)) (Real.cos x)
    _ ≤ κ / 7 + κ / 42 :=
      add_le_add (by simpa [abs_sub_comm] using ht) (hm.trans hq)
    _ = κ / 6 := by ring

theorem sin_symmetry_combined_error (k : OrbitIndex) :
    |((RationalApprox.sinℚ
        (2 * Noperthedron.piQ * reducedOrbit k / 5) : ℚ) : ℝ) -
      Real.sin (2 * π * (k : ℝ) / 5)| ≤ κ / 6 := by
  let q : ℚ := 2 * Noperthedron.piQ * reducedOrbit k / 5
  let x : ℝ := 2 * π * (reducedOrbit k : ℝ) / 5
  have ht := RationalApprox.sinℚ_approx' (q : ℝ) (rationalAngle_mem k)
  have hm : |Real.sin (q : ℝ) - Real.sin x| ≤ |(q : ℝ) - x| :=
    Real.abs_sin_sub_sin_le _ _
  have hq : |(q : ℝ) - x| ≤ κ / 42 := angle_error k
  rw [sin_orbit_reduced k]
  rw [← RationalApprox.sinℚ_match q] at ht
  calc
    |((RationalApprox.sinℚ q : ℚ) : ℝ) - Real.sin x|
      ≤ |((RationalApprox.sinℚ q : ℚ) : ℝ) - Real.sin (q : ℝ)| +
          |Real.sin (q : ℝ) - Real.sin x| := by
        exact abs_sub_le
          (((RationalApprox.sinℚ q : ℚ) : ℝ))
          (Real.sin (q : ℝ)) (Real.sin x)
    _ ≤ κ / 7 + κ / 42 :=
      add_le_add (by simpa [abs_sub_comm] using ht) (hm.trans hq)
    _ = κ / 6 := by ring

private lemma RzL_apply_0 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 0 = cos θ * v 0 - sin θ * v 1 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]
  ring

private lemma RzL_apply_1 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 1 = sin θ * v 0 + cos θ * v 1 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]

private lemma RzL_apply_2 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 2 = v 2 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]

private lemma seed_xy_sq_le_one (i : SeedIndex) :
    ((seedVertex i 0 : ℚ) : ℝ) ^ 2 + ((seedVertex i 1 : ℚ) : ℝ) ^ 2 ≤ 1 := by
  fin_cases i <;> norm_num [seedVertex]

/-- The rational Taylor bridge is well inside half of the `κ` budget. -/
theorem taylorVertex_close (i : VertexIndex) :
    ‖toR3 (taylorVertex i) - exactVertex i‖ ≤ κ / 2 := by
  let k := orbitIndex i
  let s := seedIndex i
  let q : ℚ := 2 * Noperthedron.piQ * reducedOrbit k / 5
  let θ : ℝ := 2 * π * (k : ℝ) / 5
  let ce : ℝ := ((RationalApprox.cosℚ q : ℚ) : ℝ) - Real.cos θ
  let se : ℝ := ((RationalApprox.sinℚ q : ℚ) : ℝ) - Real.sin θ
  let a : ℝ := (seedVertex s 0 : ℚ)
  let b : ℝ := (seedVertex s 1 : ℚ)
  let d := toR3 (taylorVertex i) - exactVertex i
  have hce : |ce| ≤ κ / 6 := cos_symmetry_combined_error k
  have hse : |se| ≤ κ / 6 := sin_symmetry_combined_error k
  have hab : a ^ 2 + b ^ 2 ≤ 1 := seed_xy_sq_le_one s
  have hd0 : d 0 = ce * a - se * b := by
    simp only [d, taylorVertex, exactVertex, k, s, q, θ, ce, se, a, b,
      reducedOrbit, toR3, PiLp.sub_apply, Matrix.cons_val_zero, RzL_apply_0]
    push_cast
    ring
  have hd1 : d 1 = se * a + ce * b := by
    simp only [d, taylorVertex, exactVertex, k, s, q, θ, ce, se, a, b,
      reducedOrbit, toR3, PiLp.sub_apply, Matrix.cons_val_one, RzL_apply_1]
    push_cast
    ring
  have hd2 : d 2 = 0 := by
    simp [d, taylorVertex, exactVertex, toR3, RzL_apply_2]
  have hsq : d 0 ^ 2 + d 1 ^ 2 = (ce ^ 2 + se ^ 2) * (a ^ 2 + b ^ 2) := by
    rw [hd0, hd1]
    ring
  have hce_sq : ce ^ 2 ≤ (κ / 6) ^ 2 :=
    sq_le_sq' (abs_le.mp hce).1 (abs_le.mp hce).2
  have hse_sq : se ^ 2 ≤ (κ / 6) ^ 2 :=
    sq_le_sq' (abs_le.mp hse).1 (abs_le.mp hse).2
  have hκ : (0 : ℝ) ≤ κ / 2 := by norm_num [κ]
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hκ]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, norm_eq_abs, sq_abs]
  rw [hd2, zero_pow (by omega), add_zero, hsq]
  calc
    (ce ^ 2 + se ^ 2) * (a ^ 2 + b ^ 2)
      ≤ (2 * (κ / 6) ^ 2) * 1 :=
        mul_le_mul (by linarith) hab (by positivity) (by positivity)
    _ ≤ (κ / 2) ^ 2 := by norm_num [κ]

/-- The printed STL decimals agree with the rational Taylor bridge much more
closely than required.  This finite arithmetic statement is kernel checked. -/
theorem stl_taylor_sq_close : ∀ i : VertexIndex,
    (rationalVertex i 0 - taylorVertex i 0) ^ 2 +
    (rationalVertex i 1 - taylorVertex i 1) ^ 2 +
    (rationalVertex i 2 - taylorVertex i 2) ^ 2 ≤ (1 : ℚ) / 10 ^ 24 := by
  decide +kernel

theorem stl_taylor_close (i : VertexIndex) :
    ‖toR3 (rationalVertex i) - toR3 (taylorVertex i)‖ ≤ κ / 2 := by
  have hκ : (0 : ℝ) ≤ κ / 2 := by norm_num [κ]
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hκ]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, norm_eq_abs, sq_abs, toR3, PiLp.sub_apply]
  norm_cast
  grw [stl_taylor_sq_close i]
  norm_num [κ]

theorem vertex_close (i : VertexIndex) :
    ‖exactVertex i - toR3 (rationalVertex i)‖ ≤ κ := by
  rw [norm_sub_rev]
  calc
    ‖toR3 (rationalVertex i) - exactVertex i‖ =
        ‖(toR3 (rationalVertex i) - toR3 (taylorVertex i)) +
          (toR3 (taylorVertex i) - exactVertex i)‖ := by
      congr 1
      abel
    _ ≤ ‖toR3 (rationalVertex i) - toR3 (taylorVertex i)‖ +
        ‖toR3 (taylorVertex i) - exactVertex i‖ := norm_add_le _ _
    _ ≤ κ / 2 + κ / 2 := add_le_add (stl_taylor_close i) (taylorVertex_close i)
    _ = κ := by ring

noncomputable def exactApproximation :
    RationalApprox.κApproxPoly exactPolyhedron rationalPolyhedron where
  bijection := Equiv.refl VertexIndex
  approx i := vertex_close i

end Noperthedron.Nopert214

end
