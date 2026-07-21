module

public import Noperthedron.Nopert214.Approximation

@[expose] public section

/-!
# Tight rational approximation for the fivefold orbit

The general Nopert #214 checker uses a deliberately loose `10⁻¹⁰` vertex
allowance.  Near an outer silhouette transition that allowance is much larger
than the actual rounding error in the published coordinates.  This module
uses the exact trigonometric values at 72 and 144 degrees, together with a
kernel-checked rational bridge for all twenty vertices, to prove the sharper
`5 * 10⁻¹⁶` bound used by the projective local certificate.
-/

open Real

namespace Noperthedron.Nopert214

def cos72Q : ℚ := 30901699437494745 / 10^17
def sin72Q : ℚ := 9510565162951535 / 10^16
def cos144Q : ℚ := 2 * cos72Q ^ 2 - 1
def sin144Q : ℚ := 2 * sin72Q * cos72Q
noncomputable def tightTrigError : ℝ := 1 / 10^16
/-- Uniform vertex error used by the support-sensitive local checker. -/
def tightVertexErrorQ : ℚ := 5 / 10^16

theorem cos72_tight :
    |Real.cos (2 * Real.pi / 5) - (cos72Q : ℝ)| ≤ 4 / 10^17 := by
  have hsqrt0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  have hsqrtLower :
      (22360679774997896 / 10^16 : ℝ) ≤ Real.sqrt 5 := by
    nlinarith [sq_nonneg (Real.sqrt 5 - 22360679774997896 / 10^16)]
  have hsqrtUpper :
      Real.sqrt 5 ≤ (22360679774997898 / 10^16 : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt 5 - 22360679774997898 / 10^16)]
  rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring,
    Real.cos_two_mul, Real.cos_pi_div_five]
  have hformula :
      2 * ((1 + Real.sqrt 5) / 4) ^ 2 - 1 =
        (Real.sqrt 5 - 1) / 4 := by
    nlinarith [hsqrtSq]
  rw [hformula]
  rw [abs_le]
  norm_num [cos72Q, tightTrigError]
  constructor <;> nlinarith

theorem sin72_tight :
    |Real.sin (2 * Real.pi / 5) - (sin72Q : ℝ)| ≤ tightTrigError := by
  have hangle0 : 0 < 2 * Real.pi / 5 := by positivity
  have hanglePi : 2 * Real.pi / 5 < Real.pi := by
    nlinarith [Real.pi_pos]
  have hsin0 : 0 < Real.sin (2 * Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi hangle0 hanglePi
  have hcos := cos72_tight
  rw [abs_le] at hcos ⊢
  have htrig := Real.sin_sq_add_cos_sq (2 * Real.pi / 5)
  norm_num [cos72Q, sin72Q, tightTrigError] at hcos ⊢
  constructor <;> nlinarith [
    sq_nonneg (Real.sin (2 * Real.pi / 5) -
      (9510565162951534 / 10^16 : ℝ)),
    sq_nonneg (Real.sin (2 * Real.pi / 5) -
      (9510565162951536 / 10^16 : ℝ))]

theorem cos144_tight :
    |Real.cos (4 * Real.pi / 5) - (cos144Q : ℝ)| ≤ 4 / 10^17 := by
  have hsqrt0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  have hsqrtLower :
      (22360679774997896 / 10^16 : ℝ) ≤ Real.sqrt 5 := by
    nlinarith [sq_nonneg (Real.sqrt 5 - 22360679774997896 / 10^16)]
  have hsqrtUpper :
      Real.sqrt 5 ≤ (22360679774997898 / 10^16 : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt 5 - 22360679774997898 / 10^16)]
  rw [show 4 * Real.pi / 5 = Real.pi - Real.pi / 5 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_five]
  rw [abs_le]
  norm_num [cos72Q, cos144Q, tightTrigError]
  constructor <;> nlinarith

theorem sin144_tight :
    |Real.sin (4 * Real.pi / 5) - (sin144Q : ℝ)| ≤ tightTrigError := by
  have hangle0 : 0 < 4 * Real.pi / 5 := by positivity
  have hanglePi : 4 * Real.pi / 5 < Real.pi := by
    nlinarith [Real.pi_pos]
  have hsin0 : 0 < Real.sin (4 * Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi hangle0 hanglePi
  have hcos := cos144_tight
  rw [abs_le] at hcos ⊢
  rcases hcos with ⟨hcosLower, hcosUpper⟩
  have htrig := Real.sin_sq_add_cos_sq (4 * Real.pi / 5)
  norm_num [cos72Q, cos144Q, sin72Q, sin144Q, tightTrigError]
    at hcosLower hcosUpper ⊢
  have hcosNeg : 0 ≤ -Real.cos (4 * Real.pi / 5) := by linarith
  have habsLower :
      -(((cos144Q : ℚ) : ℝ) + 4 / 10^17) ≤
        -Real.cos (4 * Real.pi / 5) := by
    norm_num [cos72Q, cos144Q]
    linarith
  have hcosSqLower :
      (-(((cos144Q : ℚ) : ℝ) + 4 / 10^17)) ^ 2 ≤
        (-Real.cos (4 * Real.pi / 5)) ^ 2 := by
    apply (sq_le_sq₀ (by norm_num [cos72Q, cos144Q]) hcosNeg).2
    exact habsLower
  norm_num [cos72Q, cos144Q] at hcosSqLower
  constructor
  · nlinarith [sq_nonneg (Real.sin (4 * Real.pi / 5) -
      ((sin144Q : ℚ) : ℝ) - tightTrigError)]
  · let upper : ℝ := ((sin144Q : ℚ) : ℝ) + tightTrigError
    have hupper0 : 0 ≤ upper := by norm_num [upper, sin72Q, sin144Q,
      cos72Q, tightTrigError]
    have hsq : Real.sin (4 * Real.pi / 5) ^ 2 ≤ upper ^ 2 := by
      dsimp [upper]
      norm_num [sin144Q, sin72Q, cos72Q, tightTrigError]
      nlinarith
    have hu := (sq_le_sq₀ (le_of_lt hsin0) hupper0).mp hsq
    norm_num [upper, tightTrigError, sin72Q, sin144Q, cos72Q] at hu ⊢
    exact hu

def tightCos : OrbitIndex → ℚ := ![1, cos72Q, cos144Q, cos144Q, cos72Q]
def tightSin : OrbitIndex → ℚ := ![0, sin72Q, sin144Q, -sin144Q, -sin72Q]

def tightVertex (i : VertexIndex) : Fin 3 → ℚ :=
  let c := tightCos (orbitIndex i)
  let s := tightSin (orbitIndex i)
  let v := seedVertex (seedIndex i)
  ![c * v 0 - s * v 1, s * v 0 + c * v 1, v 2]

theorem tightCos_close (k : OrbitIndex) :
    |((tightCos k : ℚ) : ℝ) - Real.cos (2 * Real.pi * (k : ℝ) / 5)| ≤
      tightTrigError := by
  fin_cases k
  · norm_num [tightCos, tightTrigError]
  · calc
      _ ≤ 4 / 10^17 := by simpa [tightCos, abs_sub_comm] using cos72_tight
      _ ≤ tightTrigError := by norm_num [tightTrigError]
  · norm_num [tightCos]
    calc
      _ ≤ 4 / 10^17 := by
        simpa [show 2 * Real.pi * (2 : ℝ) / 5 = 4 * Real.pi / 5 by ring,
          abs_sub_comm] using cos144_tight
      _ ≤ tightTrigError := by norm_num [tightTrigError]
  · norm_num [tightCos]
    rw [show 2 * Real.pi * (3 : ℝ) / 5 = 2 * Real.pi - 4 * Real.pi / 5 by ring,
      Real.cos_two_pi_sub]
    calc
      _ ≤ 4 / 10^17 := by simpa [abs_sub_comm] using cos144_tight
      _ ≤ tightTrigError := by norm_num [tightTrigError]
  · norm_num [tightCos]
    rw [show 2 * Real.pi * (4 : ℝ) / 5 = 2 * Real.pi - 2 * Real.pi / 5 by ring,
      Real.cos_two_pi_sub]
    calc
      _ ≤ 4 / 10^17 := by simpa [abs_sub_comm] using cos72_tight
      _ ≤ tightTrigError := by norm_num [tightTrigError]

theorem tightSin_close (k : OrbitIndex) :
    |((tightSin k : ℚ) : ℝ) - Real.sin (2 * Real.pi * (k : ℝ) / 5)| ≤
      tightTrigError := by
  fin_cases k
  · norm_num [tightSin, tightTrigError]
  · simpa [tightSin, abs_sub_comm] using sin72_tight
  · norm_num [tightSin]
    have h := sin144_tight
    norm_num at h ⊢
    simpa [show 2 * Real.pi * (2 : ℝ) / 5 = 4 * Real.pi / 5 by ring,
      abs_sub_comm] using h
  · norm_num [tightSin]
    rw [show 2 * Real.pi * (3 : ℝ) / 5 = 2 * Real.pi - 4 * Real.pi / 5 by ring,
      Real.sin_two_pi_sub]
    calc
      _ = |Real.sin (4 * Real.pi / 5) - ((sin144Q : ℚ) : ℝ)| := by
        congr 1 <;> ring
      _ ≤ tightTrigError := sin144_tight
  · norm_num [tightSin]
    rw [show 2 * Real.pi * (4 : ℝ) / 5 = 2 * Real.pi - 2 * Real.pi / 5 by ring,
      Real.sin_two_pi_sub]
    calc
      _ = |Real.sin (2 * Real.pi / 5) - ((sin72Q : ℚ) : ℝ)| := by
        congr 1 <;> ring
      _ ≤ tightTrigError := sin72_tight

private lemma tight_RzL_apply_0 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 0 = cos θ * v 0 - sin θ * v 1 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]
  ring

private lemma tight_RzL_apply_1 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 1 = sin θ * v 0 + cos θ * v 1 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]

private lemma tight_RzL_apply_2 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 2 = v 2 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]

private lemma tight_seed_xy_sq_le_one (i : SeedIndex) :
    ((seedVertex i 0 : ℚ) : ℝ) ^ 2 + ((seedVertex i 1 : ℚ) : ℝ) ^ 2 ≤ 1 := by
  fin_cases i <;> norm_num [seedVertex]

theorem tightVertex_exact_close (i : VertexIndex) :
    ‖toR3 (tightVertex i) - exactVertex i‖ ≤ 2 / 10^16 := by
  let k := orbitIndex i
  let s := seedIndex i
  let θ : ℝ := 2 * Real.pi * (k : ℝ) / 5
  let ce : ℝ := (tightCos k : ℚ) - Real.cos θ
  let se : ℝ := (tightSin k : ℚ) - Real.sin θ
  let a : ℝ := (seedVertex s 0 : ℚ)
  let b : ℝ := (seedVertex s 1 : ℚ)
  let d := toR3 (tightVertex i) - exactVertex i
  have hce : |ce| ≤ 1 / 10^16 := tightCos_close k
  have hse : |se| ≤ 1 / 10^16 := tightSin_close k
  have hab : a ^ 2 + b ^ 2 ≤ 1 := tight_seed_xy_sq_le_one s
  have hd0 : d 0 = ce * a - se * b := by
    simp only [d, tightVertex, exactVertex, k, s, θ, ce, se, a, b,
      toR3, PiLp.sub_apply, Matrix.cons_val_zero, tight_RzL_apply_0]
    push_cast
    ring
  have hd1 : d 1 = se * a + ce * b := by
    simp only [d, tightVertex, exactVertex, k, s, θ, ce, se, a, b,
      toR3, PiLp.sub_apply, Matrix.cons_val_one, tight_RzL_apply_1]
    push_cast
    ring
  have hd2 : d 2 = 0 := by
    simp [d, tightVertex, exactVertex, toR3, tight_RzL_apply_2]
  have hsq : d 0 ^ 2 + d 1 ^ 2 =
      (ce ^ 2 + se ^ 2) * (a ^ 2 + b ^ 2) := by
    rw [hd0, hd1]
    ring
  have hce_sq : ce ^ 2 ≤ (1 / 10^16 : ℝ) ^ 2 :=
    sq_le_sq' (abs_le.mp hce).1 (abs_le.mp hce).2
  have hse_sq : se ^ 2 ≤ (1 / 10^16 : ℝ) ^ 2 :=
    sq_le_sq' (abs_le.mp hse).1 (abs_le.mp hse).2
  have he : (0 : ℝ) ≤ 2 / 10^16 := by norm_num
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq he]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, norm_eq_abs, sq_abs]
  rw [hd2, zero_pow (by omega), add_zero, hsq]
  nlinarith

theorem stl_tight_sq_close : ∀ i : VertexIndex,
    (rationalVertex i 0 - tightVertex i 0) ^ 2 +
    (rationalVertex i 1 - tightVertex i 1) ^ 2 +
    (rationalVertex i 2 - tightVertex i 2) ^ 2 ≤ (3 / 10^16 : ℚ) ^ 2 := by
  decide +kernel

theorem stl_tight_close (i : VertexIndex) :
    ‖toR3 (rationalVertex i) - toR3 (tightVertex i)‖ ≤ 3 / 10^16 := by
  have he : (0 : ℝ) ≤ 3 / 10^16 := by norm_num
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq he]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, norm_eq_abs, sq_abs, toR3, PiLp.sub_apply]
  have h := stl_tight_sq_close i
  have hreal :
      (((rationalVertex i 0 - tightVertex i 0) ^ 2 +
        (rationalVertex i 1 - tightVertex i 1) ^ 2 +
        (rationalVertex i 2 - tightVertex i 2) ^ 2 : ℚ) : ℝ) ≤
          (((3 / 10^16 : ℚ) ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at hreal
  norm_num at hreal ⊢
  exact hreal

theorem vertex_close_tight (i : VertexIndex) :
    ‖exactVertex i - toR3 (rationalVertex i)‖ ≤
      (tightVertexErrorQ : ℝ) := by
  rw [norm_sub_rev]
  calc
    ‖toR3 (rationalVertex i) - exactVertex i‖ =
        ‖(toR3 (rationalVertex i) - toR3 (tightVertex i)) +
          (toR3 (tightVertex i) - exactVertex i)‖ := by
      congr 1
      abel
    _ ≤ ‖toR3 (rationalVertex i) - toR3 (tightVertex i)‖ +
        ‖toR3 (tightVertex i) - exactVertex i‖ := norm_add_le _ _
    _ ≤ 3 / 10^16 + 2 / 10^16 :=
      add_le_add (stl_tight_close i) (tightVertex_exact_close i)
    _ = (tightVertexErrorQ : ℝ) := by
      norm_num [tightVertexErrorQ]

end Noperthedron.Nopert214

end
