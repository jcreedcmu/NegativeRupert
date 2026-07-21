module

public import Noperthedron.Checker.RatQuadratic3
public import Noperthedron.SnubCube.BernsteinCertificate

@[expose] public section

/-!
# Bernstein bounds for rational quadratics on three-dimensional boxes

This specializes the tensor Bernstein convex-hull theorem to the ten-field
quadratic representation used by the Nopert #214 atlas checker.
-/

namespace Noperthedron.Nopert214.QuadraticBernstein

open Noperthedron.Checker
open Noperthedron.SnubCube.BernsteinCertificate

def min3 (f : Fin 3 → ℚ) : ℚ := min (f 0) (min (f 1) (f 2))

theorem min3_le (f : Fin 3 → ℚ) (i : Fin 3) : min3 f ≤ f i := by
  fin_cases i <;> simp [min3]

/-- One tensor-degree `(2,2,2)` Bernstein control coefficient after the
affine substitution from the unit cube to `vars`. -/
def coefficient (vars : Fin 3 → RatBall) (q : RatQuadratic3)
    (i j k : Fin 3) : ℚ :=
  let lx := (vars 0).center - (vars 0).radius
  let ly := (vars 1).center - (vars 1).radius
  let lz := (vars 2).center - (vars 2).radius
  let wx := 2 * (vars 0).radius
  let wy := 2 * (vars 1).radius
  let wz := 2 * (vars 2).radius
  let u : ℚ := i.val / 2
  let v : ℚ := j.val / 2
  let w : ℚ := k.val / 2
  let a0 := q.evalQ lx ly lz
  let ax := wx * (q.cx + 2*q.cxx*lx + q.cxy*ly + q.cxz*lz)
  let ay := wy * (q.cy + q.cxy*lx + 2*q.cyy*ly + q.cyz*lz)
  let az := wz * (q.cz + q.cxz*lx + q.cyz*ly + 2*q.czz*lz)
  let axx := q.cxx * wx * wx
  let ayy := q.cyy * wy * wy
  let azz := q.czz * wz * wz
  let axy := q.cxy * wx * wy
  let axz := q.cxz * wx * wz
  let ayz := q.cyz * wy * wz
  a0 + u*ax + v*ay + w*az +
    (if i = 2 then axx else 0) +
    (if j = 2 then ayy else 0) +
    (if k = 2 then azz else 0) +
    u*v*axy + u*w*axz + v*w*ayz

@[simp] theorem coefficient_add (vars : Fin 3 → RatBall)
    (a b : RatQuadratic3) (i j k : Fin 3) :
    coefficient vars (a + b) i j k =
      coefficient vars a i j k + coefficient vars b i j k := by
  simp [coefficient, RatQuadratic3.evalQ]
  split_ifs <;> ring

@[simp] theorem coefficient_scale (vars : Fin 3 → RatBall)
    (s : ℚ) (q : RatQuadratic3) (i j k : Fin 3) :
    coefficient vars (RatQuadratic3.scale s q) i j k =
      s * coefficient vars q i j k := by
  simp [coefficient, RatQuadratic3.evalQ]
  split_ifs <;> ring

@[simp] theorem coefficient_neg (vars : Fin 3 → RatBall)
    (q : RatQuadratic3) (i j k : Fin 3) :
    coefficient vars (-q) i j k = -coefficient vars q i j k := by
  simp [coefficient, RatQuadratic3.evalQ]
  split_ifs <;> ring

@[simp] theorem coefficient_sub (vars : Fin 3 → RatBall)
    (a b : RatQuadratic3) (i j k : Fin 3) :
    coefficient vars (a - b) i j k =
      coefficient vars a i j k - coefficient vars b i j k := by
  simp [coefficient, RatQuadratic3.evalQ]
  split_ifs <;> ring

def lower (vars : Fin 3 → RatBall) (q : RatQuadratic3) : ℚ :=
  min3 fun i => min3 fun j => min3 fun k => coefficient vars q i j k

noncomputable def evalBernstein (vars : Fin 3 → RatBall)
    (q : RatQuadratic3) (tx ty tz : ℝ) : ℝ :=
  ∑ i : Fin 3, (∑ j : Fin 3, (∑ k : Fin 3,
    (coefficient vars q i j k : ℝ) * basis 2 k.val tz) *
      basis 2 j.val ty) * basis 2 i.val tx

theorem evalBernstein_eq (vars : Fin 3 → RatBall) (q : RatQuadratic3)
    (tx ty tz : ℝ) :
    evalBernstein vars q tx ty tz =
      q.evalReal
        ((vars 0).center - (vars 0).radius + 2*(vars 0).radius*tx)
        ((vars 1).center - (vars 1).radius + 2*(vars 1).radius*ty)
        ((vars 2).center - (vars 2).radius + 2*(vars 2).radius*tz) := by
  simp [evalBernstein, coefficient, basis, Fin.sum_univ_three,
    RatQuadratic3.evalQ, RatQuadratic3.evalReal]
  ring

private theorem lower_le_sum_mul {ι : Type} [Fintype ι]
    (weight coefficient : ι → ℝ) (lower : ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (hcoefficient : ∀ i, lower ≤ coefficient i) :
    lower ≤ ∑ i, coefficient i * weight i := by
  calc
    lower = ∑ i, lower * weight i := by rw [← Finset.mul_sum, hsum, mul_one]
    _ ≤ ∑ i, coefficient i * weight i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hcoefficient i) (hweight i)

theorem lower_le_evalBernstein (vars : Fin 3 → RatBall)
    (q : RatQuadratic3) {tx ty tz : ℝ}
    (htx : 0 ≤ tx ∧ tx ≤ 1) (hty : 0 ≤ ty ∧ ty ≤ 1)
    (htz : 0 ≤ tz ∧ tz ≤ 1) :
    (lower vars q : ℝ) ≤ evalBernstein vars q tx ty tz := by
  unfold evalBernstein
  apply lower_le_sum_mul (fun i : Fin 3 => basis 2 i.val tx)
  · intro i
    exact basis_nonnegative htx.1 htx.2
  · simp [Fin.sum_univ_three, basis]
    ring
  · intro i
    apply lower_le_sum_mul (fun j : Fin 3 => basis 2 j.val ty)
    · intro j
      exact basis_nonnegative hty.1 hty.2
    · simp [Fin.sum_univ_three, basis]
      ring
    · intro j
      apply lower_le_sum_mul (fun k : Fin 3 => basis 2 k.val tz)
      · intro k
        exact basis_nonnegative htz.1 htz.2
      · simp [Fin.sum_univ_three, basis]
        ring
      · intro k
        exact_mod_cast (min3_le (fun i =>
          min3 fun j => min3 fun k => coefficient vars q i j k) i).trans
            ((min3_le (fun j => min3 fun k => coefficient vars q i j k) j).trans
              (min3_le (fun k => coefficient vars q i j k) k))

theorem exists_unit_coordinate {b : RatBall} {x : ℝ} (h : b.Holds x) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      x = (b.center - b.radius : ℚ) + 2*(b.radius : ℝ)*t := by
  have habs : |x - (b.center : ℝ)| ≤ (b.radius : ℝ) := h
  have hr : 0 ≤ (b.radius : ℝ) := (abs_nonneg _).trans habs
  rw [abs_le] at habs
  by_cases hzero : b.radius = 0
  · refine ⟨0, by norm_num, by norm_num, ?_⟩
    have hzeroReal : (b.radius : ℝ) = 0 := by exact_mod_cast hzero
    push_cast
    rw [hzeroReal]
    norm_num at habs ⊢
    linarith
  · have hrpos : 0 < (b.radius : ℝ) := lt_of_le_of_ne hr (by
      have hrne : (b.radius : ℝ) ≠ 0 := by exact_mod_cast hzero
      exact hrne.symm)
    refine ⟨(x - ((b.center : ℝ) - (b.radius : ℝ))) /
        (2 * (b.radius : ℝ)), ?_, ?_, ?_⟩
    · apply div_nonneg
      · linarith [habs.1]
      · positivity
    · apply (div_le_iff₀ (by positivity)).mpr
      linarith
    · push_cast
      field_simp
      ring

theorem lower_le_evalReal {vars : Fin 3 → RatBall} {x y z : ℝ}
    (hvars : ∀ i, (vars i).Holds (![x, y, z] i))
    (q : RatQuadratic3) :
    (lower vars q : ℝ) ≤ q.evalReal x y z := by
  obtain ⟨tx, htx0, htx1, hx⟩ := exists_unit_coordinate (hvars 0)
  obtain ⟨ty, hty0, hty1, hy⟩ := exists_unit_coordinate (hvars 1)
  obtain ⟨tz, htz0, htz1, hz⟩ := exists_unit_coordinate (hvars 2)
  have hx' : x = ((vars 0).center - (vars 0).radius : ℚ) +
      2 * ((vars 0).radius : ℝ) * tx := by simpa using hx
  have hy' : y = ((vars 1).center - (vars 1).radius : ℚ) +
      2 * ((vars 1).radius : ℝ) * ty := by simpa using hy
  have hz' : z = ((vars 2).center - (vars 2).radius : ℚ) +
      2 * ((vars 2).radius : ℝ) * tz := by simpa using hz
  rw [hx', hy', hz']
  have h := lower_le_evalBernstein vars q ⟨htx0, htx1⟩ ⟨hty0, hty1⟩
    ⟨htz0, htz1⟩
  rw [evalBernstein_eq] at h
  push_cast at h ⊢
  exact h

end Noperthedron.Nopert214.QuadraticBernstein

end
