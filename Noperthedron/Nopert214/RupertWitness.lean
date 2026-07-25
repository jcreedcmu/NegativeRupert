module

public import Noperthedron.Nopert214.TightApproximation
public import Noperthedron.Rupert.Equivalences.RupertEquivRupertSet
public import Noperthedron.Cayley
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

@[expose] public section

/-!
# Nopert #214 is Rupert

Contrary to the original goal of this development, the exact
fivefold-symmetric Nopert #214 *does* have the Rupert property.  The
passage is astronomically thin: the inner shadow clears the outer shadow
boundary by about `1.8e-8`, which is far below the resolution of the
floating-point searches that classified this polyhedron as a "nopert".

This file exhibits an explicit rational witness.  Both rotations are Cayley
matrices with rational parameters, hence exactly special orthogonal.  The
containment proof reduces to twenty strict triangle-membership inequalities
over `ℚ` (checked by `decide` against the `tightVertex` rational model)
plus the kernel-proved `2e-16` bound between `tightVertex` and the exact
vertices.  The worst rational sub-area margin is about `1.37e-8`, six
orders of magnitude above the total approximation error.

The witness was discovered by following the failure set of the local
certificate search: the achievable local margin crosses zero along a curve
of outer view directions, and past that curve first-order fitting
perturbations of the diagonal pose exist and survive at finite angle.
-/

open Matrix

namespace Noperthedron.Nopert214

namespace RupertWitness

/-! ## The witness data -/

/-- Cayley parameters of the inner rotation. -/
def cx₁ : ℚ := -119091614393 / 171136508057
def cy₁ : ℚ := -445838043814 / 513409524171
def cz₁ : ℚ := -640307571101 / 513409524171

/-- Cayley parameters of the outer rotation. -/
def cx₂ : ℚ := -178692746467 / 256835444761
def cy₂ : ℚ := -222739085837 / 256835444761
def cz₂ : ℚ := -91469524897 / 73381555646

/-- The inner shadow translation. -/
def offsetQ : Fin 2 → ℚ :=
  ![-68618674499 / 1000000000000000, 1164714843 / 25000000000000]

/-- For each inner vertex, an outer triangle strictly containing its
projection, oriented counterclockwise. -/
def witnessTriangle : Fin 20 → Fin 20 × Fin 20 × Fin 20 := ![
  (2, 8, 13), (5, 13, 7), (5, 14, 7), (0, 19, 3), (0, 5, 8),
  (0, 5, 8), (3, 6, 8), (0, 3, 7), (0, 5, 8), (5, 8, 12),
  (6, 8, 14), (5, 19, 7), (2, 8, 12), (8, 13, 19), (4, 14, 19),
  (7, 13, 19), (1, 8, 13), (0, 14, 19), (0, 14, 19), (7, 12, 19)]

/-! ## Rational shadow points -/

/-- The rational Cayley rotation matrix. -/
def cayleyMatrixQ (x y z : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  let d := 1 + x ^ 2 + y ^ 2 + z ^ 2
  !![(1 + x ^ 2 - y ^ 2 - z ^ 2) / d, 2 * (x * y - z) / d,
      2 * (x * z + y) / d;
     2 * (x * y + z) / d, (1 - x ^ 2 + y ^ 2 - z ^ 2) / d,
      2 * (y * z - x) / d;
     2 * (x * z - y) / d, 2 * (y * z + x) / d,
      (1 - x ^ 2 - y ^ 2 + z ^ 2) / d]

def innerMatrixQ : Matrix (Fin 3) (Fin 3) ℚ := cayleyMatrixQ cx₁ cy₁ cz₁
def outerMatrixQ : Matrix (Fin 3) (Fin 3) ℚ := cayleyMatrixQ cx₂ cy₂ cz₂

/-- Embed a plane coordinate index into space. -/
def dim2to3 (j : Fin 2) : Fin 3 := ⟨j.val, by omega⟩

/-- Rational model of the projected translated inner vertices. -/
def innerPointQ (i : VertexIndex) (j : Fin 2) : ℚ :=
  offsetQ j + ∑ k, innerMatrixQ (dim2to3 j) k * tightVertex i k

/-- Rational model of the projected outer vertices. -/
def outerPointQ (i : VertexIndex) (j : Fin 2) : ℚ :=
  ∑ k, outerMatrixQ (dim2to3 j) k * tightVertex i k

/-- Twice the signed area of a rational plane triangle. -/
def crossQ2 (p a b : Fin 2 → ℚ) : ℚ :=
  (a 0 - p 0) * (b 1 - p 1) - (a 1 - p 1) * (b 0 - p 0)

/-- Uniform bound on `‖toR3 (tightVertex i) - exactVertex i‖`. -/
def δQ : ℚ := 2 / 10 ^ 16

/-- The complete decidable certificate: every projected inner vertex is
inside its witness triangle with margin dwarfing the approximation error,
and all involved coordinates are bounded by two. -/
def RationalChecks : Prop := ∀ i : VertexIndex,
  let t := witnessTriangle i
  let p := innerPointQ i
  let a := outerPointQ t.1
  let b := outerPointQ t.2.1
  let c := outerPointQ t.2.2
  40 * δQ < crossQ2 p b c ∧ 40 * δQ < crossQ2 p c a ∧
    40 * δQ < crossQ2 p a b ∧
    (∀ j, |p j| ≤ 2 ∧ |a j| ≤ 2 ∧ |b j| ≤ 2 ∧ |c j| ≤ 2)

instance : Decidable RationalChecks := by
  unfold RationalChecks
  infer_instance

theorem rationalChecks : RationalChecks := by decide +kernel

/-! ## The real witness -/

noncomputable def innerRot : Matrix (Fin 3) (Fin 3) ℝ :=
  cayleyMatrix (cx₁ : ℝ) (cy₁ : ℝ) (cz₁ : ℝ)

noncomputable def outerRot : Matrix (Fin 3) (Fin 3) ℝ :=
  cayleyMatrix (cx₂ : ℝ) (cy₂ : ℝ) (cz₂ : ℝ)

theorem innerRot_mem : innerRot ∈ SO3 := cayleyMatrix_mem_SO3 _ _ _
theorem outerRot_mem : outerRot ∈ SO3 := cayleyMatrix_mem_SO3 _ _ _

noncomputable def innerSO3 : SO3 := ⟨innerRot, innerRot_mem⟩
noncomputable def outerSO3 : SO3 := ⟨outerRot, outerRot_mem⟩

noncomputable def offsetR : ℝ² := !₂[(offsetQ 0 : ℝ), (offsetQ 1 : ℝ)]

/-- The affine map producing the translated inner shadow. -/
noncomputable def innerMap : ℝ³ →ᵃ[ℝ] ℝ² :=
  full_transform_affine offsetR innerSO3

/-- The affine map producing the outer shadow. -/
noncomputable def outerMap : ℝ³ →ᵃ[ℝ] ℝ² :=
  proj_xy_rotation_is_affine outerSO3

/-! ## Coordinate control -/

theorem abs_coord_le_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (j : Fin n) : |x j| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (abs_nonneg (x j))]
  apply Real.sqrt_le_sqrt
  simp only [Real.norm_eq_abs, sq_abs]
  exact Finset.single_le_sum (fun k _ => sq_nonneg (x k))
    (Finset.mem_univ j)

/-- Rotating by a special orthogonal matrix preserves norms. -/
theorem norm_so3_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M ∈ SO3)
    (v : ℝ³) : ‖M.toEuclideanLin v‖ = ‖v‖ := by
  let u : ℝ³ ≃ₗᵢ[ℝ] ℝ³ :=
    Bounding.OrthogonalGroup.toLinearIsometryEquiv ⟨M, hM.1⟩
  have hu : u v = M.toEuclideanLin v := rfl
  rw [← hu, u.norm_map]

/-! ## Casting the rational model -/

theorem innerRot_eq_map :
    innerRot = innerMatrixQ.map ((↑) : ℚ → ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [innerRot, innerMatrixQ, cayleyMatrix, cayleyMatrixQ,
      cayleyDenom]

theorem outerRot_eq_map :
    outerRot = outerMatrixQ.map ((↑) : ℚ → ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [outerRot, outerMatrixQ, cayleyMatrix, cayleyMatrixQ,
      cayleyDenom]

theorem proj_xyL_coord (x : ℝ³) (j : Fin 2) :
    proj_xyL x j = x (dim2to3 j) := by
  fin_cases j <;>
    simp [proj_xyL, proj_xy_mat, dim2to3, Matrix.toLpLin_apply,
      dotProduct, Fin.sum_univ_three]

theorem innerMap_coord (v : ℝ³) (j : Fin 2) :
    innerMap v j = offsetR j + (innerRot.toEuclideanLin v) (dim2to3 j) := by
  show (offsetR + proj_xyL (innerRot.toEuclideanLin v)) j = _
  rw [PiLp.add_apply, proj_xyL_coord]

theorem outerMap_coord (v : ℝ³) (j : Fin 2) :
    outerMap v j = (outerRot.toEuclideanLin v) (dim2to3 j) := by
  show (proj_xyL (outerRot.toEuclideanLin v)) j = _
  rw [proj_xyL_coord]

theorem map_toR3_coord (Mq : Matrix (Fin 3) (Fin 3) ℚ) (w : Fin 3 → ℚ)
    (k : Fin 3) :
    ((Mq.map ((↑) : ℚ → ℝ)).toEuclideanLin (toR3 w)) k =
      ((∑ l, Mq k l * w l : ℚ) : ℝ) := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, toR3,
    Fin.sum_univ_three]

theorem offsetR_coord (j : Fin 2) : offsetR j = ((offsetQ j : ℚ) : ℝ) := by
  fin_cases j <;> simp [offsetR]

theorem innerMap_rat (i : VertexIndex) (j : Fin 2) :
    innerMap (toR3 (tightVertex i)) j = ((innerPointQ i j : ℚ) : ℝ) := by
  rw [innerMap_coord, innerRot_eq_map, map_toR3_coord, offsetR_coord,
    innerPointQ]
  push_cast
  ring

theorem outerMap_rat (i : VertexIndex) (j : Fin 2) :
    outerMap (toR3 (tightVertex i)) j = ((outerPointQ i j : ℚ) : ℝ) := by
  rw [outerMap_coord, outerRot_eq_map, map_toR3_coord, outerPointQ]

/-! ## Approximation control -/

theorem innerMap_close (i : VertexIndex) (j : Fin 2) :
    |innerMap (exactVertex i) j - ((innerPointQ i j : ℚ) : ℝ)| ≤
      (δQ : ℝ) := by
  rw [← innerMap_rat]
  have hdiff : innerMap (exactVertex i) j -
      innerMap (toR3 (tightVertex i)) j =
      (innerRot.toEuclideanLin
        (exactVertex i - toR3 (tightVertex i))) (dim2to3 j) := by
    rw [innerMap_coord, innerMap_coord, map_sub, PiLp.sub_apply]
    ring
  rw [hdiff]
  calc |(innerRot.toEuclideanLin
        (exactVertex i - toR3 (tightVertex i))) (dim2to3 j)|
      ≤ ‖innerRot.toEuclideanLin (exactVertex i - toR3 (tightVertex i))‖ :=
        abs_coord_le_norm _ _
    _ = ‖exactVertex i - toR3 (tightVertex i)‖ :=
        norm_so3_apply _ innerRot_mem _
    _ = ‖toR3 (tightVertex i) - exactVertex i‖ := norm_sub_rev _ _
    _ ≤ 2 / 10 ^ 16 := tightVertex_exact_close i
    _ = (δQ : ℝ) := by norm_num [δQ]

theorem outerMap_close (i : VertexIndex) (j : Fin 2) :
    |outerMap (exactVertex i) j - ((outerPointQ i j : ℚ) : ℝ)| ≤
      (δQ : ℝ) := by
  rw [← outerMap_rat]
  have hdiff : outerMap (exactVertex i) j -
      outerMap (toR3 (tightVertex i)) j =
      (outerRot.toEuclideanLin
        (exactVertex i - toR3 (tightVertex i))) (dim2to3 j) := by
    rw [outerMap_coord, outerMap_coord, map_sub, PiLp.sub_apply]
  rw [hdiff]
  calc |(outerRot.toEuclideanLin
        (exactVertex i - toR3 (tightVertex i))) (dim2to3 j)|
      ≤ ‖outerRot.toEuclideanLin (exactVertex i - toR3 (tightVertex i))‖ :=
        abs_coord_le_norm _ _
    _ = ‖exactVertex i - toR3 (tightVertex i)‖ :=
        norm_so3_apply _ outerRot_mem _
    _ = ‖toR3 (tightVertex i) - exactVertex i‖ := norm_sub_rev _ _
    _ ≤ 2 / 10 ^ 16 := tightVertex_exact_close i
    _ = (δQ : ℝ) := by norm_num [δQ]

/-! ## Transferring strict positivity from the rational model -/

private theorem prod_close {x y x' y' ε : ℝ} (hx : |x - x'| ≤ ε)
    (hy : |y - y'| ≤ ε) (hx' : |x'| ≤ 4) (hy' : |y'| ≤ 4)
    (hε0 : 0 ≤ ε) (hε2 : ε ≤ 2) :
    |x * y - x' * y'| ≤ 10 * ε := by
  have hid : x * y - x' * y' =
      (x - x') * y' + x' * (y - y') + (x - x') * (y - y') := by ring
  calc |x * y - x' * y'|
      ≤ |(x - x') * y' + x' * (y - y')| + |(x - x') * (y - y')| := by
        rw [hid]; exact abs_add_le _ _
    _ ≤ |(x - x') * y'| + |x' * (y - y')| + |(x - x') * (y - y')| := by
        gcongr
        exact abs_add_le _ _
    _ = |x - x'| * |y'| + |x'| * |y - y'| + |x - x'| * |y - y'| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ ε * 4 + 4 * ε + ε * ε := by gcongr
    _ ≤ ε * 4 + 4 * ε + 2 * ε := by
        have : ε * ε ≤ 2 * ε := by nlinarith
        linarith
    _ = 10 * ε := by ring

theorem cross_pos_of_close
    {p0 p1 a0 a1 b0 b1 q0 q1 c0 c1 d0 d1 δ : ℝ}
    (hp0 : |p0 - q0| ≤ δ) (hp1 : |p1 - q1| ≤ δ)
    (ha0 : |a0 - c0| ≤ δ) (ha1 : |a1 - c1| ≤ δ)
    (hb0 : |b0 - d0| ≤ δ) (hb1 : |b1 - d1| ≤ δ)
    (hq0 : |q0| ≤ 2) (hq1 : |q1| ≤ 2) (hc0 : |c0| ≤ 2) (hc1 : |c1| ≤ 2)
    (hd0 : |d0| ≤ 2) (hd1 : |d1| ≤ 2)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hm : 40 * δ < (c0 - q0) * (d1 - q1) - (c1 - q1) * (d0 - q0)) :
    0 < (a0 - p0) * (b1 - p1) - (a1 - p1) * (b0 - p0) := by
  have hu0 : |(a0 - p0) - (c0 - q0)| ≤ 2 * δ := by
    calc |(a0 - p0) - (c0 - q0)| = |(a0 - c0) - (p0 - q0)| := by ring_nf
      _ ≤ |a0 - c0| + |p0 - q0| := abs_sub _ _
      _ ≤ 2 * δ := by linarith
  have hu1 : |(a1 - p1) - (c1 - q1)| ≤ 2 * δ := by
    calc |(a1 - p1) - (c1 - q1)| = |(a1 - c1) - (p1 - q1)| := by ring_nf
      _ ≤ |a1 - c1| + |p1 - q1| := abs_sub _ _
      _ ≤ 2 * δ := by linarith
  have hv0 : |(b0 - p0) - (d0 - q0)| ≤ 2 * δ := by
    calc |(b0 - p0) - (d0 - q0)| = |(b0 - d0) - (p0 - q0)| := by ring_nf
      _ ≤ |b0 - d0| + |p0 - q0| := abs_sub _ _
      _ ≤ 2 * δ := by linarith
  have hv1 : |(b1 - p1) - (d1 - q1)| ≤ 2 * δ := by
    calc |(b1 - p1) - (d1 - q1)| = |(b1 - d1) - (p1 - q1)| := by ring_nf
      _ ≤ |b1 - d1| + |p1 - q1| := abs_sub _ _
      _ ≤ 2 * δ := by linarith
  have hc0q : |c0 - q0| ≤ 4 := by
    calc |c0 - q0| ≤ |c0| + |q0| := abs_sub _ _
      _ ≤ 4 := by linarith
  have hc1q : |c1 - q1| ≤ 4 := by
    calc |c1 - q1| ≤ |c1| + |q1| := abs_sub _ _
      _ ≤ 4 := by linarith
  have hd0q : |d0 - q0| ≤ 4 := by
    calc |d0 - q0| ≤ |d0| + |q0| := abs_sub _ _
      _ ≤ 4 := by linarith
  have hd1q : |d1 - q1| ≤ 4 := by
    calc |d1 - q1| ≤ |d1| + |q1| := abs_sub _ _
      _ ≤ 4 := by linarith
  have h2δ0 : 0 ≤ 2 * δ := by linarith
  have h2δ2 : 2 * δ ≤ 2 := by linarith
  have hprod1 : |(a0 - p0) * (b1 - p1) - (c0 - q0) * (d1 - q1)| ≤
      10 * (2 * δ) := prod_close hu0 hv1 hc0q hd1q h2δ0 h2δ2
  have hprod2 : |(a1 - p1) * (b0 - p0) - (c1 - q1) * (d0 - q0)| ≤
      10 * (2 * δ) := prod_close hu1 hv0 hc1q hd0q h2δ0 h2δ2
  have h1 := abs_le.mp hprod1
  have h2 := abs_le.mp hprod2
  linarith [h1.1, h2.2]

/-! ## Interior of a positively oriented triangle -/

/-- Twice the signed area of a real plane triangle. -/
noncomputable def crossR (p a b : ℝ²) : ℝ :=
  (a 0 - p 0) * (b 1 - p 1) - (a 1 - p 1) * (b 0 - p 0)

theorem mem_interior_triangle {P A B C : ℝ²}
    (h1 : 0 < crossR P B C) (h2 : 0 < crossR P C A)
    (h3 : 0 < crossR P A B) :
    P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²)) := by
  have hsum : crossR A B C = crossR P B C + crossR P C A + crossR P A B := by
    unfold crossR; ring
  have hT : 0 < crossR A B C := by rw [hsum]; linarith
  set f : Fin 3 → ℝ² := ![A, B, C] with hf
  have hrange : Set.range f = {A, B, C} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [hf]
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hind : AffineIndependent ℝ f := by
    rw [affineIndependent_iff_not_collinear, hrange]
    intro hcol
    obtain ⟨v, hv⟩ := (collinear_iff_of_mem
      (Set.mem_insert A {B, C})).mp hcol
    obtain ⟨rB, hrB⟩ := hv B (by simp)
    obtain ⟨rC, hrC⟩ := hv C (by simp)
    have hB0 : B 0 = rB * v 0 + A 0 := by
      rw [hrB]; simp [PiLp.add_apply, PiLp.smul_apply]
    have hB1 : B 1 = rB * v 1 + A 1 := by
      rw [hrB]; simp [PiLp.add_apply, PiLp.smul_apply]
    have hC0 : C 0 = rC * v 0 + A 0 := by
      rw [hrC]; simp [PiLp.add_apply, PiLp.smul_apply]
    have hC1 : C 1 = rC * v 1 + A 1 := by
      rw [hrC]; simp [PiLp.add_apply, PiLp.smul_apply]
    have : crossR A B C = 0 := by
      unfold crossR
      rw [hB0, hB1, hC0, hC1]
      ring
    linarith
  have hspan : affineSpan ℝ (Set.range f) = ⊤ := by
    rw [hind.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp
  let basis : AffineBasis (Fin 3) ℝ ℝ² := ⟨f, hind, hspan⟩
  set T := crossR A B C with hTdef
  set w : Fin 3 → ℝ := ![crossR P B C / T, crossR P C A / T,
    crossR P A B / T] with hw
  have hwsum : ∑ i, w i = 1 := by
    simp only [hw, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp
    linarith [hsum]
  have hcomb : (Finset.univ.affineCombination ℝ f) w = P := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hwsum]
    have hTne : T ≠ 0 := ne_of_gt hT
    ext j
    simp only [Fin.sum_univ_three, hw, hf, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    fin_cases j <;>
      (simp only [Fin.mk_zero, Fin.mk_one]
       field_simp
       simp only [hTdef, crossR]
       ring)
  have hcoord : ∀ i, 0 < basis.coord i P := by
    intro i
    rw [← hcomb, show f = ⇑basis from rfl,
      basis.coord_apply_combination_of_mem (Finset.mem_univ i) hwsum]
    fin_cases i
    · exact div_pos h1 hT
    · exact div_pos h2 hT
    · exact div_pos h3 hT
  have hbasis_range : Set.range ⇑basis = {A, B, C} := by
    rw [show ⇑basis = f from rfl, hrange]
  rw [← hbasis_range, basis.interior_convexHull]
  exact hcoord

/-! ## Per-vertex containment -/

theorem innerVertex_mem (i : VertexIndex) :
    innerMap (exactVertex i) ∈
      interior (convexHull ℝ (⇑outerMap '' (exactVerts : Set ℝ³))) := by
  obtain ⟨hm1, hm2, hm3, hbounds⟩ := rationalChecks i
  simp only [crossQ2] at hm1 hm2 hm3
  set a := (witnessTriangle i).1 with ha
  set b := (witnessTriangle i).2.1 with hb
  set c := (witnessTriangle i).2.2 with hc
  have hδ0 : (0 : ℝ) ≤ (δQ : ℝ) := by norm_num [δQ]
  have hδ1 : (δQ : ℝ) ≤ 1 := by norm_num [δQ]
  have hsub : ({outerMap (exactVertex a), outerMap (exactVertex b),
      outerMap (exactVertex c)} : Set ℝ²) ⊆
        ⇑outerMap '' (exactVerts : Set ℝ³) := by
    rintro x (rfl | rfl | rfl) <;>
      exact ⟨exactVertex _, by simp [exactVerts], rfl⟩
  refine Set.mem_of_mem_of_subset ?_ (interior_mono (convexHull_mono hsub))
  apply mem_interior_triangle
  · show (0 : ℝ) < _
    apply cross_pos_of_close (innerMap_close i 0) (innerMap_close i 1)
      (outerMap_close b 0) (outerMap_close b 1)
      (outerMap_close c 0) (outerMap_close c 1)
      _ _ _ _ _ _ hδ0 hδ1
    · exact_mod_cast hm1
    · exact_mod_cast (hbounds 0).1
    · exact_mod_cast (hbounds 1).1
    · exact_mod_cast (hbounds 0).2.2.1
    · exact_mod_cast (hbounds 1).2.2.1
    · exact_mod_cast (hbounds 0).2.2.2
    · exact_mod_cast (hbounds 1).2.2.2
  · show (0 : ℝ) < _
    apply cross_pos_of_close (innerMap_close i 0) (innerMap_close i 1)
      (outerMap_close c 0) (outerMap_close c 1)
      (outerMap_close a 0) (outerMap_close a 1)
      _ _ _ _ _ _ hδ0 hδ1
    · exact_mod_cast hm2
    · exact_mod_cast (hbounds 0).1
    · exact_mod_cast (hbounds 1).1
    · exact_mod_cast (hbounds 0).2.2.2
    · exact_mod_cast (hbounds 1).2.2.2
    · exact_mod_cast (hbounds 0).2.1
    · exact_mod_cast (hbounds 1).2.1
  · show (0 : ℝ) < _
    apply cross_pos_of_close (innerMap_close i 0) (innerMap_close i 1)
      (outerMap_close a 0) (outerMap_close a 1)
      (outerMap_close b 0) (outerMap_close b 1)
      _ _ _ _ _ _ hδ0 hδ1
    · exact_mod_cast hm3
    · exact_mod_cast (hbounds 0).1
    · exact_mod_cast (hbounds 1).1
    · exact_mod_cast (hbounds 0).2.1
    · exact_mod_cast (hbounds 1).2.1
    · exact_mod_cast (hbounds 0).2.2.1
    · exact_mod_cast (hbounds 1).2.2.1

end RupertWitness

open RupertWitness in
/-- **The exact fivefold-symmetric Nopert #214 is Rupert.**  The witness
pose threads the polyhedron through itself with a clearance of roughly
`1.8e-8`. -/
theorem isRupert_exactVerts : IsRupert exactVerts := by
  refine ⟨innerRot, innerRot_mem, offsetR, outerRot, outerRot_mem, ?_⟩
  intro hull inner_shadow outer_shadow
  have h_inner : inner_shadow = ⇑innerMap '' hull := by
    change _ = (fun p => offsetR + proj_xyL (innerRot.toEuclideanLin p)) '' _
    rw [← proj_xy_eq_proj_xyL]
    rfl
  have h_outer : outer_shadow = ⇑outerMap '' hull := by
    change _ = (fun p => proj_xyL (outerRot.toEuclideanLin p)) '' _
    rw [← proj_xy_eq_proj_xyL]
    rfl
  rw [h_inner, h_outer, show hull = convexHull ℝ (exactVerts : Set ℝ³)
    from rfl, AffineMap.image_convexHull, AffineMap.image_convexHull]
  apply convexHull_min
  · rintro x ⟨v, hv, rfl⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    exact innerVertex_mem i
  · exact (convex_convexHull ℝ _).interior

end Noperthedron.Nopert214

end
