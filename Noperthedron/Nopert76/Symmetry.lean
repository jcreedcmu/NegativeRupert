module

public import Noperthedron.Nopert76.Approximation
public import Noperthedron.Pose
public import Noperthedron.RealMod

@[expose] public section

/-!
# Fivefold symmetry of Nopert #214

The exact model is invariant under rotation by `2π/5` around the z axis.
Consequently either Euler azimuth may be reduced modulo `2π/5` without
changing the corresponding projected hull.
-/

open Real

namespace Noperthedron.Nopert76

def nextOrbit : OrbitIndex ≃ OrbitIndex where
  toFun k := ⟨(k.val + 1) % 5, Nat.mod_lt _ (by omega)⟩
  invFun k := ⟨(k.val + 4) % 5, Nat.mod_lt _ (by omega)⟩
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

private lemma RzL_apply_add (α β : ℝ) (v : ℝ³) :
    RzL (α + β) v = RzL α (RzL β v) := by
  have h := RzC.map_add_eq_mul α β
  simp only [RzC_coe] at h
  rw [h]
  rfl

theorem rotate_vertex (k : OrbitIndex) (s : SeedIndex) :
    RzL (2 * π / 5) (exactVertex (vertexIndex k s)) =
      exactVertex (vertexIndex (nextOrbit k) s) := by
  simp only [exactVertex, orbitIndex_vertexIndex, seedIndex_vertexIndex]
  rw [← RzL_apply_add]
  fin_cases k
  · simp [nextOrbit]
  · simp [nextOrbit]
    ring_nf
  · simp [nextOrbit]
    ring_nf
  · simp [nextOrbit]
    ring_nf
  · simp [nextOrbit]
    ring_nf
    rw [show π * 2 = 0 + (1 : ℤ) * (2 * π) by ring]
    simp only [RzL, Rz_mat_add_int_mul_two_pi]

theorem rotate_vertices :
    RzL (2 * π / 5) '' (exactVerts : Set ℝ³) = exactVerts := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [exactVerts, Finset.mem_coe, Finset.mem_image,
      Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨i, rfl⟩ := hy
    let k := orbitIndex i
    let s := seedIndex i
    have hi : vertexIndex k s = i := indexEquiv.symm_apply_apply i
    refine ⟨vertexIndex (nextOrbit k) s, ?_⟩
    rw [← rotate_vertex k s, hi]
  · intro hx
    simp only [exactVerts, Finset.mem_coe, Finset.mem_image,
      Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    let k := orbitIndex i
    let s := seedIndex i
    have hi : vertexIndex k s = i := indexEquiv.symm_apply_apply i
    let p := nextOrbit.symm k
    refine ⟨exactVertex (vertexIndex p s), ?_, ?_⟩
    · simp only [exactVerts, Finset.mem_coe, Finset.mem_image,
        Finset.mem_univ, true_and]
      exact ⟨vertexIndex p s, rfl⟩
    · rw [rotate_vertex p s, nextOrbit.apply_symm_apply, hi]

theorem rotate_hull :
    RzL (2 * π / 5) '' exactPolyhedron.hull = exactPolyhedron.hull := by
  rw [exactPolyhedron_hull]
  change (RzL (2 * π / 5)).toLinearMap '' convexHull ℝ (exactVerts : Set ℝ³) =
    convexHull ℝ (exactVerts : Set ℝ³)
  rw [LinearMap.image_convexHull]
  congr 1
  simpa using rotate_vertices

/-- Every nonnegative power of the generating fivefold rotation preserves
the exact hull. -/
theorem rotate_hull_iterated_nat (n : ℕ) :
    RzL ((n : ℝ) * (2 * π / 5)) '' exactPolyhedron.hull =
      exactPolyhedron.hull := by
  induction n with
  | zero =>
      have hzero : RzL 0 = ContinuousLinearMap.id ℝ ℝ³ := by
        apply ContinuousLinearMap.ext
        intro v
        ext i
        fin_cases i <;>
          simp [RzL, Rz_mat, Matrix.toLpLin_apply,
            dotProduct, Fin.sum_univ_three]
      rw [Nat.cast_zero, zero_mul, hzero]
      exact Set.image_id _
  | succ n ih =>
      have hangle : ((n + 1 : ℕ) : ℝ) * (2 * π / 5) =
          2 * π / 5 + (n : ℝ) * (2 * π / 5) := by
        push_cast
        ring
      have hmap : RzL (((n + 1 : ℕ) : ℝ) * (2 * π / 5)) =
          RzL (2 * π / 5) ∘L RzL ((n : ℝ) * (2 * π / 5)) := by
        rw [hangle]
        apply ContinuousLinearMap.ext
        intro v
        exact RzL_apply_add _ _ v
      rw [hmap]
      push_cast
      rw [Set.image_comp, ih, rotate_hull]

/-- A single symmetry step does not change the shadow at fixed inclination. -/
theorem rotM_add_fifth (θ φ : ℝ) :
    rotM (θ + 2 * π / 5) φ '' exactPolyhedron.hull =
      rotM θ φ '' exactPolyhedron.hull := by
  repeat rw [rotM_identity]
  push_cast
  have hmap : RzL (-(θ + 2 * π / 5)) =
      RzL (-θ) ∘L RzL (-(2 * π / 5)) := by
    ext v
    rw [show -(θ + 2 * π / 5) = -θ + -(2 * π / 5) by ring,
      RzL_apply_add]
    rfl
  have hneg : RzL (-(2 * π / 5)) '' exactPolyhedron.hull =
      exactPolyhedron.hull := by
    have hinv (v : ℝ³) :
        RzL (-(2 * π / 5)) (RzL (2 * π / 5) v) = v := by
      rw [← RzL_apply_add,
        show -(2 * π / 5) + 2 * π / 5 = 0 by ring]
      ext i
      fin_cases i <;> simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyimg : y ∈ RzL (2 * π / 5) '' exactPolyhedron.hull := by
        rw [rotate_hull]
        exact hy
      obtain ⟨z, hz, rfl⟩ := hyimg
      rw [hinv]
      exact hz
    · intro hx
      refine ⟨RzL (2 * π / 5) x, ?_, hinv x⟩
      have hmem : RzL (2 * π / 5) x ∈
          RzL (2 * π / 5) '' exactPolyhedron.hull := ⟨x, hx, rfl⟩
      rwa [rotate_hull] at hmem
  rw [hmap]
  push_cast
  repeat rw [Set.image_comp]
  rw [hneg]

theorem rotM_add_fifth_iterated {θ φ : ℝ} (n : ℤ) :
    rotM (θ + n * (2 * π / 5)) φ '' exactPolyhedron.hull =
      rotM θ φ '' exactPolyhedron.hull := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n hn =>
      rw [← hn]
      push_cast
      have h := rotM_add_fifth (θ + n * (2 * π / 5)) φ
      ring_nf at h ⊢
      exact h
  | pred n hn =>
      rw [← hn]
      push_cast
      have h := rotM_add_fifth (θ + (-1 - n) * (2 * π / 5)) φ
      ring_nf at h ⊢
      exact h.symm

end Noperthedron.Nopert76

end
