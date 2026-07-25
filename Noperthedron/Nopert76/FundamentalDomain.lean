module

public import Mathlib.Data.Finset.Max
public import Noperthedron.Nopert76.CayleyAtlas

@[expose] public section

/-!
# Fivefold relative-rotation fundamental domain

Right composition of the inner copy by an exact fivefold symmetry does not
change its shadow.  We choose the representative maximizing matrix trace.
This Dirichlet condition is later converted to two quadratic inequalities in
each Cayley chart, allowing most of relative-rotation space to be pruned
before geometric certificates are attempted.
-/

namespace Noperthedron.Nopert76

open scoped Matrix

/-- The `k`th exact rotation around the symmetry axis. -/
noncomputable def fivefoldMatrix (k : OrbitIndex) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Rz_mat ((k : ℝ) * (2 * Real.pi / 5))

theorem fivefoldMatrix_mem_SO3 (k : OrbitIndex) :
    fivefoldMatrix k ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  exact MatrixPose.Rz_mat_mem_SO3 _

noncomputable def fivefoldSO3 (k : OrbitIndex) : SO3 :=
  ⟨fivefoldMatrix k, fivefoldMatrix_mem_SO3 k⟩

def composeSymmetry (a b : OrbitIndex) : OrbitIndex :=
  ⟨(a.val + b.val) % 5, Nat.mod_lt _ (by omega)⟩

@[simp] theorem fivefoldMatrix_zero : fivefoldMatrix 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fivefoldMatrix, Rz_mat]

theorem fivefoldMatrix_mul (a b : OrbitIndex) :
    fivefoldMatrix a * fivefoldMatrix b =
      fivefoldMatrix (composeSymmetry a b) := by
  change Rz_mat ((a : ℝ) * (2 * Real.pi / 5)) *
      Rz_mat ((b : ℝ) * (2 * Real.pi / 5)) =
    Rz_mat ((composeSymmetry a b : ℝ) * (2 * Real.pi / 5))
  rw [Bounding.Rz_mat_mul_Rz_mat]
  have hdecomp : (a.val : ℝ) + (b.val : ℝ) =
      (((a.val + b.val) % 5 : ℕ) : ℝ) +
        5 * (((a.val + b.val) / 5 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div (a.val + b.val) 5).symm
  have hangle :
      (a : ℝ) * (2 * Real.pi / 5) +
          (b : ℝ) * (2 * Real.pi / 5) =
        (composeSymmetry a b : ℝ) * (2 * Real.pi / 5) +
          ((((a.val + b.val) / 5 : ℕ) : ℝ) * (2 * Real.pi)) := by
    change (a.val : ℝ) * (2 * Real.pi / 5) +
        (b.val : ℝ) * (2 * Real.pi / 5) =
      (((a.val + b.val) % 5 : ℕ) : ℝ) * (2 * Real.pi / 5) +
        ((((a.val + b.val) / 5 : ℕ) : ℝ) * (2 * Real.pi))
    calc
      _ = ((a.val : ℝ) + b.val) * (2 * Real.pi / 5) := by ring
      _ = ((((a.val + b.val) % 5 : ℕ) : ℝ) +
          5 * (((a.val + b.val) / 5 : ℕ) : ℝ)) *
            (2 * Real.pi / 5) := by rw [hdecomp]
      _ = _ := by ring
  rw [hangle]
  convert Rz_mat_add_int_mul_two_pi
    (Int.ofNat ((a.val + b.val) / 5))
    ((composeSymmetry a b : ℝ) * (2 * Real.pi / 5)) using 1 <;>
    norm_num

/-- Every exact fivefold rotation maps the exact hull onto itself. -/
theorem fivefoldMatrix_image_hull (k : OrbitIndex) :
    (fivefoldMatrix k).toEuclideanLin '' exactPolyhedron.hull =
      exactPolyhedron.hull := by
  change RzL ((k : ℝ) * (2 * Real.pi / 5)) '' exactPolyhedron.hull = _
  exact rotate_hull_iterated_nat k.val

/-- Compose only the inner rotation by an exact symmetry. -/
noncomputable def _root_.MatrixPose.rightNopert76Symmetry
    (p : MatrixPose) (k : OrbitIndex) : MatrixPose where
  innerRot := p.innerRot * fivefoldSO3 k
  outerRot := p.outerRot
  innerOffset := p.innerOffset

theorem innerShadow_rightNopert76Symmetry
    (p : MatrixPose) (k : OrbitIndex) :
    innerShadow (p.rightNopert76Symmetry k) exactPolyhedron.hull =
      innerShadow p exactPolyhedron.hull := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hgv : (fivefoldMatrix k).toEuclideanLin v ∈
        exactPolyhedron.hull := by
      rw [← fivefoldMatrix_image_hull k]
      exact ⟨v, hv, rfl⟩
    refine ⟨(fivefoldMatrix k).toEuclideanLin v, hgv, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.rightNopert76Symmetry,
      fivefoldSO3, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (fivefoldMatrix k).toEuclideanLin ''
        exactPolyhedron.hull := by
      rwa [fivefoldMatrix_image_hull k]
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨u, hu, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.rightNopert76Symmetry,
      fivefoldSO3, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

@[simp] theorem outerShadow_rightNopert76Symmetry
    (p : MatrixPose) (k : OrbitIndex) :
    outerShadow (p.rightNopert76Symmetry k) exactPolyhedron.hull =
      outerShadow p exactPolyhedron.hull := by
  rfl

theorem RupertPose_rightNopert76Symmetry_iff
    (p : MatrixPose) (k : OrbitIndex) :
    RupertPose (p.rightNopert76Symmetry k) exactPolyhedron.hull ↔
      RupertPose p exactPolyhedron.hull := by
  simp only [RupertPose, innerShadow_rightNopert76Symmetry,
    outerShadow_rightNopert76Symmetry]

/-- A relative rotation is in the identity fivefold Dirichlet cell when no
right symmetry increases its trace. -/
def InFivefoldFundamentalDomain
    (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ k : OrbitIndex,
    Matrix.trace (R * fivefoldMatrix k) ≤ Matrix.trace R

theorem exists_mul_fivefold_inFundamentalDomain
    (R : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ k : OrbitIndex,
      InFivefoldFundamentalDomain (R * fivefoldMatrix k) := by
  obtain ⟨k, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j : OrbitIndex => Matrix.trace (R * fivefoldMatrix j))
    Finset.univ_nonempty
  refine ⟨k, fun j => ?_⟩
  rw [Matrix.mul_assoc, fivefoldMatrix_mul]
  exact hmax (composeSymmetry k j) (Finset.mem_univ _)

def _root_.MatrixPose.InNopert76FundamentalDomain
    (p : MatrixPose) : Prop :=
  InFivefoldFundamentalDomain p.relativeRotation

@[simp] theorem MatrixPose.relativeRotation_rightNopert76Symmetry
    (p : MatrixPose) (k : OrbitIndex) :
    (p.rightNopert76Symmetry k).relativeRotation =
      p.relativeRotation * fivefoldMatrix k := by
  simp [MatrixPose.relativeRotation,
    MatrixPose.rightNopert76Symmetry, fivefoldSO3, Matrix.mul_assoc]

theorem MatrixPose.exists_rightNopert76Symmetry_inFundamentalDomain
    (p : MatrixPose) :
    ∃ k : OrbitIndex,
      (p.rightNopert76Symmetry k).InNopert76FundamentalDomain := by
  obtain ⟨k, hk⟩ := exists_mul_fivefold_inFundamentalDomain p.relativeRotation
  exact ⟨k, by simpa [MatrixPose.InNopert76FundamentalDomain] using hk⟩

end Noperthedron.Nopert76

end
