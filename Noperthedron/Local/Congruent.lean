module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Invertible

public import Noperthedron.Basic
public import Noperthedron.Local.EpsSpanning

@[expose] public section


namespace Local

open Module
open scoped RealInnerProductSpace Real
open scoped Matrix

def Triangle.toMatrix (P : Local.Triangle) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => P j i

@[simp]
lemma Triangle.toMatrix_col (P : Local.Triangle) (j : Fin 3) : P.toMatrix.col j = P j := rfl

def Triangle.toSymMatrix (P : Local.Triangle) : Matrix (Fin 3) (Fin 3) ℝ :=
  (P.toMatrix.transpose) * P.toMatrix

@[simp]
lemma Triangle.toSymMatrix_apply (P : Triangle) (i j : Fin 3) :
    P.toSymMatrix i j = ⟪P j, P i⟫ := by
  simp [Triangle.toSymMatrix, Triangle.toMatrix, Matrix.mul_apply, Fin.sum_univ_three,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]

/--
[SY25] Lemma 35. Map the basis `Q` to the vectors `P`; equality of their Gram
matrices makes this linear map preserve inner products.
-/
lemma congruent_iff_sym_matrix_eq (P Q : Triangle) (hQ : Invertible (Q.toMatrix)) :
    P.Congruent Q ↔ (P.toSymMatrix = Q.toSymMatrix) := by
  constructor
  · rintro ⟨L, hL⟩
    ext i j
    simp [Triangle.toSymMatrix_apply, hL, LinearIsometry.inner_map_map]
  · intro hSym
    classical
    have hli : LinearIndependent ℝ Q := by
      have h := Matrix.linearIndependent_cols_of_det_ne_zero
        (Matrix.isUnit_det_of_invertible Q.toMatrix).ne_zero
      exact h.map' (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap (LinearEquiv.ker _)
    let b : Basis (Fin 3) ℝ Euc(3) := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
    have hb (i : Fin 3) : b i = Q i :=
      congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli (by simp)) i
    let L : Euc(3) →ₗ[ℝ] Euc(3) := b.constr ℝ P
    have hL (i : Fin 3) : L (Q i) = P i := by rw [← hb]; exact b.constr_basis ℝ P i
    have hinner (i j : Fin 3) : ⟪P i, P j⟫ = ⟪Q i, Q j⟫ := by
      simpa using congrFun (congrFun hSym j) i
    have hisom : ∀ x y, ⟪L x, L y⟫ = ⟪x, y⟫ := by
      intro x y
      have expand (w : Euc(3)) : L w = ∑ i, b.repr w i • P i := b.constr_apply_fintype ℝ P w
      rw [expand x, expand y]
      conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
      simp [sum_inner, inner_sum,
        real_inner_smul_left, real_inner_smul_right, hb, hinner]
    exact ⟨L.isometryOfInner hisom, fun i => (hL i).symm⟩

end Local
end
