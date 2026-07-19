module

public import Noperthedron.SnubCube.Normalized
public import Noperthedron.Rupert.Basic

@[expose] public section


/-!
# Exact rotational symmetries of the snub cube

The 24 vertex matrices below are the orientation-reversing signed
permutations that carry the seed `(t, 1, t²)` to the vertices of the chosen
snub-cube chirality.  Quotients of two such matrices are therefore the 24
orientation-preserving rotational symmetries.
-/

namespace Noperthedron.SnubCube

open scoped Matrix

/-- Coordinate selected in each row of `permute3`. -/
def coordinatePermutation : Fin 6 → Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2],
    ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

/-- Integral signed permutation matrix carrying the seed to vertex `i`. -/
def vertexMatrixInt (i : VertexIndex) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun c k => if coordinatePermutation i.permutation c = k then
    signPattern i.permutation i.signs c else 0

/-- The same vertex matrix over the reals. -/
def vertexMatrix (i : VertexIndex) : Matrix (Fin 3) (Fin 3) ℝ :=
  (vertexMatrixInt i).map fun z => (z : ℝ)

theorem vertexMatrix_mulVec_seed (t : ℝ) (i : VertexIndex) :
    WithLp.toLp 2 (vertexMatrix i *ᵥ ![t, 1, t ^ 2]) = vertexAt t i := by
  obtain ⟨p, s⟩ := i
  ext c
  fin_cases p <;> fin_cases s <;> fin_cases c <;>
    simp [vertexMatrix, vertexMatrixInt, coordinatePermutation, vertexAt, permute3,
      signPattern, permutationOdd, oddSignPattern, evenSignPattern,
      Matrix.mulVec, dotProduct]

/-- Integral rotation represented by vertex `g`, relative to vertex zero.
Since vertex zero has matrix `-I`, the quotient is `-vertexMatrixInt g`. -/
def symmetryMatrixInt (g : VertexIndex) : Matrix (Fin 3) (Fin 3) ℤ :=
  -vertexMatrixInt g

/-- The same symmetry matrix over the reals. -/
def symmetryMatrix (g : VertexIndex) : Matrix (Fin 3) (Fin 3) ℝ :=
  (symmetryMatrixInt g).map fun z => (z : ℝ)

/-- The average of all rotational symmetry matrices is zero. -/
theorem sum_symmetryMatrix :
    ∑ g : VertexIndex, symmetryMatrix g = 0 := by
  ext i j
  change ∑ g : VertexIndex, (symmetryMatrixInt g i j : ℝ) = 0
  norm_cast
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem symmetryMatrixInt_mul_transpose (g : VertexIndex) :
    symmetryMatrixInt g * (symmetryMatrixInt g)ᵀ = 1 := by
  obtain ⟨p, s⟩ := g
  fin_cases p <;> fin_cases s <;> decide

private theorem symmetryMatrixInt_det (g : VertexIndex) :
    (symmetryMatrixInt g).det = 1 := by
  obtain ⟨p, s⟩ := g
  fin_cases p <;> fin_cases s <;> decide

/-- Compact enumeration index used by the checked symmetry action table. -/
def VertexIndex.toFin24 (i : VertexIndex) : Fin 24 :=
  ⟨4 * i.permutation.val + i.signs.val, by omega⟩

/-- Left multiplication of the 24 signed vertex matrices by each of the 24
rotation matrices. -/
def symmetryActionTable : Fin 24 → Fin 24 → Fin 24 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22],
  ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21],
  ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20],
  ![4, 6, 5, 7, 0, 2, 1, 3, 12, 14, 13, 15, 8, 10, 9, 11, 20, 22, 21, 23, 16, 18, 17, 19],
  ![5, 7, 4, 6, 1, 3, 0, 2, 13, 15, 12, 14, 9, 11, 8, 10, 21, 23, 20, 22, 17, 19, 16, 18],
  ![6, 4, 7, 5, 2, 0, 3, 1, 14, 12, 15, 13, 10, 8, 11, 9, 22, 20, 23, 21, 18, 16, 19, 17],
  ![7, 5, 6, 4, 3, 1, 2, 0, 15, 13, 14, 12, 11, 9, 10, 8, 23, 21, 22, 20, 19, 17, 18, 16],
  ![8, 9, 11, 10, 17, 16, 18, 19, 1, 0, 2, 3, 20, 21, 23, 22, 4, 5, 7, 6, 13, 12, 14, 15],
  ![9, 8, 10, 11, 16, 17, 19, 18, 0, 1, 3, 2, 21, 20, 22, 23, 5, 4, 6, 7, 12, 13, 15, 14],
  ![10, 11, 9, 8, 19, 18, 16, 17, 3, 2, 0, 1, 22, 23, 21, 20, 6, 7, 5, 4, 15, 14, 12, 13],
  ![11, 10, 8, 9, 18, 19, 17, 16, 2, 3, 1, 0, 23, 22, 20, 21, 7, 6, 4, 5, 14, 15, 13, 12],
  ![12, 14, 15, 13, 22, 20, 21, 23, 6, 4, 5, 7, 16, 18, 19, 17, 0, 2, 3, 1, 10, 8, 9, 11],
  ![13, 15, 14, 12, 23, 21, 20, 22, 7, 5, 4, 6, 17, 19, 18, 16, 1, 3, 2, 0, 11, 9, 8, 10],
  ![14, 12, 13, 15, 20, 22, 23, 21, 4, 6, 7, 5, 18, 16, 17, 19, 2, 0, 1, 3, 8, 10, 11, 9],
  ![15, 13, 12, 14, 21, 23, 22, 20, 5, 7, 6, 4, 19, 17, 16, 18, 3, 1, 0, 2, 9, 11, 10, 8],
  ![16, 19, 17, 18, 9, 10, 8, 11, 21, 22, 20, 23, 0, 3, 1, 2, 12, 15, 13, 14, 5, 6, 4, 7],
  ![17, 18, 16, 19, 8, 11, 9, 10, 20, 23, 21, 22, 1, 2, 0, 3, 13, 14, 12, 15, 4, 7, 5, 6],
  ![18, 17, 19, 16, 11, 8, 10, 9, 23, 20, 22, 21, 2, 1, 3, 0, 14, 13, 15, 12, 7, 4, 6, 5],
  ![19, 16, 18, 17, 10, 9, 11, 8, 22, 21, 23, 20, 3, 0, 2, 1, 15, 12, 14, 13, 6, 5, 7, 4],
  ![20, 23, 22, 21, 14, 13, 12, 15, 18, 17, 16, 19, 4, 7, 6, 5, 8, 11, 10, 9, 2, 1, 0, 3],
  ![21, 22, 23, 20, 15, 12, 13, 14, 19, 16, 17, 18, 5, 6, 7, 4, 9, 10, 11, 8, 3, 0, 1, 2],
  ![22, 21, 20, 23, 12, 15, 14, 13, 16, 19, 18, 17, 6, 5, 4, 7, 10, 9, 8, 11, 0, 3, 2, 1],
  ![23, 20, 21, 22, 13, 14, 15, 12, 17, 18, 19, 16, 7, 4, 5, 6, 11, 8, 9, 10, 1, 2, 3, 0]
]

/-- Permutation of vertices induced by a rotational symmetry. -/
def symmetryAction (g i : VertexIndex) : VertexIndex :=
  VertexIndex.ofFin24 (symmetryActionTable g.toFin24 i.toFin24)

/-- Kernel-reduced verification of the complete integer action table. -/
theorem symmetryMatrixInt_mul_vertexMatrixInt (g i : VertexIndex) :
    symmetryMatrixInt g * vertexMatrixInt i =
      vertexMatrixInt (symmetryAction g i) := by
  obtain ⟨gp, gs⟩ := g
  obtain ⟨ip, is⟩ := i
  fin_cases gp <;> fin_cases gs <;> fin_cases ip <;> fin_cases is <;> decide

theorem symmetryMatrix_mul_vertexMatrix (g i : VertexIndex) :
    symmetryMatrix g * vertexMatrix i = vertexMatrix (symmetryAction g i) := by
  change (symmetryMatrixInt g).map (Int.castRingHom ℝ) *
      (vertexMatrixInt i).map (Int.castRingHom ℝ) =
    (vertexMatrixInt (symmetryAction g i)).map (Int.castRingHom ℝ)
  rw [← Matrix.map_mul, symmetryMatrixInt_mul_vertexMatrixInt]

theorem symmetryMatrix_mem_SO3 (g : VertexIndex) :
    symmetryMatrix g ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · change (symmetryMatrixInt g).map (Int.castRingHom ℝ) *
        ((symmetryMatrixInt g).map (Int.castRingHom ℝ))ᵀ = 1
    rw [← Matrix.transpose_map, ← Matrix.map_mul,
      symmetryMatrixInt_mul_transpose]
    simp
  · calc
      (symmetryMatrix g).det = ((symmetryMatrixInt g).det : ℝ) :=
        (Int.cast_det (symmetryMatrixInt g)).symm
      _ = 1 := by rw [symmetryMatrixInt_det]; norm_num

/-- The exact snub-cube rotation indexed by `g`. -/
def symmetry (g : VertexIndex) : SO3 :=
  ⟨symmetryMatrix g, symmetryMatrix_mem_SO3 g⟩

/-- Index zero is the identity rotation. -/
@[simp] theorem symmetry_zero : symmetry (VertexIndex.ofFin24 0) = 1 := by
  apply Subtype.ext
  change (symmetryMatrixInt (VertexIndex.ofFin24 0)).map
      (Int.castRingHom ℝ) = 1
  have h : symmetryMatrixInt (VertexIndex.ofFin24 0) =
      (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
    decide +kernel
  rw [h]
  simp

@[simp] theorem symmetryAction_zero (i : VertexIndex) :
    symmetryAction (VertexIndex.ofFin24 0) i = i := by
  decide +kernel +revert

theorem symmetry_apply_exactVertex (g i : VertexIndex) :
    (symmetry g).val.toEuclideanLin (exactVertex i) =
      exactVertex (symmetryAction g i) := by
  rw [exactVertex, ← vertexMatrix_mulVec_seed tribonacci i,
    exactVertex, ← vertexMatrix_mulVec_seed tribonacci (symmetryAction g i)]
  simp only [symmetry, Matrix.toLpLin_apply]
  rw [Matrix.mulVec_mulVec, symmetryMatrix_mul_vertexMatrix]

theorem symmetry_apply_normalizedExactVertex (g i : VertexIndex) :
    (symmetry g).val.toEuclideanLin (normalizedExactVertex i) =
      normalizedExactVertex (symmetryAction g i) := by
  simp only [normalizedExactVertex, map_smul]
  rw [symmetry_apply_exactVertex]

end Noperthedron.SnubCube

end
