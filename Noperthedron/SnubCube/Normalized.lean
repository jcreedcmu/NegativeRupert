module

public import Noperthedron.RationalApprox.Basic
public import Noperthedron.SnubCube.Approx

@[expose] public section


/-!
# Radius-one snub-cube model

The global Taylor estimates in `Noperthedron.Global` are stated for vertices
of norm at most one.  Scaling every vertex by the same positive rational
factor does not change whether the polyhedron is Rupert, so we use the factor
`1 / 5`.  This keeps both the exact and certificate vertices especially
simple.
-/

namespace Noperthedron.SnubCube

noncomputable def normalizedExactVertex (i : VertexIndex) : ℝ³ :=
  (1 / 5 : ℝ) • exactVertex i

def normalizedRationalVertex (i : VertexIndex) : Fin 3 → ℚ :=
  fun c => rationalVertex i c / 5

noncomputable def normalizedExactPolyhedron : Polyhedron VertexIndex ℝ³ :=
  ⟨normalizedExactVertex⟩

def normalizedRationalPolyhedron : Polyhedron VertexIndex (Fin 3 → ℚ) :=
  ⟨normalizedRationalVertex⟩

private theorem exactVertex_norm_le_five (i : VertexIndex) :
    ‖exactVertex i‖ ≤ 5 := by
  obtain ⟨p, s⟩ := i
  have ht0 : 0 ≤ tribonacci := tribonacci_pos.le
  have ht2 : tribonacci ≤ 2 := tribonacci_mem_Icc.2
  have ht_sq : tribonacci ^ 2 ≤ 2 ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self ht0 ht2
  have ht_sq0 : 0 ≤ tribonacci ^ 2 := sq_nonneg tribonacci
  have ht_four : (tribonacci ^ 2) ^ 2 ≤ (2 ^ 2) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self ht_sq0 ht_sq
  rw [EuclideanSpace.norm_eq]
  apply (Real.sqrt_le_iff).2
  constructor
  · norm_num
  · fin_cases p <;> fin_cases s <;>
      simp [exactVertex, vertexAt, signPattern, permutationOdd, oddSignPattern,
        evenSignPattern, permute3, Fin.sum_univ_three] <;>
      nlinarith

theorem normalizedExactVertex_norm_le_one (i : VertexIndex) :
    ‖normalizedExactVertex i‖ ≤ 1 := by
  rw [normalizedExactVertex, norm_smul]
  norm_num
  linarith [exactVertex_norm_le_five i]

private theorem exactVertex_ne_zero (i : VertexIndex) : exactVertex i ≠ 0 := by
  obtain ⟨p, s⟩ := i
  have ht : tribonacci ≠ 0 := ne_of_gt tribonacci_pos
  intro h
  have hcoord := congrFun (congrArg WithLp.ofLp h) (0 : Fin 3)
  fin_cases p <;> fin_cases s <;>
    simp [exactVertex, vertexAt, signPattern, permutationOdd, oddSignPattern,
      evenSignPattern, permute3] at hcoord <;>
    exact ht hcoord

theorem normalizedExactVertex_norm_pos (i : VertexIndex) :
    0 < ‖normalizedExactVertex i‖ := by
  rw [norm_pos_iff, normalizedExactVertex, smul_ne_zero_iff]
  exact ⟨by norm_num, exactVertex_ne_zero i⟩

noncomputable def normalizedGoodPoly : GoodPoly VertexIndex where
  vertices := normalizedExactPolyhedron
  nontriv := normalizedExactVertex_norm_pos
  vertex_radius_le_one := normalizedExactVertex_norm_le_one

theorem toR3_normalizedRationalVertex (i : VertexIndex) :
    toR3 (normalizedRationalVertex i) = (1 / 5 : ℝ) • approxVertex i := by
  ext c
  simp [normalizedRationalVertex, approxVertex, toR3, div_eq_mul_inv, mul_comm]

theorem normalized_exact_approx_norm_error (i : VertexIndex) :
    ‖normalizedExactVertex i - toR3 (normalizedRationalVertex i)‖ ≤ 7 / (5 * 10 ^ 15) := by
  rw [normalizedExactVertex, toR3_normalizedRationalVertex, ← smul_sub, norm_smul]
  norm_num
  nlinarith [exact_approx_norm_error i]

noncomputable def normalizedApproximation :
    RationalApprox.κApproxPoly normalizedGoodPoly.vertices normalizedRationalPolyhedron where
  bijection := Equiv.refl VertexIndex
  approx := by
    intro i
    simpa [normalizedGoodPoly, normalizedExactPolyhedron, normalizedRationalPolyhedron]
      using (normalized_exact_approx_norm_error i).trans (by
        unfold RationalApprox.κ
        norm_num)

end Noperthedron.SnubCube

end
