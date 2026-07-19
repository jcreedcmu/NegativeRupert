module

public import Noperthedron.SnubCube.Vertices

@[expose] public section


/-!
# Rational snub-cube vertices

The computational certificate uses rational vertices.  This file connects
them to the exact tribonacci model with a uniform coordinate error bound.
-/

namespace Noperthedron.SnubCube

/-- Lower endpoint of the certified tribonacci enclosure. -/
def tribonacciQ : ℚ := 1839286755214161 / 10 ^ 15

def rationalVertex (i : VertexIndex) : Fin 3 → ℚ :=
  let base : Fin 3 → ℚ := ![tribonacciQ, 1, tribonacciQ ^ 2]
  fun c => (signPattern i.permutation i.signs c : ℚ) *
    permute3 i.permutation base c

def rationalPolyhedron : Polyhedron VertexIndex (Fin 3 → ℚ) := ⟨rationalVertex⟩

noncomputable def approxVertex (i : VertexIndex) : ℝ³ := toR3 (rationalVertex i)

noncomputable def approxPolyhedron : Polyhedron VertexIndex ℝ³ :=
  rationalPolyhedron.toReal

theorem approxPolyhedron_vertex (i : VertexIndex) :
    approxPolyhedron.v i = approxVertex i := rfl

theorem tribonacciQ_cast : (tribonacciQ : ℝ) = 1839286755214161 / 10 ^ 15 := by
  norm_num [tribonacciQ]

theorem tribonacciQ_le : (tribonacciQ : ℝ) ≤ tribonacci := by
  rw [tribonacciQ_cast]
  exact tribonacci_enclosure.1

theorem tribonacci_sub_approx_le :
    tribonacci - (tribonacciQ : ℝ) ≤ 1 / 10 ^ 15 := by
  rw [tribonacciQ_cast]
  linarith [tribonacci_enclosure.2]

theorem tribonacci_sq_sub_approx_sq_le :
    tribonacci ^ 2 - (tribonacciQ : ℝ) ^ 2 ≤ 4 / 10 ^ 15 := by
  have hdiff0 : 0 ≤ tribonacci - (tribonacciQ : ℝ) := sub_nonneg.mpr tribonacciQ_le
  have hsum0 : 0 ≤ tribonacci + (tribonacciQ : ℝ) := by
    rw [tribonacciQ_cast]
    exact add_nonneg tribonacci_pos.le (by norm_num)
  have hsum4 : tribonacci + (tribonacciQ : ℝ) ≤ 4 := by
    rw [tribonacciQ_cast]
    linarith [tribonacci_mem_Icc.2]
  have hmul := mul_le_mul tribonacci_sub_approx_le hsum4 hsum0
    (show 0 ≤ 1 / 10 ^ 15 by positivity)
  rw [show tribonacci ^ 2 - (tribonacciQ : ℝ) ^ 2 =
    (tribonacci - (tribonacciQ : ℝ)) * (tribonacci + (tribonacciQ : ℝ)) by ring]
  norm_num at hmul ⊢
  exact hmul

private theorem base_coordinate_error (c : Fin 3) :
    |(![tribonacci, (1 : ℝ), tribonacci ^ 2] c) -
      (![(tribonacciQ : ℝ), (1 : ℝ), (tribonacciQ : ℝ) ^ 2] c)| ≤ 4 / 10 ^ 15 := by
  have h0 : |tribonacci - (tribonacciQ : ℝ)| ≤ 4 / 10 ^ 15 := by
    rw [abs_of_nonneg (sub_nonneg.mpr tribonacciQ_le)]
    linarith [tribonacci_sub_approx_le]
  have h1 : |(1 : ℝ) - 1| ≤ 4 / 10 ^ 15 := by norm_num
  have h2 : |tribonacci ^ 2 - (tribonacciQ : ℝ) ^ 2| ≤ 4 / 10 ^ 15 := by
    rw [abs_of_nonneg]
    · exact tribonacci_sq_sub_approx_sq_le
    · rw [show tribonacci ^ 2 - (tribonacciQ : ℝ) ^ 2 =
        (tribonacci - (tribonacciQ : ℝ)) * (tribonacci + (tribonacciQ : ℝ)) by ring]
      exact mul_nonneg (sub_nonneg.mpr tribonacciQ_le) (by
        rw [tribonacciQ_cast]
        exact add_nonneg tribonacci_pos.le (by norm_num))
  fin_cases c <;> simp at h0 h1 h2 ⊢ <;> assumption

private theorem permute3_coordinate_error (p : Fin 6) (c : Fin 3) :
    |permute3 p ![tribonacci, (1 : ℝ), tribonacci ^ 2] c -
      permute3 p ![(tribonacciQ : ℝ), (1 : ℝ), (tribonacciQ : ℝ) ^ 2] c| ≤
        4 / 10 ^ 15 := by
  fin_cases p <;> fin_cases c <;>
    first | simpa [permute3] using base_coordinate_error 0 |
      simpa [permute3] using base_coordinate_error 1 |
      simpa [permute3] using base_coordinate_error 2

private theorem abs_signPattern (p : Fin 6) (s : Fin 4) (c : Fin 3) :
    |(signPattern p s c : ℝ)| = 1 := by
  fin_cases p <;> fin_cases s <;> fin_cases c <;>
    norm_num [signPattern, permutationOdd, oddSignPattern, evenSignPattern]

theorem exact_approx_coordinate_error (i : VertexIndex) (c : Fin 3) :
    |exactVertex i c - approxVertex i c| ≤ 4 / 10 ^ 15 := by
  simp only [exactVertex, vertexAt, approxVertex, toR3, rationalVertex, PiLp.toLp_apply]
  push_cast
  have hcast :
      ((permute3 i.permutation ![tribonacciQ, (1 : ℚ), tribonacciQ ^ 2] c : ℚ) : ℝ) =
        permute3 i.permutation
          ![(tribonacciQ : ℝ), (1 : ℝ), (tribonacciQ : ℝ) ^ 2] c := by
    generalize hp : i.permutation = p
    generalize hc : c = d
    fin_cases p <;> fin_cases d <;> simp [permute3]
  rw [hcast]
  change |(signPattern i.permutation i.signs c : ℝ) *
      permute3 i.permutation ![tribonacci, (1 : ℝ), tribonacci ^ 2] c -
    (signPattern i.permutation i.signs c : ℝ) *
      permute3 i.permutation ![(tribonacciQ : ℝ), (1 : ℝ), (tribonacciQ : ℝ) ^ 2] c| ≤ _
  rw [← mul_sub, abs_mul, abs_signPattern, one_mul]
  exact permute3_coordinate_error i.permutation c

/-- Euclidean error bound used by the analytic bridge lemmas. -/
theorem exact_approx_norm_error (i : VertexIndex) :
    ‖exactVertex i - approxVertex i‖ ≤ 7 / 10 ^ 15 := by
  let d := exactVertex i - approxVertex i
  have hd (c : Fin 3) : |d c| ≤ 4 / 10 ^ 15 := by
    simpa [d] using exact_approx_coordinate_error i c
  have hd_sq (c : Fin 3) : d c ^ 2 ≤ (4 / 10 ^ 15 : ℝ) ^ 2 :=
    sq_le_sq' (abs_le.mp (hd c)).1 (abs_le.mp (hd c)).2
  have hbound : (0 : ℝ) ≤ 7 / 10 ^ 15 := by positivity
  change ‖d‖ ≤ 7 / 10 ^ 15
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hbound]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  nlinarith [hd_sq 0, hd_sq 1, hd_sq 2]

end Noperthedron.SnubCube

end
