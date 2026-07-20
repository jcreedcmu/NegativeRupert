module

public import Noperthedron.Nopert214.Tightening
public import Noperthedron.SnubCube.CayleyInterval

@[expose] public section

/-!
# A four-chart bounded Cayley atlas

The four diagonal half-turns give a particularly small rational atlas for
`SO(3)`.  For every rotation, the traces after left multiplication by these
four matrices sum to zero.  Hence one trace is nonnegative and the existing
bounded Cayley theorem supplies coordinates in `[-2,2]³`.
-/

namespace Noperthedron.Nopert214.CayleyAtlas

open scoped Matrix

abbrev ChartIndex := Fin 4

/-- Chart zero is the identity.  Chart `i + 1` is the diagonal half-turn
whose `i`th entry is `1` and whose other two entries are `-1`. -/
def chartMatrix (chart : ChartIndex) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    if i ≠ j then 0
    else if chart.val = 0 ∨ chart.val = i.val + 1 then 1 else -1

theorem chartMatrix_mem_SO3 (chart : ChartIndex) :
    chartMatrix chart ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff,
    Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases chart <;> fin_cases i <;> fin_cases j <;>
      norm_num [chartMatrix, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_three]
  · have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    fin_cases chart <;>
      norm_num [chartMatrix, Matrix.det_fin_three, h20, h21, h02, h12]

noncomputable def chartSO3 (chart : ChartIndex) : SO3 :=
  ⟨chartMatrix chart, chartMatrix_mem_SO3 chart⟩

@[simp] theorem chartMatrix_mul_self (chart : ChartIndex) :
    chartMatrix chart * chartMatrix chart = 1 := by
  ext i j
  fin_cases chart <;> fin_cases i <;> fin_cases j <;>
    norm_num [chartMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_chart_trace_nonneg (R : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ chart : ChartIndex, 0 ≤ Matrix.trace (chartMatrix chart * R) := by
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp [chartMatrix, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_three] at h0 h1 h2 h3
  linarith

theorem exists_bounded_chart_cayley (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ chart : ChartIndex,
      ∃ x ∈ Set.Icc (-2 : ℝ) 2,
      ∃ y ∈ Set.Icc (-2 : ℝ) 2,
      ∃ z ∈ Set.Icc (-2 : ℝ) 2,
        x ^ 2 + y ^ 2 + z ^ 2 ≤ 3 ∧
        R = chartMatrix chart * cayleyMatrix x y z := by
  obtain ⟨chart, htrace⟩ := exists_chart_trace_nonneg R
  have hproduct : chartMatrix chart * R ∈
      Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ (chartMatrix_mem_SO3 chart) hR
  obtain ⟨x, y, z, hradius, heq⟩ :=
    exists_cayleyMatrix_of_trace_nonneg
      (chartMatrix chart * R) hproduct htrace
  have hxSq : x ^ 2 ≤ 3 := by nlinarith [sq_nonneg y, sq_nonneg z]
  have hySq : y ^ 2 ≤ 3 := by nlinarith [sq_nonneg x, sq_nonneg z]
  have hzSq : z ^ 2 ≤ 3 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hx : x ∈ Set.Icc (-2 : ℝ) 2 := by
    constructor <;> nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2)]
  have hy : y ∈ Set.Icc (-2 : ℝ) 2 := by
    constructor <;> nlinarith [sq_nonneg (y - 2), sq_nonneg (y + 2)]
  have hz : z ∈ Set.Icc (-2 : ℝ) 2 := by
    constructor <;> nlinarith [sq_nonneg (z - 2), sq_nonneg (z + 2)]
  refine ⟨chart, x, hx, y, hy, z, hz, hradius, ?_⟩
  calc
    R = 1 * R := by rw [Matrix.one_mul]
    _ = (chartMatrix chart * chartMatrix chart) * R := by
      rw [chartMatrix_mul_self]
    _ = chartMatrix chart * (chartMatrix chart * R) := by
      rw [Matrix.mul_assoc]
    _ = chartMatrix chart * cayleyMatrix x y z := by rw [heq]

end Noperthedron.Nopert214.CayleyAtlas

end
