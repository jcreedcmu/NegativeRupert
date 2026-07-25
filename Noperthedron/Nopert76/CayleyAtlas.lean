module

public import Noperthedron.Nopert76.Tightening
public import Noperthedron.SnubCube.CayleyInterval

@[expose] public section

/-!
# A four-chart bounded Cayley atlas

The four diagonal half-turns give a particularly small rational atlas for
`SO(3)`.  For every rotation, the traces after left multiplication by these
four matrices sum to zero.  Hence one trace is nonnegative and the existing
bounded Cayley theorem supplies coordinates in `[-2,2]³`.
-/

namespace Noperthedron.Nopert76.CayleyAtlas

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

def toggleX : ChartIndex → ChartIndex := ![1, 0, 3, 2]
def toggleY : ChartIndex → ChartIndex := ![2, 3, 0, 1]
def toggleZ : ChartIndex → ChartIndex := ![3, 2, 1, 0]

@[simp] theorem chartMatrix_toggleX_mul (chart : ChartIndex) :
    chartMatrix (toggleX chart) * chartMatrix chart = chartMatrix 1 := by
  ext i j
  fin_cases chart <;> fin_cases i <;> fin_cases j <;>
    norm_num [toggleX, chartMatrix, Matrix.mul_apply, Fin.sum_univ_three]

@[simp] theorem chartMatrix_toggleY_mul (chart : ChartIndex) :
    chartMatrix (toggleY chart) * chartMatrix chart = chartMatrix 2 := by
  ext i j
  fin_cases chart <;> fin_cases i <;> fin_cases j <;>
    norm_num [toggleY, chartMatrix, Matrix.mul_apply, Fin.sum_univ_three]

@[simp] theorem chartMatrix_toggleZ_mul (chart : ChartIndex) :
    chartMatrix (toggleZ chart) * chartMatrix chart = chartMatrix 3 := by
  ext i j
  fin_cases chart <;> fin_cases i <;> fin_cases j <;>
    norm_num [toggleZ, chartMatrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- Cayley coordinates in a chart whose trace is maximal among the four
diagonal half-turn charts lie in the unit cube. -/
theorem cayley_mem_unit_cube_of_maximal_chart (chart : ChartIndex)
    (x y z : ℝ)
    (hmax : ∀ other : ChartIndex,
      Matrix.trace
          (chartMatrix other * (chartMatrix chart * cayleyMatrix x y z)) ≤
        Matrix.trace
          (chartMatrix chart * (chartMatrix chart * cayleyMatrix x y z))) :
    x ∈ Set.Icc (-1 : ℝ) 1 ∧ y ∈ Set.Icc (-1 : ℝ) 1 ∧
      z ∈ Set.Icc (-1 : ℝ) 1 := by
  have hx := hmax (toggleX chart)
  have hy := hmax (toggleY chart)
  have hz := hmax (toggleZ chart)
  have hx' : Matrix.trace (chartMatrix 1 * cayleyMatrix x y z) ≤
      Matrix.trace (cayleyMatrix x y z) := by
    simpa only [← Matrix.mul_assoc, chartMatrix_toggleX_mul,
      chartMatrix_mul_self, Matrix.one_mul] using hx
  have hy' : Matrix.trace (chartMatrix 2 * cayleyMatrix x y z) ≤
      Matrix.trace (cayleyMatrix x y z) := by
    simpa only [← Matrix.mul_assoc, chartMatrix_toggleY_mul,
      chartMatrix_mul_self, Matrix.one_mul] using hy
  have hz' : Matrix.trace (chartMatrix 3 * cayleyMatrix x y z) ≤
      Matrix.trace (cayleyMatrix x y z) := by
    simpa only [← Matrix.mul_assoc, chartMatrix_toggleZ_mul,
      chartMatrix_mul_self, Matrix.one_mul] using hz
  have hd := cayleyDenom_pos x y z
  simp [chartMatrix, Matrix.trace, Matrix.mul_apply, cayleyMatrix,
    Fin.sum_univ_three] at hx' hy' hz'
  have hx'' := mul_le_mul_of_nonneg_right hx' hd.le
  have hy'' := mul_le_mul_of_nonneg_right hy' hd.le
  have hz'' := mul_le_mul_of_nonneg_right hz' hd.le
  field_simp [cayleyDenom_ne] at hx'' hy'' hz''
  constructor
  · constructor <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
  · constructor
    · constructor <;> nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1)]
    · constructor <;> nlinarith [sq_nonneg (z - 1), sq_nonneg (z + 1)]

/-- Choosing a maximum-trace chart, rather than merely a nonnegative-trace
chart, puts every Cayley coordinate in `[-1,1]`. -/
theorem exists_bounded_chart_cayley (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ chart : ChartIndex,
      ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      ∃ y ∈ Set.Icc (-1 : ℝ) 1,
      ∃ z ∈ Set.Icc (-1 : ℝ) 1,
        x ^ 2 + y ^ 2 + z ^ 2 ≤ 3 ∧
        R = chartMatrix chart * cayleyMatrix x y z := by
  obtain ⟨chart, hmax⟩ := Finite.exists_max
    (fun chart : ChartIndex ↦ Matrix.trace (chartMatrix chart * R))
  obtain ⟨nonnegativeChart, hnonnegative⟩ := exists_chart_trace_nonneg R
  have htrace : 0 ≤ Matrix.trace (chartMatrix chart * R) :=
    hnonnegative.trans (hmax nonnegativeChart)
  have hproduct : chartMatrix chart * R ∈
      Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ (chartMatrix_mem_SO3 chart) hR
  obtain ⟨x, y, z, hradius, heq⟩ :=
    exists_cayleyMatrix_of_trace_nonneg
      (chartMatrix chart * R) hproduct htrace
  have hrelative : R = chartMatrix chart * cayleyMatrix x y z := by
    calc
      R = 1 * R := by rw [Matrix.one_mul]
      _ = (chartMatrix chart * chartMatrix chart) * R := by
        rw [chartMatrix_mul_self]
      _ = chartMatrix chart * (chartMatrix chart * R) := by
        rw [Matrix.mul_assoc]
      _ = chartMatrix chart * cayleyMatrix x y z := by rw [heq]
  have hmaxC : ∀ other : ChartIndex,
      Matrix.trace
          (chartMatrix other *
            (chartMatrix chart * cayleyMatrix x y z)) ≤
        Matrix.trace
          (chartMatrix chart *
            (chartMatrix chart * cayleyMatrix x y z)) := by
    intro other
    rw [← hrelative]
    exact hmax other
  obtain ⟨hx, hy, hz⟩ :=
    cayley_mem_unit_cube_of_maximal_chart chart x y z hmaxC
  refine ⟨chart, x, hx, y, hy, z, hz, hradius, ?_⟩
  exact hrelative

end Noperthedron.Nopert76.CayleyAtlas

end
