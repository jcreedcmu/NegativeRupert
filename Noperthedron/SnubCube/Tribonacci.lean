module

public import Noperthedron.Basic

@[expose] public section


/-!
# The tribonacci coordinate

The standard snub-cube coordinates use the unique real root in `[1,2]` of
`x^3 - x^2 - x - 1`.
-/

namespace Noperthedron.SnubCube

/-- The cubic whose positive root occurs in the snub-cube coordinates. -/
def tribonacciPolynomial (x : ℝ) : ℝ := x ^ 3 - x ^ 2 - x - 1

theorem tribonacciPolynomial_continuous : Continuous tribonacciPolynomial := by
  unfold tribonacciPolynomial
  fun_prop

theorem tribonacciPolynomial_strictMonoOn :
    StrictMonoOn tribonacciPolynomial (Set.Ici 1) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hxy_pos : 0 < y - x := sub_pos.mpr hxy
  have hfactor :
      tribonacciPolynomial y - tribonacciPolynomial x =
        (y - x) * (x ^ 2 + x * y + y ^ 2 - x - y - 1) := by
    simp only [tribonacciPolynomial]
    ring
  have hx0 : 0 ≤ x ^ 2 - x := by
    nlinarith [mul_nonneg (show 0 ≤ x by linarith) (sub_nonneg.mpr hx)]
  have hy1 : 1 < y := hx.trans_lt hxy
  have hy0 : 0 < y ^ 2 - y := by nlinarith
  have hxy0 : 0 ≤ x * y - 1 := by
    have hmul : 1 * 1 ≤ x * y := mul_le_mul hx hy (by norm_num) (by linarith)
    nlinarith
  have hsecond : 0 < x ^ 2 + x * y + y ^ 2 - x - y - 1 := by nlinarith
  have hdifference : 0 < tribonacciPolynomial y - tribonacciPolynomial x := by
    rw [hfactor]
    positivity
  linarith

theorem exists_unique_tribonacci :
    ∃! x : ℝ, x ∈ Set.Icc 1 2 ∧ tribonacciPolynomial x = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (tribonacciPolynomial 1) (tribonacciPolynomial 2) := by
    norm_num [tribonacciPolynomial]
  obtain ⟨x, hx, hroot⟩ :=
    intermediate_value_Icc (show (1 : ℝ) ≤ 2 by norm_num)
      tribonacciPolynomial_continuous.continuousOn hzero
  refine ⟨x, ⟨hx, hroot⟩, ?_⟩
  intro y hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hyx | hxy
  · have := tribonacciPolynomial_strictMonoOn hy.1.1 hx.1 hyx
    linarith [hroot, hy.2]
  · have := tribonacciPolynomial_strictMonoOn hx.1 hy.1.1 hxy
    linarith [hroot, hy.2]

/-- The tribonacci constant, characterized without radicals. -/
noncomputable def tribonacci : ℝ := Classical.choose exists_unique_tribonacci

theorem tribonacci_mem_Icc : tribonacci ∈ Set.Icc (1 : ℝ) 2 :=
  (Classical.choose_spec exists_unique_tribonacci).1.1

theorem tribonacci_root : tribonacciPolynomial tribonacci = 0 :=
  (Classical.choose_spec exists_unique_tribonacci).1.2

theorem tribonacci_pos : 0 < tribonacci := lt_of_lt_of_le zero_lt_one tribonacci_mem_Icc.1

/-- A decimal-scale enclosure used to connect exact and rational vertex data. -/
theorem tribonacci_enclosure :
    tribonacci ∈ Set.Icc
      (1839286755214161 / 10 ^ 15 : ℝ)
      (1839286755214162 / 10 ^ 15 : ℝ) := by
  constructor
  · by_contra h
    have ht : tribonacci < (1839286755214161 / 10 ^ 15 : ℝ) := lt_of_not_ge h
    have hlo_mem : (1839286755214161 / 10 ^ 15 : ℝ) ∈ Set.Ici 1 := by norm_num
    have hmono := tribonacciPolynomial_strictMonoOn tribonacci_mem_Icc.1 hlo_mem ht
    rw [tribonacci_root] at hmono
    have hlo : tribonacciPolynomial (1839286755214161 / 10 ^ 15 : ℝ) < 0 := by
      norm_num [tribonacciPolynomial]
    linarith
  · by_contra h
    have ht : (1839286755214162 / 10 ^ 15 : ℝ) < tribonacci := lt_of_not_ge h
    have hhi_mem : (1839286755214162 / 10 ^ 15 : ℝ) ∈ Set.Ici 1 := by norm_num
    have hmono := tribonacciPolynomial_strictMonoOn hhi_mem tribonacci_mem_Icc.1 ht
    rw [tribonacci_root] at hmono
    have hhi : 0 < tribonacciPolynomial (1839286755214162 / 10 ^ 15 : ℝ) := by
      norm_num [tribonacciPolynomial]
    linarith

end Noperthedron.SnubCube

end
