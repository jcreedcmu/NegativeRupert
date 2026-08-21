module

public import Noperthedron.Checker.KappaApprox
public import Noperthedron.SolutionTable.Basic
public import Noperthedron.SolutionTable.Global
public import Noperthedron.Local.Congruent
public import Noperthedron.RationalApprox.RationalLocal
public import Noperthedron.Vertices.Exact
public import Noperthedron.Vertices.Symmetry

public section


namespace Noperthedron.Solution

open scoped RealInnerProductSpace Real
open scoped Matrix

/-- The transported triangle for `exact_κApprox_python` is just `pythonVertex ∘ Pi`. -/
private lemma transportTri_python (Pi : Fin 3 → VertexIndex) :
    (KappaApprox.exact_κApprox_python.transportTri Pi : Local.TriangleQ) =
      pythonVertex ∘ Pi := rfl

/-- Bridge from a rational κ-spanning hypothesis on `(θ, φ)` to real `κSpanning`
for the Python polyhedron. Used for both `P_spanning` (with `(θ₁, φ₁)`) and
`Q_spanning` (with `(θ₂, φ₂)`). -/
private lemma py_κSpanning_of_rational
    (idx : Fin 3 → VertexIndex) (θ φ ε : ℚ) (hε : 0 < ε)
    (h : Spanningℚ θ φ ε (pythonVertexA ∘ idx)) :
    (KappaApprox.exact_κApprox_python.transportTri idx).toReal.κSpanning
      (θ : ℝ) (φ : ℝ) ε := by
  refine ⟨mod_cast hε, fun i => ?_⟩
  have hi := h i
  simp only [Function.comp_apply, pythonVertexA_eq] at hi
  have hcast : ((2 * ε * (sqrt_twoℚ + ε) + 6 * RationalApprox.κℚ : ℚ) : ℝ) <
      ⟪rotR (π / 2) (RationalApprox.rotMℚℝ (θ : ℝ) (φ : ℝ) (toR3 (pythonVertex (idx i)))),
        RationalApprox.rotMℚℝ (θ : ℝ) (φ : ℝ) (toR3 (pythonVertex (idx (i + 1))))⟫ := by
    rw [← RationalApprox.rot90_rotMℚ_inner_eq_real_inner]
    exact_mod_cast hi
  have hε_real : (0 : ℝ) ≤ (ε : ℝ) := mod_cast hε.le
  have hsqrt2 : (√2 : ℝ) ≤ (142 / 100 : ℝ) :=
    ((Real.sqrt_lt' (by norm_num)).mpr (by norm_num)).le
  have hcastκ : (RationalApprox.κℚ : ℝ) = RationalApprox.κ := by
    simp [RationalApprox.κℚ, RationalApprox.κ]
  have hbound :
      2 * (ε : ℝ) * (Real.sqrt 2 + ε) + 6 * RationalApprox.κ ≤
        ((2 * ε * (sqrt_twoℚ + ε) + 6 * RationalApprox.κℚ : ℚ) : ℝ) := by
    push_cast [hcastκ]
    nlinarith [hε_real, hsqrt2]
  exact lt_of_le_of_lt hbound hcast

theorem valid_local_imp_no_rupert (row : Row) (hrow : row.ValidLocal) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  let ε := row.epsilon
  obtain ⟨s, hs₁, hs₂⟩ := hrow.exists_symmetry
  have hε : 0 < ε := hrow.epsilon_pos
  have pc : RationalApprox.LocalTheorem.RationalLocalTheoremPrecondition
      exactPoly pythonPolyQ KappaApprox.exact_κApprox_python
      row.interval.centerPose ε := {
    Pi := row.Pi
    Qi := row.Qi
    cong_tri := Noperthedron.TriangleSymmetry.congruent_of_apply s row.Pi row.Qi hs₁ hs₂
    hp := hrow.center_in_fourQ
    δ := row.δ
    r := row.r
    hr := hrow.rpos
    approx := RationalApprox.sqrtApprox16
    hr₁ := by have h := hrow.r_valid; rwa [pythonVertexA_eq] at h
    hδ := by
      intro i
      -- row.δ rewrites to Finset.max' over BoundDeltaℚi via Row.δ_eq_max'_BoundDeltaℚi.
      have hi_mem : RationalApprox.LocalTheorem.BoundDeltaℚi
          row.interval.centerPose (pythonVertex ∘ row.Pi) (pythonVertex ∘ row.Qi)
          RationalApprox.sqrtApprox16 i ∈
          Finset.image (RationalApprox.LocalTheorem.BoundDeltaℚi
            row.interval.centerPose (pythonVertex ∘ row.Pi) (pythonVertex ∘ row.Qi)
            RationalApprox.sqrtApprox16) Finset.univ :=
        Finset.mem_image_of_mem _ (Finset.mem_univ i)
      have hle := Finset.le_max' _ _ hi_mem
      show row.δ ≥ RationalApprox.LocalTheorem.BoundDeltaℚi row.interval.centerPose
        (KappaApprox.exact_κApprox_python.transportTri row.Pi)
        (KappaApprox.exact_κApprox_python.transportTri row.Qi) RationalApprox.sqrtApprox16 i
      rw [transportTri_python row.Pi, transportTri_python row.Qi,
          Row.δ_eq_max'_BoundDeltaℚi]
      exact hle
    ae₁ := ⟨0, by have h := hrow.X₁_inner_gt; rwa [pythonVertexA_eq] at h⟩
    ae₂ := ⟨row.sigma_Q.val, by have h := hrow.X₂_inner_gt; rwa [pythonVertexA_eq] at h⟩
    span₁ := py_κSpanning_of_rational row.Pi
      row.interval.centerPose.θ₁ row.interval.centerPose.φ₁ ε hε hrow.P_spanning
    span₂ := py_κSpanning_of_rational row.Qi
      row.interval.centerPose.θ₂ row.interval.centerPose.φ₂ ε hε hrow.Q_spanning
    be := by have h := hrow.Bεℚ; rwa [pythonVertexA_eq] at h
  }
  exact no_rupert_in_interval_of_ball row
    (RationalApprox.LocalTheorem.rational_local exactPoly pythonPolyQ
      KappaApprox.exact_κApprox_python row.interval.centerPose ε pc)

theorem valid_local₂_imp_no_rupert (row : Row) (hrow : row.ValidLocal₂) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  obtain ⟨s, hs₁, hs₂⟩ := hrow.exists_symmetry
  have pc : RationalApprox.LocalTheorem.RationalLocalTheoremPrecondition₂
      exactPoly pythonPolyQ KappaApprox.exact_κApprox_python
      row.interval.centerPose row.εα row.εθ₁ row.εφ₁ row.εθ₂ row.εφ₂ := {
    Pi := row.Pi
    Qi := row.Qi
    cong_tri := Noperthedron.TriangleSymmetry.congruent_of_apply s row.Pi row.Qi hs₁ hs₂
    hp := hrow.center_in_fourQ
    hεα := row.εα_nonneg
    hεθ₁ := row.εθ₁_nonneg
    hεφ₁ := row.εφ₁_nonneg
    hεθ₂ := row.εθ₂_nonneg
    hεφ₂ := row.εφ₂_nonneg
    δ := row.δ₂
    r := row.r
    hr := hrow.rpos
    approx := RationalApprox.sqrtApprox16
    hr₁ := by have h := hrow.r_valid; rwa [pythonVertexA_eq] at h
    hδ := by
      have h := row.boundDelta₂_δ₂
      rwa [pythonVertexA_eq] at h
    ae₁ := ⟨0, by have h := hrow.X₁_inner_gt; rwa [pythonVertexA_eq] at h⟩
    ae₂ := ⟨row.sigma_Q.val, by have h := hrow.X₂_inner_gt; rwa [pythonVertexA_eq] at h⟩
    span₁ := by have h := hrow.P_spanning; rwa [pythonVertexA_eq] at h
    span₂ := by have h := hrow.Q_spanning; rwa [pythonVertexA_eq] at h
    be := by have h := hrow.Bε₂ℚ; rwa [pythonVertexA_eq] at h
  }
  have h := RationalApprox.LocalTheorem.rational_local₂ exactPoly pythonPolyQ
    KappaApprox.exact_κApprox_python row.interval.centerPose
    row.εα row.εθ₁ row.εφ₁ row.εθ₂ row.εφ₂ pc
  rintro ⟨q, hqi, hqr⟩
  exact h ⟨q, near_center_of_mem_toReal row hqi, hqr⟩

end Noperthedron.Solution
end
