module

public import Noperthedron.BalancedSupport.TranslatedPose
public import Noperthedron.PoseInterval
public import Noperthedron.SnubCube.Symmetry

@[expose] public section


/-!
# Symmetry reduction for snub-cube poses

The rotational symmetry group can move every viewing vector into the closed
positive octant.  This is the first, purely algebraic part of reducing the
five-dimensional pose domain before generating a solution tree.
-/

namespace Noperthedron.SnubCube

open Real
open scoped Matrix

private theorem symmetryMatrix_zero :
    symmetryMatrix (VertexIndex.ofFin24 0) =
      !![(1 : ℝ), 0, 0; 0, 1, 0; 0, 0, 1] := by
  rw [symmetryMatrix]
  have h : symmetryMatrixInt (VertexIndex.ofFin24 0) =
      !![(1 : ℤ), 0, 0; 0, 1, 0; 0, 0, 1] := by decide +kernel
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

private theorem symmetryMatrix_one :
    symmetryMatrix (VertexIndex.ofFin24 1) =
      !![(-1 : ℝ), 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [symmetryMatrix]
  have h : symmetryMatrixInt (VertexIndex.ofFin24 1) =
      !![(-1 : ℤ), 0, 0; 0, -1, 0; 0, 0, 1] := by decide +kernel
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

private theorem symmetryMatrix_two :
    symmetryMatrix (VertexIndex.ofFin24 2) =
      !![(-1 : ℝ), 0, 0; 0, 1, 0; 0, 0, -1] := by
  rw [symmetryMatrix]
  have h : symmetryMatrixInt (VertexIndex.ofFin24 2) =
      !![(-1 : ℤ), 0, 0; 0, 1, 0; 0, 0, -1] := by decide +kernel
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

private theorem symmetryMatrix_three :
    symmetryMatrix (VertexIndex.ofFin24 3) =
      !![(1 : ℝ), 0, 0; 0, -1, 0; 0, 0, -1] := by
  rw [symmetryMatrix]
  have h : symmetryMatrixInt (VertexIndex.ofFin24 3) =
      !![(1 : ℤ), 0, 0; 0, -1, 0; 0, 0, -1] := by decide +kernel
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

private theorem symmetryMatrix_four :
    symmetryMatrix (VertexIndex.ofFin24 4) =
      !![(-1 : ℝ), 0, 0; 0, 0, 1; 0, 1, 0] := by
  rw [symmetryMatrix]
  have h : symmetryMatrixInt (VertexIndex.ofFin24 4) =
      !![(-1 : ℤ), 0, 0; 0, 0, 1; 0, 1, 0] := by decide +kernel
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

private theorem symmetryMatrix_five :
    symmetryMatrix (VertexIndex.ofFin24 5) =
      !![(1 : ℝ), 0, 0; 0, 0, -1; 0, 1, 0] := by
  rw [symmetryMatrix]
  have h : symmetryMatrixInt (VertexIndex.ofFin24 5) =
      !![(1 : ℤ), 0, 0; 0, 0, -1; 0, 1, 0] := by decide +kernel
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

private theorem symmetryMatrixInt_six :
    symmetryMatrixInt (VertexIndex.ofFin24 6) =
      !![(1 : ℤ), 0, 0; 0, 0, 1; 0, -1, 0] := by
  decide +kernel

private theorem symmetryMatrix_six :
    symmetryMatrix (VertexIndex.ofFin24 6) =
      !![(1 : ℝ), 0, 0; 0, 0, 1; 0, -1, 0] := by
  rw [symmetryMatrix, symmetryMatrixInt_six]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

private theorem symmetryMatrix_seven :
    symmetryMatrix (VertexIndex.ofFin24 7) =
      !![(-1 : ℝ), 0, 0; 0, 0, -1; 0, -1, 0] := by
  rw [symmetryMatrix]
  have h : symmetryMatrixInt (VertexIndex.ofFin24 7) =
      !![(-1 : ℤ), 0, 0; 0, 0, -1; 0, -1, 0] := by decide +kernel
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- One of the 24 exact rotational symmetries moves any row vector into the
closed positive octant. -/
theorem exists_symmetry_vecMul_nonneg (v : Fin 3 → ℝ) :
    ∃ g : VertexIndex,
      0 ≤ (v ᵥ* symmetryMatrix g) 0 ∧
      0 ≤ (v ᵥ* symmetryMatrix g) 1 ∧
      0 ≤ (v ᵥ* symmetryMatrix g) 2 := by
  by_cases hx : 0 ≤ v 0
  · by_cases hy : 0 ≤ v 1
    · by_cases hz : 0 ≤ v 2
      · exact ⟨VertexIndex.ofFin24 0, by
          rw [symmetryMatrix_zero]
          simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using
            And.intro hx (And.intro hy hz)⟩
      · exact ⟨VertexIndex.ofFin24 6, by
          rw [symmetryMatrix_six]
          simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using
            And.intro hx (And.intro (neg_nonneg.mpr (le_of_not_ge hz)) hy)⟩
    · by_cases hz : 0 ≤ v 2
      · exact ⟨VertexIndex.ofFin24 5, by
          rw [symmetryMatrix_five]
          simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using
            And.intro hx (And.intro hz (neg_nonneg.mpr (le_of_not_ge hy)))⟩
      · exact ⟨VertexIndex.ofFin24 3, by
          rw [symmetryMatrix_three]
          simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using
            And.intro hx (And.intro (neg_nonneg.mpr (le_of_not_ge hy))
              (neg_nonneg.mpr (le_of_not_ge hz)))⟩
  · by_cases hy : 0 ≤ v 1
    · by_cases hz : 0 ≤ v 2
      · exact ⟨VertexIndex.ofFin24 4, by
          rw [symmetryMatrix_four]
          simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using
            And.intro (neg_nonneg.mpr (le_of_not_ge hx)) (And.intro hz hy)⟩
      · exact ⟨VertexIndex.ofFin24 2, by
          rw [symmetryMatrix_two]
          simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using
            And.intro (neg_nonneg.mpr (le_of_not_ge hx))
              (And.intro hy (neg_nonneg.mpr (le_of_not_ge hz)))⟩
    · by_cases hz : 0 ≤ v 2
      · exact ⟨VertexIndex.ofFin24 1, by
          rw [symmetryMatrix_one]
          simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using
            And.intro (neg_nonneg.mpr (le_of_not_ge hx))
              (And.intro (neg_nonneg.mpr (le_of_not_ge hy)) hz)⟩
      · exact ⟨VertexIndex.ofFin24 7, by
          rw [symmetryMatrix_seven]
          simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using
            And.intro (neg_nonneg.mpr (le_of_not_ge hx))
              (And.intro (neg_nonneg.mpr (le_of_not_ge hz))
                (neg_nonneg.mpr (le_of_not_ge hy)))⟩

/-- The checked vertex action of every symmetry is a permutation. -/
theorem symmetryAction_surjective (g : VertexIndex) :
    Function.Surjective (symmetryAction g) := by
  obtain ⟨p, s⟩ := g
  fin_cases p <;> fin_cases s <;> decide +kernel

/-- Every exact snub-cube symmetry carries the normalized hull onto itself. -/
theorem symmetry_image_normalizedHull (g : VertexIndex) :
    (symmetry g).val.toEuclideanLin '' normalizedExactPolyhedron.hull =
      normalizedExactPolyhedron.hull := by
  unfold Polyhedron.hull normalizedExactPolyhedron
  rw [LinearMap.image_convexHull]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨symmetryAction g i, (symmetry_apply_normalizedExactVertex g i).symm⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := symmetryAction_surjective g i
    exact ⟨normalizedExactVertex j, ⟨j, rfl⟩,
      symmetry_apply_normalizedExactVertex g j⟩

/-- Compose the inner and outer rotations on the right by independently
chosen snub-cube symmetries.  The offset is unchanged. -/
noncomputable def _root_.MatrixPose.rightSnubSymmetries
    (p : MatrixPose) (innerSymmetry outerSymmetry : VertexIndex) : MatrixPose where
  innerRot := p.innerRot * symmetry innerSymmetry
  outerRot := p.outerRot * symmetry outerSymmetry
  innerOffset := p.innerOffset

theorem innerShadow_rightSnubSymmetries
    (p : MatrixPose) (gi go : VertexIndex) :
    innerShadow (p.rightSnubSymmetries gi go) normalizedExactPolyhedron.hull =
      innerShadow p normalizedExactPolyhedron.hull := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hgv : (symmetry gi).val.toEuclideanLin v ∈
        normalizedExactPolyhedron.hull := by
      rw [← symmetry_image_normalizedHull gi]
      exact ⟨v, hv, rfl⟩
    refine ⟨(symmetry gi).val.toEuclideanLin v, hgv, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.rightSnubSymmetries,
      Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (symmetry gi).val.toEuclideanLin ''
        normalizedExactPolyhedron.hull := by
      rwa [symmetry_image_normalizedHull gi]
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨u, hu, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.rightSnubSymmetries,
      Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

theorem outerShadow_rightSnubSymmetries
    (p : MatrixPose) (gi go : VertexIndex) :
    outerShadow (p.rightSnubSymmetries gi go) normalizedExactPolyhedron.hull =
      outerShadow p normalizedExactPolyhedron.hull := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hgv : (symmetry go).val.toEuclideanLin v ∈
        normalizedExactPolyhedron.hull := by
      rw [← symmetry_image_normalizedHull go]
      exact ⟨v, hv, rfl⟩
    refine ⟨(symmetry go).val.toEuclideanLin v, hgv, ?_⟩
    simp [PoseLike.outer, MatrixPose.rightSnubSymmetries,
      Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (symmetry go).val.toEuclideanLin ''
        normalizedExactPolyhedron.hull := by
      rwa [symmetry_image_normalizedHull go]
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨u, hu, ?_⟩
    simp [PoseLike.outer, MatrixPose.rightSnubSymmetries,
      Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- Independent right composition by exact snub-cube rotations preserves the
Rupert predicate, including arbitrary planar translation. -/
theorem RupertPose_rightSnubSymmetries_iff
    (p : MatrixPose) (gi go : VertexIndex) :
    RupertPose (p.rightSnubSymmetries gi go) normalizedExactPolyhedron.hull ↔
      RupertPose p normalizedExactPolyhedron.hull := by
  simp only [RupertPose, innerShadow_rightSnubSymmetries,
    outerShadow_rightSnubSymmetries]

/-- Spherical coordinates in the closed positive octant can be chosen with
both angles in `[0, π/2]`. -/
theorem exists_positive_spherical_coords (v : ℝ³) (hv : ‖v‖ = 1)
    (h0 : 0 ≤ v 0) (h1 : 0 ≤ v 1) (h2 : 0 ≤ v 2) :
    ∃ θ φ : ℝ, θ ∈ Set.Icc 0 (π / 2) ∧ φ ∈ Set.Icc 0 (π / 2) ∧
      v = ![Real.sin φ * Real.cos θ, Real.sin φ * Real.sin θ, Real.cos φ] := by
  let θ := Complex.arg (v 0 + v 1 * Complex.I)
  let φ := Real.arccos (v 2)
  refine ⟨θ, φ, ?_, ?_, ?_⟩
  · exact ⟨Complex.arg_nonneg_iff.mpr (by simpa [θ] using h1),
      Complex.arg_le_pi_div_two_iff.mpr (Or.inl (by simpa [θ] using h0))⟩
  · exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr h2⟩
  · have hv' := hv
    simp only [EuclideanSpace.norm_eq, norm_eq_abs, sq_abs,
      Fin.sum_univ_three, sqrt_eq_one, Nat.succ_eq_add_one,
      Nat.reduceAdd] at hv' ⊢
    have h_cos_sin : Real.cos φ = v 2 ∧
        Real.sin φ = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) := by
      dsimp only [φ]
      rw [Real.cos_arccos, Real.sin_arccos] <;>
        try linarith [sq_nonneg (1 + v 2), sq_nonneg (1 - v 2),
          sq_nonneg (v 0), sq_nonneg (v 1)]
      exact ⟨rfl, congrArg Real.sqrt <| sub_eq_iff_eq_add.mpr hv'.symm⟩
    by_cases h : v 0 + v 1 * Complex.I = 0
    · simp_all
      simp_all [Complex.ext_iff]
      ext i
      fin_cases i <;> tauto
    · have hpos : 0 < v 0 ^ 2 + v 1 ^ 2 := by
        rw [← Complex.normSq_add_mul_I]
        exact Complex.normSq_pos.mpr h
      dsimp only [θ]
      simp_all [Complex.cos_arg, Complex.sin_arg]
      simp [Complex.normSq, Complex.norm_def] at *
      simp [← sq, mul_div_cancel₀ _ (ne_of_gt <| Real.sqrt_pos.mpr hpos)]
      ext i
      fin_cases i <;> rfl

private def matrixThirdRow (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ³ :=
  WithLp.toLp 2 (fun j => M 2 j)

private theorem matrixThirdRow_norm (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ‖matrixThirdRow M‖ = 1 := by
  have hparts := (Matrix.mem_specialOrthogonalGroup_iff).mp hM
  have horth : M * Mᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hparts.1
  have h22 := congrFun (congrFun horth (2 : Fin 3)) (2 : Fin 3)
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h22
  have hs : M 2 0 ^ 2 + M 2 1 ^ 2 + M 2 2 ^ 2 = 1 := by
    nlinarith [h22]
  rw [EuclideanSpace.norm_eq]
  simp [matrixThirdRow, Fin.sum_univ_three, sq_abs, hs]

/-- An SO(3) matrix whose third row is in the positive octant has `rotRM`
coordinates with both viewing angles in `[0, π/2]`; the in-plane angle is
chosen in `(-π, π]`. -/
theorem SO3_to_positive_rotRM_params
    (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (h0 : 0 ≤ M 2 0) (h1 : 0 ≤ M 2 1) (h2 : 0 ≤ M 2 2) :
    ∃ θ φ α : ℝ,
      θ ∈ Set.Icc 0 (π / 2) ∧ φ ∈ Set.Icc 0 (π / 2) ∧
      α ∈ Set.Ioc (-π) π ∧ M = rotRM_mat θ φ α := by
  obtain ⟨θ, φ, hθ, hφ, hrow⟩ := exists_positive_spherical_coords
    (matrixThirdRow M) (matrixThirdRow_norm M hM) h0 h1 h2
  let B := rotRM_mat θ φ 0
  have hB : B ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    rotRM_mat_mem_SO3 θ φ 0
  have hBrow (j : Fin 3) : B 2 j = M 2 j := by
    have hj := congrFun hrow j
    fin_cases j <;>
      simpa [matrixThirdRow, B, rotRM_mat, Matrix.mul_apply,
        Fin.sum_univ_three] using hj.symm
  have hBt : Bᵀ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    have hBparts := (Matrix.mem_specialOrthogonalGroup_iff).mp hB
    rw [Matrix.mem_specialOrthogonalGroup_iff,
      Matrix.mem_orthogonalGroup_iff]
    constructor
    · simpa only [Matrix.transpose_transpose] using
        (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hBparts.1
    · simpa only [Matrix.det_transpose] using hBparts.2
  let A := M * Bᵀ
  have hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ hM hBt
  let ez : Fin 3 → ℝ := fun i => if i = 2 then 1 else 0
  have htranspose_ez : Bᵀ *ᵥ ez = Mᵀ *ᵥ ez := by
    ext j
    simpa [ez, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hBrow j
  have hAfix : A.toEuclideanLin !₂[0, 0, 1] = !₂[0, 0, 1] := by
    ext j
    change (A *ᵥ (![0, 0, 1] : Fin 3 → ℝ)) j =
      (![0, 0, 1] : Fin 3 → ℝ) j
    have hez : (![0, 0, 1] : Fin 3 → ℝ) = ez := by
      funext i
      fin_cases i <;> simp [ez]
    rw [hez]
    rw [show A *ᵥ ez = M *ᵥ (Bᵀ *ᵥ ez) by
      simp only [A, Matrix.mulVec_mulVec]]
    rw [htranspose_ez, Matrix.mulVec_mulVec]
    have hMparts := (Matrix.mem_specialOrthogonalGroup_iff).mp hM
    rw [(Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hMparts.1,
      Matrix.one_mulVec]
  obtain ⟨α, hα⟩ := Bounding.SO3_fixing_z_is_Rz A hA hAfix
  have hBparts := (Matrix.mem_specialOrthogonalGroup_iff).mp hB
  have hBtB : Bᵀ * B = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hBparts.1
  have hrecover : A * B = M := by
    simp only [A, Matrix.mul_assoc, hBtB, Matrix.mul_one]
  have hform : M = rotRM_mat θ φ α := by
    rw [← hrecover, hα]
    simp only [B, rotRM_mat, Bounding.Rz_mat_zero, Matrix.mul_one,
      ← Matrix.mul_assoc, Bounding.Rz_mat_mul_Rz_mat]
    congr 3
    ring
  obtain ⟨α', hα'mem, hα'⟩ := Bounding.Rz_mod_two_pi α
  refine ⟨θ, φ, α', hθ, hφ, hα'mem, hform.trans ?_⟩
  simp only [rotRM_mat]
  rw [hα']

/-- Every unit vector has spherical coordinates in the standard bounded
domain.  Unlike `exists_positive_spherical_coords`, this does not assume an
octant, so the azimuth may be negative and the polar angle may exceed `π/2`.
-/
theorem exists_bounded_spherical_coords (v : ℝ³) (hv : ‖v‖ = 1) :
    ∃ θ φ : ℝ, θ ∈ Set.Ioc (-π) π ∧ φ ∈ Set.Icc 0 π ∧
      v = ![Real.sin φ * Real.cos θ, Real.sin φ * Real.sin θ, Real.cos φ] := by
  let θ := Complex.arg (v 0 + v 1 * Complex.I)
  let φ := Real.arccos (v 2)
  refine ⟨θ, φ, ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩,
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩, ?_⟩
  have hv' := hv
  simp only [EuclideanSpace.norm_eq, norm_eq_abs, sq_abs,
    Fin.sum_univ_three, sqrt_eq_one, Nat.succ_eq_add_one,
    Nat.reduceAdd] at hv' ⊢
  have h_cos_sin : Real.cos φ = v 2 ∧
      Real.sin φ = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) := by
    dsimp only [φ]
    rw [Real.cos_arccos, Real.sin_arccos] <;>
      try linarith [sq_nonneg (1 + v 2), sq_nonneg (1 - v 2),
        sq_nonneg (v 0), sq_nonneg (v 1)]
    exact ⟨rfl, congrArg Real.sqrt <| sub_eq_iff_eq_add.mpr hv'.symm⟩
  by_cases h : v 0 + v 1 * Complex.I = 0
  · simp_all
    simp_all [Complex.ext_iff]
    ext i
    fin_cases i <;> tauto
  · have hpos : 0 < v 0 ^ 2 + v 1 ^ 2 := by
      rw [← Complex.normSq_add_mul_I]
      exact Complex.normSq_pos.mpr h
    dsimp only [θ]
    simp_all [Complex.cos_arg, Complex.sin_arg]
    simp [Complex.normSq, Complex.norm_def] at *
    simp [← sq, mul_div_cancel₀ _ (ne_of_gt <| Real.sqrt_pos.mpr hpos)]
    ext i
    fin_cases i <;> rfl

/-- Every SO(3) matrix has `rotRM` coordinates in the standard bounded Euler
domain.  This complements the smaller positive-octant theorem above and is
used when a separately chosen symmetry must be preserved. -/
theorem SO3_to_bounded_rotRM_params
    (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ θ φ α : ℝ,
      θ ∈ Set.Ioc (-π) π ∧ φ ∈ Set.Icc 0 π ∧
      α ∈ Set.Ioc (-π) π ∧ M = rotRM_mat θ φ α := by
  obtain ⟨θ, φ, hθ, hφ, hrow⟩ := exists_bounded_spherical_coords
    (matrixThirdRow M) (matrixThirdRow_norm M hM)
  let B := rotRM_mat θ φ 0
  have hB : B ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    rotRM_mat_mem_SO3 θ φ 0
  have hBrow (j : Fin 3) : B 2 j = M 2 j := by
    have hj := congrFun hrow j
    fin_cases j <;>
      simpa [matrixThirdRow, B, rotRM_mat, Matrix.mul_apply,
        Fin.sum_univ_three] using hj.symm
  have hBt : Bᵀ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    have hBparts := (Matrix.mem_specialOrthogonalGroup_iff).mp hB
    rw [Matrix.mem_specialOrthogonalGroup_iff,
      Matrix.mem_orthogonalGroup_iff]
    constructor
    · simpa only [Matrix.transpose_transpose] using
        (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hBparts.1
    · simpa only [Matrix.det_transpose] using hBparts.2
  let A := M * Bᵀ
  have hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ hM hBt
  let ez : Fin 3 → ℝ := fun i => if i = 2 then 1 else 0
  have htranspose_ez : Bᵀ *ᵥ ez = Mᵀ *ᵥ ez := by
    ext j
    simpa [ez, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hBrow j
  have hAfix : A.toEuclideanLin !₂[0, 0, 1] = !₂[0, 0, 1] := by
    ext j
    change (A *ᵥ (![0, 0, 1] : Fin 3 → ℝ)) j =
      (![0, 0, 1] : Fin 3 → ℝ) j
    have hez : (![0, 0, 1] : Fin 3 → ℝ) = ez := by
      funext i
      fin_cases i <;> simp [ez]
    rw [hez]
    rw [show A *ᵥ ez = M *ᵥ (Bᵀ *ᵥ ez) by
      simp only [A, Matrix.mulVec_mulVec]]
    rw [htranspose_ez, Matrix.mulVec_mulVec]
    have hMparts := (Matrix.mem_specialOrthogonalGroup_iff).mp hM
    rw [(Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hMparts.1,
      Matrix.one_mulVec]
  obtain ⟨α, hα⟩ := Bounding.SO3_fixing_z_is_Rz A hA hAfix
  have hBparts := (Matrix.mem_specialOrthogonalGroup_iff).mp hB
  have hBtB : Bᵀ * B = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hBparts.1
  have hrecover : A * B = M := by
    simp only [A, Matrix.mul_assoc, hBtB, Matrix.mul_one]
  have hform : M = rotRM_mat θ φ α := by
    rw [← hrecover, hα]
    simp only [B, rotRM_mat, Bounding.Rz_mat_zero, Matrix.mul_one,
      ← Matrix.mul_assoc, Bounding.Rz_mat_mul_Rz_mat]
    congr 3
    ring
  obtain ⟨α', hα'mem, hα'⟩ := Bounding.Rz_mod_two_pi α
  refine ⟨θ, φ, α', hθ, hφ, hα'mem, hform.trans ?_⟩
  simp only [rotRM_mat]
  rw [hα']

/-- Right composition by one exact snub-cube symmetry puts an arbitrary
rotation into positive-octant `rotRM` coordinates. -/
theorem SO3_to_symmetry_reduced_rotRM_params (M : SO3) :
    ∃ g : VertexIndex, ∃ θ φ α : ℝ,
      θ ∈ Set.Icc 0 (π / 2) ∧ φ ∈ Set.Icc 0 (π / 2) ∧
      α ∈ Set.Ioc (-π) π ∧
      M.val * symmetryMatrix g = rotRM_mat θ φ α := by
  obtain ⟨g, hg0, hg1, hg2⟩ :=
    exists_symmetry_vecMul_nonneg (fun j => M.val 2 j)
  have hM : M.val * symmetryMatrix g ∈
      Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ M.property (symmetryMatrix_mem_SO3 g)
  have hrow (j : Fin 3) :
      (M.val * symmetryMatrix g) 2 j =
        ((fun k => M.val 2 k) ᵥ* symmetryMatrix g) j := by
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  obtain ⟨θ, φ, α, hθ, hφ, hα, hform⟩ :=
    SO3_to_positive_rotRM_params (M.val * symmetryMatrix g) hM
      (by simpa [hrow] using hg0) (by simpa [hrow] using hg1)
      (by simpa [hrow] using hg2)
  exact ⟨g, θ, φ, α, hθ, hφ, hα, hform⟩

private theorem Rz_mul_rotRM_mat (δ θ φ α : ℝ) :
    Rz_mat δ * rotRM_mat θ φ α = rotRM_mat θ φ (δ + α) := by
  simp only [rotRM_mat, ← Matrix.mul_assoc,
    Bounding.Rz_mat_mul_Rz_mat]
  congr 3
  ring

/-- Rational rectangular superset of the symmetry-reduced Euler domain. -/
def reducedPoseInterval : PoseInterval ℝ :=
  PoseInterval.mk
    { θ₁ := 0, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := -4 }
    { θ₁ := 2, θ₂ := 2, φ₁ := 2, φ₂ := 2, α := 4 }
    (by rw [Pose.le_iff]; norm_num)

/-- Every full matrix pose is Rupert-equivalent, after exact snub-cube
symmetries and a common screen rotation, to a translated Euler pose in the
small rational root box. -/
theorem exists_reduced_translated_pose (p : MatrixPose) :
    ∃ gi go : VertexIndex, ∃ δ : ℝ, ∃ q : Pose ℝ, ∃ offset : ℝ²,
      q ∈ reducedPoseInterval ∧
      q.matrixPoseWithOffset offset =
        (p.rightSnubSymmetries gi go).rotateBy δ := by
  obtain ⟨gi, θi, φi, αi, hθi, hφi, _hαi, hinner⟩ :=
    SO3_to_symmetry_reduced_rotRM_params p.innerRot
  obtain ⟨go, θo, φo, αo, hθo, hφo, _hαo, houter⟩ :=
    SO3_to_symmetry_reduced_rotRM_params p.outerRot
  let δ := -αo
  obtain ⟨α, hα, hRzα⟩ := Bounding.Rz_mod_two_pi (δ + αi)
  let q : Pose ℝ := {
    θ₁ := θi, θ₂ := θo, φ₁ := φi, φ₂ := φo, α := α
  }
  let offset := rotR δ p.innerOffset
  have hq : q ∈ reducedPoseInterval := by
    rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff]
    dsimp [q, reducedPoseInterval]
    have hpi2 : π / 2 ≤ 2 := by linarith [Real.pi_le_four]
    have hpi4 := Real.pi_le_four
    exact ⟨
      ⟨hθi.1, hθo.1, hφi.1, hφo.1, by linarith [hα.1]⟩,
      ⟨hθi.2.trans hpi2, hθo.2.trans hpi2,
        hφi.2.trans hpi2, hφo.2.trans hpi2,
        by linarith [hα.2]⟩⟩
  refine ⟨gi, go, δ, q, offset, hq, ?_⟩
  have hin : Rz_mat δ * (p.innerRot.val * symmetryMatrix gi) =
      rotRM_mat θi φi α := by
    rw [hinner, Rz_mul_rotRM_mat]
    unfold rotRM_mat
    rw [hRzα]
  have hout : Rz_mat δ * (p.outerRot.val * symmetryMatrix go) =
      rotRM_mat θo φo 0 := by
    rw [houter, Rz_mul_rotRM_mat]
    congr 1
    dsimp [δ]
    ring
  simp only [Pose.matrixPoseWithOffset, Pose.matrixPoseOfPose,
    MatrixPose.rotateBy, MatrixPose.rightSnubSymmetries]
  congr 1
  · apply Subtype.ext
    exact hin.symm
  · apply Subtype.ext
    exact hout.symm

/-- It is enough for the finite tree to exclude translated Euler poses in
`reducedPoseInterval`; symmetry reduction and screen rotation cover every
full matrix pose. -/
theorem no_matrixPose_of_no_reduced_translated_pose
    (h : ¬ ∃ q ∈ reducedPoseInterval, ∃ offset : ℝ²,
      RupertPose (q.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull) :
    ¬ ∃ p : MatrixPose,
      RupertPose p normalizedExactPolyhedron.hull := by
  rintro ⟨p, hp⟩
  obtain ⟨gi, go, δ, q, offset, hq, heq⟩ :=
    exists_reduced_translated_pose p
  have hsym : RupertPose (p.rightSnubSymmetries gi go)
      normalizedExactPolyhedron.hull :=
    (RupertPose_rightSnubSymmetries_iff p gi go).mpr hp
  have hrot : RupertPose ((p.rightSnubSymmetries gi go).rotateBy δ)
      normalizedExactPolyhedron.hull :=
    (MatrixPose.RupertPose_rotateBy_iff
      (p.rightSnubSymmetries gi go) δ normalizedExactPolyhedron.hull).mpr hsym
  exact h ⟨q, hq, offset, heq.symm ▸ hrot⟩

end Noperthedron.SnubCube

end
