module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Noperthedron.Basic

public section


open scoped Matrix

/-!
## Derivatives of rotation matrices rotR, rotM, rotMθ, rotMφ w.r.t. angles

These are needed for computing first and second partial derivatives of rotproj functions.
Each rotation map is `(M t).toEuclideanLin.toContinuousLinearMap S` for a matrix path `M`,
so its derivative is obtained by differentiating the matrix entries
(`hasDerivAt_toEuclideanLin_apply`); the `*_mat` definitions stay the single source of
truth for the formulas.
-/

/-- Transport `HasDerivAt` through application of a matrix path to a fixed vector:
if every entry of `M` has the corresponding entry of `M' t` as derivative at `t`, then
`fun s => (M s).toEuclideanLin.toContinuousLinearMap S` has derivative
`(M' t).toEuclideanLin.toContinuousLinearMap S` at `t`. -/
lemma hasDerivAt_toEuclideanLin_apply {m n : ℕ} {M M' : ℝ → Matrix (Fin m) (Fin n) ℝ} {t : ℝ}
    (h : ∀ i j, HasDerivAt (fun s => M s i j) (M' t i j) t) (S : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s => (M s).toEuclideanLin.toContinuousLinearMap S)
      ((M' t).toEuclideanLin.toContinuousLinearMap S) t := by
  have hpi : HasDerivAt (fun s => (M s) *ᵥ S.ofLp) ((M' t) *ᵥ S.ofLp) t := by
    rw [hasDerivAt_pi]
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (h i j).mul_const (S.ofLp j)
  let lpmap : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toContinuousLinearMap
  simpa [lpmap, Matrix.toLpLin_apply, LinearMap.coe_toContinuousLinearMap'] using
    HasDerivAt.clm_apply (hasDerivAt_const t lpmap) hpi

theorem HasDerivAt_rotR (α : ℝ) (v : ℝ²) :
    HasDerivAt (rotR · v) (rotR' α v) α := by
  refine hasDerivAt_toEuclideanLin_apply (M := rotR_mat) (M' := rotR'_mat) (fun i j => ?_) v
  fin_cases i <;> fin_cases j <;>
    simp only [rotR_mat, rotR'_mat, Fin.zero_eta, Fin.isValue, Fin.mk_one]
  · exact Real.hasDerivAt_cos α
  · exact (Real.hasDerivAt_sin α).neg
  · exact Real.hasDerivAt_sin α
  · exact Real.hasDerivAt_cos α

/-- Derivative of rotM w.r.t. θ gives rotMθ -/
lemma hasDerivAt_rotM_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotM θ' φ S) (rotMθ θ φ S) θ := by
  refine hasDerivAt_toEuclideanLin_apply (M := (rotM_mat · φ)) (M' := (rotMθ_mat · φ)) (fun i j => ?_) S
  fin_cases i <;> fin_cases j <;>
    simp only [rotM_mat, rotMθ_mat, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · exact (Real.hasDerivAt_sin θ).neg
  · exact Real.hasDerivAt_cos θ
  · exact hasDerivAt_const _ _
  · simpa using (Real.hasDerivAt_cos θ).neg.mul_const (Real.cos φ)
  · simpa using (Real.hasDerivAt_sin θ).neg.mul_const (Real.cos φ)
  · exact hasDerivAt_const _ _

/-- Derivative of rotM w.r.t. φ gives rotMφ -/
lemma hasDerivAt_rotM_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotM θ φ' S) (rotMφ θ φ S) φ := by
  refine hasDerivAt_toEuclideanLin_apply (M := (rotM_mat θ ·)) (M' := (rotMφ_mat θ ·)) (fun i j => ?_) S
  fin_cases i <;> fin_cases j <;>
    simp only [rotM_mat, rotMφ_mat, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · simpa using (Real.hasDerivAt_cos φ).const_mul (-Real.cos θ)
  · simpa using (Real.hasDerivAt_cos φ).const_mul (-Real.sin θ)
  · exact Real.hasDerivAt_sin φ

/-- Derivative of rotMθ w.r.t. θ gives rotMθθ -/
lemma hasDerivAt_rotMθ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMθ θ' φ S) (rotMθθ θ φ S) θ := by
  refine hasDerivAt_toEuclideanLin_apply (M := (rotMθ_mat · φ)) (M' := (rotMθθ_mat · φ)) (fun i j => ?_) S
  fin_cases i <;> fin_cases j <;>
    simp only [rotMθ_mat, rotMθθ_mat, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · have h := (Real.hasDerivAt_cos θ).neg
    rw [neg_neg] at h
    exact h
  · exact (Real.hasDerivAt_sin θ).neg
  · exact hasDerivAt_const _ _
  · simpa using (Real.hasDerivAt_sin θ).mul_const (Real.cos φ)
  · simpa using (Real.hasDerivAt_cos θ).neg.mul_const (Real.cos φ)
  · exact hasDerivAt_const _ _

/-- Derivative of rotMθ w.r.t. φ gives rotMθφ -/
lemma hasDerivAt_rotMθ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMθ θ φ' S) (rotMθφ θ φ S) φ := by
  refine hasDerivAt_toEuclideanLin_apply (M := (rotMθ_mat θ ·)) (M' := (rotMθφ_mat θ ·)) (fun i j => ?_) S
  fin_cases i <;> fin_cases j <;>
    simp only [rotMθ_mat, rotMθφ_mat, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · simpa [neg_mul, mul_neg] using (Real.hasDerivAt_cos φ).const_mul (Real.sin θ)
  · simpa [neg_mul, mul_neg] using (Real.hasDerivAt_cos φ).const_mul (-Real.cos θ)
  · exact hasDerivAt_const _ _

/-- Derivative of rotMφ w.r.t. θ gives rotMθφ -/
lemma hasDerivAt_rotMφ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMφ θ' φ S) (rotMθφ θ φ S) θ := by
  refine hasDerivAt_toEuclideanLin_apply (M := (rotMφ_mat · φ)) (M' := (rotMθφ_mat · φ)) (fun i j => ?_) S
  fin_cases i <;> fin_cases j <;>
    simp only [rotMφ_mat, rotMθφ_mat, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · simpa [neg_mul, mul_neg] using (Real.hasDerivAt_cos θ).mul_const (Real.sin φ)
  · simpa using (Real.hasDerivAt_sin θ).mul_const (Real.sin φ)
  · exact hasDerivAt_const _ _

/-- Derivative of rotMφ w.r.t. φ gives rotMφφ -/
lemma hasDerivAt_rotMφ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMφ θ φ' S) (rotMφφ θ φ S) φ := by
  refine hasDerivAt_toEuclideanLin_apply (M := (rotMφ_mat θ ·)) (M' := (rotMφφ_mat θ ·)) (fun i j => ?_) S
  fin_cases i <;> fin_cases j <;>
    simp only [rotMφ_mat, rotMφφ_mat, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · simpa using (Real.hasDerivAt_sin φ).const_mul (Real.cos θ)
  · simpa using (Real.hasDerivAt_sin φ).const_mul (Real.sin θ)
  · simpa using Real.hasDerivAt_cos φ

/-- Derivative of rotMθθ w.r.t. θ gives -rotMθ (third θ-derivative of rotM) -/
lemma hasDerivAt_rotMθθ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMθθ θ' φ S) (-(rotMθ θ φ S)) θ := by
  have h := hasDerivAt_toEuclideanLin_apply (M := (rotMθθ_mat · φ))
    (M' := fun t => -(rotMθ_mat t φ)) (t := θ) (fun i j => ?_) S
  · simpa [rotMθθ, rotMθ] using h
  fin_cases i <;> fin_cases j <;>
    simp only [rotMθθ_mat, rotMθ_mat, Matrix.neg_apply, Fin.zero_eta, Fin.isValue,
      Fin.mk_one, Fin.reduceFinMk]
  · simpa using Real.hasDerivAt_sin θ
  · exact (Real.hasDerivAt_cos θ).neg
  · simpa using hasDerivAt_const θ (0 : ℝ)
  · simpa [neg_mul] using (Real.hasDerivAt_cos θ).mul_const (Real.cos φ)
  · simpa using (Real.hasDerivAt_sin θ).mul_const (Real.cos φ)
  · simpa using hasDerivAt_const θ (0 : ℝ)

/-- Derivative of rotMθθ w.r.t. φ gives rotMθθφ -/
lemma hasDerivAt_rotMθθ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMθθ θ φ' S) (rotMθθφ θ φ S) φ := by
  refine hasDerivAt_toEuclideanLin_apply (M := (rotMθθ_mat θ ·)) (M' := (rotMθθφ_mat θ ·)) (fun i j => ?_) S
  fin_cases i <;> fin_cases j <;>
    simp only [rotMθθ_mat, rotMθθφ_mat, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · simpa [neg_mul, mul_neg] using (Real.hasDerivAt_cos φ).const_mul (Real.cos θ)
  · simpa [neg_mul, mul_neg] using (Real.hasDerivAt_cos φ).const_mul (Real.sin θ)
  · exact hasDerivAt_const _ _

/-- Derivative of rotMθφ w.r.t. θ gives rotMθθφ -/
lemma hasDerivAt_rotMθφ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMθφ θ' φ S) (rotMθθφ θ φ S) θ := by
  refine hasDerivAt_toEuclideanLin_apply (M := (rotMθφ_mat · φ)) (M' := (rotMθθφ_mat · φ)) (fun i j => ?_) S
  fin_cases i <;> fin_cases j <;>
    simp only [rotMθφ_mat, rotMθθφ_mat, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · simpa [neg_mul] using (Real.hasDerivAt_sin θ).neg.mul_const (Real.sin φ)
  · simpa [neg_mul] using (Real.hasDerivAt_cos θ).mul_const (Real.sin φ)
  · exact hasDerivAt_const _ _

/-- Derivative of rotMθφ w.r.t. φ gives rotMθφφ -/
lemma hasDerivAt_rotMθφ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMθφ θ φ' S) (rotMθφφ θ φ S) φ := by
  refine hasDerivAt_toEuclideanLin_apply (M := (rotMθφ_mat θ ·)) (M' := (rotMθφφ_mat θ ·)) (fun i j => ?_) S
  fin_cases i <;> fin_cases j <;>
    simp only [rotMθφ_mat, rotMθφφ_mat, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · simpa [neg_mul, mul_neg] using (Real.hasDerivAt_sin φ).const_mul (-Real.sin θ)
  · simpa using (Real.hasDerivAt_sin φ).const_mul (Real.cos θ)
  · exact hasDerivAt_const _ _

/-- Derivative of rotMφφ w.r.t. θ gives rotMθφφ -/
lemma hasDerivAt_rotMφφ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMφφ θ' φ S) (rotMθφφ θ φ S) θ := by
  refine hasDerivAt_toEuclideanLin_apply (M := (rotMφφ_mat · φ)) (M' := (rotMθφφ_mat · φ)) (fun i j => ?_) S
  fin_cases i <;> fin_cases j <;>
    simp only [rotMφφ_mat, rotMθφφ_mat, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · simpa [neg_mul] using (Real.hasDerivAt_cos θ).mul_const (Real.cos φ)
  · simpa using (Real.hasDerivAt_sin θ).mul_const (Real.cos φ)
  · exact hasDerivAt_const _ _

/-- Derivative of rotMφφ w.r.t. φ gives -rotMφ (third φ-derivative of rotM) -/
lemma hasDerivAt_rotMφφ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMφφ θ φ' S) (-(rotMφ θ φ S)) φ := by
  have h := hasDerivAt_toEuclideanLin_apply (M := (rotMφφ_mat θ ·))
    (M' := fun t => -(rotMφ_mat θ t)) (t := φ) (fun i j => ?_) S
  · simpa [rotMφφ, rotMφ] using h
  fin_cases i <;> fin_cases j <;>
    simp only [rotMφφ_mat, rotMφ_mat, Matrix.neg_apply, Fin.zero_eta, Fin.isValue,
      Fin.mk_one, Fin.reduceFinMk]
  · simpa using hasDerivAt_const φ (0 : ℝ)
  · simpa using hasDerivAt_const φ (0 : ℝ)
  · simpa using hasDerivAt_const φ (0 : ℝ)
  · simpa [mul_neg] using (Real.hasDerivAt_cos φ).const_mul (Real.cos θ)
  · simpa [mul_neg] using (Real.hasDerivAt_cos φ).const_mul (Real.sin θ)
  · exact (Real.hasDerivAt_sin φ).neg

/-! Derivatives of the mixed third-order matrices and of `rotMθθφφ`.  With
`∂θ³ = -∂θ` and `∂φ³ = -∂φ` these close the grid
`{∂θᵃ∂φᵇ rotM : a, b ≤ 2}` under both partial derivatives (up to sign). -/

/-- Derivative of rotMθθφ w.r.t. θ gives -rotMθφ -/
lemma hasDerivAt_rotMθθφ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMθθφ θ' φ S) (-(rotMθφ θ φ S)) θ := by
  have h := hasDerivAt_toEuclideanLin_apply (M := (rotMθθφ_mat · φ))
    (M' := fun t => -(rotMθφ_mat t φ)) (t := θ) (fun i j => ?_) S
  · simpa [rotMθθφ, rotMθφ] using h
  fin_cases i <;> fin_cases j <;>
    simp only [rotMθθφ_mat, rotMθφ_mat, Matrix.neg_apply, Fin.zero_eta, Fin.isValue,
      Fin.mk_one, Fin.reduceFinMk]
  · simpa using hasDerivAt_const θ (0 : ℝ)
  · simpa using hasDerivAt_const θ (0 : ℝ)
  · simpa using hasDerivAt_const θ (0 : ℝ)
  · simpa [neg_mul] using (Real.hasDerivAt_cos θ).neg.mul_const (Real.sin φ)
  · simpa [neg_mul] using (Real.hasDerivAt_sin θ).neg.mul_const (Real.sin φ)
  · simpa using hasDerivAt_const θ (0 : ℝ)

/-- Derivative of rotMθθφ w.r.t. φ gives rotMθθφφ -/
lemma hasDerivAt_rotMθθφ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMθθφ θ φ' S) (rotMθθφφ θ φ S) φ := by
  refine hasDerivAt_toEuclideanLin_apply (M := (rotMθθφ_mat θ ·)) (M' := (rotMθθφφ_mat θ ·)) (fun i j => ?_) S
  fin_cases i <;> fin_cases j <;>
    simp only [rotMθθφ_mat, rotMθθφφ_mat, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · simpa [neg_mul] using (Real.hasDerivAt_sin φ).const_mul (-Real.cos θ)
  · simpa [neg_mul] using (Real.hasDerivAt_sin φ).const_mul (-Real.sin θ)
  · exact hasDerivAt_const _ _

/-- Derivative of rotMθφφ w.r.t. θ gives rotMθθφφ -/
lemma hasDerivAt_rotMθφφ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMθφφ θ' φ S) (rotMθθφφ θ φ S) θ := by
  refine hasDerivAt_toEuclideanLin_apply (M := (rotMθφφ_mat · φ)) (M' := (rotMθθφφ_mat · φ)) (fun i j => ?_) S
  fin_cases i <;> fin_cases j <;>
    simp only [rotMθφφ_mat, rotMθθφφ_mat, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · simpa [neg_mul] using (Real.hasDerivAt_sin θ).neg.mul_const (Real.cos φ)
  · simpa [neg_mul] using (Real.hasDerivAt_cos θ).mul_const (Real.cos φ)
  · exact hasDerivAt_const _ _

/-- Derivative of rotMθφφ w.r.t. φ gives -rotMθφ -/
lemma hasDerivAt_rotMθφφ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMθφφ θ φ' S) (-(rotMθφ θ φ S)) φ := by
  have h := hasDerivAt_toEuclideanLin_apply (M := (rotMθφφ_mat θ ·))
    (M' := fun t => -(rotMθφ_mat θ t)) (t := φ) (fun i j => ?_) S
  · simpa [rotMθφφ, rotMθφ] using h
  fin_cases i <;> fin_cases j <;>
    simp only [rotMθφφ_mat, rotMθφ_mat, Matrix.neg_apply, Fin.zero_eta, Fin.isValue,
      Fin.mk_one, Fin.reduceFinMk]
  · simpa using hasDerivAt_const φ (0 : ℝ)
  · simpa using hasDerivAt_const φ (0 : ℝ)
  · simpa using hasDerivAt_const φ (0 : ℝ)
  · simpa [neg_mul, mul_neg] using (Real.hasDerivAt_cos φ).const_mul (-Real.sin θ)
  · simpa [neg_mul, mul_neg] using (Real.hasDerivAt_cos φ).const_mul (Real.cos θ)
  · simpa using hasDerivAt_const φ (0 : ℝ)

/-- Derivative of rotMθθφφ w.r.t. θ gives -rotMθφφ -/
lemma hasDerivAt_rotMθθφφ_θ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun θ' => rotMθθφφ θ' φ S) (-(rotMθφφ θ φ S)) θ := by
  have h := hasDerivAt_toEuclideanLin_apply (M := (rotMθθφφ_mat · φ))
    (M' := fun t => -(rotMθφφ_mat t φ)) (t := θ) (fun i j => ?_) S
  · simpa [rotMθθφφ, rotMθφφ] using h
  fin_cases i <;> fin_cases j <;>
    simp only [rotMθθφφ_mat, rotMθφφ_mat, Matrix.neg_apply, Fin.zero_eta, Fin.isValue,
      Fin.mk_one, Fin.reduceFinMk]
  · simpa using hasDerivAt_const θ (0 : ℝ)
  · simpa using hasDerivAt_const θ (0 : ℝ)
  · simpa using hasDerivAt_const θ (0 : ℝ)
  · simpa [neg_mul] using (Real.hasDerivAt_cos θ).neg.mul_const (Real.cos φ)
  · simpa [neg_mul] using (Real.hasDerivAt_sin θ).neg.mul_const (Real.cos φ)
  · simpa using hasDerivAt_const θ (0 : ℝ)

/-- Derivative of rotMθθφφ w.r.t. φ gives -rotMθθφ -/
lemma hasDerivAt_rotMθθφφ_φ (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun φ' => rotMθθφφ θ φ' S) (-(rotMθθφ θ φ S)) φ := by
  have h := hasDerivAt_toEuclideanLin_apply (M := (rotMθθφφ_mat θ ·))
    (M' := fun t => -(rotMθθφ_mat θ t)) (t := φ) (fun i j => ?_) S
  · simpa [rotMθθφφ, rotMθθφ] using h
  fin_cases i <;> fin_cases j <;>
    simp only [rotMθθφφ_mat, rotMθθφ_mat, Matrix.neg_apply, Fin.zero_eta, Fin.isValue,
      Fin.mk_one, Fin.reduceFinMk]
  · simpa using hasDerivAt_const φ (0 : ℝ)
  · simpa using hasDerivAt_const φ (0 : ℝ)
  · simpa using hasDerivAt_const φ (0 : ℝ)
  · simpa [neg_mul, mul_neg] using (Real.hasDerivAt_cos φ).const_mul (-Real.cos θ)
  · simpa [neg_mul, mul_neg] using (Real.hasDerivAt_cos φ).const_mul (-Real.sin θ)
  · simpa using hasDerivAt_const φ (0 : ℝ)

end
