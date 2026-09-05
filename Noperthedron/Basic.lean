module

public import Noperthedron.Rupert.Basic

@[expose] public section


open scoped Matrix

open Real

-- flip about y-axis
@[simp]
noncomputable
def flip_y_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1,  0;
     0, -1]

noncomputable
def flip_y : (ℝ² →L[ℝ] ℝ²) := flip_y_mat |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def flip_y_equiv : (ℝ² ≃L[ℝ] ℝ²) := {
  flip_y with
  invFun := flip_y,
  left_inv := by intro v; ext i; fin_cases i <;> (simp [flip_y, Matrix.vecHead, Matrix.vecTail])
  right_inv := by intro v; ext i; fin_cases i <;> (simp [flip_y, Matrix.vecHead, Matrix.vecTail])
}

-- dimension reduction with a rotation baked in
@[simp]
noncomputable
def reduce_mat : Matrix (Fin 2) (Fin 3) ℝ :=
  !![0,  1, 0;
     -1, 0, 0]

noncomputable
def reduceL : (ℝ³ →L[ℝ] ℝ²) := reduce_mat |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def proj_xy_mat : Matrix (Fin 2) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 1, 0]

noncomputable
def proj_xyL : (ℝ³ →L[ℝ] ℝ²) := proj_xy_mat |>.toEuclideanLin.toContinuousLinearMap

/-
As mere functions, `proj_xy` and `proj_xyL` are the same.
The only difference is that `proj_xyL` knows that it is continuous linear,
and it's defined a little differently, via a matrix, which is the reason
that it's so easy to see that it's linear.

I think we ought to prefer `proj_xyL` to `proj_xy` in most places.
but this lemma lets us push back the boundary between the newer uses
of `proj_xyL` and the older uses of `proj_xy`.
-/
lemma proj_xy_eq_proj_xyL :
    proj_xy = proj_xyL := by
  ext1
  simp only [proj_xy, Fin.isValue, proj_xyL, proj_xy_mat, LinearMap.coe_toContinuousLinearMap']
  ext i
  fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]

-- rotation about x-axis by θ
@[simp]
noncomputable
def Rx_mat (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,     0,      0;
     0, cos θ, -sin θ;
     0, sin θ,  cos θ]

noncomputable
def RxL (θ : ℝ) : (ℝ³ →L[ℝ] ℝ³) := Rx_mat θ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def RxC : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := RxL α
  map_zero_eq_one' := by
    ext v i; fin_cases i <;> simp [RxL, Matrix.vecHead, Matrix.vecTail]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;> (simp [RxL, Matrix.vecHead, Matrix.vecTail, cos_add, sin_add]; try ring)

lemma RxC_coe : RxC = RxL := rfl

@[simp]
noncomputable
def Ry_mat (θ : ℝ) : (Matrix (Fin 3) (Fin 3) ℝ) :=
  !![cos θ, 0, -sin θ;
     0,     1,      0;
     sin θ, 0,  cos θ]

noncomputable
def RyL (θ : ℝ) : (ℝ³ →L[ℝ] ℝ³) := Ry_mat θ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def RyC : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := RyL α
  map_zero_eq_one' := by
    ext v i; fin_cases i <;> simp [RyL,  Matrix.vecHead, Matrix.vecTail]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;> (simp [RyL, Matrix.vecHead, Matrix.vecTail, cos_add, sin_add]; try ring)

lemma RyC_coe : RyC = RyL := rfl

-- rotation about z-axis by θ
@[simp]
noncomputable
def Rz_mat (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos θ, -sin θ, 0;
     sin θ,  cos θ, 0;
     0,      0,     1]

noncomputable
def RzL (θ : ℝ) : (ℝ³ →L[ℝ] ℝ³) := Rz_mat θ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def RzC : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := RzL α
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [RzL, Matrix.vecHead, Matrix.vecTail]
  map_add_eq_mul' a b := by
    ext v i
    fin_cases i <;> {
      simp [RzL, Fin.sum_univ_succ, Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Rz_mat, cos_add, sin_add];
      try ring_nf
    }

lemma RzC_coe : RzC = RzL := rfl

@[simp]
theorem Rz_mat_add_int_mul_two_pi (z : ℤ) (x : ℝ) : Rz_mat (x + z * (2 * π)) = Rz_mat x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem RzC_two_pi (z : ℤ) : RzC (2 * π * z) = RzC 0 := by
  simp only [show 2 * π * z = 0 + z * (2 * π) by ring_nf, RzC, RzL, AddChar.coe_mk]
  simp only [Rz_mat_add_int_mul_two_pi]

noncomputable
def rot3_mat : Fin 3 → ℝ → Matrix (Fin 3) (Fin 3) ℝ
  | 0 => Rx_mat
  | 1 => Ry_mat
  | 2 => Rz_mat

noncomputable
def rot3 : Fin 3 → AddChar ℝ (ℝ³ →L[ℝ] ℝ³)
  | 0 => RxC
  | 1 => RyC
  | 2 => RzC

@[simp]
noncomputable
def rotR_mat (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos α, -Real.sin α;
     Real.sin α,  Real.cos α]

@[simp]
noncomputable
def rotR'_mat (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-Real.sin α, -Real.cos α;
     Real.cos α,  -Real.sin α]

-- [SY25] § 1.1 Definition 2
noncomputable
def rotR : AddChar ℝ (ℝ² →L[ℝ] ℝ²) where
  toFun α := (rotR_mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext x i
    fin_cases i <;> simp [Matrix.toEuclideanLin, Matrix.vecHead, Matrix.vecTail]

  map_add_eq_mul' := by
    intro α β
    ext v i
    fin_cases i <;> {
      simp [Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, rotR_mat, cos_add, sin_add]
      ring_nf
     }

-- Derivative of rotR with respect to its parameter
noncomputable
def rotR' (α : ℝ) : ℝ² →L[ℝ] ℝ² :=
  (rotR'_mat α).toEuclideanLin.toContinuousLinearMap

/-- Differentiating a planar rotation adds a quarter turn. -/
lemma rotR'_eq_rotR_add_pi_div_two (α : ℝ) :
    rotR' α = rotR (α + π / 2) := by
  ext v i
  fin_cases i <;> simp [rotR', rotR'_mat, rotR, rotR_mat,
    Matrix.vecHead, Matrix.vecTail, sin_add_pi_div_two, cos_add_pi_div_two]

-- [SY25] § 1.1 Definition 2
noncomputable
def vecX (θ : ℝ) (φ : ℝ) : ℝ³ :=
  !₂[ cos θ * sin φ, sin θ * sin φ, cos φ ]

noncomputable
def vecX_mat (θ : ℝ) (φ : ℝ) : Matrix (Fin 3) (Fin 1) ℝ :=
  !![ cos θ * sin φ; sin θ * sin φ; cos φ ]

noncomputable
def vecXL (θ : ℝ) (φ : ℝ) : Euc(1) →L[ℝ] ℝ³ :=
  vecX_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

-- [SY25] § 1.1 Definition 2
noncomputable
def rotM_mat (θ : ℝ) (φ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![-sin θ, cos θ, 0; -cos θ * cos φ, -sin θ * cos φ, sin φ]

noncomputable
def rotM (θ : ℝ) (φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotM_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

-- Partial derivative of rotM with respect to θ
noncomputable
def rotMθ_mat (θ : ℝ) (φ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![-cos θ, -sin θ, 0; sin θ * cos φ, -cos θ * cos φ, 0]

noncomputable
def rotMθ (θ : ℝ) (φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  (rotMθ_mat θ φ).toEuclideanLin.toContinuousLinearMap

-- Partial derivative of rotM with respect to φ
noncomputable
def rotMφ_mat (θ : ℝ) (φ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![0, 0, 0; cos θ * sin φ, sin θ * sin φ, cos φ]

noncomputable
def rotMφ (θ : ℝ) (φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  (rotMφ_mat θ φ).toEuclideanLin.toContinuousLinearMap

-- Second partial derivatives of rotM
-- ∂²rotM/∂θ² (derivative of rotMθ w.r.t. θ)
noncomputable
def rotMθθ_mat (θ : ℝ) (φ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![sin θ, -cos θ, 0; cos θ * cos φ, sin θ * cos φ, 0]

noncomputable
def rotMθθ (θ : ℝ) (φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  (rotMθθ_mat θ φ).toEuclideanLin.toContinuousLinearMap

-- ∂²rotM/∂θ∂φ (derivative of rotMθ w.r.t. φ, or rotMφ w.r.t. θ)
noncomputable
def rotMθφ_mat (θ : ℝ) (φ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![0, 0, 0; -sin θ * sin φ, cos θ * sin φ, 0]

noncomputable
def rotMθφ (θ : ℝ) (φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  (rotMθφ_mat θ φ).toEuclideanLin.toContinuousLinearMap

-- ∂²rotM/∂φ² (derivative of rotMφ w.r.t. φ)
noncomputable
def rotMφφ_mat (θ : ℝ) (φ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![0, 0, 0; cos θ * cos φ, sin θ * cos φ, -sin φ]

noncomputable
def rotMφφ (θ : ℝ) (φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  (rotMφφ_mat θ φ).toEuclideanLin.toContinuousLinearMap

-- Third partial derivatives of rotM.  Only the two mixed ones need new
-- definitions: ∂³rotM/∂θ³ = -rotMθ and ∂³rotM/∂φ³ = -rotMφ.
-- ∂³rotM/∂θ²∂φ (derivative of rotMθθ w.r.t. φ, or of rotMθφ w.r.t. θ)
noncomputable
def rotMθθφ_mat (θ : ℝ) (φ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![0, 0, 0; -cos θ * sin φ, -sin θ * sin φ, 0]

noncomputable
def rotMθθφ (θ : ℝ) (φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  (rotMθθφ_mat θ φ).toEuclideanLin.toContinuousLinearMap

-- ∂³rotM/∂θ∂φ² (derivative of rotMθφ w.r.t. φ, or of rotMφφ w.r.t. θ)
noncomputable
def rotMθφφ_mat (θ : ℝ) (φ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![0, 0, 0; -sin θ * cos φ, cos θ * cos φ, 0]

noncomputable
def rotMθφφ (θ : ℝ) (φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  (rotMθφφ_mat θ φ).toEuclideanLin.toContinuousLinearMap

-- ∂⁴rotM/∂θ²∂φ² (derivative of rotMθθφ w.r.t. φ, or of rotMθφφ w.r.t. θ).
-- The last member of the ∂-closed derivative grid `rotMFam`: together with
-- ∂θ³ = -∂θ and ∂φ³ = -∂φ it closes the family {∂θᵃ∂φᵇ rotM : a, b ≤ 2}
-- under both partial derivatives (up to sign).
noncomputable
def rotMθθφφ_mat (θ : ℝ) (φ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![0, 0, 0; -cos θ * cos φ, -sin θ * cos φ, 0]

noncomputable
def rotMθθφφ (θ : ℝ) (φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  (rotMθθφφ_mat θ φ).toEuclideanLin.toContinuousLinearMap

infixr:80 " ∘ᵃ " => AffineMap.comp

-- This is R(α) M(θ, φ) in (5) in [SY25] § 2.2,
-- except we don't project to ℝ²
noncomputable
def rotRM (θ : ℝ) (φ : ℝ) (α : ℝ) : ℝ³ →L[ℝ] ℝ³ :=
  RzL (-(π / 2)) ∘L RzL α ∘L RyL φ ∘L RzL (-θ)

-- This is R(α) M(θ, φ) in (5) in [SY25] § 2.2,
noncomputable
def rotprojRM (θ : ℝ) (φ : ℝ) (α : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotR α ∘L rotM θ φ

/-
Some nice identities as laid out in [SY25] §2.2
-/

lemma vecX_identity (θ φ : ℝ) :
    vecX θ φ = (RzL θ ∘L RyL (-φ)) !₂[0, 0, 1] := by
  ext i
  fin_cases i <;> simp [RyL, RzL, Matrix.vecHead, Matrix.vecTail, vecX]

lemma rotM_identity (θ φ : ℝ) : rotM θ φ = reduceL ∘L RyL φ ∘L RzL (-θ) := by
  unfold reduceL
  ext v i
  fin_cases i <;> (simp [RzL, RyL, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]; try ring_nf)

lemma rotprojRM_identity (θ φ α : ℝ) : rotprojRM θ φ α = reduceL ∘L RzL α ∘L RyL φ ∘L RzL (-θ) := by
  simp only [rotprojRM]
  unfold reduceL
  ext v i
  fin_cases i <;>
  · simp [RzL, RyL, rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
    ring_nf

lemma reduce_identity : reduceL = proj_xyL ∘L RzL (-(π / 2)) := by
  unfold reduceL
  ext v i
  simp only [RzL, proj_xyL, proj_xy_mat]
  fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]

lemma projxy_rotRM_eq_rotprojRM (θ φ α : ℝ) : proj_xyL ∘ rotRM θ φ α = rotprojRM θ φ α := by
  rw [rotprojRM_identity, reduce_identity]
  rfl

/-- Projecting to xy after Rz rotation equals 2D rotation after projection. -/
@[simp]
lemma proj_xyL_comp_RzL (δ : ℝ) : proj_xyL ∘L RzL δ = rotR δ ∘L proj_xyL := by
  ext v i
  fin_cases i <;> simp [proj_xyL, proj_xy_mat, RzL, Rz_mat, rotR, rotR_mat,
    Matrix.vecHead, Matrix.vecTail] <;> ring

lemma rotR_add_pi_eq_neg_rotR {α : ℝ} :
    rotR (α + π) = -rotR α := by
  ext v i; fin_cases i <;>
  · simp [Matrix.vecHead, Matrix.vecTail, rotR, rotR_mat]; ring_nf

lemma rotM_mod_eq_neg_rotM {θ φ : ℝ} :
    rotM (θ + π) (2 * π - φ) = -rotM θ φ := by
  ext v i; fin_cases i <;>
  · simp [Matrix.vecHead, Matrix.vecTail, rotM, rotM_mat]; ring_nf

lemma rotRM_mod_eq_rotRM {α θ φ : ℝ} :
    rotR (α + π) ∘ rotM (θ + π) (2 * π - φ) = rotR α ∘ rotM θ φ := by
  simp only [rotR_add_pi_eq_neg_rotR, rotM_mod_eq_neg_rotM]
  ext; simp

lemma rotM_periodic_φ {θ φ : ℝ} {k : ℤ} :
    rotM θ (φ + k * (2 * π)) = rotM θ φ := by
  ext v i; fin_cases i <;>
  · simp [rotM, rotM_mat]

/-- A convex polyhedron, given as a finite indexed set of vertices. -/
structure Polyhedron (ι X : Type) where
  v : ι → X

/-- Cast a `Fin 3 → ℚ` to an `ℝ³` point. -/
def toR3 (v : Fin 3 → ℚ) : ℝ³ :=
  WithLp.toLp 2 (fun i => (v i : ℝ))

/-- Cast a `Fin 2 → ℚ` to an `ℝ²` point. -/
def toR2 (v : Fin 2 → ℚ) : ℝ² :=
  WithLp.toLp 2 (fun i => (v i : ℝ))

noncomputable
def Polyhedron.toReal {ι : Type} (p : Polyhedron ι (Fin 3 → ℚ)) : Polyhedron ι ℝ³ :=
  ⟨fun j => toR3 (p.v j)⟩

def Polyhedron.hull {ι : Type} [Fintype ι] (poly : Polyhedron ι ℝ³) : Set ℝ³ :=
  convexHull ℝ { poly.v i | i }

structure GoodPoly (ι : Type) [Fintype ι] [Nonempty ι] where
  vertices : Polyhedron ι ℝ³
  nontriv : ∀ i, 0 < ‖vertices.v i‖
  vertex_radius_le_one : ∀ i, ‖vertices.v i‖ ≤ 1

def GoodPoly.hull {ι : Type} [Fintype ι] [Nonempty ι] (poly : GoodPoly ι) : Set ℝ³ :=
  poly.vertices.hull

end
