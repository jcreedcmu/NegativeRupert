module

public import Mathlib.Algebra.Lie.OfAssociative
public import Noperthedron.PointSym
public import Noperthedron.PoseInterval
public import Noperthedron.RationalApprox.Basic
public import Noperthedron.RationalApprox.MatrixBounds
public import Noperthedron.Local.Prelims

public section


open scoped RealInnerProductSpace

namespace RationalApprox

variable {P Q Q_ P_ : ℝ³} {θ φ : Set.Icc (-4 : ℝ) 4}

/-!
## Helper: vector norm difference bound

The operator norm bound `‖vecXL θ φ - vecXLℚℝ θ φ‖ ≤ κ` implies
the vector norm bound `‖vecX θ φ - vecXℚ θ φ‖ ≤ κ` because `vecX`
is the image of the unit basis vector under the column-matrix linear map `vecXL`.
-/

private lemma vecX_sub_vecXℚ_norm_le (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4) 4)
    (hφ : φ ∈ Set.Icc (-4) 4) :
    ‖vecX θ φ - vecXℚℝ θ φ‖ ≤ κ := by
  -- vecX θ φ - vecXℚ θ φ = (vecXL θ φ - vecXLℚℝ θ φ) (single 0 1)
  have h_eq : vecX θ φ - vecXℚℝ θ φ = (vecXL θ φ - vecXLℚℝ θ φ) (EuclideanSpace.single 0 1) := by
    simp [vecX, vecXℚℝ, vecXL, vecX_mat, vecXLℚℝ, vecXℚ_mat, sub_apply, Matrix.toLpLin_apply]
    ext i; fin_cases i <;> simp
  rw [h_eq]
  calc ‖(vecXL θ φ - vecXLℚℝ θ φ) (EuclideanSpace.single 0 1)‖
    _ ≤ ‖vecXL θ φ - vecXLℚℝ θ φ‖ * ‖EuclideanSpace.single (𝕜 := ℝ) 0 (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖vecXL θ φ - vecXLℚℝ θ φ‖ * 1 := by rw [PiLp.norm_single, norm_one]
    _ = ‖vecXL θ φ - vecXLℚℝ θ φ‖ := mul_one _
    _ ≤ κ := X_difference_norm_bounded θ φ hθ hφ

private lemma vecXℚ_norm_le (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4) 4)
    (hφ : φ ∈ Set.Icc (-4) 4) :
    ‖vecXℚℝ θ φ‖ ≤ 1 + κ := by
  calc ‖vecXℚℝ θ φ‖
    _ ≤ ‖vecX θ φ‖ + ‖vecX θ φ - vecXℚℝ θ φ‖ := norm_le_insert _ _
    _ = 1 + ‖vecX θ φ - vecXℚℝ θ φ‖ := by rw [Bounding.vecX_norm_one]
    _ ≤ 1 + κ := by gcongr; exact vecX_sub_vecXℚ_norm_le θ φ hθ hφ

/-!
[SY25] Lemma 49
-/

lemma bounds_kappa3_X (hP : ‖P‖ ≤ 1) (Papprox : ‖P - P_‖ ≤ κ) :
    ‖⟪vecX θ φ, P⟫ - ⟪vecXℚℝ θ φ, P_⟫‖ ≤ 3 * κ := by
  -- Decompose: ⟪vecX, P⟫ - ⟪vecXℚ, P_⟫ = ⟪vecX - vecXℚ, P⟫ + ⟪vecXℚ, P - P_⟫
  have decomp : ⟪vecX θ φ, P⟫ - ⟪vecXℚℝ θ φ, P_⟫ =
      ⟪vecX θ φ - vecXℚℝ θ φ, P⟫ + ⟪vecXℚℝ θ φ, P - P_⟫ := by
    simp [inner_sub_left, inner_sub_right]
  rw [decomp, Real.norm_eq_abs]
  calc |⟪vecX ↑θ ↑φ - vecXℚℝ ↑θ ↑φ, P⟫ + ⟪vecXℚℝ ↑θ ↑φ, P - P_⟫|
    _ ≤ |⟪vecX ↑θ ↑φ - vecXℚℝ ↑θ ↑φ, P⟫| + |⟪vecXℚℝ ↑θ ↑φ, P - P_⟫| := abs_add_le _ _
    _ ≤ ‖vecX ↑θ ↑φ - vecXℚℝ ↑θ ↑φ‖ * ‖P‖ + ‖vecXℚℝ ↑θ ↑φ‖ * ‖P - P_‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ κ * 1 + (1 + κ) * κ :=
        add_le_add
          (mul_le_mul (vecX_sub_vecXℚ_norm_le _ _ (θ.property) (φ.property))
            hP (norm_nonneg _) (by norm_num [κ]))
          (mul_le_mul (vecXℚ_norm_le _ _ (θ.property) (φ.property))
            Papprox (norm_nonneg _) (by norm_num [κ]))
    _ ≤ 3 * κ := by unfold κ; norm_num

end RationalApprox
end
