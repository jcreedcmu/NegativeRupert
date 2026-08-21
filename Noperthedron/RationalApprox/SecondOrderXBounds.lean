module

public import Noperthedron.Global.VecXPartials
public import Noperthedron.RationalApprox.Basic
public import Noperthedron.RationalApprox.MatrixBounds
public import Noperthedron.RationalApprox.Cast

@[expose] public section


/-!
# κ-bounds for the partial-derivative `X` vectors

Rational counterparts of `vecXθ`/`vecXφ`/`vecXθθ`/`vecXθφ` (the first and
second partials of the axis vector, used by the second-order `Aε₂`
condition), with the same `DistLeKappaEntry` machinery as `vecX` itself:
entrywise trig-approximation error gives `‖vecXa − vecXaℚℝ‖ ≤ κ`, and the
inner products against a κ-approximated vertex are within `3κ`.
-/

open scoped RealInnerProductSpace

namespace RationalApprox

/-! ## The rational vectors and their real casts -/

def vecXθℚ (θ φ : ℚ) : (Fin 3 → ℚ) :=
  ![ -sinℚ θ * sinℚ φ, cosℚ θ * sinℚ φ, 0 ]

def vecXφℚ (θ φ : ℚ) : (Fin 3 → ℚ) :=
  ![ cosℚ θ * cosℚ φ, sinℚ θ * cosℚ φ, -sinℚ φ ]

def vecXθθℚ (θ φ : ℚ) : (Fin 3 → ℚ) :=
  ![ -cosℚ θ * sinℚ φ, -sinℚ θ * sinℚ φ, 0 ]

def vecXθφℚ (θ φ : ℚ) : (Fin 3 → ℚ) :=
  ![ -sinℚ θ * cosℚ φ, cosℚ θ * cosℚ φ, 0 ]

noncomputable def vecXθℚℝ (θ φ : ℝ) : ℝ³ :=
  !₂[ -sinℚ θ * sinℚ φ, cosℚ θ * sinℚ φ, 0 ]

noncomputable def vecXφℚℝ (θ φ : ℝ) : ℝ³ :=
  !₂[ cosℚ θ * cosℚ φ, sinℚ θ * cosℚ φ, -sinℚ φ ]

noncomputable def vecXθθℚℝ (θ φ : ℝ) : ℝ³ :=
  !₂[ -cosℚ θ * sinℚ φ, -sinℚ θ * sinℚ φ, 0 ]

noncomputable def vecXθφℚℝ (θ φ : ℝ) : ℝ³ :=
  !₂[ -sinℚ θ * cosℚ φ, cosℚ θ * cosℚ φ, 0 ]

lemma toR3_vecXθℚ (θ φ : ℚ) : toR3 (vecXθℚ θ φ) = vecXθℚℝ (↑θ : ℝ) ↑φ := by
  ext j; unfold toR3 vecXθℚ vecXθℚℝ
  fin_cases j <;> simp [sinℚ_match, cosℚ_match]

lemma toR3_vecXφℚ (θ φ : ℚ) : toR3 (vecXφℚ θ φ) = vecXφℚℝ (↑θ : ℝ) ↑φ := by
  ext j; unfold toR3 vecXφℚ vecXφℚℝ
  fin_cases j <;> simp [sinℚ_match, cosℚ_match]

lemma toR3_vecXθθℚ (θ φ : ℚ) : toR3 (vecXθθℚ θ φ) = vecXθθℚℝ (↑θ : ℝ) ↑φ := by
  ext j; unfold toR3 vecXθθℚ vecXθθℚℝ
  fin_cases j <;> simp [sinℚ_match, cosℚ_match]

lemma toR3_vecXθφℚ (θ φ : ℚ) : toR3 (vecXθφℚ θ φ) = vecXθφℚℝ (↑θ : ℝ) ↑φ := by
  ext j; unfold toR3 vecXθφℚ vecXθφℚℝ
  fin_cases j <;> simp [sinℚ_match, cosℚ_match]

/-! ## Approximation matrices and difference bounds -/

def vecXθ_approx : Matrix (Fin 3) (Fin 1) DistLeKappaEntry :=
  !![ (.msin, .sin); (.cos, .sin); (.zero, .zero) ]

def vecXφ_approx : Matrix (Fin 3) (Fin 1) DistLeKappaEntry :=
  !![ (.cos, .cos); (.sin, .cos); (.one, .msin) ]

def vecXθθ_approx : Matrix (Fin 3) (Fin 1) DistLeKappaEntry :=
  !![ (.mcos, .sin); (.msin, .sin); (.zero, .zero) ]

def vecXθφ_approx : Matrix (Fin 3) (Fin 1) DistLeKappaEntry :=
  !![ (.msin, .cos); (.cos, .cos); (.zero, .zero) ]

/-- The column of a 3×1 `DistLeKappaEntry` difference, as a vector norm
bound: the operator-norm bound applied to the basis vector. -/
private lemma column_diff_norm_le
    (A : Matrix (Fin 3) (Fin 1) DistLeKappaEntry) (θ_ φ_ : Set.Icc (-4 : ℝ) 4)
    {v vℚ : ℝ³}
    (hv : v = clinActual A θ_ φ_ (EuclideanSpace.single 0 1))
    (hvℚ : vℚ = clinApprox A θ_ φ_ (EuclideanSpace.single 0 1)) :
    ‖v - vℚ‖ ≤ κ := by
  rw [hv, hvℚ, ← sub_apply]
  calc ‖(clinActual A θ_ φ_ - clinApprox A θ_ φ_) (EuclideanSpace.single 0 1)‖
    _ ≤ ‖clinActual A θ_ φ_ - clinApprox A θ_ φ_‖ *
        ‖EuclideanSpace.single (𝕜 := ℝ) 0 (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖clinActual A θ_ φ_ - clinApprox A θ_ φ_‖ := by rw [PiLp.norm_single, norm_one, mul_one]
    _ ≤ κ := norm_matrix_actual_approx_le_kappa (m := ⟨3, by norm_num⟩) (n := ⟨1, by norm_num⟩)
        A θ_ φ_

theorem Xθ_difference_norm_bounded (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4) 4)
    (hφ : φ ∈ Set.Icc (-4) 4) : ‖vecXθ θ φ - vecXθℚℝ θ φ‖ ≤ κ := by
  refine column_diff_norm_le vecXθ_approx ⟨θ, hθ⟩ ⟨φ, hφ⟩ ?_ ?_ <;>
    · ext i
      fin_cases i <;>
        simp [vecXθ, vecXθℚℝ, clinActual, clinApprox, vecXθ_approx, Matrix.toLpLin_apply]

theorem Xφ_difference_norm_bounded (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4) 4)
    (hφ : φ ∈ Set.Icc (-4) 4) : ‖vecXφ θ φ - vecXφℚℝ θ φ‖ ≤ κ := by
  refine column_diff_norm_le vecXφ_approx ⟨θ, hθ⟩ ⟨φ, hφ⟩ ?_ ?_ <;>
    · ext i
      fin_cases i <;>
        simp [vecXφ, vecXφℚℝ, clinActual, clinApprox, vecXφ_approx, Matrix.toLpLin_apply]

theorem Xθθ_difference_norm_bounded (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4) 4)
    (hφ : φ ∈ Set.Icc (-4) 4) : ‖vecXθθ θ φ - vecXθθℚℝ θ φ‖ ≤ κ := by
  refine column_diff_norm_le vecXθθ_approx ⟨θ, hθ⟩ ⟨φ, hφ⟩ ?_ ?_ <;>
    · ext i
      fin_cases i <;>
        simp [vecXθθ, vecXθθℚℝ, clinActual, clinApprox, vecXθθ_approx, Matrix.toLpLin_apply]

theorem Xθφ_difference_norm_bounded (θ φ : ℝ) (hθ : θ ∈ Set.Icc (-4) 4)
    (hφ : φ ∈ Set.Icc (-4) 4) : ‖vecXθφ θ φ - vecXθφℚℝ θ φ‖ ≤ κ := by
  refine column_diff_norm_le vecXθφ_approx ⟨θ, hθ⟩ ⟨φ, hφ⟩ ?_ ?_ <;>
    · ext i
      fin_cases i <;>
        simp [vecXθφ, vecXθφℚℝ, clinActual, clinApprox, vecXθφ_approx, Matrix.toLpLin_apply]

/-! ## Inner-product bridges

The generic decomposition behind `bounds_kappa3_X`, then its four
instantiations at the derivative vectors. -/

/-- κ-approximated vector against a κ-approximated unit vertex: the inner
products agree within `3κ`. -/
lemma inner_bridge_3kappa {x xℚ P P_ : ℝ³}
    (hdiff : ‖x - xℚ‖ ≤ κ) (hx : ‖x‖ ≤ 1)
    (hP : ‖P‖ ≤ 1) (hPapprox : ‖P - P_‖ ≤ κ) :
    |⟪x, P⟫ - ⟪xℚ, P_⟫| ≤ 3 * κ := by
  have hxℚ : ‖xℚ‖ ≤ 1 + κ := by
    calc ‖xℚ‖ ≤ ‖x‖ + ‖x - xℚ‖ := norm_le_insert _ _
      _ ≤ 1 + κ := add_le_add hx hdiff
  have decomp : ⟪x, P⟫ - ⟪xℚ, P_⟫ = ⟪x - xℚ, P⟫ + ⟪xℚ, P - P_⟫ := by
    simp [inner_sub_left, inner_sub_right]
  rw [decomp]
  calc |⟪x - xℚ, P⟫ + ⟪xℚ, P - P_⟫|
    _ ≤ |⟪x - xℚ, P⟫| + |⟪xℚ, P - P_⟫| := abs_add_le _ _
    _ ≤ ‖x - xℚ‖ * ‖P‖ + ‖xℚ‖ * ‖P - P_‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ κ * 1 + (1 + κ) * κ :=
        add_le_add
          (mul_le_mul hdiff hP (norm_nonneg _) (by norm_num [κ]))
          (mul_le_mul hxℚ hPapprox (norm_nonneg _) (by norm_num [κ]))
    _ ≤ 3 * κ := by unfold κ; norm_num

variable {P P_ : ℝ³} {θ φ : Set.Icc (-4 : ℝ) 4}

lemma bounds_kappa3_Xθ (hP : ‖P‖ ≤ 1) (hPapprox : ‖P - P_‖ ≤ κ) :
    |⟪vecXθ ↑θ ↑φ, P⟫ - ⟪vecXθℚℝ ↑θ ↑φ, P_⟫| ≤ 3 * κ :=
  inner_bridge_3kappa (Xθ_difference_norm_bounded _ _ θ.property φ.property)
    (GlobalTheorem.vecXθ_norm_le_one _ _) hP hPapprox

lemma bounds_kappa3_Xφ (hP : ‖P‖ ≤ 1) (hPapprox : ‖P - P_‖ ≤ κ) :
    |⟪vecXφ ↑θ ↑φ, P⟫ - ⟪vecXφℚℝ ↑θ ↑φ, P_⟫| ≤ 3 * κ :=
  inner_bridge_3kappa (Xφ_difference_norm_bounded _ _ θ.property φ.property)
    (GlobalTheorem.vecXφ_norm_le_one _ _) hP hPapprox

lemma bounds_kappa3_Xθθ (hP : ‖P‖ ≤ 1) (hPapprox : ‖P - P_‖ ≤ κ) :
    |⟪vecXθθ ↑θ ↑φ, P⟫ - ⟪vecXθθℚℝ ↑θ ↑φ, P_⟫| ≤ 3 * κ :=
  inner_bridge_3kappa (Xθθ_difference_norm_bounded _ _ θ.property φ.property)
    (GlobalTheorem.vecXθθ_norm_le_one _ _) hP hPapprox

lemma bounds_kappa3_Xθφ (hP : ‖P‖ ≤ 1) (hPapprox : ‖P - P_‖ ≤ κ) :
    |⟪vecXθφ ↑θ ↑φ, P⟫ - ⟪vecXθφℚℝ ↑θ ↑φ, P_⟫| ≤ 3 * κ :=
  inner_bridge_3kappa (Xθφ_difference_norm_bounded _ _ θ.property φ.property)
    (GlobalTheorem.vecXθφ_norm_le_one _ _) hP hPapprox

end RationalApprox
end
