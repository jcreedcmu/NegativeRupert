module

public import Noperthedron.BalancedSupport.TranslatedPose
public import Noperthedron.Bounding.SmallConsecutiveRotations

@[expose] public section


/-!
# Operator-norm bounds for nearby Euler rotations

These estimates turn a rational box radius in the five pose coordinates into
the division-free small-rotation hypothesis used by the snub-cube local
checker.
-/

namespace Noperthedron.BalancedSupport

/-- Perturbing two factors of a product costs at most the sum of the two
perturbations when the untouched factors have norm at most one. -/
theorem norm_comp_sub_comp_le
    (A B C D : ℝ³ →L[ℝ] ℝ³) (hA : ‖A‖ ≤ 1) (hD : ‖D‖ ≤ 1) :
    ‖A ∘L B - C ∘L D‖ ≤ ‖A - C‖ + ‖B - D‖ := by
  have hdecomp : A ∘L B - C ∘L D =
      A ∘L (B - D) + (A - C) ∘L D := by
    ext x
    simp
  rw [hdecomp]
  calc
    ‖A ∘L (B - D) + (A - C) ∘L D‖
        ≤ ‖A ∘L (B - D)‖ + ‖(A - C) ∘L D‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖B - D‖ + ‖A - C‖ * ‖D‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ‖A - C‖ + ‖B - D‖ := by
      have hBC : 0 ≤ ‖B - D‖ := norm_nonneg _
      have hAC : 0 ≤ ‖A - C‖ := norm_nonneg _
      nlinarith

theorem norm_rot3_sub_le (d : Fin 3) (x y : ℝ) :
    ‖rot3 d x - rot3 d y‖ ≤ |x - y| := by
  rw [Bounding.dist_rot3]
  have h : |Real.sin ((x - y) / 2)| ≤ |(x - y) / 2| :=
    Real.abs_sin_le_abs
  rw [abs_div, abs_two] at h
  linarith

private theorem norm_rot3_le_one (d : Fin 3) (x : ℝ) : ‖rot3 d x‖ ≤ 1 := by
  rw [Bounding.lemma9]

private theorem norm_two_rotations_le_one
    (d e : Fin 3) (x y : ℝ) : ‖rot3 d x ∘L rot3 e y‖ ≤ 1 := by
  calc
    ‖rot3 d x ∘L rot3 e y‖ ≤ ‖rot3 d x‖ * ‖rot3 e y‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = 1 := by rw [Bounding.lemma9, Bounding.lemma9, one_mul]

/-- The full unprojected Euler rotation is 1-Lipschitz in the ℓ¹ distance
of its three parameters. -/
theorem norm_rotRM_sub_le (θ φ α θ₀ φ₀ α₀ : ℝ) :
    ‖rotRM θ φ α - rotRM θ₀ φ₀ α₀‖ ≤
      |α - α₀| + |φ - φ₀| + |θ - θ₀| := by
  let tail : ℝ → ℝ → ℝ³ →L[ℝ] ℝ³ := fun φ θ =>
    RyL φ ∘L RzL (-θ)
  have htail (φ θ φ₀ θ₀ : ℝ) :
      ‖tail φ θ - tail φ₀ θ₀‖ ≤ |φ - φ₀| + |θ - θ₀| := by
    apply (norm_comp_sub_comp_le (RyL φ) (RzL (-θ))
      (RyL φ₀) (RzL (-θ₀))
      (norm_rot3_le_one 1 φ) (norm_rot3_le_one 2 (-θ₀))).trans
    have hφ := norm_rot3_sub_le 1 φ φ₀
    have hθ := norm_rot3_sub_le 2 (-θ) (-θ₀)
    change ‖RyL φ - RyL φ₀‖ ≤ |φ - φ₀| at hφ
    change ‖RzL (-θ) - RzL (-θ₀)‖ ≤ |-θ - -θ₀| at hθ
    rw [show -θ - -θ₀ = -(θ - θ₀) by ring, abs_neg] at hθ
    linarith
  have hmiddle :
      ‖RzL α ∘L tail φ θ - RzL α₀ ∘L tail φ₀ θ₀‖ ≤
        |α - α₀| + (|φ - φ₀| + |θ - θ₀|) := by
    apply (norm_comp_sub_comp_le (RzL α) (tail φ θ)
      (RzL α₀) (tail φ₀ θ₀)
      (norm_rot3_le_one 2 α) (norm_two_rotations_le_one 1 2 φ₀ (-θ₀))).trans
    have hα := norm_rot3_sub_le 2 α α₀
    change ‖RzL α - RzL α₀‖ ≤ |α - α₀| at hα
    linarith [htail φ θ φ₀ θ₀]
  simp only [rotRM]
  rw [show RzL (-(Real.pi / 2)) ∘L RzL α ∘L RyL φ ∘L RzL (-θ) =
      RzL (-(Real.pi / 2)) ∘L (RzL α ∘L (RyL φ ∘L RzL (-θ))) by rfl,
    show RzL (-(Real.pi / 2)) ∘L RzL α₀ ∘L RyL φ₀ ∘L RzL (-θ₀) =
      RzL (-(Real.pi / 2)) ∘L (RzL α₀ ∘L (RyL φ₀ ∘L RzL (-θ₀))) by rfl]
  rw [← ContinuousLinearMap.comp_sub]
  rw [Bounding.Rz_preserves_op_norm]
  linarith

end Noperthedron.BalancedSupport

end
