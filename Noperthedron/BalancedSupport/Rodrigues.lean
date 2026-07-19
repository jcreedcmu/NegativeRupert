module

public import Noperthedron.Bounding.OrthEquivRotz

@[expose] public section


/-!
# Exact axis-angle decomposition

The local balanced-support argument needs an exact finite-rotation identity,
not an infinitesimal approximation.  We obtain it from the existing theorem
that every element of `SO(3)` is orthogonally conjugate to a rotation about
the z axis.
-/

namespace Noperthedron.BalancedSupport

open scoped Matrix Real

noncomputable def zFirst (v : ℝ³) : ℝ³ := !₂[-v 1, v 0, 0]

noncomputable def zRemainder (v : ℝ³) : ℝ³ := !₂[-v 0, -v 1, 0]

theorem Rz_apply_sub_exact (s : ℝ) (v : ℝ³) :
    RzL s v - v = (Real.sin s) • zFirst v + (1 - Real.cos s) • zRemainder v := by
  ext i
  fin_cases i <;>
    simp [RzL, Rz_mat, zFirst, zRemainder, Matrix.vecHead, Matrix.vecTail] <;>
    ring

theorem zRemainder_norm_le (v : ℝ³) : ‖zRemainder v‖ ≤ ‖v‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp [zRemainder]
  nlinarith [sq_nonneg (v 2)]

theorem zFirst_norm_eq_zRemainder (v : ℝ³) :
    ‖zFirst v‖ = ‖zRemainder v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three, zFirst, zRemainder]
  ring

/-- An axis-angle presentation of a three-dimensional rotation.  The axis is
encoded by the orthonormal frame taking the standard z axis to that axis. -/
structure AxisAngle (Q : ℝ³ →L[ℝ] ℝ³) where
  frame : ℝ³ ≃ₗᵢ[ℝ] ℝ³
  angle : ℝ
  angle_mem : angle ∈ Set.Ioc (-Real.pi) Real.pi
  rotation_eq : Q =
    frame.toLinearIsometry.toContinuousLinearMap ∘L RzL angle ∘L
      frame.symm.toLinearIsometry.toContinuousLinearMap

noncomputable def AxisAngle.first {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (v : ℝ³) : ℝ³ :=
  a.frame (zFirst (a.frame.symm v))

noncomputable def AxisAngle.remainder {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (v : ℝ³) : ℝ³ :=
  a.frame (zRemainder (a.frame.symm v))

theorem AxisAngle.apply_sub_exact {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (v : ℝ³) :
    Q v - v = (Real.sin a.angle) • a.first v +
      (1 - Real.cos a.angle) • a.remainder v := by
  have hQ : Q v = a.frame (RzL a.angle (a.frame.symm v)) := by
    have h := congrArg (fun f : ℝ³ →L[ℝ] ℝ³ => f v) a.rotation_eq
    change Q v = a.frame.toLinearIsometry.toContinuousLinearMap
      (RzL a.angle (a.frame.symm.toLinearIsometry.toContinuousLinearMap v))
    simpa only [ContinuousLinearMap.comp_apply] using h
  rw [hQ]
  simp only [AxisAngle.first, AxisAngle.remainder]
  have hz := Rz_apply_sub_exact a.angle (a.frame.symm v)
  calc
    a.frame (RzL a.angle (a.frame.symm v)) - v =
        a.frame (RzL a.angle (a.frame.symm v) - a.frame.symm v) := by
      rw [map_sub, LinearIsometryEquiv.apply_symm_apply]
    _ = a.frame ((Real.sin a.angle) • zFirst (a.frame.symm v) +
        (1 - Real.cos a.angle) • zRemainder (a.frame.symm v)) := by rw [hz]
    _ = (Real.sin a.angle) • a.frame (zFirst (a.frame.symm v)) +
        (1 - Real.cos a.angle) • a.frame (zRemainder (a.frame.symm v)) := by
      rw [map_add, map_smul, map_smul]

theorem AxisAngle.remainder_norm_le {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (v : ℝ³) : ‖a.remainder v‖ ≤ ‖v‖ := by
  rw [AxisAngle.remainder, a.frame.norm_map]
  exact (zRemainder_norm_le _).trans_eq (a.frame.symm.norm_map v)

theorem AxisAngle.first_norm_le {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (v : ℝ³) : ‖a.first v‖ ≤ ‖v‖ := by
  rw [AxisAngle.first, a.frame.norm_map, zFirst_norm_eq_zRemainder]
  exact (zRemainder_norm_le _).trans_eq (a.frame.symm.norm_map v)

/-- Every special orthogonal matrix has an exact `AxisAngle` presentation
with angle in `(-π,π]`. -/
theorem exists_axisAngle (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Nonempty (AxisAngle A.toEuclideanLin.toContinuousLinearMap) := by
  obtain ⟨U, hU, s, hs, hconj⟩ := Bounding.SO3_is_conj_Rz_within_pi A hA
  let u : ℝ³ ≃ₗᵢ[ℝ] ℝ³ := Bounding.OrthogonalGroup.toLinearIsometryEquiv ⟨U, hU⟩
  have hu : ∀ x : ℝ³, (u x).ofLp = U *ᵥ x.ofLp :=
    Bounding.OrthogonalGroup.toLinearIsometryEquiv_apply ⟨U, hU⟩
  have hUdet : IsUnit U.det := Matrix.isUnit_det_of_left_inverse hU.1
  have hu_symm : ∀ x : ℝ³, (u.symm x).ofLp = U⁻¹ *ᵥ x.ofLp := fun x => by
    have h := hu (u.symm x)
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    rw [h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hUdet, Matrix.one_mulVec]
  have toCLM_mul : ∀ B C : Matrix (Fin 3) (Fin 3) ℝ,
      (B * C).toEuclideanLin.toContinuousLinearMap =
        B.toEuclideanLin.toContinuousLinearMap ∘L C.toEuclideanLin.toContinuousLinearMap := by
    intro B C
    ext v
    simp
  have hUclm : u.toLinearIsometry.toContinuousLinearMap =
      U.toEuclideanLin.toContinuousLinearMap := by
    ext x
    simp [hu]
  have hUinvclm : u.symm.toLinearIsometry.toContinuousLinearMap =
      U⁻¹.toEuclideanLin.toContinuousLinearMap := by
    ext x
    simp [hu_symm]
  refine ⟨⟨u, s, hs, ?_⟩⟩
  rw [hconj, toCLM_mul, toCLM_mul, hUclm, hUinvclm, RzL,
    ContinuousLinearMap.comp_assoc]

end Noperthedron.BalancedSupport

end
