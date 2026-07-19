module

public import Noperthedron.Bounding.OrthEquivRotz
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct

@[expose] public section


/-!
# Exact axis-angle decomposition

The local balanced-support argument needs an exact finite-rotation identity,
not an infinitesimal approximation.  We obtain it from the existing theorem
that every element of `SO(3)` is orthogonally conjugate to a rotation about
the z axis.
-/

namespace Noperthedron.BalancedSupport

open scoped Matrix Real RealInnerProductSpace

noncomputable def zFirst (v : ℝ³) : ℝ³ := !₂[-v 1, v 0, 0]

noncomputable def zRemainder (v : ℝ³) : ℝ³ := !₂[-v 0, -v 1, 0]

/-- Euclidean-space wrapper for the ordinary three-dimensional cross
product. -/
noncomputable def cross3 (v w : ℝ³) : ℝ³ :=
  WithLp.toLp 2 (v.ofLp ⨯₃ w.ofLp)

theorem cross3_norm_le (v w : ℝ³) : ‖cross3 v w‖ ≤ ‖v‖ * ‖w‖ := by
  rw [cross3, InnerProductGeometry.norm_ofLp_crossProduct]
  exact (mul_le_mul_of_nonneg_left (Real.sin_le_one _)
    (mul_nonneg (norm_nonneg v) (norm_nonneg w))).trans_eq (mul_one _)

theorem cross3_sub_right (u v w : ℝ³) :
    cross3 u (v - w) = cross3 u v - cross3 u w := by
  ext i
  fin_cases i <;> simp [cross3, cross_apply] <;> ring

/-- The standard unit z vector. -/
noncomputable def zAxis : ℝ³ := !₂[0, 0, 1]

theorem zFirst_eq_cross3 (v : ℝ³) : zFirst v = cross3 zAxis v := by
  ext i
  fin_cases i <;> simp [zFirst, cross3, zAxis, cross_apply]

def vecRows (x y z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![x, y, z]

theorem inner_cross3_eq_det (u v w : ℝ³) :
    ⟪u, cross3 v w⟫ = Matrix.det (vecRows u.ofLp v.ofLp w.ofLp) := by
  rw [cross3, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  rw [dotProduct_comm]
  simpa [vecRows] using triple_product_eq_det u.ofLp v.ofLp w.ofLp

private theorem vecRows_mul_transpose
    (M : Matrix (Fin 3) (Fin 3) ℝ) (x y z : Fin 3 → ℝ) :
    vecRows (M *ᵥ x) (M *ᵥ y) (M *ᵥ z) =
      vecRows x y z * M.transpose := by
  ext i j
  fin_cases i <;>
    simp [vecRows, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      mul_comm]

private theorem det_vecRows_map
    (M : Matrix (Fin 3) (Fin 3) ℝ)
    (x y z : Fin 3 → ℝ) :
    Matrix.det (vecRows (M *ᵥ x) (M *ᵥ y) (M *ᵥ z)) =
      Matrix.det (vecRows x y z) * M.det := by
  rw [vecRows_mul_transpose, Matrix.det_mul, Matrix.det_transpose]

private theorem det_vecRows_cycle (x y z : Fin 3 → ℝ) :
    Matrix.det (vecRows x y z) = Matrix.det (vecRows y z x) := by
  simp only [vecRows]
  rw [← triple_product_eq_det, ← triple_product_eq_det]
  exact triple_product_permutation x y z

/-- Orientation-preserving orthonormal frames carry the standard infinitesimal
z rotation to cross product with their z axis. -/
theorem oriented_frame_first_inner
    (frame : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (inverseMatrix : Matrix (Fin 3) (Fin 3) ℝ)
    (hinverse : ∀ x : ℝ³,
      (frame.symm x).ofLp = inverseMatrix *ᵥ x.ofLp)
    (v d : ℝ³) :
    ⟪d, frame (zFirst (frame.symm v))⟫ =
      inverseMatrix.det * ⟪frame zAxis, cross3 v d⟫ := by
  have hz : zAxis.ofLp = inverseMatrix *ᵥ (frame zAxis).ofLp := by
    simpa using hinverse (frame zAxis)
  calc
    ⟪d, frame (zFirst (frame.symm v))⟫ =
        ⟪frame.symm d, zFirst (frame.symm v)⟫ := by
      simpa using frame.inner_map_map (frame.symm d) (zFirst (frame.symm v))
    _ = Matrix.det (vecRows (frame.symm d).ofLp zAxis.ofLp
          (frame.symm v).ofLp) := by
      rw [zFirst_eq_cross3, inner_cross3_eq_det]
    _ = Matrix.det (vecRows (inverseMatrix *ᵥ d.ofLp)
          (inverseMatrix *ᵥ (frame zAxis).ofLp)
          (inverseMatrix *ᵥ v.ofLp)) := by rw [hinverse d, hz, hinverse v]
    _ = Matrix.det (vecRows d.ofLp (frame zAxis).ofLp v.ofLp) *
        inverseMatrix.det := det_vecRows_map inverseMatrix _ _ _
    _ = inverseMatrix.det *
        Matrix.det (vecRows (frame zAxis).ofLp v.ofLp d.ofLp) := by
      rw [det_vecRows_cycle]
      ring
    _ = inverseMatrix.det * ⟪frame zAxis, cross3 v d⟫ := by
      rw [inner_cross3_eq_det]

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
  axis : ℝ³
  axis_norm : ‖axis‖ = 1
  first_inner : ∀ v d,
    ⟪d, frame (zFirst (frame.symm v))⟫ = ⟪axis, cross3 v d⟫
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

theorem AxisAngle.first_inner_eq {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (v d : ℝ³) :
    ⟪d, a.first v⟫ = ⟪a.axis, cross3 v d⟫ := by
  exact a.first_inner v d

/-- Orient the axis so that the coefficient of its first variation is
`|sin angle|`, independently of the sign convention for the angle. -/
noncomputable def AxisAngle.signedAxis {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) : ℝ³ :=
  if 0 ≤ Real.sin a.angle then a.axis else -a.axis

theorem AxisAngle.signedAxis_norm {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) : ‖a.signedAxis‖ = 1 := by
  by_cases h : 0 ≤ Real.sin a.angle
  · simp [AxisAngle.signedAxis, h, a.axis_norm]
  · simp [AxisAngle.signedAxis, h, a.axis_norm]

theorem AxisAngle.sin_mul_first_inner {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (v d : ℝ³) :
    Real.sin a.angle * ⟪d, a.first v⟫ =
      |Real.sin a.angle| * ⟪a.signedAxis, cross3 v d⟫ := by
  rw [a.first_inner_eq]
  by_cases h : 0 ≤ Real.sin a.angle
  · simp [AxisAngle.signedAxis, h, abs_of_nonneg h]
  · have h' : Real.sin a.angle < 0 := lt_of_not_ge h
    rw [AxisAngle.signedAxis, if_neg h, abs_of_neg h']
    simp only [inner_neg_left]
    ring

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

/-- Operator-norm distance from the identity determines the half-angle. -/
theorem AxisAngle.norm_sub_id {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) :
    ‖Q - 1‖ = 2 * |Real.sin (a.angle / 2)| := by
  have hconj : Q - 1 =
      a.frame.toLinearIsometry.toContinuousLinearMap ∘L (RzL a.angle - 1) ∘L
        a.frame.symm.toLinearIsometry.toContinuousLinearMap := by
    ext x
    have hrot := congrArg (fun f : ℝ³ →L[ℝ] ℝ³ => f x) a.rotation_eq
    simp only [ContinuousLinearMap.comp_apply] at hrot
    simp only [sub_apply, one_apply_eq_self,
      ContinuousLinearMap.comp_apply]
    rw [hrot]
    simp
  rw [hconj, LinearIsometry.norm_toContinuousLinearMap_comp]
  refine (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ a.frame.symm).trans ?_
  rw [← RzC_coe]
  have hdist := Bounding.dist_rot3 (d := 2) (α := a.angle) (α' := 0)
  simpa only [rot3, AddChar.map_zero_eq_one, sub_zero] using hdist

/-- A squared operator-norm test implies the bend/first coefficient ratio
needed by the axis-free finite-rotation theorem.  This form has no division
and is convenient for rational interval certificates. -/
theorem AxisAngle.ratio_of_norm_sq {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (c : ℝ) (hc : 0 ≤ c)
    (hsmall : ‖Q - 1‖ ^ 2 * (1 + c ^ 2) ≤ 4 * c ^ 2) :
    1 - Real.cos a.angle ≤ |Real.sin a.angle| * c := by
  let sh := Real.sin (a.angle / 2)
  let ch := Real.cos (a.angle / 2)
  have hnormsq : ‖Q - 1‖ ^ 2 = 4 * sh ^ 2 := by
    rw [a.norm_sub_id, mul_pow, sq_abs]
    ring
  have hcircle : sh ^ 2 + ch ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (a.angle / 2)
  have hsquare : sh ^ 2 ≤ c ^ 2 * ch ^ 2 := by
    nlinarith
  have habs : |sh| ≤ c * |ch| := by
    rw [← sq_le_sq₀ (abs_nonneg sh) (mul_nonneg hc (abs_nonneg ch))]
    rw [sq_abs, mul_pow, sq_abs]
    exact hsquare
  have hmul := mul_le_mul_of_nonneg_left habs
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg sh))
  have hbend : 1 - Real.cos a.angle = 2 * sh ^ 2 := by
    dsimp [sh]
    rw [Real.sin_sq, Real.cos_sq]
    ring_nf
  have hsin : Real.sin a.angle = 2 * sh * ch := by
    dsimp [sh, ch]
    conv_lhs => rw [show a.angle = 2 * (a.angle / 2) by ring]
    rw [Real.sin_two_mul]
  rw [hbend, hsin, abs_mul, abs_mul]
  norm_num at hmul ⊢
  nlinarith [sq_abs sh]

theorem AxisAngle.ratio_of_norm_bound {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (c r : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hnorm : ‖Q - 1‖ ≤ r)
    (hsmall : r ^ 2 * (1 + c ^ 2) ≤ 4 * c ^ 2) :
    1 - Real.cos a.angle ≤ |Real.sin a.angle| * c := by
  apply a.ratio_of_norm_sq c hc
  have hsq : ‖Q - 1‖ ^ 2 ≤ r ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) hr).2 hnorm
  exact (mul_le_mul_of_nonneg_right hsq (by positivity)).trans hsmall

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
  let ug : Matrix.orthogonalGroup (Fin 3) ℝ := ⟨U, hU⟩
  have hUinv_orth : U⁻¹ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    have hinv : (↑ug⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) * U = 1 := by
      simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using
        congrArg Subtype.val (inv_mul_cancel ug)
    rw [Matrix.inv_eq_left_inv hinv]
    exact ug⁻¹.property
  have hdet_sq : (U⁻¹).det ^ 2 = 1 := by
    rw [Matrix.mem_orthogonalGroup_iff] at hUinv_orth
    have horth := hUinv_orth
    have hdet := congrArg Matrix.det horth
    simpa [Matrix.det_mul, Matrix.det_transpose, pow_two] using hdet
  have hdet_abs : |(U⁻¹).det| = 1 := by
    rcases (sq_eq_one_iff.mp hdet_sq) with h | h <;> simp [h]
  have haxis : ‖(U⁻¹).det • u zAxis‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hdet_abs, one_mul, u.norm_map,
      EuclideanSpace.norm_eq]
    simp [zAxis, Fin.sum_univ_three]
  refine ⟨⟨u, (U⁻¹).det • u zAxis, haxis,
    (fun v d => by
      rw [real_inner_smul_left]
      exact oriented_frame_first_inner u U⁻¹ hu_symm v d),
    s, hs, ?_⟩⟩
  rw [hconj, toCLM_mul, toCLM_mul, hUclm, hUinvclm, RzL,
    ContinuousLinearMap.comp_assoc]

end Noperthedron.BalancedSupport

end
