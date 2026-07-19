module

public import Mathlib.LinearAlgebra.Trace
public import Noperthedron.BalancedSupport.Rodrigues
public import Noperthedron.Bounding.SmallConsecutiveRotations

@[expose] public section


/-!
# Cayley coordinates for three-dimensional rotations

The vector `(x, y, z)` represents the unit quaternion proportional to
`(1, x, y, z)`.  Unlike Euler coordinates, the resulting rotation matrix is
rational in the three parameters.  These coordinates cover exactly the
rotations without angle `pi`; in particular they cover every rotation whose
trace is nonnegative.
-/

namespace Noperthedron

open scoped Matrix RealInnerProductSpace

open BalancedSupport

/-- The positive denominator in the three-dimensional Cayley transform. -/
def cayleyDenom (x y z : ℝ) : ℝ := 1 + x ^ 2 + y ^ 2 + z ^ 2

theorem cayleyDenom_pos (x y z : ℝ) : 0 < cayleyDenom x y z := by
  unfold cayleyDenom
  positivity

theorem cayleyDenom_ne (x y z : ℝ) : cayleyDenom x y z ≠ 0 :=
  ne_of_gt (cayleyDenom_pos x y z)

/-- Polynomial numerator of the Cayley rotation, defined over any
commutative ring so rational certificate evaluation uses the same formula. -/
def cayleyNumeratorMatrix {R : Type} [CommRing R]
    (x y z : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1 + x * x - y * y - z * z,
      2 * (x * y - z),
      2 * (x * z + y);
     2 * (x * y + z),
      1 - x * x + y * y - z * z,
      2 * (y * z - x);
     2 * (x * z - y),
      2 * (y * z + x),
      1 - x * x - y * y + z * z]

/-- The rational rotation matrix with Cayley vector `(x, y, z)`. -/
noncomputable def cayleyMatrix (x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let d := cayleyDenom x y z
  !![(1 + x ^ 2 - y ^ 2 - z ^ 2) / d,
      2 * (x * y - z) / d,
      2 * (x * z + y) / d;
     2 * (x * y + z) / d,
      (1 - x ^ 2 + y ^ 2 - z ^ 2) / d,
      2 * (y * z - x) / d;
     2 * (x * z - y) / d,
     2 * (y * z + x) / d,
      (1 - x ^ 2 - y ^ 2 + z ^ 2) / d]

theorem cayleyMatrix_eq_div_numerator (x y z : ℝ) :
    cayleyMatrix x y z = fun i j =>
      cayleyNumeratorMatrix x y z i j / cayleyDenom x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayleyMatrix, cayleyNumeratorMatrix, pow_two]

@[simp]
theorem cayleyMatrix_zero : cayleyMatrix 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cayleyMatrix, cayleyDenom]

/-- Cayley matrices are orientation-preserving orthogonal matrices. -/
theorem cayleyMatrix_mem_SO3 (x y z : ℝ) :
    cayleyMatrix x y z ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff,
    Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cayleyMatrix, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_three] <;>
      field_simp [cayleyDenom_ne] <;>
      simp only [cayleyDenom] <;> ring
  · simp [cayleyMatrix, Matrix.det_fin_three]
    field_simp [cayleyDenom_ne]
    simp only [cayleyDenom]
    ring

/-- The Cayley matrix bundled as an element of `SO(3)`. -/
noncomputable def cayleySO3 (x y z : ℝ) : SO3 :=
  ⟨cayleyMatrix x y z, cayleyMatrix_mem_SO3 x y z⟩

/-- The Euclidean vector represented by the three scalar coordinates. -/
noncomputable def cayleyVector (x y z : ℝ) : ℝ³ := !₂[x, y, z]

/-- Exact Rodrigues form of the Cayley transform. -/
theorem cayleyMatrix_apply_sub (x y z : ℝ) (v : ℝ³) :
    (cayleyMatrix x y z).toEuclideanLin v - v =
      (2 / cayleyDenom x y z) • cross3 (cayleyVector x y z) v +
      (2 / cayleyDenom x y z) •
        cross3 (cayleyVector x y z) (cross3 (cayleyVector x y z) v) := by
  ext i
  fin_cases i <;>
    simp [cayleyMatrix, cayleyVector, cayleyDenom, Matrix.toLpLin_apply,
      dotProduct, Fin.sum_univ_three, cross3, cross_apply] <;>
    field_simp <;> ring

theorem cross3_smul_left (c : ℝ) (u v : ℝ³) :
    cross3 (c • u) v = c • cross3 u v := by
  ext i
  fin_cases i <;> simp [cross3, cross_apply]

theorem cross3_smul_right (c : ℝ) (u v : ℝ³) :
    cross3 u (c • v) = c • cross3 u v := by
  ext i
  fin_cases i <;> simp [cross3, cross_apply]

/-- Cayley rotation about a unit axis, written in Rodrigues form. -/
theorem cayleyMatrix_smul_unit_apply_sub
    (c : ℝ) (axis v : ℝ³) (haxis : ‖axis‖ = 1) :
    (cayleyMatrix (c * axis 0) (c * axis 1) (c * axis 2)).toEuclideanLin v - v =
      (2 * c / (1 + c ^ 2)) • cross3 axis v +
      (2 * c ^ 2 / (1 + c ^ 2)) • cross3 axis (cross3 axis v) := by
  have haxisSq : axis 0 ^ 2 + axis 1 ^ 2 + axis 2 ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) haxis
    simpa [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three] using h
  have hvec :
      cayleyVector (c * axis 0) (c * axis 1) (c * axis 2) = c • axis := by
    ext i
    fin_cases i <;> simp [cayleyVector]
  have hdenom :
      cayleyDenom (c * axis 0) (c * axis 1) (c * axis 2) = 1 + c ^ 2 := by
    unfold cayleyDenom
    nlinarith
  rw [cayleyMatrix_apply_sub, hvec, hdenom,
    cross3_smul_left, cross3_smul_left, cross3_smul_right]
  simp only [smul_smul]
  module

/-- Trace is a rational function of the squared Cayley radius. -/
theorem trace_cayleyMatrix (x y z : ℝ) :
    Matrix.trace (cayleyMatrix x y z) =
      (3 - (x ^ 2 + y ^ 2 + z ^ 2)) / cayleyDenom x y z := by
  simp [Matrix.trace, cayleyMatrix, Fin.sum_univ_three]
  field_simp [cayleyDenom_ne]
  ring

namespace BalancedSupport

theorem inner_cross3_cycle (d u v : ℝ³) :
    ⟪d, cross3 u v⟫ = ⟪u, cross3 v d⟫ := by
  rw [inner_cross3_eq_det, inner_cross3_eq_det]
  simp only [vecRows]
  rw [← triple_product_eq_det, ← triple_product_eq_det]
  exact triple_product_permutation d.ofLp u.ofLp v.ofLp

theorem AxisAngle.first_eq_cross3 {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (v : ℝ³) :
    a.first v = cross3 a.axis v := by
  apply ext_inner_left ℝ
  intro d
  rw [a.first_inner_eq]
  exact (inner_cross3_cycle d a.axis v).symm

private theorem zFirst_zFirst (v : ℝ³) :
    zFirst (zFirst v) = zRemainder v := by
  ext i
  fin_cases i <;> simp [zFirst, zRemainder]

theorem AxisAngle.first_first {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (v : ℝ³) :
    a.first (a.first v) = a.remainder v := by
  simp only [AxisAngle.first, AxisAngle.remainder,
    LinearIsometryEquiv.symm_apply_apply, zFirst_zFirst]

theorem AxisAngle.remainder_eq_cross3_cross3 {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (v : ℝ³) :
    a.remainder v = cross3 a.axis (cross3 a.axis v) := by
  rw [← a.first_first, a.first_eq_cross3, a.first_eq_cross3]

/-- Linear trace recovers the cosine of any axis-angle presentation. -/
theorem AxisAngle.linear_trace_eq {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) :
    LinearMap.trace ℝ ℝ³ Q = 1 + 2 * Real.cos a.angle := by
  calc
    LinearMap.trace ℝ ℝ³ Q = LinearMap.trace ℝ ℝ³
        (a.frame.toLinearIsometry.toContinuousLinearMap ∘L RzL a.angle ∘L
          a.frame.symm.toLinearIsometry.toContinuousLinearMap) := by
      exact congrArg
        (fun f : ℝ³ →L[ℝ] ℝ³ => LinearMap.trace ℝ ℝ³ f)
        a.rotation_eq
    _ = LinearMap.trace ℝ ℝ³ (RzL a.angle) := by
      exact LinearMap.trace_conj'
        (RzL a.angle : ℝ³ →ₗ[ℝ] ℝ³) a.frame.toLinearEquiv
    _ = 1 + 2 * Real.cos a.angle := Bounding.tr_RzL

/-- Matrix trace recovers the cosine of an axis-angle presentation. -/
theorem AxisAngle.matrix_trace_eq
    {A : Matrix (Fin 3) (Fin 3) ℝ}
    (a : AxisAngle A.toEuclideanLin.toContinuousLinearMap) :
    Matrix.trace A = 1 + 2 * Real.cos a.angle := by
  calc
    Matrix.trace A = LinearMap.trace ℝ ℝ³ A.toEuclideanLin := by
      simp only [Matrix.toLpLin_eq_toLin, Matrix.trace_toLin_eq]
    _ = LinearMap.trace ℝ ℝ³
        A.toEuclideanLin.toContinuousLinearMap := by
      congr 1
    _ = 1 + 2 * Real.cos a.angle := a.linear_trace_eq

end BalancedSupport

/-- Every special orthogonal matrix of nonnegative trace has a Cayley vector
of squared radius at most three.  This is the closed, bounded chart needed by
the snub-cube max-trace fundamental domain. -/
theorem exists_cayleyMatrix_of_trace_nonneg
    (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (htrace : 0 ≤ Matrix.trace A) :
    ∃ x y z : ℝ,
      x ^ 2 + y ^ 2 + z ^ 2 ≤ 3 ∧ A = cayleyMatrix x y z := by
  obtain ⟨a⟩ := BalancedSupport.exists_axisAngle A hA
  let co := Real.cos a.angle
  let si := Real.sin a.angle
  let c := si / (1 + co)
  have hcos : -(1 / 2 : ℝ) ≤ co := by
    dsimp only [co]
    linarith [a.matrix_trace_eq]
  have hdenomPos : 0 < 1 + co := by linarith
  have hcircle : si ^ 2 + co ^ 2 = 1 := by
    dsimp only [si, co]
    exact Real.sin_sq_add_cos_sq a.angle
  have hhalfDenom : (1 + co) ^ 2 + si ^ 2 = 2 * (1 + co) := by
    nlinarith
  have hcSqMul : c ^ 2 * (1 + co) = 1 - co := by
    dsimp only [c]
    field_simp [ne_of_gt hdenomPos]
    nlinarith
  have hcSq : c ^ 2 ≤ 3 := by
    nlinarith
  have hcFirst : 2 * c / (1 + c ^ 2) = si := by
    dsimp only [c]
    field_simp [ne_of_gt hdenomPos]
    rw [hhalfDenom]
    ring
  have hcRemainder : 2 * c ^ 2 / (1 + c ^ 2) = 1 - co := by
    dsimp only [c]
    field_simp [ne_of_gt hdenomPos]
    nlinarith
  let x := c * a.axis 0
  let y := c * a.axis 1
  let z := c * a.axis 2
  have haxisSq : a.axis 0 ^ 2 + a.axis 1 ^ 2 + a.axis 2 ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) a.axis_norm
    simpa [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three] using h
  have hxyz : x ^ 2 + y ^ 2 + z ^ 2 = c ^ 2 := by
    dsimp only [x, y, z]
    nlinarith
  refine ⟨x, y, z, hxyz.le.trans hcSq, ?_⟩
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro v
  have hcay := cayleyMatrix_smul_unit_apply_sub c a.axis v a.axis_norm
  have hrot := a.apply_sub_exact v
  dsimp only [x, y, z]
  rw [hcFirst, hcRemainder, ← a.remainder_eq_cross3_cross3,
    ← a.first_eq_cross3] at hcay
  dsimp only [si, co] at hcay
  have hsub :
      (cayleyMatrix (c * a.axis 0) (c * a.axis 1)
        (c * a.axis 2)).toEuclideanLin v - v = A.toEuclideanLin v - v :=
    hcay.trans hrot.symm
  exact (sub_left_inj.mp hsub).symm

/-- For a Cayley rotation, the finite bend/first coefficient ratio is exactly
the Euclidean norm of the Cayley vector.  This removes all relative-rotation
Taylor error from local certificates. -/
public theorem BalancedSupport.AxisAngle.cayley_ratio_eq_of_rotation_eq
    {Q : ℝ³ →L[ℝ] ℝ³} (a : BalancedSupport.AxisAngle Q)
    (x y z : ℝ)
    (hQ : Q = (cayleyMatrix x y z).toEuclideanLin.toContinuousLinearMap) :
    1 - Real.cos a.angle =
      |Real.sin a.angle| * Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := by
  let s := x ^ 2 + y ^ 2 + z ^ 2
  have hs : 0 ≤ s := by
    dsimp only [s]
    positivity
  have hdenom : cayleyDenom x y z = 1 + s := by
    dsimp only [s]
    unfold cayleyDenom
    ring
  have hdenomPos : 0 < cayleyDenom x y z := cayleyDenom_pos x y z
  have hcos : Real.cos a.angle = (1 - s) / cayleyDenom x y z := by
    have htrace : Matrix.trace (cayleyMatrix x y z) =
        1 + 2 * Real.cos a.angle := by
      calc
        Matrix.trace (cayleyMatrix x y z) = LinearMap.trace ℝ ℝ³
            (cayleyMatrix x y z).toEuclideanLin := by
          simp only [Matrix.toLpLin_eq_toLin, Matrix.trace_toLin_eq]
        _ = LinearMap.trace ℝ ℝ³
            (cayleyMatrix x y z).toEuclideanLin.toContinuousLinearMap := by
          congr 1
        _ = LinearMap.trace ℝ ℝ³ Q := by rw [hQ]
        _ = 1 + 2 * Real.cos a.angle := a.linear_trace_eq
    rw [trace_cayleyMatrix] at htrace
    rw [show x ^ 2 + y ^ 2 + z ^ 2 = s by rfl] at htrace
    field_simp [cayleyDenom_ne] at htrace ⊢
    rw [hdenom] at htrace ⊢
    nlinarith
  have hsinSq :
      Real.sin a.angle ^ 2 * cayleyDenom x y z ^ 2 = 4 * s := by
    have hcircle := Real.sin_sq_add_cos_sq a.angle
    rw [hcos] at hcircle
    field_simp [cayleyDenom_ne] at hcircle
    rw [hdenom] at hcircle ⊢
    nlinarith
  have hsqrtSq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
  have hsinAbs :
      |Real.sin a.angle| =
        2 * Real.sqrt s / cayleyDenom x y z := by
    have hrhs : 0 ≤ 2 * Real.sqrt s / cayleyDenom x y z :=
      div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        hdenomPos.le
    rw [← sq_eq_sq₀ (abs_nonneg _) hrhs, sq_abs, div_pow, mul_pow,
      hsqrtSq]
    field_simp [cayleyDenom_ne]
    nlinarith
  change 1 - Real.cos a.angle = |Real.sin a.angle| * Real.sqrt s
  rw [hcos, hsinAbs]
  field_simp [cayleyDenom_ne]
  rw [hsqrtSq, hdenom]
  ring

public theorem BalancedSupport.AxisAngle.cayley_ratio_eq
    (x y z : ℝ)
    (a : BalancedSupport.AxisAngle
      (cayleyMatrix x y z).toEuclideanLin.toContinuousLinearMap) :
    1 - Real.cos a.angle =
      |Real.sin a.angle| * Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) :=
  a.cayley_ratio_eq_of_rotation_eq x y z rfl

end Noperthedron

end
