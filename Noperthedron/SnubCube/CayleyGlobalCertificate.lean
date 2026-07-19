module

public import Noperthedron.SnubCube.CayleyFundamentalPrune
public import Noperthedron.SnubCube.CayleyLocalCertificate

@[expose] public section


/-!
# Polynomial balanced-support certificates for Cayley boxes

Multiplication by the positive Cayley denominator turns each projected
inner-minus-outer displacement into a quadratic polynomial in `(x,y,z)`.
The outer viewing matrix is frozen at the rational box center; a uniform
operator-norm budget accounts for its two angle coordinates and for the
rational vertex approximations.
-/

namespace Noperthedron.SnubCube.CayleyGlobalCertificate

open scoped Matrix RealInnerProductSpace
open Noperthedron.Checker
open RationalApprox GlobalTheorem

abbrev Polynomial := RatPolynomial 3

structure Contact where
  innerIndex : VertexIndex
  outerIndex : VertexIndex
  direction : Fin 2 → ℚ
deriving DecidableEq, Repr

structure Box where
  interval : CayleyInterval ℚ
  contact : Fin 3 → Contact
deriving DecidableEq

def Box.center (box : Box) : CayleyPose ℚ where
  θ := (box.interval.coordinateBall 0).center
  φ := (box.interval.coordinateBall 1).center
  x := (box.interval.coordinateBall 2).center
  y := (box.interval.coordinateBall 3).center
  z := (box.interval.coordinateBall 4).center

abbrev Box.εθ (box : Box) : ℚ := (box.interval.coordinateBall 0).radius
abbrev Box.εφ (box : Box) : ℚ := (box.interval.coordinateBall 1).radius

theorem Box.εθ_nonneg (box : Box) : 0 ≤ box.εθ := by
  change 0 ≤ (box.interval.max.θ - box.interval.min.θ) / 2
  exact div_nonneg
    (sub_nonneg.mpr ((CayleyPose.le_iff _ _).mp box.interval.min_le_max).1)
    (by norm_num)

theorem Box.εφ_nonneg (box : Box) : 0 ≤ box.εφ := by
  change 0 ≤ (box.interval.max.φ - box.interval.min.φ) / 2
  exact div_nonneg
    (sub_nonneg.mpr ((CayleyPose.le_iff _ _).mp box.interval.min_le_max).2.1)
    (by norm_num)

def Contact.outerContact (contact : Contact) : LocalCertificate.Contact where
  index := contact.outerIndex
  direction := contact.direction

/-- A shell used to reuse interval and outer-support lemmas.  Its certificate
payload and local-radius fields are immaterial. -/
def Box.localShell (box : Box) : CayleyLocalCertificate.Box := {
    interval := box.interval
    certificate := fun _ => {
      contact := fun _ => (box.contact 0).outerContact }
    c := 0
    r := 0
  }

def Box.supportBox (box : Box) : LocalCertificate.Box := box.localShell.eulerBox

def Box.weight (box : Box) : Fin 3 → ℚ :=
  ![LocalCertificate.det2 (box.contact 1).direction (box.contact 2).direction,
    LocalCertificate.det2 (box.contact 2).direction (box.contact 0).direction,
    LocalCertificate.det2 (box.contact 0).direction (box.contact 1).direction]

def Box.totalWeight (box : Box) : ℚ := ∑ i, box.weight i

def Box.balanced (box : Box) : Prop :=
  ∑ i, box.weight i • (box.contact i).direction = 0

instance (box : Box) : Decidable box.balanced := by
  unfold Box.balanced
  infer_instance

def denomPolynomial : Polynomial :=
  1 + CayleyFundamentalPrune.px * CayleyFundamentalPrune.px +
    CayleyFundamentalPrune.py * CayleyFundamentalPrune.py +
    CayleyFundamentalPrune.pz * CayleyFundamentalPrune.pz

def sum2 (f : Fin 2 → Polynomial) : Polynomial := f 0 + f 1

def Box.centerMatrix (box : Box) : Matrix (Fin 2) (Fin 3) ℚ :=
  RationalApprox.rotMℚ_mat box.center.θ box.center.φ

def Box.liftCoefficient (box : Box) (contact : Contact) (j : Fin 3) : ℚ :=
  ∑ i, contact.direction i * box.centerMatrix i j

/-- Quadratic numerator of one contact's projected displacement. -/
def Box.contactPolynomial (box : Box) (contact : Contact) : Polynomial :=
  CayleyFundamentalPrune.sum3 fun i =>
    RatPolynomial.scale (box.liftCoefficient contact i)
      (CayleyFundamentalPrune.sum3 (fun j =>
          RatPolynomial.scale (normalizedRationalVertex contact.innerIndex j)
            (CayleyFundamentalPrune.numeratorPolynomial i j)) -
        RatPolynomial.scale (normalizedRationalVertex contact.outerIndex i)
          denomPolynomial)

def Box.displacementPolynomial (box : Box) : Polynomial :=
  CayleyFundamentalPrune.sum3 fun i =>
    RatPolynomial.scale (box.weight i) (box.contactPolynomial (box.contact i))

def Box.variableBalls (box : Box) : Fin 3 → RatBall :=
  ![box.interval.coordinateBall 2,
    box.interval.coordinateBall 3,
    box.interval.coordinateBall 4]

def Box.displacementBall (box : Box) : RatBall :=
  RatPolynomial.evalBall box.variableBalls box.displacementPolynomial

/-- Upper bound for the positive Cayley denominator throughout the box. -/
def Box.dBound (box : Box) : ℚ :=
  1 + CayleyLocalCertificate.endpointAbsBound
      box.interval.min.x box.interval.max.x ^ 2 +
    CayleyLocalCertificate.endpointAbsBound
      box.interval.min.y box.interval.max.y ^ 2 +
    CayleyLocalCertificate.endpointAbsBound
      box.interval.min.z box.interval.max.z ^ 2

def Box.viewError (box : Box) : ℚ := box.εθ + box.εφ + κℚ

theorem Box.viewError_nonneg (box : Box) : 0 ≤ box.viewError := by
  unfold Box.viewError
  exact add_nonneg (add_nonneg box.εθ_nonneg box.εφ_nonneg) (by
    norm_num [RationalApprox.κℚ])

/-- Error for one unit-direction contact after multiplying by the Cayley
denominator. -/
def Box.contactError (box : Box) : ℚ :=
  2 * box.dBound * (κℚ + (1 + κℚ) * box.viewError)

def Box.error (box : Box) : ℚ := box.totalWeight * box.contactError

noncomputable def Box.approxVector (box : Box) (contact : Contact)
    (x y z : ℝ) : ℝ³ :=
  (cayleyNumeratorMatrix x y z).toEuclideanLin
      (toR3 (normalizedRationalVertex contact.innerIndex)) -
    cayleyDenom x y z •
      toR3 (normalizedRationalVertex contact.outerIndex)

noncomputable def Box.exactVector (box : Box) (contact : Contact)
    (x y z : ℝ) : ℝ³ :=
  (cayleyNumeratorMatrix x y z).toEuclideanLin
      (normalizedExactVertex contact.innerIndex) -
    cayleyDenom x y z • normalizedExactVertex contact.outerIndex

noncomputable def Box.approxContactValue (box : Box) (contact : Contact)
    (x y z : ℝ) : ℝ :=
  ⟪toR2 contact.direction,
    ((box.centerMatrix.map fun q => (q : ℝ)).toEuclideanLin
      (box.approxVector contact x y z))⟫

theorem eval_denomPolynomial (x y z : ℝ) :
    RatPolynomial.evalReal ![x, y, z] denomPolynomial =
      cayleyDenom x y z := by
  norm_num [denomPolynomial, CayleyFundamentalPrune.px,
    CayleyFundamentalPrune.py, CayleyFundamentalPrune.pz,
    RatPolynomial.evalReal, cayleyDenom]
  simp
  ring

theorem Box.eval_contactPolynomial (box : Box) (contact : Contact)
    (x y z : ℝ) :
    RatPolynomial.evalReal ![x, y, z] (box.contactPolynomial contact) =
      box.approxContactValue contact x y z := by
  simp only [Box.contactPolynomial, CayleyFundamentalPrune.sum3,
    RatPolynomial.evalReal_add, RatPolynomial.evalReal_sub,
    RatPolynomial.evalReal_scale,
    CayleyFundamentalPrune.eval_numeratorPolynomial,
    eval_denomPolynomial]
  simp [Box.approxContactValue, Box.approxVector, Box.liftCoefficient,
    Box.centerMatrix, RationalApprox.rotMℚ_mat,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Fin.sum_univ_three, toR2, toR3,
    PiLp.inner_apply]
  ring

theorem Box.eval_displacementPolynomial (box : Box) (x y z : ℝ) :
    RatPolynomial.evalReal ![x, y, z] box.displacementPolynomial =
      ∑ i, (box.weight i : ℝ) *
        box.approxContactValue (box.contact i) x y z := by
  simp only [Box.displacementPolynomial, CayleyFundamentalPrune.sum3,
    RatPolynomial.evalReal_add, RatPolynomial.evalReal_scale,
    box.eval_contactPolynomial]
  push_cast
  simp [Fin.sum_univ_three]

theorem Box.denom_le_dBound (box : Box) {p : CayleyPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    cayleyDenom p.x p.y p.z ≤ (box.dBound : ℝ) := by
  have hs := box.localShell.sq_sum_le_radiusSq hp
  change 1 + p.x ^ 2 + p.y ^ 2 + p.z ^ 2 ≤ _
  simp only [Box.dBound]
  push_cast
  simp only [Box.localShell, CayleyLocalCertificate.Box.radiusSq] at hs
  push_cast at hs
  linarith

private theorem norm_rotM_sub_le (θ φ θ₀ φ₀ : ℝ) :
    ‖rotM θ φ - rotM θ₀ φ₀‖ ≤ |φ - φ₀| + |θ - θ₀| := by
  have hnonneg : 0 ≤ |φ - φ₀| + |θ - θ₀| := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hnonneg
  intro v
  have hrot := Noperthedron.BalancedSupport.norm_rotRM_sub_le
    θ φ 0 θ₀ φ₀ 0
  calc
    ‖(rotM θ φ - rotM θ₀ φ₀) v‖ =
        ‖proj_xyL ((rotRM θ φ 0 - rotRM θ₀ φ₀ 0) v)‖ := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
        map_sub, Pose.proj_rm_eq_m, Pose.proj_rm_eq_m]
    _ ≤ ‖(rotRM θ φ 0 - rotRM θ₀ φ₀ 0) v‖ :=
      Noperthedron.BalancedSupport.proj_xyL_norm_le _
    _ ≤ ‖rotRM θ φ 0 - rotRM θ₀ φ₀ 0‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (|φ - φ₀| + |θ - θ₀|) * ‖v‖ := by
      gcongr
      simpa using hrot

noncomputable def Box.centerCLM (box : Box) : ℝ³ →L[ℝ] ℝ² :=
  (box.centerMatrix.map fun q => (q : ℝ)).toEuclideanLin.toContinuousLinearMap

theorem Box.centerCLM_eq (box : Box) :
    box.centerCLM = RationalApprox.rotMℚℝ
      (box.center.θ : ℝ) (box.center.φ : ℝ) := by
  unfold Box.centerCLM Box.centerMatrix RationalApprox.rotMℚℝ
  rw [RationalApprox.rotMℚ_mat_castℝ]

theorem Box.norm_view_sub_centerCLM_le (box : Box)
    (hcenter : box.supportBox.center ∈ fourInterval ℚ)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal) :
    ‖rotM p.θ p.φ - box.centerCLM‖ ≤ (box.viewError : ℝ) := by
  have hθ := box.interval.coordinateBall_holds hp 0
  have hφ := box.interval.coordinateBall_holds hp 1
  have hθ' : |p.θ - (box.center.θ : ℝ)| ≤ (box.εθ : ℝ) := by
    simpa [RatBall.Holds, Box.center] using hθ
  have hφ' : |p.φ - (box.center.φ : ℝ)| ≤ (box.εφ : ℝ) := by
    simpa [RatBall.Holds, Box.center] using hφ
  have hfour := PoseInterval.contains_iff_components.mp hcenter
  have hθfourQ : box.center.θ ∈ Set.Icc (-4 : ℚ) 4 := by
    simpa [Box.supportBox, Box.localShell,
      CayleyLocalCertificate.Box.eulerBox,
      CayleyLocalCertificate.Box.eulerInterval,
      CayleyLocalCertificate.outerPose, Box.center,
      LocalCertificate.Box.center, CayleyInterval.coordinateBall,
      RatBall.ofEndpoints] using hfour.1
  have hφfourQ : box.center.φ ∈ Set.Icc (-4 : ℚ) 4 := by
    simpa [Box.supportBox, Box.localShell,
      CayleyLocalCertificate.Box.eulerBox,
      CayleyLocalCertificate.Box.eulerInterval,
      CayleyLocalCertificate.outerPose, Box.center,
      LocalCertificate.Box.center, CayleyInterval.coordinateBall,
      RatBall.ofEndpoints] using hfour.2.2.1
  have happ := RationalApprox.M_difference_norm_bounded
    (box.center.θ : ℝ) (box.center.φ : ℝ)
    (by exact ⟨by exact_mod_cast hθfourQ.1, by exact_mod_cast hθfourQ.2⟩)
    (by exact ⟨by exact_mod_cast hφfourQ.1, by exact_mod_cast hφfourQ.2⟩)
  rw [box.centerCLM_eq]
  calc
    ‖rotM p.θ p.φ - RationalApprox.rotMℚℝ
        (box.center.θ : ℝ) (box.center.φ : ℝ)‖ ≤
      ‖rotM p.θ p.φ - rotM (box.center.θ : ℝ) (box.center.φ : ℝ)‖ +
        ‖rotM (box.center.θ : ℝ) (box.center.φ : ℝ) -
          RationalApprox.rotMℚℝ (box.center.θ : ℝ) (box.center.φ : ℝ)‖ := by
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (box.εφ : ℝ) + (box.εθ : ℝ) + RationalApprox.κ := by
      linarith [norm_rotM_sub_le p.θ p.φ
        (box.center.θ : ℝ) (box.center.φ : ℝ)]
    _ = (box.viewError : ℝ) := by
      simp [Box.viewError, RationalApprox.κ, RationalApprox.κℚ]
      ring

theorem norm_normalizedRationalVertex_le (i : VertexIndex) :
    ‖toR3 (normalizedRationalVertex i)‖ ≤ 1 + RationalApprox.κ := by
  have happ := normalizedApproximation.approx i
  calc
    ‖toR3 (normalizedRationalVertex i)‖ =
        ‖normalizedExactVertex i -
          (normalizedExactVertex i - toR3 (normalizedRationalVertex i))‖ := by
      congr 2
      abel
    _ ≤ ‖normalizedExactVertex i‖ +
        ‖normalizedExactVertex i - toR3 (normalizedRationalVertex i)‖ :=
      norm_sub_le _ _
    _ ≤ 1 + RationalApprox.κ :=
      add_le_add (normalizedExactVertex_norm_le_one i) happ

theorem Box.norm_exactVector_sub_approxVector_le
    (box : Box) (contact : Contact) (x y z : ℝ) :
    ‖box.exactVector contact x y z - box.approxVector contact x y z‖ ≤
      2 * cayleyDenom x y z * RationalApprox.κ := by
  have hrearrange :
      box.exactVector contact x y z - box.approxVector contact x y z =
        (cayleyNumeratorMatrix x y z).toEuclideanLin
          (normalizedExactVertex contact.innerIndex -
            toR3 (normalizedRationalVertex contact.innerIndex)) -
        cayleyDenom x y z •
          (normalizedExactVertex contact.outerIndex -
            toR3 (normalizedRationalVertex contact.outerIndex)) := by
    unfold Box.exactVector Box.approxVector
    rw [map_sub]
    module
  rw [hrearrange]
  calc
    ‖(cayleyNumeratorMatrix x y z).toEuclideanLin
          (normalizedExactVertex contact.innerIndex -
            toR3 (normalizedRationalVertex contact.innerIndex)) -
        cayleyDenom x y z •
          (normalizedExactVertex contact.outerIndex -
            toR3 (normalizedRationalVertex contact.outerIndex))‖ ≤
      ‖(cayleyNumeratorMatrix x y z).toEuclideanLin
          (normalizedExactVertex contact.innerIndex -
            toR3 (normalizedRationalVertex contact.innerIndex))‖ +
        ‖cayleyDenom x y z •
          (normalizedExactVertex contact.outerIndex -
            toR3 (normalizedRationalVertex contact.outerIndex))‖ :=
      norm_sub_le _ _
    _ ≤ cayleyDenom x y z * RationalApprox.κ +
        cayleyDenom x y z * RationalApprox.κ := by
      apply add_le_add
      · exact (norm_cayleyNumeratorMatrix_apply_le x y z _).trans
          (mul_le_mul_of_nonneg_left
            (normalizedApproximation.approx contact.innerIndex)
            (cayleyDenom_pos x y z).le)
      · rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (cayleyDenom_pos x y z)]
        exact mul_le_mul_of_nonneg_left
          (normalizedApproximation.approx contact.outerIndex)
          (cayleyDenom_pos x y z).le
    _ = 2 * cayleyDenom x y z * RationalApprox.κ := by ring

theorem Box.norm_approxVector_le (box : Box) (contact : Contact)
    (x y z : ℝ) :
    ‖box.approxVector contact x y z‖ ≤
      2 * cayleyDenom x y z * (1 + RationalApprox.κ) := by
  unfold Box.approxVector
  calc
    ‖(cayleyNumeratorMatrix x y z).toEuclideanLin
          (toR3 (normalizedRationalVertex contact.innerIndex)) -
        cayleyDenom x y z •
          toR3 (normalizedRationalVertex contact.outerIndex)‖ ≤
      ‖(cayleyNumeratorMatrix x y z).toEuclideanLin
          (toR3 (normalizedRationalVertex contact.innerIndex))‖ +
        ‖cayleyDenom x y z •
          toR3 (normalizedRationalVertex contact.outerIndex)‖ :=
      norm_sub_le _ _
    _ ≤ cayleyDenom x y z * (1 + RationalApprox.κ) +
        cayleyDenom x y z * (1 + RationalApprox.κ) := by
      apply add_le_add
      · exact (norm_cayleyNumeratorMatrix_apply_le x y z _).trans
          (mul_le_mul_of_nonneg_left
            (norm_normalizedRationalVertex_le contact.innerIndex)
            (cayleyDenom_pos x y z).le)
      · rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (cayleyDenom_pos x y z)]
        exact mul_le_mul_of_nonneg_left
          (norm_normalizedRationalVertex_le contact.outerIndex)
          (cayleyDenom_pos x y z).le
    _ = 2 * cayleyDenom x y z * (1 + RationalApprox.κ) := by ring

noncomputable def Box.exactContactValue (box : Box) (p : CayleyPose ℝ)
    (contact : Contact) : ℝ :=
  ⟪toR2 contact.direction,
    rotM p.θ p.φ (box.exactVector contact p.x p.y p.z)⟫

theorem Box.contactValue_error (box : Box)
    (hcenter : box.supportBox.center ∈ fourInterval ℚ)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal)
    (contact : Contact)
    (hdirection : LocalCertificate.directionUnit contact.direction) :
    |box.exactContactValue p contact -
        box.approxContactValue contact p.x p.y p.z| ≤
      (box.contactError : ℝ) := by
  have hudir : ‖toR2 contact.direction‖ = 1 := by
    rw [EuclideanSpace.norm_eq, ← Real.sqrt_one]
    congr 1
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, toR2,
      WithLp.ofLp_toLp]
    exact_mod_cast hdirection
  have hdecomp :
      rotM p.θ p.φ (box.exactVector contact p.x p.y p.z) -
          box.centerCLM (box.approxVector contact p.x p.y p.z) =
        rotM p.θ p.φ
          (box.exactVector contact p.x p.y p.z -
            box.approxVector contact p.x p.y p.z) +
        (rotM p.θ p.φ - box.centerCLM)
          (box.approxVector contact p.x p.y p.z) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  have hmap :
      ‖rotM p.θ p.φ (box.exactVector contact p.x p.y p.z) -
          box.centerCLM (box.approxVector contact p.x p.y p.z)‖ ≤
        2 * cayleyDenom p.x p.y p.z *
          (RationalApprox.κ +
            (1 + RationalApprox.κ) * (box.viewError : ℝ)) := by
    rw [hdecomp]
    calc
      ‖rotM p.θ p.φ
            (box.exactVector contact p.x p.y p.z -
              box.approxVector contact p.x p.y p.z) +
          (rotM p.θ p.φ - box.centerCLM)
            (box.approxVector contact p.x p.y p.z)‖ ≤
        ‖rotM p.θ p.φ
            (box.exactVector contact p.x p.y p.z -
              box.approxVector contact p.x p.y p.z)‖ +
          ‖(rotM p.θ p.φ - box.centerCLM)
            (box.approxVector contact p.x p.y p.z)‖ := norm_add_le _ _
      _ ≤ 2 * cayleyDenom p.x p.y p.z * RationalApprox.κ +
          (box.viewError : ℝ) *
            (2 * cayleyDenom p.x p.y p.z *
              (1 + RationalApprox.κ)) := by
        apply add_le_add
        · exact (ContinuousLinearMap.le_opNorm _ _).trans (by
            rw [Bounding.rotM_norm_one, one_mul]
            exact box.norm_exactVector_sub_approxVector_le contact p.x p.y p.z)
        · exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul
              (box.norm_view_sub_centerCLM_le hcenter hp)
              (box.norm_approxVector_le contact p.x p.y p.z)
              (norm_nonneg _) (by exact_mod_cast box.viewError_nonneg))
      _ = 2 * cayleyDenom p.x p.y p.z *
          (RationalApprox.κ +
            (1 + RationalApprox.κ) * (box.viewError : ℝ)) := by ring
  unfold Box.exactContactValue Box.approxContactValue
  rw [← inner_sub_right]
  calc
    |⟪toR2 contact.direction,
        rotM p.θ p.φ (box.exactVector contact p.x p.y p.z) -
          box.centerCLM (box.approxVector contact p.x p.y p.z)⟫| ≤
      ‖toR2 contact.direction‖ *
        ‖rotM p.θ p.φ (box.exactVector contact p.x p.y p.z) -
          box.centerCLM (box.approxVector contact p.x p.y p.z)‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ 2 * cayleyDenom p.x p.y p.z *
        (RationalApprox.κ +
          (1 + RationalApprox.κ) * (box.viewError : ℝ)) := by
      rw [hudir, one_mul]
      exact hmap
    _ ≤ 2 * (box.dBound : ℝ) *
        (RationalApprox.κ +
          (1 + RationalApprox.κ) * (box.viewError : ℝ)) := by
      have hfactor : 0 ≤ RationalApprox.κ +
          (1 + RationalApprox.κ) * (box.viewError : ℝ) :=
        add_nonneg (by norm_num [RationalApprox.κ])
          (mul_nonneg (by norm_num [RationalApprox.κ])
            (by exact_mod_cast box.viewError_nonneg))
      have hmul := mul_le_mul_of_nonneg_right (box.denom_le_dBound hp) hfactor
      nlinarith
    _ = (box.contactError : ℝ) := by
      simp [Box.contactError, RationalApprox.κ, RationalApprox.κℚ]

def Contact.supported (box : Box) (contact : Contact) : Prop :=
  contact.outerContact.supported box.supportBox

instance (box : Box) (contact : Contact) : Decidable (contact.supported box) := by
  unfold Contact.supported
  infer_instance

@[mk_iff]
structure Box.Valid (box : Box) : Prop where
  center_in_four : box.supportBox.center ∈ fourInterval ℚ
  direction_unit : ∀ i, LocalCertificate.directionUnit (box.contact i).direction
  weight_pos : ∀ i, 0 < box.weight i
  balanced : box.balanced
  supported : ∀ i, (box.contact i).supported box
  displacement :
    box.error < box.displacementBall.center - box.displacementBall.radius

instance (box : Box) : Decidable box.Valid :=
  decidable_of_iff _ (Box.valid_iff box).symm

noncomputable def Box.approxDisplacement (box : Box) (p : CayleyPose ℝ) : ℝ :=
  ∑ i, (box.weight i : ℝ) *
    box.approxContactValue (box.contact i) p.x p.y p.z

noncomputable def Box.exactDisplacement (box : Box) (p : CayleyPose ℝ) : ℝ :=
  ∑ i, (box.weight i : ℝ) * box.exactContactValue p (box.contact i)

theorem Box.displacement_error (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal) :
    |box.exactDisplacement p - box.approxDisplacement p| ≤
      (box.error : ℝ) := by
  have hrewrite : box.exactDisplacement p - box.approxDisplacement p =
      ∑ i, (box.weight i : ℝ) *
        (box.exactContactValue p (box.contact i) -
          box.approxContactValue (box.contact i) p.x p.y p.z) := by
    unfold Box.exactDisplacement Box.approxDisplacement
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hrewrite]
  calc
    |∑ i, (box.weight i : ℝ) *
        (box.exactContactValue p (box.contact i) -
          box.approxContactValue (box.contact i) p.x p.y p.z)| ≤
      ∑ i, |(box.weight i : ℝ) *
        (box.exactContactValue p (box.contact i) -
          box.approxContactValue (box.contact i) p.x p.y p.z)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, (box.weight i : ℝ) *
        |box.exactContactValue p (box.contact i) -
          box.approxContactValue (box.contact i) p.x p.y p.z| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_pos (by exact_mod_cast h.weight_pos i)]
    _ ≤ ∑ i, (box.weight i : ℝ) * (box.contactError : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (box.contactValue_error h.center_in_four hp (box.contact i)
          (h.direction_unit i))
        (by exact_mod_cast (h.weight_pos i).le)
    _ = (box.error : ℝ) := by
      simp [Box.error, Box.totalWeight, Finset.sum_mul]

theorem Box.approxDisplacement_gt_error (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal) :
    (box.error : ℝ) < box.approxDisplacement p := by
  have hvars : ∀ i : Fin 3,
      (box.variableBalls i).Holds (![p.x, p.y, p.z] i) := by
    intro i
    fin_cases i
    · exact box.interval.coordinateBall_holds hp 2
    · exact box.interval.coordinateBall_holds hp 3
    · exact box.interval.coordinateBall_holds hp 4
  have henclose := RatPolynomial.evalBall_holds hvars box.displacementPolynomial
  have hlower := RatBall.lower_le_of_holds henclose
  rw [box.eval_displacementPolynomial] at hlower
  change (box.displacementBall.center - box.displacementBall.radius : ℚ) ≤
    box.approxDisplacement p at hlower
  exact lt_of_lt_of_le (by exact_mod_cast h.displacement) hlower

theorem Box.exactDisplacement_nonneg (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal) :
    0 ≤ box.exactDisplacement p := by
  have herr := box.displacement_error h hp
  have hpos := box.approxDisplacement_gt_error h hp
  rw [abs_le] at herr
  linarith

noncomputable def Box.actualContactValue (box : Box) (p : CayleyPose ℝ)
    (contact : Contact) : ℝ :=
  ⟪toR2 contact.direction,
    rotM p.θ p.φ
      ((cayleyMatrix p.x p.y p.z).toEuclideanLin
          (normalizedExactVertex contact.innerIndex) -
        normalizedExactVertex contact.outerIndex)⟫

noncomputable def Box.actualDisplacement (box : Box) (p : CayleyPose ℝ) : ℝ :=
  ∑ i, (box.weight i : ℝ) * box.actualContactValue p (box.contact i)

theorem Box.exactContactValue_eq_denom_mul (box : Box) (p : CayleyPose ℝ)
    (contact : Contact) :
    box.exactContactValue p contact =
      cayleyDenom p.x p.y p.z * box.actualContactValue p contact := by
  have happ :
      (cayleyNumeratorMatrix p.x p.y p.z).toEuclideanLin
          (normalizedExactVertex contact.innerIndex) =
        cayleyDenom p.x p.y p.z •
          (cayleyMatrix p.x p.y p.z).toEuclideanLin
            (normalizedExactVertex contact.innerIndex) := by
    rw [cayleyNumeratorMatrix_eq_denom_smul]
    ext i
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, mul_add]
  unfold Box.exactContactValue Box.actualContactValue Box.exactVector
  rw [happ]
  simp only [← smul_sub, map_smul, inner_smul_right, real_inner_comm]

theorem Box.exactDisplacement_eq_denom_mul (box : Box) (p : CayleyPose ℝ) :
    box.exactDisplacement p =
      cayleyDenom p.x p.y p.z * box.actualDisplacement p := by
  unfold Box.exactDisplacement Box.actualDisplacement
  simp_rw [box.exactContactValue_eq_denom_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem Box.actualDisplacement_nonneg (box : Box) (h : box.Valid)
    {p : CayleyPose ℝ} (hp : p ∈ box.interval.toReal) :
    0 ≤ box.actualDisplacement p := by
  have hexact := box.exactDisplacement_nonneg h hp
  rw [box.exactDisplacement_eq_denom_mul] at hexact
  exact nonneg_of_mul_nonneg_right hexact (cayleyDenom_pos p.x p.y p.z)

theorem Box.valid_imp_not_translated_rupert (box : Box) (h : box.Valid) :
    ∀ p ∈ box.interval.toReal, ∀ offset : ℝ²,
      ¬ RupertPose (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull := by
  intro p hp offset
  let q := CayleyLocalCertificate.outerPose p
  have hqmem : q ∈ box.supportBox.realInterval := by
    simpa [Box.supportBox] using
      (box.localShell.outerPose_mem_eulerRealInterval hp)
  have hqnear := box.supportBox.near_center_of_mem_realInterval hqmem
  apply Noperthedron.BalancedSupport.not_rupertPose_of_balanced_support
    normalizedExactPolyhedron (p.matrixPoseWithOffset offset)
    (fun i => (box.contact i).innerIndex)
    (fun i => (box.contact i).outerIndex)
    (fun i => (box.weight i : ℝ))
    (fun i => toR2 (box.contact i).direction)
  · intro i hdirection
    have hnorm : ‖toR2 (box.contact i).direction‖ = 1 := by
      rw [EuclideanSpace.norm_eq, ← Real.sqrt_one]
      congr 1
      simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, toR2,
        WithLp.ofLp_toLp]
      exact_mod_cast h.direction_unit i
    rw [hdirection, norm_zero] at hnorm
    norm_num at hnorm
  · intro i
    exact_mod_cast (h.weight_pos i).le
  · exact ⟨0, by exact_mod_cast h.weight_pos 0⟩
  · ext c
    have hb := congrFun h.balanced c
    simp only [Box.balanced, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply] at hb
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
      Pi.smul_apply, toR2, smul_eq_mul, WithLp.ofLp_zero, Pi.zero_apply]
    exact_mod_cast hb
  · intro i y hy
    obtain ⟨v, ⟨j, rfl⟩, rfl⟩ := hy
    have hs := LocalCertificate.contact_support_matrixPose
      box.supportBox (box.contact i).outerContact h.center_in_four
      (h.direction_unit i) (h.supported i) hqnear offset j
    have hs' :
        ⟪toR2 (box.contact i).direction,
          rotM p.θ p.φ (normalizedExactVertex j)⟫ ≤
        ⟪toR2 (box.contact i).direction,
          rotM p.θ p.φ
            (normalizedExactVertex (box.contact i).outerIndex)⟫ := by
      simpa [q, Box.supportBox, Box.localShell,
        CayleyLocalCertificate.Box.eulerBox,
        CayleyLocalCertificate.outerPose,
        Noperthedron.BalancedSupport.outerProjectionLinear,
        Noperthedron.BalancedSupport.matrixPoseWithOffset_outer_rotation_project,
        Pose.outer_eq_M, Pose.rotM₂,
        CayleyGlobalCertificate.Contact.outerContact] using hs
    change
      ⟪toR2 (box.contact i).direction,
        proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin
          (normalizedExactVertex j))⟫ ≤
      ⟪toR2 (box.contact i).direction,
        proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin
          (normalizedExactVertex (box.contact i).outerIndex))⟫
    rw [CayleyPose.matrixPoseWithOffset_outer_rotation_project,
      CayleyPose.matrixPoseWithOffset_outer_rotation_project]
    exact hs'
  · have hdisp := box.actualDisplacement_nonneg h hp
    change 0 ≤ ∑ i, (box.weight i : ℝ) *
      ⟪toR2 (box.contact i).direction,
        proj_xyL ((p.matrixPoseWithOffset offset).innerRot.val.toEuclideanLin
          (normalizedExactVertex (box.contact i).innerIndex)) -
        proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin
          (normalizedExactVertex (box.contact i).outerIndex))⟫
    simp_rw [CayleyPose.matrixPoseWithOffset_inner_rotation_project,
      CayleyPose.matrixPoseWithOffset_outer_rotation_project, ← map_sub]
    simpa only [Box.actualDisplacement, Box.actualContactValue] using hdisp

theorem Box.valid_imp_no_translated_rupert_in_interval
    (box : Box) (h : box.Valid) :
    ¬ ∃ p ∈ box.interval.toReal, ∃ offset : ℝ²,
      RupertPose (p.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull := by
  rintro ⟨p, hp, offset, hrupert⟩
  exact box.valid_imp_not_translated_rupert h p hp offset hrupert

end Noperthedron.SnubCube.CayleyGlobalCertificate

end
