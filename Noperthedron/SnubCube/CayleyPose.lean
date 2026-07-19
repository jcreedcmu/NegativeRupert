module

public import Noperthedron.SnubCube.FundamentalDomain

@[expose] public section


/-!
# Five-parameter poses with rational relative rotation

After screen rotation and snub-cube symmetry reduction, the outer rotation
needs two spherical angles and the relative rotation lies in a bounded
Cayley chart.  Thus `(theta, phi, x, y, z)` replaces the previous pair of
Euler rotations.  The equality stratum is the coordinate plane
`x = y = z = 0`, and all dependence on the relative rotation is rational.
-/

namespace Noperthedron.SnubCube

open scoped Matrix

/-- Two outer viewing angles and a three-dimensional relative Cayley vector. -/
structure CayleyPose (R : Type) where
  θ : R
  φ : R
  x : R
  y : R
  z : R
deriving DecidableEq, Repr

namespace CayleyPose

def equivPi {R : Type} : CayleyPose R ≃ (Fin 5 → R) where
  toFun p := ![p.θ, p.φ, p.x, p.y, p.z]
  invFun f := ⟨f 0, f 1, f 2, f 3, f 4⟩
  left_inv p := by cases p; rfl
  right_inv f := by ext i; fin_cases i <;> rfl

instance {R : Type} [PartialOrder R] : PartialOrder (CayleyPose R) :=
  PartialOrder.lift equivPi equivPi.injective

theorem le_iff {R : Type} [PartialOrder R] (p q : CayleyPose R) :
    p ≤ q ↔ p.θ ≤ q.θ ∧ p.φ ≤ q.φ ∧ p.x ≤ q.x ∧
      p.y ≤ q.y ∧ p.z ≤ q.z := by
  show equivPi p ≤ equivPi q ↔ _
  rw [Pi.le_def]
  refine ⟨fun h => ⟨h 0, h 1, h 2, h 3, h 4⟩, ?_⟩
  rintro ⟨hθ, hφ, hx, hy, hz⟩ i
  fin_cases i <;> assumption

instance {R : Type} [PartialOrder R] [DecidableLE R] :
    DecidableLE (CayleyPose R) :=
  fun p q => decidable_of_iff _ (le_iff p q).symm

/-- Closed rational root used by the checked solution tree. -/
def rootInterval (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    NonemptyInterval (CayleyPose R) :=
  NonemptyInterval.mk
    ⟨{ θ := 0, φ := 0, x := -2, y := -2, z := -2 },
      { θ := 2, φ := 2, x := 2, y := 2, z := 2 }⟩
    (by rw [le_iff]; norm_num)

/-- Componentwise rational-to-real conversion. -/
def toReal (p : CayleyPose ℚ) : CayleyPose ℝ where
  θ := p.θ
  φ := p.φ
  x := p.x
  y := p.y
  z := p.z

@[simp] theorem toReal_θ (p : CayleyPose ℚ) : p.toReal.θ = (p.θ : ℝ) := rfl
@[simp] theorem toReal_φ (p : CayleyPose ℚ) : p.toReal.φ = (p.φ : ℝ) := rfl
@[simp] theorem toReal_x (p : CayleyPose ℚ) : p.toReal.x = (p.x : ℝ) := rfl
@[simp] theorem toReal_y (p : CayleyPose ℚ) : p.toReal.y = (p.y : ℝ) := rfl
@[simp] theorem toReal_z (p : CayleyPose ℚ) : p.toReal.z = (p.z : ℝ) := rfl

/-- Turn the five parameters and a planar translation into a full matrix
pose.  The inner rotation is `outer * relative`. -/
noncomputable def matrixPoseWithOffset
    (p : CayleyPose ℝ) (offset : ℝ²) : MatrixPose where
  outerRot := ⟨rotRM_mat p.θ p.φ 0, rotRM_mat_mem_SO3 _ _ _⟩
  innerRot :=
    ⟨rotRM_mat p.θ p.φ 0 * cayleyMatrix p.x p.y p.z,
      Submonoid.mul_mem _ (rotRM_mat_mem_SO3 _ _ _)
        (cayleyMatrix_mem_SO3 _ _ _)⟩
  innerOffset := offset

@[simp]
theorem matrixPoseWithOffset_outerRot_val
    (p : CayleyPose ℝ) (offset : ℝ²) :
    (p.matrixPoseWithOffset offset).outerRot.val =
      rotRM_mat p.θ p.φ 0 := rfl

@[simp]
theorem matrixPoseWithOffset_innerRot_val
    (p : CayleyPose ℝ) (offset : ℝ²) :
    (p.matrixPoseWithOffset offset).innerRot.val =
      rotRM_mat p.θ p.φ 0 * cayleyMatrix p.x p.y p.z := rfl

/-- Pulling the inner rotation back through the outer rotation recovers the
Cayley matrix exactly. -/
@[simp]
theorem matrixPoseWithOffset_relativeRotation
    (p : CayleyPose ℝ) (offset : ℝ²) :
    (p.matrixPoseWithOffset offset).relativeRotation =
      cayleyMatrix p.x p.y p.z := by
  have horth := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp
    (rotRM_mat_mem_SO3 p.θ p.φ 0).1
  simp only [MatrixPose.relativeRotation,
    matrixPoseWithOffset_outerRot_val, matrixPoseWithOffset_innerRot_val]
  rw [← Matrix.mul_assoc, horth, Matrix.one_mul]

theorem matrixPoseWithOffset_inner_rotation_project
    (p : CayleyPose ℝ) (offset : ℝ²) (v : ℝ³) :
    proj_xyL ((p.matrixPoseWithOffset offset).innerRot.val.toEuclideanLin v) =
      rotM p.θ p.φ ((cayleyMatrix p.x p.y p.z).toEuclideanLin v) := by
  have hrot := congrArg (fun f : ℝ³ →L[ℝ] ℝ³ =>
      f ((cayleyMatrix p.x p.y p.z).toEuclideanLin v))
    (rotRM_eq_rotRM_mat p.θ p.φ 0)
  rw [← Pose.proj_rm_eq_m]
  apply congrArg proj_xyL
  simpa [matrixPoseWithOffset_innerRot_val, Matrix.toLpLin_apply,
    Matrix.mulVec_mulVec] using hrot.symm

theorem matrixPoseWithOffset_outer_rotation_project
    (p : CayleyPose ℝ) (offset : ℝ²) (v : ℝ³) :
    proj_xyL ((p.matrixPoseWithOffset offset).outerRot.val.toEuclideanLin v) =
      rotM p.θ p.φ v := by
  have hrot := congrArg (fun f : ℝ³ →L[ℝ] ℝ³ => f v)
    (rotRM_eq_rotRM_mat p.θ p.φ 0)
  rw [← Pose.proj_rm_eq_m]
  apply congrArg proj_xyL
  simpa [matrixPoseWithOffset_outerRot_val] using hrot.symm

end CayleyPose

/-- The inner rotation of any matrix pose is its outer rotation followed by
its relative rotation. -/
theorem MatrixPose.outer_mul_relativeRotation (p : MatrixPose) :
    p.outerRot.val * p.relativeRotation = p.innerRot.val := by
  have horth := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp
    p.outerRot.property.1
  simp only [MatrixPose.relativeRotation, ← Matrix.mul_assoc, horth,
    Matrix.one_mul]

private theorem matrixPose_ext_val {p q : MatrixPose}
    (hinner : p.innerRot.val = q.innerRot.val)
    (houter : p.outerRot.val = q.outerRot.val)
    (hoffset : p.innerOffset = q.innerOffset) : p = q := by
  cases p with
  | mk pinner pouter poffset =>
    cases q with
    | mk qinner qouter qoffset =>
      have hi : pinner = qinner := Subtype.ext hinner
      have ho : pouter = qouter := Subtype.ext houter
      subst hi
      subst ho
      subst hoffset
      rfl

/-- Every matrix pose has an equivalent representative in the bounded
five-dimensional Cayley root, still carrying its arbitrary translation and
the exact fundamental-domain condition. -/
theorem exists_cayley_translated_pose (p : MatrixPose) :
    ∃ gi go : VertexIndex, ∃ δ : ℝ, ∃ q : CayleyPose ℝ, ∃ offset : ℝ²,
      q ∈ CayleyPose.rootInterval ℝ ∧
      (q.matrixPoseWithOffset offset).InSnubFundamentalDomain ∧
      q.matrixPoseWithOffset offset =
        (p.rightSnubSymmetries gi go).rotateBy δ := by
  obtain ⟨gi, go, δ, euler, offset, heuler, heq, hfund⟩ :=
    exists_fundamental_translated_pose p
  obtain ⟨x, hx, y, hy, z, hz, _hradius, hrelative⟩ :=
    exists_bounded_cayley_of_inFundamentalDomain
      (euler.matrixPoseWithOffset offset).relativeRotation
      (Noperthedron.SnubCube.MatrixPose.relativeRotation_mem_SO3
        (euler.matrixPoseWithOffset offset)) hfund
  let q : CayleyPose ℝ :=
    { θ := euler.θ₂, φ := euler.φ₂, x := x, y := y, z := z }
  have heulerComponents := heuler
  rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff] at heulerComponents
  have hq : q ∈ CayleyPose.rootInterval ℝ := by
    rw [NonemptyInterval.mem_def, CayleyPose.le_iff, CayleyPose.le_iff]
    dsimp only [q, CayleyPose.rootInterval]
    exact ⟨
      ⟨heulerComponents.1.2.1, heulerComponents.1.2.2.2.1,
        hx.1, hy.1, hz.1⟩,
      ⟨heulerComponents.2.2.1, heulerComponents.2.2.2.2.1,
        hx.2, hy.2, hz.2⟩⟩
  have hinner :
      (q.matrixPoseWithOffset offset).innerRot.val =
        (euler.matrixPoseWithOffset offset).innerRot.val := by
    have hrecover :=
      Noperthedron.SnubCube.MatrixPose.outer_mul_relativeRotation
        (euler.matrixPoseWithOffset offset)
    rw [hrelative] at hrecover
    simpa only [q, CayleyPose.matrixPoseWithOffset_innerRot_val,
      Pose.matrixPoseWithOffset, Pose.matrixPoseOfPose,
      CayleyPose.matrixPoseWithOffset_outerRot_val] using hrecover
  have hmatrix : q.matrixPoseWithOffset offset =
      euler.matrixPoseWithOffset offset := by
    apply matrixPose_ext_val
    · exact hinner
    · rfl
    · rfl
  refine ⟨gi, go, δ, q, offset, hq, ?_, hmatrix.trans heq⟩
  rw [hmatrix]
  exact hfund

/-- It suffices to exclude translated Cayley poses in the bounded root. -/
theorem no_matrixPose_of_no_cayley_translated_pose
    (h : ¬ ∃ q ∈ CayleyPose.rootInterval ℝ, ∃ offset : ℝ²,
      (q.matrixPoseWithOffset offset).InSnubFundamentalDomain ∧
      RupertPose (q.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull) :
    ¬ ∃ p : MatrixPose,
      RupertPose p normalizedExactPolyhedron.hull := by
  rintro ⟨p, hp⟩
  obtain ⟨gi, go, δ, q, offset, hq, hfund, heq⟩ :=
    exists_cayley_translated_pose p
  have hsym : RupertPose (p.rightSnubSymmetries gi go)
      normalizedExactPolyhedron.hull :=
    (RupertPose_rightSnubSymmetries_iff p gi go).mpr hp
  have hrot : RupertPose ((p.rightSnubSymmetries gi go).rotateBy δ)
      normalizedExactPolyhedron.hull :=
    (MatrixPose.RupertPose_rotateBy_iff
      (p.rightSnubSymmetries gi go) δ normalizedExactPolyhedron.hull).mpr hsym
  exact h ⟨q, hq, offset, hfund, heq.symm ▸ hrot⟩

end Noperthedron.SnubCube

end
