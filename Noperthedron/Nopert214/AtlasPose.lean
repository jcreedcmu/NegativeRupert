module

public import Noperthedron.Nopert214.CayleyAtlas

@[expose] public section

/-!
# Nopert #214 poses in the bounded Cayley atlas

An atlas pose retains only the two outer viewing angles.  Its relative
rotation is represented in one of the four rational Cayley charts.  Thus the
certificate domain is four copies of a five-dimensional rational box, with
no Euler singularities.
-/

namespace Noperthedron.Nopert214

open scoped Matrix
open CayleyAtlas

/-- Two outer viewing angles and three relative Cayley coordinates. -/
structure AtlasPose (R : Type) where
  θ : R
  φ : R
  x : R
  y : R
  z : R
deriving DecidableEq, Repr

namespace AtlasPose

def equivPi {R : Type} : AtlasPose R ≃ (Fin 5 → R) where
  toFun p := ![p.θ, p.φ, p.x, p.y, p.z]
  invFun f := ⟨f 0, f 1, f 2, f 3, f 4⟩
  left_inv p := by cases p; rfl
  right_inv f := by ext i; fin_cases i <;> rfl

instance {R : Type} [PartialOrder R] : PartialOrder (AtlasPose R) :=
  PartialOrder.lift equivPi equivPi.injective

theorem le_iff {R : Type} [PartialOrder R] (p q : AtlasPose R) :
    p ≤ q ↔ p.θ ≤ q.θ ∧ p.φ ≤ q.φ ∧ p.x ≤ q.x ∧
      p.y ≤ q.y ∧ p.z ≤ q.z := by
  show equivPi p ≤ equivPi q ↔ _
  rw [Pi.le_def]
  refine ⟨fun h => ⟨h 0, h 1, h 2, h 3, h 4⟩, ?_⟩
  rintro ⟨hθ, hφ, hx, hy, hz⟩ i
  fin_cases i <;> assumption

instance {R : Type} [PartialOrder R] [DecidableLE R] :
    DecidableLE (AtlasPose R) :=
  fun p q => decidable_of_iff _ (le_iff p q).symm

/-- The rational root common to all four charts. -/
def rootInterval (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    NonemptyInterval (AtlasPose R) :=
  NonemptyInterval.mk
    ⟨{ θ := 0, φ := 0, x := -2, y := -2, z := -2 },
      { θ := 8 / 5, φ := 4, x := 2, y := 2, z := 2 }⟩
    (by rw [le_iff]; norm_num)

/-- Componentwise rational-to-real conversion. -/
def toReal (p : AtlasPose ℚ) : AtlasPose ℝ where
  θ := p.θ
  φ := p.φ
  x := p.x
  y := p.y
  z := p.z

@[simp] theorem toReal_θ (p : AtlasPose ℚ) : p.toReal.θ = (p.θ : ℝ) := rfl
@[simp] theorem toReal_φ (p : AtlasPose ℚ) : p.toReal.φ = (p.φ : ℝ) := rfl
@[simp] theorem toReal_x (p : AtlasPose ℚ) : p.toReal.x = (p.x : ℝ) := rfl
@[simp] theorem toReal_y (p : AtlasPose ℚ) : p.toReal.y = (p.y : ℝ) := rfl
@[simp] theorem toReal_z (p : AtlasPose ℚ) : p.toReal.z = (p.z : ℝ) := rfl

/-- The outer viewing rotation bundled as an element of `SO(3)`. -/
noncomputable def outerSO3 (p : AtlasPose ℝ) : SO3 :=
  ⟨rotRM_mat p.θ p.φ 0, rotRM_mat_mem_SO3 _ _ _⟩

/-- Interpret an atlas pose and chart as a full matrix pose. -/
noncomputable def matrixPoseWithOffset (chart : ChartIndex)
    (p : AtlasPose ℝ) (offset : ℝ²) : MatrixPose where
  outerRot := p.outerSO3
  innerRot := p.outerSO3 * chartSO3 chart * cayleySO3 p.x p.y p.z
  innerOffset := offset

@[simp] theorem matrixPoseWithOffset_outerRot_val (chart : ChartIndex)
    (p : AtlasPose ℝ) (offset : ℝ²) :
    (p.matrixPoseWithOffset chart offset).outerRot.val =
      rotRM_mat p.θ p.φ 0 := rfl

@[simp] theorem matrixPoseWithOffset_innerRot_val (chart : ChartIndex)
    (p : AtlasPose ℝ) (offset : ℝ²) :
    (p.matrixPoseWithOffset chart offset).innerRot.val =
      (rotRM_mat p.θ p.φ 0 * chartMatrix chart) *
        cayleyMatrix p.x p.y p.z := rfl

@[simp] theorem matrixPoseWithOffset_relativeRotation (chart : ChartIndex)
    (p : AtlasPose ℝ) (offset : ℝ²) :
    (p.matrixPoseWithOffset chart offset).relativeRotation =
      chartMatrix chart * cayleyMatrix p.x p.y p.z := by
  have horth := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp
    (rotRM_mat_mem_SO3 p.θ p.φ 0).1
  simp only [MatrixPose.relativeRotation,
    matrixPoseWithOffset_outerRot_val, matrixPoseWithOffset_innerRot_val]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc
    (rotRM_mat p.θ p.φ 0)ᵀ, horth, Matrix.one_mul]

theorem matrixPoseWithOffset_inner_rotation_project (chart : ChartIndex)
    (p : AtlasPose ℝ) (offset : ℝ²) (v : ℝ³) :
    proj_xyL ((p.matrixPoseWithOffset chart offset).innerRot.val.toEuclideanLin v) =
      rotM p.θ p.φ
        ((chartMatrix chart * cayleyMatrix p.x p.y p.z).toEuclideanLin v) := by
  have hrot := congrArg (fun f : ℝ³ →L[ℝ] ℝ³ =>
      f ((chartMatrix chart * cayleyMatrix p.x p.y p.z).toEuclideanLin v))
    (rotRM_eq_rotRM_mat p.θ p.φ 0)
  rw [← Pose.proj_rm_eq_m]
  apply congrArg proj_xyL
  simpa [matrixPoseWithOffset_innerRot_val, Matrix.toLpLin_apply,
    Matrix.mulVec_mulVec, Matrix.mul_assoc] using hrot.symm

theorem matrixPoseWithOffset_outer_rotation_project (chart : ChartIndex)
    (p : AtlasPose ℝ) (offset : ℝ²) (v : ℝ³) :
    proj_xyL ((p.matrixPoseWithOffset chart offset).outerRot.val.toEuclideanLin v) =
      rotM p.θ p.φ v := by
  have hrot := congrArg (fun f : ℝ³ →L[ℝ] ℝ³ => f v)
    (rotRM_eq_rotRM_mat p.θ p.φ 0)
  rw [← Pose.proj_rm_eq_m]
  apply congrArg proj_xyL
  simpa [matrixPoseWithOffset_outerRot_val] using hrot.symm

end AtlasPose

theorem matrixPose_ext_val {p q : MatrixPose}
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

/-- Keep the outer view of an Euler pose and replace its relative rotation
by three Cayley coordinates. -/
def AtlasPose.ofPose (euler : Pose ℝ) (x y z : ℝ) : AtlasPose ℝ :=
  { θ := euler.θ₂, φ := euler.φ₂, x := x, y := y, z := z }

def AtlasPose.CayleyBounded (p : AtlasPose ℝ) : Prop :=
  p.x ^ 2 + p.y ^ 2 + p.z ^ 2 ≤ 3

/-- The exact outer-view wedge inherited from the symmetry-reduced Euler
representative. -/
def AtlasPose.InViewWedge (p : AtlasPose ℝ) : Prop :=
  p.θ ∈ Set.Icc 0 (2 * Real.pi / 5) ∧ p.φ ∈ Set.Icc 0 Real.pi

/-- The unoriented viewing line is represented by its upper-hemisphere
normal. -/
def AtlasPose.InUpperView (p : AtlasPose ℝ) : Prop :=
  p.φ ≤ Real.pi / 2

theorem AtlasPose.ofPose_mem_root (euler : Pose ℝ) (x y z : ℝ)
    (heuler : euler ∈ tightPoseInterval)
    (hx : x ∈ Set.Icc (-2 : ℝ) 2)
    (hy : y ∈ Set.Icc (-2 : ℝ) 2)
    (hz : z ∈ Set.Icc (-2 : ℝ) 2) :
    AtlasPose.ofPose euler x y z ∈ AtlasPose.rootInterval ℝ := by
  rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff] at heuler
  rw [NonemptyInterval.mem_def, AtlasPose.le_iff, AtlasPose.le_iff]
  dsimp only [AtlasPose.ofPose, AtlasPose.rootInterval]
  exact ⟨
    ⟨heuler.1.2.1, heuler.1.2.2.2.1, hx.1, hy.1, hz.1⟩,
    ⟨heuler.2.2.1, heuler.2.2.2.2.1, hx.2, hy.2, hz.2⟩⟩

theorem AtlasPose.matrixPoseWithOffset_ofPose_eq (euler : Pose ℝ)
    (offset : ℝ²) (chart : ChartIndex) (x y z : ℝ)
    (hrelative : (euler.matrixPoseWithOffset offset).relativeRotation =
      chartMatrix chart * cayleyMatrix x y z) :
    (AtlasPose.ofPose euler x y z).matrixPoseWithOffset chart offset =
      euler.matrixPoseWithOffset offset := by
  let oldPose := euler.matrixPoseWithOffset offset
  have hrecover :=
    Noperthedron.SnubCube.MatrixPose.outer_mul_relativeRotation oldPose
  apply matrixPose_ext_val
  · calc
      ((AtlasPose.ofPose euler x y z).matrixPoseWithOffset chart offset).innerRot.val =
          (oldPose.outerRot.val * chartMatrix chart) *
            cayleyMatrix x y z := by rfl
      _ = oldPose.outerRot.val *
            (chartMatrix chart * cayleyMatrix x y z) := by
        rw [Matrix.mul_assoc]
      _ = oldPose.outerRot.val * oldPose.relativeRotation := by
        rw [hrelative]
      _ = oldPose.innerRot.val := hrecover
  · rfl
  · rfl

/-- Replace a pose in the symmetry-reduced Euler box by an exactly equal pose
in one of the bounded atlas boxes. -/
theorem exists_atlas_pose_of_tight_pose (euler : Pose ℝ) (offset : ℝ²)
    (heuler : euler ∈ tightPoseInterval) :
    ∃ chart : ChartIndex, ∃ q ∈ AtlasPose.rootInterval ℝ,
      q.matrixPoseWithOffset chart offset =
        euler.matrixPoseWithOffset offset := by
  let oldPose := euler.matrixPoseWithOffset offset
  obtain ⟨chart, x, hx, y, hy, z, hz, _hradius, hrelative⟩ :=
    exists_bounded_chart_cayley oldPose.relativeRotation
      (Noperthedron.SnubCube.MatrixPose.relativeRotation_mem_SO3 oldPose)
  refine ⟨chart, AtlasPose.ofPose euler x y z,
    AtlasPose.ofPose_mem_root euler x y z heuler hx hy hz, ?_⟩
  exact AtlasPose.matrixPoseWithOffset_ofPose_eq
    euler offset chart x y z hrelative

/-- The atlas representative also lies in the radius-`√3` Cayley ball. -/
theorem exists_bounded_atlas_pose_of_tight_pose
    (euler : Pose ℝ) (offset : ℝ²)
    (heuler : euler ∈ tightPoseInterval) (hview : InViewWedge euler) :
    ∃ chart : ChartIndex, ∃ q ∈ AtlasPose.rootInterval ℝ,
      q.CayleyBounded ∧ q.InViewWedge ∧
      q.matrixPoseWithOffset chart offset =
        euler.matrixPoseWithOffset offset := by
  let oldPose := euler.matrixPoseWithOffset offset
  obtain ⟨chart, x, hx, y, hy, z, hz, hradius, hrelative⟩ :=
    exists_bounded_chart_cayley oldPose.relativeRotation
      (Noperthedron.SnubCube.MatrixPose.relativeRotation_mem_SO3 oldPose)
  refine ⟨chart, AtlasPose.ofPose euler x y z,
    AtlasPose.ofPose_mem_root euler x y z heuler hx hy hz,
    hradius, by simpa [AtlasPose.InViewWedge, AtlasPose.ofPose, InViewWedge]
      using hview, ?_⟩
  exact AtlasPose.matrixPoseWithOffset_ofPose_eq
    euler offset chart x y z hrelative

/-- Every matrix pose has an equivalent representative in one of the four
bounded atlas roots. -/
theorem exists_atlas_translated_pose (p : MatrixPose) :
    ∃ δ : ℝ, ∃ chart : ChartIndex, ∃ q : AtlasPose ℝ, ∃ offset : ℝ²,
      q ∈ AtlasPose.rootInterval ℝ ∧
      (RupertPose (q.matrixPoseWithOffset chart offset)
          exactPolyhedron.hull ↔
        RupertPose (p.rotateBy δ) exactPolyhedron.hull) := by
  obtain ⟨δ, euler, offset, heuler, -, heq⟩ :=
    exists_tight_translated_pose p
  obtain ⟨chart, q, hq, hmatrix⟩ :=
    exists_atlas_pose_of_tight_pose euler offset heuler.1
  refine ⟨δ, chart, q, offset, hq, ?_⟩
  rw [hmatrix]
  exact heq

/-- Excluding every chart root excludes every matrix pose. -/
theorem no_matrixPose_of_no_atlas_translated_pose
    (h : ¬ ∃ chart : ChartIndex, ∃ q ∈ AtlasPose.rootInterval ℝ,
      ∃ offset : ℝ²,
        RupertPose (q.matrixPoseWithOffset chart offset)
          exactPolyhedron.hull) :
    ¬ ∃ p : MatrixPose, RupertPose p exactPolyhedron.hull := by
  rintro ⟨p, hp⟩
  obtain ⟨δ, chart, q, offset, hq, heq⟩ :=
    exists_atlas_translated_pose p
  have hrot : RupertPose (p.rotateBy δ) exactPolyhedron.hull :=
    (MatrixPose.RupertPose_rotateBy_iff p δ exactPolyhedron.hull).mpr hp
  exact h ⟨chart, q, hq, offset, heq.mpr hrot⟩

/-- It suffices to exclude only the radius-bounded part of each atlas root. -/
theorem no_matrixPose_of_no_bounded_atlas_translated_pose
    (h : ¬ ∃ chart : ChartIndex, ∃ q ∈ AtlasPose.rootInterval ℝ,
      q.CayleyBounded ∧ q.InViewWedge ∧ ∃ offset : ℝ²,
        RupertPose (q.matrixPoseWithOffset chart offset)
          exactPolyhedron.hull) :
    ¬ ∃ p : MatrixPose, RupertPose p exactPolyhedron.hull := by
  rintro ⟨p, hp⟩
  obtain ⟨δ, euler, offset, heuler, hview, heq⟩ :=
    exists_tight_translated_pose p
  obtain ⟨chart, q, hq, hbounded, hqview, hmatrix⟩ :=
    exists_bounded_atlas_pose_of_tight_pose euler offset heuler.1 hview
  have hrot : RupertPose (p.rotateBy δ) exactPolyhedron.hull :=
    (MatrixPose.RupertPose_rotateBy_iff p δ exactPolyhedron.hull).mpr hp
  have heulerRupert :
      RupertPose (euler.matrixPoseWithOffset offset) exactPolyhedron.hull :=
    heq.mpr hrot
  exact h ⟨chart, q, hq, hbounded, hqview, offset,
    hmatrix ▸ heulerRupert⟩

end Noperthedron.Nopert214

end
