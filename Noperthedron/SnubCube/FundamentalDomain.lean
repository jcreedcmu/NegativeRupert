module

public import Mathlib.Data.Finset.Max
public import Noperthedron.Cayley
public import Noperthedron.SnubCube.Tightening

@[expose] public section


/-!
# Relative-rotation fundamental domain

Right composition of the inner copy by a snub-cube symmetry lets us choose a
Dirichlet representative of every relative rotation.  We use matrix trace as
the score: maximizing `trace (R * g)` is equivalent to minimizing rotation
angle from the identity.  The finite maximum is purely exact and leaves only
the identity equality stratum in the selected domain.
-/

namespace Noperthedron.SnubCube

open scoped Matrix

/-- The checked action table is also the multiplication table of the 24
rotation matrices. -/
theorem symmetryMatrix_mul_symmetryMatrix (g h : VertexIndex) :
    symmetryMatrix g * symmetryMatrix h =
      symmetryMatrix (symmetryAction g h) := by
  change (symmetryMatrixInt g).map (Int.castRingHom ℝ) *
      (symmetryMatrixInt h).map (Int.castRingHom ℝ) =
    (symmetryMatrixInt (symmetryAction g h)).map (Int.castRingHom ℝ)
  rw [← Matrix.map_mul]
  congr 1
  obtain ⟨gp, gs⟩ := g
  obtain ⟨hp, hs⟩ := h
  fin_cases gp <;> fin_cases gs <;> fin_cases hp <;> fin_cases hs <;>
    decide +kernel

/-- A relative rotation is in the identity Dirichlet cell when no right
snub-cube symmetry increases its trace. -/
def InFundamentalDomain (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ g : VertexIndex, Matrix.trace (R * symmetryMatrix g) ≤ Matrix.trace R

/-- A matrix in the max-trace Dirichlet cell has nonnegative trace.  This is
the key fact excluding the angle-`pi` singularity of Cayley coordinates. -/
theorem trace_nonneg_of_inFundamentalDomain
    {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : InFundamentalDomain R) :
    0 ≤ Matrix.trace R := by
  have hsum :
      (∑ g : VertexIndex, Matrix.trace (R * symmetryMatrix g)) ≤
        ∑ _g : VertexIndex, Matrix.trace R :=
    Finset.sum_le_sum fun g _ => hR g
  have hleft :
      (∑ g : VertexIndex, Matrix.trace (R * symmetryMatrix g)) = 0 := by
    rw [← Matrix.trace_sum, ← Matrix.mul_sum, sum_symmetryMatrix]
    simp
  rw [hleft] at hsum
  norm_num at hsum ⊢
  have hcard : (0 : ℝ) < Fintype.card VertexIndex := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card VertexIndex)
  nlinarith

/-- The max-trace cell is contained in one bounded Cayley chart. -/
theorem exists_bounded_cayley_of_inFundamentalDomain
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hSO : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hfund : InFundamentalDomain R) :
    ∃ x ∈ Set.Icc (-2 : ℝ) 2,
      ∃ y ∈ Set.Icc (-2 : ℝ) 2,
      ∃ z ∈ Set.Icc (-2 : ℝ) 2,
        x ^ 2 + y ^ 2 + z ^ 2 ≤ 3 ∧ R = cayleyMatrix x y z := by
  obtain ⟨x, y, z, hradius, hR⟩ :=
    exists_cayleyMatrix_of_trace_nonneg R hSO
      (trace_nonneg_of_inFundamentalDomain hfund)
  have hxSq : x ^ 2 ≤ 3 := by
    nlinarith [sq_nonneg y, sq_nonneg z]
  have hySq : y ^ 2 ≤ 3 := by
    nlinarith [sq_nonneg x, sq_nonneg z]
  have hzSq : z ^ 2 ≤ 3 := by
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hx : x ∈ Set.Icc (-2 : ℝ) 2 := by
    constructor <;> nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2)]
  have hy : y ∈ Set.Icc (-2 : ℝ) 2 := by
    constructor <;> nlinarith [sq_nonneg (y - 2), sq_nonneg (y + 2)]
  have hz : z ∈ Set.Icc (-2 : ℝ) 2 := by
    constructor <;> nlinarith [sq_nonneg (z - 2), sq_nonneg (z + 2)]
  exact ⟨x, hx, y, hy, z, hz, hradius, hR⟩

/-- Every matrix has a right-symmetry representative in the Dirichlet cell.
No analytic compactness is needed: this is a maximum over 24 values. -/
theorem exists_mul_symmetry_inFundamentalDomain
    (R : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ h : VertexIndex, InFundamentalDomain (R * symmetryMatrix h) := by
  obtain ⟨h, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun g : VertexIndex => Matrix.trace (R * symmetryMatrix g))
    Finset.univ_nonempty
  refine ⟨h, fun g => ?_⟩
  rw [Matrix.mul_assoc, symmetryMatrix_mul_symmetryMatrix]
  exact hmax (symmetryAction h g) (Finset.mem_univ _)

/-- Relative rotation of a full pose, with the outer frame pulled back. -/
def _root_.MatrixPose.relativeRotation (p : MatrixPose) :
    Matrix (Fin 3) (Fin 3) ℝ := p.outerRot.valᵀ * p.innerRot.val

theorem MatrixPose.relativeRotation_mem_SO3 (p : MatrixPose) :
    p.relativeRotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have hout := (Matrix.mem_specialOrthogonalGroup_iff).mp p.outerRot.property
  have houtT : p.outerRot.valᵀ ∈
      Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    rw [Matrix.mem_specialOrthogonalGroup_iff,
      Matrix.mem_orthogonalGroup_iff]
    constructor
    · simpa only [Matrix.transpose_transpose] using
        (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hout.1
    · simpa only [Matrix.det_transpose] using hout.2
  exact Submonoid.mul_mem _ houtT p.innerRot.property

def _root_.MatrixPose.InSnubFundamentalDomain (p : MatrixPose) : Prop :=
  InFundamentalDomain p.relativeRotation

/-- Every normalized matrix pose has a bounded rational relative-rotation
coordinate triple. -/
theorem MatrixPose.exists_bounded_relative_cayley
    (p : MatrixPose) (hfund : p.InSnubFundamentalDomain) :
    ∃ x ∈ Set.Icc (-2 : ℝ) 2,
      ∃ y ∈ Set.Icc (-2 : ℝ) 2,
      ∃ z ∈ Set.Icc (-2 : ℝ) 2,
        x ^ 2 + y ^ 2 + z ^ 2 ≤ 3 ∧
          p.relativeRotation = cayleyMatrix x y z :=
  exists_bounded_cayley_of_inFundamentalDomain p.relativeRotation
    (relativeRotation_mem_SO3 p) hfund

/-- After fixing an outer symmetry, a further inner symmetry selects the
relative fundamental-domain representative. -/
theorem exists_inner_symmetry_inFundamentalDomain
    (p : MatrixPose) (outerSymmetry : VertexIndex) :
    ∃ innerSymmetry : VertexIndex,
      (p.rightSnubSymmetries innerSymmetry outerSymmetry).InSnubFundamentalDomain := by
  let R := (p.outerRot.val * symmetryMatrix outerSymmetry)ᵀ *
    (p.innerRot.val * symmetryMatrix outerSymmetry)
  obtain ⟨h, hh⟩ := exists_mul_symmetry_inFundamentalDomain R
  refine ⟨symmetryAction outerSymmetry h, ?_⟩
  have hinner : symmetryMatrix (symmetryAction outerSymmetry h) =
      symmetryMatrix outerSymmetry * symmetryMatrix h :=
    (symmetryMatrix_mul_symmetryMatrix outerSymmetry h).symm
  simpa only [R, MatrixPose.InSnubFundamentalDomain,
    MatrixPose.relativeRotation, MatrixPose.rightSnubSymmetries,
    MulMemClass.coe_mul, symmetry, hinner, Matrix.transpose_mul,
    Matrix.mul_assoc] using hh

private theorem Rz_transpose_mul_self (δ : ℝ) :
    (Rz_mat δ)ᵀ * Rz_mat δ = 1 :=
  (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp
    (MatrixPose.Rz_mat_mem_SO3 δ).1

/-- A common screen rotation leaves the relative rotation exactly unchanged. -/
theorem MatrixPose.relativeRotation_rotateBy (p : MatrixPose) (δ : ℝ) :
    (p.rotateBy δ).relativeRotation = p.relativeRotation := by
  simp only [MatrixPose.relativeRotation, MatrixPose.rotateBy,
    Matrix.transpose_mul]
  rw [Matrix.mul_assoc p.outerRot.valᵀ, ← Matrix.mul_assoc (Rz_mat δ)ᵀ,
    Rz_transpose_mul_self, Matrix.one_mul]

theorem MatrixPose.inFundamentalDomain_rotateBy_iff
    (p : MatrixPose) (δ : ℝ) :
    (p.rotateBy δ).InSnubFundamentalDomain ↔ p.InSnubFundamentalDomain := by
  rw [MatrixPose.InSnubFundamentalDomain,
    MatrixPose.InSnubFundamentalDomain,
    MatrixPose.relativeRotation_rotateBy]

private theorem Rz_mul_rotRM_mat (δ θ φ α : ℝ) :
    Rz_mat δ * rotRM_mat θ φ α = rotRM_mat θ φ (δ + α) := by
  simp only [rotRM_mat, ← Matrix.mul_assoc,
    Bounding.Rz_mat_mul_Rz_mat]
  congr 3
  ring

/-- Rational box compatible with the relative-rotation fundamental domain.
The outer rotation retains the positive-octant reduction; the inner rotation
uses the standard bounded Euler domain because its symmetry has already been
chosen by the Dirichlet condition. -/
def fundamentalPoseInterval : PoseInterval ℝ :=
  PoseInterval.mk
    { θ₁ := -4, θ₂ := 0, φ₁ := 0, φ₂ := 0, α := -4 }
    { θ₁ := 4, θ₂ := 2, φ₁ := 4, φ₂ := 2, α := 4 }
    (by rw [Pose.le_iff]; norm_num)

/-- Every matrix pose has an equivalent translated Euler representative in
the bounded root box whose relative rotation lies in the exact snub-cube
Dirichlet fundamental domain. -/
theorem exists_fundamental_translated_pose (p : MatrixPose) :
    ∃ gi go : VertexIndex, ∃ δ : ℝ, ∃ q : Pose ℝ, ∃ offset : ℝ²,
      q ∈ fundamentalPoseInterval ∧
      q.matrixPoseWithOffset offset =
        (p.rightSnubSymmetries gi go).rotateBy δ ∧
      (q.matrixPoseWithOffset offset).InSnubFundamentalDomain := by
  obtain ⟨go, θo, φo, αo, hθo, hφo, _hαo, houter⟩ :=
    SO3_to_symmetry_reduced_rotRM_params p.outerRot
  obtain ⟨gi, hfund⟩ := exists_inner_symmetry_inFundamentalDomain p go
  have hinnerSO3 : p.innerRot.val * symmetryMatrix gi ∈
      Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ p.innerRot.property (symmetryMatrix_mem_SO3 gi)
  obtain ⟨θi, φi, αi, hθi, hφi, _hαi, hinner⟩ :=
    SO3_to_bounded_rotRM_params
      (p.innerRot.val * symmetryMatrix gi) hinnerSO3
  let δ := -αo
  obtain ⟨α, hα, hRzα⟩ := Bounding.Rz_mod_two_pi (δ + αi)
  let q : Pose ℝ := {
    θ₁ := θi, θ₂ := θo, φ₁ := φi, φ₂ := φo, α := α
  }
  let offset := rotR δ p.innerOffset
  have hq : q ∈ fundamentalPoseInterval := by
    rw [NonemptyInterval.mem_def, Pose.le_iff, Pose.le_iff]
    dsimp [q, fundamentalPoseInterval]
    have hpi2 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_le_four]
    have hpi4 := Real.pi_le_four
    exact ⟨
      ⟨by linarith [hθi.1], hθo.1, hφi.1, hφo.1,
        by linarith [hα.1]⟩,
      ⟨by linarith [hθi.2], hθo.2.trans hpi2,
        hφi.2.trans hpi4, hφo.2.trans hpi2,
        by linarith [hα.2]⟩⟩
  refine ⟨gi, go, δ, q, offset, hq, ?_⟩
  have hin : Rz_mat δ * (p.innerRot.val * symmetryMatrix gi) =
      rotRM_mat θi φi α := by
    rw [hinner, Rz_mul_rotRM_mat]
    unfold rotRM_mat
    rw [hRzα]
  have hout : Rz_mat δ * (p.outerRot.val * symmetryMatrix go) =
      rotRM_mat θo φo 0 := by
    rw [houter, Rz_mul_rotRM_mat]
    congr 1
    dsimp [δ]
    ring
  have heq : q.matrixPoseWithOffset offset =
      (p.rightSnubSymmetries gi go).rotateBy δ := by
    simp only [Pose.matrixPoseWithOffset, Pose.matrixPoseOfPose,
      MatrixPose.rotateBy, MatrixPose.rightSnubSymmetries]
    congr 1
    · apply Subtype.ext
      exact hin.symm
    · apply Subtype.ext
      exact hout.symm
  refine ⟨heq, ?_⟩
  rw [heq]
  exact (MatrixPose.inFundamentalDomain_rotateBy_iff _ _).mpr hfund

/-- It suffices to exclude translated Euler poses in the bounded Dirichlet
root.  This is the normalization bridge used by a prunable solution tree. -/
theorem no_matrixPose_of_no_fundamental_translated_pose
    (h : ¬ ∃ q ∈ fundamentalPoseInterval, ∃ offset : ℝ²,
      (q.matrixPoseWithOffset offset).InSnubFundamentalDomain ∧
      RupertPose (q.matrixPoseWithOffset offset)
        normalizedExactPolyhedron.hull) :
    ¬ ∃ p : MatrixPose,
      RupertPose p normalizedExactPolyhedron.hull := by
  rintro ⟨p, hp⟩
  obtain ⟨gi, go, δ, q, offset, hq, heq, hfund⟩ :=
    exists_fundamental_translated_pose p
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
