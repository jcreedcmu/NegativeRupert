module

public import Noperthedron.SnubCube.LocalRigidity

@[expose] public section


/-!
# Axis-free local rigidity at the identity stratum

This is the shape-independent specialization of the balanced finite-rotation
argument.  It needs no polyhedron symmetry: the same supporting vertex is
tracked on the inner and outer copies.  A finite family of balanced support
triples covers the unknown relative-rotation axis, while a perturbation budget
allows the outer viewing direction to range over a box.

The elementary outer-lift and first-variation definitions currently live in
the snub-cube local-geometry module.  They are already polymorphic in the
vertices and are reused here; a later mechanical refactor can move them into
this namespace without changing the theorem statement.
-/

namespace Noperthedron.BalancedSupport

open scoped RealInnerProductSpace

/-- Division-free local-angle bound for an ordinary identity-stratum box.
Unlike the symmetry-specialized form, this uses the unadjusted relative
rotation and is therefore shape-independent. -/
theorem AxisAngle.ratio_of_identity_pose_box
    (p center : Pose ℝ) (offset centerOffset : ℝ²)
    (a : AxisAngle ((relativeRotation
      (p.matrixPoseWithOffset offset)).val.toEuclideanLin.toContinuousLinearMap))
    (c r : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hcenter :
      relativeRotation (center.matrixPoseWithOffset centerOffset) = 1)
    (hbox :
      |p.α - center.α| + |p.φ₁ - center.φ₁| + |p.θ₁ - center.θ₁| +
          (|p.φ₂ - center.φ₂| + |p.θ₂ - center.θ₂|) ≤ r)
    (hsmall : r ^ 2 * (1 + c ^ 2) ≤ 4 * c ^ 2) :
    1 - Real.cos a.angle ≤ |Real.sin a.angle| * c := by
  apply a.ratio_of_norm_bound c r hc hr
  · have h := Noperthedron.SnubCube.norm_relativeRotation_matrixPoseWithOffset_sub_le
      p center offset centerOffset
    have hone : Noperthedron.SnubCube.so3CLM (1 : SO3) = 1 := by
      ext v
      simp [Noperthedron.SnubCube.so3CLM]
    rw [hcenter, hone] at h
    exact h.trans hbox
  · exact hsmall

/-- A perturbation-stable family of balanced certificates rules out a pose
near the identity relative-rotation stratum for an arbitrary polyhedron. -/
theorem not_rupertPose_of_identity_axisFree_certificates_of_cover_perturbation
    {ι J κ : Type} [Fintype ι] [Fintype J] [Nonempty J]
    [Fintype κ] [Nonempty κ]
    (poly : Polyhedron ι ℝ³) (p : MatrixPose)
    (a : AxisAngle
      ((relativeRotation p).val.toEuclideanLin.toContinuousLinearMap))
    (index : J → κ → ι)
    (weight : J → κ → ℝ) (direction : J → κ → ℝ²)
    (A normalizedA centerNormalizedA : J → ℝ³) (B : J → ℝ)
    (c δ : ℝ)
    (hB : ∀ j, 0 < B j)
    (hA : ∀ j, A j = B j • normalizedA j)
    (hcover : ∀ axis : ℝ³, ‖axis‖ = 1 →
      ∃ j, c + δ ≤ ⟪axis, centerNormalizedA j⟫)
    (hmove : ∀ j, ‖normalizedA j - centerNormalizedA j‖ ≤ δ)
    (hA_eq : ∀ j, A j = Noperthedron.SnubCube.firstVariationVector p
      (weight j) (direction j) (fun i => poly.v (index j i)))
    (hB_bound : ∀ j, ∑ i, weight j i *
      (‖direction j i‖ * ‖poly.v (index j i)‖) ≤ B j)
    (hratio : 1 - Real.cos a.angle ≤ |Real.sin a.angle| * c)
    (hdirection : ∀ j i, direction j i ≠ 0)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hweight_pos : ∀ j, ∃ i, 0 < weight j i)
    (hbalance : ∀ j, ∑ i, weight j i • direction j i = 0)
    (hsupport : ∀ j i k,
      ⟪direction j i, outerProjectionLinear p (poly.v k)⟫ ≤
        ⟪direction j i, outerProjectionLinear p (poly.v (index j i))⟫) :
    ¬ RupertPose p poly.hull := by
  obtain ⟨j, hj⟩ :=
    exists_axis_certificate_dominating_remainder_of_cover_perturbation
      centerNormalizedA normalizedA A B c δ |Real.sin a.angle|
      (1 - Real.cos a.angle) (abs_nonneg _) hB hA hcover hmove hratio
      a.signedAxis a.signedAxis_norm
  apply not_rupertPose_of_axisAngle_certificate poly p a
    (index j) (weight j) (direction j)
    (hdirection j) (hweight j) (hweight_pos j) (hbalance j) (hsupport j)
  have hremainder :
      (1 - Real.cos a.angle) *
          (∑ i, weight j i * (‖direction j i‖ * ‖poly.v (index j i)‖)) ≤
        (1 - Real.cos a.angle) * B j :=
    mul_le_mul_of_nonneg_left (hB_bound j)
      (sub_nonneg.mpr (Real.cos_le_one a.angle))
  rw [Noperthedron.SnubCube.axisAngle_weighted_first_identity a p
    (weight j) (direction j) (fun i => poly.v (index j i))]
  rw [← hA_eq j]
  exact hremainder.trans hj

end Noperthedron.BalancedSupport

end
