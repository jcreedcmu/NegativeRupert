module

public import Noperthedron.PoseClasses
public import Noperthedron.Basic

@[expose] public section


structure Pose (R : Type) : Type where
  θ₁ : R
  θ₂ : R
  φ₁ : R
  φ₂ : R
  α : R
deriving DecidableEq, Repr

instance {R : Type} [ToString R] : ToString (Pose R) where
  toString p := s!"\{θ₁ := {p.θ₁}, θ₂ := {p.θ₂}, φ₁ := {p.φ₁}, φ₂ := {p.φ₂}, α := {p.α}}"

noncomputable
instance : PoseLike (Pose ℝ) where
  inner vp := (rotRM vp.θ₁ vp.φ₁ vp.α).toAffineMap
  outer vp := (rotRM vp.θ₂ vp.φ₂ 0).toAffineMap

namespace Pose

/-- Bijection between `Pose` and `Fin 5 → ℝ`, used to transfer
the (sup-norm) `MetricSpace` instance from the Pi type. -/
def equivPi {R : Type} : Pose R ≃ (Fin 5 → R) where
  toFun p := ![p.θ₁, p.θ₂, p.φ₁, p.φ₂, p.α]
  invFun f := ⟨f 0, f 1, f 2, f 3, f 4⟩
  left_inv p := by cases p; rfl
  right_inv f := by ext i; fin_cases i <;> rfl

/-- Sup-norm transferred from `Fin 5 → R`. -/
instance {R} [MetricSpace R] : MetricSpace (Pose R) :=
  MetricSpace.induced equivPi equivPi.injective inferInstance

instance {R} [PartialOrder R] : PartialOrder (Pose R) := PartialOrder.lift equivPi equivPi.injective

lemma le_iff {R} [PartialOrder R] (p q : Pose R) :
    p ≤ q ↔ p.θ₁ ≤ q.θ₁ ∧ p.θ₂ ≤ q.θ₂ ∧ p.φ₁ ≤ q.φ₁ ∧ p.φ₂ ≤ q.φ₂ ∧ p.α ≤ q.α := by
  show equivPi p ≤ equivPi q ↔ _
  rw [Pi.le_def]
  refine ⟨fun h => ⟨h 0, h 1, h 2, h 3, h 4⟩, ?_⟩
  rintro ⟨h1, h2, h3, h4, h5⟩ i
  fin_cases i <;> assumption

instance {R} [PartialOrder R] [DecidableLE R] : DecidableLE (Pose R) :=
  fun p q => decidable_of_iff _ (le_iff p q).symm

lemma mem_closedBall_iff {R} [MetricSpace R] {p q : Pose R} {ε : ℝ} :
    p ∈ Metric.closedBall q ε ↔
      dist p.θ₁ q.θ₁ ≤ ε ∧ dist p.θ₂ q.θ₂ ≤ ε ∧
      dist p.φ₁ q.φ₁ ≤ ε ∧ dist p.φ₂ q.φ₂ ≤ ε ∧ dist p.α q.α ≤ ε := by
  rw [Metric.mem_closedBall,
      show dist p q = dist (equivPi p) (equivPi q) from rfl,
      dist_pi_le_iff']
  refine ⟨fun h => ?_, ?_⟩
  · exact ⟨h 0, h 1, h 2, h 3, h 4⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩ i
    fin_cases i <;> assumption

end Pose

namespace Pose

-- Some convenience functions for doing rotations with dot notation
-- Maybe the rotations in basic could be inlined here? It depends on whether
-- we actually use them not in the context of a Pose.

noncomputable
def rotM₁ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotM (p.θ₁) (p.φ₁)
noncomputable
def rotM₂ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotM (p.θ₂) (p.φ₂)
noncomputable
def rotR (p : Pose ℝ) : ℝ² →L[ℝ] ℝ² := _root_.rotR (p.α)
noncomputable
def vecX₁ (p : Pose ℝ) : ℝ³ := vecX (p.θ₁) (p.φ₁)
noncomputable
def vecX₂ (p : Pose ℝ) : ℝ³ := vecX (p.θ₂) (p.φ₂)

noncomputable
def rotM₁θ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθ (p.θ₁) (p.φ₁)
noncomputable
def rotM₂θ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθ (p.θ₂) (p.φ₂)
noncomputable
def rotM₁φ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMφ (p.θ₁) (p.φ₁)
noncomputable
def rotM₂φ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMφ (p.θ₂) (p.φ₂)
noncomputable
def rotR' (p : Pose ℝ) : ℝ² →L[ℝ] ℝ² := _root_.rotR' (p.α)

noncomputable
def rotM₁θθ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθθ (p.θ₁) (p.φ₁)
noncomputable
def rotM₁θφ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθφ (p.θ₁) (p.φ₁)
noncomputable
def rotM₁φφ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMφφ (p.θ₁) (p.φ₁)
noncomputable
def rotM₂θθ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθθ (p.θ₂) (p.φ₂)
noncomputable
def rotM₂θφ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMθφ (p.θ₂) (p.φ₂)
noncomputable
def rotM₂φφ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := rotMφφ (p.θ₂) (p.φ₂)

noncomputable
def inner (p : Pose ℝ) : ℝ³ →ᵃ[ℝ] ℝ² := innerProj p
noncomputable
def outer (p : Pose ℝ) : ℝ³ →ᵃ[ℝ] ℝ² := outerProj p


inductive equiv {α : Type} [PoseLike α] (p1 p2 : α) : Prop where
  | on_the_nose : innerShadow p1 = innerShadow p2 ∧ outerShadow p1 = outerShadow p2 → equiv p1 p2
  | off_by_neg : innerShadow p1 = -innerShadow p2 ∧ outerShadow p1 = -outerShadow p2 → equiv p1 p2


def innerParams (p : Pose ℝ) : ℝ³ := !₂[p.α, p.θ₁, p.φ₁]

def outerParams (p : Pose ℝ) : ℝ² := !₂[p.θ₂, p.φ₂]

lemma p_outer_eq_outer_shadow (p : Pose ℝ) (S : Set ℝ³) : p.outer '' S  = outerShadow p S := by
  simp only [Pose.outer, outerProj, outerShadow]
  ext v
  simp

lemma proj_rm_eq_m (θ φ : ℝ) (v : ℝ³) :
    proj_xyL (rotRM θ φ 0 v) = rotM θ φ v := by
  change (proj_xyL ∘ rotRM θ φ 0) v = rotM θ φ v
  rw [projxy_rotRM_eq_rotprojRM]
  change ((_root_.rotR 0) ∘L rotM θ φ) v = rotM θ φ v
  rw [AddChar.map_zero_eq_one]
  rfl

/--
If we have a convex polyhedron with p being a pose witness of the
rupert property, then in particular every vertex in the "inner"
transformation lies in the convex hull of the vertices under the
"outer" transformation.
-/
theorem is_rupert_imp_inner_in_outer (p : Pose ℝ)
    (poly : Finset ℝ³)
    (h_rupert : RupertPose p (convexHull ℝ poly)) (v : ℝ³) (hv : v ∈ poly) :
     p.inner v ∈ convexHull ℝ (p.outer '' poly) := by
  simp only [RupertPose] at h_rupert
  grw [← subset_closure, interior_subset] at h_rupert
  simp only [Pose.inner]
  have : v ∈ convexHull ℝ poly := by rw [mem_convexHull_iff]; intro _ a _; exact a hv
  rw [← AffineMap.image_convexHull p.outer poly, p_outer_eq_outer_shadow]
  refine h_rupert ?_
  simp only [innerShadow, Set.mem_ofPred_eq, innerProj]
  use v
  simpa

lemma inner_shadow_eq_img_inner (p : Pose ℝ) (S : Set ℝ³) :
    innerShadow p S = p.inner '' S := by
  rfl

lemma outer_shadow_eq_img_outer (p : Pose ℝ) (S : Set ℝ³) :
    outerShadow p S = p.outer '' S := by
  rfl

lemma pose_on_the_nose {p1 p2 : Pose ℝ} : p1.inner = p2.inner ∧ p1.outer = p2.outer → equiv p1 p2 := by
  rintro ⟨h1, h2⟩
  refine .on_the_nose ⟨?_, ?_⟩ <;>
  · ext1 S; simp [inner_shadow_eq_img_inner, outer_shadow_eq_img_outer, h1, h2]

lemma pose_off_by_neg {p1 p2 : Pose ℝ} : p1.inner = -p2.inner ∧ p1.outer = -p2.outer → equiv p1 p2 := by
  rintro ⟨h1, h2⟩
  refine .off_by_neg ⟨?_, ?_⟩ <;>
  · ext1 S; simp [inner_shadow_eq_img_inner, outer_shadow_eq_img_outer, h1, h2]; aesop

lemma inner_eq_RM (p : Pose ℝ)  :
    p.inner = (p.rotR ∘ p.rotM₁) := by
  ext1 v
  change (proj_xyL ∘ rotRM p.θ₁ p.φ₁ p.α) v = p.rotR (p.rotM₁ v)
  rw [projxy_rotRM_eq_rotprojRM]
  rfl

lemma outer_eq_M (p : Pose ℝ) : p.outer = ⇑p.rotM₂ := by
  ext1 v
  exact proj_rm_eq_m p.θ₂ p.φ₂ v

lemma inner_shadow_eq_RM (p : Pose ℝ) (S : Set ℝ³) :
    innerShadow p S = (p.rotR ∘L p.rotM₁) '' S := by
  rw [inner_shadow_eq_img_inner]
  refine Set.image_congr ?_
  intro v _
  rw [inner_eq_RM]
  rfl

lemma outer_shadow_eq_M (p : Pose ℝ) (S : Set ℝ³) :
    outerShadow p S = p.rotM₂ '' S := by
  rw [outer_shadow_eq_img_outer]
  refine Set.image_congr ?_
  intro v _
  rw [outer_eq_M]

lemma poselike_inner_eq_proj_inner (p : Pose ℝ) :
    proj_xyL ∘ PoseLike.inner p = p.inner := by
  ext v
  simp only [PoseLike.inner, Pose.inner, innerProj, AffineMap.coe_comp,
    LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe, Function.comp_apply]

lemma poselike_outer_eq_proj_outer (p : Pose ℝ) :
    proj_xyL ∘ PoseLike.outer p = p.outer := by
  ext v
  simp only [PoseLike.outer, Pose.outer, outerProj, AffineMap.coe_comp,
    LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe, Function.comp_apply]

lemma equiv_rupert_imp_rupert {P : Type} [PoseLike P] {p1 p2 : P} {S : Set ℝ³} (e : equiv p1 p2) (r : RupertPose p1 S) :
    RupertPose p2 S := by
  match e with
  | .on_the_nose e =>
    simp only [RupertPose, innerShadow, outerShadow]
    obtain ⟨e_inner, e_outer⟩ := e
    calc
      closure (innerShadow p2 S)
      _ = closure (innerShadow p1 S) := by rw [e_inner]
      _ ⊆ interior (outerShadow p1 S) := r
      _ = interior (outerShadow p2 S) := by rw [e_outer]
  | .off_by_neg e =>
    simp only [RupertPose, innerShadow, outerShadow]
    obtain ⟨e_inner, e_outer⟩ := e
    calc
      closure (innerShadow p2 S)
      _ = closure (-((-innerShadow p2) S)) := by simp
      _ = closure (-(innerShadow p1 S)) := by rw [e_inner]
      _ = -closure ((innerShadow p1 S)) := by rw [neg_closure]
      _ ⊆ -interior (outerShadow p1 S) := by rw [Set.neg_subset_neg]; exact r
      _ = interior (-(outerShadow p1 S)) := (Homeomorph.neg ℝ²).preimage_interior _
      _ = interior (-((-outerShadow p2) S)) := by rw [e_outer]
      _ = interior (((outerShadow p2) S)) := by simp

lemma matrix_rm_eq_imp_pose_equiv {p q : Pose ℝ} (rme : p.rotR ∘ p.rotM₁ = q.rotR ∘ q.rotM₁)
    (rm2 : p.rotM₂ = q.rotM₂) : equiv p q := by
  refine pose_on_the_nose ?_
  constructor
  · ext1 v
    rw [inner_eq_RM p, inner_eq_RM q, rme]
  · ext1 v
    rw [outer_eq_M p, outer_eq_M q, rm2]

lemma matrix_rm_eq_neg_imp_pose_equiv {p q : Pose ℝ} (rme : p.rotR ∘ p.rotM₁ = -(q.rotR ∘ q.rotM₁))
    (rm2 : p.rotM₂ = -q.rotM₂) : equiv p q := by
  refine pose_off_by_neg ?_
  constructor
  · ext1 v
    change p.inner v = -(q.inner v)
    rw [inner_eq_RM p, inner_eq_RM q, rme]
    rfl
  · ext1 v
    change p.outer v = -(q.outer v)
    rw [outer_eq_M p, outer_eq_M q, rm2]
    rfl

lemma matrix_eq_imp_pose_equiv {p q : Pose ℝ} (re : p.rotR = q.rotR)
    (rm1 : p.rotM₁ = q.rotM₁) (rm2 : p.rotM₂ = q.rotM₂) : equiv p q :=
  matrix_rm_eq_imp_pose_equiv (by rw [re, rm1]) rm2

lemma matrix_neg_imp_pose_equiv {p q : Pose ℝ} (re : p.rotR = -q.rotR)
    (rm1 : p.rotM₁ = q.rotM₁) (rm2 : p.rotM₂ = -q.rotM₂) : equiv p q := by
  exact matrix_rm_eq_neg_imp_pose_equiv (by rw [re, rm1]; ext v; rfl) rm2

end Pose

end
