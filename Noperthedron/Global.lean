module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Noperthedron.PoseInterval
public import Noperthedron.Global.Basic
public import Noperthedron.Global.BoundedPartialsControlDifference
public import Noperthedron.Global.RotationPartials
public import Noperthedron.Vertices.Exact

@[expose] public section


open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private lemma f_le_max {n : ℕ} {V : Finset (E n)} (Vne : V.Nonempty) (w : E n → ℝ) (hw1 : ∀ y ∈ V, 0 ≤ w y)
      (f : E n →ₗ[ℝ] ℝ) :
  ↑(∑ x ∈ V, w x * f x) ≤ ∑ x ∈ V, ↑(w x) * (Finset.image (⇑f) V).max' (by simp [Finset.image_nonempty]; exact Vne) := by
  have fx_le_fvmax (x : V) : f x ≤ (Finset.image f V).max' (by simp [Finset.image_nonempty]; exact Vne) := by
    refine Finset.le_max' _ _ ?_
    simp only [Finset.mem_image]
    exact ⟨x, Finset.coe_mem x, rfl⟩
  refine Finset.sum_le_sum ?_
  intro x hx
  grw [fx_le_fvmax ⟨x, hx⟩]
  exact hw1 x hx

theorem finset_hull_linear_max {n : ℕ} {V : Finset (E n)} (Vne : V.Nonempty)
    (S : E n) (hs : S ∈ convexHull ℝ V) (f : E n →ₗ[ℝ] ℝ) :
    f S ≤ (V.image f).max' (Finset.image_nonempty.mpr Vne) := by
  have Vine : (V.image f).Nonempty := by simp [Finset.image_nonempty]; exact Vne
  have hs_orig := hs
  rw [Finset.convexHull_eq] at hs
  obtain ⟨w, hw1, hw2, hw3⟩ := hs
  calc
    (f S) = (f (∑ i ∈ V, w i • id i)) := by rw [← hw3, Finset.centerMass_eq_of_sum_1 V id hw2]
    _       = ∑ x ∈ V, w x * f x := by simp
    _       ≤ ∑ x ∈ V, w x * ((Finset.image f V).max' Vine) := f_le_max Vne w hw1 f
    _       = (∑ x ∈ V, w x) * ((Finset.image f V).max' Vine) := by rw [← Finset.sum_mul]
    _       = (Finset.image f V).max' _ := by rw [hw2]; simp

/- [SY25] Lemma 18 -/
theorem hull_scalar_prod {n : ℕ} (V : Finset (E n)) (Vne : V.Nonempty)
    (S : E n) (hs : S ∈ convexHull ℝ V) (w : E n) :
    ⟪w, S⟫ ≤ Finset.max' (V.image (⟪w, ·⟫)) (Finset.image_nonempty.mpr Vne) := by
  exact finset_hull_linear_max Vne S hs (InnerProductSpace.toDual ℝ (E n) w |>.toLinearMap)

-- rotproj_inner, rotproj_outer, rotation_partials_exist, rotation_partials_exist_outer
-- are now imported from Noperthedron.Global.Definitions
-- (via Noperthedron.Global.RotationPartials)

-- rotation_third_partials_bounded, rotation_third_partials_bounded_outer ([SY25] Lemma 19) are
-- now imported from Noperthedron.Global.RotationPartials (via SecondPartialInner/SecondPartialOuter)

/--
A measure of how far an inner-shadow vertex S can "stick out".

Second-order anisotropic version: per-axis radii `εα`, `εθ`, `εφ` weight the
first partials, the exact second partials at the center (with multiplicities
from the symmetric 3×3 table), and a `(εα+εθ+εφ)³/6` Lagrange remainder from
the bounded third partials. On the diagonal `εα = εθ = εφ = ε` this recovers
the previous isotropic penalty with remainder `(3ε)³/6 = 9ε³/2`. [SY25] uses
the weaker first-order penalty `9ε²/2`.
-/
noncomputable
def G (p : Pose ℝ) (εα εθ εφ : ℝ) (S : ℝ³) (w : ℝ²) : ℝ :=
  ⟪p.inner S, w⟫ - (εα * |⟪p.rotR' (p.rotM₁ S), w⟫| + εθ * |⟪p.rotR (p.rotM₁θ S), w⟫|
      + εφ * |⟪p.rotR (p.rotM₁φ S), w⟫|
  + 1 / 2 * (εα ^ 2 * |⟪p.rotR (p.rotM₁ S), w⟫|
      + 2 * (εα * εθ) * |⟪p.rotR' (p.rotM₁θ S), w⟫| + 2 * (εα * εφ) * |⟪p.rotR' (p.rotM₁φ S), w⟫|
      + εθ ^ 2 * |⟪p.rotR (p.rotM₁θθ S), w⟫| + 2 * (εθ * εφ) * |⟪p.rotR (p.rotM₁θφ S), w⟫|
      + εφ ^ 2 * |⟪p.rotR (p.rotM₁φφ S), w⟫|)
  + (εα + εθ + εφ) ^ 3 / 6)

/--
A measure of how far an outer-shadow vertex P can "reach" along w.

Second-order anisotropic version with per-axis radii `εθ`, `εφ`; the Lagrange
remainder is `(εθ+εφ)³/6` (on the diagonal `εθ = εφ = ε`, `(2ε)³/6 = 4ε³/3`).
-/
noncomputable
def H (p : Pose ℝ) (εθ εφ : ℝ) (w : ℝ²) (P : ℝ³) : ℝ :=
  ⟪p.rotM₂ P, w⟫ + εθ * |⟪p.rotM₂θ P, w⟫| + εφ * |⟪p.rotM₂φ P, w⟫|
  + 1 / 2 * (εθ ^ 2 * |⟪p.rotM₂θθ P, w⟫| + 2 * (εθ * εφ) * |⟪p.rotM₂θφ P, w⟫|
      + εφ ^ 2 * |⟪p.rotM₂φφ P, w⟫|)
  + (εθ + εφ) ^ 3 / 6

/--
A measure of how far all of the outer-shadow vertices can "reach" along w.
-/
noncomputable
def maxH {ι : Type} [Fintype ι] [ne : Nonempty ι]
    (p : Pose ℝ) (poly : GoodPoly ι) (εθ εφ : ℝ) (w : ℝ²) : ℝ :=
  Finset.image (H p εθ εφ w ∘ poly.vertices.v) Finset.univ |>.max' <| by
    simp only [Finset.image_nonempty]
    exact Finset.univ_nonempty_iff.mpr ne

/--
A compact way of saying "the pose satisfies the global theorem precondition at
per-axis widths `εα εθ₁ εφ₁ εθ₂ εφ₂`". We require the index `Si` of some
inner-shadow vertex of the polyhedron, and a covector w meant to express the
direction we're projecting ℝ² → ℝ to find that the vertex "sticks out too far"
compared to all the outer-shadow vertices P (which the calculation of H
iterates over) in the polygon that lies in ℝ².
-/
structure GlobalTheoremPrecondition {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (p : Pose ℝ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ) : Type where
  Si : ι
  w : ℝ²
  w_unit : ‖w‖ = 1
  exceeds : G p εα εθ₁ εφ₁ (poly.vertices.v Si) w > maxH p poly εθ₂ εφ₂ w

/-- The inner-shadow vertex singled out by the precondition. -/
noncomputable
def GlobalTheoremPrecondition.S
    {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι} {p : Pose ℝ} {εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ}
    (hp : GlobalTheoremPrecondition poly p εα εθ₁ εφ₁ εθ₂ εφ₂) : ℝ³ :=
  poly.vertices.v hp.Si

noncomputable
def GlobalTheoremPrecondition.Sval
    {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι} {p : Pose ℝ} {εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ}
    (hp : GlobalTheoremPrecondition poly p εα εθ₁ εφ₁ εθ₂ εφ₂) (q : Pose ℝ) : ℝ :=
    ⟪hp.w, q.inner hp.S⟫

theorem GlobalTheoremPrecondition.norm_S_le_one
    {ι : Type} [Fintype ι] [Nonempty ι]
    {poly : GoodPoly ι} {p : Pose ℝ} {εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ}
    (hp : GlobalTheoremPrecondition poly p εα εθ₁ εφ₁ εθ₂ εφ₂) : ‖hp.S‖ ≤ 1 :=
  poly.vertex_radius_le_one hp.Si

noncomputable
def imgInner (p : Pose ℝ) (V : Finset ℝ³) (w : ℝ²) : Finset ℝ :=
  V.image fun P => ⟪w, p.inner P⟫

noncomputable
def maxInner {ι : Type} [Fintype ι] [ne : Nonempty ι]
    (p : Pose ℝ) (poly : GoodPoly ι) (w : ℝ²) : ℝ :=
  (imgInner p (Finset.image poly.vertices.v Finset.univ) w).max' (by
    simp only [imgInner, Finset.image_nonempty, Finset.univ_nonempty_iff]; exact ne)

noncomputable
def imgOuter (p : Pose ℝ) (V : Finset ℝ³) (w : ℝ²) : Finset ℝ :=
  V.image fun P => ⟪w, p.outer P⟫

noncomputable
def maxOuter {ι : Type} [Fintype ι] [ne : Nonempty ι]
    (p : Pose ℝ) (poly : GoodPoly ι) (w : ℝ²) : ℝ :=
  (imgOuter p (Finset.image poly.vertices.v Finset.univ) w).max' (by
    simp only [imgOuter, Finset.image_nonempty, Finset.univ_nonempty_iff]; exact ne)

/--
This is where we use hull_scalar_prod. The text in [SY25] this corresponds to is:

"As noted before, Rupert’s condition and Lemma 18 imply in particular that
max_{P} ⟪ R(α) M(θ₁, φ₁), P, w ⟫ < max_{P} ⟪ M(θ₂, φ₂), P, w ⟫"
-/
private lemma hull_eq_convexHull_finset {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) :
    poly.hull = convexHull ℝ ↑(Finset.image poly.vertices.v Finset.univ) := by
  simp only [GoodPoly.hull, Polyhedron.hull, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  congr 1

theorem global_theorem_le_reasoning {ι : Type} [Fintype ι] [ne : Nonempty ι] (p : Pose ℝ)
    (poly : GoodPoly ι)
    (h_rupert : RupertPose p poly.hull) (w : ℝ²) :
    maxInner p poly w ≤ maxOuter p poly w
    := by
  let verts := Finset.image poly.vertices.v Finset.univ
  have verts_ne : verts.Nonempty := by
    simp only [verts, Finset.image_nonempty, Finset.univ_nonempty_iff]; exact ne
  have h_rupert' : RupertPose p (convexHull ℝ ↑verts) := by
    rwa [← hull_eq_convexHull_finset]
  simp only [maxInner]
  refine Finset.max'_le _ _ _ ?_
  intro y hy
  simp only [maxOuter, imgOuter]
  simp only [imgInner] at hy
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  change ⟪w, p.inner v⟫ ≤ (verts.image (⟪w, p.outer ·⟫)).max' _
  convert_to ⟪w, p.inner v⟫ ≤ ((verts.image p.outer).image (⟪w, ·⟫)).max' (by
      simp only [Finset.image_nonempty]; exact verts_ne)
  · simp [Finset.image_image]; rfl
  let S := p.inner v
  let V := verts.image p.outer
  have Vne : V.Nonempty := by simp only [V, Finset.image_nonempty]; exact verts_ne
  change ⟪w, S⟫ ≤ Finset.max' (V.image (⟪w, ·⟫)) _
  refine hull_scalar_prod V Vne S ?_ w
  simp only [Finset.coe_image, V, S]
  exact p.is_rupert_imp_inner_in_outer verts h_rupert' v hv

lemma rotproj_inner_pose_eq {S : ℝ³} {w : ℝ²} (p : Pose ℝ) : rotproj_inner S w p.innerParams = ⟪p.inner S, w⟫ := by
  simp only [rotproj_inner, Pose.inner, innerProj, PoseLike.inner, Pose.innerParams,
             Matrix.cons_val_zero, Matrix.cons_val, AffineMap.coe_comp,
             LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe, Function.comp_apply]
  change _ = ⟪(proj_xyL ∘L rotRM p.θ₁ p.φ₁ p.α) S, w⟫
  rw [← projxy_rotRM_eq_rotprojRM]
  rfl

-- Differentiable.rotprojRM, Differentiable.rotproj_inner, rotproj_inner', rotprojRM',
-- HasFDerivAt.rotproj_inner are now imported from Noperthedron.Global.RotationPartials.Rotproj

lemma partials_helper0 (pbar : Pose ℝ) (S : ℝ³) (w : ℝ²) :
    nth_partial 0 (rotproj_inner S w) pbar.innerParams =
    ⟪pbar.rotR' (pbar.rotM₁ S), w⟫ := by
  simp only [nth_partial, (HasFDerivAt.rotproj_inner pbar S w).fderiv]
  simp [rotproj_inner']

lemma partials_helper1 (pbar : Pose ℝ) (S : ℝ³) (w : ℝ²) :
    nth_partial 1 (rotproj_inner S w) pbar.innerParams =
    ⟪pbar.rotR (pbar.rotM₁θ S), w⟫ := by
  simp only [nth_partial, (HasFDerivAt.rotproj_inner pbar S w).fderiv]
  simp [rotproj_inner']

lemma partials_helper2 (pbar : Pose ℝ) (S : ℝ³) (w : ℝ²) :
    nth_partial 2 (rotproj_inner S w) pbar.innerParams =
    ⟪pbar.rotR (pbar.rotM₁φ S), w⟫ := by
  simp only [nth_partial, (HasFDerivAt.rotproj_inner pbar S w).fderiv]
  simp [rotproj_inner']

lemma partials_helper3 (pbar : Pose ℝ) (P : ℝ³) (w : ℝ²) :
    nth_partial 0 (rotproj_outer P w) pbar.outerParams = ⟪pbar.rotM₂θ P, w⟫ := by
  unfold nth_partial rotproj_outer
  rw [fderiv_inner_const _ w pbar.outerParams (EuclideanSpace.single 0 1)
    ((Differentiable.rotM_outer P).differentiableAt)]
  congr 1
  rw [(HasFDerivAt.rotM_outer pbar P).fderiv]
  ext i; simp [Pose.rotM₂θ]

lemma partials_helper4 (pbar : Pose ℝ) (P : ℝ³) (w : ℝ²) :
    nth_partial 1 (rotproj_outer P w) pbar.outerParams = ⟪pbar.rotM₂φ P, w⟫ := by
  unfold nth_partial rotproj_outer
  rw [fderiv_inner_const _ w pbar.outerParams (EuclideanSpace.single 1 1)
    ((Differentiable.rotM_outer P).differentiableAt)]
  congr 1
  rw [(HasFDerivAt.rotM_outer pbar P).fderiv]
  ext i; simp [Pose.rotM₂φ]

/-- The ε-weighted sum of first-partial magnitudes appearing in `G` equals the
ε-weighted sum of first-partial magnitudes of `rotproj_inner S w` at the
center. -/
lemma partials_helper (pbar : Pose ℝ) (S : ℝ³) (w : ℝ²) (εα εθ₁ εφ₁ : ℝ) :
    εα * |⟪pbar.rotR' (pbar.rotM₁ S), w⟫| + εθ₁ * |⟪pbar.rotR (pbar.rotM₁θ S), w⟫|
      + εφ₁ * |⟪pbar.rotR (pbar.rotM₁φ S), w⟫|
    = ∑ i, ![εα, εθ₁, εφ₁] i * |nth_partial i (rotproj_inner S w) pbar.innerParams| := by
  rw [← partials_helper0 pbar S w, ← partials_helper1 pbar S w, ← partials_helper2 pbar S w,
    Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- Outer analog of `partials_helper`, with weights `εθ₂`, `εφ₂`. -/
lemma partials_helper_outer (pbar : Pose ℝ) (P : ℝ³) (w : ℝ²) (εθ₂ εφ₂ : ℝ) :
    εθ₂ * |⟪pbar.rotM₂θ P, w⟫| + εφ₂ * |⟪pbar.rotM₂φ P, w⟫| =
    ∑ i, ![εθ₂, εφ₂] i * |nth_partial i (rotproj_outer P w) pbar.outerParams| := by
  rw [← partials_helper3 pbar P w, ← partials_helper4 pbar P w, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

private lemma innerParams_0 (pbar : Pose ℝ) : pbar.innerParams.ofLp 0 = pbar.α := by
  simp [Pose.innerParams]
private lemma innerParams_1 (pbar : Pose ℝ) : pbar.innerParams.ofLp 1 = pbar.θ₁ := by
  simp [Pose.innerParams]
private lemma innerParams_2 (pbar : Pose ℝ) : pbar.innerParams.ofLp 2 = pbar.φ₁ := by
  simp [Pose.innerParams]
private lemma outerParams_0 (pbar : Pose ℝ) : pbar.outerParams.ofLp 0 = pbar.θ₂ := by
  simp [Pose.outerParams]
private lemma outerParams_1 (pbar : Pose ℝ) : pbar.outerParams.ofLp 1 = pbar.φ₂ := by
  simp [Pose.outerParams]

private lemma second_partials_key (pbar : Pose ℝ) (S : ℝ³) (w : ℝ²) (i j : Fin 3) :
    nth_partial i (nth_partial j (rotproj_inner S w)) pbar.innerParams =
      ⟪inner_second_partial_A pbar.α pbar.θ₁ pbar.φ₁ i j S, w⟫ := by
  rw [second_partial_rotproj_inner_eq S w pbar.innerParams i j,
    innerParams_0, innerParams_1, innerParams_2]

/-- The ε-weighted sum of second-partial magnitudes appearing in `G` equals the
ε-weighted 3×3 sum of second partials of `rotproj_inner S w` at the center. -/
lemma second_partials_helper (pbar : Pose ℝ) (S : ℝ³) (w : ℝ²) (εα εθ₁ εφ₁ : ℝ) :
    εα ^ 2 * |⟪pbar.rotR (pbar.rotM₁ S), w⟫|
      + 2 * (εα * εθ₁) * |⟪pbar.rotR' (pbar.rotM₁θ S), w⟫|
      + 2 * (εα * εφ₁) * |⟪pbar.rotR' (pbar.rotM₁φ S), w⟫|
      + εθ₁ ^ 2 * |⟪pbar.rotR (pbar.rotM₁θθ S), w⟫|
      + 2 * (εθ₁ * εφ₁) * |⟪pbar.rotR (pbar.rotM₁θφ S), w⟫|
      + εφ₁ ^ 2 * |⟪pbar.rotR (pbar.rotM₁φφ S), w⟫|
    = ∑ i, ∑ j, ![εα, εθ₁, εφ₁] i * ![εα, εθ₁, εφ₁] j *
        |nth_partial i (nth_partial j (rotproj_inner S w)) pbar.innerParams| := by
  simp only [second_partials_key]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  simp only [inner_second_partial_A, neg_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, inner_neg_left, abs_neg]
  simp only [Pose.rotR, Pose.rotR', Pose.rotM₁, Pose.rotM₁θ, Pose.rotM₁φ,
    Pose.rotM₁θθ, Pose.rotM₁θφ, Pose.rotM₁φφ]
  ring

private lemma second_partials_key_outer (pbar : Pose ℝ) (P : ℝ³) (w : ℝ²) (i j : Fin 2) :
    nth_partial i (nth_partial j (rotproj_outer P w)) pbar.outerParams =
      ⟪outer_second_partial_A pbar.θ₂ pbar.φ₂ i j P, w⟫ := by
  rw [show rotproj_outer P w = fun z : ℝ² => ⟪rotM (z.ofLp 0) (z.ofLp 1) P, w⟫ from rfl,
    second_partial_rotproj_outer_eq P w pbar.outerParams i j, outerParams_0, outerParams_1]

/-- Outer analog of `second_partials_helper`, with weights `εθ₂`, `εφ₂`. -/
lemma second_partials_helper_outer (pbar : Pose ℝ) (P : ℝ³) (w : ℝ²) (εθ₂ εφ₂ : ℝ) :
    εθ₂ ^ 2 * |⟪pbar.rotM₂θθ P, w⟫| + 2 * (εθ₂ * εφ₂) * |⟪pbar.rotM₂θφ P, w⟫|
      + εφ₂ ^ 2 * |⟪pbar.rotM₂φφ P, w⟫|
    = ∑ i, ∑ j, ![εθ₂, εφ₂] i * ![εθ₂, εφ₂] j *
        |nth_partial i (nth_partial j (rotproj_outer P w)) pbar.outerParams| := by
  simp only [second_partials_key_outer]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [outer_second_partial_A]
  simp only [Pose.rotM₂θθ, Pose.rotM₂θφ, Pose.rotM₂φφ]
  ring

/-- Evaluating `rotproj_outer` at a pose's outer parameters gives the projected
outer shadow. -/
lemma rotproj_outer_pose_eq (p : Pose ℝ) (P : ℝ³) (w : ℝ²) :
    rotproj_outer P w p.outerParams = ⟪p.rotM₂ P, w⟫ := by
  show ⟪rotM (p.outerParams.ofLp 0) (p.outerParams.ofLp 1) P, w⟫ = _
  rw [outerParams_0, outerParams_1]
  rfl

/--
Use the analytic bounds on rotations, Lemmas 19 and 20.
-/
lemma global_theorem_inequality_ii {ι : Type} [Fintype ι] [Nonempty ι]
    (pbar p : Pose ℝ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ)
    (hεα : 0 ≤ εα) (hεθ₁ : 0 ≤ εθ₁) (hεφ₁ : 0 ≤ εφ₁)
    (p_near_pbar : Pose.near pbar εα εθ₁ εφ₁ εθ₂ εφ₂ p)
    (poly : GoodPoly ι)
    (pc : GlobalTheoremPrecondition poly pbar εα εθ₁ εφ₁ εθ₂ εφ₂) :
    G pbar εα εθ₁ εφ₁ pc.S pc.w ≤ pc.Sval p := by
  have S_norm_le_one : ‖pc.S‖ ≤ 1 := pc.norm_S_le_one
  have hεv : ∀ i, 0 ≤ ![εα, εθ₁, εφ₁] i := by
    intro i
    fin_cases i
    · exact hεα
    · exact hεθ₁
    · exact hεφ₁
  have hdiffv : ∀ i : Fin 3,
      |pbar.innerParams.ofLp i - p.innerParams.ofLp i| ≤ ![εα, εθ₁, εφ₁] i := by
    obtain ⟨hθ₁, hφ₁, -, -, hα⟩ := p_near_pbar
    intro i
    simp only [Pose.innerParams, WithLp.ofLp_toLp]
    rw [abs_sub_comm]
    fin_cases i
    · exact hα
    · exact hθ₁
    · exact hφ₁
  have hz := bounded_partials_control_difference2
    (rotproj_inner pc.S pc.w) rotation_partials_exist
    pbar.innerParams p.innerParams ![εα, εθ₁, εφ₁] hεv hdiffv
    (rotation_third_partials_bounded pc.S pc.w_unit)
  rw [show ∑ i, ![εα, εθ₁, εφ₁] i = εα + εθ₁ + εφ₁ by simp [Fin.sum_univ_three],
    rotproj_inner_pose_eq pbar, rotproj_inner_pose_eq p] at hz
  simp only [G]
  refine sub_le_of_abs_sub_le_right ?_
  rw [show pc.Sval p = ⟪p.inner pc.S, pc.w⟫ from real_inner_comm _ _,
    partials_helper pbar pc.S pc.w εα εθ₁ εφ₁, second_partials_helper pbar pc.S pc.w εα εθ₁ εφ₁]
  have hcube : ‖pc.S‖ * (εα + εθ₁ + εφ₁) ^ 3 / 6 ≤ (εα + εθ₁ + εφ₁) ^ 3 / 6 := by
    nth_rewrite 2 [← one_mul ((εα + εθ₁ + εφ₁) ^ 3)]
    have : (0:ℝ) ≤ (εα + εθ₁ + εφ₁) ^ 3 := by positivity
    gcongr
  linarith

/--
Use the analytic bounds on rotations, Lemmas 19 and 20.
-/
lemma global_theorem_inequality_iv {ι : Type} [Fintype ι] [Nonempty ι]
    (pbar p : Pose ℝ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ)
    (hεθ₂ : 0 ≤ εθ₂) (hεφ₂ : 0 ≤ εφ₂)
    (p_near_pbar : Pose.near pbar εα εθ₁ εφ₁ εθ₂ εφ₂ p)
    (poly : GoodPoly ι)
    (pc : GlobalTheoremPrecondition poly pbar εα εθ₁ εφ₁ εθ₂ εφ₂) :
    maxOuter p poly pc.w ≤ maxH pbar poly εθ₂ εφ₂ pc.w := by
  -- First of all, we can relate these two maximums by relating
  -- their components.
  suffices h : ∀ i : ι,
      ⟪pc.w, p.outer (poly.vertices.v i)⟫ ≤ H pbar εθ₂ εφ₂ pc.w (poly.vertices.v i) by
    simp only [maxOuter, maxH, imgOuter]
    apply Finset.max'_le
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine le_trans (h i) ?_
    show (H pbar εθ₂ εφ₂ pc.w ∘ poly.vertices.v) i ≤ _
    exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  -- Now we're just considering a single polyhedron vertex
  intro i
  set P := poly.vertices.v i
  have P_norm_le_one : ‖P‖ ≤ 1 := poly.vertex_radius_le_one i
  have hεv : ∀ i, 0 ≤ ![εθ₂, εφ₂] i := by
    intro i
    fin_cases i
    · exact hεθ₂
    · exact hεφ₂
  have hdiffv : ∀ i : Fin 2,
      |pbar.outerParams.ofLp i - p.outerParams.ofLp i| ≤ ![εθ₂, εφ₂] i := by
    obtain ⟨-, -, hθ₂, hφ₂, -⟩ := p_near_pbar
    intro i
    simp only [Pose.outerParams, WithLp.ofLp_toLp]
    rw [abs_sub_comm]
    fin_cases i
    · exact hθ₂
    · exact hφ₂
  have hz := bounded_partials_control_difference2
    (rotproj_outer P pc.w) rotation_partials_exist_outer
    pbar.outerParams p.outerParams ![εθ₂, εφ₂] hεv hdiffv
    (rotation_third_partials_bounded_outer P pc.w_unit)
  rw [show ∑ i, ![εθ₂, εφ₂] i = εθ₂ + εφ₂ by simp [Fin.sum_univ_two],
    rotproj_outer_pose_eq pbar, rotproj_outer_pose_eq p] at hz
  simp only [H]
  rw [abs_sub_comm] at hz
  replace hz := sub_le_of_abs_sub_le_right hz
  rw [tsub_le_iff_right, ← partials_helper_outer pbar P pc.w εθ₂ εφ₂,
    ← second_partials_helper_outer pbar P pc.w εθ₂ εφ₂] at hz
  rw [show (⟪pc.w, p.outer P⟫ : ℝ) = ⟪p.rotM₂ P, pc.w⟫ by
      rw [Pose.outer_eq_M]; exact real_inner_comm _ _]
  have hcube : ‖P‖ * (εθ₂ + εφ₂) ^ 3 / 6 ≤ (εθ₂ + εφ₂) ^ 3 / 6 := by
    nth_rewrite 2 [← one_mul ((εθ₂ + εφ₂) ^ 3)]
    have : (0:ℝ) ≤ (εθ₂ + εφ₂) ^ 3 := by positivity
    gcongr
  linarith

/--
Here we run through the "sequence of inequalities [which yield] the desired contradiction"
-/
theorem global_theorem_gt_reasoning {ι : Type} [Fintype ι] [Nonempty ι]
    (pbar p : Pose ℝ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ)
    (hεα : 0 ≤ εα) (hεθ₁ : 0 ≤ εθ₁) (hεφ₁ : 0 ≤ εφ₁) (hεθ₂ : 0 ≤ εθ₂) (hεφ₂ : 0 ≤ εφ₂)
    (p_near_pbar : Pose.near pbar εα εθ₁ εφ₁ εθ₂ εφ₂ p)
    (poly : GoodPoly ι)
    (pc : GlobalTheoremPrecondition poly pbar εα εθ₁ εφ₁ εθ₂ εφ₂) :
    maxInner p poly pc.w > maxOuter p poly pc.w := by
  have sval_in_img_inner : pc.Sval p ∈ imgInner p (Finset.image poly.vertices.v Finset.univ) pc.w := by
    simp only [Finset.mem_image, imgInner, GlobalTheoremPrecondition.Sval, Finset.mem_univ,
      true_and]
    exact ⟨pc.S, ⟨pc.Si, rfl⟩, rfl⟩
  calc
    maxInner p poly pc.w
    _ ≥ pc.Sval p := Finset.le_max' (H2 := sval_in_img_inner)
    _ ≥ G pbar εα εθ₁ εφ₁ pc.S pc.w :=
        global_theorem_inequality_ii pbar p εα εθ₁ εφ₁ εθ₂ εφ₂ hεα hεθ₁ hεφ₁ p_near_pbar poly pc
    _ > maxH pbar poly εθ₂ εφ₂ pc.w := pc.exceeds
    _ ≥ maxOuter p poly pc.w :=
        global_theorem_inequality_iv pbar p εα εθ₁ εφ₁ εθ₂ εφ₂ hεθ₂ hεφ₂ p_near_pbar poly pc

/--
The Global Theorem, [SY25] Theorem 17, with a per-axis box in place of the
closed ball.
-/
theorem global_theorem {ι : Type} [Fintype ι] [Nonempty ι]
    (pbar : Pose ℝ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ)
    (hεα : 0 ≤ εα) (hεθ₁ : 0 ≤ εθ₁) (hεφ₁ : 0 ≤ εφ₁) (hεθ₂ : 0 ≤ εθ₂) (hεφ₂ : 0 ≤ εφ₂)
    (poly : GoodPoly ι)
    (pc : GlobalTheoremPrecondition poly pbar εα εθ₁ εφ₁ εθ₂ εφ₂) :
    ¬ ∃ p, Pose.near pbar εα εθ₁ εφ₁ εθ₂ εφ₂ p ∧ RupertPose p poly.hull := by
  rintro ⟨p, p_near_pbar, p_is_rupert⟩
  have hgt := global_theorem_gt_reasoning pbar p εα εθ₁ εφ₁ εθ₂ εφ₂
    hεα hεθ₁ hεφ₁ hεθ₂ hεφ₂ p_near_pbar poly pc
  have hle := global_theorem_le_reasoning p poly p_is_rupert pc.w
  exact lt_irrefl _ (lt_of_lt_of_le hgt hle)

end GlobalTheorem

end
