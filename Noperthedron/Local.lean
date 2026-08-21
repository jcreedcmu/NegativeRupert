module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.InnerProductSpace.PiL2

public import Noperthedron.Basic
public import Noperthedron.Bounding.OpNorm
public import Noperthedron.PoseInterval
public import Noperthedron.Local.Coss
public import Noperthedron.Local.EpsSpanning
public import Noperthedron.Local.LocallyMaximallyDistant
public import Noperthedron.Local.Prelims
public import Noperthedron.Local.OriginInTriangle
public import Noperthedron.Local.Spanp
public import Noperthedron.Global.VecXPartials

@[expose] public section


namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

/--
[SY25] Lemma 30, with the two disc memberships around the midpoint T combined
into a single bound on the distance between the two shadow points.
-/
theorem inCirc {δ ε θ₁ θ₁_ θ₂ θ₂_ φ₁ φ₁_ φ₂ φ₂_ α α_: ℝ} {P Q : Euc(3)}
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hε : 0 < ε)
    (hθ₁ : |θ₁ - θ₁_| ≤ ε) (hφ₁ : |φ₁ - φ₁_| ≤ ε)
    (hθ₂ : |θ₂ - θ₂_| ≤ ε) (hφ₂ : |φ₂ - φ₂_| ≤ ε)
    (hα : |α - α_| ≤ ε)
    (hδ : ‖rotR α_ (rotM θ₁_ φ₁_ P) - rotM θ₂_ φ₂_ Q‖ ≤ 2 * δ) :
    ‖rotR α (rotM θ₁ φ₁ P) - rotM θ₂ φ₂ Q‖ < 2 * (δ + √5 * ε) := by
  have h₁ : ‖rotR α (rotM θ₁ φ₁ P) - rotR α_ (rotM θ₁_ φ₁_ P)‖ < √5 * ε := by
    rw [←ContinuousLinearMap.comp_apply, ←ContinuousLinearMap.comp_apply, ← sub_apply]
    grw [ContinuousLinearMap.le_opNorm, mul_le_of_le_one_right (norm_nonneg _) hP]
    exact Bounding.norm_RM_sub_RM_le hε hθ₁ hφ₁ hα
  have h₂ : ‖rotM θ₂_ φ₂_ Q - rotM θ₂ φ₂ Q‖ < √2 * ε := by
    rw [← sub_apply]
    grw [ContinuousLinearMap.le_opNorm, mul_le_of_le_one_right (norm_nonneg _) hQ]
    exact Bounding.norm_M_sub_lt hε (by rwa [abs_sub_comm]) (by rwa [abs_sub_comm])
  have h₃ : √2 * ε ≤ √5 * ε :=
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by norm_num)) hε.le
  have h₄ := norm_sub_le_norm_sub_add_norm_sub
    (rotR α (rotM θ₁ φ₁ P)) (rotR α_ (rotM θ₁_ φ₁_ P)) (rotM θ₂ φ₂ Q)
  have h₅ := norm_sub_le_norm_sub_add_norm_sub
    (rotR α_ (rotM θ₁_ φ₁_ P)) (rotM θ₂_ φ₂_ Q) (rotM θ₂ φ₂ Q)
  linarith

/--
Condition A_ε from [SY25] Theorem 36
-/
def Triangle.Aε (X : ℝ³) (P : Triangle) (ε : ℝ) : Prop :=
  ∃ σ : ℕ, ∀ i : Fin 3, (-1)^σ * ⟪X, P i⟫ > √2 * ε

noncomputable
def Bε.lhs (v₁ v₂ : Euc(3)) (p : Pose ℝ) (ε : ℝ) : ℝ :=
   (⟪p.rotM₂ v₁, p.rotM₂ (v₁ - v₂)⟫ - 2 * ε * ‖v₁ - v₂‖ * (√2 + ε))
   / ((‖p.rotM₂ v₁‖ + √2 * ε) * (‖p.rotM₂ (v₁ - v₂)‖ + 2 * √2 * ε))

/--
Condition B_ε from [SY25] Theorem 36. The triangle it constrains is `v ∘ Qi`;
taking the indices `Qi` rather than the triangle itself guarantees that the
triangle's vertices are among the polyhedron's vertices `v`.
-/
def Bε {ι : Type} (Qi : Fin 3 → ι)
    (v : ι → Euc(3)) (p : Pose ℝ) (ε δ r : ℝ) : Prop :=
  ∀ i : Fin 3, ∀ k : ι, k ≠ Qi i →
    (δ + √5 * ε) / r < Bε.lhs (v (Qi i)) (v k) p ε

/-- The condition on δ in the Local Theorem -/
def BoundDelta (δ : ℝ) (p : Pose ℝ) (P Q : Triangle) : Prop :=
  ∀ i : Fin 3, δ ≥ ‖p.rotR (p.rotM₁ (P i)) - p.rotM₂ (Q i)‖/2

/-- The condition on r in the Local Theorem -/
def BoundR (r ε : ℝ) (p : Pose ℝ) (Q : Triangle): Prop :=
  ∀ i : Fin 3, ‖p.rotM₂ (Q i)‖ > r + √2 * ε

/--
A compact way of saying "the pose `p_` satisfies the Local Theorem precondition
at width `ε`": indices `Pi`, `Qi` of a pair of congruent triangles among the
vertices of `poly`, together with bounds `δ` and `r`, witnessing that no pose
within `ε` of `p_` can be a Rupert pose.
-/
structure LocalTheoremPrecondition {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (p_ : Pose ℝ) (ε : ℝ) : Type where
  Pi : Fin 3 → ι
  Qi : Fin 3 → ι
  cong_tri : Triangle.Congruent (poly.vertices.v ∘ Pi) (poly.vertices.v ∘ Qi)
  δ : ℝ
  r : ℝ
  hr : 0 < r
  hr₁ : BoundR r ε p_ (poly.vertices.v ∘ Qi)
  hδ : BoundDelta δ p_ (poly.vertices.v ∘ Pi) (poly.vertices.v ∘ Qi)
  ae₁ : Triangle.Aε p_.vecX₁ (poly.vertices.v ∘ Pi) ε
  ae₂ : Triangle.Aε p_.vecX₂ (poly.vertices.v ∘ Qi) ε
  span₁ : Triangle.Spanning (poly.vertices.v ∘ Pi) p_.θ₁ p_.φ₁ ε
  span₂ : Triangle.Spanning (poly.vertices.v ∘ Qi) p_.θ₂ p_.φ₂ ε
  be : Bε Qi poly.vertices.v p_ ε δ r

/-- The Locally-Maximally-Distant step of `local_theorem` ([SY25] Lemmas 33 and 32):
under `BoundR` and `Bε` at the center pose `p_`, the projected `Qi i` vertex is
locally maximally distant among all projected vertices, at any pose `p` within `ε`. -/
private lemma lmd_step {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) {p_ p : Pose ℝ} {ε δ r : ℝ}
    (Qi : Fin 3 → ι) (i : Fin 3)
    (hε : 0 < ε) (hr : 0 < r) (hδnn : 0 ≤ δ)
    (hθ₂ : |p.θ₂ - p_.θ₂| ≤ ε) (hφ₂ : |p.φ₂ - p_.φ₂| ≤ ε)
    (hr₁ : BoundR r ε p_ (poly.vertices.v ∘ Qi))
    (be : Bε Qi poly.vertices.v p_ ε δ r) :
    LocallyMaximallyDistant (2 * (δ + √5 * ε)) (rotM p.θ₂ p.φ₂ (poly.vertices.v (Qi i)))
      (Finset.image (rotM p.θ₂ p.φ₂) (Finset.image poly.vertices.v Finset.univ)) := by
  have hQ₁ : ‖poly.vertices.v (Qi i)‖ ≤ 1 := poly.vertex_radius_le_one (Qi i)
  -- apply lemma 15
  have h₃ : r < ‖rotM p.θ₂ p.φ₂ (poly.vertices.v (Qi i))‖ :=
    Bounding.norm_M_apply_gt hQ₁ hε hθ₂ hφ₂ (hr₁ i)
  -- apply lemma 33
  have h₅' (k : ι) (hkQ : k ≠ Qi i) :
      (δ + √5 * ε) / r <
        ⟪(rotM p.θ₂ p.φ₂) (poly.vertices.v (Qi i)),
         (rotM p.θ₂ p.φ₂) (poly.vertices.v (Qi i) - poly.vertices.v k)⟫ /
        (‖(rotM p.θ₂ p.φ₂) (poly.vertices.v (Qi i))‖ *
         ‖(rotM p.θ₂ p.φ₂) (poly.vertices.v (Qi i) - poly.vertices.v k)‖) := by
    have h₆ : (δ + √5 * ε) / r < Bε.lhs (poly.vertices.v (Qi i)) (poly.vertices.v k) p_ ε :=
      be i k hkQ
    unfold Bε.lhs Pose.rotM₂ at h₆
    have h₅ := coss (Q := poly.vertices.v k) hQ₁ (poly.vertex_radius_le_one k) hε hθ₂ hφ₂
      ((show (0:ℝ) < (δ + √5 * ε) / r by positivity).trans h₆)
    linarith only [h₅, h₆]
  -- apply lemma 32
  refine inner_ge_implies_LMD (r := r) ?_ hr h₃ ?_
  · exact Finset.mem_image_of_mem _
      (Finset.mem_image.mpr ⟨Qi i, Finset.mem_univ _, rfl⟩)
  · intro Pᵢ hPᵢ hPᵢQ
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hPᵢ
    obtain ⟨q, ⟨k, rfl⟩, rfl⟩ := hPᵢ
    have hkQ : k ≠ Qi i := fun h => hPᵢQ (by rw [h])
    rw [← map_sub]
    linarith [h₅' k hkQ]

/-- At a Rupert pose `p`, each inner-projected vertex lies in the interior of the
convex hull of the outer-projected vertices. -/
private lemma inner_vertex_mem_interior {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (p : Pose ℝ) (j : ι) (hΨ₂ : RupertPose p poly.hull) :
    rotR p.α (rotM p.θ₁ p.φ₁ (poly.vertices.v j)) ∈
      interior (convexHull ℝ
        (↑(Finset.image (rotM p.θ₂ p.φ₂) (Finset.image poly.vertices.v Finset.univ)) : Set ℝ²)) := by
  have h_inner_in_closure : p.inner (poly.vertices.v j) ∈ closure (innerShadow p poly.hull) := by
    rw [Pose.inner_shadow_eq_img_inner]
    refine subset_closure (Set.mem_image_of_mem _ (subset_convexHull ℝ _ ?_))
    exact ⟨j, rfl⟩
  have h_outer_eq : outerShadow p poly.hull = convexHull ℝ
      (↑(Finset.image (rotM p.θ₂ p.φ₂) (Finset.image poly.vertices.v Finset.univ)) : Set ℝ²) := by
    rw [Pose.outer_shadow_eq_M]
    have hpoly_hull : poly.hull =
        convexHull ℝ (↑(Finset.image poly.vertices.v Finset.univ) : Set ℝ³) := by
      simp [GoodPoly.hull, Polyhedron.hull, Set.range]
    rw [hpoly_hull]
    have hpm : (↑(Finset.image (rotM p.θ₂ p.φ₂)
          (Finset.image poly.vertices.v Finset.univ)) : Set ℝ²) =
        p.rotM₂ '' ↑(Finset.image poly.vertices.v Finset.univ) := by
      simp only [Finset.coe_image, Pose.rotM₂]
    rw [hpm]
    exact AffineMap.image_convexHull p.rotM₂.toAffineMap _
  have h_inner_eq : p.inner (poly.vertices.v j) =
      rotR p.α (rotM p.θ₁ p.φ₁ (poly.vertices.v j)) := by
    simp only [Pose.inner_eq_RM, Pose.rotR, Pose.rotM₁, Function.comp_apply]
  rw [← h_outer_eq, ← h_inner_eq]; exact hΨ₂ h_inner_in_closure

/-- Convert a strict comparison of projected norms into a strict comparison of squared
inner products with the axis vectors, via `pythagoras` (tail of `local_theorem`). -/
private lemma inner_sq_lt_of_rotM_norm_lt {θ₁ φ₁ θ₂ φ₂ : ℝ} {P Q : Euc(3)}
    (h_norm_eq : ‖P‖ = ‖Q‖)
    (h : ‖rotM θ₁ φ₁ P‖ < ‖rotM θ₂ φ₂ Q‖) :
    ⟪vecX θ₂ φ₂, Q⟫ ^ 2 < ⟪vecX θ₁ φ₁, P⟫ ^ 2 := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)] at h
  simp only [Local.pythagoras, h_norm_eq] at h
  linarith

/-- Turn a squared comparison into a signed one: if `x² < y²` and the `(-1)^σP`-signed `y`
is positive, then any signed `x` lies below it (tail of `local_theorem`). -/
private lemma neg_one_pow_mul_lt_of_sq_lt_sq {x y : ℝ} (σQ σP : ℕ)
    (hsq : x ^ 2 < y ^ 2) (hy : 0 < (-1 : ℝ) ^ σP * y) :
    (-1 : ℝ) ^ σQ * x < (-1 : ℝ) ^ σP * y :=
  calc (-1 : ℝ) ^ σQ * x
      ≤ |(-1 : ℝ) ^ σQ * x| := le_abs_self _
    _ = |x| := by rw [abs_mul, abs_neg_one_pow, one_mul]
    _ < |y| := sq_lt_sq.mp hsq
    _ = |(-1 : ℝ) ^ σP * y| := by rw [abs_mul, abs_neg_one_pow, one_mul]
    _ = (-1 : ℝ) ^ σP * y := abs_of_pos hy

/--
  [SY25] Theorem 36
-/
theorem local_theorem {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (p_ : Pose ℝ) (ε : ℝ)
    (pc : LocalTheoremPrecondition poly p_ ε)
    : ¬∃ p ∈ Metric.closedBall p_ ε, RupertPose p poly.hull := by
  obtain ⟨Pi, Qi, cong_tri, δ, r, hr, hr₁, hδ, ae₁, ae₂, span₁, span₂, be⟩ := pc
  have hε : 0 < ε := span₁.pos
  set P : Triangle := poly.vertices.v ∘ Pi
  set Q : Triangle := poly.vertices.v ∘ Qi
  rintro ⟨p, hΨ₁, hΨ₂⟩
  obtain ⟨L, hL⟩ := cong_tri
  obtain ⟨σP, hσP₂⟩ := ae₁
  obtain ⟨σQ, hσQ₂⟩ := ae₂
  let Y := vecX p.θ₁ p.φ₁
  let K := (-1 : ℝ)^(σP + σQ) • L.toContinuousLinearMap
  let Z := K (vecX p.θ₂ p.φ₂)
  have hδnn : 0 ≤ δ := le_trans (by positivity) (hδ 0)
  have hY : ‖Y‖ = 1 := by simp [Y, Bounding.vecX_norm_one]
  have hZ : ‖Z‖ = 1 := by simp [Z, K, norm_smul, Bounding.vecX_norm_one]
  have hα : |p.α - p_.α| ≤ ε := mem_closedBall_abs_sub_getParam hΨ₁ .α
  have hθ₁ : |p.θ₁ - p_.θ₁| ≤ ε := mem_closedBall_abs_sub_getParam hΨ₁ .θ₁
  have hφ₁ : |p.φ₁ - p_.φ₁| ≤ ε := mem_closedBall_abs_sub_getParam hΨ₁ .φ₁
  have hθ₂ : |p.θ₂ - p_.θ₂| ≤ ε := mem_closedBall_abs_sub_getParam hΨ₁ .θ₂
  have hφ₂ : |p.φ₂ - p_.φ₂| ≤ ε := mem_closedBall_abs_sub_getParam hΨ₁ .φ₂
  let P_ : Triangle := fun i ↦ (-1: ℝ) ^ σP • (P i)
  let Q_ : Triangle := fun i ↦ (-1: ℝ) ^ σQ • (Q i)
  have hP_ (i) : ‖P_ i‖ ≤ 1 := by
    simpa [P_, P, norm_smul, abs_neg_one_pow] using poly.vertex_radius_le_one (Pi i)
  have hQ_ (i) : ‖Q_ i‖ ≤ 1 := by
    simpa [Q_, Q, norm_smul, abs_neg_one_pow] using poly.vertex_radius_le_one (Qi i)
  have hPQ_ (i) : P_ i = K (Q_ i) := by
    simp [P_, Q_, K]
    rw [smul_smul, hL]
    congr 1
    rw [← pow_add, show σQ + (σP + σQ) = σP + 2 * σQ by ring,
        pow_add, pow_mul]
    norm_num
  have h₁ : Y ∈ Spanp P_ ∧ Z ∈ Spanp P_ := by
    constructor
    · have h₄ (i) : 0 < ⟪vecX p.θ₁ p.φ₁, P_ i⟫ :=
        Bounding.XPgt0 (hP_ i) hε hθ₁ hφ₁
          (by simpa [P_, Pose.vecX₁, ← real_inner_smul_right] using hσP₂ i)
      refine vecX_spanning P_ hθ₁ hφ₁ ?_ hP_ h₄
      exact spanning_neg σP span₁
    · have h₅ (i) : 0 < ⟪vecX p.θ₂ p.φ₂, Q_ i⟫ :=
        Bounding.XPgt0 (hQ_ i) hε hθ₂ hφ₂
          (by simpa [Q_, Pose.vecX₂, ← real_inner_smul_right] using hσQ₂ i)
      have h₆ : vecX p.θ₂ p.φ₂ ∈ Spanp Q_ := by
        refine vecX_spanning Q_ hθ₂ hφ₂ ?_ hQ_ h₅
        exact spanning_neg σQ span₂
      simp only [Spanp, Set.mem_ofPred_eq, Z] at h₆ ⊢
      obtain ⟨c, hc₁, hc₂⟩ := h₆
      use c, hc₁
      simp [hc₂, map_sum, map_smul, ←hPQ_]
  suffices h₂ : ∀ i, ⟪Z, P_ i⟫ < ⟪Y, P_ i⟫ by
    obtain ⟨i, h₃⟩ := langles (hY.trans hZ.symm) h₁.1 h₁.2
    rw [real_inner_comm Y (P_ i), real_inner_comm Z (P_ i)] at h₃
    exact lt_iff_not_ge.mp (h₂ i) h₃
  intro i
  have hQ₁ : ‖Q i‖ ≤ 1 := poly.vertex_radius_le_one (Qi i)
  -- apply lemma 30
  have hP₁ : ‖P i‖ ≤ 1 := poly.vertex_radius_le_one (Pi i)
  have hd : ‖rotR p.α (rotM p.θ₁ p.φ₁ (P i)) - rotM p.θ₂ p.φ₂ (Q i)‖ < 2 * (δ + √5 * ε) := by
    refine inCirc hP₁ hQ₁ hε hθ₁ hφ₁ hθ₂ hφ₂ hα ?_
    have h := hδ i
    simp only [Pose.rotR, Pose.rotM₁, Pose.rotM₂] at h
    linarith
  -- apply lemmas 33 and 32
  let pm : Finset Euc(2) :=
    Finset.image (rotM p.θ₂ p.φ₂) (Finset.image poly.vertices.v Finset.univ)
  have h₈ : LocallyMaximallyDistant (2 * (δ + √5 * ε)) (rotM p.θ₂ p.φ₂ (Q i)) pm :=
    lmd_step poly Qi i hε hr hδnn hθ₂ hφ₂ hr₁ be
  -- Step 1: Show rotR p.α (rotM p.θ₁ p.φ₁ (P i)) ∈ sect (interior of pm)
  have h_in_interior_outer : rotR p.α (rotM p.θ₁ p.φ₁ (P i)) ∈
      interior (convexHull ℝ (↑pm : Set ℝ²)) :=
    inner_vertex_mem_interior poly p (Pi i) hΨ₂
  -- Step 2: Combine with hd to get sect membership, apply LMD for norm bound
  have h_sect : rotR p.α (rotM p.θ₁ p.φ₁ (P i)) ∈
      sect (2 * (δ + √5 * ε)) (rotM p.θ₂ p.φ₂ (Q i)) pm :=
    ⟨mem_ball_iff_norm.mpr hd, h_in_interior_outer⟩
  have h_norm_bound : ‖rotM p.θ₁ p.φ₁ (P i)‖ < ‖rotM p.θ₂ p.φ₂ (Q i)‖ := by
    rw [← Bounding.rotR_preserves_norm p.α]; exact h₈ _ h_sect
  -- Step 3: Apply pythagoras to convert norm bounds to inner product bounds
  have h_inner_sq : ⟪vecX p.θ₂ p.φ₂, Q i⟫^2 < ⟪Y, P i⟫^2 :=
    inner_sq_lt_of_rotM_norm_lt (by rw [hL i, L.norm_map]) h_norm_bound
  -- Step 4: Handle sign conventions using |(-1)^σ * x| = |x|
  have hYP_pos : 0 < ⟪Y, P_ i⟫ :=
    Bounding.XPgt0 (hP_ i) hε hθ₁ hφ₁
      (by simpa [P_, Pose.vecX₁, ← real_inner_smul_right] using hσP₂ i)
  -- ⟪Z, P_ i⟫ = (-1)^σQ * ⟪vecX p.θ₂ p.φ₂, Q i⟫ and ⟪Y, P_ i⟫ = (-1)^σP * ⟪Y, P i⟫
  have h_ZP : ⟪Z, P_ i⟫ = (-1 : ℝ)^σQ * ⟪vecX p.θ₂ p.φ₂, Q i⟫ := by
    simp only [Z, K, P_, FunLike.coe_smul, _root_.Pi.smul_apply,
      LinearIsometry.coe_toContinuousLinearMap, inner_smul_left, real_inner_smul_right, RCLike.conj_to_real]
    rw [hL i, L.inner_map_map]
    have h_exp : (-1 : ℝ)^(σP + σQ) * (-1 : ℝ)^σP = (-1 : ℝ)^σQ := by
      rw [← pow_add, show σP + σQ + σP = 2 * σP + σQ by ring,
          pow_add, pow_mul]; norm_num
    rw [←mul_assoc, h_exp]
  have h_YP : ⟪Y, P_ i⟫ = (-1 : ℝ)^σP * ⟪Y, P i⟫ := by simp only [P_, real_inner_smul_right]
  rw [h_ZP, h_YP]
  -- The right-hand side is positive, so compare via absolute values
  exact neg_one_pow_mul_lt_of_sq_lt_sq σQ σP h_inner_sq (h_YP ▸ hYP_pos)

/-! ## The second-order local theorem

The same skeleton as `local_theorem`, with every Lipschitz `ε`-slack
(`√2·ε`, `√5·ε`, `2ε(√2+ε)`) replaced by the order-2-exact per-axis variation
budgets of `Noperthedron.Global.SecondOrderBounds` / `SpanProducts` /
`VecXPartials`, over the anisotropic box `Pose.near p_ εα εθ₁ εφ₁ εθ₂ εφ₂`. -/

/-- Condition A_ε from [SY25] Theorem 36, second-order: the signed axis inner
product at the center exceeds its own variation budget. -/
def Triangle.Aε₂ (P : Triangle) (θ_ φ_ εθ εφ : ℝ) : Prop :=
  ∃ σ : ℕ, ∀ i : Fin 3,
    GlobalTheorem.ΔvecX (P i) εθ εφ θ_ φ_ < (-1)^σ * ⟪vecX θ_ φ_, P i⟫

noncomputable
def Bε₂.lhs (v₁ v₂ : Euc(3)) (p : Pose ℝ) (εθ εφ : ℝ) : ℝ :=
  (⟪p.rotM₂ v₁, p.rotM₂ (v₁ - v₂)⟫
      - GlobalTheorem.ΔprodMM (ContinuousLinearMap.id ℝ ℝ²) v₁ (v₁ - v₂) εθ εφ p.θ₂ p.φ₂)
  / ((‖p.rotM₂ v₁‖ + GlobalTheorem.ΔrotM v₁ εθ εφ p.θ₂ p.φ₂)
      * (‖p.rotM₂ (v₁ - v₂)‖ + GlobalTheorem.ΔrotM (v₁ - v₂) εθ εφ p.θ₂ p.φ₂))

/-- Condition B_ε from [SY25] Theorem 36, second-order.  The variation budgets
are folded into `δ` (see `BoundDelta₂`), so the cosine threshold is plainly
`δ/r`; the numerator of `Bε₂.lhs` is additionally required positive, which the
abstract quotient transfer needs. -/
def Bε₂ {ι : Type} (Qi : Fin 3 → ι)
    (v : ι → Euc(3)) (p : Pose ℝ) (εθ εφ δ r : ℝ) : Prop :=
  ∀ i : Fin 3, ∀ k : ι, k ≠ Qi i →
    0 < ⟪p.rotM₂ (v (Qi i)), p.rotM₂ (v (Qi i) - v k)⟫
        - GlobalTheorem.ΔprodMM (ContinuousLinearMap.id ℝ ℝ²) (v (Qi i)) (v (Qi i) - v k)
            εθ εφ p.θ₂ p.φ₂
      ∧ δ / r < Bε₂.lhs (v (Qi i)) (v k) p εθ εφ

/-- The condition on δ in the second-order Local Theorem: the center shadow
distance plus both variation budgets stays under `2δ`. -/
def BoundDelta₂ (δ εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ) (p : Pose ℝ) (P Q : Triangle) : Prop :=
  ∀ i : Fin 3, ‖p.rotR (p.rotM₁ (P i)) - p.rotM₂ (Q i)‖
    + GlobalTheorem.ΔrotRM (P i) εα εθ₁ εφ₁ p.θ₁ p.φ₁
    + GlobalTheorem.ΔrotM (Q i) εθ₂ εφ₂ p.θ₂ p.φ₂ < 2 * δ

/-- The condition on r in the second-order Local Theorem. -/
def BoundR₂ (r εθ εφ : ℝ) (p : Pose ℝ) (Q : Triangle) : Prop :=
  ∀ i : Fin 3, r + GlobalTheorem.ΔrotM (Q i) εθ εφ p.θ₂ p.φ₂ < ‖p.rotM₂ (Q i)‖

/--
The second-order analog of `LocalTheoremPrecondition`, over the anisotropic
box of per-axis radii `εα εθ₁ εφ₁ εθ₂ εφ₂` around `p_`.
-/
structure LocalTheoremPrecondition₂ {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (p_ : Pose ℝ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ) : Type where
  Pi : Fin 3 → ι
  Qi : Fin 3 → ι
  cong_tri : Triangle.Congruent (poly.vertices.v ∘ Pi) (poly.vertices.v ∘ Qi)
  δ : ℝ
  r : ℝ
  hr : 0 < r
  hr₁ : BoundR₂ r εθ₂ εφ₂ p_ (poly.vertices.v ∘ Qi)
  hδ : BoundDelta₂ δ εα εθ₁ εφ₁ εθ₂ εφ₂ p_ (poly.vertices.v ∘ Pi) (poly.vertices.v ∘ Qi)
  ae₁ : Triangle.Aε₂ (poly.vertices.v ∘ Pi) p_.θ₁ p_.φ₁ εθ₁ εφ₁
  ae₂ : Triangle.Aε₂ (poly.vertices.v ∘ Qi) p_.θ₂ p_.φ₂ εθ₂ εφ₂
  span₁ : Triangle.Spanning₂ (poly.vertices.v ∘ Pi) p_.θ₁ p_.φ₁ εθ₁ εφ₁
  span₂ : Triangle.Spanning₂ (poly.vertices.v ∘ Qi) p_.θ₂ p_.φ₂ εθ₂ εφ₂
  be : Bε₂ Qi poly.vertices.v p_ εθ₂ εφ₂ δ r

/-- The LMD step of `local_theorem₂`: `BoundR₂` and `Bε₂` at the center give
local maximal distance at radius `2δ` at any pose in the box. -/
private lemma lmd_step₂ {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) {p_ p : Pose ℝ} {εθ₂ εφ₂ δ r : ℝ}
    (Qi : Fin 3 → ι) (i : Fin 3)
    (hεθ₂ : 0 ≤ εθ₂) (hεφ₂ : 0 ≤ εφ₂) (hr : 0 < r)
    (hθ₂ : |p.θ₂ - p_.θ₂| ≤ εθ₂) (hφ₂ : |p.φ₂ - p_.φ₂| ≤ εφ₂)
    (hr₁ : BoundR₂ r εθ₂ εφ₂ p_ (poly.vertices.v ∘ Qi))
    (be : Bε₂ Qi poly.vertices.v p_ εθ₂ εφ₂ δ r) :
    LocallyMaximallyDistant (2 * δ) (rotM p.θ₂ p.φ₂ (poly.vertices.v (Qi i)))
      (Finset.image (rotM p.θ₂ p.φ₂) (Finset.image poly.vertices.v Finset.univ)) := by
  -- apply the second-order lemma 15
  have h₃ : r < ‖rotM p.θ₂ p.φ₂ (poly.vertices.v (Qi i))‖ := by
    have h := hr₁ i
    simp only [Function.comp_apply, Pose.rotM₂] at h
    exact GlobalTheorem.norm_M_apply_gt₂ hεθ₂ hεφ₂ hθ₂ hφ₂ h
  -- apply the second-order lemma 33
  have h₅' (k : ι) (hkQ : k ≠ Qi i) :
      δ / r <
        ⟪(rotM p.θ₂ p.φ₂) (poly.vertices.v (Qi i)),
         (rotM p.θ₂ p.φ₂) (poly.vertices.v (Qi i) - poly.vertices.v k)⟫ /
        (‖(rotM p.θ₂ p.φ₂) (poly.vertices.v (Qi i))‖ *
         ‖(rotM p.θ₂ p.φ₂) (poly.vertices.v (Qi i) - poly.vertices.v k)‖) := by
    obtain ⟨hpos, h₆⟩ := be i k hkQ
    unfold Bε₂.lhs at h₆
    simp only [Pose.rotM₂] at hpos h₆
    set v₁ := poly.vertices.v (Qi i)
    set v₂ := poly.vertices.v k
    have hnum := GlobalTheorem.inner_prod_MM_sub_le (ContinuousLinearMap.id ℝ ℝ²)
      ContinuousLinearMap.norm_id_le (v := v₁) (w := v₁ - v₂) hεθ₂ hεφ₂ hθ₂ hφ₂
    simp only [ContinuousLinearMap.id_apply] at hnum
    have h1' : |‖rotM p.θ₂ p.φ₂ v₁‖ - ‖rotM p_.θ₂ p_.φ₂ v₁‖|
        ≤ GlobalTheorem.ΔrotM v₁ εθ₂ εφ₂ p_.θ₂ p_.φ₂ :=
      le_trans (abs_norm_sub_norm_le _ _)
        (GlobalTheorem.norm_rotM_apply_sub_le hεθ₂ hεφ₂ hθ₂ hφ₂)
    have h2' : |‖rotM p.θ₂ p.φ₂ (v₁ - v₂)‖ - ‖rotM p_.θ₂ p_.φ₂ (v₁ - v₂)‖|
        ≤ GlobalTheorem.ΔrotM (v₁ - v₂) εθ₂ εφ₂ p_.θ₂ p_.φ₂ :=
      le_trans (abs_norm_sub_norm_le _ _)
        (GlobalTheorem.norm_rotM_apply_sub_le hεθ₂ hεφ₂ hθ₂ hφ₂)
    have hnum_pos : 0 < ⟪rotM p.θ₂ p.φ₂ v₁, rotM p.θ₂ p.φ₂ (v₁ - v₂)⟫ := by
      have h := abs_le.mp hnum
      linarith [h.1]
    have hn1 : 0 < ‖rotM p.θ₂ p.φ₂ v₁‖ := hr.trans h₃
    have hn2 : 0 < ‖rotM p.θ₂ p.φ₂ (v₁ - v₂)‖ := by
      rcases eq_or_lt_of_le (norm_nonneg (rotM p.θ₂ p.φ₂ (v₁ - v₂))) with hz | h
      · rw [show rotM p.θ₂ p.φ₂ (v₁ - v₂) = 0 from norm_eq_zero.mp hz.symm,
          inner_zero_right] at hnum_pos
        exact absurd hnum_pos (lt_irrefl 0)
      · exact h
    have hkey := GlobalTheorem.quotient_ge_of_bounds hnum h1' h2' hn1 hn2 hpos.le
    exact h₆.trans_le hkey
  -- apply lemma 32
  refine inner_ge_implies_LMD (r := r) ?_ hr h₃ ?_
  · exact Finset.mem_image_of_mem _
      (Finset.mem_image.mpr ⟨Qi i, Finset.mem_univ _, rfl⟩)
  · intro Pᵢ hPᵢ hPᵢQ
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hPᵢ
    obtain ⟨q, ⟨k, rfl⟩, rfl⟩ := hPᵢ
    have hkQ : k ≠ Qi i := fun h => hPᵢQ (by rw [h])
    rw [← map_sub]
    linarith [h₅' k hkQ]

/--
  [SY25] Theorem 36, second-order anisotropic version.
-/
theorem local_theorem₂ {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (p_ : Pose ℝ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℝ)
    (hεα : 0 ≤ εα) (hεθ₁ : 0 ≤ εθ₁) (hεφ₁ : 0 ≤ εφ₁)
    (hεθ₂ : 0 ≤ εθ₂) (hεφ₂ : 0 ≤ εφ₂)
    (pc : LocalTheoremPrecondition₂ poly p_ εα εθ₁ εφ₁ εθ₂ εφ₂) :
    ¬∃ p, Pose.near p_ εα εθ₁ εφ₁ εθ₂ εφ₂ p ∧ RupertPose p poly.hull := by
  obtain ⟨Pi, Qi, cong_tri, δ, r, hr, hr₁, hδ, ae₁, ae₂, span₁, span₂, be⟩ := pc
  set P : Triangle := poly.vertices.v ∘ Pi
  set Q : Triangle := poly.vertices.v ∘ Qi
  rintro ⟨p, hΨ₁, hΨ₂⟩
  obtain ⟨hθ₁, hφ₁, hθ₂, hφ₂, hα⟩ := hΨ₁
  obtain ⟨L, hL⟩ := cong_tri
  obtain ⟨σP, hσP₂⟩ := ae₁
  obtain ⟨σQ, hσQ₂⟩ := ae₂
  let Y := vecX p.θ₁ p.φ₁
  let K := (-1 : ℝ)^(σP + σQ) • L.toContinuousLinearMap
  let Z := K (vecX p.θ₂ p.φ₂)
  have hY : ‖Y‖ = 1 := by simp [Y, Bounding.vecX_norm_one]
  have hZ : ‖Z‖ = 1 := by simp [Z, K, norm_smul, Bounding.vecX_norm_one]
  let P_ : Triangle := fun i ↦ (-1: ℝ) ^ σP • (P i)
  let Q_ : Triangle := fun i ↦ (-1: ℝ) ^ σQ • (Q i)
  have hP_ (i) : ‖P_ i‖ ≤ 1 := by
    simpa [P_, P, norm_smul, abs_neg_one_pow] using poly.vertex_radius_le_one (Pi i)
  have hQ_ (i) : ‖Q_ i‖ ≤ 1 := by
    simpa [Q_, Q, norm_smul, abs_neg_one_pow] using poly.vertex_radius_le_one (Qi i)
  have hPQ_ (i) : P_ i = K (Q_ i) := by
    simp [P_, Q_, K]
    rw [smul_smul, hL]
    congr 1
    rw [← pow_add, show σQ + (σP + σQ) = σP + 2 * σQ by ring,
        pow_add, pow_mul]
    norm_num
  have h₄ (i) : 0 < ⟪vecX p.θ₁ p.φ₁, P_ i⟫ := by
    refine GlobalTheorem.XPgt0₂ (hP_ i) hεθ₁ hεφ₁ hθ₁ hφ₁ ?_
    rw [show P_ i = (-1:ℝ)^σP • (P i) from rfl,
      GlobalTheorem.ΔvecX_neg_one_pow_smul, real_inner_smul_right]
    exact hσP₂ i
  have h₅ (i) : 0 < ⟪vecX p.θ₂ p.φ₂, Q_ i⟫ := by
    refine GlobalTheorem.XPgt0₂ (hQ_ i) hεθ₂ hεφ₂ hθ₂ hφ₂ ?_
    rw [show Q_ i = (-1:ℝ)^σQ • (Q i) from rfl,
      GlobalTheorem.ΔvecX_neg_one_pow_smul, real_inner_smul_right]
    exact hσQ₂ i
  have h₁ : Y ∈ Spanp P_ ∧ Z ∈ Spanp P_ := by
    constructor
    · exact vecX_spanning₂ P_ hεθ₁ hεφ₁ hθ₁ hφ₁ (spanning₂_neg σP span₁) h₄
    · have h₆ : vecX p.θ₂ p.φ₂ ∈ Spanp Q_ :=
        vecX_spanning₂ Q_ hεθ₂ hεφ₂ hθ₂ hφ₂ (spanning₂_neg σQ span₂) h₅
      simp only [Spanp, Set.mem_ofPred_eq, Z] at h₆ ⊢
      obtain ⟨c, hc₁, hc₂⟩ := h₆
      use c, hc₁
      simp [hc₂, map_sum, map_smul, ←hPQ_]
  suffices h₂ : ∀ i, ⟪Z, P_ i⟫ < ⟪Y, P_ i⟫ by
    obtain ⟨i, h₃⟩ := langles (hY.trans hZ.symm) h₁.1 h₁.2
    rw [real_inner_comm Y (P_ i), real_inner_comm Z (P_ i)] at h₃
    exact lt_iff_not_ge.mp (h₂ i) h₃
  intro i
  -- apply the second-order lemma 30
  have hd : ‖rotR p.α (rotM p.θ₁ p.φ₁ (P i)) - rotM p.θ₂ p.φ₂ (Q i)‖ < 2 * δ := by
    refine GlobalTheorem.inCirc₂ hεα hεθ₁ hεφ₁ hεθ₂ hεφ₂ hα hθ₁ hφ₁ hθ₂ hφ₂ ?_
    have h := hδ i
    simp only [Pose.rotR, Pose.rotM₁, Pose.rotM₂] at h
    exact h
  -- apply the second-order lemmas 33 and 32
  let pm : Finset Euc(2) :=
    Finset.image (rotM p.θ₂ p.φ₂) (Finset.image poly.vertices.v Finset.univ)
  have h₈ : LocallyMaximallyDistant (2 * δ) (rotM p.θ₂ p.φ₂ (Q i)) pm :=
    lmd_step₂ poly Qi i hεθ₂ hεφ₂ hr hθ₂ hφ₂ hr₁ be
  have h_in_interior_outer : rotR p.α (rotM p.θ₁ p.φ₁ (P i)) ∈
      interior (convexHull ℝ (↑pm : Set ℝ²)) :=
    inner_vertex_mem_interior poly p (Pi i) hΨ₂
  have h_sect : rotR p.α (rotM p.θ₁ p.φ₁ (P i)) ∈
      sect (2 * δ) (rotM p.θ₂ p.φ₂ (Q i)) pm :=
    ⟨mem_ball_iff_norm.mpr hd, h_in_interior_outer⟩
  have h_norm_bound : ‖rotM p.θ₁ p.φ₁ (P i)‖ < ‖rotM p.θ₂ p.φ₂ (Q i)‖ := by
    rw [← Bounding.rotR_preserves_norm p.α]; exact h₈ _ h_sect
  have h_inner_sq : ⟪vecX p.θ₂ p.φ₂, Q i⟫^2 < ⟪Y, P i⟫^2 :=
    inner_sq_lt_of_rotM_norm_lt (by rw [hL i, L.norm_map]) h_norm_bound
  have h_ZP : ⟪Z, P_ i⟫ = (-1 : ℝ)^σQ * ⟪vecX p.θ₂ p.φ₂, Q i⟫ := by
    simp only [Z, K, P_, FunLike.coe_smul, _root_.Pi.smul_apply,
      LinearIsometry.coe_toContinuousLinearMap, inner_smul_left, real_inner_smul_right,
      RCLike.conj_to_real]
    rw [hL i, L.inner_map_map]
    have h_exp : (-1 : ℝ)^(σP + σQ) * (-1 : ℝ)^σP = (-1 : ℝ)^σQ := by
      rw [← pow_add, show σP + σQ + σP = 2 * σP + σQ by ring,
          pow_add, pow_mul]; norm_num
    rw [←mul_assoc, h_exp]
  have h_YP : ⟪Y, P_ i⟫ = (-1 : ℝ)^σP * ⟪Y, P i⟫ := by simp only [P_, real_inner_smul_right]
  rw [h_ZP, h_YP]
  exact neg_one_pow_mul_lt_of_sq_lt_sq σQ σP h_inner_sq (h_YP ▸ h₄ i)

end Local
end
