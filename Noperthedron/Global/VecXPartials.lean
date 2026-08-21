module

public import Noperthedron.Global.RotationPartials.SecondPartialOuter
public import Noperthedron.Global.BoundedPartialsControlDifference

@[expose] public section


/-!
# Partial derivatives of the viewing direction `vecX`

The ∂-grid of `vecX (θ, φ)`: every entry of `vecX` is `c(θ)·trig(φ)` with a
genuinely trigonometric `φ`-part, so `∂φ² = -id` entrywise and the φ-chain
folds after ONE step (`vecXφφ = -vecX`); the θ-chain folds after two
(`∂θ³ = -∂θ`), exactly as for `rotM`.  The grid therefore has 3×2 members
  `vecXFam a b = ∂θᵃ ∂φᵇ vecX`,  a ≤ 2, b ≤ 1,
all of norm ≤ 1, and the family `± ⟪vecXFam a b (θ, φ), P⟫` is closed under
`nth_partial` (`IsVecXDerivFam`), giving the exact second partials
(`second_partial_vecX_inner_eq`) and the any-order `≤ ‖P‖` bound that the
second-order local certificate's A-conditions consume.
-/

open scoped RealInnerProductSpace
open Real

noncomputable def vecXθ (θ φ : ℝ) : ℝ³ :=
  !₂[ -sin θ * sin φ, cos θ * sin φ, 0 ]

noncomputable def vecXφ (θ φ : ℝ) : ℝ³ :=
  !₂[ cos θ * cos φ, sin θ * cos φ, -sin φ ]

noncomputable def vecXθθ (θ φ : ℝ) : ℝ³ :=
  !₂[ -cos θ * sin φ, -sin θ * sin φ, 0 ]

noncomputable def vecXθφ (θ φ : ℝ) : ℝ³ :=
  !₂[ -sin θ * cos φ, cos θ * cos φ, 0 ]

noncomputable def vecXθθφ (θ φ : ℝ) : ℝ³ :=
  !₂[ -cos θ * cos φ, -sin θ * cos φ, 0 ]

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## Norm bounds -/

private lemma norm_le_one_of_sq_le {v : ℝ³} (h : ‖v‖ ^ 2 ≤ 1) : ‖v‖ ≤ 1 :=
  (pow_le_one_iff_of_nonneg (norm_nonneg v) two_ne_zero).mp h

private lemma sq_norm_euc3 (a b c : ℝ) :
    ‖(!₂[a, b, c] : ℝ³)‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_three, sq_abs]

lemma vecXθ_norm_le_one (θ φ : ℝ) : ‖vecXθ θ φ‖ ≤ 1 := by
  refine norm_le_one_of_sq_le ?_
  rw [vecXθ, sq_norm_euc3]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_le_one φ, sq_nonneg (Real.sin φ)]

lemma vecXφ_norm_le_one (θ φ : ℝ) : ‖vecXφ θ φ‖ ≤ 1 := by
  refine norm_le_one_of_sq_le ?_
  rw [vecXφ, sq_norm_euc3]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]

lemma vecXθθ_norm_le_one (θ φ : ℝ) : ‖vecXθθ θ φ‖ ≤ 1 := by
  refine norm_le_one_of_sq_le ?_
  rw [vecXθθ, sq_norm_euc3]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_le_one φ, sq_nonneg (Real.sin φ)]

lemma vecXθφ_norm_le_one (θ φ : ℝ) : ‖vecXθφ θ φ‖ ≤ 1 := by
  refine norm_le_one_of_sq_le ?_
  rw [vecXθφ, sq_norm_euc3]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.cos_sq_le_one φ, sq_nonneg (Real.cos φ)]

lemma vecXθθφ_norm_le_one (θ φ : ℝ) : ‖vecXθθφ θ φ‖ ≤ 1 := by
  refine norm_le_one_of_sq_le ?_
  rw [vecXθθφ, sq_norm_euc3]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.cos_sq_le_one φ, sq_nonneg (Real.cos φ)]

/-! ## Entrywise derivative transport -/

/-- `HasDerivAt` for an `ℝ³`-valued path given entrywise derivatives. -/
private lemma hasDerivAt_euc3 {f0 f1 f2 : ℝ → ℝ} {g0 g1 g2 : ℝ} {t : ℝ}
    (h0 : HasDerivAt f0 g0 t) (h1 : HasDerivAt f1 g1 t) (h2 : HasDerivAt f2 g2 t) :
    HasDerivAt (fun s => (!₂[f0 s, f1 s, f2 s] : ℝ³)) !₂[g0, g1, g2] t := by
  have hpi : HasDerivAt (fun s => (![f0 s, f1 s, f2 s] : Fin 3 → ℝ)) ![g0, g1, g2] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
  let lpmap : (Fin 3 → ℝ) →L[ℝ] ℝ³ :=
    (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toContinuousLinearMap
  simpa [lpmap] using HasDerivAt.clm_apply (hasDerivAt_const t lpmap) hpi

/-! ## The twelve grid steps -/

lemma hasDerivAt_vecX_θ (θ φ : ℝ) : HasDerivAt (fun t => vecX t φ) (vecXθ θ φ) θ := by
  unfold vecX vecXθ
  exact hasDerivAt_euc3
    (by simpa [neg_mul] using (Real.hasDerivAt_cos θ).mul_const (Real.sin φ))
    ((Real.hasDerivAt_sin θ).mul_const (Real.sin φ))
    (hasDerivAt_const θ _)

lemma hasDerivAt_vecX_φ (θ φ : ℝ) : HasDerivAt (fun t => vecX θ t) (vecXφ θ φ) φ := by
  unfold vecX vecXφ
  exact hasDerivAt_euc3
    ((Real.hasDerivAt_sin φ).const_mul (Real.cos θ))
    ((Real.hasDerivAt_sin φ).const_mul (Real.sin θ))
    (by simpa using Real.hasDerivAt_cos φ)

lemma hasDerivAt_vecXθ_θ (θ φ : ℝ) : HasDerivAt (fun t => vecXθ t φ) (vecXθθ θ φ) θ := by
  unfold vecXθ vecXθθ
  exact hasDerivAt_euc3
    (by simpa [neg_mul] using ((Real.hasDerivAt_sin θ).neg.mul_const (Real.sin φ)))
    (by simpa [neg_mul] using (Real.hasDerivAt_cos θ).mul_const (Real.sin φ))
    (hasDerivAt_const θ _)

lemma hasDerivAt_vecXθ_φ (θ φ : ℝ) : HasDerivAt (fun t => vecXθ θ t) (vecXθφ θ φ) φ := by
  unfold vecXθ vecXθφ
  exact hasDerivAt_euc3
    (by simpa [neg_mul, mul_neg] using (Real.hasDerivAt_sin φ).const_mul (-Real.sin θ))
    ((Real.hasDerivAt_sin φ).const_mul (Real.cos θ))
    (hasDerivAt_const φ _)

lemma hasDerivAt_vecXφ_θ (θ φ : ℝ) : HasDerivAt (fun t => vecXφ t φ) (vecXθφ θ φ) θ := by
  unfold vecXφ vecXθφ
  exact hasDerivAt_euc3
    (by simpa [neg_mul] using (Real.hasDerivAt_cos θ).mul_const (Real.cos φ))
    ((Real.hasDerivAt_sin θ).mul_const (Real.cos φ))
    (hasDerivAt_const θ _)

lemma hasDerivAt_vecXφ_φ (θ φ : ℝ) : HasDerivAt (fun t => vecXφ θ t) (-(vecX θ φ)) φ := by
  unfold vecXφ
  convert hasDerivAt_euc3 (t := φ)
    (show HasDerivAt (fun s => Real.cos θ * Real.cos s) (Real.cos θ * -Real.sin φ) φ from
      (Real.hasDerivAt_cos φ).const_mul _)
    (show HasDerivAt (fun s => Real.sin θ * Real.cos s) (Real.sin θ * -Real.sin φ) φ from
      (Real.hasDerivAt_cos φ).const_mul _)
    (show HasDerivAt (fun s => -Real.sin s) (-Real.cos φ) φ from
      (Real.hasDerivAt_sin φ).neg) using 1
  ext i
  fin_cases i <;> simp [vecX] <;> ring

lemma hasDerivAt_vecXθθ_θ (θ φ : ℝ) :
    HasDerivAt (fun t => vecXθθ t φ) (-(vecXθ θ φ)) θ := by
  unfold vecXθθ
  convert hasDerivAt_euc3 (t := θ)
    (show HasDerivAt (fun s => -Real.cos s * Real.sin φ) (Real.sin θ * Real.sin φ) θ from
      by simpa [neg_mul] using ((Real.hasDerivAt_cos θ).neg.mul_const (Real.sin φ)))
    (show HasDerivAt (fun s => -Real.sin s * Real.sin φ) (-Real.cos θ * Real.sin φ) θ from
      by simpa [neg_mul] using ((Real.hasDerivAt_sin θ).neg.mul_const (Real.sin φ)))
    (hasDerivAt_const θ (0:ℝ)) using 1
  ext i
  fin_cases i <;> simp [vecXθ] <;> ring

lemma hasDerivAt_vecXθθ_φ (θ φ : ℝ) :
    HasDerivAt (fun t => vecXθθ θ t) (vecXθθφ θ φ) φ := by
  unfold vecXθθ vecXθθφ
  exact hasDerivAt_euc3
    (by simpa [neg_mul, mul_neg] using (Real.hasDerivAt_sin φ).const_mul (-Real.cos θ))
    (by simpa [neg_mul, mul_neg] using (Real.hasDerivAt_sin φ).const_mul (-Real.sin θ))
    (hasDerivAt_const φ _)

lemma hasDerivAt_vecXθφ_θ (θ φ : ℝ) :
    HasDerivAt (fun t => vecXθφ t φ) (vecXθθφ θ φ) θ := by
  unfold vecXθφ vecXθθφ
  exact hasDerivAt_euc3
    (by simpa [neg_mul] using ((Real.hasDerivAt_sin θ).neg.mul_const (Real.cos φ)))
    (by simpa [neg_mul] using (Real.hasDerivAt_cos θ).mul_const (Real.cos φ))
    (hasDerivAt_const θ _)

lemma hasDerivAt_vecXθφ_φ (θ φ : ℝ) :
    HasDerivAt (fun t => vecXθφ θ t) (-(vecXθ θ φ)) φ := by
  unfold vecXθφ
  convert hasDerivAt_euc3 (t := φ)
    (show HasDerivAt (fun s => -Real.sin θ * Real.cos s) (-Real.sin θ * -Real.sin φ) φ from
      by simpa [neg_mul] using (Real.hasDerivAt_cos φ).const_mul (-Real.sin θ))
    (show HasDerivAt (fun s => Real.cos θ * Real.cos s) (Real.cos θ * -Real.sin φ) φ from
      (Real.hasDerivAt_cos φ).const_mul _)
    (hasDerivAt_const φ (0:ℝ)) using 1
  ext i
  fin_cases i <;> simp [vecXθ] <;> ring

lemma hasDerivAt_vecXθθφ_θ (θ φ : ℝ) :
    HasDerivAt (fun t => vecXθθφ t φ) (-(vecXθφ θ φ)) θ := by
  unfold vecXθθφ
  convert hasDerivAt_euc3 (t := θ)
    (show HasDerivAt (fun s => -Real.cos s * Real.cos φ) (Real.sin θ * Real.cos φ) θ from
      by simpa [neg_mul] using ((Real.hasDerivAt_cos θ).neg.mul_const (Real.cos φ)))
    (show HasDerivAt (fun s => -Real.sin s * Real.cos φ) (-Real.cos θ * Real.cos φ) θ from
      by simpa [neg_mul] using ((Real.hasDerivAt_sin θ).neg.mul_const (Real.cos φ)))
    (hasDerivAt_const θ (0:ℝ)) using 1
  ext i
  fin_cases i <;> simp [vecXθφ] <;> ring

lemma hasDerivAt_vecXθθφ_φ (θ φ : ℝ) :
    HasDerivAt (fun t => vecXθθφ θ t) (-(vecXθθ θ φ)) φ := by
  unfold vecXθθφ
  convert hasDerivAt_euc3 (t := φ)
    (show HasDerivAt (fun s => -Real.cos θ * Real.cos s) (-Real.cos θ * -Real.sin φ) φ from
      by simpa [neg_mul] using (Real.hasDerivAt_cos φ).const_mul (-Real.cos θ))
    (show HasDerivAt (fun s => -Real.sin θ * Real.cos s) (-Real.sin θ * -Real.sin φ) φ from
      by simpa [neg_mul] using (Real.hasDerivAt_cos φ).const_mul (-Real.sin θ))
    (hasDerivAt_const φ (0:ℝ)) using 1
  ext i
  fin_cases i <;> simp [vecXθθ] <;> ring

/-! ## The grid, its step lemmas, and the ∂-closed scalar family -/

/-- The vecX derivative grid: `vecXFam a b = ∂θᵃ ∂φᵇ vecX`. -/
noncomputable def vecXFam : Fin 3 → Fin 2 → ℝ → ℝ → ℝ³
  | 0, 0 => vecX
  | 0, 1 => vecXφ
  | 1, 0 => vecXθ
  | 1, 1 => vecXθφ
  | 2, 0 => vecXθθ
  | 2, 1 => vecXθθφ

/-- One φ-derivative on the two-element grid coordinate: bump, folding
`1 ↦ 0` with a sign flip (`∂φ² = -id` entrywise on the X-family). -/
def famStepX : Fin 2 → Bool × Fin 2
  | 0 => (false, 1)
  | 1 => (true, 0)

lemma vecXFam_hasDerivAt_θ (a : Fin 3) (b : Fin 2) (θ φ : ℝ) :
    HasDerivAt (fun t => vecXFam a b t φ)
      (cond (famStep a).1 (-(vecXFam (famStep a).2 b θ φ))
        (vecXFam (famStep a).2 b θ φ)) θ := by
  fin_cases a <;> fin_cases b
  · exact hasDerivAt_vecX_θ θ φ
  · exact hasDerivAt_vecXφ_θ θ φ
  · exact hasDerivAt_vecXθ_θ θ φ
  · exact hasDerivAt_vecXθφ_θ θ φ
  · exact hasDerivAt_vecXθθ_θ θ φ
  · exact hasDerivAt_vecXθθφ_θ θ φ

lemma vecXFam_hasDerivAt_φ (a : Fin 3) (b : Fin 2) (θ φ : ℝ) :
    HasDerivAt (fun t => vecXFam a b θ t)
      (cond (famStepX b).1 (-(vecXFam a (famStepX b).2 θ φ))
        (vecXFam a (famStepX b).2 θ φ)) φ := by
  fin_cases a <;> fin_cases b
  · exact hasDerivAt_vecX_φ θ φ
  · exact hasDerivAt_vecXφ_φ θ φ
  · exact hasDerivAt_vecXθ_φ θ φ
  · exact hasDerivAt_vecXθφ_φ θ φ
  · exact hasDerivAt_vecXθθ_φ θ φ
  · exact hasDerivAt_vecXθθφ_φ θ φ

lemma vecXFam_norm_le_one (a : Fin 3) (b : Fin 2) (θ φ : ℝ) :
    ‖vecXFam a b θ φ‖ ≤ 1 := by
  fin_cases a <;> fin_cases b
  · exact le_of_eq (Bounding.vecX_norm_one θ φ)
  · exact vecXφ_norm_le_one θ φ
  · exact vecXθ_norm_le_one θ φ
  · exact vecXθφ_norm_le_one θ φ
  · exact vecXθθ_norm_le_one θ φ
  · exact vecXθθφ_norm_le_one θ φ

/-- Joint differentiability of a grid member in `(θ, φ)`. -/
lemma differentiableAt_vecXFam (a : Fin 3) (b : Fin 2) (y : E 2) :
    DifferentiableAt ℝ (fun z : E 2 => vecXFam a b (z.ofLp 0) (z.ofLp 1)) y := by
  fin_cases a <;> fin_cases b <;>
    (rw [differentiableAt_piLp]; intro i; fin_cases i <;>
      (simp [vecXFam, vecX, vecXθ, vecXφ, vecXθθ, vecXθφ, vecXθθφ]; try fun_prop))

/-- Coordinate extraction in `E 2` (private duplicates of the ones in
`SecondPartialOuter`). -/
private lemma coordX_same (i : Fin 2) (y : E 2) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E 2)).ofLp i = y.ofLp i + t := by simp

private lemma coordX_other {i j : Fin 2} (hij : j ≠ i) (y : E 2) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E 2)).ofLp j = y.ofLp j := by simp [hij]

/-- `nth_partial 0` (θ-direction) of `⟪V (θ, φ), P⟫` given the θ-derivative of
the vector family `V`. -/
private lemma nth_partial_vecX_e0 {P : ℝ³} {V : ℝ → ℝ → ℝ³} {V' : ℝ³} {y : E 2}
    (hdiff : DifferentiableAt ℝ (fun z : E 2 => V (z.ofLp 0) (z.ofLp 1)) y)
    (hV : HasDerivAt (fun t => V t (y.ofLp 1)) V' (y.ofLp 0)) :
    nth_partial 0 (fun z : E 2 => ⟪V (z.ofLp 0) (z.ofLp 1), P⟫) y = ⟪V', P⟫ := by
  show (fderiv ℝ _ y) (EuclideanSpace.single 0 1) = _
  rw [fderiv_inner_const _ P y _ hdiff]
  congr 1
  refine fderiv_single_eq hdiff ?_
  simp only [coordX_same, coordX_other (by decide : (1 : Fin 2) ≠ 0)]
  exact hasDerivAt_comp_add _ _ _ hV

/-- `nth_partial 1` (φ-direction) of `⟪V (θ, φ), P⟫`. -/
private lemma nth_partial_vecX_e1 {P : ℝ³} {V : ℝ → ℝ → ℝ³} {V' : ℝ³} {y : E 2}
    (hdiff : DifferentiableAt ℝ (fun z : E 2 => V (z.ofLp 0) (z.ofLp 1)) y)
    (hV : HasDerivAt (fun t => V (y.ofLp 0) t) V' (y.ofLp 1)) :
    nth_partial 1 (fun z : E 2 => ⟪V (z.ofLp 0) (z.ofLp 1), P⟫) y = ⟪V', P⟫ := by
  show (fderiv ℝ _ y) (EuclideanSpace.single 1 1) = _
  rw [fderiv_inner_const _ P y _ hdiff]
  congr 1
  refine fderiv_single_eq hdiff ?_
  simp only [coordX_same, coordX_other (by decide : (0 : Fin 2) ≠ 1)]
  exact hasDerivAt_comp_add _ _ _ hV

/-- The ∂-closed family of scalar functions `± ⟪∂θᵃ∂φᵇ X(θ,φ), P⟫`. -/
inductive IsVecXDerivFam (P : ℝ³) : (E 2 → ℝ) → Prop where
  | base (a : Fin 3) (b : Fin 2) :
      IsVecXDerivFam P (fun y => ⟪vecXFam a b (y.ofLp 0) (y.ofLp 1), P⟫)
  | neg {f} : IsVecXDerivFam P f → IsVecXDerivFam P (fun y => -(f y))

/-- The family is closed under partial derivatives. -/
lemma IsVecXDerivFam.nth_partial {P : ℝ³} {f : E 2 → ℝ}
    (hf : IsVecXDerivFam P f) (i : Fin 2) :
    IsVecXDerivFam P (nth_partial i f) := by
  induction hf with
  | neg _ ih => rw [nth_partial_neg]; exact ih.neg
  | base a b =>
    fin_cases i
    · -- θ-direction
      show IsVecXDerivFam P
        (GlobalTheorem.nth_partial 0 (fun y : E 2 => ⟪vecXFam a b (y.ofLp 0) (y.ofLp 1), P⟫))
      rcases hs : famStep a with ⟨c, a'⟩
      cases c
      · rw [show GlobalTheorem.nth_partial 0
              (fun y : E 2 => ⟪vecXFam a b (y.ofLp 0) (y.ofLp 1), P⟫)
            = fun y : E 2 => ⟪vecXFam a' b (y.ofLp 0) (y.ofLp 1), P⟫ from funext fun y =>
          nth_partial_vecX_e0 (differentiableAt_vecXFam a b y)
            (by simpa [hs] using vecXFam_hasDerivAt_θ a b (y.ofLp 0) (y.ofLp 1))]
        exact .base a' b
      · rw [show GlobalTheorem.nth_partial 0
              (fun y : E 2 => ⟪vecXFam a b (y.ofLp 0) (y.ofLp 1), P⟫)
            = fun y : E 2 => -(⟪vecXFam a' b (y.ofLp 0) (y.ofLp 1), P⟫ : ℝ) from
          funext fun y => by
            rw [nth_partial_vecX_e0 (differentiableAt_vecXFam a b y)
              (by simpa [hs] using vecXFam_hasDerivAt_θ a b (y.ofLp 0) (y.ofLp 1))]
            exact inner_neg_left _ _]
        exact (IsVecXDerivFam.base a' b).neg
    · -- φ-direction
      show IsVecXDerivFam P
        (GlobalTheorem.nth_partial 1 (fun y : E 2 => ⟪vecXFam a b (y.ofLp 0) (y.ofLp 1), P⟫))
      rcases hs : famStepX b with ⟨c, b'⟩
      cases c
      · rw [show GlobalTheorem.nth_partial 1
              (fun y : E 2 => ⟪vecXFam a b (y.ofLp 0) (y.ofLp 1), P⟫)
            = fun y : E 2 => ⟪vecXFam a b' (y.ofLp 0) (y.ofLp 1), P⟫ from funext fun y =>
          nth_partial_vecX_e1 (differentiableAt_vecXFam a b y)
            (by simpa [hs] using vecXFam_hasDerivAt_φ a b (y.ofLp 0) (y.ofLp 1))]
        exact .base a b'
      · rw [show GlobalTheorem.nth_partial 1
              (fun y : E 2 => ⟪vecXFam a b (y.ofLp 0) (y.ofLp 1), P⟫)
            = fun y : E 2 => -(⟪vecXFam a b' (y.ofLp 0) (y.ofLp 1), P⟫ : ℝ) from
          funext fun y => by
            rw [nth_partial_vecX_e1 (differentiableAt_vecXFam a b y)
              (by simpa [hs] using vecXFam_hasDerivAt_φ a b (y.ofLp 0) (y.ofLp 1))]
            exact inner_neg_left _ _]
        exact (IsVecXDerivFam.base a b').neg

/-- Every family member is pointwise bounded by `‖P‖`. -/
lemma IsVecXDerivFam.abs_le {P : ℝ³} {f : E 2 → ℝ}
    (hf : IsVecXDerivFam P f) (y : E 2) : |f y| ≤ ‖P‖ := by
  induction hf with
  | base a b =>
    calc |⟪vecXFam a b (y.ofLp 0) (y.ofLp 1), P⟫|
        ≤ ‖vecXFam a b (y.ofLp 0) (y.ofLp 1)‖ * ‖P‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖P‖ :=
          mul_le_mul_of_nonneg_right (vecXFam_norm_le_one a b _ _) (norm_nonneg _)
      _ = ‖P‖ := one_mul _
  | neg _ ih => simpa using ih

/-- The scalar projection of `vecX` is `C³`. -/
lemma vecX_inner_contDiff (P : ℝ³) :
    ContDiff ℝ 3 (fun y : E 2 => ⟪vecX (y.ofLp 0) (y.ofLp 1), P⟫) := by
  apply ContDiff.inner ℝ _ contDiff_const
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> (simp [vecX]; fun_prop)

/-- All third partials of `⟪vecX (θ,φ), P⟫` are bounded by `‖P‖`. -/
lemma vecX_third_partials_bounded (P : ℝ³) :
    third_partials_bounded (fun y : E 2 => ⟪vecX (y.ofLp 0) (y.ofLp 1), P⟫) ‖P‖ :=
  fun x i j k =>
    ((((IsVecXDerivFam.base (P := P) 0 0).nth_partial k).nth_partial j).nth_partial i).abs_le x

/-- First partials of `⟪vecX (θ,φ), P⟫` at `x`, identified. -/
lemma first_partial_vecX_inner_e0 (P : ℝ³) (x : E 2) :
    nth_partial 0 (fun y : E 2 => ⟪vecX (y.ofLp 0) (y.ofLp 1), P⟫) x =
      ⟪vecXθ (x.ofLp 0) (x.ofLp 1), P⟫ :=
  nth_partial_vecX_e0 (differentiableAt_vecXFam 0 0 x)
    (hasDerivAt_vecX_θ (x.ofLp 0) (x.ofLp 1))

lemma first_partial_vecX_inner_e1 (P : ℝ³) (x : E 2) :
    nth_partial 1 (fun y : E 2 => ⟪vecX (y.ofLp 0) (y.ofLp 1), P⟫) x =
      ⟪vecXφ (x.ofLp 0) (x.ofLp 1), P⟫ :=
  nth_partial_vecX_e1 (differentiableAt_vecXFam 0 0 x)
    (hasDerivAt_vecX_φ (x.ofLp 0) (x.ofLp 1))

/-- Second partials of `⟪vecX (θ,φ), P⟫` at `x`, identified:
the table is `[[Xθθ, Xθφ], [Xθφ, -X]]`. -/
lemma second_partial_vecX_inner_eq (P : ℝ³) (x : E 2) (i j : Fin 2) :
    nth_partial i (nth_partial j (fun y : E 2 => ⟪vecX (y.ofLp 0) (y.ofLp 1), P⟫)) x =
      ⟪![![vecXθθ, vecXθφ], ![vecXθφ, fun θ φ => -(vecX θ φ)]] i j
          (x.ofLp 0) (x.ofLp 1), P⟫ := by
  have h0 : GlobalTheorem.nth_partial 0 (fun y : E 2 => ⟪vecX (y.ofLp 0) (y.ofLp 1), P⟫)
      = fun y : E 2 => ⟪vecXθ (y.ofLp 0) (y.ofLp 1), P⟫ :=
    funext fun y => first_partial_vecX_inner_e0 P y
  have h1 : GlobalTheorem.nth_partial 1 (fun y : E 2 => ⟪vecX (y.ofLp 0) (y.ofLp 1), P⟫)
      = fun y : E 2 => ⟪vecXφ (y.ofLp 0) (y.ofLp 1), P⟫ :=
    funext fun y => first_partial_vecX_inner_e1 P y
  have hdθ : DifferentiableAt ℝ (fun z : E 2 => vecXθ (z.ofLp 0) (z.ofLp 1)) x :=
    differentiableAt_vecXFam 1 0 x
  have hdφ : DifferentiableAt ℝ (fun z : E 2 => vecXφ (z.ofLp 0) (z.ofLp 1)) x :=
    differentiableAt_vecXFam 0 1 x
  fin_cases i <;> fin_cases j
  · show GlobalTheorem.nth_partial 0 (GlobalTheorem.nth_partial 0 _) x = _
    rw [h0, nth_partial_vecX_e0 hdθ (hasDerivAt_vecXθ_θ (x.ofLp 0) (x.ofLp 1))]
    rfl
  · show GlobalTheorem.nth_partial 0 (GlobalTheorem.nth_partial 1 _) x = _
    rw [h1, nth_partial_vecX_e0 hdφ (hasDerivAt_vecXφ_θ (x.ofLp 0) (x.ofLp 1))]
    rfl
  · show GlobalTheorem.nth_partial 1 (GlobalTheorem.nth_partial 0 _) x = _
    rw [h0, nth_partial_vecX_e1 hdθ (hasDerivAt_vecXθ_φ (x.ofLp 0) (x.ofLp 1))]
    rfl
  · show GlobalTheorem.nth_partial 1 (GlobalTheorem.nth_partial 1 _) x = _
    rw [h1, nth_partial_vecX_e1 hdφ (hasDerivAt_vecXφ_φ (x.ofLp 0) (x.ofLp 1))]
    rfl

/-! ## The second-order A-condition transfer -/

private lemma innerParamsX_0 (θ φ : ℝ) : ((!₂[θ, φ] : E 2)).ofLp 0 = θ := rfl
private lemma innerParamsX_1 (θ φ : ℝ) : ((!₂[θ, φ] : E 2)).ofLp 1 = φ := rfl

/-- **Second-order [SY25] Lemma 14**: the orientation condition transfers from
the center to the whole per-axis box, charging the exact first and second
partials of `⟪X, P⟫` at the center plus a cubic remainder (`‖P‖ ≤ 1`).
Replaces the Lipschitz bound `√2·ε` of `XPgt0` with typically much smaller
center data. -/
theorem XPgt0₂ {P : ℝ³} {εθ εφ θ θ_ φ φ_ : ℝ} (hP : ‖P‖ ≤ 1)
    (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ) (hθ : |θ - θ_| ≤ εθ) (hφ : |φ - φ_| ≤ εφ)
    (hX : εθ * |⟪vecXθ θ_ φ_, P⟫| + εφ * |⟪vecXφ θ_ φ_, P⟫|
        + (1/2) * (εθ^2 * |⟪vecXθθ θ_ φ_, P⟫| + 2*(εθ*εφ) * |⟪vecXθφ θ_ φ_, P⟫|
            + εφ^2 * |⟪vecX θ_ φ_, P⟫|)
        + (εθ + εφ)^3/6 < ⟪vecX θ_ φ_, P⟫) :
    0 < ⟪vecX θ φ, P⟫ := by
  set f : E 2 → ℝ := fun y => ⟪vecX (y.ofLp 0) (y.ofLp 1), P⟫ with hf
  have hεv : ∀ i, 0 ≤ (![εθ, εφ] : Fin 2 → ℝ) i := by
    intro i; fin_cases i
    · exact hεθ
    · exact hεφ
  have hdiffv : ∀ i : Fin 2,
      |(!₂[θ_, φ_] : E 2) i - (!₂[θ, φ] : E 2) i| ≤ ![εθ, εφ] i := by
    intro i; fin_cases i
    · simpa [abs_sub_comm] using hθ
    · simpa [abs_sub_comm] using hφ
  have htpb : third_partials_bounded f 1 := fun x i j k =>
    le_trans (vecX_third_partials_bounded P x i j k) hP
  have key := bounded_partials_control_difference2 f (vecX_inner_contDiff P)
    !₂[θ_, φ_] !₂[θ, φ] ![εθ, εφ] hεv hdiffv htpb
  rw [show ∑ i, (![εθ, εφ] : Fin 2 → ℝ) i = εθ + εφ by simp [Fin.sum_univ_two]] at key
  have hsum1 : ∑ i, (![εθ, εφ] : Fin 2 → ℝ) i * |nth_partial i f !₂[θ_, φ_]|
      = εθ * |⟪vecXθ θ_ φ_, P⟫| + εφ * |⟪vecXφ θ_ φ_, P⟫| := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hf,
      first_partial_vecX_inner_e0, first_partial_vecX_inner_e1,
      innerParamsX_0, innerParamsX_1]
  have hsum2 : ∑ i, ∑ j, (![εθ, εφ] : Fin 2 → ℝ) i * ![εθ, εφ] j *
        |nth_partial i (nth_partial j f) !₂[θ_, φ_]|
      = εθ^2 * |⟪vecXθθ θ_ φ_, P⟫| + 2*(εθ*εφ) * |⟪vecXθφ θ_ φ_, P⟫|
        + εφ^2 * |⟪vecX θ_ φ_, P⟫| := by
    simp only [hf, second_partial_vecX_inner_eq, innerParamsX_0, innerParamsX_1]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      inner_neg_left, abs_neg]
    ring
  rw [hsum1, hsum2] at key
  have hfx : f !₂[θ_, φ_] = ⟪vecX θ_ φ_, P⟫ := rfl
  have hfy : f !₂[θ, φ] = ⟪vecX θ φ, P⟫ := rfl
  rw [hfx, hfy] at key
  have := abs_le.mp key
  linarith [this.1]

end GlobalTheorem

end
