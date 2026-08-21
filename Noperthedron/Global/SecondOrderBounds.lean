module

public import Noperthedron.Global.RotationPartials
public import Noperthedron.Global.BoundedPartialsControlDifference

@[expose] public section


/-!
# Second-order variation bounds for applied rotation vectors

Instantiations of `norm_sub_control_difference2` at the two vector shapes of
the local theorem: the outer applied vector `M(θ,φ)P` and the inner applied
vector `R(α)(M(θ,φ)P)`.  The direction-uniform data comes from the existing
`rotproj_outer`/`rotproj_inner` machinery (smoothness, the ∂-closed-family
third bounds, and the first/second partial identifications), and the
resulting `b1`/`b2` bounds are the norms of the family-applied vectors at the
center — exactly the `Δ`-terms of the second-order local certificate.
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private lemma abs_inner_le_norm_of_unit {w u : ℝ²} (hu : ‖u‖ = 1) : |⟪w, u⟫| ≤ ‖w‖ := by
  calc |⟪w, u⟫| ≤ ‖w‖ * ‖u‖ := abs_real_inner_le_norm _ _
    _ = ‖w‖ := by rw [hu, mul_one]

private lemma norm_rotR_apply_le (a : ℝ) (w : ℝ²) : ‖rotR a w‖ ≤ ‖w‖ := by
  calc ‖rotR a w‖ ≤ ‖rotR a‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖w‖ := by rw [Bounding.rotR_norm_one, one_mul]

private lemma norm_rotR'_apply_le (a : ℝ) (w : ℝ²) : ‖rotR' a w‖ ≤ ‖w‖ := by
  calc ‖rotR' a w‖ ≤ ‖rotR' a‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖w‖ := by rw [Bounding.rotR'_norm_one, one_mul]

/-- The second-order variation budget of the outer applied vector `M(θ,φ)P`
over a per-axis box of radii `(εθ, εφ)` centered at `(θ_, φ_)`. -/
noncomputable def ΔrotM (P : ℝ³) (εθ εφ θ_ φ_ : ℝ) : ℝ :=
  εθ * ‖rotMθ θ_ φ_ P‖ + εφ * ‖rotMφ θ_ φ_ P‖
  + (1/2) * (εθ^2 * ‖rotMθθ θ_ φ_ P‖ + 2*(εθ*εφ) * ‖rotMθφ θ_ φ_ P‖
      + εφ^2 * ‖rotMφφ θ_ φ_ P‖)
  + ‖P‖ * (εθ + εφ)^3 / 6

/-- The second-order variation budget of the inner applied vector
`R(α)(M(θ,φ)P)` (the `α`-slots use the `R`-isometry). -/
noncomputable def ΔrotRM (P : ℝ³) (εα εθ εφ θ_ φ_ : ℝ) : ℝ :=
  εα * ‖rotM θ_ φ_ P‖ + εθ * ‖rotMθ θ_ φ_ P‖ + εφ * ‖rotMφ θ_ φ_ P‖
  + (1/2) * (εα^2 * ‖rotM θ_ φ_ P‖
      + 2*(εα*εθ) * ‖rotMθ θ_ φ_ P‖ + 2*(εα*εφ) * ‖rotMφ θ_ φ_ P‖
      + εθ^2 * ‖rotMθθ θ_ φ_ P‖ + 2*(εθ*εφ) * ‖rotMθφ θ_ φ_ P‖
      + εφ^2 * ‖rotMφφ θ_ φ_ P‖)
  + ‖P‖ * (εα + εθ + εφ)^3 / 6

/-- **Second-order variation of the outer applied vector.**  The per-axis
first-order charges are the norms of the derivative-family vectors at the
center, the second-order charges the second-family norms, and the remainder
is cubic.  Replaces the Lipschitz bound `‖M(θ,φ)P − M(θ̄,φ̄)P‖ ≤ √2·ε·‖P‖`. -/
theorem norm_rotM_apply_sub_le {P : ℝ³} {εθ εφ θ θ_ φ φ_ : ℝ}
    (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ) (hθ : |θ - θ_| ≤ εθ) (hφ : |φ - φ_| ≤ εφ) :
    ‖rotM θ φ P - rotM θ_ φ_ P‖ ≤ ΔrotM P εθ εφ θ_ φ_ := by
  unfold ΔrotM
  set v : E 2 → ℝ² := fun z => rotM (z.ofLp 0) (z.ofLp 1) P with hv
  set b1 : Fin 2 → ℝ := ![‖rotMθ θ_ φ_ P‖, ‖rotMφ θ_ φ_ P‖] with hb1def
  set b2 : Fin 2 → Fin 2 → ℝ :=
    fun i j => ![![‖rotMθθ θ_ φ_ P‖, ‖rotMθφ θ_ φ_ P‖],
                 ![‖rotMθφ θ_ φ_ P‖, ‖rotMφφ θ_ φ_ P‖]] i j with hb2def
  have hεv : ∀ i, 0 ≤ (![εθ, εφ] : Fin 2 → ℝ) i := by
    intro i; fin_cases i
    · exact hεθ
    · exact hεφ
  have hdiffv : ∀ i : Fin 2,
      |(!₂[θ_, φ_] : E 2) i - (!₂[θ, φ] : E 2) i| ≤ ![εθ, εφ] i := by
    intro i; fin_cases i
    · simpa [abs_sub_comm] using hθ
    · simpa [abs_sub_comm] using hφ
  have hb1 : ∀ i, 0 ≤ b1 i := by
    intro i; fin_cases i <;> simp [hb1def]
  have hb2 : ∀ i j, 0 ≤ b2 i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [hb2def]
  have key := norm_sub_control_difference2 v !₂[θ_, φ_] !₂[θ, φ] ![εθ, εφ] hεv hdiffv
    (M := ‖P‖) b1 b2 hb1 hb2 (norm_nonneg P) ?_
  · rw [show v !₂[θ_, φ_] = rotM θ_ φ_ P from rfl, show v !₂[θ, φ] = rotM θ φ P from rfl,
      norm_sub_rev] at key
    refine key.trans (le_of_eq ?_)
    rw [show ∑ i, (![εθ, εφ] : Fin 2 → ℝ) i = εθ + εφ by simp [Fin.sum_univ_two]]
    simp only [Fin.sum_univ_two, hb1def, hb2def, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · intro u hu
    refine ⟨rotation_partials_exist_outer, rotation_third_partials_bounded_outer P hu,
      ?_, ?_⟩
    · intro i
      fin_cases i
      · show |GlobalTheorem.nth_partial 0 (fun z => ⟪v z, u⟫) !₂[θ_, φ_]| ≤ b1 0
        rw [show GlobalTheorem.nth_partial 0 (fun z => ⟪v z, u⟫) !₂[θ_, φ_]
              = ⟪rotMθ θ_ φ_ P, u⟫ from first_partial_rotproj_outer_e0 P u _]
        simpa [hb1def] using abs_inner_le_norm_of_unit (w := rotMθ θ_ φ_ P) hu
      · show |GlobalTheorem.nth_partial 1 (fun z => ⟪v z, u⟫) !₂[θ_, φ_]| ≤ b1 1
        rw [show GlobalTheorem.nth_partial 1 (fun z => ⟪v z, u⟫) !₂[θ_, φ_]
              = ⟪rotMφ θ_ φ_ P, u⟫ from first_partial_rotproj_outer_e1 P u _]
        simpa [hb1def] using abs_inner_le_norm_of_unit (w := rotMφ θ_ φ_ P) hu
    · intro i j
      rw [show GlobalTheorem.nth_partial i (GlobalTheorem.nth_partial j (fun z => ⟪v z, u⟫))
            !₂[θ_, φ_] = ⟪outer_second_partial_A θ_ φ_ i j P, u⟫ from
          second_partial_rotproj_outer_eq P u _ i j]
      refine (abs_inner_le_norm_of_unit hu).trans (le_of_eq ?_)
      fin_cases i <;> fin_cases j <;> simp [outer_second_partial_A, hb2def]

set_option linter.unusedSimpArgs false in
/-- **Second-order variation of the inner applied vector** `R(α)(M(θ,φ)P)`,
with the `α`-slots charged at `‖M̄P‖`-type norms via the `R`-isometry.
Replaces the Lipschitz bound `√5·ε·‖P‖`. -/
theorem norm_rotRM_apply_sub_le {P : ℝ³} {εα εθ εφ α α_ θ θ_ φ φ_ : ℝ}
    (hεα : 0 ≤ εα) (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    (hα : |α - α_| ≤ εα) (hθ : |θ - θ_| ≤ εθ) (hφ : |φ - φ_| ≤ εφ) :
    ‖rotR α (rotM θ φ P) - rotR α_ (rotM θ_ φ_ P)‖ ≤ ΔrotRM P εα εθ εφ θ_ φ_ := by
  unfold ΔrotRM
  set v : E 3 → ℝ² := fun z => rotR (z.ofLp 0) (rotM (z.ofLp 1) (z.ofLp 2) P) with hv
  set b1 : Fin 3 → ℝ :=
    ![‖rotM θ_ φ_ P‖, ‖rotMθ θ_ φ_ P‖, ‖rotMφ θ_ φ_ P‖] with hb1def
  set b2 : Fin 3 → Fin 3 → ℝ :=
    fun i j => ![![‖rotM θ_ φ_ P‖, ‖rotMθ θ_ φ_ P‖, ‖rotMφ θ_ φ_ P‖],
                 ![‖rotMθ θ_ φ_ P‖, ‖rotMθθ θ_ φ_ P‖, ‖rotMθφ θ_ φ_ P‖],
                 ![‖rotMφ θ_ φ_ P‖, ‖rotMθφ θ_ φ_ P‖, ‖rotMφφ θ_ φ_ P‖]] i j with hb2def
  have hεv : ∀ i, 0 ≤ (![εα, εθ, εφ] : Fin 3 → ℝ) i := by
    intro i; fin_cases i
    · exact hεα
    · exact hεθ
    · exact hεφ
  have hdiffv : ∀ i : Fin 3,
      |(!₂[α_, θ_, φ_] : E 3) i - (!₂[α, θ, φ] : E 3) i| ≤ ![εα, εθ, εφ] i := by
    intro i; fin_cases i
    · simpa [abs_sub_comm] using hα
    · simpa [abs_sub_comm] using hθ
    · simpa [abs_sub_comm] using hφ
  have hb1 : ∀ i, 0 ≤ b1 i := by
    intro i; fin_cases i <;> simp [hb1def]
  have hb2 : ∀ i j, 0 ≤ b2 i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [hb2def]
  have key := norm_sub_control_difference2 v !₂[α_, θ_, φ_] !₂[α, θ, φ] ![εα, εθ, εφ]
    hεv hdiffv (M := ‖P‖) b1 b2 hb1 hb2 (norm_nonneg P) ?_
  · rw [show v !₂[α_, θ_, φ_] = rotR α_ (rotM θ_ φ_ P) from rfl,
      show v !₂[α, θ, φ] = rotR α (rotM θ φ P) from rfl, norm_sub_rev] at key
    refine key.trans (le_of_eq ?_)
    rw [show ∑ i, (![εα, εθ, εφ] : Fin 3 → ℝ) i = εα + εθ + εφ by simp [Fin.sum_univ_three]]
    simp only [Fin.sum_univ_three, hb1def, hb2def, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  · intro u hu
    refine ⟨rotation_partials_exist, rotation_third_partials_bounded P hu, ?_, ?_⟩
    · intro i
      fin_cases i
      · show |GlobalTheorem.nth_partial 0 (fun z => ⟪v z, u⟫) !₂[α_, θ_, φ_]| ≤ b1 0
        rw [show GlobalTheorem.nth_partial 0 (fun z => ⟪v z, u⟫) !₂[α_, θ_, φ_]
              = ⟪rotR' α_ (rotM θ_ φ_ P), u⟫ from congrFun (nth_partial_rotproj_inner_e0 P u) _]
        refine (abs_inner_le_norm_of_unit hu).trans ?_
        simpa [hb1def] using norm_rotR'_apply_le α_ (rotM θ_ φ_ P)
      · show |GlobalTheorem.nth_partial 1 (fun z => ⟪v z, u⟫) !₂[α_, θ_, φ_]| ≤ b1 1
        rw [show GlobalTheorem.nth_partial 1 (fun z => ⟪v z, u⟫) !₂[α_, θ_, φ_]
              = ⟪rotR α_ (rotMθ θ_ φ_ P), u⟫ from congrFun (nth_partial_rotproj_inner_e1 P u) _]
        refine (abs_inner_le_norm_of_unit hu).trans ?_
        simpa [hb1def] using norm_rotR_apply_le α_ (rotMθ θ_ φ_ P)
      · show |GlobalTheorem.nth_partial 2 (fun z => ⟪v z, u⟫) !₂[α_, θ_, φ_]| ≤ b1 2
        rw [show GlobalTheorem.nth_partial 2 (fun z => ⟪v z, u⟫) !₂[α_, θ_, φ_]
              = ⟪rotR α_ (rotMφ θ_ φ_ P), u⟫ from congrFun (nth_partial_rotproj_inner_e2 P u) _]
        refine (abs_inner_le_norm_of_unit hu).trans ?_
        simpa [hb1def] using norm_rotR_apply_le α_ (rotMφ θ_ φ_ P)
    · intro i j
      rw [show GlobalTheorem.nth_partial i (GlobalTheorem.nth_partial j (fun z => ⟪v z, u⟫))
            !₂[α_, θ_, φ_] = ⟪inner_second_partial_A α_ θ_ φ_ i j P, u⟫ from
          second_partial_rotproj_inner_eq P u _ i j]
      refine (abs_inner_le_norm_of_unit hu).trans ?_
      fin_cases i <;> fin_cases j <;>
        simp only [inner_second_partial_A, hb2def, ContinuousLinearMap.coe_comp,
          Function.comp_apply, neg_apply, norm_neg, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
          Fin.isValue]
      · exact norm_rotR_apply_le α_ (rotM θ_ φ_ P)
      · exact norm_rotR'_apply_le α_ (rotMθ θ_ φ_ P)
      · exact norm_rotR'_apply_le α_ (rotMφ θ_ φ_ P)
      · exact norm_rotR'_apply_le α_ (rotMθ θ_ φ_ P)
      · exact norm_rotR_apply_le α_ (rotMθθ θ_ φ_ P)
      · exact norm_rotR_apply_le α_ (rotMθφ θ_ φ_ P)
      · exact norm_rotR'_apply_le α_ (rotMφ θ_ φ_ P)
      · exact norm_rotR_apply_le α_ (rotMθφ θ_ φ_ P)
      · exact norm_rotR_apply_le α_ (rotMφφ θ_ φ_ P)

/-- **Second-order r-condition transfer** ([SY25] Lemma 15 upgraded): a lower
bound on `‖M P‖` at the center with the variation budget as slack transfers
to the whole box. -/
theorem norm_M_apply_gt₂ {P : ℝ³} {r εθ εφ θ θ_ φ φ_ : ℝ}
    (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ) (hθ : |θ - θ_| ≤ εθ) (hφ : |φ - φ_| ≤ εφ)
    (h : r + ΔrotM P εθ εφ θ_ φ_ < ‖rotM θ_ φ_ P‖) :
    r < ‖rotM θ φ P‖ := by
  have hvar := norm_rotM_apply_sub_le (P := P) hεθ hεφ hθ hφ
  have htri : ‖rotM θ_ φ_ P‖ - ‖rotM θ φ P‖ ≤ ‖rotM θ φ P - rotM θ_ φ_ P‖ := by
    rw [norm_sub_rev]
    exact norm_sub_norm_le _ _
  linarith

/-- **Second-order δ-transfer** ([SY25] Lemma 30 upgraded): the distance
between the two shadows at any pose in the box is bounded by its center value
plus the inner and outer variation budgets (the two parts are separable). -/
theorem inCirc₂ {P Q : ℝ³}
    {δ εα εθ₁ εφ₁ εθ₂ εφ₂ α α_ θ₁ θ₁_ φ₁ φ₁_ θ₂ θ₂_ φ₂ φ₂_ : ℝ}
    (hεα : 0 ≤ εα) (hεθ₁ : 0 ≤ εθ₁) (hεφ₁ : 0 ≤ εφ₁)
    (hεθ₂ : 0 ≤ εθ₂) (hεφ₂ : 0 ≤ εφ₂)
    (hα : |α - α_| ≤ εα) (hθ₁ : |θ₁ - θ₁_| ≤ εθ₁) (hφ₁ : |φ₁ - φ₁_| ≤ εφ₁)
    (hθ₂ : |θ₂ - θ₂_| ≤ εθ₂) (hφ₂ : |φ₂ - φ₂_| ≤ εφ₂)
    (hδ : ‖rotR α_ (rotM θ₁_ φ₁_ P) - rotM θ₂_ φ₂_ Q‖
        + ΔrotRM P εα εθ₁ εφ₁ θ₁_ φ₁_ + ΔrotM Q εθ₂ εφ₂ θ₂_ φ₂_ ≤ 2 * δ) :
    ‖rotR α (rotM θ₁ φ₁ P) - rotM θ₂ φ₂ Q‖ ≤ 2 * δ := by
  have h1 := norm_rotRM_apply_sub_le (P := P) hεα hεθ₁ hεφ₁ hα hθ₁ hφ₁
  have h2 := norm_rotM_apply_sub_le (P := Q) hεθ₂ hεφ₂ hθ₂ hφ₂
  have hrearr : rotR α (rotM θ₁ φ₁ P) - rotM θ₂ φ₂ Q
      = (rotR α_ (rotM θ₁_ φ₁_ P) - rotM θ₂_ φ₂_ Q)
        + (rotR α (rotM θ₁ φ₁ P) - rotR α_ (rotM θ₁_ φ₁_ P))
        - (rotM θ₂ φ₂ Q - rotM θ₂_ φ₂_ Q) := by abel
  rw [hrearr]
  calc ‖(rotR α_ (rotM θ₁_ φ₁_ P) - rotM θ₂_ φ₂_ Q)
        + (rotR α (rotM θ₁ φ₁ P) - rotR α_ (rotM θ₁_ φ₁_ P))
        - (rotM θ₂ φ₂ Q - rotM θ₂_ φ₂_ Q)‖
      ≤ ‖(rotR α_ (rotM θ₁_ φ₁_ P) - rotM θ₂_ φ₂_ Q)
          + (rotR α (rotM θ₁ φ₁ P) - rotR α_ (rotM θ₁_ φ₁_ P))‖
        + ‖rotM θ₂ φ₂ Q - rotM θ₂_ φ₂_ Q‖ := norm_sub_le _ _
    _ ≤ ‖rotR α_ (rotM θ₁_ φ₁_ P) - rotM θ₂_ φ₂_ Q‖
        + ‖rotR α (rotM θ₁ φ₁ P) - rotR α_ (rotM θ₁_ φ₁_ P)‖
        + ‖rotM θ₂ φ₂ Q - rotM θ₂_ φ₂_ Q‖ := by
          linarith [norm_add_le (rotR α_ (rotM θ₁_ φ₁_ P) - rotM θ₂_ φ₂_ Q)
            (rotR α (rotM θ₁ φ₁ P) - rotR α_ (rotM θ₁_ φ₁_ P))]
    _ ≤ 2 * δ := by linarith

/-- **Abstract second-order quotient transfer** (the core of [SY25] Lemma 33):
a cosine quotient at a displaced pose is bounded below by center data with
variation budgets on the numerator and the two denominator factors. -/
theorem quotient_ge_of_bounds {num num_ n1 n1_ n2 n2_ ΔN Δ1 Δ2 : ℝ}
    (hnum : |num - num_| ≤ ΔN) (h1 : |n1 - n1_| ≤ Δ1) (h2 : |n2 - n2_| ≤ Δ2)
    (hn1 : 0 < n1) (hn2 : 0 < n2) (hpos : 0 ≤ num_ - ΔN) :
    (num_ - ΔN) / ((n1_ + Δ1) * (n2_ + Δ2)) ≤ num / (n1 * n2) := by
  have hnum' : num_ - ΔN ≤ num := by
    have := abs_le.mp hnum
    linarith [this.1]
  have h1' : n1 ≤ n1_ + Δ1 := by
    have := abs_le.mp h1
    linarith [this.2]
  have h2' : n2 ≤ n2_ + Δ2 := by
    have := abs_le.mp h2
    linarith [this.2]
  have hd1 : 0 < n1_ + Δ1 := lt_of_lt_of_le hn1 h1'
  have hd2 : 0 < n2_ + Δ2 := lt_of_lt_of_le hn2 h2'
  gcongr
  exact le_trans hpos hnum'

end GlobalTheorem

end
