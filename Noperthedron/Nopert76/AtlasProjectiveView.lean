module

public import Noperthedron.Nopert76.AtlasEdgeCertificate
public import Noperthedron.Nopert76.AtlasFundamentalPrune
public import Noperthedron.SnubCube.ProjectiveView

@[expose] public section

/-!
# A signed projective atlas for Nopert #214 viewing directions

Unlike the snub cube, Nopert #214 does not have enough symmetry to move
every outer view into one positive chamber.  Eight signed coordinate
triangles cover the whole sphere.  Dividing a unit view by its signed
coordinate sum puts it in the appropriate rational triangle, and that sum
is at least one.
-/

namespace Noperthedron.Nopert76.AtlasProjectiveView

open scoped RealInnerProductSpace
open AtlasEdgeCertificate
open Noperthedron.SnubCube.ProjectiveView

abbrev Vector (R : Type) := Fin 3 → R
abbrev Triangle (R : Type) := Fin 3 → Vector R

/-- The eight coordinate sign patterns, in binary order. -/
def rootSign (root : Fin 8) : Vector ℚ := ![
  ![1, 1, 1], ![1, 1, -1], ![1, -1, 1], ![1, -1, -1],
  ![-1, 1, 1], ![-1, 1, -1], ![-1, -1, 1], ![-1, -1, -1]] root

@[simp] theorem rootSign_sq (root : Fin 8) (c : Fin 3) :
    rootSign root c ^ 2 = 1 := by
  fin_cases root <;> fin_cases c <;> norm_num [rootSign]

def signedBasis (root : Fin 8) (c : Fin 3) : Vector ℚ :=
  fun d => if c = d then rootSign root c else 0

/-- One signed coordinate face of the projective octahedron. -/
def rootTriangle (root : Fin 8) : Triangle ℚ :=
  fun c => signedBasis root c

/-- A rational projective triangle containing the exact upper fivefold
viewing wedge.  Its slanted vertex has slope `31/10`, just above
`tan(2π/5)`. -/
def upperWedgeTriangle : Triangle ℚ :=
  ![![1, 0, 0], ![10 / 41, 31 / 41, 0], ![0, 0, 1]]

/-- The two signed projective roots that meet the exact fivefold-reduced
viewing wedge. -/
def wedgeRoot (root : Fin 2) : Fin 8 :=
  ⟨root.val, by omega⟩

noncomputable def viewScale (root : Fin 8) (p : AtlasPose ℝ) : ℝ :=
  ∑ c, (rootSign root c : ℝ) * viewVector p c

noncomputable def normalizedView (root : Fin 8)
    (p : AtlasPose ℝ) : Vector ℝ :=
  fun c => viewVector p c / viewScale root p

theorem one_le_viewScale_of_sign {root : Fin 8} {p : AtlasPose ℝ}
    (hsign : ∀ c, 0 ≤ (rootSign root c : ℝ) * viewVector p c) :
    1 ≤ viewScale root p := by
  have hnorm := viewVector_norm p
  have hnormsq := congrArg (fun x : ℝ => x ^ 2) hnorm
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs,
    Fin.sum_univ_three] at hnormsq
  have h0 := hsign 0
  have h1 := hsign 1
  have h2 := hsign 2
  have hs0 : ((rootSign root 0 : ℚ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast rootSign_sq root 0
  have hs1 : ((rootSign root 1 : ℚ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast rootSign_sq root 1
  have hs2 : ((rootSign root 2 : ℚ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast rootSign_sq root 2
  unfold viewScale
  simp only [Fin.sum_univ_three]
  nlinarith

theorem normalizedView_mem_root_of_sign {root : Fin 8}
    {p : AtlasPose ℝ}
    (hsign : ∀ c, 0 ≤ (rootSign root c : ℝ) * viewVector p c) :
    InTriangle (toReal (rootTriangle root)) (normalizedView root p) := by
  have hscale := one_le_viewScale_of_sign hsign
  have hscale0 : 0 < viewScale root p := lt_of_lt_of_le (by norm_num) hscale
  let weight : Vector ℝ := fun c =>
    (rootSign root c : ℝ) * viewVector p c / viewScale root p
  refine ⟨weight, ?_, ?_, ?_⟩
  · intro c
    exact div_nonneg (hsign c) hscale0.le
  · simp only [weight]
    rw [← Finset.sum_div]
    exact div_self hscale0.ne'
  · funext c
    fin_cases c
    · simp [normalizedView, affinePoint, rootTriangle, signedBasis,
        toReal, weight, Fin.sum_univ_three]
      field_simp [hscale0.ne']
      rw [show ((rootSign root 0 : ℚ) : ℝ) ^ 2 = 1 by
        exact_mod_cast rootSign_sq root 0]
      ring
    · simp [normalizedView, affinePoint, rootTriangle, signedBasis,
        toReal, weight, Fin.sum_univ_three]
      field_simp [hscale0.ne']
      rw [show ((rootSign root 1 : ℚ) : ℝ) ^ 2 = 1 by
        exact_mod_cast rootSign_sq root 1]
      ring
    · simp [normalizedView, affinePoint, rootTriangle, signedBasis,
        toReal, weight, Fin.sum_univ_three]
      field_simp [hscale0.ne']
      rw [show ((rootSign root 2 : ℚ) : ℝ) ^ 2 = 1 by
        exact_mod_cast rootSign_sq root 2]
      ring

/-- In the exact symmetry-reduced wedge, the first two viewing coordinates
are nonnegative. -/
theorem viewVector_first_two_nonneg {p : AtlasPose ℝ}
    (hview : p.InViewWedge) :
    0 ≤ viewVector p 0 ∧ 0 ≤ viewVector p 1 := by
  have hthetaHalf : p.θ ≤ Real.pi / 2 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    exact hview.1.2.trans (by nlinarith)
  have hcos : 0 ≤ Real.cos p.θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hview.1.1], hthetaHalf⟩
  have hsinTheta : 0 ≤ Real.sin p.θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hview.1.1
      (hthetaHalf.trans (by linarith [Real.pi_pos]))
  have hsinPhi : 0 ≤ Real.sin p.φ :=
    Real.sin_nonneg_of_mem_Icc hview.2
  constructor <;> simp [viewVector, mul_nonneg, hcos, hsinTheta, hsinPhi]

theorem viewVector_third_nonneg {p : AtlasPose ℝ}
    (hview : p.InViewWedge) (hupper : p.InUpperView) :
    0 ≤ viewVector p 2 := by
  have hlower : -(Real.pi / 2) ≤ p.φ :=
    (neg_nonpos.mpr (div_nonneg Real.pi_pos.le (by norm_num))).trans
      hview.2.1
  have hcos : 0 ≤ Real.cos p.φ :=
    Real.cos_nonneg_of_mem_Icc ⟨hlower, hupper⟩
  simpa [viewVector] using hcos

theorem viewVector_second_le_slope_first {p : AtlasPose ℝ}
    (hview : p.InViewWedge) :
    viewVector p 1 ≤ (31 / 10 : ℝ) * viewVector p 0 := by
  let angle := 2 * Real.pi / 5
  have hangle : 0 ≤ angle := by positivity
  have hangleHalf : angle < Real.pi / 2 := by
    dsimp [angle]
    nlinarith [Real.pi_pos]
  have hθ : p.θ ∈ Set.Icc 0 angle := hview.1
  have hhalfPi : Real.pi / 2 < Real.pi := by
    nlinarith [Real.pi_pos]
  have hsinθ : 0 ≤ Real.sin p.θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
      (hθ.2.trans (hangleHalf.trans hhalfPi).le)
  have hnegHalf : -(Real.pi / 2) ≤ 0 :=
    neg_nonpos.mpr (div_nonneg Real.pi_pos.le (by norm_num))
  have hcosθ : 0 ≤ Real.cos p.θ :=
    Real.cos_nonneg_of_mem_Icc ⟨hnegHalf.trans hθ.1,
      hθ.2.trans hangleHalf.le⟩
  have hdiff : 0 ≤ Real.sin (angle - p.θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact sub_nonneg.mpr hθ.2
    · nlinarith [hθ.1, hangleHalf, Real.pi_pos]
  rw [Real.sin_sub] at hdiff
  have hc := AtlasFundamentalPrune.cos_two_pi_div_five_bounds
  have hs := AtlasFundamentalPrune.sin_two_pi_div_five_bounds
  change |Real.cos angle - (309017 / 1000000 : ℝ)| ≤
    1 / 1000000 at hc
  change |Real.sin angle - (951057 / 1000000 : ℝ)| ≤
    1 / 1000000 at hs
  rw [abs_le] at hc hs
  have htrig : Real.sin p.θ ≤ (31 / 10 : ℝ) * Real.cos p.θ := by
    have hlo : (308 / 1000 : ℝ) * Real.sin p.θ ≤
        Real.cos angle * Real.sin p.θ :=
      mul_le_mul_of_nonneg_right (by linarith [hc.1]) hsinθ
    have hhi : Real.sin angle * Real.cos p.θ ≤
        (952 / 1000 : ℝ) * Real.cos p.θ :=
      mul_le_mul_of_nonneg_right (by linarith [hs.2]) hcosθ
    nlinarith
  have hsinφ : 0 ≤ Real.sin p.φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hview.2.1 hview.2.2
  simpa [viewVector, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right htrig hsinφ

/-- In the upper representative of the exact fivefold wedge, the single
signed root `+++` contains the viewing direction. -/
theorem upperView_mem_root (p : AtlasPose ℝ)
    (hview : p.InViewWedge) (hupper : p.InUpperView) :
    1 ≤ viewScale 0 p ∧
      InTriangle (toReal (rootTriangle 0)) (normalizedView 0 p) := by
  obtain ⟨hx, hy⟩ := viewVector_first_two_nonneg hview
  have hz := viewVector_third_nonneg hview hupper
  have hsign : ∀ c,
      0 ≤ (rootSign 0 c : ℝ) * viewVector p c := by
    intro c
    fin_cases c <;> simp [rootSign, hx, hy, hz]
  exact ⟨one_le_viewScale_of_sign hsign,
    normalizedView_mem_root_of_sign hsign⟩

/-- The upper fivefold view belongs to the sharper rational wedge triangle. -/
theorem upperView_mem_wedgeTriangle (p : AtlasPose ℝ)
    (hview : p.InViewWedge) (hupper : p.InUpperView) :
    1 ≤ viewScale 0 p ∧
      InTriangle (toReal upperWedgeTriangle) (normalizedView 0 p) := by
  obtain ⟨hx, hy⟩ := viewVector_first_two_nonneg hview
  have hz := viewVector_third_nonneg hview hupper
  have hslope := viewVector_second_le_slope_first hview
  have hsign : ∀ c,
      0 ≤ (rootSign 0 c : ℝ) * viewVector p c := by
    intro c
    fin_cases c <;> simp [rootSign, hx, hy, hz]
  have hscale := one_le_viewScale_of_sign hsign
  have hscale0 : 0 < viewScale 0 p := lt_of_lt_of_le (by norm_num) hscale
  let u := normalizedView 0 p
  let weight : Vector ℝ :=
    ![u 0 - (10 / 31) * u 1, (41 / 31) * u 1, u 2]
  have hu0 : 0 ≤ u 0 := div_nonneg hx hscale0.le
  have hu1 : 0 ≤ u 1 := div_nonneg hy hscale0.le
  have hu2 : 0 ≤ u 2 := div_nonneg hz hscale0.le
  have huslope : u 1 ≤ (31 / 10 : ℝ) * u 0 := by
    calc
      u 1 = viewVector p 1 / viewScale 0 p := rfl
      _ ≤ ((31 / 10 : ℝ) * viewVector p 0) / viewScale 0 p :=
        div_le_div_of_nonneg_right hslope hscale0.le
      _ = (31 / 10 : ℝ) * u 0 := by
        dsimp [u, normalizedView]
        ring
  have hscaleEq : viewScale 0 p =
      viewVector p 0 + viewVector p 1 + viewVector p 2 := by
    simp [viewScale, rootSign, Fin.sum_univ_three]
  have husum : u 0 + u 1 + u 2 = 1 := by
    calc
      _ = (viewVector p 0 + viewVector p 1 + viewVector p 2) /
          viewScale 0 p := by
        dsimp [u, normalizedView]
        ring
      _ = 1 := by rw [← hscaleEq, div_self hscale0.ne']
  refine ⟨hscale, weight, ?_, ?_, ?_⟩
  · intro c
    fin_cases c
    · dsimp [weight]
      nlinarith
    · dsimp [weight]
      positivity
    · exact hu2
  · simp only [Fin.sum_univ_three]
    dsimp [weight]
    nlinarith [husum]
  · funext c
    fin_cases c <;>
      simp [weight, u, upperWedgeTriangle, affinePoint, toReal,
        Fin.sum_univ_three] <;> ring_nf

/-- Every view in the exact fivefold-reduced wedge belongs to one of the
two projective roots `+++` and `++-`. -/
theorem exists_wedgeRoot (p : AtlasPose ℝ) (hview : p.InViewWedge) :
    ∃ root : Fin 2,
      1 ≤ viewScale (wedgeRoot root) p ∧
      InTriangle (toReal (rootTriangle (wedgeRoot root)))
        (normalizedView (wedgeRoot root) p) := by
  obtain ⟨hx, hy⟩ := viewVector_first_two_nonneg hview
  by_cases hz : 0 ≤ viewVector p 2
  · let root : Fin 2 := 0
    have hsign : ∀ c,
        0 ≤ (rootSign (wedgeRoot root) c : ℝ) * viewVector p c := by
      intro c
      fin_cases c <;> simp [root, wedgeRoot, rootSign, hx, hy, hz]
    exact ⟨root, one_le_viewScale_of_sign hsign,
      normalizedView_mem_root_of_sign hsign⟩
  · let root : Fin 2 := 1
    have hz' : viewVector p 2 ≤ 0 := le_of_not_ge hz
    have hsign : ∀ c,
        0 ≤ (rootSign (wedgeRoot root) c : ℝ) * viewVector p c := by
      intro c
      fin_cases c <;> simp [root, wedgeRoot, rootSign, hx, hy, hz']
    exact ⟨root, one_le_viewScale_of_sign hsign,
      normalizedView_mem_root_of_sign hsign⟩

/-- Every outer view belongs to one of the eight signed projective roots,
with a positive scaling factor at least one. -/
theorem exists_root (p : AtlasPose ℝ) :
    ∃ root : Fin 8, 1 ≤ viewScale root p ∧
      InTriangle (toReal (rootTriangle root)) (normalizedView root p) := by
  by_cases h0 : 0 ≤ viewVector p 0
  · by_cases h1 : 0 ≤ viewVector p 1
    · by_cases h2 : 0 ≤ viewVector p 2
      · have hs : ∀ c, 0 ≤ (rootSign 0 c : ℝ) * viewVector p c := by
          intro c
          fin_cases c <;> simp [rootSign, h0, h1, h2]
        exact ⟨0, one_le_viewScale_of_sign hs,
          normalizedView_mem_root_of_sign hs⟩
      · have h2' : viewVector p 2 ≤ 0 := le_of_not_ge h2
        refine ⟨1, one_le_viewScale_of_sign ?_,
          normalizedView_mem_root_of_sign ?_⟩ <;>
          intro c <;> fin_cases c <;> simp [rootSign, h0, h1, h2']
    · have h1' : viewVector p 1 ≤ 0 := le_of_not_ge h1
      by_cases h2 : 0 ≤ viewVector p 2
      · refine ⟨2, one_le_viewScale_of_sign ?_,
          normalizedView_mem_root_of_sign ?_⟩ <;>
          intro c <;> fin_cases c <;> simp [rootSign, h0, h1', h2]
      · have h2' : viewVector p 2 ≤ 0 := le_of_not_ge h2
        refine ⟨3, one_le_viewScale_of_sign ?_,
          normalizedView_mem_root_of_sign ?_⟩ <;>
          intro c <;> fin_cases c <;> simp [rootSign, h0, h1', h2']
  · have h0' : viewVector p 0 ≤ 0 := le_of_not_ge h0
    by_cases h1 : 0 ≤ viewVector p 1
    · by_cases h2 : 0 ≤ viewVector p 2
      · refine ⟨4, one_le_viewScale_of_sign ?_,
          normalizedView_mem_root_of_sign ?_⟩ <;>
          intro c <;> fin_cases c <;> simp [rootSign, h0', h1, h2]
      · have h2' : viewVector p 2 ≤ 0 := le_of_not_ge h2
        refine ⟨5, one_le_viewScale_of_sign ?_,
          normalizedView_mem_root_of_sign ?_⟩ <;>
          intro c <;> fin_cases c <;> simp [rootSign, h0', h1, h2']
    · have h1' : viewVector p 1 ≤ 0 := le_of_not_ge h1
      by_cases h2 : 0 ≤ viewVector p 2
      · refine ⟨6, one_le_viewScale_of_sign ?_,
          normalizedView_mem_root_of_sign ?_⟩ <;>
          intro c <;> fin_cases c <;> simp [rootSign, h0', h1', h2]
      · have h2' : viewVector p 2 ≤ 0 := le_of_not_ge h2
        refine ⟨7, one_le_viewScale_of_sign ?_,
          normalizedView_mem_root_of_sign ?_⟩ <;>
          intro c <;> fin_cases c <;> simp [rootSign, h0', h1', h2']

end Noperthedron.Nopert76.AtlasProjectiveView

end
