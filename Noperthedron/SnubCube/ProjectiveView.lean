module

public import Noperthedron.SnubCube.CayleyEdgeCertificate

@[expose] public section


/-!
# Rational projective viewing triangles

After outer snub-cube symmetry reduction, the viewing vector has nonnegative
coordinates and its first coordinate is maximal.  Dividing by the positive
coordinate sum places it in a rational quadrilateral in the affine simplex.
That quadrilateral is the union of two triangles.  Repeated midpoint
subdivision gives an exact, adaptive replacement for trigonometric angle
boxes.
-/

namespace Noperthedron.SnubCube.ProjectiveView

open Noperthedron.SnubCube
open CayleyEdgeCertificate

abbrev Vector (R : Type) := Fin 3 → R
abbrev Triangle (R : Type) := Fin 3 → Vector R

def affinePoint (triangle : Triangle ℝ) (weight : Vector ℝ) : Vector ℝ :=
  fun c => ∑ i, weight i * triangle i c

def InTriangle (triangle : Triangle ℝ) (point : Vector ℝ) : Prop :=
  ∃ weight : Vector ℝ, (∀ i, 0 ≤ weight i) ∧
    (∑ i, weight i) = 1 ∧ point = affinePoint triangle weight

def linearValue (point coefficient : Vector ℝ) : ℝ :=
  point 0 * coefficient 0 + point 1 * coefficient 1 +
    point 2 * coefficient 2

theorem linearValue_le_of_mem {triangle : Triangle ℝ} {point : Vector ℝ}
    {coefficient : Vector ℝ} {bound : ℝ}
    (hmem : InTriangle triangle point)
    (hbound : ∀ i, linearValue (triangle i) coefficient ≤ bound) :
    linearValue point coefficient ≤ bound := by
  obtain ⟨weight, hnonneg, hsum, hpoint⟩ := hmem
  have hsum3 : weight 0 + weight 1 + weight 2 = 1 := by
    simpa [Fin.sum_univ_three] using hsum
  have h0 := mul_le_mul_of_nonneg_left (hbound 0) (hnonneg 0)
  have h1 := mul_le_mul_of_nonneg_left (hbound 1) (hnonneg 1)
  have h2 := mul_le_mul_of_nonneg_left (hbound 2) (hnonneg 2)
  have hboundsum : weight 0 * bound + weight 1 * bound +
      weight 2 * bound = bound := by
    calc
      _ = (weight 0 + weight 1 + weight 2) * bound := by ring
      _ = bound := by rw [hsum3]; ring
  rw [hpoint]
  have heq : linearValue (affinePoint triangle weight) coefficient =
      weight 0 * linearValue (triangle 0) coefficient +
        weight 1 * linearValue (triangle 1) coefficient +
        weight 2 * linearValue (triangle 2) coefficient := by
    simp [linearValue, affinePoint, Fin.sum_univ_three]
    ring
  rw [heq]
  linarith

theorem le_linearValue_of_mem {triangle : Triangle ℝ} {point : Vector ℝ}
    {coefficient : Vector ℝ} {bound : ℝ}
    (hmem : InTriangle triangle point)
    (hbound : ∀ i, bound ≤ linearValue (triangle i) coefficient) :
    bound ≤ linearValue point coefficient := by
  obtain ⟨weight, hnonneg, hsum, hpoint⟩ := hmem
  have hsum3 : weight 0 + weight 1 + weight 2 = 1 := by
    simpa [Fin.sum_univ_three] using hsum
  have h0 := mul_le_mul_of_nonneg_left (hbound 0) (hnonneg 0)
  have h1 := mul_le_mul_of_nonneg_left (hbound 1) (hnonneg 1)
  have h2 := mul_le_mul_of_nonneg_left (hbound 2) (hnonneg 2)
  have hboundsum : weight 0 * bound + weight 1 * bound +
      weight 2 * bound = bound := by
    calc
      _ = (weight 0 + weight 1 + weight 2) * bound := by ring
      _ = bound := by rw [hsum3]; ring
  rw [hpoint]
  have heq : linearValue (affinePoint triangle weight) coefficient =
      weight 0 * linearValue (triangle 0) coefficient +
        weight 1 * linearValue (triangle 1) coefficient +
        weight 2 * linearValue (triangle 2) coefficient := by
    simp [linearValue, affinePoint, Fin.sum_univ_three]
    ring
  rw [heq]
  linarith

def midpoint (a b : Vector ℚ) : Vector ℚ := fun c => (a c + b c) / 2

/-- The three corner triangles followed by the central triangle. -/
def split (triangle : Triangle ℚ) : Fin 4 → Triangle ℚ := ![
  ![triangle 0, midpoint (triangle 0) (triangle 1),
    midpoint (triangle 0) (triangle 2)],
  ![midpoint (triangle 0) (triangle 1), triangle 1,
    midpoint (triangle 1) (triangle 2)],
  ![midpoint (triangle 0) (triangle 2),
    midpoint (triangle 1) (triangle 2), triangle 2],
  ![midpoint (triangle 0) (triangle 1),
    midpoint (triangle 1) (triangle 2),
    midpoint (triangle 2) (triangle 0)]]

def toReal (triangle : Triangle ℚ) : Triangle ℝ :=
  fun i c => triangle i c

@[simp] theorem toReal_midpoint (a b : Vector ℚ) (c : Fin 3) :
    (midpoint a b c : ℝ) = ((a c : ℝ) + (b c : ℝ)) / 2 := by
  norm_num [midpoint]

private theorem corner_zero {triangle : Triangle ℚ} {point : Vector ℝ}
    {weight : Vector ℝ} (hnonneg : ∀ i, 0 ≤ weight i)
    (hsum : (∑ i, weight i) = 1)
    (hpoint : point = affinePoint (toReal triangle) weight)
    (hlarge : 1 / 2 ≤ weight 0) :
    InTriangle (toReal (split triangle 0)) point := by
  have hsum3 : weight 0 + weight 1 + weight 2 = 1 := by
    simpa [Fin.sum_univ_three] using hsum
  let mu : Vector ℝ := ![2 * weight 0 - 1, 2 * weight 1, 2 * weight 2]
  refine ⟨mu, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [mu] <;> linarith [hnonneg 0, hnonneg 1, hnonneg 2]
  · simp [mu, Fin.sum_univ_three]
    linarith
  · rw [hpoint]
    funext c
    simp [affinePoint, split, midpoint, toReal, mu, Fin.sum_univ_three]
    have hm := congrArg (fun x : ℝ => x * (triangle 0 c : ℝ)) hsum3
    nlinarith

private theorem corner_one {triangle : Triangle ℚ} {point : Vector ℝ}
    {weight : Vector ℝ} (hnonneg : ∀ i, 0 ≤ weight i)
    (hsum : (∑ i, weight i) = 1)
    (hpoint : point = affinePoint (toReal triangle) weight)
    (hlarge : 1 / 2 ≤ weight 1) :
    InTriangle (toReal (split triangle 1)) point := by
  have hsum3 : weight 0 + weight 1 + weight 2 = 1 := by
    simpa [Fin.sum_univ_three] using hsum
  let mu : Vector ℝ := ![2 * weight 0, 2 * weight 1 - 1, 2 * weight 2]
  refine ⟨mu, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [mu] <;> linarith [hnonneg 0, hnonneg 1, hnonneg 2]
  · simp [mu, Fin.sum_univ_three]
    linarith
  · rw [hpoint]
    funext c
    simp [affinePoint, split, midpoint, toReal, mu, Fin.sum_univ_three]
    have hm := congrArg (fun x : ℝ => x * (triangle 1 c : ℝ)) hsum3
    nlinarith

private theorem corner_two {triangle : Triangle ℚ} {point : Vector ℝ}
    {weight : Vector ℝ} (hnonneg : ∀ i, 0 ≤ weight i)
    (hsum : (∑ i, weight i) = 1)
    (hpoint : point = affinePoint (toReal triangle) weight)
    (hlarge : 1 / 2 ≤ weight 2) :
    InTriangle (toReal (split triangle 2)) point := by
  have hsum3 : weight 0 + weight 1 + weight 2 = 1 := by
    simpa [Fin.sum_univ_three] using hsum
  let mu : Vector ℝ := ![2 * weight 0, 2 * weight 1, 2 * weight 2 - 1]
  refine ⟨mu, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [mu] <;> linarith [hnonneg 0, hnonneg 1, hnonneg 2]
  · simp [mu, Fin.sum_univ_three]
    linarith
  · rw [hpoint]
    funext c
    simp [affinePoint, split, midpoint, toReal, mu, Fin.sum_univ_three]
    have hm := congrArg (fun x : ℝ => x * (triangle 2 c : ℝ)) hsum3
    nlinarith

private theorem central {triangle : Triangle ℚ} {point : Vector ℝ}
    {weight : Vector ℝ} (hnonneg : ∀ i, 0 ≤ weight i)
    (hsum : (∑ i, weight i) = 1)
    (hsmall0 : weight 0 ≤ 1 / 2) (hsmall1 : weight 1 ≤ 1 / 2)
    (hsmall2 : weight 2 ≤ 1 / 2)
    (hpoint : point = affinePoint (toReal triangle) weight) :
    InTriangle (toReal (split triangle 3)) point := by
  have hsum3 : weight 0 + weight 1 + weight 2 = 1 := by
    simpa [Fin.sum_univ_three] using hsum
  let mu : Vector ℝ :=
    ![1 - 2 * weight 2, 1 - 2 * weight 0, 1 - 2 * weight 1]
  refine ⟨mu, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [mu] <;> linarith
  · simp [mu, Fin.sum_univ_three]
    linarith
  · rw [hpoint]
    funext c
    simp [affinePoint, split, midpoint, toReal, mu, Fin.sum_univ_three]
    have hm := congrArg (fun x : ℝ => x * ((triangle 0 c : ℝ) +
      triangle 1 c + triangle 2 c)) hsum3
    nlinarith

/-- The four midpoint children cover their parent, including all shared
boundaries. -/
theorem mem_split {triangle : Triangle ℚ} {point : Vector ℝ}
    (h : InTriangle (toReal triangle) point) :
    ∃ child : Fin 4, InTriangle (toReal (split triangle child)) point := by
  obtain ⟨weight, hnonneg, hsum, hpoint⟩ := h
  by_cases h0 : 1 / 2 ≤ weight 0
  · exact ⟨0, corner_zero hnonneg hsum hpoint h0⟩
  · by_cases h1 : 1 / 2 ≤ weight 1
    · exact ⟨1, corner_one hnonneg hsum hpoint h1⟩
    · by_cases h2 : 1 / 2 ≤ weight 2
      · exact ⟨2, corner_two hnonneg hsum hpoint h2⟩
      · exact ⟨3, central hnonneg hsum (le_of_not_ge h0)
          (le_of_not_ge h1) (le_of_not_ge h2) hpoint⟩

def e0 : Vector ℚ := ![1, 0, 0]
def e1 : Vector ℚ := ![0, 1, 0]
def e2 : Vector ℚ := ![0, 0, 1]
def chamberCenter : Vector ℚ := ![1 / 3, 1 / 3, 1 / 3]

/-- The two rational triangles covering the first-coordinate-maximal part of
the positive projective simplex. -/
def chamberRoot : Fin 2 → Triangle ℚ := ![
  ![e0, midpoint e0 e1, chamberCenter],
  ![e0, chamberCenter, midpoint e0 e2]]

def InSimplex (point : Vector ℝ) : Prop :=
  (∀ i, 0 ≤ point i) ∧ (∑ i, point i) = 1

def InChamber (point : Vector ℝ) : Prop :=
  InSimplex point ∧ point 1 ≤ point 0 ∧ point 2 ≤ point 0

/-- The rational two-triangle root exactly covers the normalized outer-view
chamber. -/
theorem mem_chamberRoot {point : Vector ℝ} (h : InChamber point) :
    ∃ root : Fin 2, InTriangle (toReal (chamberRoot root)) point := by
  obtain ⟨⟨hnonneg, hsum⟩, h10, h20⟩ := h
  have hsum3 : point 0 + point 1 + point 2 = 1 := by
    simpa [Fin.sum_univ_three] using hsum
  by_cases h21 : point 2 ≤ point 1
  · let weight : Vector ℝ :=
      ![1 - 2 * point 1 - point 2, 2 * (point 1 - point 2), 3 * point 2]
    refine ⟨0, weight, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [weight] <;>
        linarith [hnonneg 0, hnonneg 1, hnonneg 2, hsum3]
    · simp [weight, Fin.sum_univ_three]
      linarith
    · funext c
      fin_cases c <;>
        simp [affinePoint, chamberRoot, e0, e1, midpoint, chamberCenter,
          toReal, weight, Fin.sum_univ_three] <;> linarith
  · let weight : Vector ℝ :=
      ![1 - point 1 - 2 * point 2, 3 * point 1, 2 * (point 2 - point 1)]
    refine ⟨1, weight, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [weight] <;>
        linarith [hnonneg 0, hnonneg 1, hnonneg 2, hsum3]
    · simp [weight, Fin.sum_univ_three]
      linarith
    · funext c
      fin_cases c <;>
        simp [affinePoint, chamberRoot, e0, e2, midpoint, chamberCenter,
          toReal, weight, Fin.sum_univ_three] <;> linarith

noncomputable def viewSum (p : CayleyPose ℝ) : ℝ :=
  viewVector p 0 + viewVector p 1 + viewVector p 2

noncomputable def normalizedView (p : CayleyPose ℝ) : Vector ℝ :=
  fun c => viewVector p c / viewSum p

theorem viewVector_eq_outer_row (p : CayleyPose ℝ) (offset : ℝ²)
    (c : Fin 3) :
    viewVector p c = (p.matrixPoseWithOffset offset).outerRot.val 2 c := by
  fin_cases c <;>
    simp [viewVector, CayleyPose.matrixPoseWithOffset_outerRot_val,
      rotRM_mat, Matrix.mul_apply, Fin.sum_univ_three, Rz_mat, Ry_mat,
      Real.sin_neg, Real.cos_neg, Real.sin_pi_div_two,
      Real.cos_pi_div_two] <;> ring

theorem viewSum_pos {p : CayleyPose ℝ} {offset : ℝ²}
    (h : (p.matrixPoseWithOffset offset).InOuterViewChamber) :
    0 < viewSum p := by
  unfold MatrixPose.InOuterViewChamber at h
  have hview : ViewInChamber (viewVector p) := by
    change ViewInChamber (fun c => viewVector p c)
    simpa only [viewVector_eq_outer_row p offset] using h
  have hnorm := CayleyEdgeCertificate.viewVector_norm p
  unfold viewSum
  by_contra hnot
  have hs : viewVector p 0 + viewVector p 1 + viewVector p 2 ≤ 0 :=
    le_of_not_gt hnot
  have h0 : viewVector p 0 = 0 := by
    linarith [hview.1, hview.2.1, hview.2.2.1]
  have h1 : viewVector p 1 = 0 := by
    linarith [hview.1, hview.2.1, hview.2.2.1]
  have h2 : viewVector p 2 = 0 := by
    linarith [hview.1, hview.2.1, hview.2.2.1]
  have hz : viewVector p = 0 := by
    rw [WithLp.ext_iff]
    funext c
    fin_cases c <;> simp [h0, h1, h2]
  rw [hz, norm_zero] at hnorm
  norm_num at hnorm

theorem one_le_viewSum {p : CayleyPose ℝ} {offset : ℝ²}
    (h : (p.matrixPoseWithOffset offset).InOuterViewChamber) :
    1 ≤ viewSum p := by
  unfold MatrixPose.InOuterViewChamber at h
  have hview : ViewInChamber (viewVector p) := by
    change ViewInChamber (fun c => viewVector p c)
    simpa only [viewVector_eq_outer_row p offset] using h
  have hnorm := CayleyEdgeCertificate.viewVector_norm p
  have hnormsq := congrArg (fun x : ℝ => x ^ 2) hnorm
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs,
    Fin.sum_univ_three] at hnormsq
  have hsumpos := viewSum_pos h
  unfold viewSum at hsumpos ⊢
  nlinarith [mul_nonneg hview.1 hview.2.1,
    mul_nonneg hview.1 hview.2.2.1,
    mul_nonneg hview.2.1 hview.2.2.1]

theorem normalizedView_inChamber {p : CayleyPose ℝ} {offset : ℝ²}
    (h : (p.matrixPoseWithOffset offset).InOuterViewChamber) :
    InChamber (normalizedView p) := by
  unfold MatrixPose.InOuterViewChamber at h
  have hview : ViewInChamber (viewVector p) := by
    change ViewInChamber (fun c => viewVector p c)
    simpa only [viewVector_eq_outer_row p offset] using h
  have hsum := viewSum_pos h
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro c
    exact div_nonneg (by
      fin_cases c
      · exact hview.1
      · exact hview.2.1
      · exact hview.2.2.1) hsum.le
  · simp [normalizedView, viewSum, Fin.sum_univ_three]
    rw [← add_div, ← add_div]
    exact div_self hsum.ne'
  · exact (div_le_div_iff_of_pos_right hsum).mpr hview.2.2.2.1
  · exact (div_le_div_iff_of_pos_right hsum).mpr hview.2.2.2.2

theorem normalizedView_mem_root {p : CayleyPose ℝ} {offset : ℝ²}
    (h : (p.matrixPoseWithOffset offset).InOuterViewChamber) :
    ∃ root : Fin 2,
      InTriangle (toReal (chamberRoot root)) (normalizedView p) :=
  mem_chamberRoot (normalizedView_inChamber h)

end Noperthedron.SnubCube.ProjectiveView

end
