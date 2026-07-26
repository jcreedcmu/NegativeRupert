module

public import Noperthedron.Nopert76.AtlasProjectiveLocalCertificate

@[expose] public section

/-!
# Sparse support checks for Nopert #214

For a linear functional to be maximized at a vertex of a polytope, it is
enough to compare that vertex with the generators of its tangent cone.  The
rational checker model of Nopert #214 has at most seven such generators at
each vertex.  This reduces the repeated local-certificate support check from
twenty vertices to seven (with padding entries equal to the selected vertex).
-/

namespace Noperthedron.Nopert76.SparseSupport

open Noperthedron.Checker
open AtlasProjectiveView
open AtlasProjectiveLocalCertificate

/-- Tangent-cone generators for each rational checker vertex.  Entries beyond
the actual degree are padded by the vertex itself. -/
def supportGenerator : VertexIndex → Fin 7 → VertexIndex := ![
  ![1, 4, 16, 17, 18, 18, 18],
  ![0, 2, 4, 18, 18, 18, 18],
  ![1, 3, 4, 5, 6, 7, 18],
  ![2, 7, 18, 19, 19, 19, 19],
  ![0, 1, 2, 5, 8, 8, 8],
  ![2, 4, 6, 8, 8, 8, 8],
  ![2, 5, 7, 8, 9, 10, 11],
  ![2, 3, 6, 11, 11, 11, 11],
  ![4, 5, 6, 9, 12, 12, 12],
  ![6, 8, 10, 12, 12, 12, 12],
  ![6, 9, 11, 12, 13, 14, 15],
  ![6, 7, 10, 15, 15, 15, 15],
  ![8, 9, 10, 13, 16, 16, 16],
  ![10, 12, 14, 16, 16, 16, 16],
  ![10, 13, 15, 16, 17, 18, 19],
  ![10, 11, 14, 19, 19, 19, 19],
  ![0, 12, 13, 14, 17, 17, 17],
  ![0, 14, 16, 18, 18, 18, 18],
  ![0, 1, 2, 3, 14, 17, 19],
  ![3, 14, 15, 18, 18, 18, 18]
]

structure TangentCombination where
  generator : Fin 3 → Fin 7
  coefficient : Fin 3 → ℚ
deriving DecidableEq

def TangentCombination.Valid (combination : TangentCombination)
    (base target : VertexIndex) : Prop :=
  (∀ l, 0 ≤ combination.coefficient l) ∧
  1 ≤ ∑ l, combination.coefficient l ∧
  (∀ l, combination.coefficient l ≠ 0 →
    supportGenerator base (combination.generator l) ≠ base) ∧
  rationalVertex target - rationalVertex base =
    ∑ l, combination.coefficient l •
      (rationalVertex (supportGenerator base (combination.generator l)) -
        rationalVertex base)

instance (combination : TangentCombination) (base target : VertexIndex) :
    Decidable (combination.Valid base target) := by
  unfold TangentCombination.Valid
  infer_instance

def TangentTableValid
    (combination : VertexIndex → VertexIndex → TangentCombination) : Prop :=
  ∀ base target, target ≠ base → (combination base target).Valid base target

instance (combination : VertexIndex → VertexIndex → TangentCombination) :
    Decidable (TangentTableValid combination) := by
  unfold TangentTableValid
  infer_instance

theorem crossQ_sum3 (u : Fin 3 → ℚ) (coefficient : Fin 3 → ℚ)
    (v : Fin 3 → Fin 3 → ℚ) :
    LocalCertificate.crossQ u (∑ l, coefficient l • v l) =
      ∑ l, coefficient l • LocalCertificate.crossQ u (v l) := by
  funext coordinate
  fin_cases coordinate <;>
    simp [LocalCertificate.crossQ, Fin.sum_univ_three] <;>
    ring

theorem dotQ_sum3 (u : Fin 3 → ℚ) (coefficient : Fin 3 → ℚ)
    (v : Fin 3 → Fin 3 → ℚ) :
    AtlasProjectiveEdgeCertificate.dotQ u (∑ l, coefficient l • v l) =
      ∑ l, coefficient l * AtlasProjectiveEdgeCertificate.dotQ u (v l) := by
  simp [AtlasProjectiveEdgeCertificate.dotQ, Fin.sum_univ_three]
  ring

theorem supportAt_eq_sum
    (combination : TangentCombination) (box : Box)
    (j : Fin 4) (corner : Fin 3) (i : Fin 3) (target : VertexIndex)
    (hcombination : combination.Valid
      ((box.certificate j).supportIndex box i) target) :
    box.supportAt j corner i target =
      ∑ l, combination.coefficient l *
        box.supportAt j corner i
          (supportGenerator ((box.certificate j).supportIndex box i)
            (combination.generator l)) := by
  have hdelta := hcombination.2.2.2
  unfold Box.supportAt AxisCertificate.deltaQ
  rw [hdelta]
  rw [crossQ_sum3, dotQ_sum3]

@[mk_iff]
structure Box.SparseViewValid (box : Box) : Prop where
  triangle_valid :
    AtlasProjectiveEdgeCertificate.SignedTriangleValid box.root box.triangle
  c_nonneg : 0 ≤ box.c
  delta_nonneg : 0 ≤ box.δ
  r_nonneg : 0 ≤ box.r
  B_pos : ∀ j, 0 < (box.certificate j).B
  weight_nonneg : ∀ j i, 0 ≤ box.weightLower j i
  weight_pos : ∀ j, ∃ i, 0 < box.weightLower j i
  support_generators : ∀ j i generator,
    box.supportUpper j i
      (supportGenerator ((box.certificate j).supportIndex box i) generator) ≤ 0
  /-- Exact cone-boundary directions can tie a second edge endpoint.  The
  tangent-generator reduction spends strict approximation slack and therefore
  cannot propagate through that zero-slack generator; for just these rare
  axes, check all twenty support vertices directly. -/
  support_boundary : ∀ j i,
    ((box.certificate j).mix i = 0 ∨
      (box.certificate j).mix i = 1000) →
    ∀ target, box.supportUpper j i target ≤ 0
  direction_nonzero : ∀ j i,
    box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0
  budget : ∀ j, box.weightBudget j ≤ (box.certificate j).B
  variation : ∀ j,
    box.variationRadiusSum j + 3 * variationError ≤
      (box.certificate j).B * box.δ
  barycentric : box.barycentricValid
  angle_bound : box.r ^ 2 * (1 + box.c ^ 2) ≤ 4 * box.c ^ 2

instance (box : Box) : Decidable (Box.SparseViewValid box) :=
  decidable_of_iff _ (Box.sparseViewValid_iff box).symm

theorem Box.SparseViewValid.support_all {box : Box}
    (h : Box.SparseViewValid box)
    (combination : VertexIndex → VertexIndex → TangentCombination)
    (htangent : TangentTableValid combination) :
    ∀ j i target, box.supportUpper j i target ≤ 0 := by
  intro j i target
  by_cases hboundary : (box.certificate j).mix i = 0 ∨
      (box.certificate j).mix i = 1000
  · exact h.support_boundary j i hboundary target
  · have hzero : (box.certificate j).mix i ≠ 0 :=
      fun hz => hboundary (Or.inl hz)
    have hthousand : (box.certificate j).mix i ≠ 1000 :=
      fun ht => hboundary (Or.inr ht)
    let base := (box.certificate j).supportIndex box i
    by_cases htie : target = base
    · simp [Box.supportUpper, Box.exactSupportTie, base, htie]
    · let selected := combination base target
      have htie' : target ≠ (box.certificate j).supportIndex box i := by
        simpa [base] using htie
      have hselected : selected.Valid base target := htangent base target htie
      have hat (corner : Fin 3) :
          box.supportAt j corner i target ≤ -supportError := by
        rw [supportAt_eq_sum selected box j corner i target hselected]
        calc
          ∑ l, selected.coefficient l *
                box.supportAt j corner i
                  (supportGenerator base (selected.generator l)) ≤
              ∑ l, selected.coefficient l * (-supportError) := by
            apply Finset.sum_le_sum
            intro l _
            by_cases hcoefficient : selected.coefficient l = 0
            · simp [hcoefficient]
            · have hgenerator :
                  supportGenerator base (selected.generator l) ≠ base :=
                hselected.2.2.1 l hcoefficient
              have hsparse := h.support_generators j i (selected.generator l)
              have hgenerator' :
                  supportGenerator
                      ((box.certificate j).supportIndex box i)
                      (selected.generator l) ≠
                    (box.certificate j).supportIndex box i := by
                simpa [base] using hgenerator
              have hcorner := AtlasProjectiveEdgeCertificate.le_max3
                (fun c => box.supportAt j c i
                  (supportGenerator base (selected.generator l))) corner
              have hraw : box.supportAt j corner i
                    (supportGenerator base (selected.generator l)) ≤
                  -supportError := by
                simp [Box.supportUpper, Box.exactSupportTie, hgenerator',
                  hzero, hthousand] at hsparse
                linarith
              exact mul_le_mul_of_nonneg_left hraw (hselected.1 l)
          _ = -supportError * ∑ l, selected.coefficient l := by
            simp only [Fin.sum_univ_three]
            ring
          _ ≤ -supportError := by
            have herror : 0 < supportError := by
              norm_num [supportError, tightVertexErrorQ]
            nlinarith [hselected.2.1]
      simp [Box.supportUpper, Box.exactSupportTie, htie', hzero,
        hthousand]
      have hmax :
          AtlasProjectiveEdgeCertificate.max3
              (fun corner => box.supportAt j corner i target) ≤
            -supportError := by
        simp only [AtlasProjectiveEdgeCertificate.max3, max_le_iff]
        exact ⟨hat 0, hat 1, hat 2⟩
      linarith

theorem Box.SparseViewValid.toViewValid {box : Box}
    (h : Box.SparseViewValid box)
    (combination : VertexIndex → VertexIndex → TangentCombination)
    (htangent : TangentTableValid combination) : box.ViewValid where
  triangle_valid := h.triangle_valid
  c_nonneg := h.c_nonneg
  delta_nonneg := h.delta_nonneg
  r_nonneg := h.r_nonneg
  B_pos := h.B_pos
  weight_nonneg := h.weight_nonneg
  weight_pos := h.weight_pos
  support := h.support_all combination htangent
  direction_nonzero := h.direction_nonzero
  budget := h.budget
  variation := h.variation
  barycentric := h.barycentric
  angle_bound := h.angle_bound

end Noperthedron.Nopert76.SparseSupport

end
