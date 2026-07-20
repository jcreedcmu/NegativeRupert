module

public import Noperthedron.Nopert214.AtlasInterval
public import Noperthedron.SnubCube.CayleyEdgeCertificate

@[expose] public section

/-!
# Exact quadratic arithmetic for the Cayley atlas

Each atlas chart is diagonal, so left multiplication by its chart matrix
only changes the signs of rows of the usual Cayley numerator.  This file
packages that observation in the normalized quadratic representation used by
the executable interval checker.
-/

namespace Noperthedron.Nopert214.AtlasQuadratic

open Noperthedron.Checker
open Noperthedron.BalancedSupport
open Noperthedron.Nopert214.CayleyAtlas
open Noperthedron.SnubCube.CayleyEdgeCertificate

def chartSign (chart : ChartIndex) (c : Fin 3) : ℚ :=
  if chart.val = 0 ∨ chart.val = c.val + 1 then 1 else -1

theorem chartMatrix_apply (chart : ChartIndex) (i j : Fin 3) :
    chartMatrix chart i j =
      if i ≠ j then 0 else (chartSign chart i : ℝ) := by
  by_cases hij : i = j
  · subst j
    simp only [chartMatrix, chartSign, ne_eq, not_true_eq_false, ↓reduceIte]
    split_ifs <;> norm_num
  · simp [chartMatrix, hij]

theorem chartMatrix_eq_diagonal (chart : ChartIndex) :
    chartMatrix chart = Matrix.diagonal fun i => (chartSign chart i : ℝ) := by
  ext i j
  rw [chartMatrix_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- Numerator matrix of `chartMatrix chart * cayleyMatrix x y z`. -/
def numeratorQuadratic (chart : ChartIndex) :
    Matrix (Fin 3) (Fin 3) RatQuadratic3 :=
  fun i j => RatQuadratic3.scale (chartSign chart i)
    (Noperthedron.SnubCube.CayleyEdgeCertificate.numeratorQuadratic i j)

theorem eval_numeratorQuadratic (chart : ChartIndex) (i j : Fin 3)
    (x y z : ℝ) :
    (numeratorQuadratic chart i j).evalReal x y z =
      (chartMatrix chart * cayleyNumeratorMatrix x y z) i j := by
  rw [numeratorQuadratic, RatQuadratic3.evalReal_scale,
    Noperthedron.SnubCube.CayleyEdgeCertificate.eval_numeratorQuadratic]
  rw [chartMatrix_eq_diagonal, Matrix.diagonal_mul]

def sum3Q (f : Fin 3 → RatQuadratic3) : RatQuadratic3 :=
  f 0 + f 1 + f 2

/-- Denominator-cleared displacement of one selected inner vertex from one
selected outer support vertex. -/
def displacementQuadratic (chart : ChartIndex)
    (inner outer : VertexIndex) (c : Fin 3) : RatQuadratic3 :=
  (sum3Q fun j => RatQuadratic3.scale (rationalVertex inner j)
      (numeratorQuadratic chart c j)) -
    RatQuadratic3.scale (rationalVertex outer c) denomQuadratic

theorem eval_displacementQuadratic (chart : ChartIndex)
    (inner outer : VertexIndex) (c : Fin 3) (x y z : ℝ) :
    (displacementQuadratic chart inner outer c).evalReal x y z =
      ∑ j, (rationalVertex inner j : ℝ) *
          (chartMatrix chart * cayleyNumeratorMatrix x y z) c j -
        (rationalVertex outer c : ℝ) * cayleyDenom x y z := by
  simp only [displacementQuadratic, sum3Q,
    RatQuadratic3.evalReal_sub, RatQuadratic3.evalReal_add,
    RatQuadratic3.evalReal_scale, eval_numeratorQuadratic,
    Noperthedron.SnubCube.CayleyEdgeCertificate.eval_denomQuadratic,
    Fin.sum_univ_three]

def edgeQ (start finish : VertexIndex) : Fin 3 → ℚ :=
  rationalVertex start - rationalVertex finish

def contactQuadratic (chart : ChartIndex) (start finish inner : VertexIndex) :
    Fin 3 → RatQuadratic3 :=
  let edge := edgeQ start finish
  let d := displacementQuadratic chart inner start
  ![RatQuadratic3.scale (edge 1) (d 2) -
      RatQuadratic3.scale (edge 2) (d 1),
    RatQuadratic3.scale (edge 2) (d 0) -
      RatQuadratic3.scale (edge 0) (d 2),
    RatQuadratic3.scale (edge 0) (d 1) -
      RatQuadratic3.scale (edge 1) (d 0)]

noncomputable def approxDisplacementVector (chart : ChartIndex)
    (inner outer : VertexIndex) (x y z : ℝ) : ℝ³ :=
  (chartMatrix chart * cayleyNumeratorMatrix x y z).toEuclideanLin
      (toR3 (rationalVertex inner)) -
    cayleyDenom x y z • toR3 (rationalVertex outer)

theorem eval_displacementQuadratic_eq_apply (chart : ChartIndex)
    (inner outer : VertexIndex) (c : Fin 3) (x y z : ℝ) :
    (displacementQuadratic chart inner outer c).evalReal x y z =
      approxDisplacementVector chart inner outer x y z c := by
  rw [eval_displacementQuadratic]
  simp [approxDisplacementVector, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, toR3]
  ring

theorem eval_contactQuadratic (chart : ChartIndex)
    (start finish inner : VertexIndex) (c : Fin 3) (x y z : ℝ) :
    (contactQuadratic chart start finish inner c).evalReal x y z =
      cross3 (toR3 (edgeQ start finish))
        (approxDisplacementVector chart inner start x y z) c := by
  fin_cases c <;>
    simp [contactQuadratic, RatQuadratic3.evalReal_sub,
      RatQuadratic3.evalReal_scale,
      eval_displacementQuadratic_eq_apply, cross3, cross_apply, edgeQ, toR3]

end Noperthedron.Nopert214.AtlasQuadratic

end
