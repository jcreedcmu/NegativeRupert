module

public import Noperthedron.SnubCube.ProjectiveTransitionCertificate
public import Noperthedron.SnubCube.SparseTribonacciPolynomial

@[expose] public section


/-!
# Full blown-up projective transition chart

Around the hard symmetry-wall seam, use exact chart variables

* `d`: the signed silhouette seam equation;
* `e`: the tangential view ratio, with normalized-view `n_z = d*e`;
* `a,b`: transverse Cayley ratios, with `x=d²*a`, `y=d²*b`;
* `t`: the main Cayley ratio, with `z=d*t`.

The generated contact families below cover the numerical transition chart.
Their complete denominator-cleared support-defect obstructions are
constructed from exact indexed snub-cube data and normalized in Lean.
-/

namespace Noperthedron.SnubCube.ProjectiveTransitionBlowup

open Noperthedron.Checker
open TribonacciExpr
open ProjectiveTransitionCertificate

abbrev Polynomial := SparseTribonacciPolynomial.Polynomial 5
abbrev PolyVector := Fin 3 → Polynomial
abbrev ExactVector := Fin 3 → TribonacciExpr

structure Family where
  edgeStart : Fin 3 → Fin 24
  edgeFinish : Fin 3 → Fin 24
  /-- Inner vertices `Pi` in the balanced-support theorem. -/
  supportVertex : Fin 3 → Fin 24
  /-- Outer support vertices `Qi`; these need not equal `Pi`. -/
  outerVertex : Fin 3 → Fin 24
  supportCompetitor : Fin 3 → Fin 24
  factorPower : ℕ
deriving DecidableEq, Repr

def family2 : Family where
  edgeStart := ![8, 15, 10]
  edgeFinish := ![9, 11, 14]
  supportVertex := ![1, 11, 10]
  outerVertex := ![1, 11, 10]
  supportCompetitor := ![1, 3, 2]
  factorPower := 1

def family89 : Family where
  edgeStart := ![5, 10, 8]
  edgeFinish := ![15, 14, 9]
  supportVertex := ![15, 10, 1]
  outerVertex := ![15, 10, 1]
  supportCompetitor := ![15, 2, 1]
  factorPower := 1

def family192 : Family where
  edgeStart := ![14, 8, 5]
  edgeFinish := ![4, 9, 15]
  supportVertex := ![14, 1, 15]
  outerVertex := ![14, 1, 15]
  supportCompetitor := ![14, 1, 15]
  factorPower := 2

/-- A genuinely translated-support family with `Pi ≠ Qi`.  On the seam its
three determinant weights limit to two antiparallel positive contacts; off
the seam the third weight opens linearly.  This family fills the thin
transverse gap missed by every `Pi = Qi` family in the 208-family bank. -/
def familyTransverse : Family where
  edgeStart := ![1, 5, 2]
  edgeFinish := ![9, 15, 14]
  supportVertex := ![9, 15, 14]
  outerVertex := ![1, 5, 2]
  supportCompetitor := ![1, 5, 2]
  factorPower := 2

/-- A translated-support Farkas certificate for the nested transition where
the tangential view ratio is itself comparable to the seam scale.  Direct
containment duality selects three outer silhouette edges and different inner
support vertices, so all three contacts have `Pi ≠ Qi`. -/
def familyNested : Family where
  edgeStart := ![14, 8, 15]
  edgeFinish := ![4, 1, 3]
  supportVertex := ![14, 8, 15]
  outerVertex := ![4, 1, 3]
  supportCompetitor := ![4, 1, 3]
  factorPower := 2

/-- A two-contact width certificate for the finite-seam `e = 0` boundary.
The first two edges are exact opposites, hence their determinant weights are
equal and the third weight is identically zero.  The two positive weighted
contacts compare the width of the rotated inner shadow with the outer one. -/
def familyWidth : Family where
  edgeStart := ![1, 0, 4]
  edgeFinish := ![0, 1, 2]
  supportVertex := ![11, 0, 5]
  outerVertex := ![2, 0, 5]
  supportCompetitor := ![2, 0, 5]
  factorPower := 1

def Family.edge (family : Family) (i : Fin 3) : ExactVector :=
  exactEdge (family.edgeStart i) (family.edgeFinish i)

def Family.support (family : Family) (i : Fin 3) : ExactVector :=
  exactSelectedVertex (family.supportVertex i)

def Family.outerSupport (family : Family) (i : Fin 3) : ExactVector :=
  exactSelectedVertex (family.outerVertex i)

def Family.competitor (family : Family) (i : Fin 3) : ExactVector :=
  exactSelectedVertex (family.supportCompetitor i)

def dotPolyExact (left : PolyVector) (right : ExactVector) : Polynomial :=
  left 0 * SparseTribonacciPolynomial.const (right 0) +
    left 1 * SparseTribonacciPolynomial.const (right 1) +
    left 2 * SparseTribonacciPolynomial.const (right 2)

def dotPoly (left right : PolyVector) : Polynomial :=
  left 0 * right 0 + left 1 * right 1 + left 2 * right 2

def crossExactPoly (left : ExactVector) (right : PolyVector) : PolyVector := ![
  SparseTribonacciPolynomial.const (left 1) * right 2 -
    SparseTribonacciPolynomial.const (left 2) * right 1,
  SparseTribonacciPolynomial.const (left 2) * right 0 -
    SparseTribonacciPolynomial.const (left 0) * right 2,
  SparseTribonacciPolynomial.const (left 0) * right 1 -
    SparseTribonacciPolynomial.const (left 1) * right 0]

def seamEdge : ExactVector := exactEdge 15 11

def seamDelta : ExactVector := fun c =>
  (exactSelectedVertex 3 c) - (exactSelectedVertex 15 c)

def seamCoefficient : ExactVector := symbolicCross seamEdge seamDelta

def seamTangentialSlope : TribonacciExpr :=
  inverseSeamSlope * (seamCoefficient 0 - seamCoefficient 2)

def viewPolynomial : PolyVector :=
  let d : Polynomial := SparseTribonacciPolynomial.var 0
  let e : Polynomial := SparseTribonacciPolynomial.var 1
  let h := d * e
  let u := SparseTribonacciPolynomial.const seamU +
    SparseTribonacciPolynomial.const inverseSeamSlope * d +
    SparseTribonacciPolynomial.const seamTangentialSlope * h
  ![1 - u - h, u, h]

def cayleyPolynomial : PolyVector :=
  let d : Polynomial := SparseTribonacciPolynomial.var 0
  let eA : Polynomial := SparseTribonacciPolynomial.var 2
  let eB : Polynomial := SparseTribonacciPolynomial.var 3
  let t : Polynomial := SparseTribonacciPolynomial.var 4
  ![d * d * eA, d * d * eB, d * t]

def cayleyDenominator : Polynomial :=
  let r := cayleyPolynomial
  1 + r 0 * r 0 + r 1 * r 1 + r 2 * r 2

/-- `N(x,y,z)q - (1+x²+y²+z²)q`, where `N` is the Cayley
rotation numerator. -/
def selfDisplacementPolynomial (q : ExactVector) : PolyVector :=
  let r := cayleyPolynomial
  let x := r 0
  let y := r 1
  let z := r 2
  ![
    SparseTribonacciPolynomial.const (ofRat (-2) * q 0) * (y*y + z*z) +
      SparseTribonacciPolynomial.const (ofRat 2 * q 1) * (x*y - z) +
      SparseTribonacciPolynomial.const (ofRat 2 * q 2) * (x*z + y),
    SparseTribonacciPolynomial.const (ofRat 2 * q 0) * (x*y + z) +
      SparseTribonacciPolynomial.const (ofRat (-2) * q 1) * (x*x + z*z) +
      SparseTribonacciPolynomial.const (ofRat 2 * q 2) * (y*z - x),
    SparseTribonacciPolynomial.const (ofRat 2 * q 0) * (x*z - y) +
      SparseTribonacciPolynomial.const (ofRat 2 * q 1) * (y*z + x) +
    SparseTribonacciPolynomial.const (ofRat (-2) * q 2) * (x*x + y*y)]

/-- `N(r)Pi - (1+|r|²)Qi`; unlike the original local families, the
transition theorem must allow the inner and outer support vertices to differ. -/
def Family.displacementPolynomial (family : Family) (i : Fin 3) : PolyVector :=
  let base := selfDisplacementPolynomial (family.support i)
  let shift : ExactVector := fun c => family.support i c - family.outerSupport i c
  fun c => base c + cayleyDenominator *
    SparseTribonacciPolynomial.const (shift c)

def Family.weightPolynomial (family : Family) : Fin 3 → Polynomial := ![
  dotPolyExact viewPolynomial (symbolicCross (family.edge 1) (family.edge 2)),
  dotPolyExact viewPolynomial (symbolicCross (family.edge 2) (family.edge 0)),
  dotPolyExact viewPolynomial (symbolicCross (family.edge 0) (family.edge 1))]

def Family.contactPolynomial (family : Family) (i : Fin 3) : Polynomial :=
  dotPoly viewPolynomial
    (crossExactPoly (family.edge i)
      (family.displacementPolynomial i))

def Family.supportPolynomial (family : Family)
    (i : Fin 3) (vertex : Fin 24) : Polynomial :=
  let delta : ExactVector := fun c =>
    exactSelectedVertex vertex c - family.outerSupport i c
  dotPolyExact viewPolynomial (symbolicCross (family.edge i) delta)

def Family.defectPolynomial (family : Family) (i : Fin 3) : Polynomial :=
  family.supportPolynomial i (family.supportCompetitor i)

def Family.supportSlackPolynomial (family : Family)
    (i : Fin 3) (vertex : Fin 24) : Polynomial :=
  family.defectPolynomial i - family.supportPolynomial i vertex

def Family.SupportHasSeamFactor (family : Family)
    (i : Fin 3) (vertex : Fin 24) : Prop :=
  SparseTribonacciPolynomial.HasFactor 0 1
    (family.supportSlackPolynomial i vertex)

instance (family : Family) (i : Fin 3) (vertex : Fin 24) :
    Decidable (family.SupportHasSeamFactor i vertex) := by
  unfold Family.SupportHasSeamFactor
  infer_instance

/-- Remove one seam factor from support slacks that vanish identically on
the seam.  Slacks with a nonzero seam value retain factor power zero. -/
def Family.supportFactorPower (family : Family)
    (i : Fin 3) (vertex : Fin 24) : ℕ :=
  if family.SupportHasSeamFactor i vertex then 1 else 0

def Family.supportAfterSeam (family : Family)
    (i : Fin 3) (vertex : Fin 24) : Polynomial :=
  SparseTribonacciPolynomial.factorOut 0
    (family.supportFactorPower i vertex)
    (family.supportSlackPolynomial i vertex)

theorem Family.supportFactorValid (family : Family)
    (i : Fin 3) (vertex : Fin 24) :
    SparseTribonacciPolynomial.HasFactor 0
      (family.supportFactorPower i vertex)
      (family.supportSlackPolynomial i vertex) := by
  unfold Family.supportFactorPower
  split
  · assumption
  · intro term _
    exact Nat.zero_le _

def Family.SupportHasTangentialFactor (family : Family)
    (i : Fin 3) (vertex : Fin 24) : Prop :=
  SparseTribonacciPolynomial.HasFactor 1 1
    (family.supportAfterSeam i vertex)

instance (family : Family) (i : Fin 3) (vertex : Fin 24) :
    Decidable (family.SupportHasTangentialFactor i vertex) := by
  unfold Family.SupportHasTangentialFactor
  infer_instance

def Family.supportTangentialFactorPower (family : Family)
    (i : Fin 3) (vertex : Fin 24) : ℕ :=
  if family.SupportHasTangentialFactor i vertex then 1 else 0

def Family.supportQuotient (family : Family)
    (i : Fin 3) (vertex : Fin 24) : Polynomial :=
  SparseTribonacciPolynomial.factorOut 1
    (family.supportTangentialFactorPower i vertex)
    (family.supportAfterSeam i vertex)

theorem Family.supportTangentialFactorValid (family : Family)
    (i : Fin 3) (vertex : Fin 24) :
    SparseTribonacciPolynomial.HasFactor 1
      (family.supportTangentialFactorPower i vertex)
      (family.supportAfterSeam i vertex) := by
  unfold Family.supportTangentialFactorPower
  split
  · assumption
  · intro term _
    exact Nat.zero_le _

theorem Family.eval_supportSlack_factor (family : Family)
    (i : Fin 3) (vertex : Fin 24) (values : Fin 5 → ℝ) :
    SparseTribonacciPolynomial.evalReal values
        (family.supportSlackPolynomial i vertex) =
      values 0 ^ family.supportFactorPower i vertex *
        (values 1 ^ family.supportTangentialFactorPower i vertex *
          SparseTribonacciPolynomial.evalReal values
            (family.supportQuotient i vertex)) := by
  have hseam := SparseTribonacciPolynomial.evalReal_factorOut values 0
    (family.supportFactorPower i vertex)
    (family.supportSlackPolynomial i vertex)
    (family.supportFactorValid i vertex)
  have htangential := SparseTribonacciPolynomial.evalReal_factorOut values 1
    (family.supportTangentialFactorPower i vertex)
    (family.supportAfterSeam i vertex)
    (family.supportTangentialFactorValid i vertex)
  exact hseam.trans (congrArg
    (fun x => values 0 ^ family.supportFactorPower i vertex * x)
    htangential)

/-- Exact denominator-cleared weighted displacement minus the selected
support-defect bound. -/
def Family.obstruction (family : Family) : Polynomial :=
  let term (i : Fin 3) := family.weightPolynomial i *
    (family.contactPolynomial i -
      cayleyDenominator * family.defectPolynomial i)
  term 0 + term 1 + term 2

def Family.FactorValid (family : Family) : Prop :=
  SparseTribonacciPolynomial.HasFactor 0 family.factorPower family.obstruction

instance (family : Family) : Decidable family.FactorValid := by
  unfold Family.FactorValid
  infer_instance

def Family.quotient (family : Family) : Polynomial :=
  SparseTribonacciPolynomial.factorOut 0 family.factorPower family.obstruction

/-- Semantic factorization once the executable exact normalizer has checked
the structural seam order. -/
theorem Family.eval_obstruction_factor (family : Family)
    (h : family.FactorValid) (values : Fin 5 → ℝ) :
    SparseTribonacciPolynomial.evalReal values family.obstruction =
      values 0 ^ family.factorPower *
        SparseTribonacciPolynomial.evalReal values family.quotient := by
  exact SparseTribonacciPolynomial.evalReal_factorOut values 0
    family.factorPower family.obstruction h

end Noperthedron.SnubCube.ProjectiveTransitionBlowup

end
