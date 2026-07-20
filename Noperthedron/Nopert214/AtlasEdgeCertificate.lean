module

public import Noperthedron.Nopert214.AtlasQuadratic
public import Noperthedron.BalancedSupport.Cycle
public import Noperthedron.Checker.RatTrigBall

@[expose] public section

/-!
# Executable edge-cycle rows for the Nopert #214 Cayley atlas

The clockwise normals of a cyclic outer-vertex list balance identically.
Each row combines its selected inner contacts as exact rational quadratics
before interval evaluation, preserving cancellations between contacts.
-/

namespace Noperthedron.Nopert214.AtlasEdgeCertificate

open Noperthedron.Checker
open Noperthedron.BalancedSupport
open Noperthedron.Nopert214.CayleyAtlas
open AtlasQuadratic
open RationalApprox

structure Box where
  interval : AtlasInterval ℚ
  chart : ChartIndex
  edgePred : ℕ
  outerIndex : Fin (edgePred + 1) → VertexIndex
  innerIndex : Fin (edgePred + 1) → VertexIndex
  nonzeroWitness : Fin (edgePred + 1) → VertexIndex

def Box.next (box : Box) : Fin (box.edgePred + 1) ≃ Fin (box.edgePred + 1) :=
  cycleNext box.edgePred

def Box.edgeQ (box : Box) (i : Fin (box.edgePred + 1)) : Fin 3 → ℚ :=
  AtlasQuadratic.edgeQ (box.outerIndex i) (box.outerIndex (box.next i))

def Box.deltaQ (box : Box) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) : Fin 3 → ℚ :=
  rationalVertex k - rationalVertex (box.outerIndex i)

def crossQ (a b : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![a 1*b 2-a 2*b 1, a 2*b 0-a 0*b 2, a 0*b 1-a 1*b 0]

def dotConstBalls (a : Fin 3 → ℚ) (b : Fin 3 → RatBall) : RatBall :=
  RatBall.add (RatBall.add (RatBall.scale (a 0) (b 0))
    (RatBall.scale (a 1) (b 1))) (RatBall.scale (a 2) (b 2))

def Box.angleBall (box : Box) (i : Fin 2) : RatBall :=
  box.interval.coordinateBall ⟨i, by omega⟩

def Box.viewBalls (box : Box) : Fin 3 → RatBall :=
  let st := (box.angleBall 0).sin
  let ct := (box.angleBall 0).cos
  let sp := (box.angleBall 1).sin
  let cp := (box.angleBall 1).cos
  ![RatBall.mul ct sp, RatBall.mul st sp, cp]

def Box.supportBall (box : Box) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) : RatBall :=
  dotConstBalls (crossQ (box.edgeQ i) (box.deltaQ i k)) box.viewBalls

def supportError : ℚ := 10 * κℚ

def Box.supportUpper (box : Box) (i : Fin (box.edgePred + 1))
    (k : VertexIndex) : ℚ :=
  (box.supportBall i k).center + (box.supportBall i k).radius + supportError

def Box.defect (box : Box) (i : Fin (box.edgePred + 1)) : ℚ :=
  (Finset.image (box.supportUpper i) Finset.univ).max' (by
    simp only [Finset.image_nonempty]
    exact Finset.univ_nonempty)

def Box.totalDefect (box : Box) : ℚ := ∑ i, box.defect i

def Box.contactQuadratic (box : Box)
    (i : Fin (box.edgePred + 1)) : Fin 3 → RatQuadratic3 :=
  AtlasQuadratic.contactQuadratic box.chart
    (box.outerIndex i) (box.outerIndex (box.next i)) (box.innerIndex i)

/-- Sum coefficient fields first, preserving cross-edge cancellation. -/
def Box.totalQuadratic (box : Box) (c : Fin 3) : RatQuadratic3 :=
  let f := fun i => box.contactQuadratic i c
  { c0 := ∑ i, (f i).c0
    cx := ∑ i, (f i).cx
    cy := ∑ i, (f i).cy
    cz := ∑ i, (f i).cz
    cxx := ∑ i, (f i).cxx
    cxy := ∑ i, (f i).cxy
    cxz := ∑ i, (f i).cxz
    cyy := ∑ i, (f i).cyy
    cyz := ∑ i, (f i).cyz
    czz := ∑ i, (f i).czz }

def Box.variableBalls (box : Box) : Fin 3 → RatBall :=
  ![box.interval.coordinateBall 2,
    box.interval.coordinateBall 3,
    box.interval.coordinateBall 4]

def Box.displacementComponents (box : Box) : Fin 3 → RatBall :=
  fun c => RatQuadratic3.evalBall box.variableBalls (box.totalQuadratic c)

def Box.displacementBall (box : Box) : RatBall :=
  let v := box.viewBalls
  let d := box.displacementComponents
  RatBall.add (RatBall.add (RatBall.mul (v 0) (d 0))
    (RatBall.mul (v 1) (d 1))) (RatBall.mul (v 2) (d 2))

def endpointAbsBound (lo hi : ℚ) : ℚ := max |lo| |hi|

def Box.dBound (box : Box) : ℚ :=
  1 + endpointAbsBound box.interval.min.x box.interval.max.x ^ 2 +
    endpointAbsBound box.interval.min.y box.interval.max.y ^ 2 +
    endpointAbsBound box.interval.min.z box.interval.max.z ^ 2

def Box.displacementError (box : Box) : ℚ :=
  (box.edgePred + 1) * 10 * box.dBound * κℚ

def Box.center (box : Box) : AtlasPose ℚ where
  θ := (box.interval.coordinateBall 0).center
  φ := (box.interval.coordinateBall 1).center
  x := (box.interval.coordinateBall 2).center
  y := (box.interval.coordinateBall 3).center
  z := (box.interval.coordinateBall 4).center

def Box.centerInFour (box : Box) : Prop :=
  box.center.θ ∈ Set.Icc (-4) 4 ∧ box.center.φ ∈ Set.Icc (-4) 4

instance (box : Box) : Decidable box.centerInFour := by
  unfold Box.centerInFour
  infer_instance

@[mk_iff]
structure Box.Valid (box : Box) : Prop where
  center_in_four : box.centerInFour
  direction_nonzero : ∀ i,
    box.supportUpper i (box.nonzeroWitness i) < 0
  displacement :
    box.dBound * box.totalDefect + box.displacementError ≤
      box.displacementBall.center - box.displacementBall.radius

instance (box : Box) : Decidable box.Valid :=
  decidable_of_iff _ (Box.valid_iff box).symm

end Noperthedron.Nopert214.AtlasEdgeCertificate

end
