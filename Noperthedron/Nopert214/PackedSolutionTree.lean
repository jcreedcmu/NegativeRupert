module

public import Noperthedron.Nopert214.AtlasProjectiveSolutionTree
public import Noperthedron.Nopert214.PackedLocalViewTree

@[expose] public section

/-!
# Packed runtime data for Nopert #214 global solution trees

The final native executable reads compact ignored artifacts instead of asking
Lean to elaborate hundreds of thousands of generated row declarations. The
decoder is deliberately total; the semantic parallel checker remains the
trusted validation step for every decoded value.
-/

namespace Noperthedron.Nopert214.PackedSolutionTree

open AtlasProjectiveSolutionTree AtlasProjectiveView
open AtlasProjectiveEdgeCertificate AtlasProjectiveGlobalCertificate
open AtlasProjectiveLocalCertificate
open PackedLocalViewTree
open Noperthedron.SnubCube.ProjectiveView

abbrev Decoder := PackedLocalViewTree.Decoder

def relativeInterval (center radius : Fin 3 → ℚ) :
    AtlasProjectiveSolutionTree.Interval :=
  AtlasInterval.mk
    { θ := 0, φ := 0,
      x := center 0 - |radius 0|,
      y := center 1 - |radius 1|,
      z := center 2 - |radius 2| }
    { θ := 8 / 5, φ := 4,
      x := center 0 + |radius 0|,
      y := center 1 + |radius 1|,
      z := center 2 + |radius 2| }
    (by
      rw [AtlasPose.le_iff]
      exact ⟨by norm_num, by norm_num,
        by linarith [abs_nonneg (radius 0)],
        by linarith [abs_nonneg (radius 1)],
        by linarith [abs_nonneg (radius 2)]⟩)

def readInterval : Decoder AtlasProjectiveSolutionTree.Interval := do
  let cx ← readRat
  let cy ← readRat
  let cz ← readRat
  let wx ← readRat
  let wy ← readRat
  let wz ← readRat
  pure (relativeInterval ![cx, cy, cz] ![wx, wy, wz])

def readTriangle : Decoder AtlasProjectiveSolutionTree.Triangle := do
  let a0 ← readRat
  let a1 ← readRat
  let a2 ← readRat
  let b0 ← readRat
  let b1 ← readRat
  let b2 ← readRat
  let c0 ← readRat
  let c1 ← readRat
  let c2 ← readRat
  pure ![![a0, a1, a2], ![b0, b1, b2], ![c0, c1, c2]]

def readMany {α : Type} (readOne : Decoder α) :
    Nat → Array α → Decoder (Array α)
  | 0, values => pure values
  | count + 1, values => do
      let value ← readOne
      readMany readOne count (values.push value)

def readNats : Nat → Array Nat → Decoder (Array Nat)
  | 0, values => pure values
  | count + 1, values => do
      let value ← readNat
      readNats count (values.push value)

def intervalAt (intervals : Array AtlasProjectiveSolutionTree.Interval)
    (index : Nat) : AtlasProjectiveSolutionTree.Interval :=
  (intervals[index]?).getD (AtlasPose.rootInterval ℚ)

def triangleAt (triangles : Array AtlasProjectiveSolutionTree.Triangle)
    (index : Nat) : AtlasProjectiveSolutionTree.Triangle :=
  (triangles[index]?).getD (rootTriangle 0)

def vertexAt (values : Array Nat) (index : Nat) : VertexIndex :=
  fin20 ((values[index]?).getD 0)

def readRegion (triangles : Array AtlasProjectiveSolutionTree.Triangle) :
    Decoder Region := do
  let root ← readNat
  let triangleIndex ← readNat
  pure (.triangle (fin8 root) (triangleAt triangles triangleIndex))

def readEdgeRow (chart : CayleyAtlas.ChartIndex)
    (triangles : Array AtlasProjectiveSolutionTree.Triangle)
    (id : Nat) (interval : AtlasProjectiveSolutionTree.Interval) :
    Decoder Row := do
  let root ← readNat
  let triangleIndex ← readNat
  let edgePred ← readNat
  let count := edgePred + 1
  let outer ← readNats count #[]
  let inner ← readNats count #[]
  let witnesses ← readNats count #[]
  let m0 ← readRat
  let m1 ← readRat
  let m2 ← readRat
  pure (.projective id {
    interval
    root := fin8 root
    triangle := triangleAt triangles triangleIndex
    chart
    edgePred
    outerIndex := fun i => vertexAt outer i
    innerIndex := fun i => vertexAt inner i
    nonzeroWitness := fun i => vertexAt witnesses i
    ballMultiplier := ![m0, m1, m2] })

def readGlobalRow (chart : CayleyAtlas.ChartIndex)
    (triangles : Array AtlasProjectiveSolutionTree.Triangle)
    (id : Nat) (interval : AtlasProjectiveSolutionTree.Interval) :
    Decoder Row := do
  let root ← readNat
  let triangleIndex ← readNat
  let certificate ← readAxis
  let innerIndex ← readVertices
  let ballMultiplier ← readRat
  pure (.projectiveGlobal id {
    interval
    root := fin8 root
    triangle := triangleAt triangles triangleIndex
    chart
    certificate
    innerIndex
    ballMultiplier })

def readMixedComponent :
    Decoder AtlasProjectiveMixedGlobalCertificate.Component := do
  let certificate ← readAxis
  let innerIndex ← readVertices
  let ballMultiplier ← readRat
  pure { certificate, innerIndex, ballMultiplier }

def readMixedGlobalRow (chart : CayleyAtlas.ChartIndex)
    (triangles : Array AtlasProjectiveSolutionTree.Triangle)
    (id : Nat) (interval : AtlasProjectiveSolutionTree.Interval) :
    Decoder Row := do
  let root ← readNat
  let triangleIndex ← readNat
  let w0 ← readRat
  let w1 ← readRat
  let w2 ← readRat
  let w3 ← readRat
  let c0 ← readMixedComponent
  let c1 ← readMixedComponent
  let c2 ← readMixedComponent
  let c3 ← readMixedComponent
  pure (.projectiveMixedGlobal id {
    interval
    root := fin8 root
    triangle := triangleAt triangles triangleIndex
    chart
    component := ![c0, c1, c2, c3]
    weight := ![w0, w1, w2, w3] })

def readLocalRow (chart : CayleyAtlas.ChartIndex)
    (triangles : Array AtlasProjectiveSolutionTree.Triangle)
    (id : Nat) (interval : AtlasProjectiveSolutionTree.Interval) :
    Decoder Row := do
  let root ← readNat
  let triangleIndex ← readNat
  let symmetryIndex ← readNat
  let certificate ← readCertificate
  let c ← readRat
  let δ ← readRat
  let r ← readRat
  pure (.projectiveLocal id {
    interval
    root := fin8 root
    triangle := triangleAt triangles triangleIndex
    chart
    symmetryIndex := fin5 symmetryIndex
    certificate
    c
    δ
    r })

def readRow (chart : CayleyAtlas.ChartIndex)
    (intervals : Array AtlasProjectiveSolutionTree.Interval)
    (triangles : Array AtlasProjectiveSolutionTree.Triangle) : Decoder Row := do
  let tag ← readNat
  let id ← readNat
  let intervalIndex ← readNat
  let interval := intervalAt intervals intervalIndex
  if tag = 0 then
    let child ← readNat
    pure (.viewRoot id child interval)
  else if tag = 1 then
    let lowerChild ← readNat
    let upperChild ← readNat
    let coordinate ← readNat
    let region ← readRegion triangles
    pure (.cayleySplit id lowerChild upperChild (fin5 coordinate)
      interval region)
  else if tag = 2 then
    let a ← readNat
    let b ← readNat
    let c ← readNat
    let d ← readNat
    let root ← readNat
    let triangleIndex ← readNat
    pure (.viewSplit id ![a, b, c, d] interval (fin8 root)
      (triangleAt triangles triangleIndex))
  else if tag = 3 then
    readEdgeRow chart triangles id interval
  else if tag = 4 then
    readGlobalRow chart triangles id interval
  else if tag = 5 then
    readLocalRow chart triangles id interval
  else if tag = 6 then
    let symmetryIndex ← readNat
    let r ← readRat
    let sharedIndex ← readNat
    let region ← readRegion triangles
    pure (.symmetryTube id {
      interval
      chart
      symmetryIndex := fin5 symmetryIndex
      r } (fin4 sharedIndex) region)
  else if tag = 7 then
    let region ← readRegion triangles
    pure (.radiusPrune id interval region)
  else if tag = 8 then
    let direction ← readNat
    let region ← readRegion triangles
    pure (.fundamentalPrune id {
      interval
      chart
      direction := if direction = 1 then .positive else .negative }
      region)
  else
    readMixedGlobalRow chart triangles id interval

def readRows (chart : CayleyAtlas.ChartIndex)
    (intervals : Array AtlasProjectiveSolutionTree.Interval)
    (triangles : Array AtlasProjectiveSolutionTree.Triangle) :
    Nat → Array Row → Decoder (Array Row)
  | 0, rows => pure rows
  | count + 1, rows => do
      let row ← readRow chart intervals triangles
      readRows chart intervals triangles count (rows.push row)

structure Decoded where
  count : Nat
  rows : Array Row

def readDecoded (chart : CayleyAtlas.ChartIndex) : Decoder Decoded := do
  let count ← readNat
  let intervalCount ← readNat
  let intervals ← readMany readInterval intervalCount #[]
  let triangleCount ← readNat
  let triangles ← readMany readTriangle triangleCount #[]
  let rows ← readRows chart intervals triangles count #[]
  pure { count, rows }

/-- Decode a compact global chart artifact and attach the already checked
shared-local tables. -/
def decodeTable (chart : CayleyAtlas.ChartIndex)
    (shared : SharedLocalTables) (packed : String) : Table :=
  let decoded :=
    (readDecoded chart { data := packed.toUTF8 }).1
  {
    chart
    get := fun i => decoded.rows[i]!
    size := decoded.count
    sharedLocal := shared
  }

end Noperthedron.Nopert214.PackedSolutionTree

end
