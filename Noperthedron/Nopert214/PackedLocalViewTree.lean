module

public import Noperthedron.Nopert214.AtlasProjectiveLocalViewTree

@[expose] public section

/-!
# Packed native certificates for the Nopert #214 local view tree

Large generated local certificates contain very little repeated axis data.
Representing every integer in that data as a separate Lean declaration makes
elaboration and code generation dominate the actual certificate check.  This
module provides a deliberately small total decoder for comma-separated natural
numbers.  Generated native-only modules can therefore contain one string
literal; `native_decide` still checks the fully decoded exact rational table.

Signed rational numerators use zig-zag coding: `z >= 0` is encoded as `2*z`,
and `z < 0` as `-2*z-1`.
-/

namespace Noperthedron.Nopert214.PackedLocalViewTree

open AtlasProjectiveView AtlasProjectiveLocalCertificate
open AtlasProjectiveLocalViewTree
open Noperthedron.SnubCube.ProjectiveView

structure Cursor where
  data : ByteArray
  pos : Nat := 0

def readNatAux (data : ByteArray) (pos acc fuel : Nat) : Nat × Nat :=
  match fuel with
  | 0 => (acc, pos)
  | fuel + 1 =>
      if h : pos < data.size then
        let value := (data[pos]).toNat
        if 48 ≤ value ∧ value ≤ 57 then
          readNatAux data (pos + 1) (10 * acc + value - 48) fuel
        else
          (acc, pos + 1)
      else
        (acc, pos)

def Cursor.readNat (cursor : Cursor) : Nat × Cursor :=
  let result := readNatAux cursor.data cursor.pos 0
    (cursor.data.size - cursor.pos)
  (result.1, { cursor with pos := result.2 })

abbrev Decoder := StateM Cursor

def readNat : Decoder Nat := fun cursor => cursor.readNat

def fin3 (n : Nat) : Fin 3 := ⟨n % 3, by omega⟩
def fin4 (n : Nat) : Fin 4 := ⟨n % 4, by omega⟩
def fin5 (n : Nat) : Fin 5 := ⟨n % 5, by omega⟩
def fin8 (n : Nat) : Fin 8 := ⟨n % 8, by omega⟩
def fin20 (n : Nat) : Fin 20 := ⟨n % 20, by omega⟩
def fin1001 (n : Nat) : Fin 1001 := ⟨n % 1001, by omega⟩

def zigzagInt (n : Nat) : Int :=
  if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)

def readRat : Decoder Rat := do
  let numerator ← readNat
  let denominator ← readNat
  pure ((((zigzagInt numerator : Int) : Rat) / (denominator : Rat)) : Rat)

def readVertices : Decoder (Fin 3 → VertexIndex) := do
  let a ← readNat
  let b ← readNat
  let c ← readNat
  pure ![fin20 a, fin20 b, fin20 c]

def readMix : Decoder (Fin 3 → Fin 1001) := do
  let a ← readNat
  let b ← readNat
  let c ← readNat
  pure ![fin1001 a, fin1001 b, fin1001 c]

def readAxis : Decoder AxisCertificate := do
  let edgeStart ← readVertices
  let edgeFinish ← readVertices
  let edgeStart₂ ← readVertices
  let edgeFinish₂ ← readVertices
  let mix ← readMix
  let index ← readVertices
  let nonzeroWitness ← readVertices
  let B ← readRat
  pure {
    edgeStart := edgeStart
    edgeFinish := edgeFinish
    edgeStart₂ := edgeStart₂
    edgeFinish₂ := edgeFinish₂
    mix := mix
    index := index
    nonzeroWitness := nonzeroWitness
    B := B }

def readCertificate : Decoder (Fin 4 → AxisCertificate) := do
  let a ← readAxis
  let b ← readAxis
  let c ← readAxis
  let d ← readAxis
  pure ![a, b, c, d]

def readTrianglePath : Nat → AtlasProjectiveView.Triangle Rat →
    Decoder (AtlasProjectiveView.Triangle Rat)
  | 0, triangle => pure triangle
  | length + 1, triangle => do
      let child ← readNat
      readTrianglePath length (split triangle (fin4 child))

def readTriangle (base : AtlasProjectiveView.Triangle Rat) :
    Decoder (AtlasProjectiveView.Triangle Rat) := do
  let length ← readNat
  readTrianglePath length base

def readRow (base : AtlasProjectiveView.Triangle Rat) : Decoder Row := do
  let tag ← readNat
  let id ← readNat
  let root ← readNat
  let triangle ← readTriangle base
  if tag = 0 then
    let a ← readNat
    let b ← readNat
    let c ← readNat
    let d ← readNat
    pure (.split id ![a, b, c, d] (fin8 root) triangle)
  else
    let symmetryIndex ← readNat
    let certificate ← readCertificate
    let c ← readRat
    let δ ← readRat
    let r ← readRat
    pure (.certificate id {
      interval := AtlasPose.rootInterval Rat
      root := fin8 root
      triangle
      chart := 0
      symmetryIndex := fin5 symmetryIndex
      certificate
      c
      δ
      r })

def readRows (base : AtlasProjectiveView.Triangle Rat) :
    Nat → Array Row → Decoder (Array Row)
  | 0, rows => pure rows
  | count + 1, rows => do
      let row ← readRow base
      readRows base count (rows.push row)

def decodeRows (base : AtlasProjectiveView.Triangle Rat)
    (count : Nat) (packed : String) : Array Row :=
  (readRows base count #[] { data := packed.toUTF8 }).1

def decodeTable (initialChild symmetryIndex : Nat) (r : Rat)
    (count : Nat) (packed : String) : Table :=
  let base := split upperWedgeTriangle (fin4 initialChild)
  let rows := decodeRows base count packed
  {
    symmetryIndex := fin5 symmetryIndex
    r
    root := 0
    triangle := base
    get := fun i => rows[i]!
    size := count
  }

end Noperthedron.Nopert214.PackedLocalViewTree

end
