module

public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype

@[expose] public section


namespace Noperthedron.SnubCube

/-- Six coordinate permutations and four compatible sign patterns give the
24 vertices of one chirality of the snub cube. -/
structure VertexIndex : Type where
  permutation : Fin 6
  signs : Fin 4
deriving Fintype, DecidableEq, Repr, Nonempty

def VertexIndex.ofFin24 (i : Fin 24) : VertexIndex :=
  ⟨⟨i.val / 4, by omega⟩, ⟨i.val % 4, by omega⟩⟩

instance : OfNat VertexIndex 0 where
  ofNat := ⟨0, 0⟩

end Noperthedron.SnubCube

end
