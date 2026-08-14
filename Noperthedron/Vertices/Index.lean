module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype

namespace Noperthedron

-- POC (module-system migration): this leaf provides `VertexIndex`, whose
-- constructor/projections and `ofFin90` are reduced by `decide +kernel` in
-- downstream files (e.g. `Vertices/PythonNat.lean`). Those reductions cross a
-- module boundary, so the bodies must be exposed, not merely public.
@[expose] public section

/--
Identifier for a Noperthedron vertex.
Corresponds to the point at `(-1)^ℓ • Rz(2π k / 15) (C i)`
-/
structure VertexIndex : Type where
  k : Fin 15
  ℓ : Fin 2
  i : Fin 3
deriving Fintype, DecidableEq, Repr, Nonempty

def VertexIndex.ofFin90 (j : Fin 90) : VertexIndex :=
 ⟨⟨j.val % 15, by omega⟩, ⟨j.val / 45, by omega⟩, ⟨(j.val % 45) / 15, by omega⟩⟩

instance instOfNatVertexIndexZero : OfNat VertexIndex 0 where
  ofNat := ⟨0, 0, 0⟩

/-! The `Nat` fast paths address vertices by the flat index
`45ℓ + 15i + k < 90`; these two lemmas let their soundness proofs move
between a `VertexIndex` and its flat index. -/

/-- Every vertex index is `ofFin90` of its flat index (below 90). -/
lemma VertexIndex.ofFin90_flat : ∀ k : VertexIndex,
    VertexIndex.ofFin90 ⟨(45 * k.ℓ.val + 15 * k.i.val + k.k.val) % 90,
      Nat.mod_lt _ (by decide)⟩ = k := by
  decide

/-- Flat indices are injective. -/
lemma VertexIndex.flat_inj : ∀ k q : VertexIndex,
    45 * k.ℓ.val + 15 * k.i.val + k.k.val = 45 * q.ℓ.val + 15 * q.i.val + q.k.val
    → k = q := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨c', hc'⟩⟩ hf
  simp only at hf
  have : a = a' ∧ b = b' ∧ c = c' := by omega
  obtain ⟨rfl, rfl, rfl⟩ := this
  rfl

end

end Noperthedron
