module

public import Noperthedron.SnubCube.Index
public import Noperthedron.SnubCube.Tribonacci

@[expose] public section


/-!
# Exact snub-cube vertices

We use the uniformly scaled coordinate seed `(t, 1, t^2)`, where `t` is the
tribonacci constant.  This is similar to the conventional seed
`(1, 1/t, t)` and avoids division in all exact coordinates.
-/

namespace Noperthedron.SnubCube

/-- The six permutations, in lexicographic order. -/
def permute3 {R : Type} (p : Fin 6) (v : Fin 3 → R) : Fin 3 → R :=
  ![![v 0, v 1, v 2], ![v 0, v 2, v 1], ![v 1, v 0, v 2],
    ![v 1, v 2, v 0], ![v 2, v 0, v 1], ![v 2, v 1, v 0]] p

/-- Whether the lexicographically indexed permutation is odd. -/
def permutationOdd : Fin 6 → Bool := ![false, true, true, false, false, true]

/-- Sign patterns with an even number of positive signs. -/
def evenSignPattern : Fin 4 → Fin 3 → ℤ :=
  ![![-1, -1, -1], ![1, 1, -1], ![1, -1, 1], ![-1, 1, 1]]

/-- Sign patterns with an odd number of positive signs. -/
def oddSignPattern : Fin 4 → Fin 3 → ℤ :=
  ![![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1], ![1, 1, 1]]

def signPattern (p : Fin 6) : Fin 4 → Fin 3 → ℤ :=
  if permutationOdd p then oddSignPattern else evenSignPattern

/-- A 24-vertex snub-cube family over an arbitrary real parameter. -/
noncomputable def vertexAt (t : ℝ) (i : VertexIndex) : ℝ³ :=
  let base : Fin 3 → ℝ := ![t, 1, t ^ 2]
  WithLp.toLp 2 fun c => (signPattern i.permutation i.signs c : ℝ) *
    permute3 i.permutation base c

/-- Exact vertices for the standard tribonacci parameter. -/
noncomputable def exactVertex (i : VertexIndex) : ℝ³ := vertexAt tribonacci i

noncomputable def exactPolyhedron : Polyhedron VertexIndex ℝ³ := ⟨exactVertex⟩

noncomputable def exactVerts : Finset ℝ³ := Finset.image exactVertex Finset.univ

theorem exactVerts_nonempty : exactVerts.Nonempty := by
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

theorem exactPolyhedron_hull : exactPolyhedron.hull = convexHull ℝ exactVerts := by
  simp only [Polyhedron.hull, exactPolyhedron, exactVerts, Finset.coe_image,
    Finset.coe_univ, Set.image_univ]
  congr 1

end Noperthedron.SnubCube

end
