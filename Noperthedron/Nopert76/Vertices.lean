module

public import Noperthedron.RationalApprox.TrigLemmas
public import Noperthedron.Vertices.Taylor
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section


/-!
# Exact and rational vertices of Nopert #76

Tom 7 publishes Nopert #76 as an ASCII STL linked from
<https://tom7.org/ruperts/>.  Its source construction takes four seed vertices
and rotates them around the z axis in increments of `2π/5`.  The STL stores
rounded decimal coordinates.  We therefore use the intended fivefold-symmetric
construction as the exact real polyhedron, and the twenty printed STL vertices
as rational approximations used by the executable checker.
-/

namespace Noperthedron.Nopert76

abbrev VertexIndex := Fin 20
abbrev SeedIndex := Fin 4
abbrev OrbitIndex := Fin 5

def stlVertices : VertexIndex → Fin 3 → ℚ := ![
  ![0.675489232895168, 0.16405886422191, 0.7188873244903643],
  ![0.8673132088577333, 0.38456101538186116, 0.3160389583411731],
  ![0.8242638702149571, 0.5636759481669922, -0.0534649204273497],
  ![0.5925421933056898, 0.21777232017726278, -0.7755443028719213],
  ![0.05270840060767448, 0.6931254137545865, 0.7188873244903643],
  ![-0.09772473860909209, 0.9436997680800874, 0.3160389583411731],
  ![-0.2813761398373796, 0.9581069722186101, -0.0534649204273497],
  ![-0.024008176557637075, 0.6308364619624353, -0.7755443028719213],
  ![-0.6429136498269797, 0.26431619994475825, 0.7188873244903643],
  ![-0.9277104188598513, 0.19867751646702597, 0.3160389583411731],
  ![-0.9981638882577007, 0.028466725522360015, -0.0534649204273497],
  ![-0.6073800624262179, 0.17210605465825232, -0.7755443028719213],
  ![-0.4500508880319958, -0.5297690184115128, 0.7188873244903643],
  ![-0.4756318319636977, -0.8209103101030484, 0.3160389583411731],
  ![-0.33552306944863164, -0.9405135682973775, -0.0534649204273497],
  ![-0.3513733461107986, -0.5244690705139882, -0.7755443028719213],
  ![0.364766904356133, -0.591731459509742, 0.7188873244903643],
  ![0.6337537805749077, -0.7060279898259261, 0.3160389583411731],
  ![0.7907992273287549, -0.6097360776105849, -0.0534649204273497],
  ![0.39021939178896364, -0.4962457662839623, -0.7755443028719213]
]

def rationalVertex (i : VertexIndex) : Fin 3 → ℚ := stlVertices i

/-- Seeds scaled by (10^15-1)/10^15 so every exact vertex has norm
strictly below one (the published decimals overshoot the unit sphere
by ~2e-16); the Rupert property is invariant under this similarity. -/
def seedVertex : SeedIndex → Fin 3 → ℚ := ![
  ![0.675489232895167324510767104832, 0.16405886422190983594113577809, 0.7188873244903635811126755096357],
  ![0.8673132088577324326867911422667, 0.38456101538186077543898461813884, 0.3160389583411727839610416588269],
  ![0.8242638702149562757361297850429, 0.5636759481669916363240518330078, -0.0534649204273496465350795726503],
  ![0.5925421933056892074578066943102, 0.21777232017726256222767982273722, -0.7755443028719205244556971280787]
]

def orbitIndex (i : VertexIndex) : OrbitIndex :=
  ⟨i.val / 4, by omega⟩

def seedIndex (i : VertexIndex) : SeedIndex :=
  ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩

/-- The STL ordering is rotation-major: four seeds for each of five orbits. -/
def indexEquiv : VertexIndex ≃ OrbitIndex × SeedIndex where
  toFun i := (orbitIndex i, seedIndex i)
  invFun ks := ⟨4 * ks.1.val + ks.2.val, by omega⟩
  left_inv i := by
    apply Fin.ext
    simp [orbitIndex, seedIndex]
    omega
  right_inv ks := by
    rcases ks with ⟨k, s⟩
    apply Prod.ext <;> apply Fin.ext <;> simp [orbitIndex, seedIndex] <;> omega

def vertexIndex (k : OrbitIndex) (s : SeedIndex) : VertexIndex :=
  indexEquiv.symm (k, s)

@[simp] theorem orbitIndex_vertexIndex (k : OrbitIndex) (s : SeedIndex) :
    orbitIndex (vertexIndex k s) = k := by
  exact congrArg Prod.fst (indexEquiv.apply_symm_apply (k, s))

@[simp] theorem seedIndex_vertexIndex (k : OrbitIndex) (s : SeedIndex) :
    seedIndex (vertexIndex k s) = s := by
  exact congrArg Prod.snd (indexEquiv.apply_symm_apply (k, s))

/-- A rational trigonometric approximation to the intended exact orbit vertex.
Angles in the second half of the orbit are reduced modulo `2π`, keeping their
absolute values below `π`. -/
def taylorVertex (i : VertexIndex) : Fin 3 → ℚ :=
  let k := orbitIndex i
  let k' : ℚ := if k.val ≤ 2 then k.val else k.val - 5
  let θ : ℚ := 2 * Noperthedron.piQ * k' / 5
  let c := RationalApprox.cosℚ θ
  let s := RationalApprox.sinℚ θ
  let v := seedVertex (seedIndex i)
  ![c * v 0 - s * v 1, s * v 0 + c * v 1, v 2]

def rationalPolyhedron : Polyhedron VertexIndex (Fin 3 → ℚ) :=
  ⟨rationalVertex⟩

noncomputable def exactVertex (i : VertexIndex) : ℝ³ :=
  RzL (2 * Real.pi * (orbitIndex i : ℝ) / 5) (toR3 (seedVertex (seedIndex i)))

noncomputable def exactPolyhedron : Polyhedron VertexIndex ℝ³ :=
  ⟨exactVertex⟩

noncomputable def exactVerts : Finset ℝ³ :=
  Finset.image exactVertex Finset.univ

theorem exactPolyhedron_hull :
    exactPolyhedron.hull = convexHull ℝ exactVerts := by
  simp only [Polyhedron.hull, exactPolyhedron, exactVerts, Finset.coe_image,
    Finset.coe_univ, Set.image_univ]
  congr 1

@[simp] theorem exactPolyhedron_vertex (i : VertexIndex) :
    exactPolyhedron.v i = exactVertex i := rfl

theorem exactVertex_norm_pos (i : VertexIndex) : 0 < ‖exactVertex i‖ := by
  rw [exactVertex, Bounding.Rz_preserves_norm, norm_pos_iff]
  intro h
  have hcoord := congrFun (congrArg WithLp.ofLp h) (2 : Fin 3)
  fin_cases i <;>
    simp [seedIndex, seedVertex, toR3] at hcoord <;>
    norm_num at hcoord

theorem exactVertex_norm_le_one (i : VertexIndex) : ‖exactVertex i‖ ≤ 1 := by
  rw [exactVertex, Bounding.Rz_preserves_norm]
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three,
    Real.norm_eq_abs, sq_abs, one_pow]
  fin_cases i <;>
    simp [seedIndex, seedVertex, toR3] <;>
    norm_num

noncomputable def exactGoodPoly : GoodPoly VertexIndex where
  vertices := exactPolyhedron
  nontriv := exactVertex_norm_pos
  vertex_radius_le_one := exactVertex_norm_le_one

end Noperthedron.Nopert76

end
