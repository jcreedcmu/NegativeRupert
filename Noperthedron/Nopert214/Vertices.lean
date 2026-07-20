module

public import Noperthedron.RationalApprox.TrigLemmas
public import Noperthedron.Vertices.Taylor
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section


/-!
# Exact and rational vertices of Nopert #214

Tom 7 publishes Nopert #214 as an ASCII STL linked from
<https://tom7.org/ruperts/>.  Its source construction takes four seed vertices
and rotates them around the z axis in increments of `2π/5`.  The STL stores
rounded decimal coordinates.  We therefore use the intended fivefold-symmetric
construction as the exact real polyhedron, and the twenty printed STL vertices
as rational approximations used by the executable checker.
-/

namespace Noperthedron.Nopert214

abbrev VertexIndex := Fin 20
abbrev SeedIndex := Fin 4
abbrev OrbitIndex := Fin 5

def stlVertices : VertexIndex → Fin 3 → ℚ := ![
  ![0.5542570167628148, 0.13498214234883502, 0.5670539264866502],
  ![0.839503072954794, 0.4526456900329921, 0.3005768949769993],
  ![0.7619849874129984, 0.5429603653859462, -0.04074876955046458],
  ![0.591853727475924, 0.13110932665305655, -0.7653829489805983],
  ![0.04289919136693016, 0.5688415234175154, 0.5670539264866502],
  ![-0.17107091670577093, 0.9382900786342319, 0.3005768949769993],
  ![-0.2809196830211049, 0.8924747677745009, -0.04074876955046458],
  ![0.05820048051375984, 0.6034013542664042, -0.7653829489805983],
  ![-0.5277438584081657, 0.2165812533354586, 0.5670539264866502],
  ![-0.9452307139655625, 0.1272494698697746, 0.3005768949769993],
  ![-0.9356028996288878, 0.008619375200364626, -0.04074876955046458],
  ![-0.5558838523568445, 0.2418132191412975, -0.7653829489805983],
  ![-0.36906283321718863, -0.4349869475301504, 0.5670539264866502],
  ![-0.41311379173527674, -0.8596455812043055, 0.3005768949769993],
  ![-0.2973147089225043, -0.8871477009388876, -0.04074876955046458],
  ![-0.40175559506751807, -0.45395256590805566, -0.7653829489805983],
  ![0.29965048349560947, -0.4854179715716587, 0.5670539264866502],
  ![0.6899123494518161, -0.6585396573326932, 0.3005768949769993],
  ![0.7518523041594987, -0.5569068074219243, -0.04074876955046458],
  ![0.3075852394346786, -0.5223713341527026, -0.7653829489805983]
]

def rationalVertex (i : VertexIndex) : Fin 3 → ℚ := stlVertices i

def seedVertex : SeedIndex → Fin 3 → ℚ := ![
  ![0.5542570167628148, 0.13498214234883502, 0.5670539264866502],
  ![0.839503072954794, 0.4526456900329921, 0.3005768949769993],
  ![0.7619849874129984, 0.5429603653859462, -0.04074876955046458],
  ![0.591853727475924, 0.13110932665305655, -0.7653829489805983]
]

def orbitIndex (i : VertexIndex) : OrbitIndex :=
  ⟨i.val / 4, by omega⟩

def seedIndex (i : VertexIndex) : SeedIndex :=
  ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩

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

end Noperthedron.Nopert214

end
