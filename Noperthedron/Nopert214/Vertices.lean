module

public import Noperthedron.RationalApprox.Basic

@[expose] public section


/-!
# Exact rational vertices of Nopert #214

Tom 7 publishes Nopert #214 as an ASCII STL linked from
<https://tom7.org/ruperts/>.  The mesh has twenty distinct vertices.  This
file interprets each printed decimal coordinate as an exact rational number,
ordered in four nearly fivefold-symmetric orbits.  Thus the formal object is
completely specified without relying on floating-point semantics or on the
triangulation of its boundary.
-/

namespace Noperthedron.Nopert214

abbrev VertexIndex := Fin 20

def rationalVertices : VertexIndex → Fin 3 → ℚ := ![
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

def rationalVertex (i : VertexIndex) : Fin 3 → ℚ := rationalVertices i

def rationalPolyhedron : Polyhedron VertexIndex (Fin 3 → ℚ) :=
  ⟨rationalVertex⟩

noncomputable def exactVertex (i : VertexIndex) : ℝ³ :=
  toR3 (rationalVertex i)

noncomputable def exactPolyhedron : Polyhedron VertexIndex ℝ³ :=
  rationalPolyhedron.toReal

@[simp] theorem exactPolyhedron_vertex (i : VertexIndex) :
    exactPolyhedron.v i = exactVertex i := rfl

theorem exactVertex_norm_pos (i : VertexIndex) : 0 < ‖exactVertex i‖ := by
  rw [norm_pos_iff]
  intro h
  have hcoord := congrFun (congrArg WithLp.ofLp h) (2 : Fin 3)
  fin_cases i <;>
    simp [exactVertex, rationalVertex, rationalVertices, toR3] at hcoord <;>
    norm_num at hcoord

theorem exactVertex_norm_le_one (i : VertexIndex) : ‖exactVertex i‖ ≤ 1 := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three,
    Real.norm_eq_abs, sq_abs, one_pow]
  fin_cases i <;>
    simp [exactVertex, rationalVertex, rationalVertices, toR3] <;>
    norm_num

noncomputable def exactGoodPoly : GoodPoly VertexIndex where
  vertices := exactPolyhedron
  nontriv := exactVertex_norm_pos
  vertex_radius_le_one := exactVertex_norm_le_one

noncomputable def exactApproximation :
    RationalApprox.κApproxPoly exactPolyhedron rationalPolyhedron where
  bijection := Equiv.refl VertexIndex
  approx := by
    intro i
    change ‖toR3 (rationalVertex i) - toR3 (rationalVertex i)‖ ≤
      RationalApprox.κ
    simp [RationalApprox.κ]

end Noperthedron.Nopert214

end
