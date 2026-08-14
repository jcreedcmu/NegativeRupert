module

public import Mathlib.Data.Finset.Max

public import Noperthedron.SolutionTable.Defs
public import Noperthedron.Vertices.Python
public import Noperthedron.Vertices.PythonInt
public import Noperthedron.Vertices.PythonNat
public import Noperthedron.Vertices.Trig
public import Noperthedron.RationalApprox.RationalGlobal
public import Noperthedron.RationalApprox.GlobalNat
-- Mirror the imports at the meta phase so the test `#eval`s below can
-- interpret cross-module code under the module system.
public meta import Mathlib.Data.Finset.Max
public meta import Noperthedron.SolutionTable.Defs
public meta import Noperthedron.Vertices.Python
public meta import Noperthedron.Vertices.PythonInt
public meta import Noperthedron.Vertices.PythonNat
public meta import Noperthedron.Vertices.Trig
public meta import Noperthedron.RationalApprox.RationalGlobal
public meta import Noperthedron.RationalApprox.GlobalNat

@[expose] public section


/-!
# Global Validity Checker

A computable, pure-ℚ checker that verifies whether a decision-tree row
satisfies the preconditions of the rational global theorem. Everything
here is computable — no `noncomputable` keyword.
-/

namespace Noperthedron.Solution

abbrev Row.G_gt_maxH (r : Row) : Prop :=
  RationalApprox.GlobalTheorem.Gℚ r.interval.centerPose r.εα r.εθ₁ r.εφ₁ r.S r.w >
    RationalApprox.GlobalTheorem.maxHℚ r.interval.centerPose pythonPolyQ r.εθ₂ r.εφ₂ r.w

/-- The all-`Nat` fast global check for a row: `Gℚ_gt_maxHℚ_fastNat` on the
packed vertex table. Under `decide +kernel` every per-vertex operation is a
single accelerated `Nat` primitive. -/
def Row.fastNatGlobal (r : Row) : Bool :=
  RationalApprox.GlobalTheorem.Gℚ_gt_maxHℚ_fastNat pythonVertexBig 90
    (45 * r.S_index.ℓ.val + 15 * r.S_index.i.val + r.S_index.k.val)
    r.interval.centerPose r.εα r.εθ₁ r.εφ₁ r.εθ₂ r.εφ₂
    r.wx_numerator r.wy_numerator r.w_denominator

theorem Row.fastNatGlobal_sound {r : Row} (h : r.fastNatGlobal = true) :
    r.G_gt_maxH := by
  have hsflat : 45 * r.S_index.ℓ.val + 15 * r.S_index.i.val + r.S_index.k.val < 90 := by
    have h1 := r.S_index.ℓ.isLt
    have h2 := r.S_index.i.isLt
    have h3 := r.S_index.k.isLt
    omega
  have hvq : ∀ (idx : VertexIndex) (c : Fin 3),
      pythonVertex idx c = ((pythonVertexNum idx c : ℤ) : ℚ) / 10 ^ 16 :=
    fun idx c => pythonVertexNumCurried_eq idx.ℓ idx.i idx.k c
  have hSix : VertexIndex.ofFin90
      ⟨45 * r.S_index.ℓ.val + 15 * r.S_index.i.val + r.S_index.k.val, hsflat⟩
      = r.S_index := by
    have h90 := VertexIndex.ofFin90_flat r.S_index
    simpa only [Nat.mod_eq_of_lt hsflat] using h90
  have hSspec := pythonVertexBig_spec
    ⟨45 * r.S_index.ℓ.val + 15 * r.S_index.i.val + r.S_index.k.val, hsflat⟩
  rw [hSix] at hSspec
  dsimp only at hSspec
  obtain ⟨hS0z, hS1z, hS2z⟩ := hSspec
  refine (RationalApprox.GlobalTheorem.Gℚ_gt_maxHℚ_check_iff r.interval.centerPose
    r.εα r.εθ₁ r.εφ₁ r.εθ₂_nonneg r.εφ₂_nonneg r.S pythonPolyQ r.w).mp ?_
  refine RationalApprox.GlobalTheorem.Gℚ_gt_maxHℚ_fastNat_sound pythonVertexBig 90
    (45 * r.S_index.ℓ.val + 15 * r.S_index.i.val + r.S_index.k.val)
    r.interval.centerPose r.εα r.εθ₁ r.εφ₁ r.εθ₂ r.εφ₂
    r.wx_numerator r.wy_numerator r.w_denominator r.S pythonPolyQ r.w rfl rfl
    (fun j => VertexIndex.ofFin90 ⟨j % 90, Nat.mod_lt _ (by norm_num)⟩)
    ?_ ?_ ?_ ?_ ?_ h
  · -- coverage
    intro k
    have h1 := k.ℓ.isLt
    have h2 := k.i.isLt
    have h3 := k.k.isLt
    exact ⟨45 * k.ℓ.val + 15 * k.i.val + k.k.val, by omega, VertexIndex.ofFin90_flat k⟩
  · -- packed-table field equations
    intro j hj
    have hspec := pythonVertexBig_spec ⟨j, hj⟩
    obtain ⟨hz0, hz1, hz2⟩ := hspec
    simp only [Nat.mod_eq_of_lt hj]
    refine ⟨?_, ?_, ?_⟩
    · rw [show pythonPolyQ.v (VertexIndex.ofFin90 ⟨j, hj⟩) 0
          = ((pythonVertexNum (VertexIndex.ofFin90 ⟨j, hj⟩) 0 : ℤ) : ℚ) / 10 ^ 16 from
        hvq _ 0, div_mul_cancel₀ _ (by norm_num : ((10:ℚ) ^ 16) ≠ 0)]
      exact_mod_cast hz0
    · rw [show pythonPolyQ.v (VertexIndex.ofFin90 ⟨j, hj⟩) 1
          = ((pythonVertexNum (VertexIndex.ofFin90 ⟨j, hj⟩) 1 : ℤ) : ℚ) / 10 ^ 16 from
        hvq _ 1, div_mul_cancel₀ _ (by norm_num : ((10:ℚ) ^ 16) ≠ 0)]
      exact_mod_cast hz1
    · rw [show pythonPolyQ.v (VertexIndex.ofFin90 ⟨j, hj⟩) 2
          = ((pythonVertexNum (VertexIndex.ofFin90 ⟨j, hj⟩) 2 : ℤ) : ℚ) / 10 ^ 16 from
        hvq _ 2, div_mul_cancel₀ _ (by norm_num : ((10:ℚ) ^ 16) ≠ 0)]
      exact_mod_cast hz2
  · -- S 0
    rw [show r.S 0 = ((pythonVertexNum r.S_index 0 : ℤ) : ℚ) / 10 ^ 16 from hvq _ 0]
    congr 1
    rw [hS0z]
    push_cast
    ring
  · -- S 1
    rw [show r.S 1 = ((pythonVertexNum r.S_index 1 : ℤ) : ℚ) / 10 ^ 16 from hvq _ 1]
    congr 1
    rw [hS1z]
    push_cast
    ring
  · -- S 2
    rw [show r.S 2 = ((pythonVertexNum r.S_index 2 : ℤ) : ℚ) / 10 ^ 16 from hvq _ 2]
    congr 1
    rw [hS2z]
    push_cast
    ring

/-- Decidable instance for `Row.G_gt_maxH`: try the all-`Nat` fast path
(`Row.fastNatGlobal`, sound by `fastNatGlobal_sound`); rows it rejects fall
back to the exact ℚ checker `Gℚ_gt_maxHℚ_check`. On table rows the
fast path always accepts, so the kernel never evaluates the fallback. -/
instance (r : Row) : Decidable r.G_gt_maxH :=
  dite (r.fastNatGlobal = true)
    (fun h => .isTrue (Row.fastNatGlobal_sound h))
    (fun _ =>
      decidable_of_iff _ <|
        RationalApprox.GlobalTheorem.Gℚ_gt_maxHℚ_check_iff
          r.interval.centerPose r.εα r.εθ₁ r.εφ₁ r.εθ₂_nonneg r.εφ₂_nonneg r.S pythonPolyQ r.w)

/-! ## The main checker -/

/-- Assertion that a row constitutes a valid application of the rational global theorem. -/
@[mk_iff]
structure Row.ValidGlobal (row : Row) : Prop where
  nodeType_eq : row.nodeType = 1
  w_unit : row.wx_numerator ^ 2 + row.wy_numerator ^ 2 = (row.w_denominator : ℤ) ^ 2
  w_denominator_pos : 0 < row.w_denominator
  center_in_fourQ : row.interval.centerPose ∈ fourInterval ℚ
  εθ₁_pos : 0 < row.εθ₁
  εφ₁_pos : 0 < row.εφ₁
  εθ₂_pos : 0 < row.εθ₂
  εφ₂_pos : 0 < row.εφ₂
  εα_pos : 0 < row.εα
  G_gt_maxH : row.G_gt_maxH

instance (row : Row) : Decidable (Row.ValidGlobal row) :=
  decidable_of_iff _ (Row.validGlobal_iff row).symm

/-! ## Smoke test -/

/-- Row 91 from `data/solution_tree_300.csv` — the first global leaf. -/
def testGlobalRow : Row := {
  ID := 91, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := Interval.ofIntPose
    { θ₁ := 0, θ₂ := 806400, φ₁ := 0, φ₂ := 808960, α := -23459840 }
    { θ₁ := 806400, θ₂ := 1612800, φ₁ := 806400, φ₂ := 1617920, α := -22650880 }
    (by decide),
  S_index := VertexIndex.ofFin90 ⟨39, by omega⟩,
  wx_numerator := 5319166373, wy_numerator := 15662395164,
  w_denominator := 16540984045,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r' := 0, sigma_Q := ⟨0, by simp [Finset.mem_Icc]⟩
}

/-- info: true -/
#guard_msgs in
#eval testGlobalRow.ValidGlobal

end Noperthedron.Solution
end
