module

public import Noperthedron.Checker.Local
public import Noperthedron.RationalApprox.RationalLocal2
public import Noperthedron.Checker.Local2Fast

@[expose] public section


/-!
# The second-order local row check

`Row.ValidLocal₂` asserts that a row certifies the second-order rational
local theorem (`rational_local₂`) at the row's per-axis half-widths.  It is
an alternative to the first-order `Row.ValidLocal` — the table checker tries
the first-order (cheaper) predicate first, so only rows produced with
second-order certificates pay for the extra partial-derivative atoms.

The `δ` of the second-order theorem is not stored in the row: `Row.δ₂`
derives it from the center pose as half the largest `BoundDelta₂ℚ`
left-hand side plus a `κℚ` bump (for the strict inequality).
-/

namespace Noperthedron.Solution

open RationalApprox (sqrtApprox16 κℚ ΔrotMℚ ΔrotRMℚ)
open RationalApprox.LocalTheorem (BoundR₂ℚ BoundDelta₂ℚ)

/-- The `i`-th left-hand side of the row's `BoundDelta₂ℚ` condition. -/
def Row.BoundDelta₂ℚi (row : Row) (i : Fin 3) : ℚ :=
  let p := row.interval.centerPose
  let P_ : Local.TriangleQ := pythonVertexA ∘ row.Pi
  let Q_ : Local.TriangleQ := pythonVertexA ∘ row.Qi
  sqrtApprox16.upper_sqrt.norm (p.rotRℚ (p.rotM₁ℚ (P_ i)) - p.rotM₂ℚ (Q_ i)) + 6 * κℚ
    + ΔrotRMℚ sqrtApprox16.upper_sqrt p.θ₁ p.φ₁ (P_ i) row.εα row.εθ₁ row.εφ₁
    + ΔrotMℚ sqrtApprox16.upper_sqrt p.θ₂ p.φ₂ (Q_ i) row.εθ₂ row.εφ₂

/-- Straight-line form of `Row.BoundDelta₂ℚi` for compiled evaluation: the
ten trig values, the vertex components, and each matrix–vector product are
`let`-bound once.  The definitional form above re-evaluates `sinℚ`/`cosℚ`
inside every matrix-entry access (`Matrix` is a function type), which costs
the native checker ~55ms per local row; this form is ~50× cheaper.
Installed by `@[csimp]`, so compiled `decide`/`native_decide` use it while
the kernel path and all proofs keep the definitional form. -/
def Row.BoundDelta₂ℚiFast (row : Row) (i : Fin 3) : ℚ :=
  let p := row.interval.centerPose
  let f := sqrtApprox16.upper_sqrt.f
  let sθ₁ := RationalApprox.sinℚ p.θ₁
  let cθ₁ := RationalApprox.cosℚ p.θ₁
  let sφ₁ := RationalApprox.sinℚ p.φ₁
  let cφ₁ := RationalApprox.cosℚ p.φ₁
  let sθ₂ := RationalApprox.sinℚ p.θ₂
  let cθ₂ := RationalApprox.cosℚ p.θ₂
  let sφ₂ := RationalApprox.sinℚ p.φ₂
  let cφ₂ := RationalApprox.cosℚ p.φ₂
  let sα := RationalApprox.sinℚ p.α
  let cα := RationalApprox.cosℚ p.α
  let P := pythonVertexA (row.Pi i)
  let px := P 0
  let py := P 1
  let pz := P 2
  let Q := pythonVertexA (row.Qi i)
  let qx := Q 0
  let qy := Q 1
  let qz := Q 2
  -- rotM(θ₁,φ₁) P, shared by the head atom and the ΔrotRMℚ `rotM` atom
  let m0 := -sθ₁ * px + cθ₁ * py
  let m1 := -(cθ₁ * cφ₁) * px + -(sθ₁ * cφ₁) * py + sφ₁ * pz
  -- head atom: rotR α (rotM₁ P) − rotM₂ Q
  let h0 := cα * m0 + -sα * m1 - (-sθ₂ * qx + cθ₂ * qy)
  let h1 := sα * m0 + cα * m1
    - (-(cθ₂ * cφ₂) * qx + -(sθ₂ * cφ₂) * qy + sφ₂ * qz)
  -- ΔrotRMℚ norm atoms at (θ₁, φ₁) on P (each `+ 3κℚ` slack included)
  let nM := f (m0 * m0 + m1 * m1) + 3 * κℚ
  let nθ := f ((-cθ₁ * px + -sθ₁ * py) ^ 2
    + (sθ₁ * cφ₁ * px + -(cθ₁ * cφ₁) * py) ^ 2) + 3 * κℚ
  let nφ := f ((cθ₁ * sφ₁ * px + sθ₁ * sφ₁ * py + cφ₁ * pz) ^ 2) + 3 * κℚ
  let nθθ := f ((sθ₁ * px + -cθ₁ * py) ^ 2
    + (cθ₁ * cφ₁ * px + sθ₁ * cφ₁ * py) ^ 2) + 3 * κℚ
  let nθφ := f ((-(sθ₁ * sφ₁) * px + cθ₁ * sφ₁ * py) ^ 2) + 3 * κℚ
  let nφφ := f ((cθ₁ * cφ₁ * px + sθ₁ * cφ₁ * py + -sφ₁ * pz) ^ 2) + 3 * κℚ
  -- ΔrotMℚ norm atoms at (θ₂, φ₂) on Q
  let mθ := f ((-cθ₂ * qx + -sθ₂ * qy) ^ 2
    + (sθ₂ * cφ₂ * qx + -(cθ₂ * cφ₂) * qy) ^ 2) + 3 * κℚ
  let mφ := f ((cθ₂ * sφ₂ * qx + sθ₂ * sφ₂ * qy + cφ₂ * qz) ^ 2) + 3 * κℚ
  let mθθ := f ((sθ₂ * qx + -cθ₂ * qy) ^ 2
    + (cθ₂ * cφ₂ * qx + sθ₂ * cφ₂ * qy) ^ 2) + 3 * κℚ
  let mθφ := f ((-(sθ₂ * sφ₂) * qx + cθ₂ * sφ₂ * qy) ^ 2) + 3 * κℚ
  let mφφ := f ((cθ₂ * cφ₂ * qx + sθ₂ * cφ₂ * qy + -sφ₂ * qz) ^ 2) + 3 * κℚ
  f (h0 * h0 + h1 * h1) + 6 * κℚ
    + (row.εα * nM + row.εθ₁ * nθ + row.εφ₁ * nφ
      + (1/2) * (row.εα ^ 2 * nM + 2 * (row.εα * row.εθ₁) * nθ
        + 2 * (row.εα * row.εφ₁) * nφ + row.εθ₁ ^ 2 * nθθ
        + 2 * (row.εθ₁ * row.εφ₁) * nθφ + row.εφ₁ ^ 2 * nφφ)
      + (row.εα + row.εθ₁ + row.εφ₁) ^ 3 / 6)
    + (row.εθ₂ * mθ + row.εφ₂ * mφ
      + (1/2) * (row.εθ₂ ^ 2 * mθθ + 2 * (row.εθ₂ * row.εφ₂) * mθφ
        + row.εφ₂ ^ 2 * mφφ)
      + (row.εθ₂ + row.εφ₂) ^ 3 / 6)

set_option maxRecDepth 8192 in
@[csimp] theorem Row.boundDelta₂ℚi_eq_fast :
    @Row.BoundDelta₂ℚi = @Row.BoundDelta₂ℚiFast := by
  funext row i
  unfold Row.BoundDelta₂ℚi Row.BoundDelta₂ℚiFast
  unfold RationalApprox.ΔrotRMℚ RationalApprox.ΔrotMℚ RationalApprox.ΔrotMℚs
  simp only [RationalApprox.UpperSqrt.norm, dotProduct, Pose.rotRℚ, RationalApprox.rotRℚ,
    RationalApprox.rotRℚ_mat, Pose.rotM₁ℚ, RationalApprox.rotMℚ, RationalApprox.rotMℚ_mat,
    neg_mul, Function.comp_apply, Matrix.toLin'_apply, Matrix.cons_mulVec, Fin.sum_univ_three,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zero_mul, add_zero,
    Matrix.empty_mulVec, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd,
    Matrix.mulVec_empty, Pose.rotM₂ℚ, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_two, Matrix.head_cons, Matrix.tail_cons, mul_neg, Matrix.cons_val_fin_one,
    Matrix.mulVec, Matrix.of_apply, Matrix.cons_val', RationalApprox.rotMθℚ_mat,
    RationalApprox.rotMφℚ_mat, mul_zero, zero_add, one_div, RationalApprox.rotMθθℚ_mat,
    RationalApprox.rotMθφℚ_mat, RationalApprox.rotMφφℚ_mat, one_mul]
  ring_nf

/-- The derived second-order `δ`: half the largest `BoundDelta₂ℚ` left-hand
side, bumped by `κℚ` so the strict inequality holds by construction. -/
def Row.δ₂ (row : Row) : ℚ :=
  Finset.max' (Finset.image row.BoundDelta₂ℚi Finset.univ)
    (Finset.image_nonempty.mpr ⟨0, Finset.mem_univ 0⟩) / 2 + κℚ

/-- `BoundDelta₂ℚ` holds at `Row.δ₂` by construction. -/
lemma Row.boundDelta₂_δ₂ (row : Row) :
    BoundDelta₂ℚ row.δ₂ row.interval.centerPose
      (pythonVertexA ∘ row.Pi) (pythonVertexA ∘ row.Qi)
      row.εα row.εθ₁ row.εφ₁ row.εθ₂ row.εφ₂ sqrtApprox16 := by
  intro i
  have hle := Finset.le_max' (Finset.image row.BoundDelta₂ℚi Finset.univ)
    (row.BoundDelta₂ℚi i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hκ : (0 : ℚ) < κℚ := by norm_num [κℚ]
  show row.BoundDelta₂ℚi i < 2 * row.δ₂
  unfold Row.δ₂
  linarith

/-- Assertion that a row constitutes a valid application of the second-order
rational local theorem at the row's per-axis half-widths. -/
@[mk_iff]
structure Row.ValidLocal₂ (row : Row) : Prop where
  nodeType_eq : row.nodeType = 2
  center_in_fourQ : row.interval.centerPose ∈ fourInterval ℚ
  exists_symmetry : ∃ s : TriangleSymmetry,
    s.applicable row.Qi ∧ ∀ i, row.Pi i = s.apply (row.Qi i)
  X₁_inner_gt : Local.TriangleQ.Aε₂ℚσ row.θ₁ row.φ₁ (pythonVertexA ∘ row.Pi)
    row.εθ₁ row.εφ₁ 0
  X₂_inner_gt : Local.TriangleQ.Aε₂ℚσ row.θ₂ row.φ₂ (pythonVertexA ∘ row.Qi)
    row.εθ₂ row.εφ₂ row.sigma_Q.val
  P_spanning : Local.TriangleQ.Spanning₂ℚ row.θ₁ row.φ₁ (pythonVertexA ∘ row.Pi)
    row.εθ₁ row.εφ₁
  Q_spanning : Local.TriangleQ.Spanning₂ℚ row.θ₂ row.φ₂ (pythonVertexA ∘ row.Qi)
    row.εθ₂ row.εφ₂
  rpos : 0 < row.r
  r_valid : BoundR₂ℚ row.r row.interval.centerPose (pythonVertexA ∘ row.Qi)
    row.εθ₂ row.εφ₂ sqrtApprox16
  Bε₂ℚ : Local.TriangleQ.Bε₂ℚ row.Qi pythonVertexA row.interval.centerPose
    row.εθ₂ row.εφ₂ row.δ₂ row.r sqrtApprox16.upper_sqrt

instance (row : Row) : Decidable (Row.ValidLocal₂ row) :=
  decidable_of_iff _ (Row.validLocal₂_iff row).symm

end Noperthedron.Solution
end
