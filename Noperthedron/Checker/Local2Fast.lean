module

public import Noperthedron.Checker.Local
public import Noperthedron.RationalApprox.RationalLocal2

@[expose] public section


/-!
# Hoisted-scalar checkers for the second-order local conditions

The second-order rational conditions read the family matrices
(`rotMℚ_mat` … `rotMφφℚ_mat`) through `Matrix.mulVec`, and every entry
access re-evaluates a `sinℚ`/`cosℚ` partial sum — ~10⁵ trig evaluations per
`Bε₂ℚ` row (measured ~90 s/row).  The `check` functions below mirror the
established `matEntries` pattern: the four trig values are computed once per
pose, the 36 family entries once per `(θ, φ)`, and each applied family
vector once per vertex; `check_iff` proves them equal to the Prop layer, and
high-priority `Decidable` instances route `Row.ValidLocal₂` through them.
-/

namespace Noperthedron.Solution

open RationalApprox (sqrtApprox16 κℚ ΔrotMℚ ΔrotMℚs ΔrotMℚ₂ ΔvecXℚ ΔprodMMℚ prodTℚ
  rot90ℚ dqNrm Bε₂ℚnum Bε₂ℚlhs vecXℚ vecXθℚ vecXφℚ vecXθθℚ vecXθφℚ
  rotMℚ_mat rotMθℚ_mat rotMφℚ_mat rotMθθℚ_mat rotMθφℚ_mat rotMφφℚ_mat
  sinℚ cosℚ UpperSqrt)
open scoped Matrix

namespace Local2Fast

/-- Entries of the six family matrices at one `(θ, φ)`, hoisted so the trig
partial sums are evaluated once. Field prefixes: `a` = M, `b` = Mθ, `c` = Mφ,
`d` = Mθθ, `e` = Mθφ, `f` = Mφφ. -/
structure Fam2 : Type where
  (a00 a01 a02 a10 a11 a12 : ℚ)
  (b00 b01 b02 b10 b11 b12 : ℚ)
  (c00 c01 c02 c10 c11 c12 : ℚ)
  (d00 d01 d02 d10 d11 d12 : ℚ)
  (e00 e01 e02 e10 e11 e12 : ℚ)
  (f00 f01 f02 f10 f11 f12 : ℚ)

@[inline] def fam2 (θ φ : ℚ) : Fam2 :=
  let st := sinℚ θ
  let ct := cosℚ θ
  let sf := sinℚ φ
  let cf := cosℚ φ
  { a00 := -st, a01 := ct, a02 := 0,
    a10 := -ct * cf, a11 := -st * cf, a12 := sf,
    b00 := -ct, b01 := -st, b02 := 0,
    b10 := st * cf, b11 := -ct * cf, b12 := 0,
    c00 := 0, c01 := 0, c02 := 0,
    c10 := ct * sf, c11 := st * sf, c12 := cf,
    d00 := st, d01 := -ct, d02 := 0,
    d10 := ct * cf, d11 := st * cf, d12 := 0,
    e00 := 0, e01 := 0, e02 := 0,
    e10 := -st * sf, e11 := ct * sf, e12 := 0,
    f00 := 0, f01 := 0, f02 := 0,
    f10 := ct * cf, f11 := st * cf, f12 := -sf }

/-- The six applied 2-vectors of one 3-vector under a `Fam2`. -/
structure App6 : Type where
  (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 f0 f1 : ℚ)
deriving Inhabited

@[inline] def app6 (g : Fam2) (v : Fin 3 → ℚ) : App6 :=
  let v0 := v 0
  let v1 := v 1
  let v2 := v 2
  { a0 := g.a00 * v0 + g.a01 * v1 + g.a02 * v2,
    a1 := g.a10 * v0 + g.a11 * v1 + g.a12 * v2,
    b0 := g.b00 * v0 + g.b01 * v1 + g.b02 * v2,
    b1 := g.b10 * v0 + g.b11 * v1 + g.b12 * v2,
    c0 := g.c00 * v0 + g.c01 * v1 + g.c02 * v2,
    c1 := g.c10 * v0 + g.c11 * v1 + g.c12 * v2,
    d0 := g.d00 * v0 + g.d01 * v1 + g.d02 * v2,
    d1 := g.d10 * v0 + g.d11 * v1 + g.d12 * v2,
    e0 := g.e00 * v0 + g.e01 * v1 + g.e02 * v2,
    e1 := g.e10 * v0 + g.e11 * v1 + g.e12 * v2,
    f0 := g.f00 * v0 + g.f01 * v1 + g.f02 * v2,
    f1 := g.f10 * v0 + g.f11 * v1 + g.f12 * v2 }

/-! ### Application identities

Each applied family component equals the corresponding `app6` field. -/

private lemma mulVec_c0 (M : Matrix (Fin 2) (Fin 3) ℚ) (v : Fin 3 → ℚ) :
    (M *ᵥ v) 0 = M 0 0 * v 0 + M 0 1 * v 1 + M 0 2 * v 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private lemma mulVec_c1 (M : Matrix (Fin 2) (Fin 3) ℚ) (v : Fin 3 → ℚ) :
    (M *ᵥ v) 1 = M 1 0 * v 0 + M 1 1 * v 1 + M 1 2 * v 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

section AppLemmas
variable (θ φ : ℚ) (v : Fin 3 → ℚ)

lemma app6_a0 : (app6 (fam2 θ φ) v).a0 = (rotMℚ_mat θ φ *ᵥ v) 0 := by
  rw [mulVec_c0]; simp [app6, fam2, rotMℚ_mat]
lemma app6_a1 : (app6 (fam2 θ φ) v).a1 = (rotMℚ_mat θ φ *ᵥ v) 1 := by
  rw [mulVec_c1]; simp [app6, fam2, rotMℚ_mat]
lemma app6_b0 : (app6 (fam2 θ φ) v).b0 = (rotMθℚ_mat θ φ *ᵥ v) 0 := by
  rw [mulVec_c0]; simp [app6, fam2, rotMθℚ_mat]
lemma app6_b1 : (app6 (fam2 θ φ) v).b1 = (rotMθℚ_mat θ φ *ᵥ v) 1 := by
  rw [mulVec_c1]; simp [app6, fam2, rotMθℚ_mat]
lemma app6_c0 : (app6 (fam2 θ φ) v).c0 = (rotMφℚ_mat θ φ *ᵥ v) 0 := by
  rw [mulVec_c0]; simp [app6, fam2, rotMφℚ_mat]
lemma app6_c1 : (app6 (fam2 θ φ) v).c1 = (rotMφℚ_mat θ φ *ᵥ v) 1 := by
  rw [mulVec_c1]; simp [app6, fam2, rotMφℚ_mat]
lemma app6_d0 : (app6 (fam2 θ φ) v).d0 = (rotMθθℚ_mat θ φ *ᵥ v) 0 := by
  rw [mulVec_c0]; simp [app6, fam2, rotMθθℚ_mat]
lemma app6_d1 : (app6 (fam2 θ φ) v).d1 = (rotMθθℚ_mat θ φ *ᵥ v) 1 := by
  rw [mulVec_c1]; simp [app6, fam2, rotMθθℚ_mat]
lemma app6_e0 : (app6 (fam2 θ φ) v).e0 = (rotMθφℚ_mat θ φ *ᵥ v) 0 := by
  rw [mulVec_c0]; simp [app6, fam2, rotMθφℚ_mat]
lemma app6_e1 : (app6 (fam2 θ φ) v).e1 = (rotMθφℚ_mat θ φ *ᵥ v) 1 := by
  rw [mulVec_c1]; simp [app6, fam2, rotMθφℚ_mat]
lemma app6_f0 : (app6 (fam2 θ φ) v).f0 = (rotMφφℚ_mat θ φ *ᵥ v) 0 := by
  rw [mulVec_c0]; simp [app6, fam2, rotMφφℚ_mat]
lemma app6_f1 : (app6 (fam2 θ φ) v).f1 = (rotMφφℚ_mat θ φ *ᵥ v) 1 := by
  rw [mulVec_c1]; simp [app6, fam2, rotMφφℚ_mat]

end AppLemmas

/-! ### Scalar forms of the shared budget pieces -/

/-- `su.norm u` on a 2-vector as a scalar `su.f` call. -/
lemma norm2_eq (su : UpperSqrt) (u : Fin 2 → ℚ) :
    su.norm u = su.f (u 0 * u 0 + u 1 * u 1) := by
  simp [RationalApprox.UpperSqrt.norm, dotProduct, Fin.sum_univ_two]

/-- `su.norm` on a 3-vector as a scalar `su.f` call. -/
lemma norm3_eq (su : UpperSqrt) (u : Fin 3 → ℚ) :
    su.norm u = su.f (u 0 * u 0 + u 1 * u 1 + u 2 * u 2) := by
  simp [RationalApprox.UpperSqrt.norm, dotProduct, Fin.sum_univ_three]

/-- `prodTℚ` at `rot90ℚ` in applied components. -/
lemma prodT_rot90 (Am Bm : Matrix (Fin 2) (Fin 3) ℚ) (v w : Fin 3 → ℚ) :
    prodTℚ rot90ℚ Am Bm v w
      = (Am *ᵥ v) 0 * (Bm *ᵥ w) 1 - (Am *ᵥ v) 1 * (Bm *ᵥ w) 0 := by
  unfold prodTℚ rot90ℚ
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- `prodTℚ` at the identity in applied components. -/
lemma prodT_one (Am Bm : Matrix (Fin 2) (Fin 3) ℚ) (v w : Fin 3 → ℚ) :
    prodTℚ 1 Am Bm v w
      = (Am *ᵥ v) 0 * (Bm *ᵥ w) 0 + (Am *ᵥ v) 1 * (Bm *ᵥ w) 1 := by
  unfold prodTℚ
  rw [Matrix.one_mulVec]
  simp [dotProduct, Fin.sum_univ_two]

/-- The scalar `ΔrotMℚs` on `app6` fields (any slack/scale). -/
@[inline] def dRotMs (su : UpperSqrt) (slack : ℚ) (q : App6) (εθ εφ scale : ℚ) : ℚ :=
  εθ * (su.f (q.b0 * q.b0 + q.b1 * q.b1) + slack)
  + εφ * (su.f (q.c0 * q.c0 + q.c1 * q.c1) + slack)
  + (1/2) * (εθ^2 * (su.f (q.d0 * q.d0 + q.d1 * q.d1) + slack)
      + 2*(εθ*εφ) * (su.f (q.e0 * q.e0 + q.e1 * q.e1) + slack)
      + εφ^2 * (su.f (q.f0 * q.f0 + q.f1 * q.f1) + slack))
  + scale * (εθ + εφ)^3 / 6

lemma dRotMs_eq (su : UpperSqrt) (slack θ φ : ℚ) (v : Fin 3 → ℚ) (εθ εφ scale : ℚ) :
    ΔrotMℚs su slack θ φ v εθ εφ scale
      = dRotMs su slack (app6 (fam2 θ φ) v) εθ εφ scale := by
  unfold ΔrotMℚs dRotMs
  rw [norm2_eq, norm2_eq, norm2_eq, norm2_eq, norm2_eq,
    app6_b0, app6_b1, app6_c0, app6_c1, app6_d0, app6_d1,
    app6_e0, app6_e1, app6_f0, app6_f1]

/-- The scalar `ΔprodMMℚ` at `rot90ℚ` on `app6` fields. -/
@[inline] def dProd90 (slack : ℚ) (qv qw : App6) (εθ εφ scale : ℚ) : ℚ :=
  εθ * (|(qv.b0 * qw.a1 - qv.b1 * qw.a0) + (qv.a0 * qw.b1 - qv.a1 * qw.b0)| + 2 * slack)
  + εφ * (|(qv.c0 * qw.a1 - qv.c1 * qw.a0) + (qv.a0 * qw.c1 - qv.a1 * qw.c0)| + 2 * slack)
  + (1/2) * (εθ^2 * (|(qv.d0 * qw.a1 - qv.d1 * qw.a0)
          + 2 * (qv.b0 * qw.b1 - qv.b1 * qw.b0)
          + (qv.a0 * qw.d1 - qv.a1 * qw.d0)| + 4 * slack)
      + 2*(εθ*εφ) * (|(qv.e0 * qw.a1 - qv.e1 * qw.a0)
          + (qv.b0 * qw.c1 - qv.b1 * qw.c0)
          + (qv.c0 * qw.b1 - qv.c1 * qw.b0)
          + (qv.a0 * qw.e1 - qv.a1 * qw.e0)| + 4 * slack)
      + εφ^2 * (|(qv.f0 * qw.a1 - qv.f1 * qw.a0)
          + 2 * (qv.c0 * qw.c1 - qv.c1 * qw.c0)
          + (qv.a0 * qw.f1 - qv.a1 * qw.f0)| + 4 * slack))
  + 8 * scale * (εθ + εφ)^3 / 6

lemma dProd90_eq (slack θ φ : ℚ) (v w : Fin 3 → ℚ) (εθ εφ scale : ℚ) :
    ΔprodMMℚ rot90ℚ slack θ φ v w εθ εφ scale
      = dProd90 slack (app6 (fam2 θ φ) v) (app6 (fam2 θ φ) w) εθ εφ scale := by
  unfold ΔprodMMℚ dProd90
  simp only [prodT_rot90, app6_a0, app6_a1, app6_b0, app6_b1, app6_c0, app6_c1,
    app6_d0, app6_d1, app6_e0, app6_e1, app6_f0, app6_f1]

/-- The scalar `ΔprodMMℚ` at the identity on `app6` fields. -/
@[inline] def dProd1 (slack : ℚ) (qv qw : App6) (εθ εφ scale : ℚ) : ℚ :=
  εθ * (|(qv.b0 * qw.a0 + qv.b1 * qw.a1) + (qv.a0 * qw.b0 + qv.a1 * qw.b1)| + 2 * slack)
  + εφ * (|(qv.c0 * qw.a0 + qv.c1 * qw.a1) + (qv.a0 * qw.c0 + qv.a1 * qw.c1)| + 2 * slack)
  + (1/2) * (εθ^2 * (|(qv.d0 * qw.a0 + qv.d1 * qw.a1)
          + 2 * (qv.b0 * qw.b0 + qv.b1 * qw.b1)
          + (qv.a0 * qw.d0 + qv.a1 * qw.d1)| + 4 * slack)
      + 2*(εθ*εφ) * (|(qv.e0 * qw.a0 + qv.e1 * qw.a1)
          + (qv.b0 * qw.c0 + qv.b1 * qw.c1)
          + (qv.c0 * qw.b0 + qv.c1 * qw.b1)
          + (qv.a0 * qw.e0 + qv.a1 * qw.e1)| + 4 * slack)
      + εφ^2 * (|(qv.f0 * qw.a0 + qv.f1 * qw.a1)
          + 2 * (qv.c0 * qw.c0 + qv.c1 * qw.c1)
          + (qv.a0 * qw.f0 + qv.a1 * qw.f1)| + 4 * slack))
  + 8 * scale * (εθ + εφ)^3 / 6

lemma dProd1_eq (slack θ φ : ℚ) (v w : Fin 3 → ℚ) (εθ εφ scale : ℚ) :
    ΔprodMMℚ 1 slack θ φ v w εθ εφ scale
      = dProd1 slack (app6 (fam2 θ φ) v) (app6 (fam2 θ φ) w) εθ εφ scale := by
  unfold ΔprodMMℚ dProd1
  simp only [prodT_one, app6_a0, app6_a1, app6_b0, app6_b1, app6_c0, app6_c1,
    app6_d0, app6_d1, app6_e0, app6_e1, app6_f0, app6_f1]


/-! ### `Aε₂ℚσ` check -/

private lemma dotX (θ φ : ℚ) (v : Fin 3 → ℚ) :
    vecXℚ θ φ ⬝ᵥ v
      = cosℚ θ * sinℚ φ * v 0 + sinℚ θ * sinℚ φ * v 1 + cosℚ φ * v 2 := by
  simp [vecXℚ, dotProduct, Fin.sum_univ_three]

private lemma dotXt (θ φ : ℚ) (v : Fin 3 → ℚ) :
    vecXθℚ θ φ ⬝ᵥ v
      = -sinℚ θ * sinℚ φ * v 0 + cosℚ θ * sinℚ φ * v 1 + 0 * v 2 := by
  simp [vecXθℚ, dotProduct, Fin.sum_univ_three]

private lemma dotXf (θ φ : ℚ) (v : Fin 3 → ℚ) :
    vecXφℚ θ φ ⬝ᵥ v
      = cosℚ θ * cosℚ φ * v 0 + sinℚ θ * cosℚ φ * v 1 + -sinℚ φ * v 2 := by
  simp [vecXφℚ, dotProduct, Fin.sum_univ_three]

private lemma dotXtt (θ φ : ℚ) (v : Fin 3 → ℚ) :
    vecXθθℚ θ φ ⬝ᵥ v
      = -cosℚ θ * sinℚ φ * v 0 + -sinℚ θ * sinℚ φ * v 1 + 0 * v 2 := by
  simp [vecXθθℚ, dotProduct, Fin.sum_univ_three]

private lemma dotXtf (θ φ : ℚ) (v : Fin 3 → ℚ) :
    vecXθφℚ θ φ ⬝ᵥ v
      = -sinℚ θ * cosℚ φ * v 0 + cosℚ θ * cosℚ φ * v 1 + 0 * v 2 := by
  simp [vecXθφℚ, dotProduct, Fin.sum_univ_three]

/-- The scalar `ΔvecXℚ` on precomputed dots. -/
@[inline] def dVecX (dX dXt dXf dXtt dXtf εθ εφ : ℚ) : ℚ :=
  εθ * (|dXt| + 3 * κℚ) + εφ * (|dXf| + 3 * κℚ)
  + (1/2) * (εθ^2 * (|dXtt| + 3 * κℚ) + 2*(εθ*εφ) * (|dXtf| + 3 * κℚ)
      + εφ^2 * (|dX| + 3 * κℚ))
  + (εθ + εφ)^3/6

private lemma dVecX_eq (θ φ : ℚ) (v : Fin 3 → ℚ) (εθ εφ : ℚ) :
    ΔvecXℚ θ φ v εθ εφ
      = dVecX (vecXℚ θ φ ⬝ᵥ v) (vecXθℚ θ φ ⬝ᵥ v) (vecXφℚ θ φ ⬝ᵥ v)
          (vecXθθℚ θ φ ⬝ᵥ v) (vecXθφℚ θ φ ⬝ᵥ v) εθ εφ := rfl

/-- Per-vertex `Aε₂ℚσ` test on hoisted trig scalars. -/
@[inline] def aeVert (st ct sf cf s εθ εφ : ℚ) (v : Fin 3 → ℚ) : Bool :=
  let dX := ct * sf * v 0 + st * sf * v 1 + cf * v 2
  let dXt := -st * sf * v 0 + ct * sf * v 1 + 0 * v 2
  let dXf := ct * cf * v 0 + st * cf * v 1 + -sf * v 2
  let dXtt := -ct * sf * v 0 + -st * sf * v 1 + 0 * v 2
  let dXtf := -st * cf * v 0 + ct * cf * v 1 + 0 * v 2
  decide (dVecX dX dXt dXf dXtt dXtf εθ εφ + 3 * κℚ < s * dX)

/-- Hoisted `Aε₂ℚσ` check. -/
def aeCheck (θ φ : ℚ) (P_ : Local.TriangleQ) (εθ εφ : ℚ) (σ : ℕ) : Bool :=
  let st := sinℚ θ
  let ct := cosℚ θ
  let sf := sinℚ φ
  let cf := cosℚ φ
  let s : ℚ := (-1)^σ
  aeVert st ct sf cf s εθ εφ (P_ 0) && aeVert st ct sf cf s εθ εφ (P_ 1)
    && aeVert st ct sf cf s εθ εφ (P_ 2)

theorem aeCheck_iff (θ φ : ℚ) (P_ : Local.TriangleQ) (εθ εφ : ℚ) (σ : ℕ) :
    aeCheck θ φ P_ εθ εφ σ = true ↔ Local.TriangleQ.Aε₂ℚσ θ φ P_ εθ εφ σ := by
  unfold aeCheck aeVert Local.TriangleQ.Aε₂ℚσ
  simp only [Bool.and_eq_true, decide_eq_true_eq, dVecX_eq,
    dotX, dotXt, dotXf, dotXtt, dotXtf]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro h
    exact ⟨⟨h 0, h 1⟩, h 2⟩

instance (priority := high) instDecidableAε₂ℚσ (θ φ : ℚ) (P_ : Local.TriangleQ)
    (εθ εφ : ℚ) (σ : ℕ) : Decidable (Local.TriangleQ.Aε₂ℚσ θ φ P_ εθ εφ σ) :=
  decidable_of_iff _ (aeCheck_iff θ φ P_ εθ εφ σ)

/-! ### `Spanning₂ℚ` check -/

/-- Per-pair spanning test on applied vectors. -/
@[inline] def spanPair (qv qw : App6) (εθ εφ : ℚ) : Bool :=
  decide (dProd90 (5 * κℚ) qv qw εθ εφ 1 + 5 * κℚ < qv.a0 * qw.a1 - qv.a1 * qw.a0)

/-- Hoisted `Spanning₂ℚ` check. -/
def spanCheck (θ φ : ℚ) (P_ : Local.TriangleQ) (εθ εφ : ℚ) : Bool :=
  let g := fam2 θ φ
  let q0 := app6 g (P_ 0)
  let q1 := app6 g (P_ 1)
  let q2 := app6 g (P_ 2)
  spanPair q0 q1 εθ εφ && spanPair q1 q2 εθ εφ && spanPair q2 q0 εθ εφ

theorem spanCheck_iff (θ φ : ℚ) (P_ : Local.TriangleQ) (εθ εφ : ℚ) :
    spanCheck θ φ P_ εθ εφ = true ↔ Local.TriangleQ.Spanning₂ℚ θ φ P_ εθ εφ := by
  unfold spanCheck spanPair Local.TriangleQ.Spanning₂ℚ
  simp only [Bool.and_eq_true, decide_eq_true_eq, dProd90_eq, prodT_rot90,
    app6_a0, app6_a1]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro h
    exact ⟨⟨h 0, h 1⟩, h 2⟩

instance (priority := high) instDecidableSpanning₂ℚ (θ φ : ℚ) (P_ : Local.TriangleQ)
    (εθ εφ : ℚ) : Decidable (Local.TriangleQ.Spanning₂ℚ θ φ P_ εθ εφ) :=
  decidable_of_iff _ (spanCheck_iff θ φ P_ εθ εφ)

/-! ### `BoundR₂ℚ` check -/

private lemma toLin'_apply_c (θ φ : ℚ) (v : Fin 3 → ℚ) :
    (RationalApprox.rotMℚ θ φ) v = rotMℚ_mat θ φ *ᵥ v := by
  simp [RationalApprox.rotMℚ, Matrix.toLin'_apply]

private lemma rotM₂Rℚ_c0' (p : Pose ℚ) (v : Fin 3 → ℚ) :
    p.rotM₂Rℚ v 0 = RationalApprox.round13 ((app6 (fam2 p.θ₂ p.φ₂) v).a0) := by
  unfold Pose.rotM₂Rℚ RationalApprox.round13v Pose.rotM₂ℚ
  rw [toLin'_apply_c, app6_a0]

private lemma rotM₂Rℚ_c1' (p : Pose ℚ) (v : Fin 3 → ℚ) :
    p.rotM₂Rℚ v 1 = RationalApprox.round13 ((app6 (fam2 p.θ₂ p.φ₂) v).a1) := by
  unfold Pose.rotM₂Rℚ RationalApprox.round13v Pose.rotM₂ℚ
  rw [toLin'_apply_c, app6_a1]

/-- Hoisted `BoundR₂ℚ` check (at `sqrtApprox16`). -/
def brCheck (r : ℚ) (p : Pose ℚ) (Q_ : Local.TriangleQ) (εθ εφ : ℚ) : Bool :=
  let g := fam2 p.θ₂ p.φ₂
  let one : ℚ := 1
  let rhsB := fun (q : App6) =>
    r + dRotMs sqrtApprox16.upper_sqrt (3 * κℚ) q εθ εφ one + 3 * κℚ
  let lhsB := fun (q : App6) =>
    let q0 := RationalApprox.round13 q.a0
    let q1 := RationalApprox.round13 q.a1
    sqrtApprox16.lower_sqrt.f (q0 * q0 + q1 * q1)
  (List.finRange 3).all fun i =>
    let q := app6 g (Q_ i)
    decide (rhsB q < lhsB q)

theorem brCheck_iff (r : ℚ) (p : Pose ℚ) (Q_ : Local.TriangleQ) (εθ εφ : ℚ) :
    brCheck r p Q_ εθ εφ = true ↔
      RationalApprox.LocalTheorem.BoundR₂ℚ r p Q_ εθ εφ sqrtApprox16 := by
  unfold brCheck RationalApprox.LocalTheorem.BoundR₂ℚ ΔrotMℚ
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]
  refine forall_congr' fun i => ?_
  rw [dRotMs_eq,
    show sqrtApprox16.lower_sqrt.norm (p.rotM₂Rℚ (Q_ i))
        = sqrtApprox16.lower_sqrt.f (p.rotM₂Rℚ (Q_ i) 0 * p.rotM₂Rℚ (Q_ i) 0
          + p.rotM₂Rℚ (Q_ i) 1 * p.rotM₂Rℚ (Q_ i) 1) from by
      simp [RationalApprox.LowerSqrt.norm, dotProduct, Fin.sum_univ_two],
    rotM₂Rℚ_c0', rotM₂Rℚ_c1']

instance (priority := high) instDecidableBoundR₂ℚ (r : ℚ) (p : Pose ℚ)
    (Q_ : Local.TriangleQ) (εθ εφ : ℚ) :
    Decidable (RationalApprox.LocalTheorem.BoundR₂ℚ r p Q_ εθ εφ sqrtApprox16) :=
  decidable_of_iff _ (brCheck_iff r p Q_ εθ εφ)

/-! ### `Bε₂ℚ` check -/

/-- Componentwise difference of applied families (`M(u−w) = Mu − Mw`). -/
@[inline] def App6.sub (x y : App6) : App6 :=
  ⟨x.a0 - y.a0, x.a1 - y.a1, x.b0 - y.b0, x.b1 - y.b1, x.c0 - y.c0, x.c1 - y.c1,
   x.d0 - y.d0, x.d1 - y.d1, x.e0 - y.e0, x.e1 - y.e1, x.f0 - y.f0, x.f1 - y.f1⟩

private lemma app6_sub (g : Fam2) (u w : Fin 3 → ℚ) :
    app6 g (u - w) = (app6 g u).sub (app6 g w) := by
  unfold app6 App6.sub
  simp only [Pi.sub_apply]
  congr 1 <;> ring

/-- Per-pose applied-family table over all 90 vertices, indexed by
`flat ⟨k, ℓ, i⟩ = 45·ℓ + 15·i + k` (as `rowDots`). -/
def apps6 (g : Fam2) : List App6 :=
  List.ofFn (n := 90) fun j => app6 g (pythonVertexA (ofFlat j.val j.isLt))

/-- Read an `apps6` table at a vertex index. -/
def apps6Get (t : List App6) (a : VertexIndex) : App6 :=
  t[45 * a.ℓ.val + 15 * a.i.val + a.k.val]!

lemma apps6Get_apps6 (g : Fam2) (a : VertexIndex) :
    apps6Get (apps6 g) a = app6 g (pythonVertexA a) := by
  obtain ⟨ka, ℓa, ia⟩ := a
  have h1 := ℓa.isLt
  have h2 := ia.isLt
  have h3 := ka.isLt
  have hlt : 45 * ℓa.val + 15 * ia.val + ka.val < (apps6 g).length := by
    rw [apps6, List.length_ofFn]; omega
  have f1 : (45 * ℓa.val + 15 * ia.val + ka.val) % 15 = ka.val := by omega
  have f2 : (45 * ℓa.val + 15 * ia.val + ka.val) / 45 = ℓa.val := by omega
  have f3 : (45 * ℓa.val + 15 * ia.val + ka.val) / 15 % 3 = ia.val := by omega
  show (apps6 g)[45 * ℓa.val + 15 * ia.val + ka.val]! = _
  rw [getElem!_pos (apps6 g) _ hlt]
  simp only [apps6, List.getElem_ofFn, ofFlat, f1, f2, f3, Fin.eta]

private lemma dot2_eq (u w : Fin 2 → ℚ) : u ⬝ᵥ w = u 0 * w 0 + u 1 * w 1 := by
  simp [dotProduct, Fin.sum_univ_two]

private lemma sub_a0 (x y : App6) : (x.sub y).a0 = x.a0 - y.a0 := rfl
private lemma sub_a1 (x y : App6) : (x.sub y).a1 = x.a1 - y.a1 := rfl

/-- Hoisted `Bε₂ℚ` check at `pythonVertexA` and `sqrtApprox16.upper_sqrt`:
trig once per pose, family entries once, applied families once per vertex
(`apps6`), applied differences by linearity. -/
def beCheck (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (εθ εφ δ r : ℚ) : Bool :=
  let g := fam2 p.θ₂ p.φ₂
  let t := apps6 g
  (List.finRange 3).all fun i =>
    let Qk := Qi i
    let qv := apps6Get t Qk
    let u := pythonVertexA Qk
    let D1 := sqrtApprox16.upper_sqrt.f (qv.a0 * qv.a0 + qv.a1 * qv.a1) + 3 * κℚ
      + dRotMs sqrtApprox16.upper_sqrt (3 * κℚ) qv εθ εφ 1
    decide <| ∀ k : VertexIndex, k ≠ Qk →
      let vk := apps6Get t k
      let w := pythonVertexA k
      let dq := qv.sub vk
      let nrm := sqrtApprox16.upper_sqrt.f ((u 0 - w 0) * (u 0 - w 0)
        + (u 1 - w 1) * (u 1 - w 1) + (u 2 - w 2) * (u 2 - w 2)) + 2 * κℚ
      let num := (qv.a0 * dq.a0 + qv.a1 * dq.a1) - 9 * κℚ
        - dProd1 (9 * κℚ) qv dq εθ εφ nrm
      let D2 := sqrtApprox16.upper_sqrt.f (dq.a0 * dq.a0 + dq.a1 * dq.a1) + 5 * κℚ
        + dRotMs sqrtApprox16.upper_sqrt (5 * κℚ) dq εθ εφ nrm
      0 < num ∧ δ / r < num / (D1 * D2)

theorem beCheck_iff (Qi : Fin 3 → VertexIndex) (p : Pose ℚ) (εθ εφ δ r : ℚ) :
    beCheck Qi p εθ εφ δ r = true ↔
      Local.TriangleQ.Bε₂ℚ Qi pythonVertexA p εθ εφ δ r sqrtApprox16.upper_sqrt := by
  unfold beCheck Local.TriangleQ.Bε₂ℚ RationalApprox.Bε₂ℚlhs RationalApprox.Bε₂ℚnum
    RationalApprox.dqNrm ΔrotMℚ ΔrotMℚ₂
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]
  refine forall_congr' fun i => ?_
  refine forall_congr' fun k => ?_
  refine imp_congr_right fun _ => ?_
  simp only [apps6Get_apps6, dRotMs_eq, dProd1_eq, norm2_eq, norm3_eq, dot2_eq,
    Matrix.mulVec_sub, Pi.sub_apply, app6_sub, sub_a0, sub_a1,
    ← app6_a0, ← app6_a1]

instance (priority := high) instDecidableBε₂ℚ (Qi : Fin 3 → VertexIndex)
    (p : Pose ℚ) (εθ εφ δ r : ℚ) :
    Decidable (Local.TriangleQ.Bε₂ℚ Qi pythonVertexA p εθ εφ δ r
      sqrtApprox16.upper_sqrt) :=
  decidable_of_iff _ (beCheck_iff Qi p εθ εφ δ r)

end Local2Fast

end Noperthedron.Solution
end
