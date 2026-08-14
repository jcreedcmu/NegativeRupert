module

public import Noperthedron.Basic
public import Noperthedron.Pose
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


namespace RationalApprox

noncomputable section

/- The below definitions are [SY25] Definition 37 -/

open scoped Nat -- for ! notation
/--
Sine partial sum $x - x^3/3! + x^5/5! - ⋯$ up to and including the degree $2n-1$ term.
-/
def sin_psum {k : Type} [Field k] (n : ℕ) (x : k) : k :=
  ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)!)

/--
Cosine partial sum $1 - x^2/2! + x^4/4! - ⋯$ up to and including the degree $2n-2$ degree term.
-/
def cos_psum {k : Type} [Field k] (n : ℕ) (x : k) : k :=
  ∑ i ∈ Finset.range n, (-1) ^ i * (x ^ (2 * i) / (2 * i)!)

/--
Round down to a multiple of `10⁻¹³`. Applied to the trig partial sums so that
the checker's rational arithmetic runs on small denominators (the raw partial
sums have denominators around `10²¹²`, making every downstream `ℚ` operation
a large-integer gcd). The rounding error is absorbed into the `κ/7` trig
budget of `sinℚ_approx'`/`cosℚ_approx'`. Defined via `Int.floor` so that it
commutes with the cast `ℚ → ℝ` (`Rat.floor_cast`). -/
def round13 {k : Type} [Field k] [LinearOrder k] [FloorRing k] (x : k) : k :=
  ⌊x * 10 ^ 13⌋ / 10 ^ 13

lemma abs_round13_sub_le {k : Type} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    [FloorRing k] (x : k) : |round13 x - x| ≤ 1 / 10 ^ 13 := by
  have h10 : (0 : k) < 10 ^ 13 := by positivity
  have h1 : ((⌊x * 10 ^ 13⌋ : ℤ) : k) ≤ x * 10 ^ 13 := Int.floor_le _
  have h2 : x * 10 ^ 13 < ((⌊x * 10 ^ 13⌋ : ℤ) : k) + 1 := Int.lt_floor_add_one _
  have hrw : round13 x - x = (((⌊x * 10 ^ 13⌋ : ℤ) : k) - x * 10 ^ 13) / 10 ^ 13 := by
    unfold round13; field_simp
  rw [hrw, abs_div, abs_of_pos h10]
  gcongr
  rw [abs_le]
  constructor <;> linarith

/-- Componentwise `round13`: round each coordinate of a vector down to a
multiple of `10⁻¹³`. Applied to the per-pose hoisted vectors of the global
and local checkers so that the per-vertex dot products run on small
denominators; the rounding error is absorbed into the `κ` budgets.

NOTE: like every `Fin n → k` value, this is a closure, so each access
re-rounds. The checkers' hot loops must read each component once into a
scalar `let` or structure field (see `HScalars` in RationalGlobal.lean). -/
def round13v {k : Type} [Field k] [LinearOrder k] [FloorRing k] {n : ℕ}
    (v : Fin n → k) : Fin n → k :=
  fun i => round13 (v i)

/-- Rounding the left vector of a dot product perturbs it by at most
`(∑ i, |P i|) / 10¹³`. -/
lemma abs_round13v_dot_sub_le {k : Type} [Field k] [LinearOrder k]
    [IsStrictOrderedRing k] [FloorRing k] {n : ℕ} (v P : Fin n → k) :
    |round13v v ⬝ᵥ P - v ⬝ᵥ P| ≤ (∑ i, |P i|) / 10 ^ 13 := by
  have h : round13v v ⬝ᵥ P - v ⬝ᵥ P = ∑ i, (round13 (v i) - v i) * P i := by
    simp only [dotProduct, round13v, ← Finset.sum_sub_distrib, sub_mul]
  rw [h, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  calc |round13 (v i) - v i| * |P i|
      ≤ (1 / 10 ^ 13) * |P i| :=
        mul_le_mul_of_nonneg_right (abs_round13_sub_le _) (abs_nonneg _)
    _ = |P i| / 10 ^ 13 := by ring

/-- Rounding both vectors of a dot product perturbs it by at most
`(∑ i, |round13v u₂ i| + ∑ i, |u₁ i|) / 10¹³`. -/
lemma abs_round13v_dot_round13v_sub_le {k : Type} [Field k] [LinearOrder k]
    [IsStrictOrderedRing k] [FloorRing k] {n : ℕ} (u₁ u₂ : Fin n → k) :
    |round13v u₁ ⬝ᵥ round13v u₂ - u₁ ⬝ᵥ u₂| ≤
      ((∑ i, |round13v u₂ i|) + ∑ i, |u₁ i|) / 10 ^ 13 := by
  have h1 := abs_round13v_dot_sub_le u₁ (round13v u₂)
  have h2 : |u₁ ⬝ᵥ round13v u₂ - u₁ ⬝ᵥ u₂| ≤ (∑ i, |u₁ i|) / 10 ^ 13 := by
    rw [dotProduct_comm u₁ (round13v u₂), dotProduct_comm u₁ u₂]
    exact abs_round13v_dot_sub_le u₂ u₁
  calc |round13v u₁ ⬝ᵥ round13v u₂ - u₁ ⬝ᵥ u₂|
      = |(round13v u₁ ⬝ᵥ round13v u₂ - u₁ ⬝ᵥ round13v u₂) +
          (u₁ ⬝ᵥ round13v u₂ - u₁ ⬝ᵥ u₂)| := by congr 1; ring
    _ ≤ |round13v u₁ ⬝ᵥ round13v u₂ - u₁ ⬝ᵥ round13v u₂| +
        |u₁ ⬝ᵥ round13v u₂ - u₁ ⬝ᵥ u₂| := abs_add_le _ _
    _ ≤ (∑ i, |round13v u₂ i|) / 10 ^ 13 + (∑ i, |u₁ i|) / 10 ^ 13 := add_le_add h1 h2
    _ = ((∑ i, |round13v u₂ i|) + ∑ i, |u₁ i|) / 10 ^ 13 := by ring

/--
Sine partial sum $x - x^3/3! + x^5/5! - ⋯ + x^{25}/25!$, rounded down to a
multiple of `10⁻¹³` (see `round13`).
-/
def sinℚ {k : Type} [Field k] [LinearOrder k] [FloorRing k] (x : k) : k :=
  round13 (sin_psum 13 x)

lemma sinℚ_match (x : ℚ) : sinℚ (k := ℚ) x = sinℚ (k := ℝ) x := by
  have h : ((sin_psum 13 x : ℚ) : ℝ) = sin_psum 13 (x : ℝ) := by
    unfold sin_psum; push_cast; rfl
  unfold sinℚ round13
  rw [← h]
  norm_cast

/--
Cosine partial sum $1 - x^2/2! + x^4/4! - ⋯ + x^{24}/24!$, rounded down to a
multiple of `10⁻¹³` (see `round13`).
-/
def cosℚ {k : Type} [Field k] [LinearOrder k] [FloorRing k] (x : k) : k :=
  round13 (cos_psum 13 x)

lemma cosℚ_match (x : ℚ) : cosℚ (k := ℚ) x = cosℚ (k := ℝ) x := by
  have h : ((cos_psum 13 x : ℚ) : ℝ) = cos_psum 13 (x : ℝ) := by
    unfold cos_psum; push_cast; rfl
  unfold cosℚ round13
  rw [← h]
  norm_cast

/--
Frequently used constant for controlling the degree of approximation
of rational versions to real counterparts.
-/
def κℚ : ℚ := 1 / 10^10
def κ : ℝ := 1 / 10^10

/--
  A real polyhedron A and a rational polyhedron B that is a κ-approximation of A.
-/
structure κApproxPoly {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : Polyhedron ι₁ ℝ³) (B : Polyhedron ι₂ (Fin 3 → ℚ)) where
  bijection : ι₁ ≃ ι₂
  approx : ∀ a : ι₁, ‖(A.v a : ℝ³) - toR3 (B.v (bijection a))‖ ≤ κ

end

def rotMℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![-sinℚ θ, cosℚ θ, 0; -cosℚ θ * cosℚ φ, -sinℚ θ * cosℚ φ, sinℚ φ]

def rotMθℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![-cosℚ θ, -sinℚ θ, 0; sinℚ θ * cosℚ φ, -cosℚ θ * cosℚ φ, 0]

def rotMφℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![0, 0, 0; cosℚ θ * sinℚ φ, sinℚ θ * sinℚ φ, cosℚ φ]

def rotMθθℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![sinℚ θ, -cosℚ θ, 0; cosℚ θ * cosℚ φ, sinℚ θ * cosℚ φ, 0]

def rotMθφℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![0, 0, 0; -sinℚ θ * sinℚ φ, cosℚ θ * sinℚ φ, 0]

def rotMφφℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (θ : k) (φ : k) : Matrix (Fin 2) (Fin 3) k :=
  !![0, 0, 0; cosℚ θ * cosℚ φ, sinℚ θ * cosℚ φ, -sinℚ φ]

def rotRℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (α : k) : Matrix (Fin 2) (Fin 2) k :=
  !![cosℚ α, -sinℚ α;
     sinℚ α,  cosℚ α]

def rotR'ℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (α : k) : Matrix (Fin 2) (Fin 2) k :=
  !![-sinℚ α, -cosℚ α;
     cosℚ α,  -sinℚ α]

def vecXℚ_mat {k : Type} [Field k] [LinearOrder k] [FloorRing k] (θ : k) (φ : k) : Matrix (Fin 3) (Fin 1) k :=
  !![ cosℚ θ * sinℚ φ; sinℚ θ * sinℚ φ; cosℚ φ ]

/-
These are merely linear instead of continuous-linear because
.toContinuousLinearMap only works on Cauchy-complete spaces.
-/

def rotMℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMℚ_mat θ φ |>.toLin'

def rotMθℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMθℚ_mat θ φ |>.toLin'

def rotMφℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMφℚ_mat θ φ |>.toLin'

def rotMθθℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMθθℚ_mat θ φ |>.toLin'

def rotMθφℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMθφℚ_mat θ φ |>.toLin'

def rotMφφℚ (θ φ : ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotMφφℚ_mat θ φ |>.toLin'

def rotRℚ (α : ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotRℚ_mat α |>.toLin'

def rotR'ℚ (α : ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  rotR'ℚ_mat α |>.toLin'

def vecXℚ (θ : ℚ) (φ : ℚ) : (Fin 3 → ℚ) :=
  ![ cosℚ θ * sinℚ φ, sinℚ θ * sinℚ φ, cosℚ φ ]

def _root_.Pose.rotRℚ (p : Pose ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := _root_.RationalApprox.rotRℚ p.α

def _root_.Pose.rotR'ℚ (p : Pose ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := _root_.RationalApprox.rotR'ℚ p.α

def _root_.Pose.rotM₁ℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂ℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMℚ p.θ₂ p.φ₂

def _root_.Pose.rotM₁θℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMθℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂θℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMθℚ p.θ₂ p.φ₂

def _root_.Pose.rotM₁φℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMφℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂φℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMφℚ p.θ₂ p.φ₂

def _root_.Pose.rotM₁θθℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMθθℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂θθℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMθθℚ p.θ₂ p.φ₂

def _root_.Pose.rotM₁θφℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMθφℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂θφℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMθφℚ p.θ₂ p.φ₂

def _root_.Pose.rotM₁φφℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMφφℚ p.θ₁ p.φ₁

def _root_.Pose.rotM₂φφℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) :=
  _root_.RationalApprox.rotMφφℚ p.θ₂ p.φ₂

/-- `rotM₂ℚ` with the resulting 2-vector rounded down componentwise to
multiples of `10⁻¹³` (see `round13v`). Used by the local certificate `Bεℚ` so
that its per-vertex-pair dot products and `UpperSqrt` norms run on small
denominators; the rounding error is absorbed into the `κ` budgets of
`bounds_kappa4`. -/
def _root_.Pose.rotM₂Rℚ (p : Pose ℚ) (v : Fin 3 → ℚ) : Fin 2 → ℚ :=
  round13v (p.rotM₂ℚ v)

def _root_.Pose.innerℚ (p : Pose ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := p.rotRℚ ∘ₗ p.rotM₁ℚ
def _root_.Pose.vecX₁ℚ (p : Pose ℚ) : (Fin 3 → ℚ) := vecXℚ (p.θ₁) (p.φ₁)
def _root_.Pose.vecX₂ℚ (p : Pose ℚ) : (Fin 3 → ℚ) := vecXℚ (p.θ₂) (p.φ₂)

noncomputable
def rotMℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotMθℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMθℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotMφℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMφℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotMθθℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMθθℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotMθφℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMθφℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotMφφℚℝ (θ φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotMφφℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotRℚℝ (α : ℝ) : ℝ² →L[ℝ] ℝ² :=
  rotRℚ_mat α |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def rotR'ℚℝ (α : ℝ) : ℝ² →L[ℝ] ℝ² :=
  rotR'ℚ_mat α |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def vecXLℚℝ (θ φ : ℝ) : Euc(1) →L[ℝ] ℝ³ :=
  vecXℚ_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def vecXℚℝ (θ : ℝ) (φ : ℝ) : ℝ³ :=
  !₂[ cosℚ θ * sinℚ φ, sinℚ θ * sinℚ φ, cosℚ φ ]

noncomputable section
def _root_.Pose.rotRℚℝ (p : Pose ℝ) : ℝ² →L[ℝ] ℝ² := _root_.RationalApprox.rotRℚℝ p.α
def _root_.Pose.rotM₁ℚℝ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := _root_.RationalApprox.rotMℚℝ p.θ₁ p.φ₁
def _root_.Pose.rotM₂ℚℝ (p : Pose ℝ) : ℝ³ →L[ℝ] ℝ² := _root_.RationalApprox.rotMℚℝ p.θ₂ p.φ₂
end

/-! ## Fixed-scale integer-cast helpers

Shared by the `Nat` fast paths (`RationalApprox/GlobalNat.lean`,
`Checker/LocalNat.lean`, `Checker/LocalFastNat.lean`): casts between the
checkers' fixed-scale integer numerators and the ℚ reference values. -/

/-- `|·|` through a scale-`10ᵏ` integer fraction. -/
theorem abs_intCast_div_pow (k : ℕ) (n : ℤ) :
    |(n : ℚ) / 10 ^ k| = ((|n| : ℤ) : ℚ) / 10 ^ k := by
  rw [abs_div, abs_of_pos (by positivity : (0:ℚ) < (10:ℚ) ^ k)]
  push_cast
  ring_nf

/-- `round13` of an integer fraction over `10¹³·D` is integer division by `D`
(at scale `10¹³`). -/
theorem round13_intCast_div (A : ℤ) (D : ℕ) :
    round13 ((A : ℚ) / (10 ^ 13 * (D : ℚ))) = ((A / (D : ℤ) : ℤ) : ℚ) / 10 ^ 13 := by
  have hfl : ⌊(A : ℚ) / (10 ^ 13 * (D : ℚ)) * 10 ^ 13⌋ = A / (D : ℤ) := by
    rw [show (A : ℚ) / (10 ^ 13 * (D : ℚ)) * 10 ^ 13 = (A : ℚ) / ((D : ℕ) : ℚ) from by
          rw [div_mul_eq_mul_div, mul_comm (A : ℚ) ((10:ℚ) ^ 13),
            mul_div_mul_left _ _ (by norm_num : ((10:ℚ) ^ 13) ≠ 0)],
      Rat.floor_intCast_div_natCast]
  unfold round13
  rw [hfl]

/-- The raw `cond`/`ble`/`sub` form of `Int.natAbs (x - c)` used by the
`Nat` tier loops. -/
theorem cond_ble_sub_cast (x c : ℕ) :
    ((cond (Nat.ble x c) (c - x) (x - c) : ℕ) : ℤ) = |(x : ℤ) - c| := by
  rcases hb : Nat.ble x c with _ | _
  · have h : ¬ x ≤ c := fun hle => by
      rw [Nat.ble_eq_true_of_le hle] at hb
      exact Bool.noConfusion hb
    rw [cond_false, abs_of_nonneg (by omega : (0:ℤ) ≤ (x:ℤ) - c)]
    omega
  · have h : x ≤ c := Nat.ble_eq ▸ hb
    rw [cond_true, abs_sub_comm, abs_of_nonneg (by omega : (0:ℤ) ≤ (c:ℤ) - x)]
    omega

structure UpperSqrt where
  f : ℚ → ℚ
  bound : ∀ (x : ℚ), 0 ≤ x → √x ≤ f x

def UpperSqrt.norm {n : ℕ} (s : UpperSqrt) (v : Fin n → ℚ) : ℚ := s.f (v ⬝ᵥ v)

structure LowerSqrt where
  f : ℚ → ℚ
  bound : ∀ (x : ℚ), 0 ≤ x → f x ≤ √x

def LowerSqrt.norm {n : ℕ} (s : LowerSqrt) (v : Fin n → ℚ) : ℚ := s.f (v ⬝ᵥ v)

structure Approx where
  lower_sqrt : LowerSqrt
  upper_sqrt : UpperSqrt
  upper_sqrt_two : ℚ
  upper_sqrt_two_gt_sqrt_two : upper_sqrt_two > √2
  upper_sqrt_five : ℚ
  upper_sqrt_five_gt_sqrt_five : upper_sqrt_five > √5

end RationalApprox

end
