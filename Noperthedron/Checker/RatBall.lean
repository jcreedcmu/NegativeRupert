module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic

@[expose] public section


/-!
# Rational center-radius arithmetic

`RatBall` is a proof-free computational enclosure.  Its operations are used
by generated certificate rows, while the theorems below prove once and for
all that their rational radii enclose the corresponding real expressions.
-/

namespace Noperthedron.Checker

structure RatBall where
  center : ℚ
  radius : ℚ
deriving DecidableEq, Repr

namespace RatBall

def Holds (b : RatBall) (x : ℝ) : Prop :=
  |x - (b.center : ℝ)| ≤ (b.radius : ℝ)

def const (q : ℚ) : RatBall := ⟨q, 0⟩

def add (a b : RatBall) : RatBall :=
  ⟨a.center + b.center, a.radius + b.radius⟩

def neg (a : RatBall) : RatBall := ⟨-a.center, a.radius⟩

def sub (a b : RatBall) : RatBall := add a (neg b)

def scale (q : ℚ) (a : RatBall) : RatBall :=
  ⟨q * a.center, |q| * a.radius⟩

/-- Standard first-order product enclosure with the quadratic remainder. -/
def mul (a b : RatBall) : RatBall :=
  ⟨a.center * b.center,
    |a.center| * b.radius + a.radius * |b.center| + a.radius * b.radius⟩

def ofEndpoints (lo hi : ℚ) : RatBall :=
  ⟨(lo + hi) / 2, (hi - lo) / 2⟩

/-- The canonical centered unit interval used after affine recentering. -/
def unit : RatBall := ⟨0, 1⟩

/-! The enclosure operations form additive and multiplicative commutative
monoids (but deliberately not a semiring: interval multiplication does not
distribute over the widened addition operation).  These instances let
finite polynomial supports use the canonical `Finset` folds. -/

instance instZero : Zero RatBall := ⟨const 0⟩
instance instOne : One RatBall := ⟨const 1⟩
instance instAdd : Add RatBall := ⟨add⟩
instance instMul : Mul RatBall := ⟨mul⟩

theorem ext {a b : RatBall} (hc : a.center = b.center)
    (hr : a.radius = b.radius) : a = b := by
  cases a
  cases b
  simp_all

@[simp] theorem zero_center : (0 : RatBall).center = 0 := rfl
@[simp] theorem zero_radius : (0 : RatBall).radius = 0 := rfl
@[simp] theorem one_center : (1 : RatBall).center = 1 := rfl
@[simp] theorem one_radius : (1 : RatBall).radius = 0 := rfl
@[simp] theorem add_center (a b : RatBall) :
    (a + b).center = a.center + b.center := rfl
@[simp] theorem add_radius (a b : RatBall) :
    (a + b).radius = a.radius + b.radius := rfl
@[simp] theorem mul_center (a b : RatBall) :
    (a * b).center = a.center * b.center := rfl
@[simp] theorem mul_radius (a b : RatBall) :
    (a * b).radius = |a.center| * b.radius +
      a.radius * |b.center| + a.radius * b.radius := rfl

instance instAddCommMonoid : AddCommMonoid RatBall where
  add := add
  add_assoc := by intro a b c; apply ext <;> simp <;> ring
  zero := const 0
  zero_add := by intro a; apply ext <;> simp
  add_zero := by intro a; apply ext <;> simp
  nsmul := nsmulRec
  nsmul_zero := by intro; rfl
  nsmul_succ := by intro n a; rfl
  add_comm := by intro a b; apply ext <;> simp <;> ring

instance instCommMonoid : CommMonoid RatBall where
  mul := mul
  mul_assoc := by intro a b c; apply ext <;> simp [abs_mul] <;> ring
  one := const 1
  one_mul := by intro a; apply ext <;> simp
  mul_one := by intro a; apply ext <;> simp
  npow := npowRec
  npow_zero := by intro; rfl
  npow_succ := by intro n a; rfl
  mul_comm := by intro a b; apply ext <;> simp <;> ring

@[simp] theorem const_center (q : ℚ) : (const q).center = q := rfl
@[simp] theorem const_radius (q : ℚ) : (const q).radius = 0 := rfl

theorem holds_const (q : ℚ) : (const q).Holds (q : ℝ) := by
  simp [Holds, const]

theorem holds_add {a b : RatBall} {x y : ℝ}
    (hx : a.Holds x) (hy : b.Holds y) :
    (add a b).Holds (x + y) := by
  unfold Holds at hx hy ⊢
  unfold add
  push_cast at hx hy ⊢
  have hrewrite :
      x + y - ((a.center : ℝ) + (b.center : ℝ)) =
        (x - (a.center : ℝ)) + (y - (b.center : ℝ)) := by ring
  rw [hrewrite]
  exact (abs_add_le _ _).trans (add_le_add hx hy)

theorem holds_neg {a : RatBall} {x : ℝ} (hx : a.Holds x) :
    (neg a).Holds (-x) := by
  unfold Holds at hx ⊢
  unfold neg
  push_cast at hx ⊢
  rw [show -x - -(a.center : ℝ) = -(x - (a.center : ℝ)) by ring,
    abs_neg]
  exact hx

theorem holds_sub {a b : RatBall} {x y : ℝ}
    (hx : a.Holds x) (hy : b.Holds y) :
    (sub a b).Holds (x - y) := by
  simpa only [sub, sub_eq_add_neg] using holds_add hx (holds_neg hy)

theorem holds_scale (q : ℚ) {a : RatBall} {x : ℝ}
    (hx : a.Holds x) : (scale q a).Holds ((q : ℝ) * x) := by
  unfold Holds at hx ⊢
  unfold scale
  push_cast at hx ⊢
  rw [show (q : ℝ) * x - (q : ℝ) * (a.center : ℝ) =
      (q : ℝ) * (x - (a.center : ℝ)) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_left hx (abs_nonneg (q : ℝ))

theorem holds_mul {a b : RatBall} {x y : ℝ}
    (hx : a.Holds x) (hy : b.Holds y) :
    (mul a b).Holds (x * y) := by
  unfold Holds at hx hy ⊢
  unfold mul
  push_cast at hx hy ⊢
  let dx := x - (a.center : ℝ)
  let dy := y - (b.center : ℝ)
  have hdecomp :
      x * y - (a.center : ℝ) * (b.center : ℝ) =
        (a.center : ℝ) * dy + dx * (b.center : ℝ) + dx * dy := by
    dsimp only [dx, dy]
    ring
  rw [hdecomp]
  calc
    |(a.center : ℝ) * dy + dx * (b.center : ℝ) + dx * dy| ≤
        |(a.center : ℝ) * dy| + |dx * (b.center : ℝ)| + |dx * dy| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ = |(a.center : ℝ)| * |dy| + |dx| * |(b.center : ℝ)| +
        |dx| * |dy| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |(a.center : ℝ)| * (b.radius : ℝ) +
        (a.radius : ℝ) * |(b.center : ℝ)| +
          (a.radius : ℝ) * (b.radius : ℝ) := by
      have hra : 0 ≤ (a.radius : ℝ) := (abs_nonneg dx).trans hx
      have hrb : 0 ≤ (b.radius : ℝ) := (abs_nonneg dy).trans hy
      gcongr

theorem holds_pow {a : RatBall} {x : ℝ} (h : a.Holds x) :
    ∀ n : ℕ, (a ^ n).Holds (x ^ n)
  | 0 => by simp [Holds]
  | n + 1 => by
      rw [pow_succ, pow_succ]
      exact holds_mul (holds_pow h n) h

theorem holds_finset_sum {ι : Type} {s : Finset ι}
    {a : ι → RatBall} {x : ι → ℝ}
    (h : ∀ i ∈ s, (a i).Holds (x i)) :
    (∑ i ∈ s, a i).Holds (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Holds]
  | @insert i s hi ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at h
      simp only [Finset.sum_insert hi]
      exact holds_add h.1 (ih h.2)

theorem holds_finset_prod {ι : Type} {s : Finset ι}
    {a : ι → RatBall} {x : ι → ℝ}
    (h : ∀ i ∈ s, (a i).Holds (x i)) :
    (∏ i ∈ s, a i).Holds (∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Holds]
  | @insert i s hi ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at h
      simp only [Finset.prod_insert hi]
      exact holds_mul h.1 (ih h.2)

theorem holds_of_mem_Icc {lo hi : ℚ} {x : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ)) :
    (ofEndpoints lo hi).Holds x := by
  unfold Holds ofEndpoints
  push_cast
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem lower_le_of_holds {b : RatBall} {x : ℝ} (h : b.Holds x) :
    (b.center - b.radius : ℚ) ≤ x := by
  unfold Holds at h
  push_cast
  rw [abs_le] at h
  linarith

theorem le_upper_of_holds {b : RatBall} {x : ℝ} (h : b.Holds x) :
    x ≤ (b.center + b.radius : ℚ) := by
  unfold Holds at h
  push_cast
  rw [abs_le] at h
  linarith

theorem nonneg_of_holds_of_lower_nonneg {b : RatBall} {x : ℝ}
    (h : b.Holds x) (hnonneg : 0 ≤ b.center - b.radius) : 0 ≤ x := by
  have hnonnegReal : (0 : ℝ) ≤ (b.center - b.radius : ℚ) := by
    exact_mod_cast hnonneg
  exact hnonnegReal.trans (lower_le_of_holds h)

/-- Every value enclosed by a center-radius ball has a normalized coordinate
in `[-1,1]`.  This is the semantic bridge for exact polynomial recentering. -/
theorem exists_normalized_of_holds {b : RatBall} {x : ℝ} (h : b.Holds x) :
    ∃ y : ℝ, unit.Holds y ∧
      x = (b.center : ℝ) + (b.radius : ℝ) * y := by
  by_cases hr : b.radius = 0
  · refine ⟨0, ?_, ?_⟩
    · simp [unit, Holds]
    · unfold Holds at h
      rw [hr] at h
      norm_num at h ⊢
      linarith
  · have hrnonnegReal : (0 : ℝ) ≤ (b.radius : ℚ) := by
      exact (abs_nonneg (x - (b.center : ℝ))).trans h
    have hrnonnegQ : (0 : ℚ) ≤ b.radius := by
      exact_mod_cast hrnonnegReal
    have hrposQ : 0 < b.radius := lt_of_le_of_ne hrnonnegQ (Ne.symm hr)
    have hrpos : (0 : ℝ) < (b.radius : ℚ) := by exact_mod_cast hrposQ
    refine ⟨(x - (b.center : ℝ)) / (b.radius : ℝ), ?_, ?_⟩
    · unfold unit Holds
      norm_num
      rw [abs_div]
      simpa [abs_of_pos hrpos] using (div_le_one hrpos).mpr h
    · field_simp
      ring

theorem pos_of_holds_of_lower_pos {b : RatBall} {x : ℝ}
    (h : b.Holds x) (hpos : 0 < b.center - b.radius) : 0 < x := by
  have hlower := lower_le_of_holds h
  exact lt_of_lt_of_le (by exact_mod_cast hpos) hlower

end RatBall

end Noperthedron.Checker

end
