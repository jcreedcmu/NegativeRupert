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

theorem pos_of_holds_of_lower_pos {b : RatBall} {x : ℝ}
    (h : b.Holds x) (hpos : 0 < b.center - b.radius) : 0 < x := by
  have hlower := lower_le_of_holds h
  exact lt_of_lt_of_le (by exact_mod_cast hpos) hlower

end RatBall

end Noperthedron.Checker

end
