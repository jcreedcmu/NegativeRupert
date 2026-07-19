module

public import Noperthedron.Checker.RatPolynomial

@[expose] public section


/-!
# Normalized rational quadratics in three variables

Combining coefficients before interval evaluation preserves cancellations
that are lost in a large expression tree.  Soundness is inherited from
`RatPolynomial`: the quadratic is rewritten around the rational box center
and evaluated on zero-centered coordinate deviations.
-/

namespace Noperthedron.Checker

/-- Coefficients in the basis
`1, x, y, z, x², xy, xz, y², yz, z²`. -/
structure RatQuadratic3 where
  c0 : ℚ
  cx : ℚ
  cy : ℚ
  cz : ℚ
  cxx : ℚ
  cxy : ℚ
  cxz : ℚ
  cyy : ℚ
  cyz : ℚ
  czz : ℚ
deriving DecidableEq, Repr

namespace RatQuadratic3

def zero : RatQuadratic3 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def add (a b : RatQuadratic3) : RatQuadratic3 :=
  ⟨a.c0 + b.c0, a.cx + b.cx, a.cy + b.cy, a.cz + b.cz,
    a.cxx + b.cxx, a.cxy + b.cxy, a.cxz + b.cxz,
    a.cyy + b.cyy, a.cyz + b.cyz, a.czz + b.czz⟩

def neg (a : RatQuadratic3) : RatQuadratic3 :=
  ⟨-a.c0, -a.cx, -a.cy, -a.cz, -a.cxx,
    -a.cxy, -a.cxz, -a.cyy, -a.cyz, -a.czz⟩

def scale (q : ℚ) (a : RatQuadratic3) : RatQuadratic3 :=
  ⟨q * a.c0, q * a.cx, q * a.cy, q * a.cz, q * a.cxx,
    q * a.cxy, q * a.cxz, q * a.cyy, q * a.cyz, q * a.czz⟩

instance : Zero RatQuadratic3 := ⟨zero⟩
instance : Add RatQuadratic3 := ⟨add⟩
instance : Neg RatQuadratic3 := ⟨neg⟩
instance : Sub RatQuadratic3 := ⟨fun a b => add a (neg b)⟩

@[simp] theorem add_c0 (a b : RatQuadratic3) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_cx (a b : RatQuadratic3) : (a + b).cx = a.cx + b.cx := rfl
@[simp] theorem add_cy (a b : RatQuadratic3) : (a + b).cy = a.cy + b.cy := rfl
@[simp] theorem add_cz (a b : RatQuadratic3) : (a + b).cz = a.cz + b.cz := rfl
@[simp] theorem add_cxx (a b : RatQuadratic3) : (a + b).cxx = a.cxx + b.cxx := rfl
@[simp] theorem add_cxy (a b : RatQuadratic3) : (a + b).cxy = a.cxy + b.cxy := rfl
@[simp] theorem add_cxz (a b : RatQuadratic3) : (a + b).cxz = a.cxz + b.cxz := rfl
@[simp] theorem add_cyy (a b : RatQuadratic3) : (a + b).cyy = a.cyy + b.cyy := rfl
@[simp] theorem add_cyz (a b : RatQuadratic3) : (a + b).cyz = a.cyz + b.cyz := rfl
@[simp] theorem add_czz (a b : RatQuadratic3) : (a + b).czz = a.czz + b.czz := rfl

@[simp] theorem neg_c0 (a : RatQuadratic3) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_cx (a : RatQuadratic3) : (-a).cx = -a.cx := rfl
@[simp] theorem neg_cy (a : RatQuadratic3) : (-a).cy = -a.cy := rfl
@[simp] theorem neg_cz (a : RatQuadratic3) : (-a).cz = -a.cz := rfl
@[simp] theorem neg_cxx (a : RatQuadratic3) : (-a).cxx = -a.cxx := rfl
@[simp] theorem neg_cxy (a : RatQuadratic3) : (-a).cxy = -a.cxy := rfl
@[simp] theorem neg_cxz (a : RatQuadratic3) : (-a).cxz = -a.cxz := rfl
@[simp] theorem neg_cyy (a : RatQuadratic3) : (-a).cyy = -a.cyy := rfl
@[simp] theorem neg_cyz (a : RatQuadratic3) : (-a).cyz = -a.cyz := rfl
@[simp] theorem neg_czz (a : RatQuadratic3) : (-a).czz = -a.czz := rfl

@[simp] theorem sub_c0 (a b : RatQuadratic3) : (a - b).c0 = a.c0 - b.c0 := by change a.c0 + -b.c0 = _; ring
@[simp] theorem sub_cx (a b : RatQuadratic3) : (a - b).cx = a.cx - b.cx := by change a.cx + -b.cx = _; ring
@[simp] theorem sub_cy (a b : RatQuadratic3) : (a - b).cy = a.cy - b.cy := by change a.cy + -b.cy = _; ring
@[simp] theorem sub_cz (a b : RatQuadratic3) : (a - b).cz = a.cz - b.cz := by change a.cz + -b.cz = _; ring
@[simp] theorem sub_cxx (a b : RatQuadratic3) : (a - b).cxx = a.cxx - b.cxx := by change a.cxx + -b.cxx = _; ring
@[simp] theorem sub_cxy (a b : RatQuadratic3) : (a - b).cxy = a.cxy - b.cxy := by change a.cxy + -b.cxy = _; ring
@[simp] theorem sub_cxz (a b : RatQuadratic3) : (a - b).cxz = a.cxz - b.cxz := by change a.cxz + -b.cxz = _; ring
@[simp] theorem sub_cyy (a b : RatQuadratic3) : (a - b).cyy = a.cyy - b.cyy := by change a.cyy + -b.cyy = _; ring
@[simp] theorem sub_cyz (a b : RatQuadratic3) : (a - b).cyz = a.cyz - b.cyz := by change a.cyz + -b.cyz = _; ring
@[simp] theorem sub_czz (a b : RatQuadratic3) : (a - b).czz = a.czz - b.czz := by change a.czz + -b.czz = _; ring

@[simp] theorem scale_c0 (q : ℚ) (a : RatQuadratic3) : (scale q a).c0 = q*a.c0 := rfl
@[simp] theorem scale_cx (q : ℚ) (a : RatQuadratic3) : (scale q a).cx = q*a.cx := rfl
@[simp] theorem scale_cy (q : ℚ) (a : RatQuadratic3) : (scale q a).cy = q*a.cy := rfl
@[simp] theorem scale_cz (q : ℚ) (a : RatQuadratic3) : (scale q a).cz = q*a.cz := rfl
@[simp] theorem scale_cxx (q : ℚ) (a : RatQuadratic3) : (scale q a).cxx = q*a.cxx := rfl
@[simp] theorem scale_cxy (q : ℚ) (a : RatQuadratic3) : (scale q a).cxy = q*a.cxy := rfl
@[simp] theorem scale_cxz (q : ℚ) (a : RatQuadratic3) : (scale q a).cxz = q*a.cxz := rfl
@[simp] theorem scale_cyy (q : ℚ) (a : RatQuadratic3) : (scale q a).cyy = q*a.cyy := rfl
@[simp] theorem scale_cyz (q : ℚ) (a : RatQuadratic3) : (scale q a).cyz = q*a.cyz := rfl
@[simp] theorem scale_czz (q : ℚ) (a : RatQuadratic3) : (scale q a).czz = q*a.czz := rfl

def evalQ (q : RatQuadratic3) (x y z : ℚ) : ℚ :=
  q.c0 + q.cx*x + q.cy*y + q.cz*z + q.cxx*x*x +
    q.cxy*x*y + q.cxz*x*z + q.cyy*y*y + q.cyz*y*z + q.czz*z*z

def evalReal (q : RatQuadratic3) (x y z : ℝ) : ℝ :=
  q.c0 + q.cx*x + q.cy*y + q.cz*z + q.cxx*x*x +
    q.cxy*x*y + q.cxz*x*z + q.cyy*y*y + q.cyz*y*z + q.czz*z*z

@[simp] theorem evalReal_zero (x y z : ℝ) :
    zero.evalReal x y z = 0 := by
  simp [zero, evalReal]

@[simp] theorem evalReal_add (a b : RatQuadratic3) (x y z : ℝ) :
    (a + b).evalReal x y z = a.evalReal x y z + b.evalReal x y z := by
  change (add a b).evalReal x y z = _
  unfold add evalReal
  push_cast
  ring

@[simp] theorem evalReal_neg (a : RatQuadratic3) (x y z : ℝ) :
    (-a).evalReal x y z = -a.evalReal x y z := by
  change (neg a).evalReal x y z = _
  unfold neg evalReal
  push_cast
  ring

@[simp] theorem evalReal_sub (a b : RatQuadratic3) (x y z : ℝ) :
    (a - b).evalReal x y z = a.evalReal x y z - b.evalReal x y z := by
  change (add a (neg b)).evalReal x y z = _
  unfold add neg evalReal
  push_cast
  ring

@[simp] theorem evalReal_scale (q : ℚ) (a : RatQuadratic3) (x y z : ℝ) :
    (scale q a).evalReal x y z = (q : ℝ) * a.evalReal x y z := by
  unfold scale evalReal
  push_cast
  ring

/-- The same quadratic expanded in deviations from a rational center. -/
def centeredPolynomial (q : RatQuadratic3) (x y z : ℚ) : RatPolynomial 3 :=
  let dx : RatPolynomial 3 := .var 0 - .const x
  let dy : RatPolynomial 3 := .var 1 - .const y
  let dz : RatPolynomial 3 := .var 2 - .const z
  .const (q.evalQ x y z) +
    RatPolynomial.scale (q.cx + 2*q.cxx*x + q.cxy*y + q.cxz*z) dx +
    RatPolynomial.scale (q.cy + q.cxy*x + 2*q.cyy*y + q.cyz*z) dy +
    RatPolynomial.scale (q.cz + q.cxz*x + q.cyz*y + 2*q.czz*z) dz +
    RatPolynomial.scale q.cxx (dx*dx) +
    RatPolynomial.scale q.cxy (dx*dy) +
    RatPolynomial.scale q.cxz (dx*dz) +
    RatPolynomial.scale q.cyy (dy*dy) +
    RatPolynomial.scale q.cyz (dy*dz) +
    RatPolynomial.scale q.czz (dz*dz)

theorem eval_centeredPolynomial (q : RatQuadratic3) (x y z : ℚ)
    (xr yr zr : ℝ) :
    RatPolynomial.evalReal ![xr, yr, zr] (q.centeredPolynomial x y z) =
      q.evalReal xr yr zr := by
  simp only [centeredPolynomial, RatPolynomial.evalReal_add,
    RatPolynomial.evalReal_sub, RatPolynomial.evalReal_scale,
    RatPolynomial.evalReal]
  simp only [evalQ, evalReal]
  push_cast
  ring

/-- Cancellation-preserving center-radius evaluation. -/
def evalBall (vars : Fin 3 → RatBall) (q : RatQuadratic3) : RatBall :=
  RatPolynomial.evalBall vars
    (q.centeredPolynomial (vars 0).center
      (vars 1).center (vars 2).center)

theorem evalBall_holds {vars : Fin 3 → RatBall}
    {x y z : ℝ}
    (hvars : ∀ i, (vars i).Holds (![x, y, z] i))
    (q : RatQuadratic3) :
    (evalBall vars q).Holds (q.evalReal x y z) := by
  have h := RatPolynomial.evalBall_holds hvars
    (q.centeredPolynomial (vars 0).center
      (vars 1).center (vars 2).center)
  rw [q.eval_centeredPolynomial] at h
  exact h

end RatQuadratic3

end Noperthedron.Checker

end
