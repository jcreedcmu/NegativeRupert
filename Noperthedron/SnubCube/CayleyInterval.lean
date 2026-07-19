module

public import Noperthedron.Checker.RatBall
public import Noperthedron.SnubCube.CayleyPose

@[expose] public section


/-!
# Rational boxes for five-parameter Cayley poses
-/

namespace Noperthedron.SnubCube

@[reducible]
def CayleyInterval (R : Type) [PartialOrder R] : Type :=
  NonemptyInterval (CayleyPose R)

namespace CayleyPose

def get {R : Type} (p : CayleyPose R) (i : Fin 5) : R := equivPi p i

@[simp] theorem get_zero {R : Type} (p : CayleyPose R) : p.get 0 = p.θ := rfl
@[simp] theorem get_one {R : Type} (p : CayleyPose R) : p.get 1 = p.φ := rfl
@[simp] theorem get_two {R : Type} (p : CayleyPose R) : p.get 2 = p.x := rfl
@[simp] theorem get_three {R : Type} (p : CayleyPose R) : p.get 3 = p.y := rfl
@[simp] theorem get_four {R : Type} (p : CayleyPose R) : p.get 4 = p.z := rfl

theorem le_iff_forall_get {R : Type} [PartialOrder R]
    (p q : CayleyPose R) : p ≤ q ↔ ∀ i, p.get i ≤ q.get i := by
  rw [le_iff]
  constructor
  · rintro ⟨hθ, hφ, hx, hy, hz⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4⟩

@[simp] theorem toReal_get (p : CayleyPose ℚ) (i : Fin 5) :
    p.toReal.get i = (p.get i : ℝ) := by
  fin_cases i <;> rfl

end CayleyPose

namespace CayleyInterval

abbrev mk {R : Type} [PartialOrder R]
    (min max : CayleyPose R) (h : min ≤ max) : CayleyInterval R :=
  NonemptyInterval.mk ⟨min, max⟩ h

abbrev min {R : Type} [PartialOrder R] (iv : CayleyInterval R) :
    CayleyPose R := iv.fst

abbrev max {R : Type} [PartialOrder R] (iv : CayleyInterval R) :
    CayleyPose R := iv.snd

abbrev min_le_max {R : Type} [PartialOrder R] (iv : CayleyInterval R) :
    iv.min ≤ iv.max := iv.fst_le_snd

def toReal (iv : CayleyInterval ℚ) : CayleyInterval ℝ :=
  CayleyInterval.mk iv.min.toReal iv.max.toReal (by
    rw [CayleyPose.le_iff_forall_get]
    intro i
    rw [CayleyPose.toReal_get, CayleyPose.toReal_get]
    exact_mod_cast (CayleyPose.le_iff_forall_get _ _).mp iv.min_le_max i)

theorem mem_toReal_iff {p : CayleyPose ℝ} {iv : CayleyInterval ℚ} :
    p ∈ iv.toReal ↔ ∀ i : Fin 5,
      p.get i ∈ Set.Icc (iv.min.get i : ℝ) (iv.max.get i : ℝ) := by
  rw [NonemptyInterval.mem_def]
  simp only [CayleyPose.le_iff_forall_get, toReal,
    CayleyPose.toReal_get, Set.mem_Icc, ← forall_and]

def coordinateBall (iv : CayleyInterval ℚ) (i : Fin 5) :
    Checker.RatBall :=
  Checker.RatBall.ofEndpoints (iv.min.get i) (iv.max.get i)

theorem coordinateBall_holds {p : CayleyPose ℝ} {iv : CayleyInterval ℚ}
    (hp : p ∈ iv.toReal) (i : Fin 5) :
    (iv.coordinateBall i).Holds (p.get i) :=
  Checker.RatBall.holds_of_mem_Icc (mem_toReal_iff.mp hp i)

end CayleyInterval

end Noperthedron.SnubCube

end
