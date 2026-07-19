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

/-- Replace one of the five Cayley-pose coordinates. -/
def set {R : Type} (p : CayleyPose R) (i : Fin 5) (value : R) :
    CayleyPose R :=
  equivPi.symm (Function.update (equivPi p) i value)

@[simp] theorem get_set_same {R : Type} (p : CayleyPose R)
    (i : Fin 5) (value : R) :
    (p.set i value).get i = value := by
  simp [get, set]

@[simp] theorem get_set_of_ne {R : Type} (p : CayleyPose R)
    {i j : Fin 5} (value : R) (h : j ≠ i) :
    (p.set i value).get j = p.get j := by
  simp [get, set, h]

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

/-- Rational midpoint of one coordinate of a Cayley box. -/
def midpoint (iv : CayleyInterval ℚ) (i : Fin 5) : ℚ :=
  (iv.min.get i + iv.max.get i) / 2

private theorem min_le_midpoint (iv : CayleyInterval ℚ) (i : Fin 5) :
    iv.min.get i ≤ iv.midpoint i := by
  have h := (CayleyPose.le_iff_forall_get _ _).mp iv.min_le_max i
  simp only [midpoint]
  linarith

private theorem midpoint_le_max (iv : CayleyInterval ℚ) (i : Fin 5) :
    iv.midpoint i ≤ iv.max.get i := by
  have h := (CayleyPose.le_iff_forall_get _ _).mp iv.min_le_max i
  simp only [midpoint]
  linarith

/-- Lower closed half of a rational Cayley box along one coordinate. -/
def lowerHalf (iv : CayleyInterval ℚ) (i : Fin 5) : CayleyInterval ℚ :=
  CayleyInterval.mk iv.min (iv.max.set i (iv.midpoint i)) (by
    rw [CayleyPose.le_iff_forall_get]
    intro j
    by_cases h : j = i
    · subst j
      simpa using iv.min_le_midpoint i
    · simpa [CayleyPose.get_set_of_ne _ _ h] using
        (CayleyPose.le_iff_forall_get _ _).mp iv.min_le_max j)

/-- Upper closed half of a rational Cayley box along one coordinate. -/
def upperHalf (iv : CayleyInterval ℚ) (i : Fin 5) : CayleyInterval ℚ :=
  CayleyInterval.mk (iv.min.set i (iv.midpoint i)) iv.max (by
    rw [CayleyPose.le_iff_forall_get]
    intro j
    by_cases h : j = i
    · subst j
      simpa using iv.midpoint_le_max i
    · simpa [CayleyPose.get_set_of_ne _ _ h] using
        (CayleyPose.le_iff_forall_get _ _).mp iv.min_le_max j)

theorem mem_lowerHalf {p : CayleyPose ℝ} {iv : CayleyInterval ℚ}
    {i : Fin 5} (hp : p ∈ iv.toReal)
    (hi : p.get i ≤ (iv.midpoint i : ℝ)) :
    p ∈ (iv.lowerHalf i).toReal := by
  rw [mem_toReal_iff] at hp ⊢
  intro j
  by_cases h : j = i
  · subst j
    simpa only [lowerHalf, CayleyInterval.min, CayleyInterval.max,
      CayleyPose.get_set_same, Set.mem_Icc] using And.intro (hp i).1 hi
  · simpa [lowerHalf, CayleyPose.get_set_of_ne _ _ h] using hp j

theorem mem_upperHalf {p : CayleyPose ℝ} {iv : CayleyInterval ℚ}
    {i : Fin 5} (hp : p ∈ iv.toReal)
    (hi : (iv.midpoint i : ℝ) ≤ p.get i) :
    p ∈ (iv.upperHalf i).toReal := by
  rw [mem_toReal_iff] at hp ⊢
  intro j
  by_cases h : j = i
  · subst j
    simpa only [upperHalf, CayleyInterval.min, CayleyInterval.max,
      CayleyPose.get_set_same, Set.mem_Icc] using And.intro hi (hp i).2
  · simpa [upperHalf, CayleyPose.get_set_of_ne _ _ h] using hp j

/-- The two midpoint children cover their parent, including their shared
boundary. -/
theorem mem_imp_mem_lowerHalf_or_upperHalf {p : CayleyPose ℝ}
    {iv : CayleyInterval ℚ} (i : Fin 5) (hp : p ∈ iv.toReal) :
    p ∈ (iv.lowerHalf i).toReal ∨ p ∈ (iv.upperHalf i).toReal := by
  rcases le_total (p.get i) (iv.midpoint i : ℝ) with h | h
  · exact Or.inl (mem_lowerHalf hp h)
  · exact Or.inr (mem_upperHalf hp h)

theorem rootInterval_toReal :
    CayleyInterval.toReal (CayleyPose.rootInterval ℚ) =
      CayleyPose.rootInterval ℝ := by
  ext <;> norm_num [toReal, CayleyPose.rootInterval, CayleyPose.toReal]

end CayleyInterval

end Noperthedron.SnubCube

end
