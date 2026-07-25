module

public import Noperthedron.Checker.RatBall
public import Noperthedron.Nopert76.AtlasPose

@[expose] public section

/-! # Rational boxes for Nopert #214 atlas poses -/

namespace Noperthedron.Nopert76

@[reducible]
def AtlasInterval (R : Type) [PartialOrder R] : Type :=
  NonemptyInterval (AtlasPose R)

namespace AtlasPose

def get {R : Type} (p : AtlasPose R) (i : Fin 5) : R := equivPi p i

def set {R : Type} (p : AtlasPose R) (i : Fin 5) (value : R) :
    AtlasPose R := equivPi.symm (Function.update (equivPi p) i value)

@[simp] theorem get_set_same {R : Type} (p : AtlasPose R)
    (i : Fin 5) (value : R) : (p.set i value).get i = value := by
  simp [get, set]

@[simp] theorem get_set_of_ne {R : Type} (p : AtlasPose R)
    {i j : Fin 5} (value : R) (h : j ≠ i) :
    (p.set i value).get j = p.get j := by
  simp [get, set, h]

@[simp] theorem get_zero {R : Type} (p : AtlasPose R) : p.get 0 = p.θ := rfl
@[simp] theorem get_one {R : Type} (p : AtlasPose R) : p.get 1 = p.φ := rfl
@[simp] theorem get_two {R : Type} (p : AtlasPose R) : p.get 2 = p.x := rfl
@[simp] theorem get_three {R : Type} (p : AtlasPose R) : p.get 3 = p.y := rfl
@[simp] theorem get_four {R : Type} (p : AtlasPose R) : p.get 4 = p.z := rfl

theorem le_iff_forall_get {R : Type} [PartialOrder R]
    (p q : AtlasPose R) : p ≤ q ↔ ∀ i, p.get i ≤ q.get i := by
  rw [le_iff]
  constructor
  · rintro ⟨hθ, hφ, hx, hy, hz⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4⟩

@[simp] theorem toReal_get (p : AtlasPose ℚ) (i : Fin 5) :
    p.toReal.get i = (p.get i : ℝ) := by
  fin_cases i <;> rfl

end AtlasPose

namespace AtlasInterval

abbrev mk {R : Type} [PartialOrder R]
    (min max : AtlasPose R) (h : min ≤ max) : AtlasInterval R :=
  NonemptyInterval.mk ⟨min, max⟩ h

abbrev min {R : Type} [PartialOrder R] (iv : AtlasInterval R) :
    AtlasPose R := iv.fst

abbrev max {R : Type} [PartialOrder R] (iv : AtlasInterval R) :
    AtlasPose R := iv.snd

abbrev min_le_max {R : Type} [PartialOrder R] (iv : AtlasInterval R) :
    iv.min ≤ iv.max := iv.fst_le_snd

def toReal (iv : AtlasInterval ℚ) : AtlasInterval ℝ :=
  AtlasInterval.mk iv.min.toReal iv.max.toReal (by
    rw [AtlasPose.le_iff_forall_get]
    intro i
    rw [AtlasPose.toReal_get, AtlasPose.toReal_get]
    exact_mod_cast (AtlasPose.le_iff_forall_get _ _).mp iv.min_le_max i)

theorem mem_toReal_iff {p : AtlasPose ℝ} {iv : AtlasInterval ℚ} :
    p ∈ iv.toReal ↔ ∀ i : Fin 5,
      p.get i ∈ Set.Icc (iv.min.get i : ℝ) (iv.max.get i : ℝ) := by
  rw [NonemptyInterval.mem_def]
  simp only [AtlasPose.le_iff_forall_get, toReal,
    AtlasPose.toReal_get, Set.mem_Icc, ← forall_and]

def coordinateBall (iv : AtlasInterval ℚ) (i : Fin 5) :
    Checker.RatBall :=
  Checker.RatBall.ofEndpoints (iv.min.get i) (iv.max.get i)

theorem coordinateBall_holds {p : AtlasPose ℝ} {iv : AtlasInterval ℚ}
    (hp : p ∈ iv.toReal) (i : Fin 5) :
    (iv.coordinateBall i).Holds (p.get i) :=
  Checker.RatBall.holds_of_mem_Icc (mem_toReal_iff.mp hp i)

def midpoint (iv : AtlasInterval ℚ) (i : Fin 5) : ℚ :=
  (iv.min.get i + iv.max.get i) / 2

private theorem min_le_midpoint (iv : AtlasInterval ℚ) (i : Fin 5) :
    iv.min.get i ≤ iv.midpoint i := by
  have h := (AtlasPose.le_iff_forall_get _ _).mp iv.min_le_max i
  simp only [midpoint]
  linarith

private theorem midpoint_le_max (iv : AtlasInterval ℚ) (i : Fin 5) :
    iv.midpoint i ≤ iv.max.get i := by
  have h := (AtlasPose.le_iff_forall_get _ _).mp iv.min_le_max i
  simp only [midpoint]
  linarith

def lowerHalf (iv : AtlasInterval ℚ) (i : Fin 5) : AtlasInterval ℚ :=
  AtlasInterval.mk iv.min (iv.max.set i (iv.midpoint i)) (by
    rw [AtlasPose.le_iff_forall_get]
    intro j
    by_cases h : j = i
    · subst j
      simpa using iv.min_le_midpoint i
    · simpa [AtlasPose.get_set_of_ne _ _ h] using
        (AtlasPose.le_iff_forall_get _ _).mp iv.min_le_max j)

def upperHalf (iv : AtlasInterval ℚ) (i : Fin 5) : AtlasInterval ℚ :=
  AtlasInterval.mk (iv.min.set i (iv.midpoint i)) iv.max (by
    rw [AtlasPose.le_iff_forall_get]
    intro j
    by_cases h : j = i
    · subst j
      simpa using iv.midpoint_le_max i
    · simpa [AtlasPose.get_set_of_ne _ _ h] using
        (AtlasPose.le_iff_forall_get _ _).mp iv.min_le_max j)

theorem mem_lowerHalf {p : AtlasPose ℝ} {iv : AtlasInterval ℚ}
    {i : Fin 5} (hp : p ∈ iv.toReal)
    (hi : p.get i ≤ (iv.midpoint i : ℝ)) :
    p ∈ (iv.lowerHalf i).toReal := by
  rw [mem_toReal_iff] at hp ⊢
  intro j
  by_cases h : j = i
  · subst j
    simpa only [lowerHalf, AtlasInterval.min, AtlasInterval.max,
      AtlasPose.get_set_same, Set.mem_Icc] using And.intro (hp i).1 hi
  · simpa [lowerHalf, AtlasPose.get_set_of_ne _ _ h] using hp j

theorem mem_upperHalf {p : AtlasPose ℝ} {iv : AtlasInterval ℚ}
    {i : Fin 5} (hp : p ∈ iv.toReal)
    (hi : (iv.midpoint i : ℝ) ≤ p.get i) :
    p ∈ (iv.upperHalf i).toReal := by
  rw [mem_toReal_iff] at hp ⊢
  intro j
  by_cases h : j = i
  · subst j
    simpa only [upperHalf, AtlasInterval.min, AtlasInterval.max,
      AtlasPose.get_set_same, Set.mem_Icc] using And.intro hi (hp i).2
  · simpa [upperHalf, AtlasPose.get_set_of_ne _ _ h] using hp j

theorem mem_imp_mem_lowerHalf_or_upperHalf {p : AtlasPose ℝ}
    {iv : AtlasInterval ℚ} (i : Fin 5) (hp : p ∈ iv.toReal) :
    p ∈ (iv.lowerHalf i).toReal ∨ p ∈ (iv.upperHalf i).toReal := by
  rcases le_total (p.get i) (iv.midpoint i : ℝ) with h | h
  · exact Or.inl (mem_lowerHalf hp h)
  · exact Or.inr (mem_upperHalf hp h)

theorem rootInterval_toReal :
    AtlasInterval.toReal (AtlasPose.rootInterval ℚ) =
      AtlasPose.rootInterval ℝ := by
  ext <;> norm_num [toReal, AtlasPose.rootInterval, AtlasPose.toReal]

end AtlasInterval

end Noperthedron.Nopert76

end
