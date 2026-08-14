module

public import Mathlib.Tactic.DeriveFintype
public import Noperthedron.Pose

@[expose] public section


/-!
# `Param`: names for the five pose parameters

`Param` lives in this small low-level module (rather than with the rest of the
solution-table definitions in `SolutionTable/Defs.lean`) so that `Pose` and
`PoseInterval` lemmas can be stated generically over the parameter being
accessed, without dependency cycles.
-/

namespace Noperthedron.Solution

-- The `Fintype` derive handler needs old-style defeq (same workaround as
-- `SignType` in Mathlib.Data.Sign.Defs).
set_option backward.isDefEq.respectTransparency false in
inductive Param where | θ₁ | φ₁ | θ₂ | φ₂ | α
deriving BEq, ReflBEq, LawfulBEq, Repr, Fintype, DecidableEq, Nonempty

/-- The canonical split order of the five pose parameters, matching the CSV
`split` codes 1–5 and the full-split `cubeFold` order. -/
def Param.splitOrder : List Param := [.θ₁, .φ₁, .θ₂, .φ₂, .α]

/-- Decode a CSV `split` column code (1–5) into the parameter being split. -/
def Param.ofSplitCode? : ℕ → Option Param
  | 0 => none
  | n + 1 => Param.splitOrder[n]?

#guard Param.ofSplitCode? 0 = none
#guard Param.ofSplitCode? 1 = some .θ₁
#guard Param.ofSplitCode? 2 = some .φ₁
#guard Param.ofSplitCode? 3 = some .θ₂
#guard Param.ofSplitCode? 4 = some .φ₂
#guard Param.ofSplitCode? 5 = some .α
#guard Param.ofSplitCode? 6 = none

end Noperthedron.Solution

/-! ## `Param`-indexed access on `Pose` -/

namespace Pose
variable {R : Type}

/-- Read the component of a `Pose` selected by a `Solution.Param`. -/
def getParam (p : Pose R) : Noperthedron.Solution.Param → R
  | .θ₁ => p.θ₁
  | .θ₂ => p.θ₂
  | .φ₁ => p.φ₁
  | .φ₂ => p.φ₂
  | .α  => p.α

/-- Replace the component of a `Pose` selected by a `Solution.Param`. -/
def setParam (p : Pose R) : Noperthedron.Solution.Param → R → Pose R
  | .θ₁, x => { p with θ₁ := x }
  | .θ₂, x => { p with θ₂ := x }
  | .φ₁, x => { p with φ₁ := x }
  | .φ₂, x => { p with φ₂ := x }
  | .α,  x => { p with α  := x }

@[simp] lemma getParam_setParam_self (p : Pose R) (a : Noperthedron.Solution.Param) (x : R) :
    (p.setParam a x).getParam a = x := by cases a <;> rfl

@[simp] lemma getParam_setParam_of_ne (p : Pose R) {a b : Noperthedron.Solution.Param}
    (h : b ≠ a) (x : R) :
    (p.setParam a x).getParam b = p.getParam b := by
  cases a <;> cases b <;> first | rfl | (exact absurd rfl h)

lemma le_iff_forall_getParam [PartialOrder R] (p q : Pose R) :
    p ≤ q ↔ ∀ a : Noperthedron.Solution.Param, p.getParam a ≤ q.getParam a := by
  rw [le_iff]
  refine ⟨fun ⟨h1, h2, h3, h4, h5⟩ a => by cases a <;> assumption,
          fun h => ⟨h .θ₁, h .θ₂, h .φ₁, h .φ₂, h .α⟩⟩

lemma mem_closedBall_iff_forall_getParam [MetricSpace R] {p q : Pose R} {ε : ℝ} :
    p ∈ Metric.closedBall q ε ↔
      ∀ a : Noperthedron.Solution.Param, dist (p.getParam a) (q.getParam a) ≤ ε := by
  rw [mem_closedBall_iff]
  refine ⟨fun ⟨h1, h2, h3, h4, h5⟩ a => by cases a <;> assumption,
          fun h => ⟨h .θ₁, h .θ₂, h .φ₁, h .φ₂, h .α⟩⟩

end Pose

end
