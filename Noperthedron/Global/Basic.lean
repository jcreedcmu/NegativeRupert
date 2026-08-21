module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Noperthedron.PoseInterval

@[expose] public section


open scoped RealInnerProductSpace

namespace GlobalTheorem

noncomputable
def nth_partial {n : ℕ} (i : Fin n) (f : E n → ℝ) (x : E n) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- All third partials of `f` are bounded by `M` everywhere. -/
def third_partials_bounded {n : ℕ} (f : E n → ℝ) (M : ℝ) : Prop :=
  ∀ (x : E n) (i j k : Fin n), |nth_partial i (nth_partial j (nth_partial k f)) x| ≤ M

end GlobalTheorem

end
