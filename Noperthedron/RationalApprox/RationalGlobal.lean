module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Set.Operations
public import Noperthedron.Global
public import Noperthedron.PointSym
public import Noperthedron.PoseInterval
public import Noperthedron.RationalApprox.Basic
public import Noperthedron.RationalApprox.TrigInt
public import Noperthedron.RationalApprox.BoundsKappa

@[expose] public section


open scoped RealInnerProductSpace

namespace RationalApprox.GlobalTheorem

/-! ### Per-pose hoisted entries for `Gℚ`/`Hℚ`

Both certificate sides evaluate a handful of `(matrix chain)ᵀ·w` 3-vectors
that depend only on the pose and `w`, then dot them against many vertices.
We hoist those 3-vectors out to per-pose work (`hEntries`/`gEntries`) and
round each component down to a multiple of `10⁻¹³` (`hEntriesR`/`gEntriesR`,
see `round13v`): the trig values `sinℚ`/`cosℚ` have denominators `10¹³`, so
the raw hoisted vectors have denominators around `10³⁶` and every per-vertex
dot product would run on large-integer gcds. The rounding perturbs each dot
product by at most `3(1+κ)/10¹³`, which is absorbed into the `3κ`/`4κ`
budgets of the soundness lemmas `H_le_Hℚ`/`Gℚ_le_G` below (whose ingredient
bounds `bounds_kappa_*` are proved with `≈ κ` to spare). -/

namespace Gℚ_gt_maxHℚ

/-- Pre-transposed `Mᵀ·w` 3-vectors so that each per-`P` `Hℚ` evaluation is
six small dot products instead of six matrix-vector multiplies. -/
structure HEntries : Type where
  m2tw   : Fin 3 → ℚ
  m2θtw  : Fin 3 → ℚ
  m2φtw  : Fin 3 → ℚ
  m2θθtw : Fin 3 → ℚ
  m2θφtw : Fin 3 → ℚ
  m2φφtw : Fin 3 → ℚ

@[inline] def hEntries (p : Pose ℚ) (w : Fin 2 → ℚ) : HEntries :=
  let st := (RationalApprox.sinNum13 p.θ₂ : ℚ) / 10 ^ 13
  let ct := (RationalApprox.cosNum13 p.θ₂ : ℚ) / 10 ^ 13
  let sp := (RationalApprox.sinNum13 p.φ₂ : ℚ) / 10 ^ 13
  let cp := (RationalApprox.cosNum13 p.φ₂ : ℚ) / 10 ^ 13
  let w0 := w 0
  let w1 := w 1
  -- M₂   = [[-st,      ct,       0    ],
  --         [-ct*cp,   -st*cp,   sp   ]]
  -- M₂θ  = [[-ct,     -st,       0    ],
  --         [ st*cp,  -ct*cp,    0    ]]
  -- M₂φ  = [[ 0,       0,        0    ],
  --         [ ct*sp,   st*sp,    cp   ]]
  -- M₂θθ = [[ st,     -ct,       0    ],
  --         [ ct*cp,   st*cp,    0    ]]
  -- M₂θφ = [[ 0,       0,        0    ],
  --         [-st*sp,   ct*sp,    0    ]]
  -- M₂φφ = [[ 0,       0,        0    ],
  --         [ ct*cp,   st*cp,   -sp   ]]
  -- (Mᵀ·w)[j] = ∑ i, M[i][j] * w[i]
  ⟨ ![-st * w0 + (-ct * cp) * w1,    ct * w0 + (-st * cp) * w1,    sp * w1],
    ![-ct * w0 + ( st * cp) * w1,   -st * w0 + (-ct * cp) * w1,    0],
    ![ (ct * sp) * w1,                (st * sp) * w1,              cp * w1],
    ![ st * w0 + (ct * cp) * w1,    -ct * w0 + (st * cp) * w1,     0],
    ![ (-st * sp) * w1,               (ct * sp) * w1,              0],
    ![ (ct * cp) * w1,                (st * cp) * w1,             -sp * w1] ⟩

/-- `hEntries` with each hoisted vector rounded down to multiples of `10⁻¹³`,
so the per-`P` dot products run on small denominators. (The checker reads
these through `HEntries.scalars`, which forces each component once.) -/
@[inline] def hEntriesR (p : Pose ℚ) (w : Fin 2 → ℚ) : HEntries :=
  let e := hEntries p w
  ⟨round13v e.m2tw, round13v e.m2θtw, round13v e.m2φtw,
   round13v e.m2θθtw, round13v e.m2θφtw, round13v e.m2φφtw⟩

@[inline] def fastH (entries : HEntries) (εθ εφ : ℚ) (kappaTerm : ℚ) (P : Fin 3 → ℚ) : ℚ :=
  entries.m2tw ⬝ᵥ P + εθ * |entries.m2θtw ⬝ᵥ P| + εφ * |entries.m2φtw ⬝ᵥ P|
    + 1 / 2 * (εθ^2 * |entries.m2θθtw ⬝ᵥ P| + 2 * (εθ * εφ) * |entries.m2θφtw ⬝ᵥ P|
        + εφ^2 * |entries.m2φφtw ⬝ᵥ P|)
    + (εθ + εφ)^3 / 6 + kappaTerm

/-- Pre-computed `(M_combined)ᵀ·w` 3-vectors for the nine matrix chains in
`Gℚ` (`R·M₁`, `R'·M₁`, `R·M₁θ`, `R·M₁φ`, `R'·M₁θ`, `R'·M₁φ`, `R·M₁θθ`,
`R·M₁θφ`, `R·M₁φφ`). With these, each chain in `Gℚ` collapses to a single
3-element dot product against `S`. -/
structure GEntries : Type where
  m1RTw    : Fin 3 → ℚ  -- (R · M₁)ᵀ · w   for `p.innerℚ S ⬝ᵥ w`
  m1R'Tw   : Fin 3 → ℚ  -- (R' · M₁)ᵀ · w  for `p.rotR'ℚ (p.rotM₁ℚ S) ⬝ᵥ w`
  m1θRTw   : Fin 3 → ℚ  -- (R · M₁θ)ᵀ · w  for `p.rotRℚ (p.rotM₁θℚ S) ⬝ᵥ w`
  m1φRTw   : Fin 3 → ℚ  -- (R · M₁φ)ᵀ · w  for `p.rotRℚ (p.rotM₁φℚ S) ⬝ᵥ w`
  m1θR'Tw  : Fin 3 → ℚ  -- (R' · M₁θ)ᵀ · w for `p.rotR'ℚ (p.rotM₁θℚ S) ⬝ᵥ w`
  m1φR'Tw  : Fin 3 → ℚ  -- (R' · M₁φ)ᵀ · w for `p.rotR'ℚ (p.rotM₁φℚ S) ⬝ᵥ w`
  m1θθRTw  : Fin 3 → ℚ  -- (R · M₁θθ)ᵀ · w for `p.rotRℚ (p.rotM₁θθℚ S) ⬝ᵥ w`
  m1θφRTw  : Fin 3 → ℚ  -- (R · M₁θφ)ᵀ · w for `p.rotRℚ (p.rotM₁θφℚ S) ⬝ᵥ w`
  m1φφRTw  : Fin 3 → ℚ  -- (R · M₁φφ)ᵀ · w for `p.rotRℚ (p.rotM₁φφℚ S) ⬝ᵥ w`

@[inline] def gEntries (p : Pose ℚ) (w : Fin 2 → ℚ) : GEntries :=
  let st1 := (RationalApprox.sinNum13 p.θ₁ : ℚ) / 10 ^ 13
  let ct1 := (RationalApprox.cosNum13 p.θ₁ : ℚ) / 10 ^ 13
  let sp1 := (RationalApprox.sinNum13 p.φ₁ : ℚ) / 10 ^ 13
  let cp1 := (RationalApprox.cosNum13 p.φ₁ : ℚ) / 10 ^ 13
  let sa  := (RationalApprox.sinNum13 p.α : ℚ) / 10 ^ 13
  let ca  := (RationalApprox.cosNum13 p.α : ℚ) / 10 ^ 13
  let w0 := w 0
  let w1 := w 1
  -- Rᵀ · w = (ca·w0 + sa·w1, -sa·w0 + ca·w1)
  let u0  := ca * w0 + sa * w1
  let u1  := -sa * w0 + ca * w1
  -- R'ᵀ · w = (-sa·w0 + ca·w1, -ca·w0 + (-sa)·w1)
  let up0 := -sa * w0 + ca * w1
  let up1 := -ca * w0 + (-sa) * w1
  -- M₁ᵀ · u: uses (M₁[j][i])
  -- M₁   = [[-st1, ct1, 0], [-ct1*cp1, -st1*cp1, sp1]]
  -- M₁θ  = [[-ct1, -st1, 0], [st1*cp1, -ct1*cp1, 0]]
  -- M₁φ  = [[0, 0, 0], [ct1*sp1, st1*sp1, cp1]]
  -- M₁θθ = [[st1, -ct1, 0], [ct1*cp1, st1*cp1, 0]]
  -- M₁θφ = [[0, 0, 0], [-st1*sp1, ct1*sp1, 0]]
  -- M₁φφ = [[0, 0, 0], [ct1*cp1, st1*cp1, -sp1]]
  ⟨ ![-st1 * u0 + (-ct1 * cp1) * u1,
       ct1 * u0 + (-st1 * cp1) * u1,
       sp1 * u1],
    -- M₁ᵀ · u'
    ![-st1 * up0 + (-ct1 * cp1) * up1,
       ct1 * up0 + (-st1 * cp1) * up1,
       sp1 * up1],
    -- M₁θᵀ · u
    ![-ct1 * u0 + (st1 * cp1) * u1,
      -st1 * u0 + (-ct1 * cp1) * u1,
       0],
    -- M₁φᵀ · u
    ![(ct1 * sp1) * u1,
      (st1 * sp1) * u1,
       cp1 * u1],
    -- M₁θᵀ · u'
    ![-ct1 * up0 + (st1 * cp1) * up1,
      -st1 * up0 + (-ct1 * cp1) * up1,
       0],
    -- M₁φᵀ · u'
    ![(ct1 * sp1) * up1,
      (st1 * sp1) * up1,
       cp1 * up1],
    -- M₁θθᵀ · u
    ![ st1 * u0 + (ct1 * cp1) * u1,
      -ct1 * u0 + (st1 * cp1) * u1,
       0],
    -- M₁θφᵀ · u
    ![(-st1 * sp1) * u1,
      (ct1 * sp1) * u1,
       0],
    -- M₁φφᵀ · u
    ![(ct1 * cp1) * u1,
      (st1 * cp1) * u1,
      -sp1 * u1] ⟩

/-- `gEntries` with each hoisted vector rounded down to multiples of `10⁻¹³`.
(Each component is read at most twice per row by `fastG`.) -/
@[inline] def gEntriesR (p : Pose ℚ) (w : Fin 2 → ℚ) : GEntries :=
  let e := gEntries p w
  ⟨round13v e.m1RTw, round13v e.m1R'Tw, round13v e.m1θRTw, round13v e.m1φRTw,
   round13v e.m1θR'Tw, round13v e.m1φR'Tw,
   round13v e.m1θθRTw, round13v e.m1θφRTw, round13v e.m1φφRTw⟩

/-- Shared proof for the fifteen `*_dot_eq` identities below: unfold the pose
matrices and both hoisted-entry structures to scalars, then close with `ring`. -/
local macro "dot_eq_tac" : tactic =>
  `(tactic| (
    simp [RationalApprox.sinNum13_div_eq, RationalApprox.cosNum13_div_eq,
      hEntries, gEntries, Pose.innerℚ, Pose.rotRℚ, Pose.rotR'ℚ,
      Pose.rotM₁ℚ, Pose.rotM₁θℚ, Pose.rotM₁φℚ, Pose.rotM₁θθℚ, Pose.rotM₁θφℚ, Pose.rotM₁φφℚ,
      Pose.rotM₂ℚ, Pose.rotM₂θℚ, Pose.rotM₂φℚ, Pose.rotM₂θθℚ, Pose.rotM₂θφℚ, Pose.rotM₂φφℚ,
      RationalApprox.rotRℚ, RationalApprox.rotR'ℚ, RationalApprox.rotMℚ,
      RationalApprox.rotMθℚ, RationalApprox.rotMφℚ, RationalApprox.rotMθθℚ,
      RationalApprox.rotMθφℚ, RationalApprox.rotMφφℚ,
      RationalApprox.rotRℚ_mat, RationalApprox.rotR'ℚ_mat, RationalApprox.rotMℚ_mat,
      RationalApprox.rotMθℚ_mat, RationalApprox.rotMφℚ_mat, RationalApprox.rotMθθℚ_mat,
      RationalApprox.rotMθφℚ_mat, RationalApprox.rotMφφℚ_mat,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring))

private lemma m2tw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2tw ⬝ᵥ P = p.rotM₂ℚ P ⬝ᵥ w := by dot_eq_tac

private lemma m2θtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2θtw ⬝ᵥ P = p.rotM₂θℚ P ⬝ᵥ w := by dot_eq_tac

private lemma m2φtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2φtw ⬝ᵥ P = p.rotM₂φℚ P ⬝ᵥ w := by dot_eq_tac

private lemma m2θθtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2θθtw ⬝ᵥ P = p.rotM₂θθℚ P ⬝ᵥ w := by dot_eq_tac

private lemma m2θφtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2θφtw ⬝ᵥ P = p.rotM₂θφℚ P ⬝ᵥ w := by dot_eq_tac

private lemma m2φφtw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    (hEntries p w).m2φφtw ⬝ᵥ P = p.rotM₂φφℚ P ⬝ᵥ w := by dot_eq_tac

private lemma m1RTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1RTw ⬝ᵥ S = p.innerℚ S ⬝ᵥ w := by dot_eq_tac

private lemma m1R'Tw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1R'Tw ⬝ᵥ S = p.rotR'ℚ (p.rotM₁ℚ S) ⬝ᵥ w := by dot_eq_tac

private lemma m1θRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1θRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁θℚ S) ⬝ᵥ w := by dot_eq_tac

private lemma m1φRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1φRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁φℚ S) ⬝ᵥ w := by dot_eq_tac

private lemma m1θR'Tw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1θR'Tw ⬝ᵥ S = p.rotR'ℚ (p.rotM₁θℚ S) ⬝ᵥ w := by dot_eq_tac

private lemma m1φR'Tw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1φR'Tw ⬝ᵥ S = p.rotR'ℚ (p.rotM₁φℚ S) ⬝ᵥ w := by dot_eq_tac

private lemma m1θθRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1θθRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁θθℚ S) ⬝ᵥ w := by dot_eq_tac

private lemma m1θφRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1θφRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁θφℚ S) ⬝ᵥ w := by dot_eq_tac

private lemma m1φφRTw_dot_eq (p : Pose ℚ) (w : Fin 2 → ℚ) (S : Fin 3 → ℚ) :
    (gEntries p w).m1φφRTw ⬝ᵥ S = p.rotRℚ (p.rotM₁φφℚ S) ⬝ᵥ w := by dot_eq_tac

@[inline] def fastG (entries : GEntries) (εα εθ εφ : ℚ) (S : Fin 3 → ℚ) : ℚ :=
  entries.m1RTw ⬝ᵥ S -
   (εα * |entries.m1R'Tw ⬝ᵥ S| + εθ * |entries.m1θRTw ⬝ᵥ S| + εφ * |entries.m1φRTw ⬝ᵥ S|
     + 1 / 2 * (εα^2 * |entries.m1RTw ⬝ᵥ S|
         + 2 * (εα * εθ) * |entries.m1θR'Tw ⬝ᵥ S| + 2 * (εα * εφ) * |entries.m1φR'Tw ⬝ᵥ S|
         + εθ^2 * |entries.m1θθRTw ⬝ᵥ S| + 2 * (εθ * εφ) * |entries.m1θφRTw ⬝ᵥ S|
         + εφ^2 * |entries.m1φφRTw ⬝ᵥ S|)
     + (εα + εθ + εφ)^3 / 6
     + 4 * κℚ * (1 + (εα + εθ + εφ) + (εα + εθ + εφ)^2 / 2))

/-- The rounded hoisted `H`-side vectors as strict scalar fields. A
`Fin 3 → ℚ` value is a closure whose components (including their `round13`
calls) are re-evaluated on every access; structure-constructor arguments are
evaluated once, at construction, so the checker's per-`P` loop reads
precomputed scalars. -/
structure HScalars : Type where
  a0 : ℚ
  a1 : ℚ
  a2 : ℚ
  b0 : ℚ
  b1 : ℚ
  b2 : ℚ
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  d0 : ℚ
  d1 : ℚ
  d2 : ℚ
  e0 : ℚ
  e1 : ℚ
  e2 : ℚ
  f0 : ℚ
  f1 : ℚ
  f2 : ℚ

@[inline] def HEntries.scalars (e : HEntries) : HScalars :=
  ⟨e.m2tw 0, e.m2tw 1, e.m2tw 2,
   e.m2θtw 0, e.m2θtw 1, e.m2θtw 2,
   e.m2φtw 0, e.m2φtw 1, e.m2φtw 2,
   e.m2θθtw 0, e.m2θθtw 1, e.m2θθtw 2,
   e.m2θφtw 0, e.m2θφtw 1, e.m2θφtw 2,
   e.m2φφtw 0, e.m2φφtw 1, e.m2φφtw 2⟩

/-- `fastH` on precomputed scalars, with the dot products written out. Takes
the vertex coordinates as scalars so each is read (a `ℚ` division for the
table's vertex functions) only once per vertex. -/
@[inline] def fastHs (e : HScalars) (εθ εφ : ℚ) (kappaTerm : ℚ) (p0 p1 p2 : ℚ) : ℚ :=
  e.a0 * p0 + e.a1 * p1 + e.a2 * p2
    + εθ * |e.b0 * p0 + e.b1 * p1 + e.b2 * p2| + εφ * |e.c0 * p0 + e.c1 * p1 + e.c2 * p2|
    + 1 / 2 * (εθ^2 * |e.d0 * p0 + e.d1 * p1 + e.d2 * p2|
        + 2 * (εθ * εφ) * |e.e0 * p0 + e.e1 * p1 + e.e2 * p2|
        + εφ^2 * |e.f0 * p0 + e.f1 * p1 + e.f2 * p2|)
    + (εθ + εφ)^3 / 6 + kappaTerm

private lemma fastHs_scalars_eq (e : HEntries) (εθ εφ kt : ℚ) (P : Fin 3 → ℚ) :
    fastHs e.scalars εθ εφ kt (P 0) (P 1) (P 2) = fastH e εθ εφ kt P := by
  simp only [fastHs, HEntries.scalars, fastH, dotProduct, Fin.sum_univ_three]

/-! #### Three-tier `H` test

For all but the few near-binding vertices `P`, the margin `g − H(P)` dwarfs
everything past the zeroth-order dot product, so per-pose ∞-norm bounds on
the first- and second-order vectors (`foBound`/`soBound`) let the common
case decide with the single `a`-dot product plus one multiply
(`cheapestHs`); the vertices that fail fall back to the three-dot `cheapHs`
(second-order group still bounded by `soBound`), and only the near-binding
ones run the exact six-dot `fastHs`. Since
`cheapestHs ≥ cheapHs ≥ fastHs` pointwise, the tiered test decides exactly
`g > fastHs`. -/

/-- Upper bound for `fastHs` that replaces the three second-order dot
products by the precomputed scalar `soBound * (|p0| + |p1| + |p2|)`. -/
@[inline] def cheapHs (e : HScalars) (εθ εφ kappaTerm soBound p0 p1 p2 : ℚ) : ℚ :=
  e.a0 * p0 + e.a1 * p1 + e.a2 * p2
    + εθ * |e.b0 * p0 + e.b1 * p1 + e.b2 * p2| + εφ * |e.c0 * p0 + e.c1 * p1 + e.c2 * p2|
    + soBound * (|p0| + |p1| + |p2|)
    + (εθ + εφ)^3 / 6 + kappaTerm

/-- The per-pose scalar for `cheapHs`: the `(εθ², 2εθεφ, εφ²)/2`-weighted
∞-norms of the three second-order vectors. -/
@[inline] def soBound (e : HScalars) (εθ εφ : ℚ) : ℚ :=
  1 / 2 * (εθ^2 * max |e.d0| (max |e.d1| |e.d2|)
    + 2 * (εθ * εφ) * max |e.e0| (max |e.e1| |e.e2|)
    + εφ^2 * max |e.f0| (max |e.f1| |e.f2|))

/-- The first-order half of the per-pose scalar for `cheapestHs`: the
`(εθ, εφ)`-weighted ∞-norms of the two first-order vectors. -/
@[inline] def foBound (e : HScalars) (εθ εφ : ℚ) : ℚ :=
  εθ * max |e.b0| (max |e.b1| |e.b2|) + εφ * max |e.c0| (max |e.c1| |e.c2|)

/-- Tier-0 upper bound for `fastHs`: everything past the zeroth-order dot
product is replaced by the two per-pose scalars
`fsBound = foBound + soBound` and `kappaRem = (εθ+εφ)³/6 + kappaTerm`, so
each vertex costs one dot product and one multiply. -/
@[inline] def cheapestHs (e : HScalars) (fsBound kappaRem p0 p1 p2 : ℚ) : ℚ :=
  e.a0 * p0 + e.a1 * p1 + e.a2 * p2 + fsBound * (|p0| + |p1| + |p2|) + kappaRem

private lemma abs_dot3_le (d0 d1 d2 p0 p1 p2 : ℚ) :
    |d0 * p0 + d1 * p1 + d2 * p2| ≤
      max |d0| (max |d1| |d2|) * (|p0| + |p1| + |p2|) := by
  have h0 : |d0| ≤ max |d0| (max |d1| |d2|) := le_max_left _ _
  have h1 : |d1| ≤ max |d0| (max |d1| |d2|) := le_trans (le_max_left _ _) (le_max_right _ _)
  have h2 : |d2| ≤ max |d0| (max |d1| |d2|) := le_trans (le_max_right _ _) (le_max_right _ _)
  calc |d0 * p0 + d1 * p1 + d2 * p2|
      ≤ |d0 * p0| + |d1 * p1| + |d2 * p2| := abs_add_three _ _ _
    _ = |d0| * |p0| + |d1| * |p1| + |d2| * |p2| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ max |d0| (max |d1| |d2|) * |p0| + max |d0| (max |d1| |d2|) * |p1|
        + max |d0| (max |d1| |d2|) * |p2| := by
          gcongr
    _ = max |d0| (max |d1| |d2|) * (|p0| + |p1| + |p2|) := by ring

private lemma fastHs_le_cheapHs {εθ εφ : ℚ} (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    (e : HScalars) (kt p0 p1 p2 : ℚ) :
    fastHs e εθ εφ kt p0 p1 p2 ≤ cheapHs e εθ εφ kt (soBound e εθ εφ) p0 p1 p2 := by
  unfold fastHs cheapHs soBound
  have hd := mul_le_mul_of_nonneg_left (abs_dot3_le e.d0 e.d1 e.d2 p0 p1 p2)
    (mul_nonneg hεθ hεθ)
  have he := mul_le_mul_of_nonneg_left (abs_dot3_le e.e0 e.e1 e.e2 p0 p1 p2)
    (mul_nonneg hεθ hεφ)
  have hf := mul_le_mul_of_nonneg_left (abs_dot3_le e.f0 e.f1 e.f2 p0 p1 p2)
    (mul_nonneg hεφ hεφ)
  linarith [hd, he, hf]

private lemma fastHs_le_cheapestHs {εθ εφ : ℚ} (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    (e : HScalars) (kt p0 p1 p2 : ℚ) :
    fastHs e εθ εφ kt p0 p1 p2 ≤
      cheapestHs e (foBound e εθ εφ + soBound e εθ εφ) ((εθ + εφ)^3 / 6 + kt) p0 p1 p2 := by
  unfold fastHs cheapestHs foBound soBound
  have hb := mul_le_mul_of_nonneg_left (abs_dot3_le e.b0 e.b1 e.b2 p0 p1 p2) hεθ
  have hc := mul_le_mul_of_nonneg_left (abs_dot3_le e.c0 e.c1 e.c2 p0 p1 p2) hεφ
  have hd := mul_le_mul_of_nonneg_left (abs_dot3_le e.d0 e.d1 e.d2 p0 p1 p2)
    (mul_nonneg hεθ hεθ)
  have he := mul_le_mul_of_nonneg_left (abs_dot3_le e.e0 e.e1 e.e2 p0 p1 p2)
    (mul_nonneg hεθ hεφ)
  have hf := mul_le_mul_of_nonneg_left (abs_dot3_le e.f0 e.f1 e.f2 p0 p1 p2)
    (mul_nonneg hεφ hεφ)
  linarith [hb, hc, hd, he, hf]

/-- One vertex of the three-tier test: try `cheapestHs` (one dot product),
then `cheapHs` (three), and fall back to the exact `fastHs` (six) only if
both fail. `Bool.or` is short-circuiting, so the later tiers are not
evaluated when an earlier test passes. -/
@[inline] def tieredHs_lt (e : HScalars) (εθ εφ kappaTerm soB fsB kR g p0 p1 p2 : ℚ) :
    Bool :=
  decide (g > cheapestHs e fsB kR p0 p1 p2) ||
  decide (g > cheapHs e εθ εφ kappaTerm soB p0 p1 p2) ||
  decide (g > fastHs e εθ εφ kappaTerm p0 p1 p2)

private lemma tieredHs_lt_iff {εθ εφ : ℚ} (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    (e : HScalars) (kt g p0 p1 p2 : ℚ) :
    tieredHs_lt e εθ εφ kt (soBound e εθ εφ) (foBound e εθ εφ + soBound e εθ εφ)
      ((εθ + εφ)^3 / 6 + kt) g p0 p1 p2 = true ↔
      g > fastHs e εθ εφ kt p0 p1 p2 := by
  simp only [tieredHs_lt, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨fun h => ?_, fun h => Or.inr h⟩
  obtain (h | h) | h := h
  · exact lt_of_le_of_lt (fastHs_le_cheapestHs hεθ hεφ e kt p0 p1 p2) h
  · exact lt_of_le_of_lt (fastHs_le_cheapHs hεθ hεφ e kt p0 p1 p2) h
  · exact h

end Gℚ_gt_maxHℚ

open Gℚ_gt_maxHℚ in
/--
A measure of how far an inner-shadow vertex S can "stick out".

Second-order anisotropic certificate: the per-axis radii `εα`, `εθ`, `εφ`
weight the first partials, the exact second partials at the center (with
multiplicities from the symmetric 3×3 table), and an `(εα+εθ+εφ)³/6`
Lagrange remainder. The nine hoisted `(R·M₁)ᵀ·w`-style 3-vectors are rounded
down to multiples of `10⁻¹³` (`gEntriesR`); with `E = εα+εθ+εφ`, the
`4κℚ(1+E+E²/2)` term absorbs the `sinℚ`/`cosℚ` approximation error and this
rounding for each chain at its weight (see `Gℚ_le_G`). On the diagonal
`εα = εθ = εφ = ε` this recovers the isotropic remainder `9ε³/2` and slack
`4κℚ(1+3ε+(9/2)ε²)`.
-/
def Gℚ (p : Pose ℚ) (εα εθ εφ : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) : ℚ :=
  fastG (gEntriesR p w) εα εθ εφ S

open Gℚ_gt_maxHℚ in
/--
A measure of how far an outer-shadow vertex P can "reach" along w.

Second-order anisotropic certificate with per-axis radii `εθ`, `εφ` and
Lagrange remainder `(εθ+εφ)³/6`. The six hoisted `M₂ᵀ·w`-style 3-vectors are
rounded down to multiples of `10⁻¹³` (`hEntriesR`); with `E = εθ+εφ`, the
`3κℚ(1+E+E²/2)` term absorbs both the `sinℚ`/`cosℚ` approximation error and
this rounding (see `H_le_Hℚ`). On the diagonal `εθ = εφ = ε` this recovers
the isotropic remainder `4ε³/3` and slack `3κℚ(1+2ε+2ε²)`.
-/
def Hℚ (p : Pose ℚ) (εθ εφ : ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) : ℚ :=
  fastH (hEntriesR p w) εθ εφ (3 * κℚ * (1 + (εθ + εφ) + (εθ + εφ)^2 / 2)) P

/--
A measure of how far all of the outer-shadow vertices can "reach" along w.
-/
def maxHℚ {ι : Type} [Fintype ι] [ne : Nonempty ι]
    (p : Pose ℚ) (poly : Polyhedron ι (Fin 3 → ℚ)) (εθ εφ : ℚ) (w : Fin 2 → ℚ) : ℚ :=
  Finset.image (Hℚ p εθ εφ w ∘ poly.v) Finset.univ  |>.max' <| by
    simp only [Finset.image_nonempty]
    exact Finset.univ_nonempty_iff.mpr ne

private lemma fastG_eq_Gℚ (p : Pose ℚ) (εα εθ εφ : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    Gℚ_gt_maxHℚ.fastG (Gℚ_gt_maxHℚ.gEntriesR p w) εα εθ εφ S = Gℚ p εα εθ εφ S w := rfl

private lemma fastH_eq_Hℚ (p : Pose ℚ) (εθ εφ : ℚ) (w : Fin 2 → ℚ) (P : Fin 3 → ℚ) :
    Gℚ_gt_maxHℚ.fastH (Gℚ_gt_maxHℚ.hEntriesR p w) εθ εφ
      (3 * κℚ * (1 + (εθ + εφ) + (εθ + εφ)^2 / 2)) P = Hℚ p εθ εφ w P :=
  rfl

open Gℚ_gt_maxHℚ in
/-- Bool-valued `Gℚ > maxHℚ` check that hoists the trig partial sums and the
rounded `Mᵀ·w` 3-vectors to per-pose work for both `Gℚ` and `Hℚ`; the
`∀ P ∈ poly.v` loop then only does small-denominator dot products, and the
three-tier `tieredHs_lt` decides all but the near-binding vertices with the
single zeroth-order dot product alone. -/
def Gℚ_gt_maxHℚ_check {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Pose ℚ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ) (S : Fin 3 → ℚ)
    (poly : Polyhedron ι (Fin 3 → ℚ)) (w : Fin 2 → ℚ) : Bool :=
  let hscalars := (hEntriesR p w).scalars
  let g := fastG (gEntriesR p w) εα εθ₁ εφ₁ S
  let kappaTerm := 3 * κℚ * (1 + (εθ₂ + εφ₂) + (εθ₂ + εφ₂)^2 / 2)
  let soB := soBound hscalars εθ₂ εφ₂
  let fsB := foBound hscalars εθ₂ εφ₂ + soB
  let kR := (εθ₂ + εφ₂)^3 / 6 + kappaTerm
  decide <| ∀ k : ι,
    tieredHs_lt hscalars εθ₂ εφ₂ kappaTerm soB fsB kR g
      (poly.v k 0) (poly.v k 1) (poly.v k 2) = true

theorem Gℚ_gt_maxHℚ_check_iff {ι : Type} [Fintype ι] [DecidableEq ι] [ne : Nonempty ι]
    (p : Pose ℚ) (εα εθ₁ εφ₁ : ℚ) {εθ₂ εφ₂ : ℚ} (hεθ₂ : 0 ≤ εθ₂) (hεφ₂ : 0 ≤ εφ₂)
    (S : Fin 3 → ℚ) (poly : Polyhedron ι (Fin 3 → ℚ)) (w : Fin 2 → ℚ) :
    Gℚ_gt_maxHℚ_check p εα εθ₁ εφ₁ εθ₂ εφ₂ S poly w = true ↔
      Gℚ p εα εθ₁ εφ₁ S w > maxHℚ p poly εθ₂ εφ₂ w := by
  unfold Gℚ_gt_maxHℚ_check maxHℚ
  simp only [decide_eq_true_eq, Gℚ_gt_maxHℚ.tieredHs_lt_iff hεθ₂ hεφ₂]
  rw [fastG_eq_Gℚ]
  constructor
  · intro hAll
    show (Finset.image (Hℚ p εθ₂ εφ₂ w ∘ poly.v) Finset.univ).max' _ < Gℚ p εα εθ₁ εφ₁ S w
    rw [Finset.max'_lt_iff]
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨k, _, rfl⟩ := hy
    have := hAll k
    rw [Gℚ_gt_maxHℚ.fastHs_scalars_eq, fastH_eq_Hℚ] at this
    exact this
  · intro hLt k
    rw [Gℚ_gt_maxHℚ.fastHs_scalars_eq, fastH_eq_Hℚ]
    apply lt_of_le_of_lt _ hLt
    apply Finset.le_max'
    rw [Finset.mem_image]
    exact ⟨k, Finset.mem_univ k, rfl⟩

/--
A compact way of saying "the pose satisfies the rational global theorem precondition at
per-axis widths `εα εθ₁ εφ₁ εθ₂ εφ₂`".
We require the existence of some inner-shadow vertex S from the polyhedron, and a covector w meant to express
the direction we're projecting ℝ² → ℝ to find that S "sticks out too far" compared to all the
other outer-shadow vertices P (which the calculation of H iterates over) in the polygon that lies in ℝ².
-/
structure RationalGlobalTheoremPrecondition {ι : Type} [Fintype ι] [Nonempty ι]
    (poly : GoodPoly ι) (poly_ : Polyhedron ι (Fin 3 → ℚ))
    (happrox : κApproxPoly poly.vertices poly_) (p : Pose ℚ)
    (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ) : Type where
  j : ι
  p_in_4 : p ∈ fourInterval ℚ
  w : Fin 2 → ℚ
  w_unit : ‖toR2 w‖ = 1
  exceeds : Gℚ p εα εθ₁ εφ₁ (poly_.v j) w > maxHℚ p poly_ εθ₂ εφ₂ w

private lemma abs_le_abs_add_of_norm_sub_le {a b C : ℝ} (h : ‖a - b‖ ≤ C) : |a| ≤ |b| + C := by
  linarith [abs_sub_abs_le_abs_sub a b, (Real.norm_eq_abs _).symm ▸ h]

/-- The coordinates of a κ-approximation `P_` of a vector of norm ≤ 1 have
`∑ i, |P_ i| ≤ 3(1+κℚ)`. -/
private lemma sum_abs_le_of_approx {P : ℝ³} {P_ : Fin 3 → ℚ}
    (hP : ‖P‖ ≤ 1) (hP_approx : ‖P - toR3 P_‖ ≤ κ) :
    ∑ i, |P_ i| ≤ 3 * (1 + κℚ) := by
  have hPnorm : ‖toR3 P_‖ ≤ 1 + κ := by
    have h := norm_le_insert P (toR3 P_)
    linarith
  have hcoord : ∀ i, |P_ i| ≤ 1 + κℚ := by
    intro i
    have h1 : |(P_ i : ℝ)| ≤ ‖toR3 P_‖ := by
      have h := PiLp.norm_apply_le (toR3 P_) i
      simpa only [toR3, WithLp.ofLp_toLp, Real.norm_eq_abs] using h
    have h2 : |(P_ i : ℝ)| ≤ 1 + κ := h1.trans hPnorm
    rw [← cast_κℚ] at h2
    exact_mod_cast h2
  rw [Fin.sum_univ_three]
  linarith [hcoord 0, hcoord 1, hcoord 2]

/-- Absorb the `round13v` rounding of a hoisted 3-vector into a κ-scale bound:
rounding perturbs the dot product against `P_` by at most `3(1+κ)/10¹³`. -/
private lemma norm_sub_round13v_dot_le {x : ℝ} {v P_ : Fin 3 → ℚ} {c : ℝ}
    (hbase : ‖x - ((v ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ c)
    (hsum : ∑ i, |P_ i| ≤ 3 * (1 + κℚ)) :
    ‖x - ((round13v v ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ c + 3 * (1 + κ) / 10 ^ 13 := by
  have hq : |round13v v ⬝ᵥ P_ - v ⬝ᵥ P_| ≤ 3 * (1 + κℚ) / 10 ^ 13 :=
    (abs_round13v_dot_sub_le v P_).trans (by gcongr)
  have hr : ‖((round13v v ⬝ᵥ P_ : ℚ) : ℝ) - ((v ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * (1 + κ) / 10 ^ 13 := by
    rw [Real.norm_eq_abs, ← Rat.cast_sub, ← Rat.cast_abs, ← cast_κℚ]
    exact_mod_cast hq
  calc ‖x - ((round13v v ⬝ᵥ P_ : ℚ) : ℝ)‖
      = ‖(x - ((v ⬝ᵥ P_ : ℚ) : ℝ)) -
          (((round13v v ⬝ᵥ P_ : ℚ) : ℝ) - ((v ⬝ᵥ P_ : ℚ) : ℝ))‖ := by
        congr 1; ring
    _ ≤ ‖x - ((v ⬝ᵥ P_ : ℚ) : ℝ)‖ +
        ‖((round13v v ⬝ᵥ P_ : ℚ) : ℝ) - ((v ⬝ᵥ P_ : ℚ) : ℝ)‖ := norm_sub_le _ _
    _ ≤ c + 3 * (1 + κ) / 10 ^ 13 := add_le_add hbase hr

/-- `norm_sub_round13v_dot_le` specialised to the `H`-side budget: a
`bounds_kappa_M`-style base bound (about the matrix form `d` of the hoisted
dot product, see the `*_dot_eq` lemmas) plus the rounding perturbation is
≤ `3κ`. -/
private lemma norm_sub_round13v_dot_le₃ {x : ℝ} {v P_ : Fin 3 → ℚ} {d : ℚ}
    (hdot : v ⬝ᵥ P_ = d) (hbase : ‖x - (d : ℝ)‖ ≤ 2 * κ + κ ^ 2)
    (hsum : ∑ i, |P_ i| ≤ 3 * (1 + κℚ)) :
    ‖x - ((round13v v ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
  (norm_sub_round13v_dot_le (hdot ▸ hbase) hsum).trans (by unfold κ; norm_num)

/-- `norm_sub_round13v_dot_le` specialised to the `G`-side budget: a
`bounds_kappa_RM`-style base bound plus the rounding perturbation is ≤ `4κ`. -/
private lemma norm_sub_round13v_dot_le₄ {x : ℝ} {v P_ : Fin 3 → ℚ} {d : ℚ}
    (hdot : v ⬝ᵥ P_ = d) (hbase : ‖x - (d : ℝ)‖ ≤ 3 * κ + 3 * κ ^ 2 + κ ^ 3)
    (hsum : ∑ i, |P_ i| ≤ 3 * (1 + κℚ)) :
    ‖x - ((round13v v ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
  (norm_sub_round13v_dot_le (hdot ▸ hbase) hsum).trans (by unfold κ; norm_num)

open Gℚ_gt_maxHℚ in
theorem Gℚ_le_G {p_ : Pose ℚ} {εα εθ εφ : ℚ}
    (hεα : 0 ≤ εα) (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    {S : ℝ³} {S_ : Fin 3 → ℚ} {w : Fin 2 → ℚ}
    (hS : ‖S‖ ≤ 1) (hS_approx : ‖S - toR3 S_‖ ≤ κ) (hw : ‖toR2 w‖ = 1)
    (hp : (fourInterval ℚ).contains p_) :
    Gℚ p_ εα εθ εφ S_ w ≤ GlobalTheorem.G p_.toReal εα εθ εφ S (toR2 w) := by
  set pbar := p_.toReal with hpbar
  have hsum := sum_abs_le_of_approx hS hS_approx
  let α4 : Set.Icc (-4 : ℚ) 4 := ⟨p_.α, hp.αBound⟩
  let θ4 : Set.Icc (-4 : ℚ) 4 := ⟨p_.θ₁, hp.θ₁Bound⟩
  let φ4 : Set.Icc (-4 : ℚ) 4 := ⟨p_.φ₁, hp.φ₁Bound⟩
  unfold Gℚ fastG GlobalTheorem.G
  rw [show pbar.inner S = pbar.rotR (pbar.rotM₁ S) by rw [Pose.inner_eq_RM]; rfl]
  have h_RM : ‖⟪pbar.rotR (pbar.rotM₁ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1RTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1RTw_dot_eq p_ w S_)
      (bounds_kappa_RM (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_R'M : ‖⟪pbar.rotR' (pbar.rotM₁ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1R'Tw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1R'Tw_dot_eq p_ w S_)
      (bounds_kappa_R'M (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_RMθ : ‖⟪pbar.rotR (pbar.rotM₁θ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1θRTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1θRTw_dot_eq p_ w S_)
      (bounds_kappa_RMθ (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_RMφ : ‖⟪pbar.rotR (pbar.rotM₁φ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1φRTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1φRTw_dot_eq p_ w S_)
      (bounds_kappa_RMφ (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_R'Mθ : ‖⟪pbar.rotR' (pbar.rotM₁θ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1θR'Tw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1θR'Tw_dot_eq p_ w S_)
      (bounds_kappa_R'Mθ (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_R'Mφ : ‖⟪pbar.rotR' (pbar.rotM₁φ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1φR'Tw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1φR'Tw_dot_eq p_ w S_)
      (bounds_kappa_R'Mφ (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_RMθθ : ‖⟪pbar.rotR (pbar.rotM₁θθ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1θθRTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1θθRTw_dot_eq p_ w S_)
      (bounds_kappa_RMθθ (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_RMθφ : ‖⟪pbar.rotR (pbar.rotM₁θφ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1θφRTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1θφRTw_dot_eq p_ w S_)
      (bounds_kappa_RMθφ (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have h_RMφφ : ‖⟪pbar.rotR (pbar.rotM₁φφ S), toR2 w⟫ -
      (((gEntriesR p_ w).m1φφRTw ⬝ᵥ S_ : ℚ) : ℝ)‖ ≤ 4 * κ :=
    norm_sub_round13v_dot_le₄ (m1φφRTw_dot_eq p_ w S_)
      (bounds_kappa_RMφφ (α := α4) (θ := θ4) (φ := φ4) hS hS_approx hw) hsum
  have hi_le : (((gEntriesR p_ w).m1RTw ⬝ᵥ S_ : ℚ) : ℝ) ≤
               ⟪pbar.rotR (pbar.rotM₁ S), toR2 w⟫ + 4 * κ := by
    have := (Real.norm_eq_abs _).symm ▸ h_RM; rw [abs_le] at this
    linarith [this.1]
  have hRM_abs := abs_le_abs_add_of_norm_sub_le h_RM
  have hR'_abs := abs_le_abs_add_of_norm_sub_le h_R'M
  have hRθ_abs := abs_le_abs_add_of_norm_sub_le h_RMθ
  have hRφ_abs := abs_le_abs_add_of_norm_sub_le h_RMφ
  have hR'θ_abs := abs_le_abs_add_of_norm_sub_le h_R'Mθ
  have hR'φ_abs := abs_le_abs_add_of_norm_sub_le h_R'Mφ
  have hθθ_abs := abs_le_abs_add_of_norm_sub_le h_RMθθ
  have hθφ_abs := abs_le_abs_add_of_norm_sub_le h_RMθφ
  have hφφ_abs := abs_le_abs_add_of_norm_sub_le h_RMφφ
  have h_κ : ((κℚ : ℚ) : ℝ) = κ := cast_κℚ
  have hεα_real : (0 : ℝ) ≤ εα := mod_cast hεα
  have hεθ_real : (0 : ℝ) ≤ εθ := mod_cast hεθ
  have hεφ_real : (0 : ℝ) ≤ εφ := mod_cast hεφ
  push_cast
  rw [h_κ]
  -- Each weighted `|real dot|` is at most the same weight times
  -- `|rational dot| + 4κ`; with `E = εα+εθ+εφ`, the accumulated per-term
  -- `4κ`-weights sum to exactly `4κ(E + E²/2)`, so together with the `4κ`
  -- from `hi_le` the `4κ(1 + E + E²/2)` slack closes the gap.
  have hfoα := mul_le_mul_of_nonneg_left hR'_abs hεα_real
  have hfoθ := mul_le_mul_of_nonneg_left hRθ_abs hεθ_real
  have hfoφ := mul_le_mul_of_nonneg_left hRφ_abs hεφ_real
  have hsoαα := mul_le_mul_of_nonneg_left hRM_abs (mul_nonneg hεα_real hεα_real)
  have hsoαθ := mul_le_mul_of_nonneg_left hR'θ_abs (mul_nonneg hεα_real hεθ_real)
  have hsoαφ := mul_le_mul_of_nonneg_left hR'φ_abs (mul_nonneg hεα_real hεφ_real)
  have hsoθθ := mul_le_mul_of_nonneg_left hθθ_abs (mul_nonneg hεθ_real hεθ_real)
  have hsoθφ := mul_le_mul_of_nonneg_left hθφ_abs (mul_nonneg hεθ_real hεφ_real)
  have hsoφφ := mul_le_mul_of_nonneg_left hφφ_abs (mul_nonneg hεφ_real hεφ_real)
  linarith [hi_le, hfoα, hfoθ, hfoφ, hsoαα, hsoαθ, hsoαφ, hsoθθ, hsoθφ, hsoφφ]

open Gℚ_gt_maxHℚ in
theorem H_le_Hℚ {p_ : Pose ℚ} {εθ εφ : ℚ} (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    {P : ℝ³} {P_ : Fin 3 → ℚ} {w : Fin 2 → ℚ}
    (hP : ‖P‖ ≤ 1) (hP_approx : ‖P - toR3 P_‖ ≤ κ) (hw : ‖toR2 w‖ = 1)
    (hp : (fourInterval ℚ).contains p_) :
    GlobalTheorem.H p_.toReal εθ εφ (toR2 w) P ≤ Hℚ p_ εθ εφ w P_ := by
  set pbar := p_.toReal with hpbar
  have hsum := sum_abs_le_of_approx hP hP_approx
  let θ4 : Set.Icc (-4 : ℚ) 4 := ⟨p_.θ₂, hp.θ₂Bound⟩
  let φ4 : Set.Icc (-4 : ℚ) 4 := ⟨p_.φ₂, hp.φ₂Bound⟩
  unfold GlobalTheorem.H Hℚ fastH
  have h_M : ‖⟪pbar.rotM₂ P, toR2 w⟫ -
      (((hEntriesR p_ w).m2tw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
    norm_sub_round13v_dot_le₃ (m2tw_dot_eq p_ w P_)
      (bounds_kappa_M (θ := θ4) (φ := φ4) hP hP_approx hw) hsum
  have h_Mθ : ‖⟪pbar.rotM₂θ P, toR2 w⟫ -
      (((hEntriesR p_ w).m2θtw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
    norm_sub_round13v_dot_le₃ (m2θtw_dot_eq p_ w P_)
      (bounds_kappa_Mθ (θ := θ4) (φ := φ4) hP hP_approx hw) hsum
  have h_Mφ : ‖⟪pbar.rotM₂φ P, toR2 w⟫ -
      (((hEntriesR p_ w).m2φtw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
    norm_sub_round13v_dot_le₃ (m2φtw_dot_eq p_ w P_)
      (bounds_kappa_Mφ (θ := θ4) (φ := φ4) hP hP_approx hw) hsum
  have h_Mθθ : ‖⟪pbar.rotM₂θθ P, toR2 w⟫ -
      (((hEntriesR p_ w).m2θθtw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
    norm_sub_round13v_dot_le₃ (m2θθtw_dot_eq p_ w P_)
      (bounds_kappa_Mθθ (θ := θ4) (φ := φ4) hP hP_approx hw) hsum
  have h_Mθφ : ‖⟪pbar.rotM₂θφ P, toR2 w⟫ -
      (((hEntriesR p_ w).m2θφtw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
    norm_sub_round13v_dot_le₃ (m2θφtw_dot_eq p_ w P_)
      (bounds_kappa_Mθφ (θ := θ4) (φ := φ4) hP hP_approx hw) hsum
  have h_Mφφ : ‖⟪pbar.rotM₂φφ P, toR2 w⟫ -
      (((hEntriesR p_ w).m2φφtw ⬝ᵥ P_ : ℚ) : ℝ)‖ ≤ 3 * κ :=
    norm_sub_round13v_dot_le₃ (m2φφtw_dot_eq p_ w P_)
      (bounds_kappa_Mφφ (θ := θ4) (φ := φ4) hP hP_approx hw) hsum
  have hm_le : ⟪pbar.rotM₂ P, toR2 w⟫ ≤
               (((hEntriesR p_ w).m2tw ⬝ᵥ P_ : ℚ) : ℝ) + 3 * κ := by
    have := (Real.norm_eq_abs _).symm ▸ h_M; rw [abs_le] at this
    linarith [this.2]
  have hθ_abs := abs_le_abs_add_of_norm_sub_le h_Mθ
  have hφ_abs := abs_le_abs_add_of_norm_sub_le h_Mφ
  have hθθ_abs := abs_le_abs_add_of_norm_sub_le h_Mθθ
  have hθφ_abs := abs_le_abs_add_of_norm_sub_le h_Mθφ
  have hφφ_abs := abs_le_abs_add_of_norm_sub_le h_Mφφ
  have h_κ : ((κℚ : ℚ) : ℝ) = κ := cast_κℚ
  have hεθ_real : (0 : ℝ) ≤ εθ := mod_cast hεθ
  have hεφ_real : (0 : ℝ) ≤ εφ := mod_cast hεφ
  push_cast
  rw [h_κ]
  -- Each weighted `|real dot|` is at most the same weight times
  -- `|rational dot| + 3κ`; with `E = εθ+εφ`, the accumulated per-term
  -- `3κ`-weights sum to exactly `3κ(E + E²/2)`, so together with the `3κ`
  -- from `hm_le` the `3κ(1 + E + E²/2)` slack closes the gap.
  have hfoθ := mul_le_mul_of_nonneg_left hθ_abs hεθ_real
  have hfoφ := mul_le_mul_of_nonneg_left hφ_abs hεφ_real
  have hsoθθ := mul_le_mul_of_nonneg_left hθθ_abs (mul_nonneg hεθ_real hεθ_real)
  have hsoθφ := mul_le_mul_of_nonneg_left hθφ_abs (mul_nonneg hεθ_real hεφ_real)
  have hsoφφ := mul_le_mul_of_nonneg_left hφφ_abs (mul_nonneg hεφ_real hεφ_real)
  linarith [hm_le, hfoθ, hfoφ, hsoθθ, hsoθφ, hsoφφ]

/-- The exact outer-support Taylor bound is at most its rationally checked
counterpart.  This contact-independent form is also used by balanced global
certificates. -/
theorem maxH_le_maxHℚ {ι₁ ι₂ : Type}
    [Fintype ι₁] [Nonempty ι₁] [Fintype ι₂] [Nonempty ι₂]
    {p : Pose ℚ} {εθ εφ : ℚ} (hεθ : 0 ≤ εθ) (hεφ : 0 ≤ εφ)
    (poly : GoodPoly ι₁) (poly_ : Polyhedron ι₂ (Fin 3 → ℚ))
    (happrox : κApproxPoly poly.vertices poly_) {w : Fin 2 → ℚ}
    (hw : ‖toR2 w‖ = 1) (hp : (fourInterval ℚ).contains p) :
    GlobalTheorem.maxH p.toReal poly εθ εφ (toR2 w) ≤
      ((maxHℚ p poly_ εθ εφ w : ℚ) : ℝ) := by
  unfold GlobalTheorem.maxH
  apply Finset.max'_le
  simp only [Function.comp, Finset.mem_image, Finset.mem_univ, true_and]
  rintro _ ⟨k, rfl⟩
  let k' := happrox.bijection k
  have hk_norm : ‖poly.vertices.v k‖ ≤ 1 := poly.vertex_radius_le_one k
  have hk_approx : ‖poly.vertices.v k - poly_.toReal.v k'‖ ≤ κ := happrox.approx k
  have h_le_Hℚ : GlobalTheorem.H p.toReal εθ εφ (toR2 w) (poly.vertices.v k) ≤
      Hℚ p εθ εφ w (poly_.v k') :=
    H_le_Hℚ hεθ hεφ hk_norm
      (show ‖poly.vertices.v k - toR3 (poly_.v k')‖ ≤ κ from hk_approx) hw hp
  have h_le_max : Hℚ p εθ εφ w (poly_.v k') ≤ maxHℚ p poly_ εθ εφ w := by
    unfold maxHℚ
    have hmem : (Hℚ p εθ εφ w ∘ poly_.v) k' ∈
        Finset.image (Hℚ p εθ εφ w ∘ poly_.v) Finset.univ :=
      Finset.mem_image_of_mem _ (Finset.mem_univ k')
    exact Finset.le_max' _ _ hmem
  exact h_le_Hℚ.trans (by exact_mod_cast h_le_max)

/-
[SY25] Theorem 43, with per-axis widths and a box conclusion in place of the
closed ball.
-/
theorem rational_global {ι : Type} [Fintype ι] [Nonempty ι]
    (p : Pose ℚ) (εα εθ₁ εφ₁ εθ₂ εφ₂ : ℚ)
    (hεα : 0 ≤ εα) (hεθ₁ : 0 ≤ εθ₁) (hεφ₁ : 0 ≤ εφ₁) (hεθ₂ : 0 ≤ εθ₂) (hεφ₂ : 0 ≤ εφ₂)
    (poly : GoodPoly ι) (poly_ : Polyhedron ι (Fin 3 → ℚ))
    (happrox : κApproxPoly poly.vertices poly_)
    (pc : RationalGlobalTheoremPrecondition poly poly_ happrox p εα εθ₁ εφ₁ εθ₂ εφ₂) :
    ¬ ∃ q, Pose.near p.toReal (εα : ℝ) (εθ₁ : ℝ) (εφ₁ : ℝ) (εθ₂ : ℝ) (εφ₂ : ℝ) q ∧
      RupertPose q poly.hull := by
  set pbar := p.toReal
  -- Step 1: Map S from poly_ to poly via the bijection
  let j := pc.j
  let i := happrox.bijection.symm j
  let S_real := poly.vertices.v i
  have hS_approx : ‖S_real - poly_.toReal.v j‖ ≤ κ := by
    show ‖poly.vertices.v (happrox.bijection.symm j) - poly_.toReal.v j‖ ≤ κ
    have := happrox.approx (happrox.bijection.symm j)
    rwa [Equiv.apply_symm_apply] at this
  have hS_norm : ‖S_real‖ ≤ 1 := poly.vertex_radius_le_one i
  -- Step 2: Show maxH_real ≤ maxHℚ
  have h_maxH_le : GlobalTheorem.maxH pbar poly εθ₂ εφ₂ (toR2 pc.w) ≤
      ((maxHℚ p poly_ εθ₂ εφ₂ pc.w : ℚ) : ℝ) := by
    unfold GlobalTheorem.maxH
    apply Finset.max'_le
    simp only [Function.comp, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨k, rfl⟩
    let k' := happrox.bijection k
    have hk_norm : ‖poly.vertices.v k‖ ≤ 1 := poly.vertex_radius_le_one k
    have hk_approx : ‖poly.vertices.v k - poly_.toReal.v k'‖ ≤ κ := happrox.approx k
    have h_le_Hℚ : GlobalTheorem.H pbar εθ₂ εφ₂ (toR2 pc.w) (poly.vertices.v k) ≤
                    Hℚ p εθ₂ εφ₂ pc.w (poly_.v k') :=
      H_le_Hℚ hεθ₂ hεφ₂ hk_norm
        (show ‖poly.vertices.v k - toR3 (poly_.v k')‖ ≤ κ from hk_approx)
        pc.w_unit pc.p_in_4
    have h_le_max : Hℚ p εθ₂ εφ₂ pc.w (poly_.v k') ≤ maxHℚ p poly_ εθ₂ εφ₂ pc.w := by
      unfold maxHℚ
      have : (Hℚ p εθ₂ εφ₂ pc.w ∘ poly_.v) k' ∈
              Finset.image (Hℚ p εθ₂ εφ₂ pc.w ∘ poly_.v) Finset.univ :=
        Finset.mem_image_of_mem _ (Finset.mem_univ k')
      exact Finset.le_max' _ _ this
    have h_le_max_real : ((Hℚ p εθ₂ εφ₂ pc.w (poly_.v k') : ℚ) : ℝ) ≤
        ((maxHℚ p poly_ εθ₂ εφ₂ pc.w : ℚ) : ℝ) :=
      mod_cast h_le_max
    linarith [h_le_Hℚ, h_le_max_real]
  -- Step 3: Build the box precondition and apply global_theorem directly.
  rintro ⟨q, hq_near, hq_rupert⟩
  exact GlobalTheorem.global_theorem pbar εα εθ₁ εφ₁ εθ₂ εφ₂
    (Rat.cast_nonneg.mpr hεα) (Rat.cast_nonneg.mpr hεθ₁) (Rat.cast_nonneg.mpr hεφ₁)
    (Rat.cast_nonneg.mpr hεθ₂) (Rat.cast_nonneg.mpr hεφ₂) poly {
    Si := i
    w := toR2 pc.w
    w_unit := pc.w_unit
    exceeds := by
      have hG_le := Gℚ_le_G hεα hεθ₁ hεφ₁ hS_norm hS_approx pc.w_unit pc.p_in_4
      have hexceeds_real : ((Gℚ p εα εθ₁ εφ₁ (poly_.v pc.j) pc.w : ℚ) : ℝ) >
                            ((maxHℚ p poly_ εθ₂ εφ₂ pc.w : ℚ) : ℝ) := mod_cast pc.exceeds
      linarith [hG_le, hexceeds_real, h_maxH_le]
  } ⟨q, hq_near, hq_rupert⟩


/-! ## Scale-`10¹⁶` cast helper (used by the `Nat` fast path in `GlobalNat`) -/

namespace Gℚ_gt_maxHℚ

lemma abs_intCast_div16 (n : ℤ) :
    |(n : ℚ) / 10 ^ 16| = ((|n| : ℤ) : ℚ) / 10 ^ 16 := by
  rw [abs_div, abs_of_pos (by positivity : (0:ℚ) < (10:ℚ) ^ 16)]
  push_cast
  ring_nf

end Gℚ_gt_maxHℚ

end RationalApprox.GlobalTheorem
end
