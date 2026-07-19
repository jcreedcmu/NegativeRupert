# Balanced-support mathematics for the snub cube

This note isolates the new mathematics needed for a formal non-Rupert proof.
It deliberately separates general theorems from the finite snub-cube
certificate search.

## 1. Translation-cancelling support certificates

Let `K` be a compact convex subset of `R^3`, let

    L : R^3 -> R^2

be an orthogonal projection written in coordinates (`L L^* = id`), and let
`Q` be a rotation.  The outer and inner shadows are `L K` and `L Q K`.

Choose nonzero directions `u_i in R^2`, weights `mu_i >= 0`, and points
`v_i in K` such that

    sum_i mu_i u_i = 0.                                      (balance)

Define

    C(L,Q) = sum_i mu_i <u_i, L(Q-I)v_i>.

### Balanced-support obstruction theorem

Assume every `v_i` supports the outer shadow in direction `u_i`:

    <u_i, L v_i> = h_{L K}(u_i).

If `C(L,Q) >= 0` and at least one `mu_i` is positive, then no translate of
`L Q K` is strictly contained in `L K`.

### Proof

If `t + L Q K` were contained in the interior of `L K`, then, for every `i`
with positive weight,

    <u_i, t + L Q v_i> < h_{L K}(u_i) = <u_i, L v_i>.

Multiply by `mu_i` and sum.  The translation term is

    <sum_i mu_i u_i, t> = 0,

so the strict inequalities give `C(L,Q) < 0`, a contradiction.

This theorem is valid for arbitrary compact convex bodies.  For a polytope it
is enough to check the support inequalities against its vertices.

In the plane, if a translation is infeasible, Farkas/Helly theory gives such
a certificate with at most three directions.  Thus three-contact leaves are
complete for each fixed pair of polygonal shadows.

## 2. Producing balanced directions from three projected support pairs

For vectors `u_1,u_2,u_3 in R^2`, set

    mu_1 = det(u_2,u_3),
    mu_2 = det(u_3,u_1),
    mu_3 = det(u_1,u_2).

The two-dimensional Grassmann identity gives

    mu_1 u_1 + mu_2 u_2 + mu_3 u_3 = 0.                    (1)

If the three directions positively span the plane in cyclic order, all three
weights are positive.  This avoids storing or solving for balancing weights:
a checker can recompute them from the directions, and (1) holds identically
as the outer viewing direction varies.

Choose two vertices `a_i,b_i` that lie on the same supporting line after
projection, and define the projected oriented normal

    u_i(L) = sigma_i J L(b_i-a_i),   sigma_i in {+1,-1},

where `J` is rotation through 90 degrees in the projection plane.  The pair
defines a supporting projected line precisely when

    <u_i(L), L(v-a_i)> <= 0

for every vertex `v` of the polytope.  Both vertices then attain the support
value for every `L` for which these inequalities hold.  Generically the pair
is an actual silhouette edge.  At a degenerate view it may instead be any two
distinct support vertices; the theorem needs only the displayed inequalities,
not adjacency in the three-dimensional edge graph.  Consequently the
baseline certificate remains exactly zero as `L` varies through an entire
silhouette regime; it does not suffer an `O(view-box-width)` loss.

This dependence on `L` is important.  Holding a center-pose normal fixed would
make a selected endpoint cease to be supporting under an arbitrarily small
change of view, preventing a local theorem from covering all rotations close
to the equality stratum.

### Coordinate-free form

Let `n` be the oriented unit viewing normal, and absorb `sigma_i` into the
oriented chord

    e_i = sigma_i (b_i-a_i).

For an oriented orthonormal projection frame, two elementary identities are

    L^* J L e_i = n x e_i,
    det(J L e_i, J L e_j) = <n, e_i x e_j>.

Thus the support inequalities become the linear conditions

    <n, e_i x (v-a_i)> <= 0,

and the determinant weights become

    mu_1 = <n, e_2 x e_3>,
    mu_2 = <n, e_3 x e_1>,
    mu_3 = <n, e_1 x e_2>.                               (CF)

This eliminates the arbitrary in-plane projection frame completely.  A
silhouette regime is a spherical polygon cut out by linear inequalities in
`n`; the weights are also linear in `n`.

## 3. A finite-rotation local rigidity theorem

Normalize the polytope so every selected vertex has norm at most one.  Let
`omega` be a unit vector and let `Q = Rot(omega,s)` be rotation through
`0 <= s < pi` about `omega`.

For a balanced supporting certificate define three-dimensional lifted
directions

    d_i = L^* u_i,

the first-variation vector

    A_vec = sum_i mu_i (v_i x d_i),

and the remainder bound

    B = sum_i mu_i ||d_i|| ||v_i||.

Since `L L^* = id`, `||d_i|| = ||u_i||`.

Rodrigues' formula says

    (Q-I)v = sin(s) (omega x v)
              + (1-cos(s)) (omega x (omega x v)).

Using

    <d, omega x v> = <omega, v x d>

and `||omega x (omega x v)|| <= ||v||` gives

    C(L,Q)
      >= sin(s) <omega,A_vec> - (1-cos(s)) B.              (2)

For interval certification it is useful to replace `B` by the larger bound

    Bbar = sum_i mu_i ||e_i|| ||v_i||,

because `||n x e_i|| <= ||e_i||`.  The sufficient inequality

    <omega,A_vec> >= c Bbar                              (Poly)

has no square roots depending on the box variables.  Indeed, by (CF), each
`mu_i` is linear in `n`, while

    A_vec = sum_i mu_i (v_i x (n x e_i))

is quadratic in `n`; its inner product with `omega` is linear in `omega`.
After the fixed vertex and edge lengths are bounded once, (Poly) is a
degree-three polynomial inequality in `(n,omega)`.  It is slightly weaker
than using the exact `B`, but far easier to certify and still retains ample
slack in the experiments below.

### Local balanced-support rigidity theorem

Under the balance and support assumptions above, suppose `B > 0` and

    <omega,A_vec> / B >= c > 0.

If

    tan(s/2) <= c,

then no translate of `L Q K` is strictly contained in `L K`.

### Proof

For `0 < s < pi`, divide the right side of (2) by `sin(s) B` and use

    (1-cos(s))/sin(s) = tan(s/2).

The hypotheses imply `C(L,Q) >= 0`, so the balanced-support obstruction
theorem applies.  At `s=0`, `C(L,I)=0`, which already contradicts strict
containment.

The theorem is exact for a finite rotation; it is not merely an asymptotic
first-order argument.

## 4. Eliminating the rotation axis from the certificate tree

For one viewing normal, suppose we have finitely many balanced-support
certificates indexed by `j`.  Write their first-variation vectors and
conservative remainder bounds as `A_j` and `Bbar_j`, and set

    a_j = A_j / Bbar_j.

Assume the convex hull of the `a_j` contains the closed radius-`c` ball about
the origin.  Then for every unit vector `omega`,

    c = <omega,c omega> <= max_j <omega,a_j>.

Consequently some `j` satisfies

    <omega,A_j> >= c Bbar_j >= c B_j,

and the finite-rotation local theorem applies whenever `tan(s/2) <= c`.

### Axis-free balanced-support rigidity theorem

Under the preceding convex-hull hypothesis, no nonzero rotation through an
angle satisfying `tan(s/2) <= c`, about *any* axis, can produce a strictly
contained translated shadow.

By Caratheodory's theorem, four vectors suffice to contain the origin, though
four arbitrary vectors need not retain the full radius.  Experimentally, at
every hard snub-cube view checked so far, four certificate vectors form a
tetrahedron whose centered inradius equals the inradius of the convex hull of
all hundreds of candidates.  A local row can therefore store four contact
triples and cover every rotation axis.  This reduces the new local certificate
tree from four variables `(view,axis)` to the two viewing variables alone.

For four points `a_0,...,a_3`, the centered inradius has a direct algebraic
test.  The distance from the origin to the face opposite `a_i`, with the other
indices `j,k,l`, is

    |det(a_j,a_k,a_l)|
    / ||(a_k-a_j) x (a_l-a_j)||.

The signs of the four barycentric determinants prove that the origin is
inside the tetrahedron; squaring the four distance inequalities proves that
it contains the radius-`c` ball.  Substituting `a_i=A_i/Bbar_i` and clearing
the positive denominators gives polynomial inequalities suitable for an
interval checker.

## 5. Symmetry strata

Let `G` be a rotational symmetry of `K`.  If the relative inner/outer rotation
is `Q` near `G`, write

    Q = E G,   E = Q G^{-1}.

Because `G K = K`, one has `Q K = E K`.  Therefore every symmetry stratum
reduces to the identity case above, with the vertices merely reindexed by
`G`.  A formal proof only needs the local theorem around `I`, plus a finite
symmetry lookup.

## 6. The finite snub-cube certificate problem

For the unit-radius snub cube `K`, define `gamma(L,omega)` as the maximum of

    <omega,A_vec> / B

over certificates consisting of at most three oriented supporting projected
lines and a choice of one supporting vertex for each line.  Away from
silhouette transitions, each line comes from a silhouette edge and the chosen
vertex is normally one of its endpoints.  At a transition, the chosen support
vertex need not be an endpoint of the pair used to define the normal.

The initially proposed mathematical target was

    gamma_* = inf_{L,omega} gamma(L,omega) > 0,             (3)

where `L` ranges over viewing directions modulo rotational octahedral
symmetry and `omega` ranges over the unit sphere.

The analytic experiment computes exactly this piecewise-algebraic first
variation (up to floating arithmetic).  Its initial results were:

* 5.12 million unrestricted `(L,omega)` pairs: minimum `0.008155`;
* nonsmooth optimization: repeated symmetry-equivalent minima near `0.006683`;
* 5.12 million pairs restricted to views where the existing Local Theorem
  fails: minimum `0.027407`;
* optimization on that restriction: approximately `0.02589`.

Further axis-free optimization found that the uniform claim (3) is false.
Near the silhouette transition

    n approximately (0.283472441, -0.958980383, 0),

the inradius tends to zero from one side, even though it jumps to a large
value at the exactly degenerate view when extra support lines appear.  The
existing Local Theorem succeeds on that side, with a margin that also tends
to zero at the transition.

The viable target is therefore the hybrid disjunction

    ExistingLocal(n)  OR  axisFreeRadius(n) >= 1/64.

An exact minimization over the rotation axis followed by constrained
view-normal optimization gives a smallest observed conservative axis-free
radius of

    0.01821295248

on the pointwise failure set of the existing Local Theorem.  This is above
`1/64 = 0.015625`; four certificates retain the full radius at the optimizer.
The corresponding guaranteed relative-rotation radius is

    2 atan(1/64) > 0.03124 radians.

However, the pointwise disjunction alone is not yet an interval theorem.  On
one side of the transition both its margins approach zero.  A finite box cover
needs a transition-aware strengthening (Section 9), rather than infinitely
refining ordinary local boxes toward the transition.

For reference, the earlier candidate constants were

    gamma(L,omega) >= 1/256              (uniform target),

or the hybrid disjunction

    ExistingLocal(L)  OR  gamma(L,omega) >= 1/64.

The corresponding guaranteed relative-rotation radii are

    2 atan(1/256) > 0.00781 radians,
    2 atan(1/64)  > 0.03124 radians.

The global `1/256` target must now be discarded.  The hybrid `1/64` target has
about 16.6 percent pointwise slack at the optimized conservative minimum.

## 7. What a local certificate row stores

A practical axis-free row for an outer-view box needs four copies of:

1. three oriented outer support pairs `(a_i,b_i,sigma_i)`;
2. one chosen supporting vertex `v_i` for each pair;
3. bounds proving each pair and chosen vertex remain supporting over the view
   box;
4. bounds proving the determinant weights remain positive;
5. the polynomial vectors `A_j` and bounds `Bbar_j`;

and one tetrahedron check proving that the four `A_j/Bbar_j` contain the
radius-`1/64` ball.  No rotation-axis coordinates occur in the row.

No translation, support-maximizing vertex search, normalized line normal, or
floating balancing weight belongs in the certificate.  All relevant
expressions are polynomial in the projection-matrix entries and the vertex
coordinates, apart from the final elementary trigonometric bounds already
handled elsewhere in the project.

## 8. Silhouette transitions

At a view where the projected silhouette changes, the set of supporting edges
changes discontinuously.  This does not create a geometric zero.  In the
observed hard Local-Theorem-failure regime, approaching a transition from a
nine-edge silhouette gives ratios near `0.026`, while the exact transition
has ten edges and a much better ratio near `0.12`.

The formal certificate tree should partition silhouette regimes and allow
multiple supporting edges on transition boxes.  It should not attempt to
differentiate a single chosen hull representation through the transition.

## 9. The transition theorem still needed

The newly discovered zero is a nonuniform first-variation phenomenon, not
evidence for a Rupert pose.  Let `d` denote signed distance of the view from
the transition and `s` the relative rotation angle.  On the problematic side,
an exact-support first-variation margin behaves like `d s`; hence it works in
the wedge `s << d`.  A support vertex that becomes active at the transition
has an outer-support deficit of order `d` but a rotation gain of order `s`, so
an approximate-support/global certificate works in the complementary wedge
`s >= C d`.

The relevant generalization of the obstruction theorem allows support
deficits

    r_i = h_{LK}(u_i) - <u_i,Lv_i> >= 0.

The same weighted-sum proof shows that strict containment is impossible if

    sum_i mu_i <u_i,L(Q-I)v_i> >= sum_i mu_i r_i.          (Defect)

At a silhouette transition, a finite theorem should combine:

1. exact-support certificates for the small-angle wedge;
2. a defect certificate of form (Defect) when rotation dominates distance to
   the transition;
3. the strong exact certificates on the other silhouette side.

This is the main remaining piece of new mathematics.  It should be a local
case split between polynomial inequalities in `(d,s)`, rather than another
high-dimensional solution tree.

## 10. Remaining mathematical questions

The obstruction, finite-rotation, coordinate-free, and axis-free theorems
above are elementary and should formalize directly.  Explicit payload
extraction now reproduces the numerical LP witnesses to about `5e-15` over
10,000 tests.  The remaining substantive tasks are:

1. formulate and test the transition theorem of Section 9;
2. certify the hybrid `ExistingLocal OR axisFreeRadius>=1/64` statement away
   from transition neighborhoods with a two-dimensional view tree;
3. replace floating snub-cube coordinates by their exact algebraic model and
   clear the tetrahedron denominators.
