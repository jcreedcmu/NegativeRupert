# Snub-cube non-Rupert reconnaissance

Run date: 2026-07-18.

This is numerical evidence and proof-architecture reconnaissance, not a
formal proof.

## Geometry and translation elimination

`experiment_snub_cube.py` constructs one chirality of the standard snub cube
from the tribonacci constant.  Sanity checks recover 24 vertices, 60 shortest
edges, 44 triangulated hull facets (32 triangular faces plus two triangles for
each of 6 squares), and all 24 rotational octahedral symmetries.

For each five-parameter pair of projections, the script solves the planar
translation problem by its LP dual.  If `A` is the outer projection and `B`
the inner projection, a strict translated containment would imply

    h_B(u_j) + u_j . t < h_A(u_j).

Nonnegative weights whose directions balance to zero eliminate `t`.  In two
dimensions an extreme dual certificate uses at most three directions, so the
script enumerates every pair and triple of outer edge normals.  Comparison
against SciPy/HiGHS on 100 random poses agreed to `1.2e-16`.

## Main numerical results

* 20,000 Haar-random five-dimensional poses: no positive translation
  clearance.  Every pose had a width obstruction in this sample.
* 35,000 arbitrary coordinate perturbations around equality strata: every
  pose had a three-contact obstruction.  Width failed once.
* 25,000 pure relative rotations around equality strata, at rotation sizes
  from `1e-2` through `1e-6`: every pose had a width obstruction and a
  three-contact obstruction.
* Optimizing the largest clearances from the hardest random poses drove 13 of
  16 starts numerically to exact rotational-symmetry/equality strata with
  clearance zero.  The remaining starts stopped at negative clearance.

Width is not sufficient globally.  Optimizing the observed width failure
produced a pose with width margin `-6.778983940705086e-4`: the inner difference
polygon lies strictly inside the outer difference polygon.  Nevertheless its
translation clearance is `-6.578995561843611e-3`, certified by three normals
with weights approximately `(0.28248, 0.28065, 0.43687)`.  Thus a formal tree
really does need asymmetric three-contact leaves.

## Second-order box sizes

The script also sums two or three copies of the same anisotropic second-order
Taylor bounds used by the current Global Theorem.  On 2,000 random poses, the
isotropic five-coordinate half-widths in radians were:

| certificate | 1% | median | 99% |
| --- | ---: | ---: | ---: |
| width | 0.02053 | 0.05842 | 0.11433 |
| three-contact | 0.03352 | 0.07381 | 0.11441 |
| better of the two | 0.03424 | 0.07424 | 0.11489 |

Three-contact certificates gave the larger box on 77.3% of samples.  The
median best half-width is about 4.25 degrees.  This is compatible with a
manageable adaptive tree after octahedral symmetry reduction, although it is
not a tree-size estimate and the radii collapse at equality strata.

## Existing Local Theorem audit

`experiment_snub_local.py` tests the epsilon-to-zero hypotheses of the current
Local Theorem at equality poses.  It searches every vertex triple for the
same-side (`A`), projected-spanning, and strict locally-maximally-distant (`B`)
conditions.

* 100,000 random viewing directions: success at 92.076% of directions.
* It fails at coordinate-axis and face-diagonal views and at many exact
  vertex-difference directions.

Consequently the current Local Theorem is insufficient for a complete snub
cube proof.  The failure is not confined to measure-zero degeneracies: about
7.9% of generic random views fail its pointwise hypotheses.

The balanced-support local behavior is much better.  Small relative rotations
were tested directly at coordinate-axis, face-diagonal, body-diagonal, and a
generic Local-Theorem-failure view.  No width or three-contact failure was
seen.  At rotation size `1e-5`, the minimum observed obstruction divided by
the rotation angle was:

| outer view | width | three-contact |
| --- | ---: | ---: |
| coordinate axis | 0.694 | 0.694 |
| face diagonal | 0.609 | 0.625 |
| body diagonal | 0.395 | 0.513 |
| generic Local failure | 0.157 | 0.198 |

This suggests replacing or supplementing the triangle/LMD Local Theorem with
a local balanced-support rigidity theorem around the rotational-symmetry
strata.

## Reproduction

```text
.venv/bin/python scripts/experiment_snub_cube.py \
  --samples 20000 --near-per-scale 500 \
  --optimize-starts 16 --optimize-iters 1600

.venv/bin/python scripts/experiment_snub_cube.py \
  --samples 5000 --near-per-scale 0 --cone-per-scale 0 \
  --optimize-starts 0 --box-samples 2000 \
  --out scripts/snub_cube_box_experiment.json

.venv/bin/python scripts/experiment_snub_local.py --random 100000
```

The saved JSON outputs contain summaries and representative hard poses.

## Continuation: analytic local rigidity and tree scale

`experiment_snub_rigidity.py` computes the one-sided first variation at an
equality pose analytically.  Its variables are the two-dimensional outer view
and the two-dimensional unit relative-rotation axis.  It handles the support
function's exposed-edge nondifferentiability by maximizing over all active
vertices, then enumerates every extreme point of the balanced translation-LP
dual.  Against finite differences at step `1e-7`, the maximum absolute error
over 100 tests was below `5.1e-8` after division by the step size.

On 5,000 views times 1,024 axes (5.12 million pairs):

* the width derivative became negative, with sampled minimum `-0.01562`;
* the three-contact derivative was positive everywhere, with sampled minimum
  `0.008155`;
* nonsmooth optimization from the 16 hardest starts converged to symmetry-
  equivalent minima near `0.006683`, never to zero.

The optimized hard view has absolute coordinate pattern approximately
`(0.20984, 0.53258, 0.81995)`.  The repeated coordinate permutations and sign
changes among optimizer outputs are a useful check that octahedral symmetry is
being respected.

A separate rejection sample selected 5,000 views where the existing Local
Theorem fails and again checked 1,024 axes per view.  The sampled minimum was
`0.027407`; optimization reduced it only to about `0.02589`.  Thus the hybrid
strategy does not need the new theorem at the unrestricted worst case: the
weak `0.00668` configurations already satisfy the existing Local Theorem,
while its complement appears to have almost four times the first-order gap.

The hard failure views approach a projected-silhouette transition near a
vertex-difference direction with coordinate pattern `(0, 0.959, 0.283)`.  The
gap does **not** vanish at the exact transition: the projected hull gains an
edge and the best three-contact derivative jumps upward to about `0.12`.
Approaching from the adjacent nine-edge regime gives values around `0.026`;
the ten-edge regime is much easier.  A formal local checker should therefore
partition by silhouette regime rather than try to use one differentiable
formula across the transition.

### Cover-size estimate

The 10,000-pose second-order box run gave best isotropic half-width quantiles
`0.03419` (1%), `0.07404` (median), and `0.11555` (99%).  A simple variable-
radius covering-density estimate is dominated by the hardest 0.1% of samples.
On the tightly tiled Euler-coordinate fundamental region described below it
gives roughly 0.31 million global leaves; removing the most extreme 0.1% gives
about 0.095 million.  Using the simple rectangular over-cover instead raises
the untrimmed estimate to about 1.0 million.  Those extremes cannot simply be
discarded; they indicate where local leaves and adaptive anisotropic splitting
matter.

For calibration, the current Noperthedron tree has 1,139,083 leaves and an
equivalent uniform half-width `0.03770` over root coordinate volume `2.7743`.
For the rotational octahedral group, one convenient chiral fundamental region
for a view vector is `x >= y >= |z|`, `x,y >= 0`.  In the current spherical
coordinates this is

    0 <= theta <= pi/4,
    |phi-pi/2| <= atan(sin(theta)).

Its `(theta,phi)` coordinate area is about `0.54259`.  Using it independently
for the inner and outer viewing directions and retaining the full `2*pi`
in-plane angle gives an effective five-coordinate root volume about `1.85`,
smaller than the Noperthedron's `2.77`.  Covering each curved chamber by its
simple bounding rectangle gives volume `5.87`; inexpensive domain-exclusion
leaves should recover most of the factor between them.  Combining this range
with the measured radii suggests approximately:

* 0.3--1 million leaves in a tightly domain-pruned implementation;
* roughly 0.6--2 million total binary-tree rows;
* likely no larger than the present Noperthedron tree, with a reasonable chance
  of being materially smaller after anisotropic splitting and local leaves.

This is not yet an emitted adaptive tree.  It is a scale estimate; the main
uncertainties are fundamental-domain boundary overhead, the hard-tail measure,
and how large a neighborhood the new local rigidity theorem certifies.

On the ten hardest global samples, optimizing anisotropic radii increased the
volume-equivalent half-width by factors around 1.05--1.31 (a volume gain up to
about 3.7).  Searching all balanced dual extreme points sometimes improved a
box substantially, but did not improve the single hardest sample.

### Formal-work implications

The remaining ingredients are now fairly sharply separated:

1. **Balanced-support theorem:** mathematically elementary.  Sum two or three
   support inequalities with nonnegative weights whose directions total zero;
   the unknown planar translation cancels.  The repository already models the
   translation in `MatrixPose`, so this replaces the use of `CommonCenter`
   rather than changing Rupert's definition.
2. **Algebraic vertices:** the tribonacci coordinate is cubic rather than
   rational.  A practical checker can use rational proxy vertices plus a
   formally proved rational enclosure for the unique root of
   `t^3-t^2-t-1`; the resulting error is negligible numerically but requires a
   new vertex-error layer in Lean.
3. **Octahedral symmetry reduction:** routine group mathematics, but more
   elaborate than the Noperthedron's cyclic angular restriction because a
   rotational-octahedral fundamental region is a union of chiral spherical
   chambers.
4. **Local balanced-support rigidity:** the only genuinely new geometric
   theorem.  Numerically it has a strong gap exactly where the old Local
   Theorem fails.  It can likely be formulated using cones in the entries of
   the relative rotation matrix, avoiding a formally awkward normalized
   axis-angle logarithm.
5. **Fallback:** polynomial/Bernstein nonnegativity leaves around any residual
   zero strata.  The present experiment found no non-symmetry zero stratum.
