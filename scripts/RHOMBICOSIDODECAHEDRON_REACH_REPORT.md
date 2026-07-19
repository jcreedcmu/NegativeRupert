# Rhombicosidodecahedron reach assessment

This note records the numerical evidence obtained on 2026-07-19 for applying
the balanced-support method to the unit-circumradius rhombicosidodecahedron.
It is evidence for proof design, not a formal certificate.

## Local failure regions

The pointwise SY25 audit failed on 118 of 5,000 Haar-random viewing
directions (2.36 percent).  The conservative axis-free balanced-support audit
succeeded on all 118:

    minimum sampled radius       0.05277270581
    median failure-region radius 0.06432187547
    constrained optimized radius 0.05109777266

At 33 exact high-symmetry directions where the SY25 audit failed, the
balanced radius was between `0.2006145597` and `0.2215731680`.  The working
constant `1/64 = 0.015625` therefore has a factor greater than three of
pointwise slack on the observed SY25 failure region.

## Global search

An exact-dual floating translation test was run on 100,000 Haar-random
five-dimensional poses:

    positive clearances (Rupert candidates)  0
    maximum random clearance                -0.002368288100
    median random clearance                 -0.03822038633

Twenty Nelder-Mead maximizations were started at the least-negative random
poses.  None found positive clearance.  Sixteen converged numerically to
zero-clearance boundary configurations.  A generalized balanced-support
first-variation audit at those sixteen configurations gave axis-free radii
between `0.04717899237` and `0.1503632161`.

The zero-clearance set includes two expected kinds of equality strata.  If
`G` is a proper symmetry, `Q=G` gives the same shadow.  If `G` is an improper
symmetry and `H_n` is reflection across the viewing plane, then

    Q = H_n G

is a rotation and `LQK = L K`.  Because the solid is centrally symmetric,
the second type can be represented by `Q=-H_n`.  A 5,000-view audit of this
reflection-derived stratum found positive balanced radii everywhere sampled;
the small values occur only while approaching the same silhouette seams
described below.

## Stitch stress test

The nonuniform seams were represented by two observed symmetry orbits:

* a coordinate-axis/high-symmetry failure;
* a golden-ratio vertex-difference failure.

For both the identity and reflection-derived equality strata, the test used:

* 24 tangent approach directions;
* 4 view distances: `1e-2`, `1e-3`, `1e-4`, `1e-5`;
* 17 values of rotation-angle/view-distance ratio from `1e-2` to `1e2`;
* 512 approximately uniform rotation axes.

This gives 3,342,336 scaled transition poses.  Every translation clearance
was nonpositive.  The smallest positive obstruction was

    9.54697432e-11,

at the smallest view distance and rotation ratio, in a branch where the SY25
theorem succeeds.  Its small absolute size is consistent with the expected
product scaling in the two small parameters; no sign loss was observed.

## Exact theorem still required

Pointwise open covers are insufficient because both an ordinary local margin
and an exact-support balanced margin can tend to zero on one side of a
silhouette seam, even though the balanced margin jumps upward at the exact
degenerate view.

A finite proof should use a transition leaf.  In abstract form, let `d` be
signed view distance from the seam and `x = tan(s/2)` measure relative
rotation.  It combines:

1. a regular exact-support bundle that works when `x <= k |d|`;
2. a central defect bundle whose support deficit is at most `D |d|` and whose
   axis-free first-variation radius is `c`;
3. the strong exact-support bundle on the other side of the seam.

For the defect bundle, Rodrigues gives a normalized lower bound of the form

    2 x (c-x) / (1+x^2) - D |d|.

Thus a simple sufficient overlap condition near the seam is `2 c k > D`.
If this conservative inequality is too weak for a selected four-certificate
bundle, the same compact transition link can instead be certified with the
exact second-order terms and a small polynomial case tree in `(direction,
x/|d|)`.  The 3.34-million-pose sweep is evidence that this link has no
unaccounted positive-clearance sector.

The next mathematical milestone is an interval-certified transition chart
for one representative of each seam orbit.  Once that exists, symmetry
transports it to every seam and removes the only presently identified local
stitching risk.

## Reproduction

* `experiment_rhombi_balanced.py` constructs the vertices, audits SY25, and
  computes balanced-support inradii.
* `rhombi_balanced_experiment.json` contains the 5,000-view local comparison.
* `experiment_rhombi_reach.py` implements the global and blown-up transition
  searches.
