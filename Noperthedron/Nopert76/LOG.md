# Nopert #76 non-Rupert program (started 2026-07-24)

Goal: formal proof that tom7's nopert #76 is not Rupert, or an explicit
Rupert configuration. Strategy mirrors the #214 program; its passage was
found via the failing proof, so the proof program doubles as the search.

## Passage search results so far (all negative)
- Coarse 900-point diagonal-pose sweep over the view fundamental domain
  (C5: theta in [0,72deg), phi in [0,90deg]): min first-order rate 1.4e-4,
  concentrated at the polar view. `scan_grid.json`, `scan76.py`.
- Silhouette-transition-curve sweep (240k views -> slack filter -> 600
  refined): min rate 3.3e-3 at funnel (1.031, 0.809). `scan_curves.json`.
- Drill-downs: funnel A floor 1.1e-3 at (1.0453, 0.7824); equator
  (0.9142, 1.5707) 1.2e-2; POLE (theta free, phi->0) floor 1.2e-5 — the
  danger spot: near-circular polar shadow. Finite-angle scan at the pole:
  min obstruction strictly positive at eps = 1e-4..1e-1 (as low as 3e-7
  at eps=1e-2, so certificates there must be sharp). `drill76.py`.
- CAVEAT: a #214-style needle (~1e-3 rad wide) could hide below this
  resolution; only the certificate searches can exclude it.

## Search infrastructure
- `scripts/nopert76_certificate_search.py`: wrapper installing #76 vertex
  tables (orbit-major, layout `VERTICES_Q[k*4+j] ~ Rz(2pi k/5) seed_j`)
  into the #214 machinery. STL audit passes (sha256 f257c3af...).
- 5e-16 vertex bound verified numerically for the unscaled model
  (max 2.96e-16, certified intervals).
- Local-view searches running for children 0-3:
  `local-view-child{0,1,2,3}.json`, target 51/10^9, tube radius 1e-7,
  max-nodes 60000, max-depth 26. 4000-node probes: zero failures,
  min margins 4.8e-7 / 3.5e-7 / 8.7e-8 / 8e-7 (child 2 = tightest,
  likely contains the pole). WATCH: failure clusters at depth cap with
  best_c null = passage signature (that is how #214 fell).
- TODO next: chart searches (generate-atlas-projective-table 0/1/2) once
  local children look stable; check FUNDAMENTAL_APPROXIMATION_ERROR
  (2/125000) is justified for #76 before trusting fundamental prunes.

## Lean port (Noperthedron/Nopert76/, 34 theory files + root)
- Copied from Nopert214 with namespace rename; excluded: Generated*,
  *Smoke*, FundamentalChart3 (regenerate from #76 searches later).
- KEY DESIGN: published #76 decimals overshoot the unit sphere by ~2e-16
  (max |v|^2 = 1.0000000000000002), violating GoodPoly.vertex_radius_le_one.
  Resolution: `seedVertex` holds seeds scaled by s = (10^15-1)/10^15
  (Rupert is similarity-invariant); `stlVertices`/`rationalVertex` stay
  the published decimals (checker model). Scaled-seed norms^2 <= 0.999...81.
- Consequence: published-vs-exact deviation grows to <= ~1.6e-15 in norm
  (9e-16 per coord). Tolerances to relax during the port:
  tightVertexErrorQ 5/10^16 -> 2/10^15 (and stl_tight_* chain), the
  Approximation.lean stl_taylor_sq_close bound, and the Python mirror's
  PROJECTIVE_LOCAL_VERTEX_ERROR must match the final Lean constant
  (regenerate/re-audit local tables if it changes after tables exist).
- Iterate: `lake build Noperthedron.Nopert76.<mod>`; failing decides
  identify the constants to bump; audit downstream slack for each bump.

## Remaining pipeline (after searches complete)
compaction -> pack emission -> constructNopert76 analogue (NativeExecutable
needs the same port) or generated native_decide tables -> final aggregator
mirroring `not_rupert_of_valid_tables`.

## 2026-07-24 (later): full Lean theory tree BUILDS
`lake build Noperthedron.Nopert76` — all 34 files, zero errors, including
the final bridge `not_rupert_of_valid_tables` for #76. Remaining work is
data + endgame mechanics only:
1. the four local-view tables (searches running),
2. chart tables 0-2 (searches not yet launched),
3. a FundamentalChart3 analogue (check how #214's 4-row table was emitted),
4. lakefile entries + root drivers for a constructNopert76 executable
   (NativeExecutable.lean is already ported),
5. emitter scripts accept --namespace, so Generated* emission should be
   reusable with Nopert76 names.

## Chart phase launched (2026-07-24 evening)
Locals: children 0 (5,297), 1 (27,905), 2 (40,673 — polar, hardest) all
COMPLETE with zero failures; child 3 finishing (~34k rows). Charts 0/1/2
launched DETACHED (disown — no completion notifications; check
chart{0,1,2}.json + chart*-run.log manually): #214-style settings, chart 0
tube radii 1/10^7 x4 pointing at the local tables. Caps 500k nodes.
Watch chart 0's origin region: pole obstruction rates ~3e-5 make it the
riskiest part of the whole program (possible radius ladder / stronger
certificates needed). Resume commands mirror #214's README with
nopert76_certificate_search.py.

## First chart-0 failure (2026-07-25, expected kind)
Cell id 21707: center ~1e-8 (origin), mismatch 1.098e-7 just OUTSIDE the
1e-7 tube; edge_lower +8e-9, global_lower -2.8e-8, shared_index 3. The
tube-boundary squeeze band. PLAN: when child 3 completes, raise per-region
tube radii to ~min(2*min_c_child)/1.1 (child mins: 4.78e-7/1.55e-7/6.2e-8/
TBD => e.g. 4/10^7, 3/10^7, 1.2/10^7, 4/10^7), port
nopert214_upgrade_chart0_tubes.py to import the 76 wrapper, migrate
chart0.json (radius INCREASE: stored tube rows stay valid, need radius
field update), resume — failures requeue automatically. Charts 1 (112k) and
2 (50k) failure-free.

## Local phase COMPLETE (2026-07-25); chart 0 resumed deeper
ALL FOUR local tables complete, zero failures: 5,297 / 27,905 / 40,673 /
60,385 rows (child 3 min c = 5.8e-8 — pins max region-3 tube radius at
~1.15e-7, too tight to be worth raising). Chart 0 therefore resumed with
radii unchanged (1e-7 x4) and DEEPER caps instead: --max-view-depth 18,
--min-relative-half-width 1/8192, 5 workers (chart0-run2.log). The
mismatch-1.1e-7 squeeze band subdivides until cells fall inside the tube;
prior failure requeued automatically on resume.

## PAUSED 2026-07-25 (user pivot to snub cube)
All searches stopped cleanly, locks free, zero failures program-wide.
State at pause: locals ALL COMPLETE (5,297/27,905/40,673/60,385);
chart0 ~122k rows/1,131 pending (deep origin tail, depths 1-11);
chart1 ~590k/325 (main octant done, siblings opening, cap now 1M);
chart2 ~290k/74 (two octants complete). To resume: the three
generate-atlas-projective-table commands in this README (chart0: view-depth
18, half-width 1/8192, radii 1/10^7 x4; chart1: 1M cap; chart2: 500k cap)
with --resume. Endgame checklist unchanged above.

## Chart 0 depth-18 interval-loss band (2026-07-26, #214-playbook fix)
25 failures at view-depth 18, mismatch 5.9e-3 (NOT tube), shared_index 3,
global_lower ~ -1.7e-8 (barely negative box bound) at the razor-wall
views. Same as #214 chart 1's depth-18 issue: pose-interval loss, not
geometry. Resumed with --min-relative-half-width 1/32768 (was 1/8192);
failures requeue.

## Razor-band chart fix: BOTH refinements required (2026-07-26)
Pose-space fit at both razor wall views: strongly positive at all scales
(rates 2.5e-2..2.4e-1; razor_fit.log) — NO passage; pure expressiveness.
Anatomy: razor point margins ~1.5e-4 at chart distances; view-depth-18
cells straddle the razor (view slack) AND half-width 1/8192 boxes carry
~1.2e-4 support slack (same order as the margin). Each refinement alone
fails (straddle-breeding at 227->426). Chart 0 now runs view-depth 22 +
half-width 1/32768 together. Local-leaf kind CANNOT rescue these cells:
tube inequality needs c ~ mismatch/2 ~ 3e-3, razor local floor is 3.4e-8.

## Razor-regime escalation gates opened (2026-07-26, engine change)
Chart 0's near-tube cells (mismatch < 1/20) were excluded from the WHOLE
escalation menu (cone5/6, audit4096, mixed_global — all chart-2-only or
tube-gated), a #214 design assumption (its razor lived inside the tube).
New `razor_retry` regime (near-tube AND widths <= 1/8192 AND view_depth
>= 14) re-enables the full menu, and audit4096/mixed gates now accept
chart 0. Failures 227->426->536 under pure subdivision were straddler
breeding; mixed certificates are the correct tool across the support
exchange. Chart 0 resumed on the new engine (run7).

## PAUSED 2026-07-28 (user needs the machine; all clean, zero failures)
State: chart2 COMPLETE+packed (798,214 rows, chart2.pack). Chart 0 paused
at ~393k rows / ~2,359 pending (shallow far-field wave draining; deep
razor band fully certified) — resume: the chart0-run7/8 command (view-
depth 22, half-width 1/32768, radii 1/10^7 x4, cap 700000, 5-9 workers).
Chart 1 paused at ~1.86M rows / ~420 pending (giant edge octant still
expanding) — resume: chart1-run2 command (view-depth 18, half-width
1/32768, cap 2M or 3M, 5 workers). Locals: ALL repaired to current
constants (69,436 certs refreshed, repair3.log) and packed; TABLE 0
NATIVELY VERIFIED post-repair; tables 1-3 packs ready, verification
partial (table 1 ~6k/15k) — the final constructNopert76 run re-verifies
everything anyway. Executable + chart-3 + tangent cones all built and
committed. Passage evidence: NONE anywhere (last check: active wave =
depth-2 far-field bulk). Remaining: finish charts 0+1, emit their packs,
run: lake exe constructNopert76 .artifacts/nopert76  (needs local-view
{0..3}.pack + chart{0,1,2}.pack in one dir).

## RESUMED 2026-07-28 (machine free again)
Chart 0 resumed (chart0-run9.log): same run7/8 settings — view-depth 22,
half-width 1/32768, radii 1/10^7 x4, cap 700000, 7 workers. Chart 1
resumed (chart1-run3.log): view-depth 18, half-width 1/32768, cap 3M,
5 workers. Local packs 1-3 native verification restarted niced in
parallel (NOTE: checkNopert76Local under `prlimit --as=17G` dies with
"failed to create thread" — run it WITHOUT prlimit; table 0 rate was
~2h/4k rows, so 1-3 take ~1-2 days; purely de-risking, the final
constructNopert76 re-verifies). Chart-pack emission confirmed to be
`scripts/nopert214_emit_packed_global.py <chart.json> <chart.pack>`
(vertex-independent encoding, same as chart2.pack).
FUNDAMENTAL_APPROXIMATION_ERROR TODO discharged: the 2/125000 allowance
is *proved* in AtlasFundamentalPrune.lean (fivefold trig coefficients
identical to #214), and chart0's 136 fundamental_prune rows each carry
an exact fundamental_audit row.

## PAUSED 2026-07-30 (user needs the machine; all clean, zero failures)
Stopped via SIGINT to the two search mains; checkpoint writes are atomic
(tmp + os.replace), both canonical JSONs validated after shutdown; the
interrupted chart1.json.tmp was deleted. State: chart0 480,032 rows /
2,119 pending (2.15GB json); chart1 2,562,992 rows / 396 pending
(2.45GB json). Local verification: tables 0+1 PASS natively; table 2
was ~29h into its run when killed (checkNopert76Local has no checkpoint
— restart from scratch, ~2 days niced; optional de-risking only).
Resume commands: chart0 = run9 settings (view-depth 22, half-width
1/32768, radii 1/10^7 x4, cap 700k, 7 workers); chart1 = run3 settings
(view-depth 18, half-width 1/32768, cap 3M, 5 workers); both --resume.
`scripts/nopert76_status.py [--deep]` = one-shot status + pending
autopsy for anyone at the keyboard.

## Passage-suspicion audit 2026-07-30 (all negative, sharpest yet)
Pending-age analysis of chart0's flat ~2.1-2.4k queue: 150 cells are
UNSTARTED root-enumeration backlog (ids 30-199, depth 1-2), ~1.9k are
one two-day-old depth-4/5 far-field wave; nothing deep, nothing
retried, zero failures ever. Direct drill76 LP hill-descent at the 5
persistent view clusters + the 2 oldest pending views: ALL POSITIVE,
worst +4.1e-3 (cluster-A, which converged to the known funnel A);
others 4e-2..1.9e-1. Passage scale would be ~1e-5. No suspicious
region anywhere in the program.

## Restart procedure gotcha 2026-08-02 (flock, learned the hard way)
Each generator holds an exclusive flock on chartN.json.lock for its
whole lifetime, and pool workers inherit the lock fd. After SIGTERM,
"pgrep shows nothing" is NOT sufficient to relaunch: during the gmpy2
rollout both relaunches died with "another generator is already
writing" because a lock holder outlived the pgrep check (parent
finishing a multi-GB checkpoint dump / workers still unwinding).
Correct sequence: (1) wait for fresh chartN.json mtime, (2) SIGTERM
parent + workers, (3) WAIT UNTIL THE LOCK IS FREE:
  until flock -n .artifacts/nopert76/chartN.json.lock true; do sleep 5; done
then relaunch. Checkpoints stayed intact throughout (atomic replace);
a kill mid-dump just loses that dump's rows back to the previous
checkpoint.

## Root-cell audit 2026-08-13 (all negative; pole rediscovered)
Probed the 29 unopened chart-0 root cells at all triangle corners +
centroids (116 seeds) with descents from the worst 6
(`drill76_root_audit.py`, results `drill76_root_audit.json`). Eight
roots (ids 66/67/72/73/78/79/84/85) share the EXACT POLE as corner2;
those seeds floor at 0.98-1.4e-5 — replicating the known July pole
floor (1.2e-5, strictly positive at finite angles, min 3e-7 at
eps=1e-2; polar pose tube already certified by local table 2). All 108
non-pole seeds floor at 3.63e-2. No new passage evidence anywhere.
Expect the 8 pole-tipped roots to subdivide deep at their tips (origin
squeeze-band treatment) — schedule cost, not risk.

## gmpy2 backend 2026-08-02 (commit 744df89)
NOPERT_GMPY2=1 (exported by nopert76_resume.sh) swaps Fraction for
gmpy2.mpq in all three search scripts. Measured on identical replays:
1.28x end-to-end on a chart1 fat cell, 1.20x on chart0's deep wave
tail; zero failures, identical row mixes, checkpoint format unchanged
(str(mpq) == str(Fraction)). Soundness unaffected: Lean re-verifies
every row. Wave per-row cost is dominated by local-certificate rows
(~12s) and failed-cascade view_split rows (~12s); edge rows are ~60ms.
chart0 --max-nodes raised 700k -> 2M (was about to hit the old cap).
