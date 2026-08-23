"""v8 probe: can heavy NO-LOCAL v7 cells shrink if the local-certificate
candidate pool is widened from "this cell's own local leaves" (empty for
these cells, by v5-inherited construction) to a GLOBAL pool of all v7 local
payloads, ordered by pose distance?

Identical greedy build to make_solution_tree_v7.build_cell2 except:
  * candidate pool = all v7 local leaves anywhere in the table;
  * the local tiers fire when the nearest pool payload's home box center is
    within --pool-radius cell-widths (max-norm) of the current box, instead
    of requiring home-box intersection.

Usage:
  python v8_probe.py [--min-rows 200] [--max-cells N] [--workers 12]
                     [--pool-radius 4.0] [--out v8_probe_results.json]
"""
import argparse
import json
import multiprocessing as mp
import os
import sys
import time

import numpy as np

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import make_solution_tree_v5 as v5
import make_solution_tree_v6 as g6
import experiment_aniso as ea
from local2_check import check_local2

LOCAL2_TRY_CAP = 48
LOCAL2_EPS_SKIP = 0.08
NEAR_CAP = 512            # pool rows handed to the tier-1 vectorized check
POOL_RADIUS = 4.0         # cell-widths: gate for attempting local tiers
LCEN2 = None              # (m,5) home-box center*2 of every pool leaf
CELL_SIDE = None          # (5,) depth-5 cell side lengths in grid units


def build_cell2_pool(cid):
    cid = int(cid)
    v7_count = int(g6.CNT[cid])
    if g6.NT[cid] != 3:
        return cid, ("copy", "leafcell")
    t0 = time.time()
    lo0 = g6.BMIN[cid].copy()
    hi0 = g6.BMAX[cid].copy()
    g0 = np.searchsorted(g6.GKEY, cid, "left")
    g1 = np.searchsorted(g6.GKEY, cid, "right")
    grows = g6.GROWS[g0:g1]
    lbmin, lbmax = g6.BMIN[grows], g6.BMAX[grows]
    lwin = np.stack([g6.SIDX[grows], g6.WXA[grows], g6.WYA[grows],
                     g6.WDA[grows]], axis=1)

    scans = 0
    nodes = []
    st = dict(n_leaf_g=0, n_leaf_l=0, n_leaf_l2=0, n_split=0, l2_tries=0)
    stack = [(lo0, hi0, None, 0)]
    while stack:
        if len(nodes) + len(stack) >= v7_count:
            return cid, ("copy", "rows")
        if scans >= g6.MAX_SCANS:
            return cid, ("copy", "scans")
        lo, hi, res, dep = stack.pop()
        scans += 1
        center = (lo + hi) / (2 * g6.DENOM)
        e = (hi - lo) / (2 * g6.DENOM)

        # ---- staged global certificate (identical to v6/v7)
        if len(lwin):
            m = ((lbmin <= hi) & (lbmax >= lo)).all(axis=1)
            seeds = lwin[m]
        else:
            seeds = lwin
        if len(seeds):
            u, cts = np.unique(seeds, axis=0, return_counts=True)
            if len(u) > g6.SEED_CAP:
                u = u[np.argsort(-cts)[:g6.SEED_CAP]]
            seeds = u
        if res is not None:
            seeds = np.concatenate([seeds, res]) if len(seeds) else res
        witness = None
        if len(seeds):
            sl = ea.eval_pairs(center, e, seeds)
            j = int(sl.argmax())
            if sl[j] >= g6.SLACK_MIN:
                witness = tuple(int(x) for x in seeds[j])
        if witness is None:
            w3 = ea.COARSE_W
            angs = ea.COARSE_ANG
            if len(seeds):
                sw = np.unique(seeds[:, 1:4], axis=0)
                w3 = np.concatenate([w3, sw])
                angs = np.concatenate([angs, np.arctan2(sw[:, 1], sw[:, 0])])
            slack, comps = ea.aniso_grid(center, e, w3)
            A = slack.shape[1]
            flat = slack.ravel()
            jb = int(flat.argmax())
            if flat[jb] >= g6.SLACK_MIN:
                s, c = jb // A, jb % A
                witness = (int(s), int(w3[c, 0]), int(w3[c, 1]), int(w3[c, 2]))
            else:
                order = np.argpartition(-flat, 63)[:64]
                order = order[np.argsort(-flat[order])]
                cols = np.unique(order % A)[:g6.REFINE_TOP]
                ra = (angs[cols][:, None] + ea.REFINE_DEL).ravel()
                ra = np.arctan2(np.sin(ra), np.cos(ra))
                rw = np.stack(v5.pythag(ra), axis=1)
                slack2, _ = ea.aniso_grid(center, e, rw)
                flat2 = slack2.ravel()
                j2 = int(flat2.argmax())
                if flat2[j2] >= g6.SLACK_MIN:
                    s, c = j2 // len(rw), j2 % len(rw)
                    witness = (int(s), int(rw[c, 0]), int(rw[c, 1]),
                               int(rw[c, 2]))
        if witness is not None:
            nodes.append((1,) + witness)
            st["n_leaf_g"] += 1
            continue

        # ---- GLOBAL POOL: nearest local payloads by pose distance
        drel = (np.abs(LCEN2 - (lo + hi)) / (2.0 * CELL_SIDE)).max(axis=1)
        dmin = float(drel.min()) if len(drel) else np.inf
        loc_isect = dmin <= POOL_RADIUS
        got = None
        if loc_isect and float(e.max()) <= g6.LOCAL_EPS_SKIP:
            near = np.argsort(drel, kind="stable")[:NEAR_CAP]
            near = near[drel[near] <= POOL_RADIUS]
            got = g6._try_local(center, float(e.max()), lo, hi, near)
        if got is not None:
            pay, _ = got
            nodes.append((2,) + pay)
            st["n_leaf_l"] += 1
            continue

        # ---- tier 2: second-order over the same pool ordering
        if loc_isect and float(e.max()) <= LOCAL2_EPS_SKIP:
            order2 = np.argsort(drel, kind="stable")
            seen = set()
            hit = None
            tried = 0
            for j in order2:
                if drel[j] > POOL_RADIUS:
                    break
                pay = tuple(int(x) for x in g6.LOCPAY[j])
                key = pay[0:6] + (pay[7],)          # (P, Q, sigma), ignore r
                if key in seen:
                    continue
                seen.add(key)
                tried += 1
                st["l2_tries"] += 1
                P = ea.VERTS[list(pay[0:3])]
                Q = ea.VERTS[list(pay[3:6])]
                sl2, r_prime = check_local2(center, e, P, Q, pay[7], ea.VERTS)
                if r_prime > 0 and sl2 > 3e-9:
                    hit = pay[0:6] + (r_prime, pay[7])
                    break
                if tried >= LOCAL2_TRY_CAP:
                    break
            if hit is not None:
                nodes.append((2,) + hit)
                st["n_leaf_l2"] += 1
                continue

        # ---- split (identical to v6/v7)
        contrib = ea.axis_contrib(e, comps, jb // A, jb % A)
        sides = hi - lo
        even = (sides >= 2) & (sides % 2 == 0)
        contrib[~even] = -np.inf
        if loc_isect:
            key = np.where(even, sides, -1)
            best = key.max()
            ax = int(np.argmax(np.where(key == best, contrib, -np.inf)))
        else:
            ax = int(np.argmax(contrib))
        if dep >= g6.DEPTH_CAP or not np.isfinite(contrib[ax]):
            return cid, ("copy", "nosplit")
        top = order[:g6.RESERVOIR_K]
        res_rows = np.stack([top // A, w3[top % A, 0], w3[top % A, 1],
                             w3[top % A, 2]], axis=1).astype(np.int64)
        mid = (int(lo[ax]) + int(hi[ax])) // 2
        hi1 = hi.copy(); hi1[ax] = mid
        lo2 = lo.copy(); lo2[ax] = mid
        nodes.append((3, ax))
        st["n_split"] += 1
        stack.append((lo2, hi, res_rows, dep + 1))
        stack.append((lo, hi1, res_rows, dep + 1))
    st["scans"] = scans
    st["seconds"] = round(time.time() - t0, 3)
    return cid, ("built", nodes, st)


def main():
    global LCEN2, CELL_SIDE, POOL_RADIUS
    ap = argparse.ArgumentParser()
    ap.add_argument("--csv", default=os.path.join(REPO, "solution_tree_v7.csv"))
    ap.add_argument("--min-rows", type=int, default=200)
    ap.add_argument("--max-rows", type=int, default=None)
    ap.add_argument("--tube", choices=["exclude", "include", "only"],
                    default="exclude")
    ap.add_argument("--sample", type=int, default=None,
                    help="deterministic stride sample of the targets")
    ap.add_argument("--max-cells", type=int, default=None)
    ap.add_argument("--workers", type=int, default=12)
    ap.add_argument("--pool-radius", type=float, default=POOL_RADIUS)
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    POOL_RADIUS = args.pool_radius

    ea.init_geometry()
    g6.prep(args.csv)
    LCEN2 = (g6.BMIN[g6.LROWS] + g6.BMAX[g6.LROWS]).astype(np.float64)
    cells = np.nonzero(g6.DEPTH == 5)[0]
    CELL_SIDE = (g6.BMAX[cells[0]] - g6.BMIN[cells[0]]).astype(np.float64)
    assert (g6.BMAX[cells] - g6.BMIN[cells] == CELL_SIDE).all(), \
        "depth-5 cells are not uniform"

    nloc = g6.CNT_BY_TYPE[2][cells]
    cnt = g6.CNT[cells]
    m = cnt > args.min_rows
    if args.max_rows is not None:
        m &= cnt <= args.max_rows
    if args.tube == "exclude":
        m &= nloc == 0
    elif args.tube == "only":
        m &= nloc > 0
    targets = cells[m]
    targets = targets[np.argsort(-cnt[np.searchsorted(cells, targets)],
                                 kind="stable")]
    if args.sample and len(targets) > args.sample:
        stride = len(targets) / args.sample
        targets = targets[(np.arange(args.sample) * stride).astype(np.int64)]
    if args.max_cells:
        targets = targets[:args.max_cells]
    print(f"pool: {len(LCEN2):,} local leaves   targets: {len(targets):,} "
          f"cells (tube={args.tube}, rows in ({args.min_rows}, "
          f"{args.max_rows or 'inf'}]) holding "
          f"{int(g6.CNT[targets].sum()):,} v7 rows   "
          f"pool_radius={POOL_RADIUS} cell-widths", flush=True)

    t0 = time.time()
    results = {}
    with mp.Pool(args.workers) as pool:
        for k, (cid, res) in enumerate(
                pool.imap_unordered(build_cell2_pool,
                                    [int(c) for c in targets]), 1):
            results[cid] = res
            v7r = int(g6.CNT[cid])
            if not args.quiet:
                if res[0] == "built":
                    st = res[2]
                    print(f"  [{k:>3}/{len(targets)}] cell {cid}: {v7r:,} -> "
                          f"{len(res[1]):,} rows  (g={st['n_leaf_g']} "
                          f"l1={st['n_leaf_l']} l2={st['n_leaf_l2']} "
                          f"sp={st['n_split']})  {st['seconds']}s", flush=True)
                else:
                    print(f"  [{k:>3}/{len(targets)}] cell {cid}: {v7r:,} -> "
                          f"COPY ({res[1]})", flush=True)
            elif k % 200 == 0 or k == len(targets):
                nb = sum(1 for r in results.values() if r[0] == "built")
                rn = sum(len(r[1]) for r in results.values()
                         if r[0] == "built")
                rc = int(g6.CNT[[c for c, r in results.items()
                                 if r[0] != "built"]].sum())
                rv = int(g6.CNT[list(results)].sum())
                rate = k / (time.time() - t0)
                print(f"  [{k:>6,}/{len(targets):,}] built={nb:,} "
                      f"ratio={(rn+rc)/max(1,rv):.3f}  {rate:.1f} cells/s "
                      f"eta {(len(targets)-k)/rate/60:.0f} min", flush=True)

    built = {c: r for c, r in results.items() if r[0] == "built"}
    v7_rows = int(g6.CNT[list(results)].sum())
    new_rows = sum(len(r[1]) for r in built.values()) + \
        int(g6.CNT[[c for c, r in results.items() if r[0] != "built"]].sum())
    n_l = sum(r[2]["n_leaf_l"] for r in built.values())
    n_l2 = sum(r[2]["n_leaf_l2"] for r in built.values())
    rep = dict(min_rows=args.min_rows, pool_radius=POOL_RADIUS,
               cells=len(results), built=len(built),
               copies=len(results) - len(built),
               v7_rows=v7_rows, new_rows=new_rows,
               ratio=round(new_rows / max(1, v7_rows), 4),
               local_first_order=n_l, local_second_order=n_l2,
               wall_seconds=round(time.time() - t0, 1))
    print(json.dumps(rep, indent=2))
    if args.out:
        with open(args.out, "w") as f:
            json.dump(dict(report=rep,
                           cells={str(c): (r[0],
                                           len(r[1]) if r[0] == "built" else None,
                                           r[2] if r[0] == "built" else r[1])
                                  for c, r in results.items()}), f, indent=2)


if __name__ == "__main__":
    main()
