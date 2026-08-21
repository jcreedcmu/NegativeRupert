"""Produce solution_tree_v7.csv: v6 with the hard-set tube rebuilt using the
SECOND-ORDER anisotropic local certificate (Lean: Row.ValidLocal₂, branch
second-order-local).

Structure:
  * The v6 tree is copied VERBATIM except below "tube" grid cells — depth-5
    cells whose v6 subtree contains a local leaf (1,973 of 216,000).
  * Each tube cell is rebuilt with make_solution_tree_v6's greedy anisotropic
    BSP (same staged global certificate, seeds from the cell's v6 global
    leaves), but the local-leaf attempt now has two tiers per box:
      1. the FIRST-ORDER float mirror (check_local_arrays, margin 1e-9) with
         candidate payloads (P,Q,r,sigma) from the cell's v6 local rows —
         accepted rows keep the candidate r (they satisfy Row.ValidLocal);
      2. on failure, the SECOND-ORDER mirror (local2_check.check_local2,
         margin 3e-9) over the same (P,Q,sigma) candidates — accepted rows
         carry the freshly derived quantized r' (they satisfy
         Row.ValidLocal₂; Lean derives δ₂ from the row).
  * A rebuilt cell is kept only if strictly smaller than its v6 subtree;
    otherwise the v6 subtree is copied verbatim (renumbered), so
    v7 <= v6 in rows with completeness/validity everywhere.

Usage:
  scripts/uvrun python scripts/make_solution_tree_v7.py \
      --v6-csv solution_tree_v6.csv --out solution_tree_v7.csv \
      --workers 12 [--resume] [--smoke] [--max-cells N]
"""
import argparse
import json
import multiprocessing as mp
import os
import pickle
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import make_solution_tree_v5 as v5
import make_solution_tree_v6 as g6
import experiment_aniso as ea
from local2_check import check_local2

LOCAL2_TRY_CAP = 48
LOCAL2_EPS_SKIP = 0.08     # sup-radius above which the second-order tier is
                           # not attempted (v6 local leaves cap at ~0.0132;
                           # the second-order certificate absorbs ~4-6x that)
TUBE_CELLS = None


def build_cell2(cid):
    """g6.build_cell with a second-order local tier.  Returns (cid, result)
    with the same result shapes as g6.build_cell."""
    cid = int(cid)
    v6_count = int(g6.CNT[cid])
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
    l0 = np.searchsorted(g6.LKEY, cid, "left")
    l1 = np.searchsorted(g6.LKEY, cid, "right")
    lidx_all = np.arange(l0, l1)
    locmin = g6.BMIN[g6.LROWS[lidx_all]]
    locmax = g6.BMAX[g6.LROWS[lidx_all]]
    have_local = len(lidx_all) > 0

    scans = 0
    nodes = []
    st = dict(n_leaf_g=0, n_leaf_l=0, n_leaf_l2=0, n_split=0)
    stack = [(lo0, hi0, None, 0)]
    while stack:
        if len(nodes) + len(stack) >= v6_count:
            return cid, ("copy", "rows")
        if scans >= g6.MAX_SCANS:
            return cid, ("copy", "scans")
        lo, hi, res, dep = stack.pop()
        scans += 1
        center = (lo + hi) / (2 * g6.DENOM)
        e = (hi - lo) / (2 * g6.DENOM)

        # ---- staged global certificate (identical to v6)
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

        # ---- local tier 1: first-order candidates (unchanged from v6)
        loc_isect = False
        got = None
        if have_local:
            m = ((locmin <= hi) & (locmax >= lo)).all(axis=1)
            loc_isect = bool(m.any())
            if loc_isect and float(e.max()) <= g6.LOCAL_EPS_SKIP:
                got = g6._try_local(center, float(e.max()), lo, hi, lidx_all[m])
        if got is not None:
            pay, _ = got
            nodes.append((2,) + pay)
            st["n_leaf_l"] += 1
            continue

        # ---- local tier 2: second-order candidates
        if loc_isect and float(e.max()) <= LOCAL2_EPS_SKIP:
            rows2 = g6.LROWS[lidx_all[m]]
            cen2 = g6.BMIN[rows2] + g6.BMAX[rows2]
            order2 = np.argsort(np.abs(cen2 - (lo + hi)).max(axis=1),
                                kind="stable")
            seen = set()
            hit = None
            tried = 0
            for jj in order2:
                j = lidx_all[m][jj]
                pay = tuple(int(x) for x in g6.LOCPAY[j])
                key = pay[0:6] + (pay[7],)          # (P, Q, sigma), ignore r
                if key in seen:
                    continue
                seen.add(key)
                tried += 1
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

        # ---- split (identical to v6)
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
    global TUBE_CELLS
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    root = os.path.dirname(HERE)
    ap.add_argument("--v6-csv", default=os.path.join(root, "solution_tree_v6.csv"))
    ap.add_argument("--out", default=os.path.join(root, "solution_tree_v7.csv"))
    ap.add_argument("--report", default=os.path.join(HERE, "v7_gen_report.json"))
    ap.add_argument("--workers", type=int, default=12)
    ap.add_argument("--checkpoint-dir", default=None)
    ap.add_argument("--resume", action="store_true")
    ap.add_argument("--max-cells", type=int, default=None)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--max-scans", type=int, default=g6.MAX_SCANS)
    args = ap.parse_args()
    g6.MAX_SCANS = args.max_scans

    t_start = time.time()
    ea.init_geometry()
    g6.prep(args.v6_csv)
    # tube cells: depth-5 split cells whose v6 subtree holds a local leaf
    cells = np.nonzero(g6.DEPTH == 5)[0]
    tube = cells[(g6.NT[cells] == 3) & (g6.CNT_BY_TYPE[2][cells] > 0)]
    TUBE_CELLS = tube[np.argsort(-g6.CNT[tube], kind="stable")]
    print(f"tube cells: {len(TUBE_CELLS):,}  "
          f"(v6 rows in tube: {int(g6.CNT[TUBE_CELLS].sum()):,}, "
          f"local leaves: {int(g6.CNT_BY_TYPE[2][TUBE_CELLS].sum()):,})",
          flush=True)

    if args.smoke:
        picks = [TUBE_CELLS[0], TUBE_CELLS[3], TUBE_CELLS[len(TUBE_CELLS)//3],
                 TUBE_CELLS[len(TUBE_CELLS)//2], TUBE_CELLS[-1]]
        for cid in picks:
            cid = int(cid)
            t0 = time.time()
            _, res = build_cell2(cid)
            nl = int(g6.CNT_BY_TYPE[2][cid])
            if res[0] == "built":
                print(f"cell {cid}: v6={int(g6.CNT[cid]):,} (loc {nl}) -> "
                      f"built {len(res[1]):,} rows  {res[2]}  "
                      f"t={time.time()-t0:.1f}s", flush=True)
            else:
                print(f"cell {cid}: v6={int(g6.CNT[cid]):,} (loc {nl}) -> "
                      f"COPY ({res[1]})  t={time.time()-t0:.1f}s", flush=True)
        return

    ckpt_dir = args.checkpoint_dir or os.path.dirname(os.path.abspath(args.out))
    os.makedirs(ckpt_dir, exist_ok=True)
    ckpt_path = os.path.join(ckpt_dir, "v7_cells.pkl")
    results = {}
    if args.resume and os.path.exists(ckpt_path):
        with open(ckpt_path, "rb") as f:
            results = pickle.load(f)
        print(f"resumed: {len(results):,} cells done", flush=True)
    todo = [int(c) for c in TUBE_CELLS if int(c) not in results]
    if args.max_cells is not None:
        todo = todo[:max(0, args.max_cells - len(results))]
    print(f"{len(todo):,} cells to build", flush=True)
    t0 = time.time()
    with mp.Pool(args.workers) as pool:
        chunk = max(1, min(16, len(todo) // (args.workers * 8) if todo else 1))
        for k, (cid, res) in enumerate(
                pool.imap_unordered(build_cell2, todo, chunksize=chunk), 1):
            results[cid] = res
            if k % 100 == 0 or k == len(todo):
                nb = sum(1 for r in results.values() if r[0] == "built")
                rn = sum(len(r[1]) for r in results.values() if r[0] == "built")
                rc = sum(int(g6.CNT[c]) for c, r in results.items()
                         if r[0] != "built")
                rv = sum(int(g6.CNT[c]) for c in results)
                rate = k / (time.time() - t0)
                print(f"  [{k:>6,}/{len(todo):,}] built={nb:,} "
                      f"rows new+copied={rn+rc:,} (v6: {rv:,}, "
                      f"ratio {(rn+rc)/max(1,rv):.3f})  "
                      f"{rate:.1f} cells/s eta {(len(todo)-k)/rate/60:.0f} min",
                      flush=True)
            if k % 500 == 0:
                v5.save_pickle(ckpt_path, results)
    v5.save_pickle(ckpt_path, results)
    if args.max_cells is not None and len(results) < len(TUBE_CELLS):
        print("pilot mode: stopping before emission", flush=True)
        return

    counts = g6.emit(args.out, results)
    n_built = sum(1 for r in results.values() if r[0] == "built")
    l1 = sum(r[2]["n_leaf_l"] for r in results.values() if r[0] == "built")
    l2 = sum(r[2]["n_leaf_l2"] for r in results.values() if r[0] == "built")
    rep = dict(
        v7_total_rows=sum(counts.values()),
        rows_by_nodeType=dict(split=counts[3], global_=counts[1],
                              local=counts[2]),
        v6_total_rows=int(g6.CNT.sum() + (g6.DEPTH < 5).sum()),
        tube=dict(cells=len(TUBE_CELLS), built=n_built,
                  copies=len(results) - n_built,
                  v6_rows=int(g6.CNT[TUBE_CELLS].sum()),
                  new_rows=sum(len(r[1]) for r in results.values()
                               if r[0] == "built"),
                  local_first_order=l1, local_second_order=l2),
        generation_wall_seconds=round(time.time() - t_start, 1),
    )
    with open(args.report, "w") as f:
        json.dump(rep, f, indent=2)
    print(json.dumps(rep, indent=2))


if __name__ == "__main__":
    main()
