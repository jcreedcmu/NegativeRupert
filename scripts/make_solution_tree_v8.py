"""Produce solution_tree_v8.csv from v7: self-iterated rebuild + adaptive
top-tree coarsening.

Phase 1 (rebuild): every multi-row depth-5 cell is rebuilt with the v7 greedy
  builder, but (a) seeded from the *current* table's witnesses (self-iteration)
  and (b) with the local-certificate candidate pool widened from "this cell's
  own local leaves" to all local payloads within --pool-radius cell-widths
  (the v5-inherited pool never reached hidden-tube cells).  A rebuilt cell is
  kept only if strictly smaller.

Phase 2 (coarsen): the fixed 5-level top grid (4x30x4x15x30 equal splits) is
  replaced by a configurable schedule of equal splits.  Bottom-up, any
  schedule box whose children are all single global rows is merged into ONE
  global row when an inherited witness certifies the whole box (same
  SLACK_MIN as the builder).  This is exactly representable in the Lean
  checker: every split row still has equal k-way children
  (Row.ValidSplitParamAt/nth_part), merged boxes are ordinary global rows.

Phase 3 (emit): BFS emission of the new tree; cells keep their rebuilt (or
  copied) subtrees; certified boxes become single global rows.

Usage:
  python make_solution_tree_v8.py rebuild [--workers 12] [--pool-radius 12]
  python make_solution_tree_v8.py coarsen           # prints savings per schedule
  python make_solution_tree_v8.py emit [--schedule S1] [--out ...]
"""
import argparse
import json
import multiprocessing as mp
import os
import pickle
import sys
import time
from collections import deque

import numpy as np

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import make_solution_tree_v5 as v5
import make_solution_tree_v6 as g6
import experiment_aniso as ea
import v8_probe

CKPT = os.path.join(REPO, "v8_cells.pkl")
W_CAP = 8
EVAL_CHUNK = 40000

# schedules: top-down list of (axis, k); per-axis products must be (4,30,4,15,30)
SCHEDULES = {
    # baseline: exactly the v7 top structure (no regrouping possible)
    "S0": [(0, 4), (1, 30), (2, 4), (3, 15), (4, 30)],
    # coarse first, then binary tails ordered so best-merging axes are deepest
    "S1": [(0, 2), (1, 15), (2, 2), (3, 5), (4, 15),
           (4, 2), (3, 3), (2, 2), (1, 2), (0, 2)],
    # low-merge axes split first (fully), high-merge axes kept coarse longest
    "S2": [(4, 15), (3, 5), (2, 2), (4, 2), (3, 3), (2, 2),
           (1, 15), (0, 2), (1, 2), (0, 2)],
}
GRID = (4, 30, 4, 15, 30)


def load_v7():
    ea.init_geometry()
    g6.prep(os.path.join(REPO, "solution_tree_v7.csv"))


# ---------------------------------------------------------------- phase 1
def rebuild(args):
    load_v7()
    v8_probe.LCEN2 = (g6.BMIN[g6.LROWS] + g6.BMAX[g6.LROWS]).astype(np.float64)
    cells = np.nonzero(g6.DEPTH == 5)[0]
    v8_probe.CELL_SIDE = (g6.BMAX[cells[0]] - g6.BMIN[cells[0]]).astype(np.float64)
    v8_probe.POOL_RADIUS = args.pool_radius
    targets = cells[(g6.NT[cells] == 3) & (g6.CNT[cells] > 1)]
    targets = targets[np.argsort(-g6.CNT[cells[np.searchsorted(cells, targets)]],
                                 kind="stable")]
    results = {}
    if args.resume and os.path.exists(CKPT):
        with open(CKPT, "rb") as f:
            results = pickle.load(f)
        print(f"resumed: {len(results):,} cells", flush=True)
    todo = [int(c) for c in targets if int(c) not in results]
    print(f"{len(todo):,} cells to rebuild "
          f"({int(g6.CNT[targets].sum()):,} v7 rows)", flush=True)
    t0 = time.time()
    with mp.Pool(args.workers) as pool:
        for k, (cid, res) in enumerate(
                pool.imap_unordered(v8_probe.build_cell2_pool, todo,
                                    chunksize=16), 1):
            results[cid] = res
            if k % 2000 == 0 or k == len(todo):
                nb = sum(1 for r in results.values() if r[0] == "built")
                rn = sum(len(r[1]) for r in results.values() if r[0] == "built")
                rc = int(g6.CNT[[c for c, r in results.items()
                                 if r[0] != "built"]].sum())
                rv = int(g6.CNT[list(results)].sum())
                rate = k / (time.time() - t0)
                print(f"  [{k:>6,}/{len(todo):,}] built={nb:,} "
                      f"ratio={(rn+rc)/max(1,rv):.4f}  {rate:.0f} cells/s "
                      f"eta {(len(todo)-k)/rate/60:.0f} min", flush=True)
            if k % 20000 == 0:
                v5.save_pickle(CKPT, results)
    v5.save_pickle(CKPT, results)
    print(f"saved {CKPT}", flush=True)


# ---------------------------------------------------------------- phase 2
def cell_cost_and_wit(results):
    """Per-cell final row count and (for 1-row global cells) witness."""
    cells = np.nonzero(g6.DEPTH == 5)[0]
    cost = {}
    wit = {}
    for cid in cells:
        cid = int(cid)
        r = results.get(cid)
        if r is not None and r[0] == "built":
            cost[cid] = len(r[1])
            if len(r[1]) == 1 and r[1][0][0] == 1:
                nd = r[1][0]          # (1, s, wx, wy, wd)
                wit[cid] = (nd[1], nd[2], nd[3], nd[4])
        else:
            cost[cid] = int(g6.CNT[cid])
            if cost[cid] == 1 and g6.NT[cid] == 1:
                wit[cid] = (int(g6.SIDX[cid]), int(g6.WXA[cid]),
                            int(g6.WYA[cid]), int(g6.WDA[cid]))
    return cost, wit


_GEOM = None


def grid_geom():
    global _GEOM
    if _GEOM is None:
        cells = np.nonzero(g6.DEPTH == 5)[0]
        side = (g6.BMAX[cells[0]] - g6.BMIN[cells[0]]).astype(np.int64)
        origin = g6.BMIN[cells].min(axis=0)
        _GEOM = (side, origin)
    return _GEOM


def box_bounds(box):
    """box = tuple of (start, count) per axis, in cell units."""
    side, origin = grid_geom()
    lo = origin + side * np.array([b[0] for b in box], dtype=np.int64)
    hi = origin + side * np.array([b[0] + b[1] for b in box], dtype=np.int64)
    return lo, hi


def coarsen(results, schedule, verbose=True):
    """Walk the schedule tree bottom-up; certify boxes whose children are all
    1-row global leaves.  Returns (certified: {box: witness}, stats)."""
    cost, wit = cell_cost_and_wit(results)
    cells = np.nonzero(g6.DEPTH == 5)[0]
    coord_of = {}
    side = (g6.BMAX[cells[0]] - g6.BMIN[cells[0]]).astype(np.int64)
    origin = g6.BMIN[cells].min(axis=0)
    for cid in cells:
        c = tuple(((g6.BMIN[cid] - origin) // side).tolist())
        coord_of[c] = int(cid)

    # levels top-down: level d box shape after applying schedule[:d]
    # enumerate boxes level by level from the bottom (cells) upward
    def children(box, d):
        ax, k = schedule[d]
        st, cnt = box[ax]
        step = cnt // k
        out = []
        for i in range(k):
            b = list(box)
            b[ax] = (st + i * step, step)
            out.append(tuple(b))
        return out

    root = tuple((0, n) for n in GRID)
    # collect boxes per level
    levels = [[root]]
    for d in range(len(schedule)):
        levels.append([c for b in levels[-1] for c in children(b, d)])
    assert len(levels[-1]) == 216000

    # bottom level: map box -> (rows, witness or None)
    info = {}
    for b in levels[-1]:
        coord = tuple(s for s, _ in b)
        cid = coord_of[coord]
        info[b] = (cost[cid], wit.get(cid))

    n_certified = 0
    rows_saved = 0
    for d in range(len(schedule) - 1, -1, -1):
        cand_boxes, cand_wits = [], []
        for b in levels[d]:
            ch = children(b, d)
            if all(info[c][0] == 1 and info[c][1] is not None for c in ch):
                ws = list({info[c][1] for c in ch})[:W_CAP]
                cand_boxes.append(b)
                cand_wits.append(ws)
        # batch evaluate
        certified = {}
        if cand_boxes:
            lo_r, hi_r, sd_r, ix_r = [], [], [], []
            for i, (b, ws) in enumerate(zip(cand_boxes, cand_wits)):
                lo, hi = box_bounds(b)
                for w in ws:
                    lo_r.append(lo); hi_r.append(hi)
                    sd_r.append(w); ix_r.append(i)
            lo_r = np.array(lo_r); hi_r = np.array(hi_r)
            sd_r = np.array(sd_r, dtype=np.int64); ix_r = np.array(ix_r)
            best = np.full(len(cand_boxes), -np.inf)
            arg = np.zeros(len(cand_boxes), dtype=np.int64)
            for s in range(0, len(sd_r), EVAL_CHUNK):
                e = slice(s, s + EVAL_CHUNK)
                pose = (lo_r[e] + hi_r[e]) / (2 * g6.DENOM)
                eps = (hi_r[e] - lo_r[e]) / (2 * g6.DENOM)
                sl = ea.eval_cert_aniso(pose, eps,
                                        sd_r[e][:, 0].astype(np.int64),
                                        sd_r[e][:, 1] / sd_r[e][:, 3],
                                        sd_r[e][:, 2] / sd_r[e][:, 3])
                for j in range(len(sl)):
                    i = ix_r[s + j]
                    if sl[j] > best[i]:
                        best[i] = sl[j]; arg[i] = s + j
            for i, b in enumerate(cand_boxes):
                if best[i] >= g6.SLACK_MIN:
                    certified[b] = tuple(int(x) for x in sd_r[arg[i]])
        # propagate: certified box costs 1 row; else 1 (split) + sum children
        lvl_cert = 0
        for b in levels[d]:
            if b in certified:
                ch = children(b, d)
                saved = sum(info[c][0] for c in ch) + 1 - 1
                rows_saved += saved - 0  # children rows + own split row - 1 leaf
                info[b] = (1, certified[b])
                lvl_cert += 1
            else:
                ch = children(b, d)
                info[b] = (1 + sum(info[c][0] for c in ch), None)
        n_certified += lvl_cert
        if verbose:
            print(f"  level {d} ({schedule[d]}): {len(levels[d]):,} boxes, "
                  f"{len(cand_boxes):,} candidates, {lvl_cert:,} certified",
                  flush=True)
    total_rows = info[root][0]
    return info, dict(total_rows=total_rows, certified=n_certified)


# ------------------------------------------------------- phase 2b: hybrid DP
# Fixed coarse top: [(4,15),(1,5),(3,5)] -> 375 boxes of cell-shape
# (4,6,4,3,2) = 576 cells.  Within each box, a DP over aligned sub-boxes picks
# the optimal equal-split structure: direct big fanouts where merging is
# sparse, cascades (or one certified row for the whole sub-box) where dense.
TOP_STAGES = [(4, 15), (1, 5), (3, 5)]
BOX_SHAPE = (4, 6, 4, 3, 2)


def divisors(n):
    return [d for d in range(2, n + 1) if n % d == 0]


def sub_geoms(shape):
    """All aligned (start, size) tuples per axis, as the cross product."""
    per_axis = []
    for n in shape:
        opts = []
        for d in [dd for dd in range(1, n + 1) if n % dd == 0]:
            opts += [(s * d, d) for s in range(n // d)]
        per_axis.append(opts)
    out = [()]
    for opts in per_axis:
        out = [g + (o,) for g in out for o in opts]
    return out


def dp_coarsen(results):
    """Returns (box_origin -> decisions, projected_total_rows).
    decisions: geom -> ("leaf", wit) | ("split", axis, k) | ("cell", cid)."""
    cost, wit = cell_cost_and_wit(results)
    side, origin = grid_geom()
    cells = np.nonzero(g6.DEPTH == 5)[0]
    coord_of = {}
    for cid in cells:
        c = tuple(((g6.BMIN[cid] - origin) // side).tolist())
        coord_of[c] = int(cid)

    nb = [GRID[a] // BOX_SHAPE[a] for a in range(5)]      # boxes per axis
    box_origins = [(i0 * BOX_SHAPE[0], i1 * BOX_SHAPE[1], i2 * BOX_SHAPE[2],
                    i3 * BOX_SHAPE[3], i4 * BOX_SHAPE[4])
                   for i0 in range(nb[0]) for i1 in range(nb[1])
                   for i2 in range(nb[2]) for i3 in range(nb[3])
                   for i4 in range(nb[4])]
    assert len(box_origins) * int(np.prod(BOX_SHAPE)) == 216000

    # per-box arrays: cell costs, one-row-global mask, witness index
    print("collecting per-box cell data ...", flush=True)
    wit_list = []
    wit_index = {}
    box_cost = {}
    box_ones = {}
    box_witix = {}
    for bo in box_origins:
        cc = np.zeros(BOX_SHAPE, dtype=np.int64)
        on = np.zeros(BOX_SHAPE, dtype=bool)
        wi = np.full(BOX_SHAPE, -1, dtype=np.int64)
        it = np.ndindex(*BOX_SHAPE)
        for off in it:
            coord = tuple(bo[a] + off[a] for a in range(5))
            cid = coord_of[coord]
            cc[off] = cost[cid]
            w = wit.get(cid)
            if cost[cid] == 1 and w is not None:
                on[off] = True
                if w not in wit_index:
                    wit_index[w] = len(wit_list)
                    wit_list.append(w)
                wi[off] = wit_index[w]
        box_cost[bo] = cc
        box_ones[bo] = on
        box_witix[bo] = wi
    wit_arr = np.array(wit_list, dtype=np.int64)
    print(f"{len(wit_arr):,} distinct witnesses", flush=True)

    # candidate (box, geom) sub-boxes with volume>1 whose cells are all
    # single global rows; batch-certify with inherited witnesses
    geoms = sub_geoms(BOX_SHAPE)
    print(f"{len(geoms):,} geometries/box, {len(box_origins)} boxes", flush=True)
    cand = []
    for bo in box_origins:
        on = box_ones[bo]
        for gm in geoms:
            vol = 1
            for _, d in gm:
                vol *= d
            if vol == 1:
                continue
            sl = tuple(slice(s, s + d) for s, d in gm)
            if bool(on[sl].all()):
                cand.append((bo, gm))
    print(f"{len(cand):,} all-single sub-boxes to certify", flush=True)

    lo_r, hi_r, sd_r, ix_r = [], [], [], []
    for i, (bo, gm) in enumerate(cand):
        sl = tuple(slice(s, s + d) for s, d in gm)
        ws = np.unique(box_witix[bo][sl].ravel())[:W_CAP]
        lo = origin + side * np.array([bo[a] + gm[a][0] for a in range(5)],
                                      dtype=np.int64)
        hi = lo + side * np.array([gm[a][1] for a in range(5)], dtype=np.int64)
        for w in ws:
            lo_r.append(lo); hi_r.append(hi); sd_r.append(w); ix_r.append(i)
    lo_r = np.array(lo_r); hi_r = np.array(hi_r)
    sd_r = wit_arr[np.array(sd_r)]; ix_r = np.array(ix_r)
    best = np.full(len(cand), -np.inf)
    arg = np.zeros(len(cand), dtype=np.int64)
    print(f"{len(sd_r):,} certification evals ...", flush=True)
    for s in range(0, len(sd_r), EVAL_CHUNK):
        e = slice(s, s + EVAL_CHUNK)
        pose = (lo_r[e] + hi_r[e]) / (2 * g6.DENOM)
        eps = (hi_r[e] - lo_r[e]) / (2 * g6.DENOM)
        sl = ea.eval_cert_aniso(pose, eps, sd_r[e][:, 0].astype(np.int64),
                                sd_r[e][:, 1] / sd_r[e][:, 3],
                                sd_r[e][:, 2] / sd_r[e][:, 3])
        np.maximum.at(best, ix_r[e], sl)
        hit = sl >= best[ix_r[e]]
        arg[ix_r[e][hit]] = np.nonzero(hit)[0] + s
    certified = {}
    for i, (bo, gm) in enumerate(cand):
        if best[i] >= g6.SLACK_MIN:
            certified[(bo, gm)] = tuple(int(x) for x in sd_r[arg[i]])
    print(f"{len(certified):,} sub-boxes certified", flush=True)

    # DP per box
    print("running DP ...", flush=True)
    decisions = {}
    total = 0
    top_internal = 0
    for bo in box_origins:
        cc = box_cost[bo]
        memo = {}
        choice = {}

        def dp(gm):
            if gm in memo:
                return memo[gm]
            vol = 1
            for _, d in gm:
                vol *= d
            if vol == 1:
                off = tuple(s for s, _ in gm)
                memo[gm] = int(cc[off])
                choice[gm] = ("cell", coord_of[tuple(bo[a] + off[a]
                                                     for a in range(5))])
                return memo[gm]
            if (bo, gm) in certified:
                memo[gm] = 1
                choice[gm] = ("leaf", certified[(bo, gm)])
                return memo[gm]
            bestc = None
            bestch = None
            for a in range(5):
                s0, d0 = gm[a]
                for k in divisors(d0):
                    step = d0 // k
                    tot = 1
                    for i in range(k):
                        g2 = list(gm)
                        g2[a] = (s0 + i * step, step)
                        tot += dp(tuple(g2))
                    if bestc is None or tot < bestc:
                        bestc = tot
                        bestch = ("split", a, k)
            memo[gm] = bestc
            choice[gm] = bestch
            return bestc

        root_gm = tuple((0, d) for d in BOX_SHAPE)
        total += dp(root_gm)
        decisions[bo] = choice
    # top rows: stages [(4,15),(1,5),(3,5)] -> 1 + 15 + 75 split rows
    n = 1
    for _, k in TOP_STAGES:
        top_internal += n
        n *= k
    total += top_internal
    print(f"projected total rows: {total:,} (top internal {top_internal})",
          flush=True)
    return decisions, total


def coarsen_cmd(args):
    load_v7()
    with open(CKPT, "rb") as f:
        results = pickle.load(f)
    for name in (args.schedule.split(",") if args.schedule else SCHEDULES):
        print(f"schedule {name}:", flush=True)
        _, st = coarsen(results, SCHEDULES[name])
        print(f"  -> total rows {st['total_rows']:,} "
              f"(certified boxes {st['certified']:,})", flush=True)


# ---------------------------------------------------------------- phase 3
def emit(args):
    load_v7()
    with open(CKPT, "rb") as f:
        results = pickle.load(f)
    decisions, projected = dp_coarsen(results)

    side, origin = grid_geom()

    expanded = {cid: g6.expand_cell(cid, r[1])
                for cid, r in results.items() if r[0] == "built"}
    print(f"{len(expanded):,} built cells expanded", flush=True)

    def bounds_str(lo, hi):
        return ",".join(f"{lo[k]},{hi[k]}" for k in range(5))

    def v7_bounds_str(i):
        return ",".join(f"{g6.BMIN[i, k]},{g6.BMAX[i, k]}" for k in range(5))

    def fmt(v, na):
        return "" if na else str(int(v))

    root = tuple((0, n) for n in GRID)
    queue = deque([("t", root, 0)])
    next_id = 1
    nid = 0
    counts = {1: 0, 2: 0, 3: 0}
    with open(args.out, "w") as f:
        f.write(v5.HEADER + "\n")
        while queue:
            kind, *rest = queue.popleft()
            if kind == "t":                     # fixed top stage box
                box, d = rest
                if d == len(TOP_STAGES):
                    bo = tuple(s for s, _ in box)
                    queue.appendleft(("g", bo, tuple((0, n) for n in BOX_SHAPE)))
                    continue
                lo = origin + side * np.array([b[0] for b in box], np.int64)
                hi = origin + side * np.array([b[0] + b[1] for b in box],
                                              np.int64)
                nt = 3
                ax, k = TOP_STAGES[d]
                st_, cnt = box[ax]
                step = cnt // k
                fcid = next_id
                for i in range(k):
                    c = list(box)
                    c[ax] = (st_ + i * step, step)
                    queue.append(("t", tuple(c), d + 1))
                next_id += k
                line = (f"{nid},3,{k},{fcid},{ax + 1},"
                        f"{bounds_str(lo, hi)},,,,,,,,,,,,")
            elif kind == "g":                   # DP node inside a box
                bo, gm = rest
                dec = decisions[bo][gm]
                if dec[0] == "cell":
                    cid = dec[1]
                    if cid in expanded:
                        queue.appendleft(("n", cid, 0))
                    else:
                        queue.appendleft(("o", cid))
                    continue
                lo = origin + side * np.array(
                    [bo[a] + gm[a][0] for a in range(5)], np.int64)
                hi = lo + side * np.array([gm[a][1] for a in range(5)],
                                          np.int64)
                b = bounds_str(lo, hi)
                if dec[0] == "leaf":
                    nt = 1
                    w = dec[1]
                    line = (f"{nid},1,,,,{b},,,,,,,,,"
                            f"{w[1]},{w[2]},{w[3]},{w[0]}")
                else:                           # ("split", axis, k)
                    nt = 3
                    _, a, k = dec
                    s0, d0 = gm[a]
                    step = d0 // k
                    fcid = next_id
                    for i in range(k):
                        g2 = list(gm)
                        g2[a] = (s0 + i * step, step)
                        queue.append(("g", bo, tuple(g2)))
                    next_id += k
                    line = f"{nid},3,{k},{fcid},{a + 1},{b},,,,,,,,,,,,"
            elif kind == "o":                   # copied original subtree row
                i = rest[0]
                b = v7_bounds_str(i)
                nt = int(g6.NT[i])
                if nt == 3:
                    fcid = next_id
                    for j in range(g6.FC[i], g6.FC[i] + g6.NRC[i]):
                        queue.append(("o", int(j)))
                    next_id += int(g6.NRC[i])
                    line = f"{nid},3,{g6.NRC[i]},{fcid},{g6.SPL[i]},{b},,,,,,,,,,,,"
                elif nt == 1:
                    line = (f"{nid},1,,,,{b},,,,,,,,,"
                            f"{g6.WXA[i]},{g6.WYA[i]},{g6.WDA[i]},{g6.SIDX[i]}")
                else:
                    m = ",".join(fmt(g6.MISC[c][i], g6.MISC_NA[c][i])
                                 for c in g6.MISC_COLS)
                    if g6.WNA[i]:
                        line = f"{nid},2,,,,{b},{m},,,,"
                    else:
                        line = (f"{nid},2,,,,{b},{m},"
                                f"{g6.WXA[i]},{g6.WYA[i]},{g6.WDA[i]},{g6.SIDX[i]}")
            else:                               # rebuilt cell nodes ("n")
                cid, k = rest
                nodes, lo, hi, chlo, chhi = expanded[cid]
                nd = nodes[k]
                b = ",".join(f"{lo[k, a]},{hi[k, a]}" for a in range(5))
                nt = nd[0]
                if nt == 3:
                    fcid = next_id
                    queue.append(("n", cid, int(chlo[k])))
                    queue.append(("n", cid, int(chhi[k])))
                    next_id += 2
                    line = f"{nid},3,2,{fcid},{nd[1] + 1},{b},,,,,,,,,,,,"
                elif nt == 1:
                    line = f"{nid},1,,,,{b},,,,,,,,,{nd[2]},{nd[3]},{nd[4]},{nd[1]}"
                else:
                    m = ",".join(str(x) for x in nd[1:9])
                    line = f"{nid},2,,,,{b},{m},,,,"
            counts[nt] += 1
            f.write(line + "\n")
            nid += 1
    total = sum(counts.values())
    print(f"wrote {args.out}: {total:,} rows "
          f"(split={counts[3]:,} global={counts[1]:,} local={counts[2]:,})",
          flush=True)
    assert next_id == total, (next_id, total)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["rebuild", "coarsen", "emit"])
    ap.add_argument("--workers", type=int, default=12)
    ap.add_argument("--pool-radius", type=float, default=12.0)
    ap.add_argument("--resume", action="store_true")
    ap.add_argument("--schedule", default=None)
    ap.add_argument("--out", default=os.path.join(REPO, "solution_tree_v8.csv"))
    args = ap.parse_args()
    if args.cmd == "rebuild":
        rebuild(args)
    elif args.cmd == "coarsen":
        coarsen_cmd(args)
    else:
        args.schedule = args.schedule or "S1"
        emit(args)


if __name__ == "__main__":
    main()
