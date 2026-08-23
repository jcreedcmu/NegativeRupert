"""Produce solution_tree_v6.csv: from-scratch ANISOTROPIC solution tree.

Supersedes make_solution_tree_v5.py's pruned/flipped tree with a rebuilt one.
The certificate is the second-order ANISOTROPIC ValidGlobal of the Lean
branch second-order (Noperthedron/RationalApprox/RationalGlobal.lean):
per-axis radii (eps_a, eps_t1, eps_f1) weight the G-side first partials, the
exact second partials at the box center, and the Lagrange remainder
E1^3/6 with E1 = eps_a + eps_t1 + eps_f1; kappa slack 4*KAPPA*(1+E1+E1^2/2).
H side analogous with E2 = eps_t2 + eps_f2, remainder E2^3/6, slack
3*KAPPA*(1+E2+E2^2/2).  The float model is regen/experiment_aniso.py's
eval_cert_aniso / aniso_grid (verified to reproduce the isotropic v5
certificate exactly on the eps-diagonal, and monotone in every eps axis).

Structure (agreed design):
  * v5's rows from the root down to the 216,000 depth-5 grid cells are
    copied VERBATIM (they are single-param k-way splits).
  * Below each grid cell a fresh greedy anisotropic BSP is built:
      - each box is tested with the aniso certificate (stage 1: witnesses
        inherited from the v5 winners of the cell's global leaves whose
        boxes intersect this box, plus parent near-miss reservoirs; stage 2:
        full-circle 1024-angle Pythagorean grid x all 90 S; stage 3: fine
        refinement of the best coarse angles);
      - on failure, local-leaf candidates (P,Q,r,sigma_Q from v5 nodeType==2
        rows of the same cell whose boxes intersect this box, nearest boxes
        first) are tested with local_check.check_local at margin 1e-9;
      - if neither certifies, the box is split in half along the axis with
        the largest eps_i * d(penalty)/d(eps_i) at the best grid witness --
        but only along axes with EVEN integer width (bounds stay integers).
  * A cell FAILS if no even axis is splittable, the split depth exceeds
    DEPTH_CAP, or the per-cell scan budget is exhausted; and a finished BSP
    with >= as many rows as v5's subtree for that cell is discarded.  In
    both cases v5's subtree for the cell is copied verbatim (renumbered).
    This guarantees v6 <= v5 in rows and completeness/validity everywhere.
  * Emission is a BFS renumbering over the whole tree in v5's 27-column
    format.  Binary splits: nodeType=3, split=axis code (1..5 = T1,V1,T2,
    V2,A per Interval.nth_part / Row.ValidSingleParamSplit), nrChildren=2,
    children contiguous from IDfirstChild, lower half first.

Every accepted global witness carries the 1e-9 slack margin against the
exact rational inequality and every local leaf passes the conservative
float mirror of Row.ValidLocal at margin 1e-9, so the output passes the
Lean checker.

Usage:
  .venv/bin/python regen/make_solution_tree_v6.py \
      --v5-csv data/solution_tree_v5.csv \
      --out    data/solution_tree_v6.csv \
      --workers 12 [--resume] [--max-cells N] [--smoke]
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

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import make_solution_tree_v5 as v5          # load_table, pythag, HEADER
import experiment_aniso as ea               # aniso certificate machinery
from local_check import check_local_arrays  # float mirror of Row.ValidLocal

DENOM = 15360000.0
SLACK_MIN = 1e-9          # min float slack for an accepted global witness
LOCAL_MARGIN = 1e-9       # margin for check_local acceptance
PARAMS = ["T1", "V1", "T2", "V2", "A"]
SEED_CAP = 256            # max distinct inherited witnesses per box
RESERVOIR_K = 8           # near-misses passed from parent to children
REFINE_TOP = 6            # best coarse angles refined on stage-2 failure
DEPTH_CAP = 48            # max binary-split depth below a grid cell
LOCAL_CHUNK = 16          # local candidates evaluated per check_local batch
LOCAL_TRY_CAP = 64        # max distinct local candidates tried per box
LOCAL_EPS_SKIP = 0.04     # skip check_local for boxes with sup radius above this
                          # (v5 local leaves have eps <= 0.0132; ValidLocal's
                          #  X/B_eps conjuncts cannot absorb eps ~ 3x that)
MISC_COLS = ["P1_index", "P2_index", "P3_index",
             "Q1_index", "Q2_index", "Q3_index", "r", "sigma_Q"]

# ---- globals shared with fork()ed workers (set by prep() before Pool) ----
NT = NRC = FC = SPL = None
BMIN = BMAX = None
SIDX = WXA = WYA = WDA = None
MISC = MISC_NA = WNA = None
DEPTH = ANC5 = CNT = None
CNT_BY_TYPE = None
CELL_IDS = None                      # cells sorted by v5 subtree size desc
GROWS = GKEY = None                  # global leaves sorted by cell (anc5)
LROWS = LKEY = LOCPAY = None         # local leaves sorted by cell (anc5)
MAX_SCANS = 60000


def prep(csv_path):
    """Parse the v5 table into flat fork-shared arrays and per-cell indexes."""
    global NT, NRC, FC, SPL, BMIN, BMAX, SIDX, WXA, WYA, WDA
    global MISC, MISC_NA, WNA, DEPTH, ANC5, CNT, CNT_BY_TYPE, CELL_IDS
    global GROWS, GKEY, LROWS, LKEY, LOCPAY
    print("loading v5 table ...", flush=True)
    df = v5.load_table(csv_path)
    n = len(df)
    print(f"{n:,} rows", flush=True)
    NT = df["nodeType"].to_numpy(np.int8)
    NRC = df["nrChildren"].fillna(0).to_numpy(np.int64)
    FC = df["IDfirstChild"].fillna(0).to_numpy(np.int64)
    SPL = df["split"].fillna(0).to_numpy(np.int64)
    BMIN = np.stack([df[p + "_min"].to_numpy(np.int64) for p in PARAMS], axis=1)
    BMAX = np.stack([df[p + "_max"].to_numpy(np.int64) for p in PARAMS], axis=1)
    SIDX = df["S_index"].fillna(0).to_numpy(np.int64)
    WXA = df["wx_nominator"].fillna(0).to_numpy(np.int64)
    WYA = df["wy_nominator"].fillna(0).to_numpy(np.int64)
    WDA = df["w_denominator"].fillna(0).to_numpy(np.int64)
    MISC = {c: df[c].fillna(0).to_numpy(np.int64) for c in MISC_COLS}
    MISC_NA = {c: df[c].isna().to_numpy() for c in MISC_COLS}
    WNA = df["wx_nominator"].isna().to_numpy()
    del df

    print("propagating depths ...", flush=True)
    DEPTH = np.full(n, -1, dtype=np.int16)
    DEPTH[0] = 0
    ANC5 = np.full(n, -1, dtype=np.int64)
    for i in np.nonzero(NT == 3)[0]:
        f, c = FC[i], NRC[i]
        d1 = DEPTH[i] + 1
        DEPTH[f:f + c] = d1
        if d1 == 5:
            ANC5[f:f + c] = np.arange(f, f + c)
        elif d1 > 5:
            ANC5[f:f + c] = ANC5[i]
    assert (DEPTH >= 0).all()
    assert ((ANC5 >= 0) == (DEPTH >= 5)).all()
    assert (NT[DEPTH < 5] == 3).all(), "non-split row above the grid layer"
    CNT = np.bincount(ANC5[ANC5 >= 0], minlength=n)
    CNT_BY_TYPE = {t: np.bincount(ANC5[(ANC5 >= 0) & (NT == t)], minlength=n)
                   for t in (1, 2, 3)}
    cells = np.nonzero(DEPTH == 5)[0]
    n_shallow = int((DEPTH < 5).sum())
    print(f"depth<5 rows: {n_shallow:,}   grid cells: {len(cells):,}   "
          f"cell-subtree rows: {int(CNT[cells].sum()):,}", flush=True)
    assert n_shallow + int(CNT[cells].sum()) == n

    # per-cell leaf indexes: rows sorted by owning cell for searchsorted slicing
    gl = np.nonzero((NT == 1) & (ANC5 >= 0))[0]
    GROWS = gl[np.argsort(ANC5[gl], kind="stable")]
    GKEY = ANC5[GROWS]
    ll = np.nonzero((NT == 2) & (ANC5 >= 0))[0]
    LROWS = ll[np.argsort(ANC5[ll], kind="stable")]
    LKEY = ANC5[LROWS]
    LOCPAY = np.stack([MISC[c][LROWS] for c in MISC_COLS], axis=1)  # (m,8)
    print(f"global leaves in cells: {len(GROWS):,}   local leaves: {len(LROWS):,}",
          flush=True)

    # big cells first for pool load balancing (and pessimistic early stats)
    CELL_IDS = cells[np.argsort(-CNT[cells], kind="stable")]
    return n


# ===================== greedy anisotropic build of one cell =====================

def _try_local(center, eps_sup, lo, hi, lidx):
    """Test local candidates lidx (indices into LROWS-space arrays) for the box
    (pose = center, sup radius eps_sup), nearest v5 boxes first, deduped.
    Returns (payload8 tuple, inherited: bool) or None."""
    rows = LROWS[lidx]
    cen2 = BMIN[rows] + BMAX[rows]                       # 2 * v5 box centers
    d = np.abs(cen2 - (lo + hi)).max(axis=1)
    order = lidx[np.argsort(d, kind="stable")]
    seen = set()
    cand = []                                            # (lidx, payload tuple)
    for j in order:
        pay = tuple(int(x) for x in LOCPAY[j])
        if pay in seen:
            continue
        seen.add(pay)
        cand.append((j, pay))
        if len(cand) >= LOCAL_TRY_CAP:
            break
    for s0 in range(0, len(cand), LOCAL_CHUNK):
        chunk = cand[s0:s0 + LOCAL_CHUNK]
        k = len(chunk)
        pays = np.array([c[1] for c in chunk], dtype=np.int64)
        acc, _ = check_local_arrays(
            np.broadcast_to(center, (k, 5)), np.full(k, eps_sup),
            pays[:, 0:3], pays[:, 3:6], pays[:, 6] / 1000.0, pays[:, 7],
            margin=LOCAL_MARGIN)
        hit = np.nonzero(acc)[0]
        if len(hit):
            j, pay = chunk[int(hit[0])]
            row = LROWS[j]
            inherited = bool((BMIN[row] == lo).all() and (BMAX[row] == hi).all())
            return pay, inherited
    return None


def build_cell(cid):
    """Rebuild the subtree of one depth-5 grid cell.

    Returns (cid, result) with result one of
      ("copy", reason)               -- fall back to v5's subtree verbatim
      ("built", nodes, stats)        -- preorder node list:
           (1, s, wx, wy, wd)                        global leaf
           (2, p1, p2, p3, q1, q2, q3, r, sigma)     local leaf
           (3, axis)                                 binary split (axis 0..4),
                                                     lower-half subtree first
    """
    cid = int(cid)
    v5_count = int(CNT[cid])
    if NT[cid] == 1:                 # cell is already a single v5 global leaf
        return cid, ("copy", "leafcell")
    t0 = time.time()
    lo0 = BMIN[cid].copy()
    hi0 = BMAX[cid].copy()
    g0, g1 = np.searchsorted(GKEY, cid, "left"), np.searchsorted(GKEY, cid, "right")
    grows = GROWS[g0:g1]
    lbmin, lbmax = BMIN[grows], BMAX[grows]
    lwin = np.stack([SIDX[grows], WXA[grows], WYA[grows], WDA[grows]], axis=1)
    l0, l1 = np.searchsorted(LKEY, cid, "left"), np.searchsorted(LKEY, cid, "right")
    lidx_all = np.arange(l0, l1)
    locmin, locmax = BMIN[LROWS[lidx_all]], BMAX[LROWS[lidx_all]]
    have_local = len(lidx_all) > 0

    scans = 0
    nodes = []
    st = dict(n_leaf_g=0, n_leaf_l=0, n_leaf_l_inherit=0, n_split=0)
    stack = [(lo0, hi0, None, 0)]           # (lo, hi, reservoir, depth); LIFO
    while stack:
        if len(nodes) + len(stack) >= v5_count:
            return cid, ("copy", "rows")
        if scans >= MAX_SCANS:
            return cid, ("copy", "scans")
        lo, hi, res, dep = stack.pop()
        scans += 1
        center = (lo + hi) / (2 * DENOM)
        e = (hi - lo) / (2 * DENOM)          # per-axis radii [T1,V1,T2,V2,A]

        # ---- stage 1: inherited witnesses (v5 winners of intersecting leaves
        #      of this cell + parent near-miss reservoir)
        if len(lwin):
            m = ((lbmin <= hi) & (lbmax >= lo)).all(axis=1)
            seeds = lwin[m]
        else:
            seeds = lwin
        if len(seeds):
            u, cts = np.unique(seeds, axis=0, return_counts=True)
            if len(u) > SEED_CAP:
                u = u[np.argsort(-cts)[:SEED_CAP]]
            seeds = u
        if res is not None:
            seeds = np.concatenate([seeds, res]) if len(seeds) else res
        witness = None
        if len(seeds):
            sl = ea.eval_pairs(center, e, seeds)
            j = int(sl.argmax())
            if sl[j] >= SLACK_MIN:
                witness = tuple(int(x) for x in seeds[j])
        if witness is None:
            # ---- stage 2: full-circle coarse grid (+ seed w's), all 90 S
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
            if flat[jb] >= SLACK_MIN:
                s, c = jb // A, jb % A
                witness = (int(s), int(w3[c, 0]), int(w3[c, 1]), int(w3[c, 2]))
            else:
                # ---- stage 3: fine refinement of the best coarse angles
                order = np.argpartition(-flat, 63)[:64]
                order = order[np.argsort(-flat[order])]
                cols = np.unique(order % A)[:REFINE_TOP]
                ra = (angs[cols][:, None] + ea.REFINE_DEL).ravel()
                ra = np.arctan2(np.sin(ra), np.cos(ra))
                rw = np.stack(v5.pythag(ra), axis=1)
                slack2, _ = ea.aniso_grid(center, e, rw)
                flat2 = slack2.ravel()
                j2 = int(flat2.argmax())
                if flat2[j2] >= SLACK_MIN:
                    s, c = j2 // len(rw), j2 % len(rw)
                    witness = (int(s), int(rw[c, 0]), int(rw[c, 1]), int(rw[c, 2]))
        if witness is not None:
            nodes.append((1,) + witness)
            st["n_leaf_g"] += 1
            continue

        # ---- local-leaf attempt (candidates from this cell's v5 local rows)
        loc_isect = False
        if have_local:
            m = ((locmin <= hi) & (locmax >= lo)).all(axis=1)
            loc_isect = bool(m.any())
            if loc_isect and float(e.max()) <= LOCAL_EPS_SKIP:
                got = _try_local(center, float(e.max()), lo, hi, lidx_all[m])
                if got is not None:
                    pay, inherited = got
                    nodes.append((2,) + pay)
                    st["n_leaf_l"] += 1
                    st["n_leaf_l_inherit"] += int(inherited)
                    continue

        # ---- split: axis with largest eps_i * d(pen)/d(eps_i) at best grid
        #      witness, restricted to even integer widths.  Near the local
        #      (hard-set) region, ValidLocal keys on the SUP radius, so the
        #      widest even axis is split instead (gradient as tiebreak).
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
        if dep >= DEPTH_CAP or not np.isfinite(contrib[ax]):
            return cid, ("copy", "nosplit")
        top = order[:RESERVOIR_K]
        res_rows = np.stack([top // A, w3[top % A, 0], w3[top % A, 1],
                             w3[top % A, 2]], axis=1).astype(np.int64)
        mid = (int(lo[ax]) + int(hi[ax])) // 2
        hi1 = hi.copy(); hi1[ax] = mid
        lo2 = lo.copy(); lo2[ax] = mid
        nodes.append((3, ax))
        st["n_split"] += 1
        stack.append((lo2, hi, res_rows, dep + 1))   # upper half (popped later)
        stack.append((lo, hi1, res_rows, dep + 1))   # lower half (popped next)
    st["scans"] = scans
    st["seconds"] = round(time.time() - t0, 3)
    return cid, ("built", nodes, st)


# ================================ driver loop ================================

def run_cells(workers, ckpt_path, resume, max_cells):
    results = {}
    if resume and os.path.exists(ckpt_path):
        with open(ckpt_path, "rb") as f:
            results = pickle.load(f)
        print(f"resumed: {len(results):,} cells done", flush=True)
    todo = [int(c) for c in CELL_IDS if int(c) not in results]
    if max_cells is not None:
        todo = todo[:max(0, max_cells - len(results))]
    print(f"{len(todo):,} cells to build", flush=True)

    def running_stats():
        n_built = n_copy = rows_new = rows_v5cmp = rows_copy = 0
        for cid, r in results.items():
            c = int(CNT[cid])
            rows_v5cmp += c
            if r[0] == "built":
                n_built += 1
                rows_new += len(r[1])
            else:
                n_copy += 1
                rows_copy += c
        return n_built, n_copy, rows_new, rows_copy, rows_v5cmp

    t0 = time.time()
    with mp.Pool(workers) as pool:
        chunk = max(1, min(64, len(todo) // (workers * 8) if todo else 1))
        for k, (cid, res) in enumerate(
                pool.imap_unordered(build_cell, todo, chunksize=chunk), 1):
            results[cid] = res
            if k % 1000 == 0 or k == len(todo):
                nb, nc, rn, rc, rv = running_stats()
                rate = k / (time.time() - t0)
                print(f"  [{k:>7,}/{len(todo):,}] built={nb:,} copy={nc:,} "
                      f"({nc / max(1, nb + nc) * 100:.1f}%)  "
                      f"rows new+copied={rn + rc:,} (v5: {rv:,}, "
                      f"ratio {(rn + rc) / max(1, rv):.3f})  "
                      f"{rate:.0f} cells/s eta {(len(todo) - k) / rate / 60:.0f} min",
                      flush=True)
            if k % 20000 == 0:
                v5.save_pickle(ckpt_path, results)
    v5.save_pickle(ckpt_path, results)
    return results


# ================================= emission =================================

def expand_cell(cid, nodes):
    """Preorder node list -> (kinds, payloads, lo(5) rows, hi(5) rows,
    child_lo, child_hi) with bounds replayed from the cell box."""
    n = len(nodes)
    size = np.ones(n, dtype=np.int64)
    chlo = np.full(n, -1, dtype=np.int64)
    chhi = np.full(n, -1, dtype=np.int64)
    sz_stack = []
    for i in range(n - 1, -1, -1):
        if nodes[i][0] == 3:
            a = sz_stack.pop()      # lower subtree (starts at i+1)
            b = sz_stack.pop()      # upper subtree
            chlo[i] = i + 1
            chhi[i] = i + 1 + a
            size[i] = 1 + a + b
        sz_stack.append(size[i])
    assert len(sz_stack) == 1 and size[0] == n
    lo = np.empty((n, 5), dtype=np.int64)
    hi = np.empty((n, 5), dtype=np.int64)
    bstack = [(0, BMIN[cid].copy(), BMAX[cid].copy())]
    while bstack:
        i, l, h = bstack.pop()
        lo[i], hi[i] = l, h
        if nodes[i][0] == 3:
            ax = nodes[i][1]
            mid = (int(l[ax]) + int(h[ax])) // 2
            h1 = h.copy(); h1[ax] = mid
            l2 = l.copy(); l2[ax] = mid
            bstack.append((chlo[i], l, h1))
            bstack.append((chhi[i], l2, h))
    return nodes, lo, hi, chlo, chhi


def emit(path, results):
    print("expanding built cells ...", flush=True)
    expanded = {cid: expand_cell(cid, r[1])
                for cid, r in results.items() if r[0] == "built"}
    print(f"{len(expanded):,} built cells, "
          f"{sum(len(e[0]) for e in expanded.values()):,} new rows", flush=True)

    def v5_bounds_str(i):
        return ",".join(f"{BMIN[i, k]},{BMAX[i, k]}" for k in range(5))

    def fmt(v, na):
        return "" if na else str(int(v))

    print("emitting v6 tree (BFS renumber) ...", flush=True)
    queue = deque([("o", 0)])
    next_id = 1
    nid = 0
    counts = {1: 0, 2: 0, 3: 0}
    with open(path, "w") as f:
        f.write(v5.HEADER + "\n")
        while queue:
            kind, *rest = queue.popleft()
            if kind == "o":
                i = rest[0]
                b = v5_bounds_str(i)
                nt = int(NT[i])
                if nt == 3:
                    fcid = next_id
                    for j in range(FC[i], FC[i] + NRC[i]):
                        if DEPTH[j] == 5 and j in expanded:
                            queue.append(("n", j, 0))
                        else:
                            queue.append(("o", int(j)))
                        next_id += 1
                    line = f"{nid},3,{NRC[i]},{fcid},{SPL[i]},{b},,,,,,,,,,,,"
                elif nt == 1:
                    line = (f"{nid},1,,,,{b},,,,,,,,,"
                            f"{WXA[i]},{WYA[i]},{WDA[i]},{SIDX[i]}")
                else:
                    m = ",".join(fmt(MISC[c][i], MISC_NA[c][i]) for c in MISC_COLS)
                    if WNA[i]:
                        line = f"{nid},2,,,,{b},{m},,,,"
                    else:
                        line = (f"{nid},2,,,,{b},{m},"
                                f"{WXA[i]},{WYA[i]},{WDA[i]},{SIDX[i]}")
            else:
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
    print(f"wrote {path}: {total:,} rows  "
          f"(split={counts[3]:,} global={counts[1]:,} local={counts[2]:,})",
          flush=True)
    return counts


def summarize(results, counts, gen_seconds, out_json):
    n_built = sum(1 for r in results.values() if r[0] == "built")
    copy_reasons = {}
    for r in results.values():
        if r[0] == "copy":
            copy_reasons[r[1]] = copy_reasons.get(r[1], 0) + 1
    n_copy = sum(copy_reasons.values())
    # leaf-cells are 1-row v5 global leaves, not failures; report separately
    n_leafcell = copy_reasons.get("leafcell", 0)
    n_fallback = n_copy - n_leafcell
    rows_new = sum(len(r[1]) for r in results.values() if r[0] == "built")
    copy_cids = [cid for cid, r in results.items()
                 if r[0] == "copy" and r[1] != "leafcell"]
    rows_fallback = int(sum(CNT[c] for c in copy_cids))
    v5_rows_built = int(sum(CNT[cid] for cid, r in results.items()
                            if r[0] == "built"))
    loc_new = sum(r[2]["n_leaf_l"] for r in results.values() if r[0] == "built")
    loc_inherit_box = sum(r[2]["n_leaf_l_inherit"] for r in results.values()
                          if r[0] == "built")
    loc_copied = int(sum(CNT_BY_TYPE[2][c] for c in copy_cids))
    total = sum(counts.values())
    est_lean_s = counts[1] * 2.6e-3 + counts[2] * 9.4e-3
    rep = dict(
        v6_total_rows=total,
        rows_by_nodeType=dict(split=counts[3], global_=counts[1], local=counts[2]),
        v5_total_rows=int(CNT.sum() + (DEPTH < 5).sum()),
        shrink_factor=round(float((CNT.sum() + (DEPTH < 5).sum()) / total), 4),
        cells=dict(total=len(results), built=n_built,
                   leafcell_copies=n_leafcell, fallback_copies=n_fallback,
                   fallback_rate_of_rebuildable=round(
                       n_fallback / max(1, n_built + n_fallback), 5),
                   fallback_reasons={k: v for k, v in copy_reasons.items()
                                     if k != "leafcell"}),
        rows=dict(new_rows_in_built_cells=rows_new,
                  v5_rows_in_built_cells=v5_rows_built,
                  built_cell_ratio=round(rows_new / max(1, v5_rows_built), 4),
                  rows_copied_from_v5_fallback=rows_fallback),
        local_leaves=dict(total=counts[2],
                          replaced_new_box=loc_new - loc_inherit_box,
                          inherited_exact_box=loc_inherit_box,
                          copied_verbatim_in_fallback_cells=loc_copied),
        est_lean_check=dict(model="2.6ms/global + 9.4ms/local row",
                            seconds=round(est_lean_s, 1),
                            minutes=round(est_lean_s / 60, 1)),
        generation_wall_seconds=round(gen_seconds, 1),
    )
    with open(out_json, "w") as f:
        json.dump(rep, f, indent=2)
    print(json.dumps(rep, indent=2))
    return rep


def main():
    global MAX_SCANS
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    root = os.path.dirname(HERE)
    ap.add_argument("--v5-csv", default=os.path.join(root, "data", "solution_tree_v5.csv"))
    ap.add_argument("--out", default=os.path.join(root, "data", "solution_tree_v6.csv"))
    ap.add_argument("--report", default=os.path.join(HERE, "v6_gen_report.json"))
    ap.add_argument("--workers", type=int, default=12)
    ap.add_argument("--checkpoint-dir", default=None)
    ap.add_argument("--resume", action="store_true")
    ap.add_argument("--max-cells", type=int, default=None,
                    help="pilot: only build this many cells, then stop (no emit)")
    ap.add_argument("--smoke", action="store_true",
                    help="build a few cells serially and print stats, no emit")
    ap.add_argument("--max-scans", type=int, default=MAX_SCANS)
    args = ap.parse_args()
    MAX_SCANS = args.max_scans

    t_start = time.time()
    ea.init_geometry()
    prep(args.v5_csv)
    ckpt_dir = args.checkpoint_dir or os.path.dirname(os.path.abspath(args.out))
    os.makedirs(ckpt_dir, exist_ok=True)
    ckpt_path = os.path.join(ckpt_dir, "v6_cells.pkl")

    if args.smoke:
        # a few cells across the size spectrum, incl. one with local leaves
        picks = [CELL_IDS[0], CELL_IDS[5], CELL_IDS[len(CELL_IDS) // 3],
                 CELL_IDS[len(CELL_IDS) // 2], CELL_IDS[-1]]
        for cid in picks:
            cid = int(cid)
            t0 = time.time()
            _, res = build_cell(cid)
            nl = int(CNT_BY_TYPE[2][cid])
            if res[0] == "built":
                print(f"cell {cid}: v5={int(CNT[cid]):,} (loc {nl}) -> "
                      f"built {len(res[1]):,} rows  {res[2]}  "
                      f"t={time.time() - t0:.1f}s", flush=True)
            else:
                print(f"cell {cid}: v5={int(CNT[cid]):,} (loc {nl}) -> "
                      f"COPY ({res[1]})  t={time.time() - t0:.1f}s", flush=True)
        return

    results = run_cells(args.workers, ckpt_path, args.resume, args.max_cells)
    if args.max_cells is not None and len(results) < len(CELL_IDS):
        print("pilot mode: stopping before emission", flush=True)
        return
    counts = emit(args.out, results)
    summarize(results, counts, time.time() - t_start, args.report)


if __name__ == "__main__":
    main()
