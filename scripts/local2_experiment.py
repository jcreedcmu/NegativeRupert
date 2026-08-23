"""Payoff experiment for the SECOND-ORDER ANISOTROPIC local certificate.

Certificate design (order-2-exact + cubic Lagrange remainder, per-axis radii
e = (e_t1, e_f1, e_t2, e_f2, e_a), mirroring the global certificate's shape;
all "family" matrices/vectors are the ∂-grids with member norms <= 1, so every
third partial of a linear quantity is <= 1 and of a product quantity <= 8):

  A_P(i):   <X1b, Pi>  >  e_t1|<X1t,Pi>| + e_f1|<X1f,Pi>|
                          + (e_t1^2|<X1tt,Pi>| + 2 e_t1 e_f1|<X1tf,Pi>|
                             + e_f1^2|<X1ff,Pi>|)/2  + E1s^3/6
            (E1s = e_t1+e_f1; X-family: Xt, Xf, Xtt, Xtf, Xff, norms <= 1)
  A_Q(i):   same with (-1)^sigma_Q, X2b, e_t2/e_f2.
  span_P(i): f = <R90 M1 Pi, M1 Pj>, j=i+1:
            fb > e|d1f| ... + (second partials exact, 4 Leibniz terms each)/2
                + 8 * E1s^3/6
  span_Q(i): same on the Q side.
  r:        pick r = min_i (||M2b Qi|| - Dr_i) where
            Dr_i = e_t2||M2t Qi|| + e_f2||M2f Qi||
                   + (e_t2^2||M2tt Qi|| + 2 e_t2 e_f2 ||M2tf Qi||
                      + e_f2^2||M2ff Qi||)/2 + E2s^3/6 * ||Qi||
            require r > 0.
  delta:    v_i = R M1 Pi - M2 Qi (inner and outer parts separable, so no
            mixed inner/outer second partials):
            Dd_i = e_a||M1b Pi|| + e_t1||M1t Pi|| + e_f1||M1f Pi||
                   + e_t2||M2t Qi|| + e_f2||M2f Qi||
                   + ( e_a^2||M1b Pi|| + 2 e_a e_t1||M1t Pi||
                       + 2 e_a e_f1||M1f Pi|| + e_t1^2||M1tt Pi||
                       + 2 e_t1 e_f1||M1tf Pi|| + e_f1^2||M1ff Pi||
                       + e_t2^2||M2tt Qi|| + 2 e_t2 e_f2||M2tf Qi||
                       + e_f2^2||M2ff Qi|| )/2
                   + (e_a+E1s)^3/6 * ||Pi|| + E2s^3/6 * ||Qi||
            (uses ||R' M w|| = ||M w||; R-isometry)
            delta = max_i (||v_i(center)|| + Dd_i)/2
  B(i,j):   N = <M2 Qi, M2 (Qi - Vj)> (theta2/phi2 only), D2 = Qi - Vj:
            DN = e_t2|d_t N| + e_f2|d_f N|
                 + (e_t2^2|d_tt N| + 2 e_t2 e_f2 |d_tf N| + e_f2^2|d_ff N|)/2
                 + 8 ||Qi|| ||D2|| E2s^3/6
            Dd_ij = Dr-shape with D2 in place of Qi
            require (N - DN) / ((||M2 Qi||+Dr_i)(||M2 D2||+Dd_ij)) > delta / r
            and N - DN >= 0.

Experiment: sample tube cells (subtree touches a local leaf), rebuild each
cell's BSP three ways with the same harness (global cert = ea.aniso_grid
stage2+3, no v5 seeds):
  rebuild1: local cert = current first-order (float mirror, sup-eps),
  rebuild2: local cert = the second-order certificate above.
Compare row counts (v6 actual count shown for reference).
"""
import sys, os, time, json
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = "/home/dwrensha.linux/src/Noperthedron"
sys.path.insert(0, os.path.join(REPO, "scripts"))
import make_solution_tree_v5 as v5
import experiment_aniso as ea

CSV = os.path.join(REPO, "solution_tree_v6.csv")
DENOM = 15360000.0
SLACK_MIN = 1e-9
MARGIN2 = 3e-9          # margin for local2 (covers kappa terms ~1e-9 + float)
LOCAL_TRY_CAP = 48
DEPTH_CAP = 48
SCAN_CAP = 40000

# ---------------- rotation families (theta, phi scalars) ----------------

def m_family(t, f):
    st, ct, sf, cf = np.sin(t), np.cos(t), np.sin(f), np.cos(f)
    M   = np.array([[-st, ct, 0], [-ct*cf, -st*cf, sf]])
    Mt  = np.array([[-ct, -st, 0], [st*cf, -ct*cf, 0]])
    Mf  = np.array([[0, 0, 0], [ct*sf, st*sf, cf]])
    Mtt = np.array([[st, -ct, 0], [ct*cf, st*cf, 0]])
    Mtf = np.array([[0, 0, 0], [-st*sf, ct*sf, 0]])
    Mff = np.array([[0, 0, 0], [ct*cf, st*cf, -sf]])
    return M, Mt, Mf, Mtt, Mtf, Mff

def x_family(t, f):
    st, ct, sf, cf = np.sin(t), np.cos(t), np.sin(f), np.cos(f)
    X   = np.array([ct*sf, st*sf, cf])
    Xt  = np.array([-st*sf, ct*sf, 0.0])
    Xf  = np.array([ct*cf, st*cf, -sf])
    Xtt = np.array([-ct*sf, -st*sf, 0.0])
    Xtf = np.array([-st*cf, ct*cf, 0.0])
    Xff = -X
    return X, Xt, Xf, Xtt, Xtf, Xff

R90 = np.array([[0.0, -1.0], [1.0, 0.0]])

def rot2(a):
    ca, sa = np.cos(a), np.sin(a)
    return np.array([[ca, -sa], [sa, ca]])

# ---------------- second-order local certificate ----------------

def local2_slack(center, e, P, Q, sigma_q, V):
    """Min slack of the second-order local certificate.
    center: pose 5 [t1,f1,t2,f2,a]; e: radii 5 (same order);
    P, Q: (3,3) triangle vertices; V: (90,3) all vertices."""
    t1, f1, t2, f2, a = center
    e_t1, e_f1, e_t2, e_f2, e_a = e
    E1s = e_t1 + e_f1
    E2s = e_t2 + e_f2
    M1, M1t, M1f, M1tt, M1tf, M1ff = m_family(t1, f1)
    M2, M2t, M2f, M2tt, M2tf, M2ff = m_family(t2, f2)
    X1, X1t, X1f, X1tt, X1tf, X1ff = x_family(t1, f1)
    X2, X2t, X2f, X2tt, X2tf, X2ff = x_family(t2, f2)
    R = rot2(a)
    sQ = -1.0 if sigma_q else 1.0
    slacks = []

    # A conditions
    for i in range(3):
        pen = (e_t1*abs(X1t @ P[i]) + e_f1*abs(X1f @ P[i])
               + 0.5*(e_t1**2*abs(X1tt @ P[i]) + 2*e_t1*e_f1*abs(X1tf @ P[i])
                      + e_f1**2*abs(X1ff @ P[i]))
               + E1s**3/6)
        slacks.append((X1 @ P[i]) - pen)
        pen = (e_t2*abs(X2t @ Q[i]) + e_f2*abs(X2f @ Q[i])
               + 0.5*(e_t2**2*abs(X2tt @ Q[i]) + 2*e_t2*e_f2*abs(X2tf @ Q[i])
                      + e_f2**2*abs(X2ff @ Q[i]))
               + E2s**3/6)
        slacks.append(sQ*(X2 @ Q[i]) - pen)

    # spanning (both sides)
    def span_slacks(M, Mt, Mf, Mtt, Mtf, Mff, T, et, ef, Es):
        out = []
        for i in range(3):
            v, w = T[i], T[(i+1) % 3]
            Mv, Mw = M@v, M@w
            Mtv, Mtw = Mt@v, Mt@w
            Mfv, Mfw = Mf@v, Mf@w
            f0 = (R90@Mv) @ Mw
            d_t = (R90@Mtv)@Mw + (R90@Mv)@Mtw
            d_f = (R90@Mfv)@Mw + (R90@Mv)@Mfw
            d_tt = (R90@(Mtt@v))@Mw + 2*((R90@Mtv)@Mtw) + (R90@Mv)@(Mtt@w)
            d_tf = ((R90@(Mtf@v))@Mw + (R90@Mtv)@Mfw
                    + (R90@Mfv)@Mtw + (R90@Mv)@(Mtf@w))
            d_ff = (R90@(Mff@v))@Mw + 2*((R90@Mfv)@Mfw) + (R90@Mv)@(Mff@w)
            pen = (et*abs(d_t) + ef*abs(d_f)
                   + 0.5*(et**2*abs(d_tt) + 2*et*ef*abs(d_tf) + ef**2*abs(d_ff))
                   + 8*Es**3/6)
            out.append(f0 - pen)
        return out
    slacks += span_slacks(M1, M1t, M1f, M1tt, M1tf, M1ff, P, e_t1, e_f1, E1s)
    slacks += span_slacks(M2, M2t, M2f, M2tt, M2tf, M2ff, Q, e_t2, e_f2, E2s)

    # Dr_i (variation of ||M2 Qi||) and r
    def dvar(w, et, ef, Es):
        # second-order variation bound of the vector M2(p) w around center
        nw = np.linalg.norm(w)
        return (et*np.linalg.norm(M2t@w) + ef*np.linalg.norm(M2f@w)
                + 0.5*(et**2*np.linalg.norm(M2tt@w)
                       + 2*et*ef*np.linalg.norm(M2tf@w)
                       + ef**2*np.linalg.norm(M2ff@w))
                + Es**3/6*nw)
    nMQ = np.array([np.linalg.norm(M2@Q[i]) for i in range(3)])
    Dr = np.array([dvar(Q[i], e_t2, e_f2, E2s) for i in range(3)])
    r = (nMQ - Dr).min() * (1 - 1e-12)
    if r <= 0:
        return -1.0
    slacks.append(r)                       # positivity of r (raw scale)

    # delta (uses R-isometry: ||R' M w|| = ||M w||)
    Etot1 = e_a + E1s
    dd = []
    for i in range(3):
        v0 = R@(M1@P[i]) - M2@Q[i]
        Dd = (e_a*np.linalg.norm(M1@P[i]) + e_t1*np.linalg.norm(M1t@P[i])
              + e_f1*np.linalg.norm(M1f@P[i])
              + e_t2*np.linalg.norm(M2t@Q[i]) + e_f2*np.linalg.norm(M2f@Q[i])
              + 0.5*(e_a**2*np.linalg.norm(M1@P[i])
                     + 2*e_a*e_t1*np.linalg.norm(M1t@P[i])
                     + 2*e_a*e_f1*np.linalg.norm(M1f@P[i])
                     + e_t1**2*np.linalg.norm(M1tt@P[i])
                     + 2*e_t1*e_f1*np.linalg.norm(M1tf@P[i])
                     + e_f1**2*np.linalg.norm(M1ff@P[i])
                     + e_t2**2*np.linalg.norm(M2tt@Q[i])
                     + 2*e_t2*e_f2*np.linalg.norm(M2tf@Q[i])
                     + e_f2**2*np.linalg.norm(M2ff@Q[i]))
              + Etot1**3/6*np.linalg.norm(P[i]) + E2s**3/6*np.linalg.norm(Q[i]))
        dd.append((np.linalg.norm(v0) + Dd)/2)
    delta = max(dd)

    # B condition over all pairs (i, j)
    bound = delta / r
    M2V = V @ M2.T                    # (90,2)
    M2tV = V @ M2t.T
    M2fV = V @ M2f.T
    M2ttV = V @ M2tt.T
    M2tfV = V @ M2tf.T
    M2ffV = V @ M2ff.T
    nV = np.linalg.norm(V, axis=1)
    for i in range(3):
        q = M2@Q[i]
        qt, qf = M2t@Q[i], M2f@Q[i]
        qtt, qtf, qff = M2tt@Q[i], M2tf@Q[i], M2ff@Q[i]
        # D2_j = Qi - Vj rows; applied differences
        d = q[None, :] - M2V
        dt = qt[None, :] - M2tV
        df = qf[None, :] - M2fV
        dtt = qtt[None, :] - M2ttV
        dtf = qtf[None, :] - M2tfV
        dff = qff[None, :] - M2ffV
        D2n = np.linalg.norm(Q[i][None, :] - V, axis=1)
        keep = D2n > 1e-12            # exclude Vj == Qi
        N = (q*d).sum(1)
        d_tN = (qt*d).sum(1) + (q*dt).sum(1)
        d_fN = (qf*d).sum(1) + (q*df).sum(1)
        d_ttN = (qtt*d).sum(1) + 2*(qt*dt).sum(1) + (q*dtt).sum(1)
        d_tfN = (qtf*d).sum(1) + (qt*df).sum(1) + (qf*dt).sum(1) + (q*dtf).sum(1)
        d_ffN = (qff*d).sum(1) + 2*(qf*df).sum(1) + (q*dff).sum(1)
        DN = (e_t2*np.abs(d_tN) + e_f2*np.abs(d_fN)
              + 0.5*(e_t2**2*np.abs(d_ttN) + 2*e_t2*e_f2*np.abs(d_tfN)
                     + e_f2**2*np.abs(d_ffN))
              + 8*np.linalg.norm(Q[i])*D2n*E2s**3/6)
        nd = np.linalg.norm(d, axis=1)
        Ddij = (e_t2*np.linalg.norm(dt, axis=1) + e_f2*np.linalg.norm(df, axis=1)
                + 0.5*(e_t2**2*np.linalg.norm(dtt, axis=1)
                       + 2*e_t2*e_f2*np.linalg.norm(dtf, axis=1)
                       + e_f2**2*np.linalg.norm(dff, axis=1))
                + E2s**3/6*D2n)
        numer = N - DN
        denom = (nMQ[i] + Dr[i]) * (nd + Ddij)
        sl = np.where(keep & (numer >= 0), numer/denom - bound, -1.0)
        slacks.append(float(sl[keep].min()))
    return min(slacks)

# ---------------- current (first-order) local certificate mirror ----------------

def local1_slack(center, eps_sup, P, Q, r_in, sigma_q, V):
    """Float mirror of the CURRENT Row.ValidLocal slack (sup-radius eps).
    r derived per box like the Lean check allows (r < min||M2 Qi|| - sqrt2 e)."""
    t1, f1, t2, f2, a = center
    e = eps_sup
    M1 = m_family(t1, f1)[0]
    M2 = m_family(t2, f2)[0]
    X1 = x_family(t1, f1)[0]
    X2 = x_family(t2, f2)[0]
    R = rot2(a)
    sQ = -1.0 if sigma_q else 1.0
    s2 = np.sqrt(2.0)
    slacks = []
    for i in range(3):
        slacks.append((X1 @ P[i]) - s2*e)
        slacks.append(sQ*(X2 @ Q[i]) - s2*e)
    for (M, T) in ((M1, P), (M2, Q)):
        for i in range(3):
            v, w = T[i], T[(i+1) % 3]
            slacks.append((R90@(M@v)) @ (M@w) - 2*e*(s2 + e))
    nMQ = np.array([np.linalg.norm(M2@Q[i]) for i in range(3)])
    r = (nMQ.min() - s2*e) * (1 - 1e-12)
    if r <= 0:
        return -1.0
    slacks.append(r)
    delta = max(np.linalg.norm(R@(M1@P[i]) - M2@Q[i]) for i in range(3))/2
    bound = (np.sqrt(5.0)*e + delta) / r
    M2V = V @ M2.T
    for i in range(3):
        q = M2@Q[i]
        d = q[None, :] - M2V
        D2n = np.linalg.norm(Q[i][None, :] - V, axis=1)
        keep = D2n > 1e-12
        N = (q*d).sum(1) - 2*e*D2n*(s2 + e)
        nd = np.linalg.norm(d, axis=1)
        denom = (nMQ[i] + s2*e) * (nd + 2*s2*e)
        sl = np.where(keep & (N >= 0), N/denom - bound, -1.0)
        slacks.append(float(sl[keep].min()))
    return min(slacks)

# ---------------- rebuild harness ----------------

def load_v6():
    NT, NRC, FC = [], [], []
    B = []
    PAY = []
    with open(CSV) as f:
        next(f)
        for line in f:
            p = line.rstrip("\n").split(",")
            NT.append(int(p[1]))
            NRC.append(int(p[2]) if p[2] else 0)
            FC.append(int(p[3]) if p[3] else 0)
            B.append([int(x) for x in p[5:15]])
            if p[1] == "2":
                PAY.append([int(p[15]), int(p[16]), int(p[17]), int(p[18]),
                            int(p[19]), int(p[20]), int(p[22])])
            else:
                PAY.append(None)
    return (np.array(NT, np.int8), np.array(NRC), np.array(FC),
            np.array(B, np.int64), PAY)

def try_global(center, e):
    w3, angs = ea.COARSE_W, ea.COARSE_ANG
    slack, comps = ea.aniso_grid(center, e, w3)
    A = slack.shape[1]
    flat = slack.ravel()
    jb = int(flat.argmax())
    if flat[jb] >= SLACK_MIN:
        return True, comps, jb, A
    order = np.argpartition(-flat, 63)[:64]
    order = order[np.argsort(-flat[order])]
    cols = np.unique(order % A)[:6]
    ra = (angs[cols][:, None] + ea.REFINE_DEL).ravel()
    ra = np.arctan2(np.sin(ra), np.cos(ra))
    rw = np.stack(v5.pythag(ra), axis=1)
    slack2, _ = ea.aniso_grid(center, e, rw)
    if slack2.max() >= SLACK_MIN:
        return True, comps, jb, A
    return False, comps, jb, A

def rebuild_cell(lo0, hi0, cands, V, VERTS, use2):
    """Greedy BSP of one cell box. cands: list of (P_idx3, Q_idx3, sigma) from
    v6 local leaves of the cell (with their boxes for intersection tests)."""
    stack = [(lo0.copy(), hi0.copy(), 0)]
    rows = 0
    scans = 0
    while stack:
        if scans >= SCAN_CAP:
            return None
        lo, hi, dep = stack.pop()
        scans += 1
        rows += 1
        center = (lo + hi) / (2 * DENOM)
        e = (hi - lo) / (2 * DENOM)
        ok, comps, jb, A = try_global(center, e)
        if ok:
            continue
        # local attempt with candidate payloads whose v6 boxes intersect,
        # nearest v6 box first
        hit = False
        isect = [c for c in cands if ((c[0] <= hi) & (c[1] >= lo)).all()]
        isect.sort(key=lambda c: int(np.abs((c[0] + c[1]) - (lo + hi)).max()))
        seen = set()
        tries = []
        for c in isect:
            key = (tuple(c[2]), tuple(c[3]), c[4])
            if key not in seen:
                seen.add(key)
                tries.append(c)
                if len(tries) >= LOCAL_TRY_CAP:
                    break
        for (clo, chi, pi, qi, sg) in tries:
            if True:
                P = VERTS[pi]
                Q = VERTS[qi]
                if use2:
                    if local2_slack(center, e, P, Q, sg, VERTS) > MARGIN2:
                        hit = True
                        break
                else:
                    if e.max() <= 0.04 and \
                       local1_slack(center, float(e.max()), P, Q, None, sg,
                                    VERTS) > MARGIN2:
                        hit = True
                        break
        if hit:
            continue
        # split
        contrib = ea.axis_contrib(e, comps, jb // A, jb % A)
        sides = hi - lo
        even = (sides >= 2) & (sides % 2 == 0)
        contrib[~even] = -np.inf
        loc_isect = any(((clo <= hi) & (chi >= lo)).all()
                        for (clo, chi, _, _, _) in cands)
        if loc_isect:
            key = np.where(even, sides, -1)
            ax = int(np.argmax(np.where(key == key.max(), contrib, -np.inf)))
        else:
            ax = int(np.argmax(contrib))
        if dep >= DEPTH_CAP or not np.isfinite(contrib[ax]):
            return None
        mid = (int(lo[ax]) + int(hi[ax])) // 2
        hi1 = hi.copy(); hi1[ax] = mid
        lo2 = lo.copy(); lo2[ax] = mid
        stack.append((lo2, hi, dep + 1))
        stack.append((lo, hi1, dep + 1))
    return rows

def main():
    n_cells = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    ea.init_geometry()
    VERTS = ea.VERTS
    NT, NRC, FC, B, PAY = load_v6()
    n = len(NT)
    BMIN = B[:, 0::2]; BMAX = B[:, 1::2]
    DEPTH = np.full(n, -1, np.int16); DEPTH[0] = 0
    for i in np.nonzero(NT == 3)[0]:
        DEPTH[FC[i]:FC[i]+NRC[i]] = DEPTH[i] + 1
    SUB = np.ones(n, np.int64)
    HASLOC = (NT == 2).copy()
    NLOC = (NT == 2).astype(np.int64)
    for i in range(n - 1, -1, -1):
        if NT[i] == 3:
            f, c = FC[i], NRC[i]
            SUB[i] += SUB[f:f+c].sum()
            HASLOC[i] = HASLOC[i] or HASLOC[f:f+c].any()
            NLOC[i] += NLOC[f:f+c].sum()
    cells = np.nonzero(DEPTH == 5)[0]
    tube = cells[HASLOC[cells] & (NT[cells] == 3)]
    # deterministic stratified sample, biased to bigger tube cells
    order = tube[np.argsort(-SUB[tube], kind="stable")]
    sel = order[np.linspace(0, len(order) - 1, n_cells).astype(int)]
    print(f"{len(tube):,} tube cells; sampled {len(sel)} "
          f"(subtree sizes {SUB[sel].min()}..{SUB[sel].max()})")
    tot6 = tot1 = tot2 = 0
    fail1 = fail2 = 0
    for ci, cell in enumerate(sel):
        # collect the cell's v6 local payloads (with boxes)
        stackx = [cell]
        cands = []
        while stackx:
            k = stackx.pop()
            if NT[k] == 3:
                stackx.extend(range(FC[k], FC[k]+NRC[k]))
            elif NT[k] == 2:
                pay = PAY[k]
                cands.append((BMIN[k].copy(), BMAX[k].copy(),
                              np.array(pay[0:3]), np.array(pay[3:6]), pay[6]))

        t0 = time.time()
        r1 = rebuild_cell(BMIN[cell], BMAX[cell], cands, None, VERTS, use2=False)
        r2 = rebuild_cell(BMIN[cell], BMAX[cell], cands, None, VERTS, use2=True)
        v6c = int(SUB[cell])
        tot6 += v6c
        tot1 += r1 if r1 else v6c
        tot2 += r2 if r2 else v6c
        fail1 += r1 is None
        fail2 += r2 is None
        print(f"cell {ci:3d} (row {cell}): v6={v6c:6d} rebuild1="
              f"{r1 if r1 else 'FAIL':>6} rebuild2={r2 if r2 else 'FAIL':>6} "
              f"locs={NLOC[cell]:4d} ({time.time()-t0:.0f}s)", flush=True)
    print(f"\nTOTALS: v6={tot6:,} rebuild1={tot1:,} rebuild2={tot2:,} "
          f"(fail1={fail1} fail2={fail2})")
    print(f"second-order / first-order rebuild ratio: {tot2/max(1,tot1):.3f}")
    print(f"second-order / v6 ratio: {tot2/max(1,tot6):.3f}")

if __name__ == "__main__":
    main()
