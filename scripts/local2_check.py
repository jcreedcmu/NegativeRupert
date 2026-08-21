"""Float mirror of Row.ValidLocal₂ (the SECOND-ORDER anisotropic local check).

Mirrors Noperthedron/Checker/Local2.lean condition by condition:

  A (X₁/X₂):  <Xb, Pi> - ΔvecX > 0        (ΔvecX = first+second exact partials
                                            at the center + E³/6 remainder)
  spanning:   <R90 M Pi, M Pj> - ΔprodMM(rot90) > 0
  r:          r'/1000 chosen so that  r + ΔrotM(Qi) < ||M₂ Qi||  holds with a
              SAFE_R float/κ cushion; positivity of r required.
  δ:          NOT a condition — Lean derives Row.δ₂ from the row; we compute
              the float value plus a SAFE_D upper cushion for the B threshold.
  B(i,k):     (N - ΔN) / ((||M₂ Qi||+Δr_i)(||M₂ D||+Δd_ik)) > δ₂/r  with
              N - ΔN ≥ NUMER_MIN  (Lean requires strict positivity of the
              κ-slacked rational numerator).

The Lean side adds κℚ = 1e-10 slack terms per atom (≤ ~1e-9 total per
condition); `margin` (default 3e-9) plus the explicit cushions cover them
and the float/trig-approx error.

The returned r' is the quantized integer the emitted row must carry
(CSV `r` column; Row.r = r'/1000).
"""
import numpy as np

R90 = np.array([[0.0, -1.0], [1.0, 0.0]])
SAFE_R = 1e-6          # cushion between float r_max and the quantized r
SAFE_D = 1e-6          # cushion added to the float δ (upper bound of Row.δ₂)
NUMER_MIN = 1e-8       # floor for the B numerator (Lean: 0 < slacked numerator)
DEFAULT_MARGIN = 1e-8


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


def rot2(a):
    ca, sa = np.cos(a), np.sin(a)
    return np.array([[ca, -sa], [sa, ca]])


def check_local2(center, e, P, Q, sigma_q, V, margin=DEFAULT_MARGIN):
    """Second-order local check for one box.

    center: pose 5 [t1,f1,t2,f2,a]; e: per-axis radii (same order);
    P, Q: (3,3) triangle vertex coordinates; sigma_q in {0,1};
    V: (90,3) all vertices.  Returns (slack_min, r_prime) — accepted iff
    slack_min > margin and r_prime > 0."""
    t1, f1, t2, f2, a = center
    e_t1, e_f1, e_t2, e_f2, e_a = e
    E1s = e_t1 + e_f1
    E2s = e_t2 + e_f2
    M1, M1t, M1f, M1tt, M1tf, M1ff = m_family(t1, f1)
    M2, M2t, M2f, M2tt, M2tf, M2ff = m_family(t2, f2)
    X1, X1t, X1f, X1tt, X1tf, _ = x_family(t1, f1)
    X2, X2t, X2f, X2tt, X2tf, _ = x_family(t2, f2)
    R = rot2(a)
    sQ = -1.0 if sigma_q else 1.0
    slacks = []

    # A conditions (note the Lean ΔvecX's εφ² atom is |<X, P>| itself: Xff = -X)
    for i in range(3):
        pen = (e_t1*abs(X1t @ P[i]) + e_f1*abs(X1f @ P[i])
               + 0.5*(e_t1**2*abs(X1tt @ P[i]) + 2*e_t1*e_f1*abs(X1tf @ P[i])
                      + e_f1**2*abs(X1 @ P[i]))
               + E1s**3/6)
        slacks.append((X1 @ P[i]) - pen)
        pen = (e_t2*abs(X2t @ Q[i]) + e_f2*abs(X2f @ Q[i])
               + 0.5*(e_t2**2*abs(X2tt @ Q[i]) + 2*e_t2*e_f2*abs(X2tf @ Q[i])
                      + e_f2**2*abs(X2 @ Q[i]))
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

    # r: quantized so that BoundR₂ℚ holds with the SAFE_R cushion
    def dvar_vec(w, et, ef, Es):
        # Lean ΔrotMℚ charges the cubic at scale 1 (unit vertices)
        return (et*np.linalg.norm(M2t@w) + ef*np.linalg.norm(M2f@w)
                + 0.5*(et**2*np.linalg.norm(M2tt@w)
                       + 2*et*ef*np.linalg.norm(M2tf@w)
                       + ef**2*np.linalg.norm(M2ff@w))
                + Es**3/6)
    nMQ = np.array([np.linalg.norm(M2@Q[i]) for i in range(3)])
    Dr = np.array([dvar_vec(Q[i], e_t2, e_f2, E2s) for i in range(3)])
    r_max = float((nMQ - Dr).min())
    r_prime = int(np.floor((r_max - SAFE_R) * 1000.0))
    if r_prime <= 0:
        return -1.0, 0
    r = r_prime / 1000.0
    slacks.append(r)

    # δ upper bound (Lean derives Row.δ₂; the cushion covers its κ terms)
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
              + Etot1**3/6 + E2s**3/6)
        dd.append((np.linalg.norm(v0) + Dd)/2)
    delta_hi = max(dd) + SAFE_D

    # B condition over all pairs (i, k)
    bound = delta_hi / r
    M2V = V @ M2.T
    M2tV = V @ M2t.T
    M2fV = V @ M2f.T
    M2ttV = V @ M2tt.T
    M2tfV = V @ M2tf.T
    M2ffV = V @ M2ff.T
    for i in range(3):
        q = M2@Q[i]
        qt, qf = M2t@Q[i], M2f@Q[i]
        qtt, qtf, qff = M2tt@Q[i], M2tf@Q[i], M2ff@Q[i]
        d = q[None, :] - M2V
        dt = qt[None, :] - M2tV
        df = qf[None, :] - M2fV
        dtt = qtt[None, :] - M2ttV
        dtf = qtf[None, :] - M2tfV
        dff = qff[None, :] - M2ffV
        D2n = np.linalg.norm(Q[i][None, :] - V, axis=1)
        keep = D2n > 1e-12            # exclude V_k == Q_i
        N = (q*d).sum(1)
        d_tN = (qt*d).sum(1) + (q*dt).sum(1)
        d_fN = (qf*d).sum(1) + (q*df).sum(1)
        d_ttN = (qtt*d).sum(1) + 2*(qt*dt).sum(1) + (q*dtt).sum(1)
        d_tfN = (qtf*d).sum(1) + (qt*df).sum(1) + (qf*dt).sum(1) + (q*dtf).sum(1)
        d_ffN = (qff*d).sum(1) + 2*(qf*df).sum(1) + (q*dff).sum(1)
        DN = (e_t2*np.abs(d_tN) + e_f2*np.abs(d_fN)
              + 0.5*(e_t2**2*np.abs(d_ttN) + 2*e_t2*e_f2*np.abs(d_tfN)
                     + e_f2**2*np.abs(d_ffN))
              + 8*D2n*E2s**3/6)
        nd = np.linalg.norm(d, axis=1)
        Ddik = (e_t2*np.linalg.norm(dt, axis=1) + e_f2*np.linalg.norm(df, axis=1)
                + 0.5*(e_t2**2*np.linalg.norm(dtt, axis=1)
                       + 2*e_t2*e_f2*np.linalg.norm(dtf, axis=1)
                       + e_f2**2*np.linalg.norm(dff, axis=1))
                + E2s**3/6*D2n)
        numer = N - DN
        denom = (nMQ[i] + Dr[i]) * (nd + Ddik)
        with np.errstate(divide="ignore", invalid="ignore"):
            quot = np.where(denom > 0, numer / denom, -1.0)
        sl = np.where(keep & (numer >= NUMER_MIN),
                      np.minimum(numer - NUMER_MIN, quot - bound), -1.0)
        slacks.append(float(sl[keep].min()))
    return float(min(slacks)), r_prime
