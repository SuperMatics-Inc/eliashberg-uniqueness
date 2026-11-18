"""Certify the ordering of two stationary energies using Arb ball arithmetic.

For g11 = 0.8 g in Fig. 2(b) of Aase, Maeland and Sudbo (arXiv:2309.15894),
the s++ stationary state lies strictly below the real state with band 2 reversed.

Model (as in t4): bands a = 0,1,2, N_a = 1 (common N_F factored out), Einstein kernel
lam_ab(k) = lam0_ab varpi^2 / (varpi^2 + k^2), lam0_ab = 2 N_F g_ab^2 / omega_E = g_ab^2 / 2000 (g in meV),
varpi = omega_E / (2 pi T) = 10/pi, T = 1 meV, window n = 0..Nf-1 with Nf = 175.
Two windows: 'frozen' (exterior spins in the normal state, Zeeman weight tau >= 0) and 'hard' (tau = 0).

Even planar reduction (manuscript, Lemma "Planar energy," with delta = 0): for gamma in R^V+, V+ = bands x {0..Nf-1},
E(S(gamma)) = 2 K(gamma),  K = sum_v w_v (1 - c_v) + 1/2 sum_{u!=v} D_uv (1 - c_u c_v) - 1/2 sum_{u,v} W_uv s_u s_v,
c = cos gamma, s = sin gamma (signed). Critical points of K are stationary points of the full spin chain
(planar + mirror-even configurations; manuscript, Lemma "Critical points in the first quadrant").

Certificate per state:
  (1) every coefficient is an Arb ball computed from exact rationals and pi;
  (2) Krawczyk test for grad K on the box X = gamma~ + [-r, r]^V: if |C g(gamma~)| + r * rowsum|I - C H(X)| < r
      componentwise, grad K has exactly one zero gamma* in X (H(X) = Arb enclosure of the Hessian on X);
  (3) K(gamma*) in K(gamma~) + [-1, 1] * r * sum_v sup_X |d_v K| (mean value theorem).
The last comparison checks that the lower endpoint of E_pi exceeds the upper endpoint of E_pp.
"""
import sys
import time

import numpy as np
from flint import arb, arb_mat, ctx

from mb_core import Model
from t2_physics import eliashberg_ZD
from t4_aase_trsb import real_solve

ctx.prec = 160
NF = 175
NB = 3
V = NB * NF
# g_ab / g as exact rationals (numerator, denominator); g = 85 meV
RAT = {(0, 0): (4, 5), (0, 1): (1, 10000), (0, 2): (3, 1000), (1, 1): (7, 5), (1, 2): (3, 1000), (2, 2): (1, 200)}


def ratio(a, b):
    return RAT[(min(a, b), max(a, b))]


def float_model(exterior):
    gm = np.array([[85.0 * ratio(a, b)[0] / ratio(a, b)[1] for b in range(NB)] for a in range(NB)])
    lam0 = 2 * 0.005 * gm ** 2 / 20.0
    return Model([1.0, 1.0, 1.0], lam0, 20.0 / (2 * np.pi), NF, exterior=exterior)


def coeffs_float(m):
    n = np.arange(NF)
    w = m.zee[:, NF:].reshape(-1)
    A = np.zeros((V, V)); B = np.zeros((V, V))
    for a in range(NB):
        for b in range(NB):
            l0, vp = m.lam0[a, b], m.varpi[a, b]
            ker = lambda k: l0 * vp ** 2 / (vp ** 2 + k ** 2)
            A[a * NF:(a + 1) * NF, b * NF:(b + 1) * NF] = ker(np.abs(n[:, None] - n[None, :]))
            B[a * NF:(a + 1) * NF, b * NF:(b + 1) * NF] = ker(n[:, None] + n[None, :] + 1.0)
    D = A - B; W = A + B
    np.fill_diagonal(D, 0.0)
    np.fill_diagonal(W, 2 * np.diag(B))
    return w, D, W


def K_float(g, w, D, W):
    c, s = np.cos(g), np.sin(g)
    return np.sum(w * (1 - c)) + 0.5 * (D.sum() - c @ D @ c) - 0.5 * s @ W @ s


def grad_float(g, w, D, W):
    c, s = np.cos(g), np.sin(g)
    return w * s + s * (D @ c) - c * (W @ s)


def hess_float(g, w, D, W):
    c, s = np.cos(g), np.sin(g)
    H = -(D * np.outer(s, s)) - W * np.outer(c, c)
    diag = w * c + c * (D @ c) + s * (W @ s) - np.diag(W) * c * c
    np.fill_diagonal(H, diag)
    return H


def newton(g, w, D, W, its=8):
    for _ in range(its):
        g = g - np.linalg.solve(hess_float(g, w, D, W), grad_float(g, w, D, W))
    return g


def coeffs_arb(exterior):
    """w, D, W as Python lists of arb balls (exact rationals, pi enclosed)."""
    varpi2 = (arb(10) / arb.pi()) ** 2
    lam0 = {}
    for a in range(NB):
        for b in range(NB):
            p, q = ratio(a, b)
            g = arb(85 * p) / q
            lam0[(a, b)] = g * g / 2000
    kmax = 2 * NF + 2
    lam = {(a, b): [lam0[(a, b)] * varpi2 / (varpi2 + k * k) for k in range(kmax)] for a in range(NB) for b in range(NB)}
    w = []
    for a in range(NB):
        for n in range(NF):
            tau = arb(0)
            if exterior:
                for b in range(NB):
                    for t in range(NF - n, NF + n + 1):
                        tau += lam[(a, b)][t]
            w.append(2 * n + 1 + tau)
    D = [[arb(0)] * V for _ in range(V)]
    W = [[arb(0)] * V for _ in range(V)]
    for a in range(NB):
        for b in range(NB):
            la = lam[(a, b)]
            for n in range(NF):
                u = a * NF + n
                Du, Wu = D[u], W[u]
                for mm in range(NF):
                    v = b * NF + mm
                    Aval = la[abs(n - mm)]
                    Bval = la[n + mm + 1]
                    if u == v:
                        Wu[v] = 2 * Bval
                    else:
                        Du[v] = Aval - Bval
                        Wu[v] = Aval + Bval
    return w, D, W


def col(vals):
    return arb_mat([[x] for x in vals])


def K_arb(gam, w, Dm, Wm, Dsum):
    c = [x.cos() for x in gam]; s = [x.sin() for x in gam]
    cc, ss = col(c), col(s)
    cDc = (cc.transpose() * Dm * cc)[0, 0]
    sWs = (ss.transpose() * Wm * ss)[0, 0]
    zee = sum((w[v] * (1 - c[v]) for v in range(V)), arb(0))
    return zee + (Dsum - cDc) / 2 - sWs / 2


def grad_arb(gam, w, Dm, Wm):
    c = [x.cos() for x in gam]; s = [x.sin() for x in gam]
    Dc = Dm * col(c); Ws = Wm * col(s)
    return [w[v] * s[v] + s[v] * Dc[v, 0] - c[v] * Ws[v, 0] for v in range(V)]


def hess_arb(gam, w, D, W, Dm, Wm):
    c = [x.cos() for x in gam]; s = [x.sin() for x in gam]
    Dc = Dm * col(c); Ws = Wm * col(s)
    rows = []
    for u in range(V):
        Du, Wu, su, cu = D[u], W[u], s[u], c[u]
        row = [-(Du[v] * su * s[v]) - Wu[v] * cu * c[v] for v in range(V)]
        row[u] = w[u] * cu + cu * Dc[u, 0] + su * Ws[u, 0] - Wu[u] * cu * cu
        rows.append(row)
    return arb_mat(rows)


def certify(label, gt, w, D, W, Dm, Wm, Dsum, Hf):
    """Krawczyk existence/uniqueness of a zero of grad K near gt, and an enclosure of K at that zero."""
    t0 = time.time()
    Cf = np.linalg.inv(Hf)
    C = arb_mat([[float(x) for x in row] for row in Cf])
    gpt = grad_arb([arb(float(x)) for x in gt], w, Dm, Wm)
    y = C * col(gpt)
    ymax = max(float(y[v, 0].abs_upper()) for v in range(V))
    r = max(1e3 * ymax, 1e-13)
    X = [arb(float(x), r) for x in gt]
    HX = hess_arb(X, w, D, W, Dm, Wm)
    Delta = arb_mat.eye(V) - C * HX if hasattr(arb_mat, "eye") else None
    if Delta is None:
        I = arb_mat([[arb(1) if i == j else arb(0) for j in range(V)] for i in range(V)])
        Delta = I - C * HX
    worst = 0.0
    ok = True
    for v in range(V):
        rs = sum((Delta[v, u].abs_upper() for u in range(V)), arb(0))
        bound = y[v, 0].abs_upper() + r * rs
        if not bound < r:
            ok = False
        worst = max(worst, float((bound / r).upper()))
    gX = grad_arb(X, w, Dm, Wm)
    slack = r * sum((g.abs_upper() for g in gX), arb(0))
    Kc = K_arb([arb(float(x)) for x in gt], w, Dm, Wm, Dsum)
    Kenc = Kc + arb(0, 1) * slack
    E = 2 * Kenc
    signs_fixed = all(abs(float(x)) > r for x in gt)
    # every box component lies in (-pi/2, pi/2) with a fixed sign (checked in ball arithmetic): no spin flip
    half_pi = arb.pi() / 2
    in_quadrant = all(bool(half_pi - (arb(abs(float(x))) + r) > 0) for x in gt)
    band_signs = [sorted({int(np.sign(x)) for x in gt[a * NF:(a + 1) * NF]}) for a in range(NB)]
    print(f"  [{label}] Newton step max|C g| = {ymax:.3e}, box radius r = {r:.3e}, Krawczyk max (|y|+r*rowsum)/r = "
          f"{worst:.3e} -> {'PASS' if ok else 'FAIL'}; box excludes gamma=0: {signs_fixed}; "
          f"box inside |gamma| < pi/2: {in_quadrant}; signs per band: {band_signs}; "
          f"E* in {E.str(20, radius=True)}  ({time.time() - t0:.1f}s)")
    return ok and signs_fixed and in_quadrant, E


def run(exterior):
    tag = "frozen exterior" if exterior else "hard cutoff"
    print(f"== window: {tag}, Nf={NF}, g11=0.8g ==")
    m = float_model(exterior)
    w_f, D_f, W_f = coeffs_float(m)
    om = 2 * np.arange(NF) + 1.0
    Dpp, _, _, err1 = eliashberg_ZD(m, tol=1e-13)
    D0 = Dpp.copy(); D0[1] *= -1
    Dpi, err2 = real_solve(m, D0)
    states = {}
    for name, Dl in (("s++", Dpp), ("theta=pi", Dpi)):
        g0 = np.arctan2(Dl, om[None, :]).reshape(-1)
        g = newton(g0, w_f, D_f, W_f)
        # consistency with the full spin-chain energy of mb_core (float)
        S = np.zeros((NB, 2 * NF, 3))
        gg = g.reshape(NB, NF)
        S[:, NF:, 0] = np.sin(gg); S[:, NF:, 2] = np.cos(gg)
        S[:, :NF, 0] = np.sin(gg)[:, ::-1]; S[:, :NF, 2] = -np.cos(gg)[:, ::-1]
        e_chain = m.energy(S.reshape(-1, 3))
        k2 = 2 * K_float(g, w_f, D_f, W_f)
        print(f"  {name}: sign(gamma_a,0) = {np.sign(gg[:, 0])}, |grad K| after Newton = "
              f"{np.max(np.abs(grad_float(g, w_f, D_f, W_f))):.2e}, 2K = {k2:.12f}, chain E = {e_chain:.12f}")
        states[name] = (g, hess_float(g, w_f, D_f, W_f), k2 - e_chain)
    t0 = time.time()
    w, D, W = coeffs_arb(exterior)
    tau_err = max(abs(float(w[a * NF + n].mid()) - w_f[a * NF + n]) for a in range(NB) for n in range(NF))
    Dm, Wm = arb_mat(D), arb_mat(W)
    Dsum = sum((x for row in D for x in row), arb(0))
    print(f"  Arb coefficients built ({time.time() - t0:.1f}s); max |w_arb - w_float| = {tau_err:.2e}")
    res = {}
    for name in ("s++", "theta=pi"):
        g, Hf, cons = states[name]
        res[name] = certify(name, g, w, D, W, Dm, Wm, Dsum, Hf)
    okpp, Epp = res["s++"]
    okpi, Epi = res["theta=pi"]
    gap = Epi - Epp
    ordered = bool(Epi > Epp)
    print(f"  E(theta=pi) - E(s++) in {gap.str(12, radius=True)}; certified lower(E_pi) > upper(E_pp): {ordered}")
    eig = np.linalg.eigvalsh(states["theta=pi"][1])
    print(f"  (float, not certified) Hessian of K at theta=pi state: lowest eigenvalues {np.round(eig[:3], 6)}")
    return okpp and okpi and ordered


def main():
    t0 = time.time()
    ok = True
    for ext in (True, False):
        ok &= run(ext)
    print(f"total {time.time() - t0:.1f}s")
    print("CERTIFIED" if ok else "CERTIFICATE FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
