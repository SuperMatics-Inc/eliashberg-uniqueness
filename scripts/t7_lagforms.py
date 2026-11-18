"""Test the signs of the lag forms on multiband critical modes.
Write the even-sector stability form in y = Delta/omega as
  Q_T(y) = sum_v w_v y_v^2 - sum_{a,b} N_a sum_k lam_ab,T(k) q_k^{ab}(y),
  q_k^{ab}(y) = 1/2 sum_{n+m+1=k} (y_an + y_bm)^2 - 1/2 sum_{|n-m|=k, (a,n)!=(b,m)} (y_an - y_bm)^2 .
Scalar (a=b): q_k >= 0 on non-negative non-increasing y (telescoping; proved in the manuscript's "Scope and open problems" section), and lam_T(k) decreases
in T for k>=1, which gives single crossing once the critical mode is non-negative and non-increasing.
Here: at T = T_c of random multiband models (bisection on the top eigenvalue r(T)=1) we test
 (i) whether each band component of the critical mode is non-negative and non-increasing in n;
 (ii) the sign of every interband lag form q_k^{ab}(y), k>=1, on that mode.
"""
import sys
import numpy as np
from scipy.optimize import brentq
from mb_core import Model
from t2_physics import stab_eig

rng = np.random.default_rng(2718)


def mats(m):
    nb, Nf = m.nb, m.Nf
    n = np.arange(Nf); V = nb * Nf
    A = np.zeros((V, V)); B = np.zeros((V, V)); w = np.zeros(V)
    for a in range(nb):
        w[a * Nf:(a + 1) * Nf] = m.zee[a, Nf + n]
        for b in range(nb):
            A[a*Nf:(a+1)*Nf, b*Nf:(b+1)*Nf] = m.N[a] * m.lam[a, b][np.ix_(Nf + n, Nf + n)]
            B[a*Nf:(a+1)*Nf, b*Nf:(b+1)*Nf] = m.N[a] * m.lam[a, b][np.ix_(Nf + n, Nf - n - 1)]
    np.fill_diagonal(A, 0.0)
    D = A - B; np.fill_diagonal(D, 0.0)
    W = A + B; np.fill_diagonal(W, 2 * np.diag(B))
    return w, D, W


def critical_mode(m):
    w, D, W = mats(m)
    d = w + D.sum(1)
    M = W / np.sqrt(np.outer(d, d))
    ev, U = np.linalg.eigh(M)
    v = U[:, -1]; v = v * np.sign(v.sum())
    y = v / np.sqrt(d)
    return ev[-1], y.reshape(m.nb, m.Nf), w


def lagform(ya, yb, k):
    Nf = len(ya)
    bpart = 0.5 * sum((ya[n] + yb[k - 1 - n]) ** 2 for n in range(k) if 0 <= k - 1 - n < Nf)
    apart = 0.5 * (np.sum((ya[:Nf - k] - yb[k:]) ** 2) + np.sum((ya[k:] - yb[:Nf - k]) ** 2))
    return bpart - apart


def main():
    nmod = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    Nf = 120
    nonmono = 0; neg_inter = 0; neg_intra = 0; worst = 0.0
    for t in range(nmod):
        nb = int(rng.integers(2, 4))
        N = rng.uniform(0.2, 2.0, nb)
        G = rng.uniform(0.0, 1.5, (nb, nb)); G = 0.5 * (G + G.T)
        if rng.random() < 0.4:
            i = int(rng.integers(nb)); G[i, i] = 0.0
        for a in range(nb - 1):
            G[a, a + 1] = G[a + 1, a] = max(G[a, a + 1], 0.05)
        Om = np.exp(rng.uniform(np.log(0.1), np.log(10.0), (nb, nb))); Om = np.sqrt(Om * Om.T)
        mk = lambda T: Model(N, G / N[:, None], Om / (2 * np.pi * T), Nf)
        f = lambda lt: stab_eig(mk(np.exp(lt))) - 1.0
        lo, hi = np.log(1e-3 * Om.max()), np.log(3.0 * Om.max())
        if not (f(lo) > 0 > f(hi)):
            continue
        Tc = np.exp(brentq(f, lo, hi, xtol=1e-10))
        if Om.max() / (2 * np.pi * Tc) > Nf / 25:
            continue
        m = mk(Tc)
        r, y, w = critical_mode(m)
        mono = all(np.all(np.diff(y[a]) <= 1e-14 * np.abs(y[a]).max()) and np.all(y[a] >= 0) for a in range(nb))
        nonmono += int(not mono)
        norm = float(np.sum(w * y.reshape(-1) ** 2))
        qmin_inter = np.inf; qmin_intra = np.inf
        for a in range(nb):
            for b in range(nb):
                for k in range(1, 40):
                    q = lagform(y[a], y[b], k) / norm
                    if a == b:
                        qmin_intra = min(qmin_intra, q)
                    else:
                        qmin_inter = min(qmin_inter, q)
        neg_inter += int(qmin_inter < -1e-12); neg_intra += int(qmin_intra < -1e-12)
        worst = min(worst, qmin_inter)
        print(f"model {t}: nb={nb} Tc/Omax={Tc/Om.max():.4f} r={r:.6f} mode nonneg+nonincreasing={mono} "
              f"min intra q_k/|y|^2={qmin_intra:+.2e} min inter q_k/|y|^2={qmin_inter:+.2e}")
    print(f"non-monotone critical modes={nonmono}, models with an intraband q_k<0={neg_intra}, "
          f"with an interband q_k<0={neg_inter}, most negative interband q_k/|y|_w^2={worst:+.3e}")
    # Three test cases: pure interband coupling, unequal band weights and a soft interband phonon.
    print("Two-band test cases: crossings of r(T)=1, largest relative increase on the temperature grid, "
          "and smallest interband q_k on the critical mode at Tc")
    cases = [
        ("pure interband", [1.0, 1.0], [[0.0, 1.0], [1.0, 0.0]], [[1.0, 1.0], [1.0, 1.0]]),
        ("pure interband", [1.0, 1e2], [[0.0, 1.0], [1.0, 0.0]], [[1.0, 1.0], [1.0, 1.0]]),
        ("pure interband", [1.0, 1e4], [[0.0, 1.0], [1.0, 0.0]], [[1.0, 1.0], [1.0, 1.0]]),
        ("strong a, soft weak interband", [1.0, 1.0], [[1.2, 0.05], [0.05, 0.0]], [[1.0, 0.05], [0.05, 1.0]]),
        ("strong a, soft interband, heavy b", [1.0, 1e3], [[1.2, 0.2], [0.2, 0.0]], [[1.0, 0.05], [0.05, 1.0]]),
        ("strong a hard, b soft intraband", [1.0, 30.0], [[1.0, 0.3], [0.3, 3.0]], [[3.0, 0.3], [0.3, 0.03]]),
    ]
    for name, N, G, Om in cases:
        N = np.array(N); G = np.array(G); Om = np.array(Om)
        mk = lambda T: Model(N, G / N[:, None], Om / (2 * np.pi * T), 160)
        Ts = np.exp(np.linspace(np.log(0.004), np.log(1.0), 40)) * Om.max()
        rs = np.array([stab_eig(mk(T)) for T in Ts])
        cross = int(np.sum(np.diff(np.sign(rs - 1)) != 0))
        qmin = np.nan
        if rs[0] > 1 > rs[-1]:
            Tc = np.exp(brentq(lambda lt: stab_eig(mk(np.exp(lt))) - 1, np.log(Ts[0]), np.log(Ts[-1]), xtol=1e-10))
            r, y, w = critical_mode(mk(Tc))
            norm = float(np.sum(w * y.reshape(-1) ** 2))
            qmin = min(min(lagform(y[0], y[1], k), lagform(y[1], y[0], k)) / norm for k in range(1, 40))
        print(f"  {name:36s} N2/N1={N[1]/N[0]:.0e}: crossings={cross} "
              f"max rel increase r(T)={np.max(np.diff(rs)/rs[:-1]):+.2e} min interband q_k/|y|^2 at Tc={qmin:+.2e}")
    sys.exit(0)


if __name__ == "__main__":
    main()
