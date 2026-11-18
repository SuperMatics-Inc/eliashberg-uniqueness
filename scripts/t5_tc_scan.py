"""T5: multiband single-crossing probe (NUMERICAL, not a proof).
For random multiband models with pair-dependent Einstein frequencies Omega_ab (spread over two decades),
nonnegative couplings (some zero intraband), random DOS, compute the top eigenvalue r(T) of the linear
stability operator diag(w+2L)^-1/2 W diag(w+2L)^-1/2 (even sector, exterior frozen) on a log T grid,
and count (i) non-monotone steps of r(T) and (ii) crossings of r = 1 (re-entrance would give >1).
Thermodynamic Tc = sup{T : r(T) > 1} by the stability decomposition (proved); single crossing is the open part.
"""
import sys
import numpy as np
from scipy.linalg import eigh
from mb_core import Model
from t2_physics import stab_eig

rng = np.random.default_rng(31415)


def model_at(N, G, Om, T, Nf):
    vp = Om / (2 * np.pi * T)
    return Model(N, G / N[:, None], vp, Nf)


def main():
    nmod = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    worst_up = -np.inf
    multi = 0
    tested = 0
    for k in range(nmod):
        nb = int(rng.integers(2, 4))
        N = rng.uniform(0.2, 2.0, nb)
        G = rng.uniform(0.0, 1.5, (nb, nb)); G = 0.5 * (G + G.T)
        if rng.random() < 0.4:
            i = int(rng.integers(nb)); G[i, i] = 0.0
        G[G < 0.15] = 0.0  # sparsify: some pairs absent
        # keep band graph connected via a chain
        for a in range(nb - 1):
            G[a, a + 1] = G[a + 1, a] = max(G[a, a + 1], 0.05)
        Om = np.exp(rng.uniform(np.log(0.1), np.log(10.0), (nb, nb))); Om = np.sqrt(Om * Om.T)
        # bracket: scan T over 3 decades around max Omega
        Ts = np.exp(np.linspace(np.log(0.003), np.log(3.0), 44)) * Om.max()
        rs = []
        for T in Ts:
            vmax = Om.max() / (2 * np.pi * T)
            Nf = int(min(220, max(40, 25 * vmax)))
            rs.append(stab_eig(model_at(N, G, Om, T, Nf)))
        rs = np.array(rs)
        ups = np.diff(rs)
        worst_up = max(worst_up, (ups / rs[:-1]).max())
        cross = int(np.sum(np.diff(np.sign(rs - 1)) != 0))
        tested += int(rs[0] > 1 > rs[-1])
        multi += int(cross > 1)
        if cross > 1 or (ups > 1e-10 * rs[:-1]).any():
            print(f"model {k}: NON-MONOTONE or multi-crossing: crossings={cross}, r(T)={np.round(rs,5)}")
    print(f"models={nmod}, bracketing Tc={tested}, multi-crossing={multi}, worst relative increase of r(T) = {worst_up:.3e}")
    sys.exit(0)


if __name__ == "__main__":
    main()
