"""Compare the finite spin functional with the Eliashberg equations numerically.

(1) Evaluate the one-band stability eigenvalue at the known Einstein lambda=1 Tc.
(2) Compare the multiband (Z, Delta) solver with a spin fixed point and
    minimization of the full three-dimensional spin energy from random starts.
    The minimization imposes no parity, phase or sign restrictions.
(3) Compare the ratio of the multiband Bardeen-Stephen free energy to the spin energy.
(4) Compare the sign of the lowest energy found with the top stability
    eigenvalue as temperature varies.
"""
import sys
import numpy as np
from mb_core import Model, minimize, phase_align

rng = np.random.default_rng(7)


def stab_eig(m):
    """top eigenvalue of diag(w+2L)^-1/2 W diag(w+2L)^-1/2 in the even sector."""
    nb, Nf = m.nb, m.Nf
    n = np.arange(Nf)
    V = nb * Nf
    A = np.zeros((V, V)); B = np.zeros((V, V)); w = np.zeros(V)
    for a in range(nb):
        w[a * Nf:(a + 1) * Nf] = m.zee[a, Nf + n]
        for b in range(nb):
            A[a*Nf:(a+1)*Nf, b*Nf:(b+1)*Nf] = m.N[a] * m.lam[a, b][np.ix_(Nf + n, Nf + n)]
            B[a*Nf:(a+1)*Nf, b*Nf:(b+1)*Nf] = m.N[a] * m.lam[a, b][np.ix_(Nf + n, Nf - n - 1)]
    np.fill_diagonal(A, 0.0)
    D = A - B; np.fill_diagonal(D, 0.0)
    W = A + B; np.fill_diagonal(W, 2 * np.diag(B))
    d = w + D.sum(1)
    M = W / np.sqrt(np.outer(d, d))
    return np.linalg.eigvalsh(M)[-1]


def eliashberg_ZD(m, iters=200000, tol=1e-14):
    """Independent real-even multiband Eliashberg solver (units pi T). Returns Delta[a,n], Z[a,n]."""
    nb, Nf = m.nb, m.Nf
    n = np.arange(Nf); om = 2 * n + 1.0
    Lp = np.zeros((nb, nb, Nf, Nf)); Lm = np.zeros_like(Lp)
    for a in range(nb):
        for b in range(nb):
            Lp[a, b] = m.lam[a, b][np.ix_(Nf + n, Nf + n)]
            Lm[a, b] = m.lam[a, b][np.ix_(Nf + n, Nf - n - 1)]
    tau = m.tau[:, Nf:]
    Dl = np.ones((nb, Nf)) * 1.0
    for it in range(iters):
        E = np.sqrt(om ** 2 + Dl ** 2)
        Z = 1 + (tau + np.einsum('abnm,bm->an', Lp - Lm, om / E)) / om
        Dn = np.einsum('abnm,bm->an', Lp + Lm, Dl / E) / Z
        err = np.max(np.abs(Dn - Dl))
        Dl = 0.5 * Dl + 0.5 * Dn
        if err < tol:
            break
    E = np.sqrt(om ** 2 + Dl ** 2)
    Z = 1 + (tau + np.einsum('abnm,bm->an', Lp - Lm, om / E)) / om
    ZN = 1 + (tau + np.einsum('abnm,bm->an', Lp - Lm, np.ones((nb, Nf)))) / om
    return Dl, Z, ZN, err


def bardeen_stephen(m, Dl, Z, ZN):
    om = 2 * np.arange(m.Nf) + 1.0
    E = np.sqrt(om ** 2 + Dl ** 2)
    # both frequency signs -> factor 2 (even solution)
    return -2 * np.sum(m.N[:, None] * (E - om) * (Z - ZN * om / E))


def spins_from_delta(m, Dl):
    nb, Nf = m.nb, m.Nf
    om = 2 * np.arange(Nf) + 1.0
    E = np.sqrt(om ** 2 + Dl ** 2)
    S = np.zeros((nb, 2 * Nf, 3))
    S[:, Nf:, 0] = Dl / E; S[:, Nf:, 2] = om / E
    S[:, :Nf, 0] = (Dl / E)[:, ::-1]; S[:, :Nf, 2] = -(om / E)[:, ::-1]
    return S.reshape(-1, 3)


def rand_model(nb, Nf, varpi_scale, zero_diag=False):
    N = rng.uniform(0.4, 2.0, nb)
    G = rng.uniform(0.1, 1.2, (nb, nb)); G = 0.5 * (G + G.T)
    if zero_diag:
        np.fill_diagonal(G, 0.0)
        G *= 2.0
    vp = varpi_scale * rng.uniform(0.5, 2.0, (nb, nb)); vp = 0.5 * (vp + vp.T)
    return Model(N, G / N[:, None], vp, Nf)


def main():
    ok = True
    # (1) one-band check: Einstein lambda=1, Tc/Omega = 0.1146195121 (scalar paper, N=400)
    vc = 1 / (2 * np.pi * 0.1146195121)
    m1 = Model([1.0], [[1.0]], [[vc]], 400, exterior=True)
    r1 = stab_eig(m1)
    print(f"(1) one-band Einstein lam=1 at T/Omega=0.1146195121: top stability eigenvalue = {r1:.10f}")
    ok &= abs(r1 - 1) < 1e-4

    # (2)+(3) random multiband instances below Tc
    print("(2) Multiband equations: spin fixed point, (Z, Delta) solver and minimization from random starts")
    ratios = []
    for trial in range(8):
        nb = [2, 2, 3, 2, 3, 2, 2, 3][trial]
        zd = trial in (1, 4)
        m = rand_model(nb, 24, varpi_scale=3.0, zero_diag=zd)
        Dl, Z, ZN, errZD = eliashberg_ZD(m)
        S0 = spins_from_delta(m, Dl)
        tq = m.torque(S0)
        Eeli = m.energy(S0)
        # Minimize the full three-dimensional energy without symmetry restrictions.
        Es, devs = [], []
        for s in range(12):
            U0 = rng.normal(size=S0.shape)
            S, res = minimize(m, U0)
            Es.append(m.energy(S))
            Sa = phase_align(S, ref_idx=int(np.argmax(np.hypot(S0[:, 0], S0[:, 1]))))
            devs.append(np.max(np.abs(Sa - S0)))
        Es = np.array(Es)
        bs = bardeen_stephen(m, Dl, Z, ZN)
        ratios.append(bs / Eeli)
        print(f"  trial {trial} nb={nb} zero_diag={zd}: lam_ab(0)=\n{np.array2string(m.lam0, precision=3)}\n"
              f"   ZD err={errZD:.1e} torque(ZD spins)={tq:.1e} E_eli={Eeli:.10f} "
              f"min_E(12 starts) in [{Es.min():.10f},{Es.max():.10f}] max|S-S_eli| mod U(1)={max(devs):.2e} "
              f"rho_stab={stab_eig(m):.4f} BS/E={bs/Eeli:.10f}")
        ok &= (tq < 1e-8) and (Es.min() > Eeli - 1e-9) and (Es.max() < Eeli + 1e-7) and (max(devs) < 1e-4)
    ratios = np.array(ratios)
    print(f"(3) Bardeen-Stephen/E ratio over instances: mean {ratios.mean():.12f} spread {np.ptp(ratios):.2e}")
    ok &= np.ptp(ratios) < 1e-6

    # (4) Tc_th = Tc_lin across temperature for one 2-band model (pair-dependent spectra, zero intraband 2-2)
    N = np.array([1.0, 0.6]); G = np.array([[0.8, 0.5], [0.5, 0.0]])
    vp0 = np.array([[1.0, 0.5], [0.5, 2.0]])  # Omega_ab/(2 pi T0)
    print("(4) T-scan: top stability eigenvalue rho vs min energy (normal-subtracted)")
    for Tfac in [0.6, 0.8, 0.9, 1.0, 1.1, 1.2, 1.4]:
        m = Model(N, G / N[:, None], vp0 / Tfac, 24)
        rho = stab_eig(m)
        best = 0.0
        for s in range(6):
            S, res = minimize(m, rng.normal(size=(m.nb * 2 * m.Nf, 3)))
            best = min(best, m.energy(S))
        print(f"   T/T0={Tfac:4.2f} rho={rho:.6f} minE={best: .3e}  {'SC' if best < -1e-10 else 'normal'}")
        ok &= ((rho > 1) == (best < -1e-10))
    print("ALL OK" if ok else "SOME CHECK FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
