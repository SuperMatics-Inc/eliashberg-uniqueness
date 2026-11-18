"""Test exact identities of the multiband spin functional in floating point.

Use random densities of states and pair-dependent Einstein kernels. The
tests include nonnegative couplings and zero or indefinite diagonals.
 (a) even-sector reduction  E_full(even config) = 2 K(theta, phi)
 (b) rearrangement          K = sum w(1-c) + sum L rho + 1/4 sum D (c-c)^2 - 1/2 sum W x x cos(dphi)
 (c) stability decomposition K = Q(x e^{i phi})/2 + 1/2 sum w (1-c)^2 + 1/4 sum D (c-c)^2
 (d) alignment identity      E(S) - E(S') = 1/2 sum J (r r' - S_perp.S'_perp) >= 0
 (e) Siraj's folding identity on band-frequency vertices: E_pl(phi,psi) = 2K(hat gamma) + R, R >= 0
 (f) strict midpoint convexity of the aligned folded energy in rho = x^2
Report the largest discrepancies. Exit with status 1 if any identity fails the relative tolerance of 1e-9.
"""
import sys
import numpy as np
from mb_core import Model

rng = np.random.default_rng(20261116)


def random_model(nb, Nf, zero_diag=False):
    N = rng.uniform(0.3, 2.0, nb)
    # symmetric weighted couplings G_ab = N_a lam_ab >= 0, connected
    G = rng.uniform(0.05, 1.5, (nb, nb))
    G = 0.5 * (G + G.T)
    if zero_diag:
        np.fill_diagonal(G, 0.0)
    lam0 = G / N[:, None]
    vp = rng.uniform(0.3, 3.0, (nb, nb))
    vp = 0.5 * (vp + vp.T)
    return Model(N, lam0, vp, Nf)


def even_structs(m):
    nb, Nf = m.nb, m.Nf
    n = np.arange(Nf)
    V = nb * Nf
    A = np.zeros((V, V)); B = np.zeros((V, V)); w = np.zeros(V)
    for a in range(nb):
        w[a * Nf:(a + 1) * Nf] = m.zee[a, Nf + n]  # N_a (2n+1+tau)
        for b in range(nb):
            lam = m.lam[a, b]  # [i,j] over window indices
            A[a * Nf:(a + 1) * Nf, b * Nf:(b + 1) * Nf] = m.N[a] * lam[np.ix_(Nf + n, Nf + n)]
            B[a * Nf:(a + 1) * Nf, b * Nf:(b + 1) * Nf] = m.N[a] * lam[np.ix_(Nf + n, Nf - n - 1)]
    np.fill_diagonal(A, 0.0)
    return w, A, B


def to_full(m, th, ph):
    """even config: S_{a,n}=(x cos ph, x sin ph, c), S_{a,-n-1}=(x cos ph, x sin ph, -c)."""
    nb, Nf = m.nb, m.Nf
    S = np.zeros((nb, 2 * Nf, 3))
    T = th.reshape(nb, Nf); P = ph.reshape(nb, Nf)
    x, c = np.sin(T), np.cos(T)
    for a in range(nb):
        S[a, Nf:, :] = np.column_stack([x[a] * np.cos(P[a]), x[a] * np.sin(P[a]), c[a]])
        S[a, :Nf, :] = np.column_stack([x[a] * np.cos(P[a]), x[a] * np.sin(P[a]), -c[a]])[::-1]
    return S.reshape(-1, 3)


def K_direct(w, A, B, th, ph):
    c, x = np.cos(th), np.sin(th)
    cc = np.outer(c, c); xx = np.outer(x, x) * np.cos(ph[:, None] - ph[None, :])
    k = np.sum(w * (1 - c))
    k += 0.5 * np.sum(A * (1 - cc - xx))
    k -= 0.5 * np.sum(B * (1 - cc + xx))
    return k


def K_rearr(w, A, B, th, ph):
    c, x = np.cos(th), np.sin(th)
    D = A - B; np.fill_diagonal(D, 0.0)
    W = A + B; np.fill_diagonal(W, 2 * np.diag(B))
    L = 0.5 * D.sum(1)
    rho = x ** 2
    xx = np.outer(x, x) * np.cos(ph[:, None] - ph[None, :])
    return (np.sum(w * (1 - c)) + np.sum(L * rho) + 0.25 * np.sum(D * (c[:, None] - c[None, :]) ** 2)
            - 0.5 * np.sum(W * xx)), D, W, L


def main():
    worst = {}
    def rec(k, v):
        worst[k] = max(worst.get(k, 0.0), v)
    for trial in range(40):
        nb = int(rng.integers(1, 4)); Nf = int(rng.integers(3, 12))
        m = random_model(nb, Nf, zero_diag=(trial % 3 == 0))
        w, A, B = even_structs(m)
        V = len(w)
        assert np.all(A - B + np.eye(V) * 1e9 >= -1e-14), "A>=B violated"
        th = rng.uniform(-np.pi, np.pi, V); ph = rng.uniform(0, 2 * np.pi, V)
        # (a)
        S = to_full(m, th, ph)
        Ef = m.energy(S); Kd = K_direct(w, A, B, th, ph)
        rec("a_even_reduction", abs(Ef - 2 * Kd) / (1 + abs(Ef)))
        # (b)
        Kr, D, W, L = K_rearr(w, A, B, th, ph)
        rec("b_rearrangement", abs(Kr - Kd) / (1 + abs(Kd)))
        rec("b_minD", -min(0.0, D.min())); rec("b_minW", -min(0.0, W.min())); rec("b_minL", -min(0.0, L.min()))
        # (c)
        c, x = np.cos(th), np.sin(th)
        z = x * np.exp(1j * ph)
        Q = np.sum((w + 2 * L) * np.abs(z) ** 2) - np.real(np.conj(z) @ W @ z)
        Kst = 0.5 * Q + 0.5 * np.sum(w * (1 - c) ** 2) + 0.25 * np.sum(D * (c[:, None] - c[None, :]) ** 2)
        rec("c_stab_decomp", abs(Kst - Kd) / (1 + abs(Kd)))
        # (d) alignment on a general (non-even, 3D) full-chain configuration
        S3 = rng.normal(size=(nb * 2 * Nf, 3)); S3 /= np.linalg.norm(S3, axis=1)[:, None]
        r = np.hypot(S3[:, 0], S3[:, 1])
        Sal = np.column_stack([r, 0 * r, S3[:, 2]])
        lhs = m.energy(S3) - m.energy(Sal)
        perp = S3[:, :2] @ S3[:, :2].T
        rhs = 0.5 * np.sum(m.J * (np.outer(r, r) - perp))
        rec("d_alignment", abs(lhs - rhs) / (1 + abs(lhs)))
        rec("d_alignment_negative", -min(0.0, lhs))
        # (e) fold identity for planar full-chain configs, phi,psi in [0,pi]
        phi = rng.uniform(0, np.pi, V); psi_ = rng.uniform(0, np.pi, V)
        Sp = np.zeros((nb, 2 * Nf, 3))
        P1 = phi.reshape(nb, Nf); P2 = psi_.reshape(nb, Nf)
        for a in range(nb):
            Sp[a, Nf:, :] = np.column_stack([np.sin(P1[a]), 0 * P1[a], np.cos(P1[a])])
            Sp[a, :Nf, :] = np.column_stack([np.sin(P2[a]), 0 * P2[a], -np.cos(P2[a])])[::-1]
        Epl = m.energy(Sp.reshape(-1, 3))
        gam = 0.5 * (phi + psi_); dl = 0.5 * (psi_ - phi)
        eta = np.where(gam <= np.pi / 2, 1.0, -1.0); gh = np.minimum(gam, np.pi - gam)
        Kg = K_direct(w, A, B, gh, 0 * gh)
        Dn = A - B; np.fill_diagonal(Dn, 0.0); Wn = A + B; np.fill_diagonal(Wn, 0.0)
        cg, sg = np.cos(gh), np.sin(gh)
        dd = dl[:, None] - dl[None, :]
        R = (np.sum(2 * w * cg * (1 - eta * np.cos(dl)))
             + np.sum(Dn * np.outer(cg, cg) * (1 - np.outer(eta, eta) * np.cos(dd)))
             + np.sum(Wn * np.outer(sg, sg) * (1 - np.cos(dd))))
        rec("e_fold_identity", abs(Epl - 2 * Kg - R) / (1 + abs(Epl)))
        rec("e_R_negative", -min(0.0, R))
        # (f) strict midpoint convexity of aligned folded energy in rho
        def Krho(rho):
            xx = np.sqrt(rho); cc = np.sqrt(1 - rho)
            return K_rearr(w, A, B, np.arctan2(xx, cc), 0 * rho)[0]
        for _ in range(20):
            r1 = rng.uniform(0, 1, V) ** rng.uniform(0.5, 4); r2 = rng.uniform(0, 1, V) ** rng.uniform(0.5, 4)
            gap = 0.5 * (Krho(r1) + Krho(r2)) - Krho(0.5 * (r1 + r2))
            rec("f_convexity_violation", -min(0.0, gap / (1 + abs(Krho(r1)))))
    ok = True
    for k, v in worst.items():
        flag = v < 1e-9
        ok &= flag
        print(f"{k:28s} worst = {v:.3e}  {'OK' if flag else 'FAIL'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
