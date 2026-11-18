"""Numerical phase checks for the phonon-only model of Aase, Maeland and Sudbo
(arXiv:2309.15894).

The model uses a common Einstein frequency omega_E = 20 meV at T = 1 meV.
The bands have equal densities of states N_F = 0.005/meV, and B_ij = |g_ij|^2 >= 0.
Here g = 85 meV, g11 is of order g, and g22 = 1.4g. The other couplings are
g33 = 0.005g, g12 = 1e-4 g, and g13 = g23 = 0.003g.
The frequency cutoff is 1100 meV (Nf = 175), with the exterior held normal.
The kernels are lam_ij(k) = lam_ij(0) varpi^2/(varpi^2+k^2), where
lam_ij(0) = 2 N_F |g_ij|^2/omega_E and varpi = omega_E/(2 pi T).
The model satisfies the multiband theorem's hypotheses: the band graph is
connected, and the couplings are symmetric and nonnegative with a common
antitone kernel.

 (A) s++ (TRS) solution; their Appendix-A phase rule evaluated at the s++ magnitudes and iterated to
     self-consistency (amplitudes from Eq.(33) + Re Eq.(34) only), with the TRSB margin and the Gram ratio
     c^2/(xy), c = f1.v.f2, x = f1.v.f1, y = f2.v.f2 (leading-order TRSB criterion of the rule is c^2 > xy).
 (B) the real stationary state with theta12 = pi reported in their Fig. 2(b) (g11 = 0.8g): torque and free
     energy relative to s++.
 (C) full complex Eliashberg iteration from a per-band TRSB start (phases 0, pi/2, pi/4 on s++ magnitudes):
     exact parameters (nearly decoupled phase mode: relaxation direction only) and an amplified variant
     (g12=0.01g, g13=g23=0.1g, g33=0.2g; same sign pattern of B^-1) where it converges.
"""
import sys
import numpy as np
from scipy.optimize import minimize as smin
from mb_core import Model
from t2_physics import eliashberg_ZD, spins_from_delta, bardeen_stephen

NF_MEV = 0.005; OMEGA_E = 20.0; T = 1.0; G = 85.0
VARPI = OMEGA_E / (2 * np.pi * T)
NF = 175  # pi T (2n+1) <= 1100 meV


def build(gmat):
    lam0 = 2 * NF_MEV * gmat ** 2 / OMEGA_E
    return Model([1.0, 1.0, 1.0], lam0, VARPI, NF, exterior=True), gmat ** 2


def blocks(m):
    nb, Nf = m.nb, m.Nf
    n = np.arange(Nf)
    Lp = np.zeros((nb, nb, Nf, Nf)); Lm = np.zeros_like(Lp)
    for a in range(nb):
        for b in range(nb):
            Lp[a, b] = m.lam[a, b][np.ix_(Nf + n, Nf + n)]
            Lm[a, b] = m.lam[a, b][np.ix_(Nf + n, Nf - n - 1)]
    return Lp, Lm


def toeplitz_inverse(Nf):
    j = np.arange(-Nf, Nf)
    v = VARPI ** 2 / (VARPI ** 2 + (j[:, None] - j[None, :]) ** 2)
    return np.linalg.inv(v)


_TG = np.linspace(0, 2 * np.pi, 241, endpoint=False)
_T12, _T13 = np.meshgrid(_TG, _TG, indexing="ij")


def phase_rule(a12, a13, a23):
    """Search the phase energy in Eq. (A1) on a grid, then refine with BFGS."""
    s = max(abs(a12), abs(a13), abs(a23))
    a12, a13, a23 = a12 / s, a13 / s, a23 / s
    f = lambda t: a12 * np.cos(t[0]) + a13 * np.cos(t[1]) + a23 * np.cos(t[1] - t[0])
    F = a12 * np.cos(_T12) + a13 * np.cos(_T13) + a23 * np.cos(_T13 - _T12)
    k = np.unravel_index(np.argmin(F), F.shape)
    r = smin(f, [_T12[k], _T13[k]], method="BFGS", options=dict(gtol=1e-14))
    t12, t13 = np.mod(r.x, 2 * np.pi)
    return t12, t13


def aase_scheme(m, Bmat, Pinv, Dinit, iters=4000, tol=1e-13):
    nb, Nf = m.nb, m.Nf
    om = 2 * np.arange(Nf) + 1.0
    Lp, Lm = blocks(m)
    tau = m.tau[:, Nf:]
    Binv = np.linalg.inv(Bmat)
    D = Dinit.copy()
    th = np.zeros(nb)
    for it in range(iters):
        E = np.sqrt(om ** 2 + D ** 2)
        Z = 1 + (tau + np.einsum('abnm,bm->an', Lp - Lm, om / E)) / om
        Phi = Z * D
        Phif = np.concatenate([Phi[:, ::-1], Phi], axis=1)  # even over the window j=-Nf..Nf-1
        q = Phif @ Pinv @ Phif.T
        a = Binv * q
        t12, t13 = phase_rule(a[0, 1], a[0, 2], a[1, 2])
        th = np.array([0.0, t12, t13])
        cosm = np.cos(th[None, :] - th[:, None])  # cos(theta_b - theta_a)
        Dn = np.einsum('ab,abnm,bm->an', cosm, Lp + Lm, D / E) / Z
        err = np.max(np.abs(Dn - D))
        D = 0.5 * D + 0.5 * Dn
        if err < tol:
            break
    E = np.sqrt(om ** 2 + D ** 2)
    Z = 1 + (tau + np.einsum('abnm,bm->an', Lp - Lm, om / E)) / om
    sinm = np.sin(th[None, :] - th[:, None])
    im_res = np.einsum('ab,abnm,bm->an', sinm, Lp + Lm, D / E)
    rel = np.max(np.abs(im_res) / np.maximum(Z * D, 1e-300), axis=1)
    return D, Z, th, a, err, rel


def spins_complex(m, D, th):
    nb, Nf = m.nb, m.Nf
    om = 2 * np.arange(Nf) + 1.0
    E = np.sqrt(om ** 2 + D ** 2)
    S = np.zeros((nb, 2 * Nf, 3))
    for a in range(nb):
        S[a, Nf:, 0] = D[a] / E[a] * np.cos(th[a]); S[a, Nf:, 1] = D[a] / E[a] * np.sin(th[a]); S[a, Nf:, 2] = om / E[a]
        S[a, :Nf, 0] = S[a, Nf:, 0][::-1]; S[a, :Nf, 1] = S[a, Nf:, 1][::-1]; S[a, :Nf, 2] = -S[a, Nf:, 2][::-1]
    return S.reshape(-1, 3)


def real_solve(m, D0, iters=400000, tol=1e-13):
    """real (signed) even multiband Eliashberg solution in the sign basin of D0."""
    Nf = m.Nf
    om = 2 * np.arange(Nf) + 1.0
    Lp, Lm = blocks(m)
    tau = m.tau[:, Nf:]
    D = D0.copy()
    for it in range(iters):
        E = np.sqrt(om ** 2 + D ** 2)
        Z = 1 + (tau + np.einsum('abnm,bm->an', Lp - Lm, om / E)) / om
        Dn = np.einsum('abnm,bm->an', Lp + Lm, D / E) / Z
        err = np.max(np.abs(Dn - D))
        D = 0.5 * D + 0.5 * Dn
        if err < tol:
            break
    return D, err


def wrap(x):
    return np.abs(np.angle(np.exp(1j * np.asarray(x))))


def is_trsb(phases, tol=1e-6):
    """Nonzero gap phases break TRS iff a relative phase is not 0 or pi."""
    phases = np.asarray(phases)
    return bool(np.any(np.abs(np.sin(phases - phases[0])) > tol))


def trsb_bounds(a13, a23):
    """Strict bounds for a12>0, a13<0, a23<0; endpoints are collinear."""
    A, C = abs(a13), abs(a23)
    lower = A * C / (A + C)
    upper = np.inf if A == C else A * C / abs(A - C)
    return lower, upper


def band_phases(S):
    tr = (S[:, 0] + 1j * S[:, 1]).reshape(3, 2 * NF)[:, NF]
    return np.angle(tr / tr[0])


def part_A(label, gmat, Pinv):
    m, Bmat = build(gmat)
    Dtrs, Ztrs, ZN, err = eliashberg_ZD(m, tol=1e-13)
    S_trs = spins_from_delta(m, Dtrs)
    E_trs = m.energy(S_trs)
    # Gram ratio with f = Delta/E over the full window and v the Einstein Toeplitz kernel
    om = 2 * np.arange(NF) + 1.0
    f = Dtrs / np.sqrt(om ** 2 + Dtrs ** 2)
    ff = np.concatenate([f[:, ::-1], f], axis=1)
    j = np.arange(-NF, NF)
    v = VARPI ** 2 / (VARPI ** 2 + (j[:, None] - j[None, :]) ** 2)
    Gm = ff @ v @ ff.T
    gram = Gm[0, 1] ** 2 / (Gm[0, 0] * Gm[1, 1])
    D, Z, th, a, err2, rel = aase_scheme(m, Bmat, Pinv, Dtrs)
    a12, a13, a23 = a[0, 1], a[0, 2], a[1, 2]
    thr, upper = trsb_bounds(a13, a23)
    trsb = is_trsb(th)
    print(f"[A {label}] lam(0) diag={np.round(np.diag(m.lam0),6)} lam12={m.lam0[0,1]:.3e} lam13={m.lam0[0,2]:.3e}; "
          f"sign(B^-1)_12,13,23 = {np.sign(np.linalg.inv(Bmat)[0,1]):+.0f},{np.sign(np.linalg.inv(Bmat)[0,2]):+.0f},"
          f"{np.sign(np.linalg.inv(Bmat)[1,2]):+.0f}")
    print(f"   s++ solution: Delta_a(n=0)/(pi T)={np.array2string(Dtrs[:,0],precision=6)} err={err:.1e} E_TRS={E_trs:.12f}")
    print(f"   phase rule (a12>0, a13,a23<0): TRSB iff {thr:.4e} < a12 < {upper:.4e}; "
          f"a12={a12:.4e} a13={a13:.4e} a23={a23:.4e} "
          f"(margin a12/lower = {a12/thr:.6f}); Gram c^2/(xy) = {gram:.8f}")
    print(f"   self-consistent scheme output: theta/pi = {np.round(th/np.pi,8)} TRSB={trsb} conv={err2:.1e}; "
          f"max_n |Im Eq34|/|Re Eq34| per band = {np.array2string(rel,precision=2)}")
    return m, Dtrs, S_trs, E_trs, trsb, a12 / thr, gram


def part_B(m, Dtrs, E_trs):
    D0 = Dtrs.copy(); D0[1] *= -1  # band 2 opposite to band 1 (their Fig. 2(b): theta12 = pi)
    D, err = real_solve(m, D0)
    S = spins_from_delta(m, D)
    tq = m.torque(S)
    dE = m.energy(S) - E_trs
    # At this sign-changing stationary point, the Bardeen-Stephen value is twice the spin energy.
    om = 2 * np.arange(m.Nf) + 1.0
    Lp, Lm = blocks(m)
    E = np.sqrt(om ** 2 + D ** 2)
    Z = 1 + (m.tau[:, m.Nf:] + np.einsum('abnm,bm->an', Lp - Lm, om / E)) / om
    ZN = 1 + (m.tau[:, m.Nf:] + np.einsum('abnm,bm->an', Lp - Lm, np.ones_like(om)[None, :].repeat(m.nb, 0))) / om
    bs_ratio = bardeen_stephen(m, D, Z, ZN) / m.energy(S)
    print(f"[B] theta12=pi real stationary state: sign(Delta_a(0)) = {np.sign(D[:,0])}, "
          f"|Delta_a(0)|/(pi T) = {np.array2string(np.abs(D[:,0]),precision=6)}, err={err:.1e}, torque={tq:.1e}, "
          f"E - E_s++ = {dE:.4e} (>0: excited stationary state), Bardeen-Stephen/E = {bs_ratio:.10f}")
    return tq, dE, bs_ratio


def part_C(label, m, Dtrs, S_trs, E_trs, iters):
    th0 = np.array([0.0, 0.5 * np.pi, 0.25 * np.pi])
    S0 = spins_complex(m, Dtrs, th0)
    E0 = m.energy(S0)
    S, err, it = m.fixed_point(S0, iters=iters, tol=1e-13, damp=0.5)
    ph = band_phases(S)
    E1 = m.energy(S)
    amp = np.max(np.abs(np.hypot(S[:, 0], S[:, 1]) - S_trs[:, 0]))
    print(f"[C {label}] TRSB start phases/pi={th0/np.pi}: E_start - E_TRS = {E0-E_trs:.4e}; after {it+1} "
          f"complex Eliashberg iterations: phases/pi={np.round(ph/np.pi,8)}, E - E_TRS = {E1-E_trs:.3e}, "
          f"max||S_perp|-|S_perp^TRS|| = {amp:.2e}, step={err:.1e}")
    return E0 - E_trs, E1 - E_trs, ph, err


def main():
    print(f"Boundary condition: frozen normal exterior; M={NF} positive frequencies per band.")
    Pinv = toeplitz_inverse(NF)
    ok = True
    exact = lambda g11: G * np.array([[g11, 1e-4, 0.003], [1e-4, 1.4, 0.003], [0.003, 0.003, 0.005]])
    amplified = lambda g11: G * np.array([[g11, 0.01, 0.1], [0.01, 1.4, 0.1], [0.1, 0.1, 0.2]])
    for g11 in [0.8, 0.9, 1.0, 1.1]:
        m, Dtrs, S_trs, E_trs, trsb, margin, gram = part_A(f"exact g11={g11}g", exact(g11), Pinv)
        ok &= (not trsb) and margin < 1 and gram <= 1 + 1e-12
        if g11 == 0.8:
            tq, dE, bsr = part_B(m, Dtrs, E_trs)
            ok &= tq < 1e-8 and dE > 0 and abs(bsr - 2) < 1e-6
        if g11 == 1.0:
            dE0, dE1, ph, err = part_C("exact g11=g", m, Dtrs, S_trs, E_trs, iters=4000)
            # band 3 re-aligns to its local field first; the slow mode is the 1-2 relative phase
            ok &= dE0 > 0 and 0 <= dE1 < dE0 and wrap(ph[1]) < 0.5 * np.pi
    for g11 in [1.0]:
        m, Dtrs, S_trs, E_trs, trsb, margin, gram = part_A(f"amplified g11={g11}g", amplified(g11), Pinv)
        ok &= (not trsb) and margin < 1 and gram <= 1 + 1e-12
        tq, dE, bsr = part_B(m, Dtrs, E_trs)
        ok &= tq < 1e-8 and dE > 0 and abs(bsr - 2) < 1e-6
        dE0, dE1, ph, err = part_C("amplified g11=g", m, Dtrs, S_trs, E_trs, iters=60000)
        ok &= dE0 > 0 and abs(dE1) < 1e-9 and np.all(wrap(ph) < 1e-6)
    print("ALL OK" if ok else "SOME CHECK FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
