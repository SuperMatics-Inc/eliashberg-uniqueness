"""Compare finite-window and infinite-symbol inverses for the model of Aase
et al. (arXiv:2309.15894).

Their Eq. (31) applies the exact inverse of the infinite Matsubara kernel,
p = 1/v(tau) in Eqs. (27)–(28), to gaps truncated at |omega_n| <= M.
Inverting on the finite window instead gives
a_ij = (B^-1)_ij (B G B)_ij with G_kl = f_k . v . f_l (f = Delta/E), for which the leading-order TRSB
criterion is c^2 > xy, excluded by Cauchy-Schwarz (t4). Here we evaluate their phase rule with the
infinite-symbol inverse p_k = (1/2pi) int e^{-ik tau} / vhat(tau), vhat(tau) = pi varpi cosh(varpi(pi-|tau|))/sinh(pi varpi),
on the same s++ solution and in the self-consistent scheme, scanning g11/g over their Fig. 3 range.
The diagnostics use a frozen normal exterior, not the hard-cutoff functional.
"""
import sys
import numpy as np
from scipy.integrate import quad
from t4_aase_trsb import (G, NF, VARPI, build, toeplitz_inverse, aase_scheme, phase_rule, is_trsb, spins_complex)
from t2_physics import eliashberg_ZD, spins_from_delta


def symbol_inverse(Nf):
    K = 2 * Nf
    s = np.sinh(np.pi * VARPI) / (np.pi * VARPI)
    f = lambda t: s / np.cosh(VARPI * (np.pi - t))
    p = np.array([quad(f, 0, np.pi, weight="cos", wvar=k, limit=400)[0] / np.pi for k in range(K)])
    j = np.arange(-Nf, Nf)
    return p[np.abs(j[:, None] - j[None, :])], p


def a_of(m, Bmat, P, D):
    om = 2 * np.arange(NF) + 1.0
    E = np.sqrt(om ** 2 + D ** 2)
    tau = m.tau[:, NF:]
    # Z from Eq.(33)
    from t4_aase_trsb import blocks
    Lp, Lm = blocks(m)
    Z = 1 + (tau + np.einsum('abnm,bm->an', Lp - Lm, om / E)) / om
    Phi = Z * D
    Phif = np.concatenate([Phi[:, ::-1], Phi], axis=1)
    return np.linalg.inv(Bmat) * (Phif @ P @ Phif.T)


def main():
    print(f"Boundary condition: frozen normal exterior; M={NF} positive frequencies per band.")
    Ptr = toeplitz_inverse(NF)
    Psym, p = symbol_inverse(NF)
    # Check the product with the kernel at the centre and at the edge.
    j = np.arange(-NF, NF)
    v = VARPI ** 2 / (VARPI ** 2 + (j[:, None] - j[None, :]) ** 2)
    I = Psym @ v
    print(f"p_0={p[0]:.6e} p_1={p[1]:.6e} p_10={p[10]:.3e}; |Psym v - 1| centre={abs(I[NF,NF]-1):.2e}, "
          f"edge={abs(I[0,0]-1):.2e}; cond(v)={np.linalg.cond(v):.2e}")
    print(" g11/g | rule on s++ (truncated inverse)   | rule on s++ (symbol inverse, theirs) | self-consistent scheme (symbol inverse)")
    any_trsb_sym = False
    for g11 in [0.8, 0.85, 0.9, 0.95, 1.0, 1.05, 1.1]:
        gm = G * np.array([[g11, 1e-4, 0.003], [1e-4, 1.4, 0.003], [0.003, 0.003, 0.005]])
        m, Bmat = build(gm)
        D, Z, ZN, err = eliashberg_ZD(m, tol=1e-13)
        E_trs = m.energy(spins_from_delta(m, D))
        out = []
        for P in (Ptr, Psym):
            a = a_of(m, Bmat, P, D)
            th = phase_rule(a[0, 1], a[0, 2], a[1, 2])
            out.append((a[0, 1], a[0, 2], a[1, 2], th))
        Ds, Zs, ths, a_s, errs, rel = aase_scheme(m, Bmat, Psym, D)
        S_sc = spins_complex(m, Ds, ths)
        dE = m.energy(S_sc) - E_trs
        trsb = is_trsb(ths)
        any_trsb_sym |= trsb
        fmt = lambda o: f"a=({o[0]:+.2e},{o[1]:+.2e},{o[2]:+.2e}) th/pi=({o[3][0]/np.pi:.4f},{o[3][1]/np.pi:.4f})"
        print(f" {g11:4.2f} | {fmt(out[0])} | {fmt(out[1])} | th/pi=({ths[1]/np.pi:.4f},{ths[2]/np.pi:.4f}) "
              f"TRSB={trsb} |Im34|/|Re34|max={rel.max():.1e} E-E_s++={dE:.3e}")
    print("symbol-inverse scheme produced TRSB:", any_trsb_sym)
    sys.exit(0)


if __name__ == "__main__":
    main()
