"""Multiband Eliashberg spin-chain core (mu*=0, T>0), finite Matsubara window.

Conventions (dimensionless, energies in units of 2*pi^2*T*N_ref as in Siraj's E):
  bands a=0..nb-1, DOS weights N_a>0, couplings lam[a,b](k) for integer k>=0,
  detailed balance N_a lam_ab(k) = N_b lam_ba(k)  (checked).
  Window W = {-Nf..Nf-1}; spins outside W frozen at the normal state N_j = sgn(w_j) e_z,
  which is exactly absorbed into an extra Zeeman weight tau_{a,j} >= 0 (antitone kernels).

Full-chain normal-subtracted energy (finite window, exterior frozen):
  E(S) = sum_{a,j} N_a (|2j+1| + tau_aj) |S_aj - N_j|^2 / 2
       + 1/2 sum_{(a,i)!=(b,j)} N_a lam_ab(|i-j|) (eps_ij - S_ai . S_bj)
  with eps_ij - S.S' = |S-S'|^2/2 (same side) or -|S+S'|^2/2 (opposite side).
Stationary points with S parallel to B are the multiband Eliashberg solutions:
  B_ai = (2i+1 + sgn_i tau_ai) e_z + sum_{b,j} lam_ab(|i-j|) S_bj.
"""
import numpy as np
from scipy.special import psi


def einstein_kernel(lam0, varpi, kmax):
    k = np.arange(kmax + 1, dtype=float)
    return lam0 * varpi**2 / (varpi**2 + k**2)


def einstein_tail(lam0, varpi, k0):
    """sum_{k>=k0} lam0 varpi^2/(varpi^2+k^2) = lam0*varpi*Im psi(k0+i varpi)."""
    return lam0 * varpi * np.imag(psi(k0 + 1j * varpi))


class Model:
    def __init__(self, N, lam0, varpi, Nf, exterior=True):
        """N: (nb,) DOS weights; lam0: (nb,nb) lam_ab(0) (row a = gap band, col b = source band);
        varpi: (nb,nb) Einstein Omega_ab/(2 pi T). Kernel lam_ab(k) = lam0_ab varpi_ab^2/(varpi_ab^2+k^2)."""
        self.N = np.asarray(N, float)
        self.lam0 = np.asarray(lam0, float)
        self.varpi = np.asarray(varpi, float) * np.ones_like(self.lam0)
        nb = len(self.N)
        self.nb, self.Nf = nb, Nf
        Wsym = self.N[:, None] * self.lam0
        assert np.allclose(Wsym, Wsym.T, rtol=1e-12, atol=0), "detailed balance violated"
        assert np.allclose(self.varpi, self.varpi.T)
        j = np.arange(-Nf, Nf)
        self.j = j
        self.sgn = np.where(j >= 0, 1.0, -1.0)
        M = 2 * Nf
        dk = np.abs(j[:, None] - j[None, :])
        # lam[a,b,i,j]
        self.lam = np.empty((nb, nb, M, M))
        for a in range(nb):
            for b in range(nb):
                ker = einstein_kernel(self.lam0[a, b], self.varpi[a, b], 2 * M + 2)
                self.lam[a, b] = ker[dk]
        self.eps = self.sgn[:, None] * self.sgn[None, :]
        # exterior Zeeman correction tau_{a,i} = sum_b sum_{l notin W} lam_ab(|i-l|) sgn_i sgn_l
        self.tau = np.zeros((nb, M))
        if exterior:
            for a in range(nb):
                for b in range(nb):
                    for ii, i in enumerate(j):
                        # l >= Nf : distance l-i >= Nf-i ; l <= -Nf-1 : distance i-l >= i+Nf+1
                        up = einstein_tail(self.lam0[a, b], self.varpi[a, b], Nf - i)
                        dn = einstein_tail(self.lam0[a, b], self.varpi[a, b], i + Nf + 1)
                        self.tau[a, ii] += self.sgn[ii] * (up - dn)
        self.zee = self.N[:, None] * (np.abs(2 * j + 1)[None, :] + self.tau)
        # symmetric coupling J[(a,i),(b,j)] = N_a lam_ab(|i-j|), zero diagonal (self pair irrelevant)
        J = self.N[:, None, None, None] * self.lam
        J = J.transpose(0, 2, 1, 3).reshape(nb * M, nb * M).copy()
        np.fill_diagonal(J, 0.0)
        self.J = J
        self.E2 = np.tile(self.eps, (nb, nb))  # eps for flattened vertices
        self.Nvec = np.zeros((nb * M, 3))
        self.Nvec[:, 2] = np.tile(self.sgn, nb)
        self.zeef = self.zee.reshape(-1)
        self.Nrep = np.repeat(self.N, M)

    # ---------- energy ----------
    def energy(self, S):
        """S: (nb*M,3) unit vectors. Stable normal-subtracted energy."""
        d = S - self.Nvec
        e = 0.5 * np.sum(self.zeef * np.sum(d * d, 1))
        # same side: 1 - S.S' = |S-S'|^2/2 ; opposite side: -(1 + S.S') = -|S+S'|^2/2
        # computed from explicit differences to avoid cancellation for tiny gaps
        Dm = np.zeros((S.shape[0], S.shape[0]))
        Dp = np.zeros_like(Dm)
        for k in range(3):
            Dm += (S[:, None, k] - S[None, :, k]) ** 2
            Dp += (S[:, None, k] + S[None, :, k]) ** 2
        pair = np.where(self.E2 > 0, 0.5 * Dm, -0.5 * Dp)
        e += 0.5 * np.sum(self.J * pair)
        return e

    def grad_S(self, S):
        """dE/dS for independent (unnormalised) vector entries."""
        return self.zeef[:, None] * (S - self.Nvec) - self.J @ S

    def field(self, S):
        """Eliashberg field B_ai (per unit N_a), incl. self term lam_aa(0) S_ai."""
        f = (self.zeef / self.Nrep)[:, None] * self.Nvec + (self.J @ S) / self.Nrep[:, None]
        self_term = np.repeat(np.diag(self.lam0), 2 * self.Nf)[:, None] * S
        return f + self_term

    # ---------- unconstrained parametrisation S = u/|u| ----------
    def f_and_g(self, u):
        U = u.reshape(-1, 3)
        r = np.linalg.norm(U, axis=1)
        S = U / r[:, None]
        e = self.energy(S)
        gS = self.grad_S(S)
        gU = (gS - np.sum(gS * S, 1)[:, None] * S) / r[:, None]
        return e, gU.reshape(-1)

    def fixed_point(self, S0, iters=20000, tol=1e-14, damp=0.5):
        S = S0.copy()
        for it in range(iters):
            B = self.field(S)
            Sn = B / np.linalg.norm(B, axis=1)[:, None]
            Sn = (1 - damp) * S + damp * Sn
            Sn /= np.linalg.norm(Sn, axis=1)[:, None]
            err = np.max(np.abs(Sn - S))
            S = Sn
            if err < tol:
                break
        return S, err, it

    def torque(self, S):
        B = self.field(S)
        return np.max(np.linalg.norm(np.cross(S, B), axis=1))

    def normal(self):
        return self.Nvec.copy()


def minimize(model, S0, maxiter=20000, gtol=1e-11):
    from scipy.optimize import minimize as smin
    res = smin(model.f_and_g, S0.reshape(-1), jac=True, method="L-BFGS-B",
               options=dict(maxiter=maxiter, maxfun=4 * maxiter, gtol=gtol, ftol=1e-16, maxcor=30))
    U = res.x.reshape(-1, 3)
    S = U / np.linalg.norm(U, axis=1)[:, None]
    return S, res


def phase_align(S, ref_idx=None):
    """Rotate about z so that the transverse part of the largest-gap spin points along +x."""
    tr = S[:, 0] + 1j * S[:, 1]
    k = np.argmax(np.abs(tr)) if ref_idx is None else ref_idx
    ph = np.angle(tr[k]) if abs(tr[k]) > 0 else 0.0
    tr2 = tr * np.exp(-1j * ph)
    return np.column_stack([tr2.real, tr2.imag, S[:, 2]])


def random_spins(n, rng, mode="any"):
    v = rng.normal(size=(n, 3))
    return v / np.linalg.norm(v, axis=1)[:, None]
