"""T3: necessity of the hypotheses (NUMERICAL counterexamples / gauge checks).
 (i)  disconnected bands (lam_12 = 0): minimisers form a U(1)xU(1) family (relative phase free).
 (ii) two-channel model, 2 bands, repulsive interband PAIRING (lam^D_12 < 0, lam^Z_12 >= 0):
      unique modulo U(1) with relative sign pi (s+-): the signed graph is balanced (gauge flip).
 (iii) two-channel model, 3 bands, all interband pairing repulsive (frustrated triangle):
      global minimum is TRSB (non-collinear phases), so it is NOT unique modulo U(1):
      its complex conjugate is a second minimiser off the U(1) orbit.
Two-channel energy (Z channel lam^Z >= 0 antitone, pairing channel lam^D signed):
  E = sum zee |S-N|^2/2 + 1/2 sum_{u!=v} [J^Z_uv (eps_uv - S^z_u S^z_v) - J^D_uv S^perp_u.S^perp_v]
      + 1/2 sum_u (J^Z_uu - J^D_uu) |S^perp_u|^2
whose stationary points are the two-channel Eliashberg equations
  B^z = (2j+1) + sum lam^Z S^z (incl. self), B^perp = sum lam^D S^perp (incl. self).
"""
import sys
import numpy as np
from scipy.optimize import minimize as smin
from mb_core import Model

rng = np.random.default_rng(11)


class TwoChannel:
    def __init__(self, N, lamZ, lamD, varpi, Nf):
        self.mZ = Model(N, lamZ, varpi, Nf)
        self.mD = Model(N, lamD, varpi, Nf, exterior=False)
        self.zeef, self.Nvec, self.E2 = self.mZ.zeef, self.mZ.Nvec, self.mZ.E2
        self.JZ, self.JD = self.mZ.J, self.mD.J
        M = 2 * Nf
        self.selfdiff = np.repeat(np.asarray(N) * (np.diag(lamZ) - np.diag(lamD)), M)

    def energy(self, S):
        d = S - self.Nvec
        e = 0.5 * np.sum(self.zeef * np.sum(d * d, 1))
        p2 = S[:, 0] ** 2 + S[:, 1] ** 2
        z = S[:, 2]
        same = 0.5 * (p2[:, None] + p2[None, :]) + 0.5 * (z[:, None] - z[None, :]) ** 2
        opp = -(0.5 * (p2[:, None] + p2[None, :]) + 0.5 * (z[:, None] + z[None, :]) ** 2)
        e += 0.5 * np.sum(self.JZ * np.where(self.E2 > 0, same, opp))
        e -= 0.5 * np.sum(self.JD * (S[:, :2] @ S[:, :2].T))
        e += 0.5 * np.sum(self.selfdiff * p2)
        return e

    def grad_S(self, S):
        g = self.zeef[:, None] * (S - self.Nvec)
        g[:, 2] -= self.JZ @ S[:, 2]
        g[:, :2] -= self.JD @ S[:, :2]
        g[:, :2] += self.selfdiff[:, None] * S[:, :2]
        return g

    def f_and_g(self, u, planar=False):
        U = u.reshape(-1, 3).copy()
        if planar:
            U[:, 1] = 0.0
        r = np.linalg.norm(U, axis=1)
        S = U / r[:, None]
        gS = self.grad_S(S)
        gU = (gS - np.sum(gS * S, 1)[:, None] * S) / r[:, None]
        if planar:
            gU[:, 1] = 0.0
        return self.energy(S), gU.reshape(-1)


def tc_min(model, S0, planar=False):
    res = smin(lambda u: model.f_and_g(u, planar), S0.reshape(-1), jac=True, method="L-BFGS-B",
               options=dict(maxiter=30000, maxfun=120000, gtol=1e-11, ftol=1e-16, maxcor=30))
    U = res.x.reshape(-1, 3).copy()
    if planar:
        U[:, 1] = 0
    return U / np.linalg.norm(U, axis=1)[:, None]


def band_phases(S, nb, Nf):
    """phase of the transverse spin at the lowest positive frequency of each band, relative to band 0."""
    tr = (S[:, 0] + 1j * S[:, 1]).reshape(nb, 2 * Nf)[:, Nf]
    ph = np.angle(tr / tr[0])
    return ph, np.abs(tr)


def main():
    ok = True
    Nf = 20
    # (i) disconnected
    N = [1.0, 1.0]
    m = TwoChannel(N, np.diag([1.0, 0.8]), np.diag([1.0, 0.8]), 3.0, Nf)
    S = tc_min(m, rng.normal(size=(2 * 2 * Nf, 3)))
    E0 = m.energy(S)
    Es = []
    for alpha in np.linspace(0, 2 * np.pi, 7):
        S2 = S.copy().reshape(2, 2 * Nf, 3)
        c, s = np.cos(alpha), np.sin(alpha)
        x, y = S2[1, :, 0].copy(), S2[1, :, 1].copy()
        S2[1, :, 0], S2[1, :, 1] = c * x - s * y, s * x + c * y
        Es.append(m.energy(S2.reshape(-1, 3)))
    print(f"(i) lam_12=0: E_min={E0:.10f}; energy under relative band-2 rotation spans {np.ptp(Es):.2e} "
          f"(=> minimiser set is U(1)xU(1), not one U(1) orbit)")
    ok &= np.ptp(Es) < 1e-12 and E0 < -1e-6

    # (ii) 2 bands, repulsive interband pairing: balanced -> s+- unique mod U(1)
    lamZ = np.array([[1.0, 0.3], [0.3, 0.8]]); lamD = np.array([[1.0, -0.3], [-0.3, 0.8]])
    m = TwoChannel(N, lamZ, lamD, 3.0, Nf)
    phs, Es = [], []
    for s in range(10):
        S = tc_min(m, rng.normal(size=(2 * 2 * Nf, 3)))
        Es.append(m.energy(S)); phs.append(band_phases(S, 2, Nf)[0][1])
    print(f"(ii) 2-band s+-: E_min spread {np.ptp(Es):.2e}, relative phases {np.round(np.abs(phs)/np.pi,6)} pi")
    ok &= np.ptp(Es) < 1e-9 and np.allclose(np.abs(phs), np.pi, atol=1e-5)

    # (iii) 3 bands, frustrated: all interband pairing repulsive
    N3 = [1.0, 1.0, 1.0]
    lamZ = np.full((3, 3), 0.15); np.fill_diagonal(lamZ, 1.0)
    lamD = np.full((3, 3), -0.15); np.fill_diagonal(lamD, 1.0)
    m = TwoChannel(N3, lamZ, lamD, 3.0, Nf)
    best3, bestS = 1e9, None
    for s in range(12):
        S = tc_min(m, rng.normal(size=(3 * 2 * Nf, 3)))
        e = m.energy(S)
        if e < best3:
            best3, bestS = e, S
    ph, amp = band_phases(bestS, 3, Nf)
    best_pl = 1e9
    for s in range(12):
        S = tc_min(m, rng.normal(size=(3 * 2 * Nf, 3)), planar=True)
        best_pl = min(best_pl, m.energy(S))
    conj = bestS.copy(); conj[:, 1] *= -1
    # distance of the conjugate from the U(1) orbit of bestS
    tr, trc = bestS[:, 0] + 1j * bestS[:, 1], conj[:, 0] + 1j * conj[:, 1]
    al = np.angle(np.vdot(trc, tr))  # best rotation of conj onto bestS
    dist = np.max(np.abs(trc * np.exp(1j * al) - tr))
    print(f"(iii) 3-band frustrated: E_min(3D)={best3:.10f}, best collinear (planar) E={best_pl:.10f}, "
          f"gap={best_pl-best3:.3e}; band phases/pi={np.round(ph/np.pi,5)}, amps={np.round(amp,5)}; "
          f"E(conj)-E={m.energy(conj)-best3:.1e}, dist(conj, U(1) orbit)={dist:.3f}")
    ok &= (best_pl - best3 > 1e-6) and dist > 1e-2
    print("ALL OK" if ok else "SOME CHECK FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
