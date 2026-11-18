# Supplement to Global uniqueness of the superconducting state in multiband and anisotropic Eliashberg models without Coulomb repulsion

Proof-support software for the companion article by Davis Rens, SuperMatics Inc. Repository: [SuperMatics-Inc/eliashberg-uniqueness](https://github.com/SuperMatics-Inc/eliashberg-uniqueness). Version 1.0.0, Apache-2.0. Supplement DOI: [10.5281/zenodo.24326101](https://doi.org/10.5281/zenodo.24326101).

## Mathematical scope

**PROVED (written proofs, not end-to-end Lean formalization).** For the attractive Eliashberg spin functional at zero Coulomb pseudopotential and identical pairing and mass-renormalization kernels, the multiband theorem gives a unique thermodynamic minimizing state modulo one common phase. Its hypotheses include density-weighted reciprocity, the stated attractive positive-lag kernels and band connectivity. It covers mirror-symmetric finite frequency windows. The infinite-chain conclusion additionally requires positive-lag summability and the paper's admissible weighted configuration space. A separate non-atomic Fermi-surface theorem assumes a standard non-atomic probability space, uniformly summable integrated rows, compact angular operators and measurable irreducibility. It also gives weighted convergence of minimizing density sequences. These are separate theorems, not a theorem for arbitrary measures. Consult the article for the full hypotheses and exact statements.

In both settings the even stability form distinguishes the unique normal minimizer from one superconducting phase orbit. Strict convexity applies after alignment, folding and the substitution of squared transverse components. This does not prove uniqueness of every stationary solution, convergence of a numerical solver, single crossing in temperature, or an extension to repulsive pairing or positive Coulomb pseudopotential.

**CERTIFIED (interval arithmetic).** The three-band example has real stationary solutions in two sign patterns. Outward energy enclosures strictly order the common-phase and band-2-reversed roots for both hard-cutoff and frozen-exterior boundary conventions. The common-phase root is the global minimizer by the written finite-window theorem. An independent interval implementation checks root inclusion and energy containment. The interval calculations do not replace the theorem's hypotheses.

**NUMERICAL.** The floating-point diagnostics in scripts t1 through t9 are not proofs, except for the explicitly identified Arb interval calculations in t8. Floating-point solver initialization is not itself certified.

## Reproduce

The reference environment uses Python 3.13.18; package versions are pinned in `requirements.txt`. From a fresh checkout using that Python:

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python scripts/replay.py --out reproduced
```

The driver first checks every SHA-256 source pin in `certificates/source-sha256.json`, then runs all nine diagnostics and the independent interval implementation sequentially. It fails if a source pin or any child fails. Logs, dependency versions, child exit codes and log hashes are written beneath the requested output directory. `mb_core.py` is an imported library exercised by the diagnostics, not a standalone command. The independent implementation includes deliberate invalid-input checks. `certificates/branch-enclosures.json` supplies reference interval results; a reproduction recomputes them.

## Lean scope

Lean and Mathlib are pinned to v4.35.0. See [lean/README.md](lean/README.md) for dependency setup and detailed limitations.

| Module | Kernel-checked mathematical content | Not established by that module |
|---|---|---|
| `KayThermo/Convex.lean` | Finite density convexity, continuity, attainment and uniqueness | Physical full-spin reduction |
| `Multiband/Coefficients.lean`, `Density.lean` | Finite coefficient identities, hidden substitution, normal-state decomposition | Analytic infinite sums and angular integrals |
| `Multiband/Phase.lean` | Alignment algebra and conditional phase/folding rigidity | Assembly of the full physical minimizing orbit |
| `Multiband/Window.lean` | Classification conditional on the explicit reduction interface; exact rational interval ordering conditional on enclosure membership | Construction of that interface, interval root validation or temperature single crossing |
| `Multiband/InfiniteCore.lean` | Nine finite inequalities and abstract connected-graph propagation statements | Infinite-dimensional existence, limits or compactness |
| `FSCore.lean` | Six pointwise algebraic identities and inequalities | Measurable irreducibility, compact angular operators, integration or continuum attainment |

No end-to-end formalization of either main theorem or the numerical certificate is claimed. No Lean build is required to run the numerical reproduction.

GitHub CI builds the Lean sources against the pinned Mathlib cache using `leanprover/lean-action@v1`, then rejects proof escapes in project sources. CI runs on push and pull requests and can also be started manually; its run links appear in the repository's Actions tab. The certificate replay is a separate required job. Neither job changes the mathematical scope stated above.

## Contents and related work

- `scripts/`: numerical diagnostics, two interval implementations and the reproduction driver.
- `data/model.json`: exact three-band parameter specification.
- `certificates/`: reference interval enclosures and source pins.
- `lean/`: scoped algebraic proofs and pinned Lean dependencies.

The companion article, [Zenodo preprint 10.5281/zenodo.24326099](https://doi.org/10.5281/zenodo.24326099), contains the proofs and the dated prior-art comparison. The separate sharp-bounds paper is [arXiv:2611.20496](https://arxiv.org/abs/2611.20496), with supplement [10.5281/zenodo.24270482](https://doi.org/10.5281/zenodo.24270482). No manuscript source or PDF is included here.
