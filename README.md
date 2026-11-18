# Supplement to Global uniqueness of the superconducting state in multiband and anisotropic Eliashberg models without Coulomb repulsion

The companion article by Davis Rens (SuperMatics Inc.) proves that the attractive multiband Eliashberg spin functional has a unique thermodynamic minimizing state up to a common phase. It treats equal pairing and mass-renormalization kernels at zero Coulomb pseudopotential. The multiband theorem applies to mirror-symmetric finite frequency windows under density-weighted reciprocity, the stated positive-lag kernel hypotheses, and band connectivity. On the infinite chain it also requires positive-lag summability and the article's admissible weighted configuration space.

A second theorem treats an anisotropic Fermi surface on a standard non-atomic probability space. It assumes uniformly summable integrated rows, compact angular operators, and measurable irreducibility. In this setting the article also proves weighted convergence of minimizing density sequences.

In both theorems, the even stability form distinguishes the unique normal minimizer from a single superconducting phase orbit. The strict convexity argument uses squared transverse components after alignment and folding. The conclusions concern thermodynamic minimizers, not arbitrary stationary states, solver convergence, or single crossing in temperature.

This repository, [SuperMatics-Inc/eliashberg-uniqueness](https://github.com/SuperMatics-Inc/eliashberg-uniqueness), contains the calculations and Lean proofs that accompany the article. Version 1.0.0 is available under Apache-2.0 at [10.5281/zenodo.24326101](https://doi.org/10.5281/zenodo.24326101).

## Three-band example

The comparison is between two real stationary states: one with a common phase and one with both relative phases equal to π. Outward interval bounds put the energy of the common-phase root strictly below that of the other root, both for a hard cutoff and for a frozen exterior. The written finite-window theorem identifies the common-phase root as the global minimizer. A separate interval implementation checks root inclusion and encloses the energy independently.

Except for the Arb enclosures identified in `t8`, the nine diagnostics are floating-point checks rather than proofs. The solvers start from uncertified floating-point approximations.

## Reproducing the calculations

Use Python 3.13.18 and the package versions in `requirements.txt`. From a fresh checkout:

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python scripts/replay.py --out reproduced
```

The driver compares the source files with the SHA-256 digests in `certificates/source-sha256.json`. It then runs the nine diagnostics and the independent interval calculation in order. A digest mismatch or a failed calculation gives a nonzero exit status.

The output directory contains the logs, their SHA-256 digests, the dependency versions, and the exit status of each calculation. The diagnostics import `mb_core.py` as a library. The independent calculation also checks that invalid inputs are rejected. The enclosures in `certificates/branch-enclosures.json` are supplied for comparison; the scripts compute them afresh.

## Lean proofs

The Lean files prove the following parts of the argument. Both Lean and Mathlib use version v4.35.0; see [lean/README.md](lean/README.md) for build instructions.

| Module | Lean result |
|---|---|
| `KayThermo/Convex.lean` | Continuity, attainment, strict convexity and uniqueness for the finite density functional under the stated hypotheses. |
| `Multiband/Coefficients.lean`, `Density.lean` | Finite coefficient identities, the substitution of squared transverse components and the normal-state decomposition. |
| `Multiband/Phase.lean` | Alignment identities and phase and folding rigidity under explicit equality hypotheses. |
| `Multiband/Window.lean` | Classification given a full-spin reduction; exact rational ordering given membership in the energy intervals. |
| `Multiband/InfiniteCore.lean` | Nine finite inequalities and equality propagation on a connected graph. |
| `FSCore.lean` | Six pointwise algebraic identities and inequalities. |

The article gives the full-spin reduction and constructs the physical minimizing orbit. It also supplies the analysis of infinite sums and limits, including existence and compactness, and the angular analysis, including integration, measurable irreducibility and continuum attainment. Interval root validation belongs to the calculations above. Neither main theorem nor the interval certificate is formalized in full.

[GitHub Actions](https://github.com/SuperMatics-Inc/eliashberg-uniqueness/actions) builds Lean with `leanprover/lean-action@v1` and checks for admitted proofs, new axiom declarations and uses of `native_decide`. The calculations run in a separate job and do not require Lean. Both jobs run on pushes and pull requests and can be started manually.

## Contents and related work

- `scripts/`: numerical diagnostics, two interval implementations and the driver.
- `data/model.json`: exact parameters for the three-band example.
- `certificates/`: reference interval enclosures and source digests.
- `lean/`: Lean proofs and dependency versions.

The companion article, [Zenodo preprint 10.5281/zenodo.24326099](https://doi.org/10.5281/zenodo.24326099), contains the proofs and the dated prior-art comparison. The separate sharp-bounds paper is [arXiv:2611.20496](https://arxiv.org/abs/2611.20496), with supplement [10.5281/zenodo.24270482](https://doi.org/10.5281/zenodo.24270482). No manuscript source or PDF is included here.

## AI use

Under the author's direction and review, AI agents generated proofs, certificates, code and Lean files. They also drafted and edited the manuscript. Davis Rens is the sole author; no language model is an author.
