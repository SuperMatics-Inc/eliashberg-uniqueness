# Lean proofs for Eliashberg uniqueness

These files accompany “Global uniqueness of the superconducting state in multiband and anisotropic Eliashberg models without Coulomb repulsion”.

The build uses Lean 4.35.0 and Mathlib v4.35.0, with `autoImplicit = false`. The Mathlib revision is `56a005855ea17e0b0958f73ec801ae140b0a1679`.

With elan installed, run these commands from this directory:

```sh
lake exe cache get
lake build
```

The first command downloads the precompiled Mathlib library. `Multiband.lean` and `FSCore.lean` print the axioms on which their theorems depend. They use the ordinary foundational axioms, with no new axioms or admitted proofs.

## Mathematical content

- `KayThermo/Convex.lean` proves continuity and attainment on the closed density cube for general finite coefficient arrays. Under the stated sign and weight hypotheses it proves strict convexity and uniqueness. It also gives the convex stationary-point criterion.
- `Multiband/Coefficients.lean` checks reciprocity and symmetry, with an exception at zero lag in the off-diagonal positivity statement. It proves positivity and monotonicity of the Einstein kernel and positivity of the squared couplings.
- `Multiband/Density.lean` rearranges finite row sums, justifies the substitution of squared transverse components and proves uniqueness. Its normal-state decomposition gives strict normal minimality even in the marginal case. A negative density energy implies a negative quadratic direction.
- `Multiband/Phase.lean` expresses alignment loss in Cartesian coordinates. It proves nonnegativity and propagates edgewise equality through positive connected couplings. Scalar folding rigidity uses the stated equality hypotheses.
- `Multiband/Window.lean` classifies full-energy minima assuming `Reduction`. This structure requires a full-spin folding map into the cube and an exact energy identity with a nonnegative remainder. It also requires an embedding with zero remainder. The two instability temperature sets agree if nonlinear descent is assumed as well. The rational interval comparisons assume that the energies belong to the stated intervals.
- `Multiband/InfiniteCore.lean` proves nine finite inequalities for Schur bounds, weighted head and mass estimates, coercivity, and complement differences. It also proves equality propagation on an abstract connected graph.
- `FSCore.lean` proves the complement identity, normal remainder and phase chord formulas. The other three statements concern positive-weight phase rigidity, complement saturation and the midpoint gap. Imports provide the finite density results. Document names in comments refer to written proofs.

## Scope

The main theorems also require written analysis and separate interval calculations. The Lean files stop short of the following steps:

1. Construction and assembly of the physical full-spin folding map and its complete equality cases.
2. Boundary perturbations, strictly interior nonzero support and physical support propagation.
3. Nonlinear small-amplitude descent, differential equivalence with Eliashberg equations, and the free-energy identity.
4. Spectral congruence, single crossing, a unique transition temperature or numerical eigenvalues.
5. Krawczyk root inclusion, outward interval arithmetic and physical energy enclosure membership.
6. Infinite-series convergence, weighted compactness, coercivity, attainment, hybrid-competitor limits and physical frequency-graph connectivity.
7. Measurable irreducibility, compact angular operators, weak lower semicontinuity, integral identities and continuum attainment.

[GitHub Actions](https://github.com/SuperMatics-Inc/eliashberg-uniqueness/actions) uses `leanprover/lean-action@v1` to download the Mathlib cache before building. A separate step checks for admitted proofs, new axiom declarations and uses of `native_decide`. The workflow runs on pushes and pull requests and can also be started manually.
