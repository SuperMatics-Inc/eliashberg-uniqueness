# Supplement to Global uniqueness of the superconducting state in multiband and anisotropic Eliashberg models without Coulomb repulsion: scoped Lean proofs

Companion to “Global uniqueness of the superconducting state in multiband and anisotropic Eliashberg models without Coulomb repulsion”, repository `SuperMatics-Inc/eliashberg-uniqueness`.

Lean 4.35.0 and Mathlib v4.35.0 are required, with `autoImplicit = false`. The git requirement and committed manifest pin Mathlib to `56a005855ea17e0b0958f73ec801ae140b0a1679`.

With elan installed, from this directory:

```sh
lake exe cache get
lake build
```

Fetch the precompiled cache rather than compiling Mathlib from source. `Multiband.lean` and `FSCore.lean` print axiom dependencies. The proofs introduce no custom axioms or admitted proofs; ordinary foundational axioms remain.

## Mathematical content

- `KayThermo/Convex.lean`: finite arbitrary-coefficient density strict convexity, continuity, compact-cube attainment, uniqueness and the convex stationary-point criterion. Signs and weights are explicit hypotheses.
- `Multiband/Coefficients.lean`: reciprocity and symmetry, the zero-lag exception in off-diagonal positivity, Einstein-kernel positivity and monotonicity, and squared-coupling positivity.
- `Multiband/Density.lean`: finite row rearrangement, hidden substitution, density uniqueness, normal-state decomposition and strict normal minimality, including the marginal case. Negative density energy implies a negative quadratic direction.
- `Multiband/Phase.lean`: Cartesian alignment identities, nonnegative alignment loss, edgewise equality and propagation along positive connected couplings; scalar folding rigidity conditional on its explicit equality hypotheses.
- `Multiband/Window.lean`: full-energy classification conditional on the explicit `Reduction` interface. That interface assumes the full-spin folding map, cube membership, nonnegative remainder, exact energy identity and zero-remainder embedding. Equality of instability temperature sets additionally assumes nonlinear descent. Exact rational ordering of displayed energy intervals is conditional on enclosure membership.
- `Multiband/InfiniteCore.lean`: nine finite Schur, weighted head/mass/coercivity and complement-difference inequalities, and abstract connected-graph equality propagation. These are algebra for the written infinite-chain proof, not its analytic limit arguments.
- `FSCore.lean`: six pointwise statements: complement identity, normal remainder, phase chord, positive-weight phase rigidity, complement saturation and midpoint gap. Imports supply the finite density core. The source comments' document names refer to the written mathematical development, not additional Lean modules.

## Explicit limits

Neither main theorem is formalized end to end. The following remain written analysis or independent interval computation:

1. Construction and assembly of the physical full-spin folding map and its complete equality cases.
2. Boundary perturbations, strictly interior nonzero support and physical support propagation.
3. Nonlinear small-amplitude descent, differential equivalence with Eliashberg equations, and the free-energy identity.
4. Spectral congruence, single crossing, a unique transition temperature or numerical eigenvalues.
5. Krawczyk root inclusion, outward interval arithmetic and physical energy enclosure membership.
6. Infinite-series convergence, weighted compactness, coercivity, attainment, hybrid-competitor limits and physical frequency-graph connectivity.
7. Measurable irreducibility, compact angular operators, weak lower semicontinuity, integral identities and continuum attainment.

GitHub CI builds the Lean sources against the pinned Mathlib cache using `leanprover/lean-action@v1`, which fetches the Mathlib cache before `lake build`. CI runs on push and pull requests and can also be started manually; see the repository's Actions tab for run links. The workflow separately rejects proof escapes in project sources. The same cache-first sequence is recommended for a fresh local checkout. The source pins identify the portable dependency configuration; neither the build nor the source check extends the mathematical scope above.
