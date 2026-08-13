# Architecture

## Dependency direction

```text
Basic ──> Lattice ──> Gauge ──> Wilson
                         │          │
Polymer ─────────────────┴──────────> StrongCoupling
Lattice + Gauge + Wilson ──────────> Gauge.SiteReflection*
Compat ──> Baseline and explicit adapter lemmas only
```

`Basic` defines the minimal finite oriented two-complex and path machinery.
`Lattice` instantiates it on cubic lattices and owns all geometric counting.
`Gauge` owns Haar data, fields, observables, specifications, and finite-volume
probability. `Wilson` owns finite-dimensional unitary representation data.
`Polymer` is a model-independent hard-core polymer library.

The `Compat` layer may import upstream `LGT`; core generic modules may not. This
prevents periodic-torus implementation choices from leaking into box and
infinite-lattice definitions.

`YangMills.lean` is the project-native public root.  It reaches the completed
theorem families through four terminal imports without making audits,
milestone tests, the periodic Douglas baseline, or the older Dobrushin
comparison branch prerequisites of every build.  `YangMills.Regression` is
the opt-in comprehensive root for those modules.

## Mathematical API boundaries

1. Positive edge variables are stored; reverse orientation evaluates by inverse.
2. Paths are typed composable words, not quotient classes.
3. Boundary conditions are explicit exterior configurations.
4. Real probability and complex analyticity use different definitions.
5. Exponential clustering and Hamiltonian spectral gap are different theorems.
6. Area-law statements require explicit nontrivial center-charge data.

## File policy

Each nontrivial file begins with its conventions, paper-level role, and any
upstream provenance. Public modules should be small enough to review in one pull
request and should expose reusable helper lemmas rather than monolithic proofs.

## Build targets

Run the narrow changed module first, then the project-native root:

```sh
lake build YangMills.Path.To.ChangedModule
lake build
```

Before a release or after changing a shared foundational API, also run:

```sh
lake build +YangMills.Regression
```
