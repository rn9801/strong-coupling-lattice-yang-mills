# Architecture

## Dependency direction

```text
Basic ──> Lattice ──> Gauge ──> Wilson
                         │          │
Polymer ─────────────────┴──────────> StrongCoupling
Lattice + Gauge + Wilson ──────────> ReflectionPositivity
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
