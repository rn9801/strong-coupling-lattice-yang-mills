# Formalization roadmap

This is the repository-facing index of the
[detailed roadmap](DETAILED_ROADMAP.md) supplied at project inception.
`STATUS.md` is authoritative for current progress.

## Phase A: verified baseline

0. Pin and audit Lean, Mathlib, `LGT`, `MarkovSemigroups`, and `GaussianField`.
0A. Compile the Douglas periodic-torus mass-gap theorem through narrow adapters.

## Phase B: finite-volume foundations

1. Cubic sites, positive and signed edges, plaquettes, paths, translations, boxes.
2. Normalized Haar probability and finite-product integration.
3. Gauge action, path holonomy covariance, and local observables.
4. General finite specifications, Gibbs measures, and complex partition functions.
5. Continuous unitary representations, Wilson potentials, loops, and center charge.

## Phase C: generic expansion and strong coupling

6. Finite abstract polymer gases and deletion recursion.
7. Connected clusters, Kotecky--Preiss bounds, and analytic families.
8. Exact plaquette-polymer representation and activity bounds.
9. Cubic-lattice connected-set counting and a safe small-`|β|` criterion.
10. Exponential boundary-condition sensitivity.
11. Boundary-independent infinite-volume local state.
12. Infinite-volume probability measure and DLR uniqueness.
13. Exponential clustering for general local observables.
14. Analytic local expectations and pressure.

## Phase D: confinement and reflection positivity

15. Edgewise center-selection rules.
16. Center-charged Wilson-loop area law and rectangle corollary.
17. Integer/site-hyperplane reflection positivity.
18. Half-integer/link-hyperplane reflection positivity via tree gauge fixing.
19. Infinite-volume reflection positivity.

## Optional phase E

20. Osterwalder--Schrader Hilbert space, transfer operator, and a genuine
Hamiltonian spectral-gap theorem.

Every milestone must build without placeholders, include executable regression
examples, record exact theorem names and assumptions, and update `STATUS.md`.
