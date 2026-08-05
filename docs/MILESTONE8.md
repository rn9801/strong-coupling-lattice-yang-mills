# Milestone 8: exact plaquette-polymer representation

`YangMills.StrongCoupling.PlaquetteExpansion` expands the complex Boltzmann
weight exactly over active plaquette subsets. `PlaquettePolymer` then equips
active plaquettes with adjacency by shared dynamic edge and defines polymers
as nonempty connected subsets.

The completed layer provides:

- dynamic-coordinate supports and dependence proofs for plaquette factors;
- product-Haar factorization over disjoint coordinate supports;
- canonical connected components of every active plaquette subset;
- compatible connected-polymer families and uniqueness of their union
  decomposition;
- activities given by the original finite-volume Haar integral;
- the bound `‖z(γ)‖ ≤ (exp(‖β‖ M)-1)^|γ|`;
- locality under changes of the frozen exterior field away from the polymer
  boundary;
- unconditional exact equality between the Yang--Mills and abstract polymer
  partition functions.

The exit theorem is
`complexPartitionFunction_eq_polymerPartition`. No factorization hypothesis is
assumed: `hasExactComponentFactorization` is derived from product Haar
locality and the canonical graph-component construction.
