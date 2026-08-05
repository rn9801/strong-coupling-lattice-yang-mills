# Milestone 9: lattice counting and explicit strong-coupling disk

`YangMills.StrongCoupling.Counting` supplies the quantitative bridge from the
exact plaquette gas to a uniform zero-free theorem.

The formal estimates are:

- every positive cubic edge belongs to at most `4d` oriented plaquettes;
- the active-plaquette adjacency degree is at most `16d`, independently of
  the finite specification and exterior field;
- a deterministic breadth-first exploration proves that a graph of maximum
  degree `D` has at most `(2^D)^(n-1)` connected `n`-vertex sets containing a
  fixed root;
- rooted-polymer sums and incompatible-polymer sums are bounded by explicit
  geometric series, with a proved tail formula;
- the cardinality weight `(8q)^|γ|` satisfies the local Dobrushin criterion
  below `dobrushinThreshold`;
- `latticeStrongCouplingRadius d M` is strictly positive and depends only on
  dimension and the potential bound.

The exit theorem
`complexPartitionFunction_ne_zero_of_norm_lt_latticeRadius` states that, for
every finite specification and every frozen exterior configuration,

```text
‖β‖ < latticeStrongCouplingRadius d Φ.bound
```

implies that the exact complex Yang--Mills partition function is nonzero. The
radius is therefore uniform in finite volume and boundary condition.
