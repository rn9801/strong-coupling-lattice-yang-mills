# Milestone 4: general finite-volume model

Milestone 4 supplies the finite-volume probability and analytic layers for an
arbitrary specification of dynamic edges, active plaquettes, and frozen
exterior edge values. No box-shaped-region convention is built into the core
definitions.

## Public modules

| Module | Main declarations |
|---|---|
| `YangMills.Gauge.Specification` | `FiniteSpecification`, exterior gluing, admissible boundary gauge transformations, product Haar measure |
| `YangMills.Gauge.FiniteVolume` | bounded real plaquette potentials, action, real weight, partition function, Gibbs expectation, bounds and gauge invariance |
| `YangMills.Gauge.ComplexFiniteVolume` | complex weight and partition function, derivative under the integral, entire analyticity |
| `YangMills.Tests.Milestone4` | executable normalization, boundedness, gauge-invariance, analyticity, and axiom regressions |

## Arbitrary specifications

`FiniteSpecification d G` consists of a finite set of dynamic positive edges,
a finite set of active coordinate plaquettes, and an exterior configuration.
`evaluate` glues a dynamic configuration to those frozen exterior values. The
construction deliberately allows active plaquettes to meet dynamic and frozen
edges in any pattern.

The dynamic variables carry normalized finite product Haar probability. A
gauge transformation is `BoundaryCompatible` precisely when it fixes the
exterior value of every frozen positive edge. Gluing then intertwines its
coordinatewise dynamic action with the infinite-configuration gauge action.

## Real finite-volume theory

`RealPlaquettePotential G` packages a continuous real class function,
inversion invariance, and an explicit uniform bound. For an arbitrary
specification `Λ`, the module defines

```text
SΛ(U)       = ∑ p ∈ Λ.activePlaquettes, Φ(HolΛ(U, p)),
wΛ,β(U)     = exp(β SΛ(U)),
ZΛ(β)       = ∫ wΛ,β(U) dHaar(U),
EΛ,β[F]     = ZΛ(β)⁻¹ ∫ wΛ,β(U) F(U) dHaar(U).
```

The action and weights are continuous and uniformly bounded. Consequently the
weight, and its product with every bounded measurable observable, is
integrable. The partition function is strictly positive for real `β`, the
Gibbs expectation is normalized on `1`, and an observable satisfying
`‖F(U)‖ ≤ C` satisfies `‖EΛ,β[F]‖ ≤ C`.

Boundary-compatible transformations conjugate active plaquette holonomies, so
conjugation invariance of `Φ` gives action, weight, partition-integrand, and
Gibbs-expectation invariance. Separately, every coordinatewise dynamic gauge
transformation preserves finite product Haar probability.

## Complex analytic layer

The complex API is intentionally unnormalized: for `β : ℂ`,

```text
ZΛ(β) = ∫ exp(β SΛ(U)) dHaar(U).
```

An explicit action bound dominates the integrand and its complex derivative on
a neighborhood of each coupling. Mathlib's dominated parametric-integral
theorem therefore justifies differentiation under the integral. The resulting
theorem `complexPartitionFunction_entire` proves that `ZΛ` is entire without
treating a complex weight as a probability density.

## Exit criterion

For every `Λ : FiniteSpecification d G` and every bounded real potential `Φ`,
the production theorems
`partitionFunction_zero` and `complexPartitionFunction_zero` prove

```text
ZΛ(0) = 1.
```

`YangMills.Tests.Milestone4` checks this arbitrary-specification statement
together with positivity, the expectation bound, admissible gauge invariance,
entire analyticity, and their axiom footprints.
