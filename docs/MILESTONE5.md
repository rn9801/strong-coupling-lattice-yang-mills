# Milestone 5: Wilson representation layer

Milestone 5 turns the general class-function observables from Milestone 3 into
canonical Wilson observables labelled by positive-dimensional continuous
unitary representations. The implementation is purpose-built for lattice gauge
theory and does not introduce a broader representation-theory dependency.

## Public modules

| Module | Main declarations |
|---|---|
| `YangMills.Wilson.Representation` | `ContinuousUnitaryRepData`, character identities and bounds, normalized character, real Wilson potential, perturbation bound |
| `YangMills.Wilson.Loop` | finite-volume Wilson action, representation-labelled loops, orientation and backtrack laws, center-charge data and covariance |
| `YangMills.Tests.Milestone5` | executable unit-bound, gauge-invariance, center-covariance, and axiom regressions |

## Continuous unitary representations

`ContinuousUnitaryRepData G n` packages a continuous monoid homomorphism

```text
ρ : G → U(n)
```

together with `0 < n`. Fixing matrix coordinates keeps trace and entrywise
unitarity arguments transparent. The positivity field makes normalization by
`n` intrinsic and excludes the degenerate zero-dimensional case.

For `χρ(g) = Tr(ρ(g))`, the module proves:

- continuity and conjugation invariance;
- `χρ(g⁻¹) = conj(χρ(g))`;
- `χρ(1) = n`;
- `‖χρ(g)‖ ≤ n` from the unit bound on every diagonal matrix entry.

Thus the normalized character `χρ/n` is a continuous class function, equals
one at the identity, respects inversion by complex conjugation, and has norm at
most one.

## Wilson potential and action

The real Wilson plaquette potential is

```text
Φρ(g) = Re(χρ(g)/n).
```

It is continuous, conjugation invariant, inversion invariant, and bounded in
absolute value by one, so it directly instantiates Milestone 4's
`RealPlaquettePotential`. The associated `wilsonAction` is therefore available
on every arbitrary finite specification and is invariant under every
boundary-compatible gauge transformation.

The production perturbation estimate is

```text
|exp(β Φρ(g)) - 1| ≤ exp(|β|) - 1.
```

This is the single-plaquette bound needed by the later polymer application.

## Wilson loops

For a based cubic loop `C`,

```text
Wρ(C; A) = χρ(HolA(C)) / n.
```

The observable reuses the finite-support `LocalObservable` layer. Its recorded
support is exactly the path's positive-edge support. The module proves:

- pointwise `‖Wρ(C; A)‖ ≤ 1`;
- gauge invariance;
- reversal gives complex conjugation;
- inserting an edge immediately followed by its reverse changes nothing.

The backtrack theorem is stated on typed path pieces, so composability is
enforced by Lean rather than by list-side conditions.

## Center phase

`CenterChargeData ρ` records a chosen central element `z`, a nontrivial
unit-modulus phase `ω`, and the explicit scalar action

```text
ρ(z) = ω · I.
```

No irreducibility assumption or Schur-lemma machinery is needed. The module
derives

```text
χρ(zg)/n = ω χρ(g)/n
```

on either side of `g`, and consequently proves that a change of loop holonomy
from `h` to `zh` multiplies the Wilson loop by `ω`. An optional
`FiniteCenterChargeData` refinement records an order `m ≥ 2` and `ω^m = 1` for
the finite-order area-law development.

## Exit criterion

The production theorems `norm_wilsonLoop_le_one`,
`wilsonLoop_gaugeInvariant`, and `wilsonLoop_center_holonomy` prove the three
Milestone 5 exit conditions. `YangMills.Tests.Milestone5` exercises them along
with orientation reversal, backtrack cancellation, the action symmetry, and
the character bound.
