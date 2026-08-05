# Milestone 3: gauge action and holonomy

Milestone 3 turns the cubic-lattice geometry into a gauge-covariant observable
layer. Configurations live on canonical positive edges, while Mathlib's typed
quiver paths enforce composability of every holonomy product.

## Public modules

| Module | Main declarations |
|---|---|
| `YangMills.Gauge.Configuration` | `Configuration`, `GaugeTransformation`, `signedEdgeValue`, `gaugeTransform`, gauge `MulAction` |
| `YangMills.Gauge.Holonomy` | path edge support, `holonomy`, concatenation/reversal, endpoint covariance, continuity |
| `YangMills.Gauge.Observable` | `ContinuousClassFunction`, `LocalObservable`, support operations, pullbacks, plaquette and Wilson loops |
| `YangMills.Tests.Milestone3` | executable covariance, locality, gauge-invariance, and axiom regressions |

## Configurations and the gauge action

`Configuration d G` stores a value in `G` for every `PositiveEdge d`.
`signedEdgeValue` evaluates a forward signed edge by its stored value and a
backward signed edge by the inverse value on the same positive edge. In
particular, reversing a signed edge inverts its value.

`GaugeTransformation d G` is a site field. Its action is

```text
(g • A)(e) = g(source(e)) · A(e) · g(target(e))⁻¹.
```

The identity and composition laws are proved and registered as a `MulAction`.
The signed-edge covariance lemma treats both orientations uniformly.

## Typed path holonomy

For a typed path `p : Path x y`, `holonomy A p` is the ordered product of its
signed-edge values. The module proves the expected algebraic interface:

- the empty path has holonomy one;
- appending an edge multiplies by its signed value;
- concatenation maps to group multiplication;
- path reversal maps to group inversion;
- holonomy depends only on the finite positive-edge set `p.edgeSupport`;
- holonomy of a fixed path is continuous in the product topology.

The central covariance theorem is

```text
Hol(g • A, p) = g(x) · Hol(A, p) · g(y)⁻¹.
```

It is proved by induction on the typed path, with adjacent endpoint factors
telescoping. For `x = y`, this becomes conjugation at the loop base point.

## Local observables

`LocalObservable d G` contains a continuous map from the infinite
configuration space to `ℂ`, a finite positive-edge support, and a proof that
the map depends only on that support. The support is intentionally not claimed
to be minimal. The API includes support enlargement, constants, sums,
products, complex conjugation, translation pullback, gauge pullback, and a
canonical bounded-continuous-map/sup-norm bound when `G` is compact.

`ContinuousClassFunction G` packages a continuous complex function invariant
under conjugation. Composing one with a based loop holonomy produces a local,
gauge-invariant observable. The `wilsonLoop` constructor presently accepts
this general label; Milestone 5 will construct the canonical labels from
normalized characters of continuous unitary representations.

## Exit criterion

The production theorems
`LocalObservable.plaquetteClassFunction_gaugeInvariant` and
`LocalObservable.wilsonLoop_gaugeInvariant` prove gauge invariance for a
one-plaquette class-function observable and an arbitrary Wilson loop.
`YangMills.Tests.Milestone3` exercises both, along with endpoint covariance and
finite-support locality.

The covariance theorem has axiom footprint `[propext, Quot.sound]`; the two
continuous-observable theorems have
`[propext, Classical.choice, Quot.sound]`.
