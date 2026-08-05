# Milestone 2: Haar probability and finite products

Milestone 2 supplies the probability space at the independent-edge point
`β = 0`. The implementation keeps the chosen Haar probability explicit and
does not install a global `MeasureSpace` on the gauge group.

## Public modules

| Module | Main declarations |
|---|---|
| `YangMills.Gauge.HaarProbability` | `GaugeHaarProbability`, `ofCompact`, left/right/inversion measure-preserving maps |
| `YangMills.Gauge.ProductHaar` | finite product Haar, coordinatewise preservation, reindexing, disjoint-support factorization |
| `YangMills.Gauge.FiniteEdgeHaar` | finite site and edge fields, edge gauge transformation, product-Haar invariance |
| `YangMills.Tests.Milestone2` | executable exit criterion and axiom regressions |

## Haar interface and compact constructor

`GaugeHaarProbability G` stores a selected measure together with
`IsProbabilityMeasure`, `Measure.IsMulLeftInvariant`,
`Measure.IsMulRightInvariant`, and `Measure.IsInvInvariant` instances. The
wrapper theorems expose fixed left multiplication, fixed right multiplication,
two-sided multiplication, and inversion as `MeasurePreserving` maps.

For a compact Borel topological group, `GaugeHaarProbability.ofCompact` uses
Mathlib's Haar measure normalized on the whole group. Right invariance is
derived by applying uniqueness of Haar probability to its right-translation
pushforward. Inversion invariance follows from the same uniqueness theorem for
the inverse measure. This construction works for noncommutative groups and
does not assume a second-countability hypothesis beyond Mathlib's actual API.

## Finite products

`ProductHaar.measure G ι` is `Measure.pi` of the selected Haar probability over
a finite index type. The module proves:

- coordinatewise measure-preserving maps preserve the corresponding product;
- an equivalence of finite index types preserves product Haar;
- integration is unchanged by that coordinate reindexing;
- measurable real functions depending on disjoint coordinate sets have a
  factorized product integral.

The last proof generalizes the argument in
`LGT.MassGap.Locality.integral_mul_of_disjoint_dependsOn` from the pinned
Douglas repository commit
`b8793ccf6a51e00e9e2b1685ba191b8626e37137`. Its provenance is recorded in the
source header. The core `Gauge` modules import Mathlib directly and do not
import `LGT` or `YangMills.Compat`.

## Exit criterion

For a finite box `b`, `FiniteEdgeHaar.SiteField b G` assigns group elements to
the sites and `FiniteEdgeHaar.EdgeField b G` assigns them to internal positive
edges. The action is

```text
(g • U)(e) = g(source(e)) · U(e) · g(target(e))⁻¹.
```

Each coordinate map preserves Haar by left and right invariance. Applying the
finite-product theorem gives
`FiniteEdgeHaar.productHaar_map_gaugeTransform`: independent Haar edge
variables remain product Haar after every finite gauge transformation.

`YangMills.Tests.Milestone2` checks this theorem along with the compact
constructor, coordinate reindexing, and disjoint-coordinate integral
factorization. The key declarations have axiom footprint
`[propext, Classical.choice, Quot.sound]`.
