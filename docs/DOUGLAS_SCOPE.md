# Douglas compatibility scope

> Historical scope note: this document records the Milestone 0A comparison
> made before the project-native cubic-lattice and cluster-expansion layers
> were implemented.  Statements below of the form “the project still needs”
> describe the gap at that checkpoint, not the current status.  See the
> repository README and `STATUS.md` for completed Milestones 1--17.

The `YangMills/Compat` layer imports selected declarations from Michael R.
Douglas and Fred Rajasekaran's `LGT` repository at commit
`b8793ccf6a51e00e9e2b1685ba191b8626e37137`. This document records the exact
scope identified after Milestone 0A.

## Adapter boundaries

| Adapter | Upstream responsibility | Project use |
|---|---|---|
| `DouglasGeometry` | periodic sites, links, plaquettes, locality support, graph and anchor distances | finite-torus regression and later equivalence tests |
| `DouglasGibbs` | product Haar, Wilson weight, normalized measure, configuration gluing, Gibbs specification, DLR | measure-theoretic patterns and periodic regression |
| `DouglasDobrushin` | influence bounds, Dobrushin condition, strong-coupling two-point decay | early verified baseline and comparison route |

`DouglasLGT` is only a convenience umbrella. New compatibility code should
import the narrowest adapter. Core project modules must not import any adapter.

## Remaining upstream specializations

### Geometry

- Sites lie in the finite periodic torus `(ZMod N)^d`, not `ℤ^d`.
- A link stores an anchor and positive coordinate direction.
- A plaquette stores an anchor and two ordered coordinate directions.
- `boundaryLinks` returns four positive links; reversal is encoded by the
  hard-coded holonomy formula rather than a reusable signed-edge path.
- `latticePlaquetteDist` measures periodic `L¹` distance between anchors.
- `linkGraphDist` is distance in the shared-plaquette link graph.

At the Milestone 0A checkpoint, the project still needed boxes, exterior configurations, translations and
reflections on `ℤ^d`, signed edges, arbitrary finite paths, and equivalence
lemmas under torus reduction.

### Gauge and observable layer

- `plaquetteHolonomy` is a four-link formula, not general path holonomy.
- Locality results cover plaquette holonomy and plaquette trace observables.
- `HasGaugeTrace` is a lightweight real-trace interface.

At the Milestone 0A checkpoint, the project still needed open paths, loops, path support, a structured continuous
unitary representation API, Wilson characters, and explicit center charge.

### Probability and Gibbs layer

- `productHaar` is indexed by all links of a finite torus.
- `partitionFn` and `ymMeasure` use the upstream Wilson action.
- `gluedConfig` splits a finite torus into an arbitrary link subset and its
  complement; it does not encode a box with a genuinely exterior configuration.
- `ymMeasure_isGibbs` proves DLR consistency only for that finite model.
- Coupling is real and nonnegative in probability theorems.

At the Milestone 0A checkpoint, the project still needed general bounded conjugation-invariant potentials,
finite box specifications, boundary-disagreement sets, complex unnormalized
partition functions, and the thermodynamic limit.

### Dobrushin and mass-gap layer

- `ymDobrushinCondition` is specialized to the upstream Wilson action and
  shared-plaquette influence relation.
- `ym_mass_gap_exponential_decay` concerns two real plaquette trace observables
  for `U(n)` on a finite periodic torus.
- The small-coupling condition is `β < 1 / (4 n maxNeighbors(d))`.
- The theorem gives periodic finite-volume decay; it does not establish
  boundary-condition sensitivity or an infinite-volume Gibbs state.

At the Milestone 0A checkpoint, the project still needed general local-observable clustering, the independent
polymer expansion, analyticity and pressure, charged-center area laws, and both
reflection-positivity constructions.

## Proved compatibility surface

`DouglasGeometry.lean` now supplies:

- `periodicPlaquetteSupportSet_eq_upstream`, identifying our finite support
  wrapper with upstream `plaquetteLinkSupport` exactly;
- `periodicPlaquetteDistance_support_lowerBound`, transporting the upstream
  plaquette-to-link distance comparison through our support and distance names.

These lemmas are deliberately one-way adapters. They do not make the future
infinite cubic-lattice types definitionally equal to the periodic types.
