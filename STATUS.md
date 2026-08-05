# Project status

Last updated: 2026-08-04

## Current milestone: 5 -- Wilson representation layer

### Completed

- Chosen the public package name `strong-coupling-lattice-yang-mills` and Lean
  namespace `YangMills`.
- Pinned Lean and Mathlib to `v4.30.0`, matching the current Douglas stack.
- Pinned `mrdouglasny/lgt` to commit
  `b8793ccf6a51e00e9e2b1685ba191b8626e37137`.
- Recorded the transitive Douglas pins:
  - `markov-semigroups` at
    `acf649108ea2222f4a8544a2782f448cb502492a`;
  - `gaussian-field` at
    `dc2b3b8378b2b7e33eaa8b61d6e943de11ff3f33`;
  - Mathlib at `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Added narrow geometry, Gibbs, and Dobrushin compatibility boundaries, plus a
  convenience umbrella that is excluded from core project layers.
- Proved `periodicPlaquetteSupportSet_eq_upstream` and
  `periodicPlaquetteDistance_support_lowerBound`, the first explicit
  compatibility results for upstream support and distance.
- Documented the exact periodic-geometry, plaquette-observable, finite-Gibbs,
  and Dobrushin specializations that remain upstream-specific.
- Added periodic-torus regression aliases for the upstream mass-gap and
  Gibbs/DLR theorems, importing only the narrow adapters they require.
- Added executable Mathlib API checks and Douglas declaration/axiom checks.
- Built the complete pinned dependency graph and this project successfully.
- Verified locally that the selected upstream measure, Gibbs, Dobrushin, and
  mass-gap declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- Proved compiling regression theorems
  `YangMills.Baseline.douglas_periodicTorus_massGap_regression` and
  `YangMills.Baseline.douglas_ymMeasure_isGibbs_regression`; their axiom
  footprints match upstream exactly.
- Searched the pinned Mathlib, `LGT`, `MarkovSemigroups`, and `GaussianField`
  sources for Kotecky--Preiss, Ursell, polymer-gas, tree-graph-bound, and cluster
  expansion infrastructure. No reusable implementation was found.
- Confirmed that project sources contain no `sorry` or `admit` placeholders.
- Initialized this directory as an independent Git repository on branch `main`;
  the parent worktree no longer governs its history.
- Audited and reused Mathlib's endpoint-indexed `Quiver.Path`, involutive quiver
  reversal, path mapping by prefunctors, and finite pointwise intervals.
- Defined cubic sites, positive edges, signed directions and edges, their
  source/target maps, reversal, and the underlying-positive-edge projection.
- Proved that reversal preserves the positive edge on which a future gauge
  configuration stores its variable.
- Added typed cubic paths with concatenation, reversal, straight segments,
  direction words, and translation.
- Defined coordinate plaquettes and arbitrary rectangular boundary loops.
- Proved the one-plaquette four-edge word and the general four-run rectangle
  word, together with closure and perimeter theorems.
- Defined nonempty finite coordinate boxes and their finite internal
  positive-edge sets.
- Added `GaugeHaarProbability`, an explicit chosen Haar probability carrying
  left, right, and inversion invariance without a global `MeasureSpace`.
- Constructed `GaugeHaarProbability.ofCompact` from Mathlib's normalized Haar
  measure for compact Borel topological groups, deriving right and inversion
  invariance from uniqueness of Haar probability.
- Exposed left, right, two-sided, and inversion maps as `MeasurePreserving`.
- Defined finite product Haar probability, proved coordinatewise preservation,
  and proved invariance of integrals under coordinate reindexing.
- Proved integral factorization for measurable real functions depending on
  disjoint coordinate sets, with explicit attribution to the generalized
  Douglas locality argument.
- Defined finite-box site fields, positive-edge fields, and their gauge action.
- Proved `productHaar_map_gaugeTransform`: independent Haar edge variables
  remain product Haar after every finite gauge transformation.
- Verified that the new core `Gauge` modules do not import `LGT` or
  `YangMills.Compat`.
- Defined infinite positive-edge configurations and sitewise gauge
  transformations, with backward signed edges evaluated by group inverse.
- Proved the identity and composition laws and registered gauge
  transformations as a genuine `MulAction` on configurations.
- Defined ordered holonomy on endpoint-indexed cubic paths and proved its
  empty-path, edge-append, concatenation, and reversal laws.
- Defined the finite positive-edge support of a path and proved holonomy only
  depends on that support.
- Proved endpoint covariance
  `Hol(g • A, p) = g(source(p)) Hol(A,p) g(target(p))⁻¹` by typed-path induction,
  and loop conjugation as its specialization.
- Proved continuity of fixed-edge evaluation and fixed-path holonomy in the
  product topology.
- Added continuous local observables with explicit finite supports, support
  enlargement, algebra operations, complex conjugation, translation and gauge
  pullbacks, and compact-domain sup-norm bounds.
- Added continuous class functions and local plaquette and Wilson-loop
  constructors.
- Proved gauge invariance of a one-plaquette class-function observable and an
  arbitrary Wilson loop, completing the Milestone 3 exit criterion.
- Defined arbitrary finite specifications by their dynamic positive edges,
  active plaquettes, and explicit frozen exterior configuration.
- Proved exterior gluing is continuous and intertwines boundary-compatible
  dynamic gauge transformations with the full configuration-space action.
- Equipped every specification's dynamic variables with finite product Haar
  probability and proved coordinatewise dynamic gauge transformations preserve
  it, including an integral change-of-variables theorem.
- Defined bounded continuous real plaquette potentials with conjugation and
  inversion symmetry, and defined their finite-volume action and an explicit
  uniform action bound.
- Defined the positive real Boltzmann weight, partition function, and normalized
  Gibbs expectation; proved weight integrability, strict partition-function
  positivity, normalization on the constant-one observable, and the bounded
  expectation estimate.
- Proved active plaquette holonomy conjugation, action and weight invariance,
  partition-integrand invariance, and Gibbs-expectation invariance under every
  boundary-compatible gauge transformation.
- Defined the complex finite-volume partition function separately from the real
  probability API, justified differentiation under its integral by an explicit
  local dominating bound, and proved it is entire.
- Proved `partitionFunction_zero` and `complexPartitionFunction_zero` for every
  arbitrary finite specification, completing the Milestone 4 exit criterion.

### Not started

- Milestone 5 Wilson representation layer (current).
- All polymer, infinite-volume, area-law, and reflection-positivity results.

## Verification log

Commands are added here only after they succeed.

```text
2026-08-04: lake update
  Success; generated lake-manifest.json at the pinned revisions.
2026-08-04: lake build YangMills.Audit.MathlibSmoke
  Success; 2,686 jobs.
2026-08-04: lake build YangMills.Baseline.PeriodicTorusMassGap
  Success; 3,687 jobs.
2026-08-04: lake build
  Success; 3,690 jobs.
2026-08-04: lake build YangMills.Audit.DouglasAxioms
  Success; 3,690 jobs; selected upstream, compatibility, and regression
  footprints are
  [propext, Classical.choice, Quot.sound].
2026-08-04: lake build
  Success; 3,693 jobs after completing the Milestone 0A adapters.
2026-08-04: lake build YangMills.Lattice.Path
  Success; 743 jobs.
2026-08-04: lake build YangMills.Lattice.Plaquette YangMills.Lattice.Box
  YangMills.Tests.Milestone1
  Success; 837 jobs; plaquette and rectangle boundary axiom footprints are
  [propext, Quot.sound].
2026-08-04: lake build
  Success; 3,699 jobs after completing Milestone 1.
2026-08-04: lake build YangMills.Gauge.ProductHaar
  YangMills.Gauge.FiniteEdgeHaar
  Success; 2,590 jobs.
2026-08-04: lake build YangMills.Tests.Milestone2
  Success; 2,591 jobs; the compact Haar constructor, disjoint-support
  factorization, and finite gauge-invariance exit theorem have footprint
  [propext, Classical.choice, Quot.sound].
2026-08-04: lake build
  Success; 3,702 jobs after completing Milestone 2.
2026-08-04: lake build YangMills.Gauge.Observable YangMills.Tests.Milestone3
  Success; 1,952 jobs; path covariance has footprint [propext, Quot.sound],
  while the plaquette and Wilson-loop gauge-invariance theorems have footprint
  [propext, Classical.choice, Quot.sound].
2026-08-04: lake build
  Success; 3,705 jobs after completing Milestone 3.
2026-08-04: lake -KmaxJobs=2 build YangMills.Gauge.ComplexFiniteVolume
  YangMills.Tests.Milestone4
  Success; 2,744 jobs; arbitrary-specification normalization, the bounded
  Gibbs expectation, admissible gauge invariance, and entire analyticity have
  footprint [propext, Classical.choice, Quot.sound].
2026-08-04: lake -KmaxJobs=2 build
  Success; 3,708 jobs after completing Milestone 4. Warnings replayed during
  this build originate in pinned external dependencies; the new project
  modules build without warnings.
```

## Conventions fixed so far

- Strong coupling means small `|β|` around the independent-Haar point `β = 0`.
- The cubic-lattice model stores variables only on positive edges;
  reversed edges evaluate by group inverse.
- Milestone 3 Wilson loops are labelled by arbitrary continuous class
  functions; Milestone 5 will construct the canonical labels from normalized
  unitary-representation characters.
- Real Gibbs probability measures and complex analytic partition functions are
  separate APIs.
- The Dobrushin baseline and the polymer strong-coupling theorem remain distinct
  theorem families.
