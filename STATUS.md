# Project status

Last updated: 2026-08-05

## Current milestone: 10 -- Boundary decay

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
- Added a positive-dimensional continuous unitary representation wrapper with
  fixed matrix coordinates and no broad representation-theory dependency.
- Proved continuity, conjugation invariance, inversion-conjugation, identity,
  and the sharp dimension bound for matrix characters.
- Constructed the normalized character as a continuous class function, proved
  its pointwise unit bound, and built the bounded real Wilson plaquette
  potential required by the general finite-volume model.
- Proved the uniform Wilson perturbation estimate
  `|exp(β Φ(g)) - 1| ≤ exp(|β|) - 1`.
- Defined the finite-volume Wilson action and representation-labelled local
  Wilson loops; proved action and loop gauge invariance, the pointwise loop
  unit bound, orientation reversal, and immediate backtrack cancellation.
- Added explicit center-charge and finite-order center-charge data, and proved
  scalar center transformation laws for characters and Wilson loops,
  completing the Milestone 5 exit criterion.
- Defined a standalone finite hard-core polymer gas with compatible families,
  restricted partition functions, deletion recursion, and finite deletion
  certificates, with no Yang--Mills imports.
- Proved the local finite Dobrushin--Kotecký--Preiss criterion by strong
  induction on deletion ratios; every restricted partition function is
  nonzero under the explicit exponential inequality.
- Defined tuple incompatibility graphs, connected spanning-subgraph sums,
  Ursell coefficients, disconnected-cluster vanishing, spanning trees, and a
  conservative proved tree-indexed graph bound.
- Added analytic activity families, entire finite partition functions,
  analytic marked connected-family sums, absolute finite-support summability,
  and analytic KP packages under deletion and explicit local Dobrushin
  hypotheses, completing Milestones 6 and 7.
- Expanded the complex Boltzmann factor exactly over active plaquette subsets
  and proved each factor depends only on its typed dynamic-edge support.
- Generalized product-Haar factorization to finite families of functions with
  pairwise disjoint coordinate supports.
- Constructed canonical graph components of every active plaquette subset,
  proved their support cover, pairwise compatibility, and uniqueness among
  compatible polymer families, and derived exact activity factorization.
- Proved unconditional equality of the finite-volume Yang--Mills partition
  function and the abstract connected-plaquette polymer partition function,
  together with activity bounds and exterior-boundary locality, completing
  Milestone 8.
- Proved that each positive cubic edge meets at most `4d` oriented plaquettes
  and that active-plaquette adjacency has degree at most `16d`, uniformly in
  the finite volume and exterior field.
- Proved by deterministic breadth-first exploration that maximum degree `D`
  implies at most `(2^D)^(n-1)` rooted connected `n`-vertex sets, constructing
  the plaquette animal-counting certificate automatically.
- Proved rooted and incompatible polymer generating-function estimates,
  geometric tails, and a cardinality-weighted Dobrushin certificate below an
  explicit positive threshold.
- Defined the positive dimension-only `latticeStrongCouplingRadius` and proved
  the exact finite-volume complex Yang--Mills partition function is zero-free
  throughout that disk, uniformly over finite volumes and frozen exterior
  configurations, completing Milestone 9.
- Added a model-independent marked influence certificate and proved an
  exponentially decaying finite-range Neumann bound.  The full defect set is
  summed inside the path-length series, so the estimate has no factor
  proportional to the boundary size.
- Defined complex local-observable numerators and normalized expectations,
  proved the exact marked plaquette-subset expansion and its sup-norm bound,
  and proved marked weights are unchanged away from the exact exterior
  disagreement set.
- Defined observable-root and boundary-disagreement plaquettes, proved the
  uniform root count `|R(F)| ≤ 4d |support(F)|`, and proved the connected-set
  graph-distance/cardinality conversion needed for boundary decay.
- Constructed arbitrary-box compact-spin Gibbs specifications and proved their
  full DLR equations by finite-product Haar gluing.
- Proved volume-independent one-edge influence, `16d` interaction-neighbor,
  row-sum, and column-sum bounds, together with the explicit positive
  `boxDobrushinRadius`.
- Proved the normalized boundary-sensitivity theorem
  `complexGibbsExpectation_boundaryDecay`, with geometric decay and no factor
  proportional to the boundary-defect cardinality, completing Milestone 10.

### In progress

- Milestone 11 planning: infinite-volume Gibbs-state construction from the
  uniform finite-volume boundary estimate.

### Not started

- Milestone 12 and all later area-law and
  reflection-positivity results.

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
2026-08-05: lake -KmaxJobs=2 build YangMills.Wilson.Loop
  YangMills.Tests.Milestone5
  Success; 2,689 jobs; the Wilson unit bound, gauge invariance, and center
  transformation law have footprint
  [propext, Classical.choice, Quot.sound].
2026-08-05: lake -KmaxJobs=2 build
  Success; 3,713 jobs after completing Milestone 5. Warnings replayed during
  this build originate in pinned external dependencies; the new project
  modules build without warnings.
2026-08-05: lake build YangMills.Tests.Milestone6
  YangMills.Tests.Milestone7 YangMills.Tests.Milestone8
  YangMills.Tests.Milestone9
  Success; 2,789 jobs. The abstract finite-gas nonvanishing theorem, cluster
  bounds and analytic exit package, exact plaquette-polymer identity, lattice
  animal count, and uniform zero-free theorem have footprint
  [propext, Classical.choice, Quot.sound].
2026-08-05: lake -KmaxJobs=2 build
  Success; 3,734 jobs after completing Milestones 6--9. Warnings replayed
  during this build originate in pinned external dependencies; the new project
  modules build without warnings.
2026-08-05: lake build YangMills.Audit.DouglasAxioms
  Success; 3,690 jobs; the pinned upstream and regression theorem footprints
  remain [propext, Classical.choice, Quot.sound].
2026-08-05: lake build YangMills.Tests.Milestone10Foundations YangMills
  Success; 3,739 jobs. The aggregate marked influence tail, exact marked
  numerator expansion, and connected-set distance conversion have footprint
  [propext, Classical.choice, Quot.sound].
2026-08-05: lake -KmaxJobs=2 build
  Success; 3,738 jobs after adding the Milestone 10 foundation modules.
  Replayed warnings originate in pinned external dependencies; the new
  project modules build without warnings.
2026-08-05: lake build YangMills.Tests.Milestone10Foundations
  Success; 2,883 jobs. The marked influence tail, exact marked numerator
  expansion, graph-distance conversion, explicit Dobrushin radius theorem,
  and concrete boundary-decay exit theorem have footprint
  [propext, Classical.choice, Quot.sound].
2026-08-05: lake -KmaxJobs=2 build
  Success; 3,744 jobs after completing Milestone 10. Remaining messages are
  linter or deprecation warnings; there are no build errors.
```

## Conventions fixed so far

- Strong coupling means small `|β|` around the independent-Haar point `β = 0`.
- The cubic-lattice model stores variables only on positive edges;
  reversed edges evaluate by group inverse.
- Milestone 3 Wilson loops are labelled by arbitrary continuous class
  functions; Milestone 5 constructs canonical labels from normalized
  unitary-representation characters.
- Real Gibbs probability measures and complex analytic partition functions are
  separate APIs.
- The Dobrushin baseline and the polymer strong-coupling theorem remain distinct
  theorem families.
