# Project status

Last updated: 2026-08-13

## Current milestone: 19 -- Infinite-volume reflection positivity (complete)

### Milestone 19 progress

- Completed the concrete integer/site-hyperplane component of Milestone 19.
  `FiniteSpecification.SiteSymmetric` records exact reflection invariance of
  dynamic edges, active plaquettes, and exterior data.  The new finite bridge
  partitions the concrete edge and plaquette labels, proves the product-Haar
  transport, splits the Wilson action, and transports every supported local
  observable to the labelled site-reflection normal form.
- Proved `siteReflectionPositive_gibbsMeasure` and
  `normSq_integral_gibbsMeasure_siteReflectionProduct_le` for every symmetric
  concrete finite specification and every real coupling, without a
  gauge-invariance hypothesis on observables.
- Proved centered identity-exterior specifications symmetric about the origin
  plane.  Finite positivity and Cauchy--Schwarz therefore hold for every
  centered approximant.  Passing through the KP local-expectation limit,
  using the one-root boundary-independence theorem, and translating gives the
  unconditional theorems `centeredInfiniteVolume_siteReflectionPositive` and
  `centeredInfiniteVolume_siteReflectionCauchySchwarz` for arbitrary exterior
  sequences and every integer coordinate plane throughout the explicit
  strong-coupling disk.
- Added `YangMills.Tests.ConcreteSiteReflection`, including concrete finite
  and infinite applications and axiom audits.  Every audited headline theorem
  uses only `propext`, `Classical.choice`, and `Quot.sound`.

- Added reflection through every affine diagonal plane
  `x τ - x σ = k` for distinct axes.  The site, signed-direction,
  signed-edge, stored-positive-edge, configuration, and local-observable
  operations are involutive; stored positive edges are permuted without
  inversion.
- Added the diagonal positive local algebra, requiring both endpoints of each
  support edge to lie in the closed positive half-lattice.  It contains all
  such local observables and deliberately has no gauge-invariance condition.
- Proved finite diagonal reflection positivity in the labelled
  fixed-plane/two-side Wilson normal form at `β ≥ 0`.  The proof conditions
  on tangential plane variables, identifies every fixed-plane slice with the
  existing explicit cut-plaquette Taylor/matrix-coefficient expansion, uses
  product-Haar Fubini, and integrates the resulting Gram sums with a positive
  plane weight.  The full pairing equals its Taylor pairing exactly.
- Proved Hermitian sesquilinearity and Cauchy--Schwarz for both the
  unnormalized and normalized finite diagonal reflection pairings.
- Proved the abstract closed-limit transfer of diagonal positivity and
  Cauchy--Schwarz, specialized it to the centered infinite-volume measure via
  `tendsto_centered_localExpectation_infiniteVolume`, proved boundary
  independence, and used translation invariance to reach every affine
  parallel diagonal plane.  Thus the diagonal infinite-volume passage is
  based on the KP cluster expansion.
- Added `YangMills.Tests.DiagonalReflection`, covering the affine formula,
  configuration involution, support predicate, automatic absence of a gauge
  premise, exact Taylor/Fubini equality, finite positivity and normalized
  Cauchy--Schwarz, abstract local limits, and the centered cluster
  specialization, with axiom audits of the headline declarations.
- Completed the concrete diagonal bridge from diagonally symmetric cubic
  `FiniteSpecification`s to the fixed-plane/two-side Taylor/Fubini normal
  form.  Centered identity-exterior boxes have the required symmetry, so the
  finite Gibbs laws satisfy diagonal positivity and Cauchy--Schwarz.
  Boundary independence and translation invariance transfer these statements
  through the KP local-expectation limit to every affine diagonal plane via
  `centeredInfiniteVolume_diagonalReflectionPositive` and
  `centeredInfiniteVolume_diagonalReflectionCauchySchwarz`.
- Added the infinite-lattice half-integer reflection on sites, stored positive
  edges, and configurations, together with continuous anti-linear site/link
  reflections of `LocalObservable`.  Both are proved involutive, and the link
  action has the required inversion on perpendicular crossing links.
- Defined the integer and half-integer positive local algebras by explicit
  support predicates.  `SiteReflectionPositive` tests all positive-side local
  observables; `LinkReflectionPositive` retains the full gauge-invariance
  hypothesis required by Milestone 18.
- Proved `siteReflectionPositive_of_localExpectation_tendsto` and
  `linkReflectionPositive_of_localExpectation_tendsto`: realness and
  nonnegativity pass to a local-state limit because `{0}` and `[0,∞)` are
  closed.  The centered specializations consume
  `tendsto_centered_localExpectation_infiniteVolume`, so this infinite-volume
  passage is entirely based on the existing KP cluster expansion.
- Proved boundary-condition independence of the resulting positivity
  statements and used the constructed measure's translation invariance to
  transfer the basic planes at `0` and `1/2` to every parallel integer and
  half-integer plane.
- Constructed the centered site-symmetric and shifted link-symmetric box
  families, proved their site geometry invariant under reflection, and proved
  the link family cofinal on every finite edge support.
- Added `YangMills.Tests.Milestone19`, exercising the reflection involutions,
  support predicates, symmetric-box geometry, abstract closed-limit passage,
  centered cluster specialization, and all-plane translation theorems.
- Completed the concrete link bridge for `FiniteSpecification.LinkSymmetric`
  specifications whose active plaquettes read only dynamic edges.  A
  one-sided full-lattice gauge transform sets every crossing link to the
  identity, preserves the negative side, and changes the positive variables
  only by Haar-preserving left/right multiplications.  The existing
  cut-plaquette Taylor/matrix-coefficient/Fubini theorem then yields the
  normalized finite Gibbs positivity and Cauchy--Schwarz declarations
  `linkReflectionPositive_gibbsMeasure` and
  `normSq_integral_gibbsMeasure_linkReflectionProduct_le`.
- Constructed completed link-symmetric specifications, proved their exact
  reflection symmetry and plaquette closure, and compared them with ordinary
  centered boxes using the finite-specification Gibbs tower and the explicit
  one-root KP boundary tail.  Their local expectations therefore converge to
  the cluster-constructed centered state.  This proves
  `centeredInfiniteVolume_linkReflectionPositive` and
  `centeredInfiniteVolume_linkReflectionCauchySchwarz` at every affine
  half-integer coordinate plane for `β ≥ 0` in the explicit strong-coupling
  disk, with the required gauge-invariance premise on observables.
- Added concrete diagonal and link reviewer regressions and axiom audits, and
  exported both theorem families from the project-native public root.
- Milestone 19 now meets its exit criterion for site, link, and diagonal
  reflections.  The only roadmap item after it is optional
  Osterwalder--Schrader reconstruction (Milestone 20).

### Completed

- Completed Milestone 18 (half-integer/link-hyperplane reflection
  positivity).  Added the reflection normal form with crossing-link fields,
  two strict-half fields, the crossing-edge inversion, and a simultaneous
  crossing-forest gauge fix whose induced side transformations are
  coordinatewise left/right multiplications.
- Proved product-Haar preservation of the forest gauge fix and identified the
  exact gauge-invariance condition on the positive algebra that sets all
  crossing links to `1`.  Unlike Milestone 17, link reflection positivity is
  deliberately stated only for gauge-invariant positive observables.
- Expanded every cross-plane Wilson potential into both orientations of the
  unitary-representation matrix coefficients.  The resulting cross action is
  exactly the normalized finite rank-one kernel
  `sum_a conj(feature_a Uminus) * feature_a Uplus`.
- Proved the normally convergent exponential Taylor expansion in the uniform
  norm, exchanged the series with product-Haar integration, expanded each
  kernel power into labelled Taylor words, and used Fubini to identify every
  coefficient with a finite Gram sum of half-volume amplitudes.
- Proved `linkReflectionPositivity` for `β ≥ 0`, Hermitian
  sesquilinearity, partition-function positivity, and Cauchy--Schwarz for
  both the unnormalized Gibbs pairing and normalized reflection inner
  product.  No Douglas compatibility module or Dobrushin theorem enters the
  proof.

- Completed the first documentation and build-dependency cleanup pass after
  Milestone 17.  The public `YangMills` root now exports the project-native
  headline theorem families without importing milestone tests, audits, the
  periodic Douglas baseline, or the older Dobrushin comparison modules.
- Completed the first Lean-warning cleanup pass on the dedicated
  `cleanup/lean-warnings` branch.  The full regression warning baseline fell
  from 715 to 511 project-owned messages.  The site/link reflection chain,
  augmented-polymer API, and concrete observable-root/KP module now compile
  without their own warnings.  The pass removes stale `simp` arguments,
  deprecated tactics, unused binders and section assumptions, and brittle
  definitional-equality reductions; it does not silence linters.  A global
  replacement of model-level `DecidableEq` instances was deliberately
  rejected after downstream elaboration showed that those instances are part
  of the computational behavior of `FinitePolymerModel`.
- Added the opt-in `YangMills.Regression` root and a declaration/import audit.
  The audit found no production proof block that can safely be deleted: every
  native module is reached by a headline theorem, a foundational result, or a
  milestone regression.  The largest cluster files are recorded as future
  file-splitting targets rather than treated as dead code.
- Added `YangMills.Tests.ReviewerSmoke`, a downstream critical-review suite
  proving twenty-one small corollaries and explicit fixtures.  It checks
  empty-volume partition functions at arbitrary real and complex coupling,
  constant Gibbs normalization, empty and constant-one Wilson loops, that
  zero lies in the explicit strong-coupling disk and carries the genuine KP
  certificate, direct vanishing of every zero-coupling polymer activity and
  of the symmetric Mayer logarithm itself, the corresponding exponential and
  zero-free theorem,
  analytic boundary independence and Wilson gauge invariance in infinite
  volume, vanishing covariance with constants, exact normalization of a
  zero-action reflection model, and the zero-area rectangle specialization.
- Rewrote the README with the lattice, gauge, Gibbs, Wilson, polymer/Mayer/KP,
  thermodynamic, pressure, area-law, and reflection definitions; indexed the
  main proved declarations and documented their exact present scope.
- Centralized the use and Apache-2.0 provenance of the pinned LGT repository,
  crediting Michael R. Douglas and Fred Rajasekaran, and removed repetitive
  historical comparisons from unrelated project-native module comments.
- Completed Milestone 17 (integer/site-hyperplane reflection positivity).
  Defined the site involution on sites, signed directions and signed edges,
  stored positive edges, paths, plaquettes, and full configurations.  Proved
  reflected signed-edge evaluation, path holonomy covariance, and invariance
  of every real plaquette potential satisfying the existing conjugation and
  inversion hypotheses.
- Added the anti-linear observable reflection `theta` on the full continuous
  observable algebra, with addition, multiplication, conjugate scalar,
  conjugation, involution, and uniform-norm laws.  Positive observables are all
  continuous functions of the plane and positive-side variables; no gauge
  invariance assumption is imposed.
- Implemented the explicit finite label partition `(A₀,A₋,A₊)` and proved
  `measurePreserving_reflectedVariableEquiv`, identifying the original finite
  product Haar law with plane Haar times two independent reflected side laws.
- Packaged the site-reflection Wilson action decomposition
  `S = S₊(A₀,A₋) + S₀(A₀) + S₊(A₀,A₊)` and supplied the
  explicit finite Wilson-plaquette constructor `ofWilsonPlaquettes`.
- Proved `gibbsReflectionPairing_eq_factorized`: Fubini and product-Haar
  factorization turn the full finite-volume reflected Gibbs integral into the
  plane integral of the two half-volume amplitudes.  On the diagonal,
  `factorizedPairing_self_eq_squareModulus` is the required weighted square
  modulus.
- Proved finite-volume site reflection positivity for every real `β` (hence
  every `β ≥ 0`) in `siteReflectionPositivity`, as well as positivity of the
  normalized reflection inner product.
- Proved Cauchy--Schwarz for the reflection inner product in squared form
  `normSq_reflectionInnerProduct_le` and norm/square-root form
  `norm_reflectionInnerProduct_le`, by identifying it with the ordinary
  complex `L²` inner product of weighted half-volume amplitudes.

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
- Audited Mathlib's countable-product Borel construction, compactness of
  probability measures on compact spaces, weak-convergence integral API, and
  Riesz--Markov/Prokhorov alternatives before choosing the compact weak-limit
  route for Milestone 12.
- Made `PositiveEdge d` explicitly countable, so the infinite configuration
  space has the required countable-product Borel structure.
- Defined centered boxes `[-n,n]^d`, proved nestedness of their site and edge
  sets, and proved that every finite edge support is eventually contained in
  the exhaustion.
- Defined centered arbitrary-boundary Yang--Mills specifications whose active
  plaquettes are exactly those incident to a dynamic edge, and pushed their
  Gibbs laws to probability measures on the full configuration space.
- Added a one-root `ClusterLimitCertificate` whose input is a uniform marked
  linked-cluster tail, and proved Cauchy convergence, additivity, complex
  homogeneity, normalization, the sup-norm bound, and boundary/sequence limit
  uniqueness for the resulting local state.
- Added an `InvariantClusterLimitCertificate` and proved that the asymptotic
  translated-boundary and gauge-transformed-boundary cluster comparisons imply
  translation and gauge invariance of the local state.
- Constructed an infinite-volume probability as a weak cluster point of the
  full-space finite-volume laws and proved that it represents every local
  cluster-state expectation.  Positivity and reality for nonnegative real
  local observables follow from the representing probability measure.
- Added a two-root linked-cluster certificate and proved the infinite-volume
  theorem `TwoRootClusterCertificate.exponential_clustering`, together with
  its literal exponential form and the explicit positive mass
  `-log(rate) > 0`.
- Kept all new Milestone 11--13 modules independent of `Compat/`, `LGT`, the
  Douglas repository, and the Dobrushin theorem family.  Their finite-volume
  hypotheses are explicitly one-root and two-root cluster-cancellation bounds.
- Added executable regressions and axiom checks for centered-box cofinality,
  the local-state algebra, probability representation, and exponential
  clustering; all have footprint
  `[propext, Classical.choice, Quot.sound]`.
- Defined the actual Mayer multi-index of a finite hard-core gas, its labelled
  incompatibility graph, Ursell coefficient, symmetry factor, activity
  monomial, and normalized connected cluster term in the polymer-only layer.
  Proved disconnected-cluster cancellation and the exact one-source and
  two-source scaling laws that select multiplicity-one rooted terms.  This
  module has no Yang--Mills, `Compat/`, `LGT`, or Douglas dependency.
- Proved the Milestone 11 cross-exhaustion principle: a vanishing one-root
  comparison tail between two independently chosen volume/boundary sequences
  forces their local cluster states to agree.
- Completed the Milestone 12 density/uniqueness step.  Real finite-edge
  cylinder functions form a separating Stone--Weierstrass algebra on the full
  compact configuration space; consequently two probability measures agreeing
  on local continuous observables are equal, and the cluster-state
  infinite-volume measure is the unique representing Borel probability.
- Proved the finite-volume normalized Mayer/log identity by a deletion-ordered
  Mayer series.  Each pinned insertion variable is strictly inside the unit
  disk under the local Dobrushin--KP certificate, its Taylor series equals
  `Complex.log (1 + u)`, and the exponential of the summed branch is exactly
  the restricted polymer partition function.  This avoids an invalid global
  principal-log choice.
- Exposed the weighted KP tree telescope and pinned bound from the existing
  explicit certificate: deletion from `U` to `V` costs at most the exponential
  of the deleted weights, while a marked compatible-partition ratio is bounded
  by `1 - exp (-a γ)`.  Instantiated both estimates and the exact Mayer
  identity for the plaquette gas on the explicit lattice strong-coupling disk,
  uniformly in finite volume and frozen exterior data.
- Added a polymer-only finite-root augmentation and instantiated one- and
  two-observable plaquette-root gases.  Root--bulk adjacency is exactly
  intersection with `observableRootPlaquettes`; distinct observable roots are
  compatible, so a two-root connected cluster can link them only through bulk
  plaquette polymers.  The associated one- and two-source partition
  polynomials are exact for arbitrary local observables; after vacuum
  normalization their linear coefficients are finite-volume expectations and
  their connected bilinear coefficient is exactly the truncated correlation.
  The construction has no `Compat/`, LGT, or Douglas dependency.
- Proved the finite connected-graph regrouping needed by the symmetric Mayer
  formula.  Spanning subgraphs are grouped by their canonical connected-
  component finpartition, finite-poset Möbius inversion isolates the connected
  fiber, and every partition-restricted signed graph sum is reduced to an
  explicit powerset inclusion--exclusion cancellation.  The public theorem
  `mayerUrsellGraph_eq_moebius_cancellation` identifies the existing Ursell
  coefficient with this Möbius cumulant.  The proof is polymer-only and has no
  Douglas or Yang--Mills dependency.
- Completed the degree-by-degree labelled-to-symmetric Mayer normalization.
  `mayerMultiIndicesOfDegree` enumerates exactly the multi-indices of total
  degree `n`; the multinomial identity proves
  `countPerms / n! = 1 / ∏γ X(γ)!`; and
  `labelledMayerDegreeSum_eq_symmetricMayerDegreeSum` applies the equality to
  the actual Ursell/activity coefficient.  The full symmetric series is now
  exposed as `symmetricMayerSum`.
- Completed the pinned symmetry normalization as well.  After distinguishing
  one of the `X(root)` labelled occurrences, the full symmetry factor is
  exactly `X(root) * pinnedMayerSymmetryFactor`; over `ℝ`, the pinned
  coefficient `X(root) / ∏γ X(γ)!` is exactly the inverse residual orbit
  factor.  The residual factor is also proved equal to the ordinary symmetry
  factor of `eraseRootOccurrence X root`, and the sum of the root-deleted
  child histograms is exactly that residual multi-index.  This removes the
  root-choice multiplicity from the remaining rooted-tree orbit enumeration.
  Degree by degree, `sum_pinnedSymmetricMayerDegreeSum` also proves that
  summing the pinned coefficient over root labels gives exactly `n` times the
  unpinned symmetric coefficient, providing the finite bridge needed to turn
  pinned KP bounds into convergence of the full Mayer series.
  The nonnegative identity `sum_pinnedNormMayerDegreeSum` proves the same
  statement for absolute degree sums, so no triangle-inequality loss is needed
  in that final convergence passage.
  `summable_normMayerDegreeSum_succ_of_pinned` packages the analytic
  consequence: summability of all positive-degree pinned norm series implies
  summability of the full positive-degree Mayer norm series.
- Strengthened the deletion-ordered logarithm with absolute convergence:
  the norm series of every pinned insertion has sum
  `-log (1 - ‖u‖)` and is bounded by its explicit Dobrushin weight `a γ`.
  The corresponding plaquette theorem
  `plaquetteAbsolutePinnedMayerSeriesBound` holds uniformly on the certified
  strong-coupling disk.
- Added the standard (activity-sum) `KoteckyPreissCertificate`, distinct from
  the deletion-ratio criterion, and proved a genuine rooted-tree fixed-point
  summability theorem: its nonnegative height layers are summable with total
  at most `exp (a γ) - 1`.  The existing plaquette animal estimates discharge
  this standard KP condition at the same explicit lattice radius with
  `a(γ)=|γ| log 2`, yielding the concrete bound `2^|γ|-1`.
- Formalized the Boolean-interval cancellation core of the Penrose argument.
  `PenroseIntervalScheme.abs_signedSum_le_card_trees` and its graph
  specialization give the sharp signed connected-graph bound by spanning
  trees, with no all-graphs multiplier, from any concrete interval scheme.
- Completed an unconditional Whitney broken-circuit proof of the sharp finite
  tree-graph inequality.  A canonical injective edge rank selects the least
  active edge; toggling it is a connectedness-preserving, sign-reversing
  involution, while inactive connected spanning edge sets are proved acyclic
  by ordered insertion and hence inject into the spanning trees.  The public
  theorem `Whitney.abs_connectedSpanningGraphSum_le_card_trees` therefore has
  no Penrose-scheme hypothesis and no all-graphs multiplier.
- Derived the exact symmetry-normalized, termwise Mayer tree domination
  `norm_mayerClusterTerm_le_mayerTreeMajorant` from the concrete Whitney
  theorem, together with its multiplicity-pinned form.  Instantiated these
  sharp bounds for the one- and two-observable augmented plaquette gases, so
  the adjoined observable roots now feed the same tree majorant as ordinary
  bulk polymers.
- Supplied the formal-power-series inverse identities missing from Mathlib.
  For complex series, `PowerSeriesBridge.expOf_logOf` proves that formal
  exponentiation recovers every series with constant coefficient one, and
  `PowerSeriesBridge.logOf_expOf` proves the converse for zero-constant-term
  series.  Both are derived from explicit logarithmic-derivative identities,
  not assumed as an interface.
- Proved the labelled-set/symmetric-multi-index half of genuine KP tree
  summation.  The factorially normalized `k`-child layer equals both its
  symmetric-multiset orbit sum and an actual `MayerMultiIndex` sum with
  denominator `∏δ X(δ)!`.  The theorem
  `hasSum_kpMayerForestDegreeSum` sums these degree layers exactly to the next
  `kpTreeIterate`; under the explicit standard KP certificate,
  `tsum_kpMayerForestDegreeSum_le_exp_of_koteckyPreiss` bounds the total by
  `exp (a root)`.
- Proved the structural root-deletion theorem for finite trees.
  `IsTree.existsUnique_adj_root_in_awayComponent` says that every connected
  component left after deleting a tree root contains exactly one vertex
  adjacent to that root.  Its acyclic uniqueness proof uses two-path
  cancellation, and its existence proof takes the first edge of a simple path
  from the root.  This supplies the canonical child root required by the
  recursive tree-species map.
- Completed the multiplicity and weight bookkeeping for rooted Mayer-tree
  deletion.  Connected components form a disjoint cover equivalent to the
  non-root vertex type; each child carries a canonical `MayerMultiIndex`;
  their sum plus the root singleton is exactly the original multi-index; and
  `histogramWeight_mayerChild_factorization` factors the complete activity
  monomial into the root weight and child monomials.  A child attachment in a
  Mayer spanning tree is formally incompatible with its parent, so
  `kpChildWeight_childRoot_eq` discharges both tests in the KP recursion.
- Defined the uniformly activity-scaled finite partition power series and its
  canonical formal Mayer logarithm.  The exact identity
  `expOf_formalMayerLog_eq_partitionPowerSeries` now fixes the branch of the
  finite logarithm algebraically; injectivity of `expOf` on zero-constant-term
  series reduces the final Mayer/log identification to the connected
  coefficient formula.
  Its coefficients vanish above `S.card`, and their finite sum through that
  degree is proved equal to `partitionOn S`, so the formal object is tied
  exactly to the existing scalar finite-volume partition function.
- Defined the restricted symmetric connected Mayer power series in the same
  formal variable.  Its constant coefficient is zero, and
  `restrictedSymmetricMayerPowerSeries_eq_formalMayerLog_of_expOf_eq` proves
  that the connected exponential formula alone implies equality with the
  canonical formal logarithm.  Thus branch selection and formal-series
  injectivity are completely separated from the remaining orbit enumeration.
- Completed the finite graph side of the rooted-tree orbit enumeration.
  `rootedGraphEquiv` makes root deletion lossless; valid attachment finsets
  are exactly componentwise Cartesian choices; and
  `sum_rootedForestData_eq_sum_forest_prod_component` gives their weighted
  product formula.  A forest is then mapped injectively to an unordered
  common-ambient family of `(vertex finset, edge finset)` tree data.  Those
  vertex finsets are pairwise disjoint and cover the residual occurrence
  type.  The weighted theorems
  `sum_rootedForestData_vertex_attachment_prod_le_exp` and
  `card_spanningTreeGraphs_mul_prod_away_le_exp_rootedChoices` compose root
  deletion, exact attachment multiplicities, activity monomials, unordered
  component families, and the finite labelled-set exponential without any
  dependent connected-component transports.
- Threaded the new finite enumeration through the actual Mayer majorant.
  `pinned_norm_mayerClusterTerm_le_componentTreeExp` starts from the sharp
  Whitney tree bound and retains the exact residual pinned factor
  `1 / ∏γ (X γ - δγ,root)!`.  Rooted child-component choices have a formally
  incompatible child label, and their occurrence weights are now rewritten
  exactly as symmetric label-histogram weights.  Thus the remaining global
  step is purely the orbit reindexing across varying residual
  `MayerMultiIndex` values, rather than any graph or weight decomposition.
- Lifted every full-volume standard KP certificate to any finite family of
  zero-activity source roots.  The bulk inequalities are unchanged and each
  root receives exactly its touching tilted bulk mass.  The explicit lattice
  disk now instantiates genuine one- and two-observable-root KP certificates,
  together with symmetric forest `tsum` bounds at each root.  This establishes
  the augmented gas estimates at the expansion point; identifying arbitrary
  observable marked numerators with those root gases remains part of the
  concrete linked-cluster certificate work.
- Completed the symmetric fixed-labelled occurrence normalization.  The
  histogram fiber of `Fin n → P` is proved to have cardinality
  `X.toMultiset.countPerms` by extracting the relevant coefficient from
  Mathlib's multivariate multinomial theorem.  Consequently the literal sum
  over every rooted labelled tree on `Option (Fin n)`, divided by `n!`, is
  exactly `residualSymmetricPinnedTreeDegreeSum`; this is then reindexed
  exactly to the degree-`n+1` multiplicity-pinned Mayer tree majorant.  No
  informal orbit quotient or varying dependent occurrence type remains.
- Added the graph-to-labelled-set-partition adapter needed for the remaining
  rooted-tree species step.  Connected components of a graph on `Fin n` are
  ordered canonically by their maximum vertices and become Mathlib
  `OrderedFinpartition` blocks with increasing vertex enumerations.  The
  construction is also instantiated for the complement of the distinguished
  `none` root in a graph on `Option (Fin n)`.  Each ordered block is now
  transported to its literal carrier `Fin (partSize i)`, is proved to be a
  tree in the restricted labelled incompatibility graph, and carries a
  canonical local attachment index whose label is incompatible with the
  parent root.
- Proved the exact fixed-labelled attached-component normalization.  After
  selecting one of the `s` possible attachment positions, `finSuccEquiv'`
  identifies its label tuple with a child root and `s-1` residual labels, and
  the component spanning-tree count becomes the existing fixed-rooted tree
  count.  The theorem
  `factorialNormalizedLabelledAttachedComponentDegreeSum_succ` realizes the
  crucial `s / s! = 1 / (s-1)!` cancellation and rewrites the result as the
  KP incompatible-child sum of the preceding rooted-tree degree layer.
- Isolated the exact final generic hypothesis as
  `RootedTreeOrbitRecurrence` and proved that it implies
  `RootedTreeOrbitBound`.  From that bound the existing explicit standard KP
  certificate now gives genuine summability of the residual pinned tree
  series, the actual multiplicity-pinned Mayer norm series, and the full
  positive-degree Mayer norm series.
- Discharged `RootedTreeOrbitRecurrence` unconditionally by the fixed-labelled
  rooted-forest species construction.  The resulting certified theorems give
  genuine pinned and unpinned Mayer summability and the quantitative residual
  rooted-orbit bound from the standard KP certificate alone; no additional
  combinatorial premise remains.
- Completed the symmetric finite connected exponential formula.  Labelled
  moments are regrouped by their exact multi-index histograms, the connected
  graph sum is identified with the partition Möbius cumulant, and Mathlib's
  Faà di Bruno theorem supplies the logarithmic derivative recurrence.  The
  theorem `restrictedSymmetricMayerPowerSeries_eq_formalMayerLog` now proves
  that the canonical symmetric Mayer series is exactly the formal logarithm
  of the finite hard-core partition series.
- Instantiated the unconditional result for plaquette polymers on the explicit
  lattice strong-coupling disk: the full positive-degree Mayer majorant is
  summable and each residual pinned tree orbit sum is bounded by `2^|γ|`.
  The one- and two-observable augmented gases inherit the exact formal
  Mayer/log identity, certified residual root-tree summability, and explicit
  volume-independent root budgets bounded in terms of the observable support.
  These statements use the cluster expansion and the standard KP certificate,
  not the Douglas influence-matrix route.
- Began the exact model-specific marked resummation.  The dynamic coordinate
  support of a local observable is now explicit, and a marked Haar weight is
  proved to factor whenever a plaquette block avoids both that support and the
  remaining marked block.  Splitting the canonical connected components into
  observable-touching and away families then gives the exact theorem
  `complexObservableNumerator_eq_sum_rootComponentWeight_mul_awayFamilyWeight`:
  every away component factors into its ordinary polymer activity while all
  observable-touching components remain in a single marked root decoration.
- Promoted those marked decorations to a finite mutually-exclusive source
  polymer type.  The canonical subset-to-decoration/bulk-family map is proved
  bijective, so `decoratedObservableRootCoefficient` is exactly the arbitrary
  local-observable numerator and the resulting decorated source polynomial is
  exactly `oneObservableSourcePartition`.  The exclusive decorated gas has an
  explicit zero-source KP certificate, a certified residual Mayer-tree budget
  at every decoration, and the exact fixed-labelled Mayer/formal-log identity.
- Proved the generic exclusive-root partition decomposition in the
  polymer-only layer: every compatible augmented family is uniquely either a
  bulk family or one root together with an allowed compatible bulk family.
  Instantiating it shows that the full partition function of
  `decoratedObservableRootModel` is exactly
  `oneObservableSourcePartition`, not merely that their displayed linear
  coefficients agree.  The common source also scales every connected Mayer
  term by the total multiplicity of all decorated roots, providing the exact
  multiplicity selector needed for the one-root cluster series.
- Closed the one-root absolute-summability bridge.  Compatible decorations
  have additive plaquette cardinality; their KP root weights are bounded by
  the ordinary observable-root budget plus the weights of the absorbed
  polymers.  The twice-tilted animal generating function then sums every
  decoration with a volume-independent observable-support prefactor.  A new
  polymer-only fixed-labelled reindexing theorem deletes the unique
  exclusive root and proves that the actual total-root-multiplicity-one Mayer
  coefficient is dominated degree by degree by those residual tree orbits.
  Consequently its norm series is genuinely summable on the explicit
  lattice strong-coupling disk, with an explicit uniform total-mass bound.
- Closed the exact one-observable connected-series identity.  Observable
  sources are retained as polynomial coefficients of the total-activity
  power series; a polymer-independent coefficientwise source derivation
  satisfies the formal exponential chain rule.  Evaluating the fixed-labelled
  Mayer exponential at every complex source value proves the pointed
  exponential formula before source extraction.  Its linear coefficient is
  the exact identity `root partition coefficient = bulk partition function *
  tsum multiplicity-one connected Mayer coefficients`.  Instantiating the
  decorated root identifies the marked numerator with this product, and,
  whenever the finite vacuum partition function is nonzero, identifies the
  normalized arbitrary-local-observable Gibbs expectation with the actual
  absolutely convergent decorated connected cluster series.  No logarithm
  branch and no Douglas/influence-matrix argument enters this proof.
- Closed the fixed-labelled two-source algebra.  A bivariate polynomial
  source power series now has coefficientwise source derivatives and a
  proved mixed exponential identity
  `R₀₁ = Z * (C₀₁ + C₀ * C₁)`.  For two mutually compatible labelled roots,
  source extraction identifies the three connected Mayer sectors exactly;
  under their absolute-summability hypotheses, evaluation at unit total
  activity gives the corresponding analytic partition identity.  Every
  nonzero mixed connected term contains a path between the two nonadjacent
  labelled roots.
- Instantiated the exact finite-volume cumulant cancellation for arbitrary
  bounded local observables.  The degreewise decorated cumulant subtracts
  the Cauchy product of the two one-root connected series from the connected
  series of the product observable.  Its norm series is summable on the
  explicit strong-coupling disk, and the normalized truncated Gibbs
  correlation is exactly its `tsum`.  This is a cluster-expansion identity;
  it does not use the Douglas compatibility layer or an influence matrix.
- Closed the genuine two-root KP/summability gap.  Deleting both labelled
  occurrences gives an exact degree-`n+2` normalization by a root-free
  two-pinned symmetric tree orbit.  A quantitative quarter-budget refinement
  of the lattice KP estimate leaves enough reserve to switch on both roots at
  explicit nonzero activities.  Source rescaling then proves absolute
  summability of the first-root, second-root, and genuinely mixed unit-source
  Mayer sectors, and instantiates the evaluated identity
  `R₀₁ = Z * (C₀₁ + C₀ * C₁)` without convergence hypotheses.
  The regularized gas also has genuine pinned spanning-tree summability at
  either root.  All of these statements are derived from the cluster
  expansion and the explicit KP certificate.
- Completed the exact support-graded two-observable reindexing.  The nested
  exclusive augmented gas has bulk, left-decoration, right-decoration, and
  intrinsic-bridge polymers with bidegrees `(0,0)`, `(1,0)`, `(0,1)`, and
  `(1,1)`.  Explicit finite bijections identify its separated and bridge
  compatible-family sectors with the original marked plaquette-subset
  expansion, proving that its full partition function is exactly
  `Z + α N_F + θ N_H + αθ N_{FH}`.
- Added a polymer-only bigraded source exponential.  Its symmetric
  multi-index coefficients obey the exact fixed-labelled Mayer exponential,
  source extraction selects the three bidegree-one sectors, and finite
  total-activity evaluation proves the honest pointed identities after
  absolute summability.  This yields
  `complexGibbsTruncatedCorrelation_eq_tsum_bivariateDecoratedMixed`, an exact
  representation of the finite-volume truncated correlation by the new
  support-graded mixed cluster series.
- Proved a genuine nonzero-source KP certificate for the complete decorated
  bivariate gas.  A positive explicit common regularization is defined from
  the finite tilted mass of every left, right, and bridge decoration; the
  bulk proof spends only the existing quarter-budget lattice reserve.
  Consequently the full regularized Mayer majorant, every pinned spanning-
  tree series, and the unit-source first, second, and mixed sectors are
  genuinely summable.  No convergence premise or Douglas/Dobrushin
  comparison theorem is used.
- Closed the remaining mixed-root normalization dichotomy.  Bidegree `(1,1)`
  is proved to contain either exactly one intrinsic bridge root or exactly
  one left and one right decoration root.  For every nonzero term in the
  second case, `bivariateDecorated_mixed_nonzero_spanning_witness` produces a
  literal simple path between the distinguished occurrences in the actual
  Mayer incompatibility graph.  Thus the former combinatorial reindexing
  roadblock is resolved; the remaining work is the spatially weighted tail
  and centered-box comparison built on this witness.
- Added the polymer-independent natural-weight scaling needed for that tail.
  Mayer activities and connected cluster terms scale exactly by total weight;
  in particular the absolute `(1,1)` sector with an arbitrary natural weight
  is exactly the unweighted mixed sector of the corresponding tilted gas.
  This reduces the spatial tail to a model-specific tilted KP certificate,
  rather than any further symmetric normalization infrastructure.
- Completed that model-specific analytic step in
  `StrongCoupling/SpatialClusterExpansion.lean`.  The strict slack in the
  explicit animal threshold gives a proved factor `plaquetteCardinalityTilt`
  strictly larger than one.  Multiplying every bulk, left-root, right-root,
  and bridge-root activity by this factor to the cardinality of its complete
  plaquette support preserves a genuine KP certificate.  A new positive
  finite-source regularization proves the certificate for the complete
  nonzero-source decorated gas.  Consequently its full Mayer majorant, every
  pinned spanning-tree series, and the exact mixed sector weighted by
  `t ^ totalPlaquetteCardinality` are genuinely summable.  This proof uses
  only cluster expansion, the existing explicit KP reserve, and animal
  counting; it has no Douglas/Dobrushin comparison dependency.
- Completed the geometric support step in
  `StrongCoupling/SpatialClusterGeometry.lean`.  The two observable roots are
  adjoined to the active-plaquette adjacency graph, and every bulk, one-sided,
  and bridge decoration is proved to have a connected carrier.  Incompatible
  decorated polymers link their carriers, so induction along the literal
  Mayer walk produces a connected two-root carrier.  Its cardinality is at
  most total charged plaquette multiplicity plus the two abstract roots.
  Therefore every nonzero mixed `(1,1)` Mayer term satisfies the genuine
  support inequality
  `observable plaquette separation ≤ total plaquette cardinality`.  This
  closes the bridge/path combinatorial and geometric roadblock without any
  Douglas or influence-matrix argument.
- Summed the spatial support inequality over the complete mixed Mayer sector
  and evaluated its weighted majorant from the existing explicit KP
  certificate.  A polymer-only source-pinning inequality charges only the
  first-coordinate source polymers, and the certified pinned-tree `tsum`
  bound gives
  `t^separation * ‖truncated correlation‖ ≤ (ρ^2)⁻¹ * reserve` without a
  bulk-volume sum.
- Proved an explicit volume-free lower bound for that regularized source
  radius.  The tilted mass of a complete decoration is controlled by its
  linear observable-root touching budget and the weights of its absorbed
  polymers; animal summation then removes the finite specification and
  exterior field.  Thus
  `pow_spatialSeparation_mul_norm_complexGibbsTruncatedCorrelation_le_uniformPinnedTreeBudget`
  is uniform in every finite volume and boundary condition for each fixed
  pair of local observables.
- Completed the symmetric one-root boundary tail in
  `StrongCoupling/ClusterBoundaryExpansion.lean`.  Mayer degree is proved
  independent of the extensionally equal finite-type enumerations induced by
  `withExterior`; clusters avoiding the exact disagreement plaquettes cancel
  term by term; and every nonzero connected multiplicity-one cluster reaching
  a defect pays its full plaquette-cardinality distance.  Genuine summability
  then gives the normalized expectation estimate
  `t^r * ‖⟨F⟩_η - ⟨F⟩_η'‖ ≤ 2 * observableCardinalityTiltDecorationBudget`.
  Disconnected defects are correctly excluded from the distance premise,
  since Mathlib records their graph distance as zero.  This entire proof is
  the decorated Mayer expansion plus the explicit KP/tree certificate; it
  imports neither the Dobrushin boundary theorem nor a Douglas compatibility
  module.
- Constructed finite ambient observable-root neighborhoods recursively and
  used centered-box cofinality to prove that every reachable disagreement
  plaquette eventually lies beyond any prescribed cluster radius.  This
  yields a uniform inverse-tilt bound for arbitrary pairs of centered exterior
  fields and the concrete theorem
  `tendsto_centered_complexGibbsExpectation_boundary_sub_zero` for any two
  boundary sequences.
- Instantiated the complete two-root finite-volume estimate as
  `centeredObservableAmplitudeClusterCertificate` over any centered one-root
  limit certificate.  The public theorem
  `centeredClusterLimit_exponential_clustering_exp` has the explicit positive
  mass `centeredClusterMass = -log plaquetteClusterDecayRate`; overlapping
  supports receive the harmless distance zero and disjoint supports retain
  the ambient plaquette-incidence distance.
- Proved the finite-product Gibbs tower for nested arbitrary specifications.
  A large-volume Gibbs expectation is exactly an average of smaller-volume
  Gibbs expectations with induced exterior data, and a uniform small-volume
  boundary diameter therefore bounds the cross-volume difference.  Its
  centered specialization closes the Cauchy argument for every local
  observable using only the one-root cluster tail.
- Defined `centeredInfiniteVolumeMeasure` at the explicit lattice
  strong-coupling radius and proved convergence of every centered local
  expectation, independence of arbitrary exterior sequences, and uniqueness
  among probability measures representing the local cluster state.
- Proved gauge invariance of the concrete infinite-volume local state from
  finite-volume gauge covariance and boundary independence, and strengthened
  it to the literal pushforward identity
  `centeredInfiniteVolumeMeasure_map_gaugeTransform` and its
  `MeasurePreserving` form.  Proved translation invariance by embedding a
  translated centered box into an
  explicitly enlarged centered box and applying the same Gibbs-tower and
  one-root KP tail comparison.
- Registered the concrete infinite-volume measure as a regular Borel
  probability.  This uses the roadmap's permitted compact weak-limit route;
  the previously proved Stone--Weierstrass density theorem supplies uniqueness
  and agreement with all local continuous observables.
- Passed the uniform two-root covariance estimate to the concrete
  infinite-volume measure.  The theorem
  `centeredInfiniteVolume_exponential_clustering` has the explicit amplitude
  `centeredClusterObservableAmplitude` and the strictly positive mass
  `centeredClusterMass`, thereby completing the Milestone 13 exit criterion.
- Completed Milestones 11--13 at the explicit strong-coupling radius.  The
  thermodynamic-limit, invariance, measure-representation, and clustering
  proofs use the plaquette polymer cluster expansion and its explicit KP/tree
  certificate, not the Douglas compatibility layer or the Dobrushin baseline.
- Audited the pinned Mathlib complex-analysis infrastructure for Milestone 14.
  Mathlib supplies locally uniform Weierstrass convergence, Cauchy derivative
  bounds, Arzelà--Ascoli compactness, and the analytic identity principle, but
  not a directly reusable complex Vitali theorem.  Added a proved disk Vitali
  package from precisely those results, without new axioms.
- Proved that every centered finite complex local expectation is exactly its
  absolutely convergent connected decorated observable-root Mayer series and
  is uniformly bounded on every smaller closed strong-coupling disk by an
  explicit volume-independent KP/tree majorant.
- Defined `analyticInfiniteVolumeLocalExpectation` as the resulting locally
  uniform thermodynamic limit.  Proved it analytic on
  `ball 0 (latticeStrongCouplingRadius d Φ.bound)`, identified its real-axis
  values with integration against `centeredInfiniteVolumeMeasure`, and proved
  the analytic continuation is independent of the centered exterior sequence.
- Constructed the countable infinite plaquette-polymer Mayer model and its
  explicit KP certificate, rooted pressure terms, absolute majorants, and
  anchored pressure.  Proved the anchored pressure analytic throughout the
  same explicit complex disk.
- Proved the centered-box boundary/volume estimate by showing the fitting-root
  fraction of every fixed finite cluster tends to one.  Tannery dominated
  convergence with the rooted KP norm sum then proves convergence of the exact
  normalized finite symmetric Mayer logarithms to both the per-site and
  per-ordered-plaquette anchored pressures.
- Proved that each finite symmetric Mayer logarithm in the pressure exhaustion
  exponentiates to the exact finite-volume Yang--Mills partition function, so
  the limiting pressure uses the cluster-normalized logarithm branch at
  `β = 0`, not an arbitrary principal logarithm.
- Completed Milestone 14.  Both the local-observable and pressure arguments use
  the plaquette/decorated polymer cluster expansion and its explicit KP/tree
  estimates; neither uses the Douglas compatibility layer nor the Dobrushin
  baseline.
- Completed the finite-edge center-selection package.  A center twist acts on
  path holonomy and every labelled Wilson Taylor word by its signed incidence
  phase; Haar change of variables therefore kills every word whose edge charge
  is nonzero modulo the order of the chosen nontrivial center phase.
- Defined finite cubical edge and plaquette charge chains, proved equivalence
  between coefficientwise Taylor screening and the chain equation
  `[C] + ∂(a-b) = 0` over `ZMod m`, and used it to show every nonzero Wilson
  Taylor monomial supplies a genuine center screening field.  This completes
  Milestone 15 without a representation-orthogonality black box.
- Proved the rectangle filling-order comparison by a discrete half-hyperplane
  flux argument.  Transverse plaquette contributions cancel, while the flux
  of the rectangle boundary through each of its `R * T` cells is one.  Thus
  every screening Taylor field has at least one distinct charged plaquette
  occurrence per cell:
  `rectangle_area_le_taylorOrder_of_taylorScreens`.
- Lifted that comparison directly to labelled Wilson words, action moments,
  and finite normalized expectations.  In particular,
  `iteratedDeriv_complexGibbsExpectation_wilsonRectangle_zero_of_lt_area`
  proves that every Taylor jet of order strictly below `R * T` vanishes.
- Passed the rectangular zero jets to infinite volume using the locally
  uniform completed-box limit produced by the cluster expansion.  Applied
  Mathlib's higher-order Schwarz lemma with the existing explicit one-root
  KP/tree closed-disk bound to prove
  `norm_analyticInfiniteVolumeWilsonRectangle_le_areaLaw` and its physical
  real-measure form `norm_integral_wilsonRectangle_le_areaLaw`:
  `K(r)^(2(R+T)) * exp(-log(r/|β|) * R*T)` for `|β| < r` inside the explicit
  strong-coupling disk.
- Completed Milestone 16.  The thermodynamic limit and quantitative prefactor
  come exclusively from the plaquette-polymer cluster expansion and its
  explicit KP/tree certificate; neither the Douglas compatibility layer nor
  the Dobrushin baseline enters the area-law proof.

### In progress

- None.  The first cleanup pass and Milestones 0--18 meet their stated exit
  criteria.

### Not started

- Milestones 19--20: infinite-volume reflection positivity and the optional
  Osterwalder--Schrader construction.

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
2026-08-10: lake -KmaxJobs=2 build
  YangMills.StrongCoupling.ClusterState
  YangMills.StrongCoupling.InfiniteVolumeMeasure
  YangMills.StrongCoupling.ExponentialClustering
  YangMills.StrongCoupling.ThermodynamicBoxes
  Success; the cluster-only Milestone 11--13 thermodynamic-limit backbone and
  centered exhaustion compile without placeholders.
2026-08-10: lake -KmaxJobs=2 build
  YangMills.Tests.Milestones11To13Foundations YangMills
  Success; 3,749 jobs. Centered-box cofinality, local-state algebra, measure
  representation, and exponential clustering have axiom footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-10: lake -KmaxJobs=2 build
  Success; 3,748 jobs after adding the cluster-only Milestone 11--13 backbone.
  Remaining messages are linter or deprecation warnings, primarily replayed
  from pinned dependencies; there are no build errors.
2026-08-10: lake build YangMills.StrongCoupling.ClusterState
  YangMills.StrongCoupling.InfiniteVolumeMeasure YangMills.Polymer.Mayer
  YangMills.Tests.Milestones11To13Foundations
  Success; 2,865 jobs. Cross-exhaustion state uniqueness, the
  Stone--Weierstrass measure-uniqueness theorem, disconnected Mayer
  cancellation, and one-/two-source scaling have footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-10: lake build
  Success; 3,749 jobs after adding the Mayer source formalism and completing
  the Milestone 12 density/measure-uniqueness step. There are no build errors.
2026-08-10: lake build YangMills.Polymer.FiniteMayer
  YangMills.StrongCoupling.ObservableRootPolymer
  YangMills.StrongCoupling.FiniteClusterExpansion
  Success. The normalized finite Mayer/log identity, weighted deletion and
  pinned KP bounds, explicit plaquette-disk instantiation, and augmented
  observable-root source constructions compile without placeholders.
2026-08-10: lake env lean YangMills/Tests/Milestones11To13Foundations.lean
  Success. The new finite Mayer, pinned, explicit plaquette, observable-root,
  and connected two-source coefficient declarations have footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-10: lake build
  Success; 3,753 jobs. Remaining output consists of linter and deprecation
  warnings, mostly replayed from pinned dependencies; there are no build
  errors.
2026-08-10: lake env lean YangMills/Tests/Milestones11To13Foundations.lean
  Success. The finite connected-component/Möbius regrouping theorem has axiom
  footprint `[propext, Classical.choice, Quot.sound]`.
2026-08-10: lake build
  Success; 3,755 jobs after adding the finite graph exponential-formula
  foundation. Remaining output consists of linter and deprecation warnings;
  there are no build errors.
2026-08-10: lake build YangMills.Polymer.Penrose
  YangMills.Polymer.Whitney YangMills.Polymer.KoteckyPreiss
  Success. The unconditional Whitney sign-reversing involution, sharp finite
  tree-graph inequality, exact termwise Mayer tree majorant, and standard KP
  rooted-tree fixed-point bound compile without placeholders.
2026-08-10: lake build YangMills.StrongCoupling.ObservableRootPolymer
  YangMills.Tests.Milestones11To13Foundations
  Success; 2,914 jobs. The one- and two-observable augmented-root pinned tree
  bounds compile, and the new Whitney/Mayer/KP declarations retain axiom
  footprint `[propext, Classical.choice, Quot.sound]`.
2026-08-10: lake build YangMills.Polymer.PowerSeriesLog
  YangMills.Polymer.LabelledTreeSummation
  YangMills.Tests.Milestones11To13Foundations
  Success; 2,995 jobs. Formal `expOf`/`logOf` inversion and exact
  labelled-set-to-symmetric-`MayerMultiIndex` KP forest summation compile;
  their regression declarations have footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-10: lake env lean YangMills/Polymer/RootedTreeDecomposition.lean
  Success.  Every component away from a tree root has a unique adjacent
  attachment vertex; the proof is placeholder-free and polymer-independent.
2026-08-10: lake env lean YangMills/Polymer/MayerPowerSeries.lean
  Success.  The canonical formal finite partition logarithm and its exact
  exponential identity compile without placeholders.
2026-08-10: lake build YangMills.Polymer.RootedTreeDecomposition
  YangMills.Polymer.LabelledTreeSummation YangMills.Polymer.PowerSeriesLog
  YangMills.Polymer.MayerPowerSeries
  YangMills.Tests.Milestones11To13Foundations
  Success; 2,997 jobs.  Root-deleted component histograms, exact activity
  factorization, pinned-to-unpinned symmetry and norm identities, the
  Mayer-to-KP child condition, and the formal logarithm regression
  declarations have footprint `[propext, Classical.choice, Quot.sound]`.
2026-08-10: lake build
  Success; 3,796 jobs after integrating the rooted Mayer weight decomposition
  and formal partition logarithm into the root import.  Remaining output is
  linter and dependency deprecation warnings; there are no build errors.
2026-08-10: lake build YangMills.Polymer.RootedForestPartition
  YangMills.Polymer.LabelledTreeSummation
  YangMills.StrongCoupling.ObservableRootPolymer
  YangMills.Tests.Milestones11To13Foundations
  Success; 2,999 jobs.  Lossless root deletion, exact component attachment
  products, the common-ambient unordered forest code, its weighted finite
  exponential bound, the fixed-multi-index pinned Mayer estimate, and the
  zero-source one-/two-observable KP certificates compile without
  placeholders.  Regression declarations retain footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-10: lake build
  Success; 3,798 jobs after integrating the finite rooted-forest orbit bridge
  and observable-root KP certificates into the root import.  Remaining output
  consists of linter and pinned-dependency deprecation warnings; there are no
  build errors.
2026-08-11: lake build YangMills.StrongCoupling.FiniteClusterExpansion
  YangMills.Tests.Milestones11To13Foundations
  Success; 3,015 jobs.  Exact two-root deletion, nonzero-root KP
  regularization, genuine pinned/tree and three-sector summability, and the
  concrete mixed connected partition identity compile without placeholders.
  Their regression declarations have footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-11: lake build
  Success; 3,814 jobs after integrating the two-root deletion and nonzero KP
  regularization into the root import.  Remaining output consists of linter
  and pinned-dependency deprecation warnings; there are no build errors.
2026-08-11: lake build YangMills.Polymer.BigradedSource
  YangMills.StrongCoupling.MarkedComponentExpansion
  YangMills.Tests.Milestones11To13Foundations
  Success; 3,016 jobs.  The bigraded source exponential and evaluated coefficient
  identities, exact decorated two-observable partition reindexing, explicit
  regularized KP certificate, genuine first/second/mixed-sector summability,
  mixed-root spanning witness, and exact truncated-correlation series compile
  without placeholders.  The checked declarations have axiom footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-11: lake build
  Success; 3,815 jobs after integrating the bigraded source and decorated bivariate
  cluster expansion into the root import.  Remaining output consists of
  linter and pinned-dependency deprecation warnings; there are no build
  errors.
2026-08-11: lake build YangMills.StrongCoupling.SpatialClusterExpansion
  YangMills.Tests.Milestones11To13Foundations
  Success; 3,017 jobs.  The explicit greater-than-one cardinality tilt,
  tilted bulk and full decorated nonzero-source KP certificates, pinned-tree
  summability, and exponentially weighted mixed-sector summability compile
  without placeholders.  The checked declarations have axiom footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-11: lake build
  Success; 3,816 jobs after integrating the spatially weighted cluster
  expansion into the root import.  Remaining output consists of linter and
  pinned-dependency deprecation warnings; there are no build errors.
2026-08-11: lake build YangMills.StrongCoupling.SpatialClusterGeometry
  YangMills.Tests.Milestones11To13Foundations
  Success; 3,018 jobs.  Connected spatial carriers for all decorated polymer
  types, incompatibility linkage, Mayer-walk carrier induction, and the final
  mixed-term separation-versus-cardinality theorem compile without
  placeholders.  The checked declaration has axiom footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-11: lake build
  Success; 3,817 jobs after integrating the spatial support geometry into the
  root import.  Remaining output consists of linter and pinned-dependency
  deprecation warnings; there are no build errors.
2026-08-11: lake build YangMills.StrongCoupling.SpatialClusterGeometry
  YangMills.Tests.Milestones11To13Foundations
  Success; 3,018 jobs.  Source-only pinning, quantitative certified
  pinned-tree summation, the explicit volume-free tilted decoration budget,
  and the resulting uniform finite-volume covariance estimate compile
  without placeholders.  The checked declarations have axiom footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-11: lake build
  Success; 3,817 jobs after integrating the uniform pinned/tree covariance
  bound.  Remaining output consists of linter and pinned-dependency
  deprecation warnings; there are no build errors.
2026-08-11: lake build YangMills.StrongCoupling.ClusterBoundaryExpansion
  YangMills.StrongCoupling.CenteredBoundaryExpansion
  YangMills.StrongCoupling.CenteredClusterGeometry
  YangMills.Tests.Milestones11To13Foundations
  Success.  Symmetric Mayer degree normalization across exterior instances,
  the absolutely summable one-root boundary tail, centered finite-neighborhood
  exhaustion, arbitrary-boundary convergence, and the concrete two-root
  exponential-clustering certificate compile without placeholders.
2026-08-11: lake build
  Success; 3,820 jobs after integrating the one-root centered boundary tail
  and concrete centered clustering certificate into the root import.
  Remaining output consists of linter and pinned-dependency deprecation
  warnings; there are no build errors.
2026-08-12: lake build YangMills.StrongCoupling.CenteredInfiniteVolume
  Success.  The generic and centered finite-product Gibbs towers, concrete
  cross-volume Cauchy theorem, arbitrary-boundary independence, gauge and
  translation invariance, regular infinite-volume probability, and explicit
  positive-mass clustering theorem compile at the lattice strong-coupling
  radius without placeholders.
2026-08-12: lake env lean YangMills/Tests/Milestones11To13Foundations.lean
  Success.  The concrete Milestone 11--13 exit declarations, including
  cofinal-subsequence convergence, have axiom footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-12: lake build
  Success; 3,824 jobs after exporting the completed Milestone 11--13 theorem
  family from the package root.  Remaining output consists of linter and
  pinned-dependency deprecation warnings; there are no build errors.
2026-08-12: lake build YangMills.StrongCoupling.ThermodynamicAnalyticity
  YangMills.StrongCoupling.ThermodynamicPressure
  Success.  The locally uniform analytic local-state limit, explicit decorated
  KP closed-disk bound, real-axis and boundary-independence identifications,
  anchored pressure, boundary/volume estimate, and normalized finite-log
  pressure limit compile without placeholders.
2026-08-12: lake env lean YangMills/Tests/Milestone14.lean
  Success.  The Milestone 14 exit declarations have axiom footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-12: lake build
  Success; 3,848 jobs after exporting the completed Milestone 14 theorem
  family from the package root.  Remaining output consists of linter and
  pinned-dependency deprecation warnings; there are no build errors.
2026-08-13: lake build YangMills.Tests.Milestone16
  Success; 3,083 jobs.  The rectangular filling-order comparison, finite and
  infinite zero-jet theorems, analytic area-power estimate, and explicit
  rectangle area law have axiom footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-13: lake build
  Success; 3,862 jobs after exporting the completed Milestone 16 theorem
  family from the package root.  Remaining output consists of linter and
  pinned-dependency deprecation warnings; there are no build errors.
2026-08-13: lake build YangMills.Tests.Milestones11To13Foundations
  Success; 3,032 jobs after adding literal pushforward and
  `MeasurePreserving` gauge invariance for the infinite-volume Yang--Mills
  probability.  Both declarations have axiom footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-13: lake build
  Success; 3,862 jobs after exporting the pushforward gauge-invariance API.
  Remaining output consists of linter and pinned-dependency deprecation
  warnings; there are no build errors.
2026-08-13: lake env lean YangMills/Tests/Milestone17.lean
  Success.  Integer/site reflection geometry, the explicit finite product-Haar
  variable partition, Wilson action decomposition, full-to-factorized Gibbs
  pairing, weighted square-modulus positivity, and reflection-inner-product
  Cauchy--Schwarz compile without placeholders.  The principal declarations
  have axiom footprint `[propext, Classical.choice, Quot.sound]` (the purely
  geometric declarations need no `Classical.choice`).
2026-08-13: lake build
  Success; 3,864 jobs after exporting the completed Milestone 17 site
  reflection-positivity and reflection-inner-product API from the package
  root.  Remaining output consists of linter and pinned-dependency
  deprecation warnings; there are no build errors.
2026-08-13: lake build YangMills.Gauge.SiteReflectionPositivity
  Success; 2,682 jobs.  A clean rebuild exposed and fixed the missing
  declaration-order variables on `reflectedVariableEquiv`; the reflection
  positivity module now elaborates from source rather than relying on a stale
  artifact.
2026-08-13: lake build
  Success; 3,089 jobs with the smaller project-native public root.  The root
  still exports the finite gauge layer, site reflection positivity,
  thermodynamic pressure, and Wilson area law, together with their transitive
  project-native dependencies.
2026-08-13: lake build +YangMills.Regression
  Success; 3,879 jobs.  All milestone axiom checks, audits, the pinned Douglas
  periodic-torus baseline, and the older finite-box Dobrushin comparison route
  compile through the opt-in comprehensive root.
2026-08-13: lake build +YangMills.Tests.ReviewerSmoke
  Success; 3,089 jobs.  The critical-review normalization, non-vacuity,
  invariance, reflection, and degenerate area-law corollaries compile through
  the public API without placeholders.
2026-08-13: lake build +YangMills.Regression
  Success; 3,880 jobs after adding the critical-review smoke suite to the
  opt-in comprehensive regression root.  There are no build errors.
2026-08-13: lake build
  Success; 3,089 jobs after the reviewer suite and documentation update.  The
  public project-native root remains green.
2026-08-13: lake env lean --stdin (reviewer theorem axiom audit)
  Success.  Representative empty-volume, direct Mayer-log normalization,
  infinite-volume gauge, reflection-normalization, and zero-area corollaries
  have the expected footprint `[propext, Classical.choice, Quot.sound]`.
2026-08-13: lake build +YangMills.Gauge.LinkReflectionPositivity
  Success; 2,697 jobs.  Crossing-forest product-Haar gauge fixing, the exact
  oriented matrix-coefficient trace kernel, normally convergent labelled
  Taylor/Fubini Gram expansion, half-integer reflection positivity at
  nonnegative coupling, and unnormalized/normalized Cauchy--Schwarz compile
  without placeholders.
2026-08-13: lake build +YangMills.Tests.Milestone18
  Success; 2,698 jobs.  Public-shape examples for the gauge-invariant
  positive subspace, degree-zero Taylor word, exact Taylor pairing,
  positivity, and both Cauchy--Schwarz forms compile.  The five principal
  declarations have axiom footprint `[propext, Classical.choice, Quot.sound]`.
2026-08-13: lake build
  Success; 3,090 jobs after exporting the completed Milestone 18 theorem
  family from the project-native public root.  Remaining output consists of
  linter and pinned-dependency warnings; there are no build errors.
2026-08-13: lake build +YangMills.Regression
  Success; 3,882 jobs.  The full milestone suite, reviewer smoke tests,
  project-native theorem graph, Douglas baseline audits, and optional older
  Dobrushin comparison route remain green after Milestone 18.
2026-08-13: lake build +YangMills.Regression
  Success; 3,882 jobs after the first warning-cleanup pass.  Project-owned
  warning messages fell from 715 to 511 without disabling linters.  The
  reflection-positivity chain, `Polymer.Augmented`,
  `StrongCoupling.ObservableRootPolymer`, and the newly touched portions of
  `StrongCoupling.MarkedComponentExpansion` compile from source; there are no
  errors, `sorry`, or admitted obligations.
2026-08-13: lake build
  Success; 3,090 jobs after the same cleanup pass.  The project-native public
  root remains green and emits 461 project-owned linter messages, concentrated
  primarily in older labelled-tree, Whitney, countable-Mayer, spatial-cluster,
  and thermodynamic modules queued for later cleanup.
2026-08-13: lake build +YangMills.Tests.DiagonalReflection
  Success; 3,016 jobs.  Affine diagonal geometry, the full one-sided local
  algebra without a gauge-invariance premise, exact Taylor/Fubini equality,
  finite positivity and normalized Cauchy--Schwarz, closed local-limit
  transfer, and the centered KP specialization compile without placeholders.
  The eight audited headline declarations have axiom footprint contained in
  `[propext, Classical.choice, Quot.sound]`.
2026-08-13: lake build
  Success; 3,096 jobs after exporting finite and infinite-volume diagonal
  reflection positivity from the project-native public root.  A clean source
  rebuild also exposed and fixed stale qualification/reduction assumptions in
  the existing all-plane coordinate-reflection translation proofs.
2026-08-13: lake build +YangMills.Regression
  Success; 3,890 jobs.  The complete milestone suite, reviewer smoke tests,
  project-native theorem graph, Douglas audits, and optional Dobrushin route
  remain green with the diagonal reflection development enabled.
2026-08-13: lake build
  Success; 3,098 jobs after exporting the concrete site-reflection bridge and
  unconditional strong-coupling site positivity/Cauchy--Schwarz theorems.
  The newly added source modules compile without their own linter warnings.
2026-08-13: lake build +YangMills.Regression
  Success; 3,893 jobs.  The new concrete site-reflection applications and
  seven headline axiom audits pass together with all existing milestone,
  Douglas-baseline, Dobrushin-comparison, and reviewer regressions.
2026-08-13: lake build +YangMills.Tests.ConcreteLinkReflection
  Success; 3,018 jobs.  The concrete link-symmetric geometry, one-root KP
  local limit, all-plane positivity and Cauchy--Schwarz, and a constant
  gauge-invariant observable application compile.  All seven audited
  headline declarations have axiom footprint
  `[propext, Classical.choice, Quot.sound]`.
2026-08-13: lake build +YangMills.Tests.DiagonalReflection
  Success; 3,024 jobs.  The suite now includes the concrete centered-box
  symmetry and unconditional all-plane strong-coupling positivity and
  Cauchy--Schwarz applications.  All eleven audited declarations have the
  standard axiom footprint.
2026-08-13: lake build
  Success; 3,102 jobs after exporting the concrete link and diagonal theorem
  families.  A clean combined-root build exposed and fixed colliding
  automatically generated names for local plaquette decidable-equality
  instances in the three finite bridges.
2026-08-13: lake build +YangMills.Regression
  Success; 3,898 jobs.  The completed site, link, and diagonal finite bridges,
  cluster-expansion infinite-volume transfers, concrete reviewer examples,
  axiom audits, all earlier milestones, and the optional Douglas/Dobrushin
  regression routes compile together without errors.
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
