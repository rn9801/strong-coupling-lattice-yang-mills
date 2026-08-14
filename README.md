# Strong-Coupling Lattice Yang--Mills in Lean

This repository formalizes constructive lattice Yang--Mills theory at strong
coupling in Lean 4.  The project works on the infinite cubic lattice
`ℤ^d`, builds arbitrary finite-volume Gibbs specifications with frozen exterior
fields, and derives the thermodynamic results from a convergent plaquette
polymer/Mayer expansion.

Milestones 0--19 are complete.  Integer/site, half-integer/link, and affine
diagonal reflection positivity are connected from concrete cubic Gibbs
specifications to the cluster-constructed infinite-volume measure, together
with the corresponding reflected Cauchy--Schwarz inequalities.
The principal proved results are:

- finite-volume gauge invariance and finite-volume DLR consistency;
- an exact plaquette-polymer representation of the partition function;
- the symmetric Mayer exponential/logarithm identity, a genuine
  Kotecký--Preiss (KP) certificate, weighted pinned-tree estimates, absolute
  convergence, and a volume-independent zero-free disk;
- a boundary-independent centered thermodynamic limit represented by a unique
  regular Borel probability measure, together with gauge and translation
  invariance;
- exponential clustering for arbitrary bounded local observables;
- analytic infinite-volume local expectations and analytic thermodynamic
  pressure throughout the explicit strong-coupling disk;
- center selection, vanishing Wilson-loop Taylor coefficients below the
  filling area, and a strong-coupling rectangle area law;
- reflection positivity and reflection Cauchy--Schwarz for concrete centered
  finite Gibbs measures and for the strong-coupling infinite-volume measure
  at every integer coordinate plane, with no gauge-invariance assumption on
  positive-side observables;
- reflection positivity and reflection Cauchy--Schwarz for concrete completed
  link-symmetric Gibbs boxes and for the infinite-volume measure at every
  half-integer coordinate plane when `β ≥ 0` lies in the strong-coupling
  disk; positive-side observables are gauge invariant because the proof fixes
  all links crossing the plane to the identity;
- reflection positivity and Cauchy--Schwarz for concrete centered Gibbs boxes
  and for the infinite-volume measure at every diagonal plane
  `xτ - xσ = k` when `β ≥ 0` lies in the strong-coupling disk, proved by
  conditioning on the links in the plane and applying the explicit
  cut-plaquette Taylor/Fubini Gram expansion; no gauge-invariance assumption
  is made on observables;
- closed-limit theorems transferring eventual finite-volume site, link, and
  diagonal reflection positivity and Cauchy--Schwarz to the
  cluster-constructed infinite-volume measure, followed by translation to
  all parallel affine planes.

The thermodynamic limit, clustering, analyticity, pressure, and area-law
proofs use the cluster expansion and its explicit KP/tree bounds.  They do not
use the separate periodic-torus Dobrushin regression theorem.

The optional next phase is Osterwalder--Schrader reconstruction and a genuine
Hamiltonian spectral-gap theorem.  See [`STATUS.md`](STATUS.md) for the exact
declaration-level progress and [`docs/ROADMAP.md`](docs/ROADMAP.md) for the
remaining optional milestone.

## Mathematical model and conventions

### Cubic lattice, edges, and paths

A lattice site in dimension `d` is

```text
Site d = Fin d → ℤ.
```

`PositiveEdge d` stores a source site and a positive coordinate direction.
Only these canonical positive edges carry independent gauge variables.
`SignedEdge d` adds an orientation; evaluating a backward signed edge reads
the corresponding stored positive edge and takes its group inverse.  This
avoids storing two variables for the same unoriented edge.

Paths are endpoint-indexed sequences of signed edges.  If
`A : Configuration d G`, their holonomy is the ordered product

```text
holonomy A p = A(e₁) A(e₂) ⋯ A(eₙ).
```

The formalization includes concatenation, reversal, translation, finite edge
support, coordinate plaquettes, and rectangular boundary loops.  A
`Plaquette d` is based at a site and has two distinct ordered coordinate
directions; its boundary is the corresponding closed four-edge path.

Principal files:
[`Lattice/Cubic.lean`](YangMills/Lattice/Cubic.lean),
[`Lattice/Path.lean`](YangMills/Lattice/Path.lean), and
[`Lattice/Plaquette.lean`](YangMills/Lattice/Plaquette.lean).

### Gauge fields and gauge transformations

For a group `G`, an infinite-volume gauge configuration and a site gauge
transformation are

```text
Configuration d G       = PositiveEdge d → G
GaugeTransformation d G = Site d → G.
```

The gauge action on a stored edge `e : x → y` is

```text
(g • A)(e) = g(x) A(e) g(y)⁻¹.
```

Path holonomy is endpoint covariant:

```text
Hol(g • A, p : x ⟶ y) = g(x) Hol(A,p) g(y)⁻¹.
```

Consequently loop holonomy transforms by conjugation.  Continuous class
functions of loop holonomy are therefore gauge-invariant observables.
`LocalObservable d G` bundles a continuous complex function on the full
configuration space with an explicit finite edge support; the support is not
required to be minimal.

Principal files:
[`Gauge/Configuration.lean`](YangMills/Gauge/Configuration.lean),
[`Gauge/Holonomy.lean`](YangMills/Gauge/Holonomy.lean), and
[`Gauge/Observable.lean`](YangMills/Gauge/Observable.lean).

### Haar probability and finite specifications

`GaugeHaarProbability G` is a chosen normalized Haar probability measure with
left, right, two-sided, and inversion invariance.  For compact Borel
topological groups it is constructed from Mathlib's normalized Haar measure.
Finite collections of edge variables carry independent product Haar
probability.

A `FiniteSpecification d G` consists of:

- a finite set of dynamic positive edges to integrate;
- a finite set of active plaquettes contributing to the action;
- a full exterior configuration supplying every non-dynamic edge value.

`FiniteSpecification.evaluate` glues a dynamic field to the frozen exterior
field.  This representation supports arbitrary finite shapes and boundary
conditions, not only periodic boxes.

Principal files:
[`Gauge/HaarProbability.lean`](YangMills/Gauge/HaarProbability.lean),
[`Gauge/ProductHaar.lean`](YangMills/Gauge/ProductHaar.lean), and
[`Gauge/Specification.lean`](YangMills/Gauge/Specification.lean).

### Yang--Mills action, partition function, and Gibbs measure

A `RealPlaquettePotential G` is a bounded continuous function
`Φ : G → ℝ` invariant under conjugation and inversion.  For a finite
specification `Λ`, its action is

```text
SΛ,Φ(U) = ∑ p ∈ Λ.activePlaquettes, Φ(Hol(Λ.evaluate U, ∂p)).
```

The project uses the Boltzmann sign convention

```text
wβ(U) = exp(β SΛ,Φ(U)),
```

so strong coupling means small `|β|` around the independent-Haar point
`β = 0`.  The real partition function and Gibbs probability are

```text
ZΛ,Φ(β) = ∫ exp(β SΛ,Φ(U)) dHaarΛ(U),

dμΛ,Φ,β(U) = ZΛ,Φ(β)⁻¹ exp(β SΛ,Φ(U)) dHaarΛ(U).
```

The real partition function is strictly positive.  A separate complex API
defines the entire function

```text
ZΛ,Φ(z) = ∫ exp(z SΛ,Φ(U)) dHaarΛ(U),    z ∈ ℂ.
```

Keeping real probability measures separate from complex analytic functions
prevents accidental use of a complex density as a probability law.

Principal files:
[`Gauge/FiniteVolume.lean`](YangMills/Gauge/FiniteVolume.lean) and
[`Gauge/ComplexFiniteVolume.lean`](YangMills/Gauge/ComplexFiniteVolume.lean).

### Wilson action and Wilson loops

`ContinuousUnitaryRepData G n` packages a positive-dimensional continuous
unitary representation `ρ : G → U(n)`.  Its normalized character is

```text
χρ(g) = Tr(ρ(g)) / n,
```

and satisfies `‖χρ(g)‖ ≤ 1`.  The Wilson plaquette potential and the Wilson
observable of a closed path `C` are

```text
Φρ(g) = Re χρ(g),
Wρ(C,A) = χρ(Hol(A,C)).
```

Both are gauge invariant.  `CenterChargeData` records a central element that
acts in the representation by a nontrivial scalar phase;
`FiniteCenterChargeData` additionally records its finite order.  This is the
precise hypothesis used by the center-selection and area-law arguments.

Principal files:
[`Wilson/Representation.lean`](YangMills/Wilson/Representation.lean),
[`Wilson/Loop.lean`](YangMills/Wilson/Loop.lean), and
[`Wilson/CenterSelection.lean`](YangMills/Wilson/CenterSelection.lean).

## Polymer and cluster expansion

### Abstract hard-core gas

`FinitePolymerModel P` consists of a finite polymer type, a symmetric
reflexive incompatibility relation, and complex activities `z(γ)`.  A family
is compatible when no two distinct members are incompatible, and its
partition function is

```text
Zpoly = ∑ Γ compatible, ∏ γ ∈ Γ, z(γ).
```

The generic `Polymer/` directory is independent of the Yang--Mills model.

### Plaquette polymers

Expanding each plaquette factor as

```text
exp(β Φ(Holp)) = 1 + (exp(β Φ(Holp)) - 1)
```

gives an exact sum over subsets of active plaquettes.  Two plaquettes are
adjacent when their factors share a dynamic edge.  A `PlaquettePolymer Λ` is
a nonempty connected active-plaquette subset.  Two such polymers are
incompatible when they overlap or have adjacent plaquettes.  The activity of
a polymer is the Haar integral of the product of its plaquette perturbations.

Regrouping every plaquette subset into its connected components proves the
exact identity

```text
complexPartitionFunction Λ Φ β
  = (plaquettePolymerModel Λ Φ β).partitionFunction.
```

### Mayer clusters

A `MayerMultiIndex P = P →₀ ℕ` records a finite multiset of polymers.  Each
occurrence is a separate vertex.  The associated incompatibility graph joins
distinct occurrences whose polymers are incompatible.  If `X` is a
multi-index, the Ursell coefficient and symmetry-normalized cluster term are

```text
φᵀ(X) = ∑ H connected spanning subgraph, (-1)^|E(H)|,

c(X) = φᵀ(X) / (∏γ X(γ)!) · ∏γ z(γ)^X(γ).
```

Disconnected incompatibility graphs have zero Ursell coefficient.  The
formal and evaluated Mayer exponential theorems show that the compatible
family partition function is the exponential of the connected cluster sum.
The resulting logarithm is the branch normalized by `Z(0)=1`; it is not
identified with the global principal `Complex.log`.

### KP certificate and explicit disk

The standard finite KP hypothesis formalized by
`KoteckyPreissCertificate` is

```text
∀ γ,
  ∑ δ incompatible with γ, ‖z(δ)‖ exp(a(δ)) ≤ a(γ),
```

for a nonnegative weight `a`.  The plaquette gas uses

```text
a(γ) = |γ| log 2.
```

Write

```text
perturbationMajorant Φ β = exp(‖β‖ Φ.bound) - 1,

dobrushinThreshold(D,C)
  = min(1/8, 1/(16(C+1)), log(2)/(16(D+1))),

latticeStrongCouplingRadius(d, Φ.bound)
  = log(1 + dobrushinThreshold(16d, 2^(16d))) / (Φ.bound + 1).
```

Inside the disk
`‖β‖ < latticeStrongCouplingRadius d Φ.bound`, lattice-animal counting
proves the KP certificate uniformly in the finite volume and exterior field.
The formalization derives:

- the sharp Whitney/Penrose tree-graph estimate;
- absolute summability of the symmetry-normalized Mayer series;
- multiplicity-pinned and weighted rooted-tree bounds;
- `exp (symmetricMayerSum) = ZΛ,Φ(β)`;
- volume-independent zero-freeness of the finite partition function.

Observable insertions are encoded by exclusive decorated root polymers.
One-root clusters give expectations and boundary comparison; a bigraded
two-root gas gives truncated correlations.  A spatial tilt charges the total
plaquette support, so every surviving mixed cluster pays at least the distance
between the two observable supports.

Principal files:
[`Polymer/Mayer.lean`](YangMills/Polymer/Mayer.lean),
[`Polymer/KoteckyPreiss.lean`](YangMills/Polymer/KoteckyPreiss.lean),
[`StrongCoupling/PlaquetteExpansion.lean`](YangMills/StrongCoupling/PlaquetteExpansion.lean),
[`StrongCoupling/PlaquettePolymer.lean`](YangMills/StrongCoupling/PlaquettePolymer.lean), and
[`StrongCoupling/FiniteClusterExpansion.lean`](YangMills/StrongCoupling/FiniteClusterExpansion.lean).

## Thermodynamic state, pressure, and reflections

### Infinite-volume local state and measure

Centered boxes form the chosen cofinal exhaustion.  The one-root cluster tail
proves that every bounded local observable has a Cauchy sequence of
finite-volume expectations, uniformly over arbitrary centered exterior
fields.  Compactness of the full configuration space supplies a probability
measure representing the limiting local state, and density of local
continuous functions makes that representing measure unique.

The resulting `centeredInfiniteVolumeMeasure` is independent of the exterior
sequence, invariant under every site gauge transformation, translation
invariant, regular, and exponentially clustering.  More precisely, for local
observables `F,H`, the code proves an explicit estimate of the form

```text
‖μ(FH) - μ(F) μ(H)‖
  ≤ A(F,H,Φ,β) exp(-m(Φ,β) · dist(supp F, supp H)),
```

where `m(Φ,β)>0` follows from the strict KP tilt.

The current uniqueness theorem is deliberately scoped: it proves uniqueness
of the probability measure representing this cluster-expanded local state and
independence of centered cofinal boundary sequences.  It does **not** yet
assert uniqueness among all possible infinite-volume DLR measures.

Principal files:
[`StrongCoupling/CenteredInfiniteVolume.lean`](YangMills/StrongCoupling/CenteredInfiniteVolume.lean) and
[`StrongCoupling/ExponentialClustering.lean`](YangMills/StrongCoupling/ExponentialClustering.lean).

### Pressure and free energy

The countable full-lattice polymer model defines a translation-invariant
rooted cluster series.  `anchoredPressurePerSite` sums over the ordered
plaquette orientations at the origin.  `anchoredPressure` divides by the
number of those orientations and is the pressure per ordered plaquette.

Exact finite connected logarithms, normalized either per lattice site or per
ordered plaquette, converge to these anchored quantities.  The finite sums
exponentiate to the exact finite partition functions, fixing the logarithm
branch at `β=0`.  The limiting pressure is analytic throughout the explicit
strong-coupling disk.

In statistical-mechanics terminology a free-energy density can be obtained
from pressure after choosing a sign and temperature normalization.  The code
currently formalizes pressure directly; it does not introduce a separate
Lean definition named `freeEnergy`.

Principal files:
[`StrongCoupling/ThermodynamicCluster.lean`](YangMills/StrongCoupling/ThermodynamicCluster.lean) and
[`StrongCoupling/ThermodynamicPressure.lean`](YangMills/StrongCoupling/ThermodynamicPressure.lean).

### Integer-hyperplane reflection and positive algebra

For a coordinate `τ` and integer `k`, site reflection is

```text
(θx)τ = 2k - xτ,
(θx)i = xi  for i ≠ τ.
```

The construction is extended to signed directions, signed and stored edges,
paths, plaquettes, configurations, and holonomy.  Edges perpendicular to the
plane acquire the inversion dictated by the stored-positive-edge convention.

After a finite reflected label set is split into plane variables `U₀` and two
copies `U₋,U₊` of the strict half-volume variables, the positive algebra is

```text
PositiveObservable G P O = C(PlaneConfiguration G O × SideConfiguration G P, ℂ).
```

It is the full continuous algebra on one side; observables are **not** assumed
gauge invariant.  The anti-linear reflection of a full observable is

```text
(ΘF)(U₀,U₋,U₊) = conj(F(U₀,U₊,U₋)).
```

For an action decomposition

```text
S(U₀,U₋,U₊) = S₊(U₀,U₋) + S₀(U₀) + S₊(U₀,U₊),
```

product-Haar Fubini factorization identifies the Gibbs pairing with an
ordinary complex `L²` inner product of weighted half-volume amplitudes.  This
proves reflection positivity for every real `β`, and the normalized pairing
satisfies Cauchy--Schwarz.

`FiniteSpecification.SiteSymmetric` records invariance of the dynamic edges,
active plaquettes, and exterior field.  The concrete bridge partitions its
edge variables and plaquettes into plane and reflected strict-side pieces,
proves product-Haar preservation of the resulting label equivalence, and
transports its action and positive-side local observables to the labelled
normal form.  Consequently every such finite specification satisfies
reflection positivity and Cauchy--Schwarz.  Centered boxes with identity
exterior data satisfy this symmetry at the origin; the KP local-expectation
limit, boundary independence, and translation invariance then prove both
statements for the constructed infinite-volume measure at every integer
coordinate plane throughout the explicit strong-coupling disk.

### Half-integer/link-hyperplane reflection

Link reflection through `xτ = k + 1/2` exchanges the two open half-lattices
and inverts the stored perpendicular edges crossing the plane.  Its positive
algebra consists of local observables supported on the positive side and,
unlike the site and diagonal cases, requires gauge invariance.

The concrete finite bridge applies a one-sided lattice gauge transformation
on the first positive layer.  It sends every crossing edge to the identity,
preserves product Haar measure by coordinatewise left/right multiplication,
and leaves the negative half unchanged.  The cut-plaquette Wilson factors can
then be Taylor-expanded into matrix coefficients; Fubini identifies every
coefficient with a finite Gram sum.  This proves normalized finite-volume
positivity and reflected Cauchy--Schwarz at `β ≥ 0`.

The completed link-symmetric specification makes every edge read by an active
plaquette dynamic.  The one-root KP boundary estimate proves that its local
expectations and those of ordinary centered boxes have the same limit.
Consequently the cluster-constructed state is link-reflection positive and
satisfies reflected Cauchy--Schwarz at every half-integer coordinate plane
throughout the nonnegative part of the explicit strong-coupling disk.

Principal files:
[`Gauge/LinkReflectionBridge.lean`](YangMills/Gauge/LinkReflectionBridge.lean)
and
[`StrongCoupling/ConcreteLinkReflectionPositivity.lean`](YangMills/StrongCoupling/ConcreteLinkReflectionPositivity.lean).

### Diagonal-hyperplane reflection

For distinct coordinates `τ` and `σ`, reflection through
`xτ - xσ = k` is the involution

```text
(xτ,xσ) ↦ (xσ+k,xτ-k).
```

It permutes stored positive edges without inversion.  The finite labelled
normal form consists of common plane variables `U₀` and two strict-side
fields `U₋,U₊`.  At fixed `U₀`, every cut-plaquette term has the Wilson
form

```text
Φ(hq(U₀,U₊) * hq(U₀,U₋)⁻¹).
```

The exponential of these terms is expanded in its normally convergent Taylor
series.  Expanding the unitary-representation traces into matrix coefficients
and applying product-Haar Fubini identifies each coefficient with a finite
Gram sum.  The remaining plane integral has a positive real weight.  There
are no perpendicular crossing-link variables to gauge-fix, so the positive
algebra is the full continuous one-sided algebra, without a gauge-invariance
premise.  Both the unnormalized and normalized pairings satisfy
Cauchy--Schwarz.

The concrete bridge partitions a diagonally symmetric cubic specification
into fixed-plane and paired side labels and transports its Haar integral,
action, and supported observables to this normal form.  Centered boxes with
identity exterior data have the required symmetry.  Their finite positivity
and Cauchy--Schwarz inequalities pass through the KP local-expectation limit,
boundary independence, and translation invariance to every affine diagonal
plane in infinite volume.

Principal files:
[`Gauge/DiagonalReflection.lean`](YangMills/Gauge/DiagonalReflection.lean),
[`Gauge/DiagonalReflectionPositivity.lean`](YangMills/Gauge/DiagonalReflectionPositivity.lean),
[`Gauge/DiagonalReflectionBridge.lean`](YangMills/Gauge/DiagonalReflectionBridge.lean),
and
[`StrongCoupling/ConcreteDiagonalReflectionPositivity.lean`](YangMills/StrongCoupling/ConcreteDiagonalReflectionPositivity.lean).

### Infinite-volume reflection limit

`LocalObservable.siteTheta`, `LocalObservable.linkTheta`, and
`LocalObservable.diagonalTheta` implement the three anti-linear reflections
on the full infinite-lattice local algebra.  The predicates
`SiteReflectionPositive`, `LinkReflectionPositive`, and
`DiagonalReflectionPositive` state positivity directly for a Borel measure;
only the link predicate retains full local gauge invariance.

The corresponding `*_of_localExpectation_tendsto` theorems prove that
positivity and reflection Cauchy--Schwarz are closed under convergence of
every local expectation.  Their centered specializations use
`tendsto_centered_localExpectation_infiniteVolume`, hence the passage to the
infinite-volume measure is based on the KP cluster expansion.  Translation
invariance then gives all parallel integer, half-integer, and affine diagonal
planes.

All three cases are connected to concrete cubic Gibbs integrals.  Site and
diagonal reflection use identity-exterior centered boxes.  Link reflection
uses completed boxes symmetric about `1/2`; the finite-specification Gibbs
tower and one-root KP boundary estimate identify their local limit with the
centered state.  Thus none of the infinite-volume reflection theorems relies
on the Douglas/Dobrushin route.

Principal files:
[`Gauge/InfiniteReflection.lean`](YangMills/Gauge/InfiniteReflection.lean),
[`Gauge/SiteReflectionBridge.lean`](YangMills/Gauge/SiteReflectionBridge.lean),
[`StrongCoupling/SymmetricReflectionBoxes.lean`](YangMills/StrongCoupling/SymmetricReflectionBoxes.lean),
and
[`StrongCoupling/InfiniteVolumeReflectionPositivity.lean`](YangMills/StrongCoupling/InfiniteVolumeReflectionPositivity.lean),
with the concrete specialization in
[`StrongCoupling/ConcreteSiteReflectionPositivity.lean`](YangMills/StrongCoupling/ConcreteSiteReflectionPositivity.lean)
and
[`StrongCoupling/ConcreteLinkReflectionPositivity.lean`](YangMills/StrongCoupling/ConcreteLinkReflectionPositivity.lean).

The diagonal extension is in
[`StrongCoupling/InfiniteVolumeDiagonalReflectionPositivity.lean`](YangMills/StrongCoupling/InfiniteVolumeDiagonalReflectionPositivity.lean)
and
[`StrongCoupling/ConcreteDiagonalReflectionPositivity.lean`](YangMills/StrongCoupling/ConcreteDiagonalReflectionPositivity.lean).

Principal files:
[`Gauge/SiteReflection.lean`](YangMills/Gauge/SiteReflection.lean) and
[`Gauge/SiteReflectionPositivity.lean`](YangMills/Gauge/SiteReflectionPositivity.lean).

## Main theorem index

| Result | Representative declarations |
|---|---|
| Holonomy covariance and Wilson gauge invariance | `holonomy_gaugeTransform`, `ContinuousUnitaryRepData.wilsonLoop_gaugeInvariant` |
| Finite-volume gauge invariance | `FiniteVolume.action_gaugeInvariant`, `FiniteVolume.gibbsExpectation_gaugeTransform`, `FiniteVolume.integral_gibbsMeasure_gaugeTransformExterior_complex` |
| Finite-volume probability and DLR | `FiniteVolume.partitionFunction_pos`, `gibbsMeasure_isGibbs_box` |
| Entire finite partition function | `FiniteVolume.complexPartitionFunction_entire` |
| Exact plaquette-polymer representation | `complexPartitionFunction_eq_polymerPartition` |
| Genuine KP and pinned/tree bounds | `plaquettePolymerModel_koteckyPreiss_of_norm_lt_latticeRadius`, `summable_plaquetteNormMayerDegreeSum_succ`, `plaquetteWeightedPinnedTreeOrbitBound` |
| Mayer logarithm and zero-free disk | `exp_plaquetteSymmetricMayerSum_eq_complexPartitionFunction`, `complexPartitionFunction_ne_zero_of_norm_lt_latticeRadius_koteckyPreiss` |
| Exact observable cluster series | `complexGibbsExpectation_eq_tsum_connectedDecoratedRoot`, `complexGibbsTruncatedCorrelation_eq_tsum_bivariateDecoratedMixed` |
| Boundary-independent thermodynamic limit | `tendsto_centered_localExpectation_infiniteVolume`, `centeredInfiniteVolumeMeasure_boundary_independent` |
| Uniqueness of the representing probability | `centeredInfiniteVolumeMeasure_unique` |
| Infinite-volume symmetries | `centeredInfiniteVolumeMeasure_map_gaugeTransform`, `centeredInfiniteVolume_integral_translatePullback` |
| Concrete reflection-positive local limits | `centeredInfiniteVolume_siteReflectionPositive`, `centeredInfiniteVolume_linkReflectionPositive`, `centeredInfiniteVolume_diagonalReflectionPositive` |
| Infinite-volume reflected Cauchy--Schwarz | `centeredInfiniteVolume_siteReflectionCauchySchwarz`, `centeredInfiniteVolume_linkReflectionCauchySchwarz`, `centeredInfiniteVolume_diagonalReflectionCauchySchwarz` |
| Exponential clustering | `centeredInfiniteVolume_exponential_clustering`, `centeredInfiniteVolume_clusteringMass_pos` |
| Analytic local expectations | `analyticOnNhd_analyticInfiniteVolumeLocalExpectation`, `analyticInfiniteVolumeLocalExpectation_boundary_independent` |
| Analytic pressure and finite-volume limit | `analyticOnNhd_anchoredPressure`, `tendsto_normalized_symmetricMayerSum_centeredBasePlaquettes` |
| Center screening and area law | `rectangle_area_le_taylorOrder_of_taylorScreens`, `norm_integral_wilsonRectangle_le_areaLaw` |
| Concrete finite site/link reflection positivity | `FiniteSpecification.siteReflectionPositive_gibbsMeasure`, `FiniteSpecification.linkReflectionPositive_gibbsMeasure` |
| Concrete finite site/link Cauchy--Schwarz | `FiniteSpecification.normSq_integral_gibbsMeasure_siteReflectionProduct_le`, `FiniteSpecification.normSq_integral_gibbsMeasure_linkReflectionProduct_le` |
| Diagonal Taylor/Fubini positivity | `DiagonalReflection.WilsonActionDecomposition.gibbsReflectionPairing_eq_taylorPairing`, `DiagonalReflection.WilsonActionDecomposition.diagonalReflectionPositivity` |
| Diagonal Cauchy--Schwarz/all planes | `DiagonalReflection.WilsonActionDecomposition.normSq_reflectionInnerProduct_le`, `centeredInfiniteVolume_diagonalReflectionCauchySchwarz_all_planes` |

All listed project theorems are proved without `sorry`, `admit`, custom
axioms, or unsafe proof shortcuts.  Their expected kernel footprint consists
only of standard Lean/Mathlib foundations such as `propext`,
`Classical.choice`, and `Quot.sound`; the milestone regression files run
`#print axioms` on the headline declarations.

## Dependency structure and builds

The default public root is deliberately small:

```text
YangMills
├── Gauge.FiniteEdgeHaar
├── concrete finite site, link, and diagonal reflection bridges
├── concrete infinite-volume reflection positivity and Cauchy--Schwarz
├── StrongCoupling.ThermodynamicPressure
└── StrongCoupling.WilsonAreaLaw
    ├── finite lattice, gauge, Haar, and Wilson layers
    ├── generic Polymer/ combinatorics and KP/tree expansion
    ├── centered thermodynamic limit and clustering
    ├── analytic local expectations
    └── center selection and Wilson Taylor jets

YangMills.Regression                    (opt-in)
├── milestone tests and axiom audits
├── older finite-box Dobrushin comparison route
└── pinned Douglas periodic-torus baseline → LGT
```

This split preserves every regression theorem while keeping the periodic LGT
baseline and the older influence-matrix comparison modules out of ordinary
project-native incremental builds.  The generic finite-product DLR layer still
uses the separately pinned `markov-semigroups` specification API.  The full
audit is in [`docs/DEPENDENCY_AUDIT.md`](docs/DEPENDENCY_AUDIT.md).

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake build
```

For the comprehensive regression build, including the pinned periodic-torus
baseline and every milestone test, run:

```sh
lake build +YangMills.Regression
```

For ordinary development, build the narrow module being edited first, for
example:

```sh
lake build YangMills.StrongCoupling.WilsonAreaLaw
lake build YangMills.Gauge.SiteReflectionPositivity
```

The first `lake update` downloads the pinned dependencies and available
Mathlib artifacts.  Subsequent native incremental builds should not rebuild
the Douglas regression path unless `YangMills.Regression` or a compatibility
module is requested.

The comprehensive root also imports
[`YangMills/Tests/ReviewerSmoke.lean`](YangMills/Tests/ReviewerSmoke.lean), a
downstream critical-review suite.  It proves concrete normalization and
degenerate-case corollaries for empty finite volumes, constant observables,
Wilson loops, direct zero-coupling activity and Mayer-log normalization,
the KP certificate, infinite-volume
invariances, reflection pairing, and the zero-area rectangle bound.

## Repository map

```text
YangMills/
  Audit/           executable Mathlib and upstream axiom checks
  Compat/          narrow adapters to the pinned LGT development
  Baseline/        optional periodic-torus regression theorems
  Basic/           endpoint-indexed paths and analytic-limit tools
  Lattice/         cubic lattice, boxes, plaquettes, charge, and geometry
  Gauge/           Haar probability, fields, observables, Gibbs measures,
                   site reflection, and reflection positivity
  Wilson/          unitary representations, characters, loops, center charge
  Polymer/         model-independent hard-core gas and Mayer/KP theory
  Probability/     generic finite-product Gibbs and center-selection tools
  StrongCoupling/  plaquette expansion, thermodynamic limit, clustering,
                   pressure, analyticity, and area law
  Tests/           milestone, axiom, and critical-review regressions
```

The generic `Polymer/` layer does not depend on Yang--Mills modules.  Core
`Basic/`, `Lattice/`, `Gauge/`, and `Wilson/` modules do not depend on the
Douglas compatibility layer.

## Use of the Douglas--Rajasekaran LGT repository

The pinned external baseline is:

> Michael R. Douglas and Fred Rajasekaran, *Lattice Gauge Theory in Lean 4*,
> [`mrdouglasny/lgt`](https://github.com/mrdouglasny/lgt), Apache-2.0,
> commit `b8793ccf6a51e00e9e2b1685ba191b8626e37137`.

The project uses it in four explicit ways:

1. `YangMills/Compat/` imports narrow periodic geometry, finite Gibbs/DLR, and
   Dobrushin interfaces from the pinned source.
2. `YangMills/Baseline/PeriodicTorusMassGap.lean` re-exports the upstream
   periodic-torus mass-gap and DLR theorems as axiom-audited regressions.
3. `Gauge/ProductHaar.lean` generalizes the proof pattern of the upstream
   disjoint-coordinate locality factorization to a type-generic Mathlib API.
4. `Probability/FiniteProductGibbs.lean` adapts the finite-product gluing and
   DLR arguments from the upstream `YMSpec` and `YMIsGibbs` modules to
   arbitrary finite coordinate systems.

The older comparison modules also use the separately pinned
`markov-semigroups` Dobrushin infrastructure.  The independent cubic-lattice
path API, plaquette polymer expansion, KP/tree summability, thermodynamic
limit, clustering, analyticity, pressure, center-selection area law, and
reflection-positivity developments are project-native and do not import the
`LGT` compatibility layer.

Exact source files, commits, licenses, declarations, adaptation decisions,
and axiom footprints are recorded in
[`DOUGLAS_REUSE_AUDIT.md`](DOUGLAS_REUSE_AUDIT.md) and
[`docs/DOUGLAS_SCOPE.md`](docs/DOUGLAS_SCOPE.md).  Required Apache-2.0
provenance notices remain next to adapted arguments; historical comparisons
are not repeated throughout unrelated cluster-expansion modules.

## Scope and terminology

- “Strong coupling” means small `|β|` near `β=0`.
- “Mass gap” in this repository means exponential clustering unless an
  Osterwalder--Schrader reconstruction is actually supplied.
- The infinite-volume theorem currently establishes the unique representing
  probability of the cluster-expanded local state, not uniqueness of all DLR
  measures.
- The proved area law is for normalized rectangular Wilson loops carrying
  finite nontrivial center-charge data.  For `0 < ‖β‖ < r` inside the explicit
  disk, its bound has the form

  ```text
  K(r)^(2(R+T)) · exp(-log(r/‖β‖) · R T).
  ```

- Integer/site-hyperplane and affine diagonal reflection positivity and
  Cauchy--Schwarz are proved for the cluster-constructed measure without
  gauge-invariance assumptions on observables.  Half-integer/link-hyperplane
  positivity and Cauchy--Schwarz are proved for gauge-invariant positive-side
  observables.  Product-Haar gauge fixing, explicit matrix-coefficient trace
  contraction, normally convergent Taylor expansion, and Fubini give the
  finite Gram sum; the one-root KP estimate supplies the infinite-volume
  passage.  Optional Osterwalder--Schrader reconstruction remains future work.

## Documentation and license

See also:

- [`STATUS.md`](STATUS.md) for exact completed declarations and build logs;
- [`docs/ROADMAP.md`](docs/ROADMAP.md) for the concise milestone roadmap;
- [`docs/DETAILED_ROADMAP.md`](docs/DETAILED_ROADMAP.md) for the original
  long-form plan;
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for dependency rules;
- [`CONTRIBUTING.md`](CONTRIBUTING.md) for the development workflow.

The project is released under the [Apache License 2.0](LICENSE).
