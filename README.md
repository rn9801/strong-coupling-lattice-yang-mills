# Strong-Coupling Lattice Yang--Mills in Lean

This repository formalizes constructive lattice Yang--Mills theory at strong
coupling in Lean 4.  The project works on the infinite cubic lattice
`ℤ^d`, builds arbitrary finite-volume Gibbs specifications with frozen exterior
fields, and derives the thermodynamic results from a convergent plaquette
polymer/Mayer expansion.

> [!IMPORTANT]
> **Project status.** This is an active research formalization and remains a
> work in progress. Every theorem advertised in this README is checked without
> `sorry`, `admit`, project-specific axioms, or unsafe proof shortcuts, but the
> APIs, documentation, quantitative estimates, and theorem coverage will
> continue to receive additions and revisions. Axiom audits of the headline
> declarations report only standard Lean/Mathlib foundations such as
> `propext`, `Classical.choice`, and `Quot.sound`.

Integer/site, half-integer/link, and affine diagonal reflection positivity are
proved for concrete cubic Gibbs specifications and transferred to the
cluster-constructed infinite-volume measure, together with the corresponding
reflected Cauchy--Schwarz inequalities.
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

Osterwalder--Schrader reconstruction and a genuine Hamiltonian spectral-gap
theorem are not currently formalized.  See [`STATUS.md`](STATUS.md) for exact
declaration-level coverage and verified build records.

## API conventions and theorem scope

The README uses mathematical notation, but each object below corresponds to a
named Lean definition.  The most common parameters are:

| Symbol | Lean object | Meaning |
|---|---|---|
| `d` | `ℕ` | Lattice dimension; sites are `Fin d → ℤ`. |
| `G` | a type | Gauge group.  Individual definitions request only the structure they use. |
| `Λ` | `FiniteSpecification d G` | Dynamic edges, active plaquettes, and a frozen exterior field. |
| `Φ` | `RealPlaquettePotential G` | Bounded continuous, conjugation- and inversion-invariant real plaquette potential. |
| `β` | `ℝ` or `ℂ` | Real Gibbs coupling or complex analytic coupling, according to the theorem. |
| `η` | `ℕ → Configuration d G` | Arbitrary exterior configurations along the centered-box exhaustion. |
| `F,H` | `LocalObservable d G` | Continuous complex observables with recorded finite edge supports. |
| `ρ` | `ContinuousUnitaryRepData G n` | Positive-dimensional continuous unitary representation in fixed matrix coordinates. |
| `κ` | [`FiniteCenterChargeData ρ`](#finitecenterchargedata) | A nontrivial finite-order scalar center charge for `ρ`. |

The thermodynamic theorems are stated for a compact Hausdorff second-countable
topological group with its Borel measurable structure and a selected
`GaugeHaarProbability`.  In Lean this is the explicit typeclass context

```lean
[Group G] [TopologicalSpace G] [IsTopologicalGroup G]
[CompactSpace G] [T2Space G]
[MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
[GaugeHaarProbability G]
```

This is not attached globally: for example, the finite hard-core gas is purely
combinatorial, and `FiniteSpecification` needs no topology or measure.  The
source of each declaration is authoritative about its weakest implemented
hypotheses.

The principal result families have the following exact scope.

| Result family | Coupling and additional hypotheses | Formal conclusion |
|---|---|---|
| Exact finite plaquette gas | Any `β : ℂ` | The complex Yang--Mills partition function equals the finite polymer partition function. |
| Evaluated Mayer/KP expansion | `‖β‖ < latticeStrongCouplingRadius d Φ.bound` | The symmetric connected sum is absolutely summable, its exponential is the exact partition function, and that partition function is nonzero. |
| Infinite-volume probability and clustering | `β : ℝ` in the same disk; arbitrary `η` | All local expectations converge, the representing probability is boundary independent, and truncated correlations obey the explicit exponential bound. |
| Analytic local expectations and pressure | `β : ℂ` in the same open disk | Local expectations and anchored pressure are analytic; finite connected logarithms converge locally with the branch fixed at `β = 0`. |
| Rectangle area law | Wilson potential, `κ`, `i ≠ j`, `0 < r < radius`, and `|β| < r` | The normalized rectangular Wilson loop has an explicit perimeter prefactor times exponential area decay. |
| Site reflection | Any `RealPlaquettePotential`, real `β` in the disk | Positivity and reflected Cauchy--Schwarz on the full supported local algebra at every integer coordinate plane. |
| Link reflection | Wilson potential, `β ≥ 0` in the disk | Positivity and Cauchy--Schwarz at every half-integer coordinate plane, restricted to gauge-invariant supported local observables. |
| Diagonal reflection | Wilson potential, `β ≥ 0` in the disk, `τ ≠ σ` | Positivity and Cauchy--Schwarz on the full supported local algebra at every plane `xτ - xσ = k`. |

“Unique” below always means the unique probability measure representing the
constructed cluster local state.  It does not mean that every DLR state has
been classified.  Likewise, “log partition function” means the analytic
Mayer branch normalized to vanish at `β = 0`, not an arbitrary global branch
of `Complex.log`.

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

`GaugeHaarProbability G` stores a chosen probability measure together with
left-, right-, and inversion-invariance.  Two-sided invariance is derived by
composition.  For compact Borel topological groups the canonical instance is
constructed by normalizing Mathlib's Haar measure on the whole group.  Finite
collections of edge variables carry the corresponding independent product
probability.

A `FiniteSpecification d G` consists of:

- a finite set of dynamic positive edges to integrate;
- a finite set of active plaquettes contributing to the action;
- a full exterior configuration supplying every non-dynamic edge value.

`FiniteSpecification.evaluate` glues a dynamic field to the frozen exterior
field coordinatewise:

```text
Λ.evaluate U e = U(e),          if e ∈ Λ.dynamicEdges,
Λ.evaluate U e = Λ.exterior e,  otherwise.
```

No closure condition is built into the structure: a caller may choose any
finite edge and plaquette sets.  The box constructors used later provide the
geometric closure properties their theorems need.  This representation
therefore supports arbitrary finite shapes and boundary conditions, not only
periodic boxes.

Principal files:
[`Gauge/HaarProbability.lean`](YangMills/Gauge/HaarProbability.lean),
[`Gauge/ProductHaar.lean`](YangMills/Gauge/ProductHaar.lean), and
[`Gauge/Specification.lean`](YangMills/Gauge/Specification.lean).

### Yang--Mills action, partition function, and Gibbs measure

A `RealPlaquettePotential G` is a continuous function `Φ : G → ℝ`, an
explicit nonnegative number `Φ.bound`, a proof `‖Φ(g)‖ ≤ Φ.bound`, and proofs
of invariance under conjugation and inversion.  For a finite
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

The real partition function is strictly positive, and the Gibbs measure is
the normalized exponential tilt of finite product Haar.  A separate complex
API defines the entire function

```text
ZΛ,Φ(z) = ∫ exp(z SΛ,Φ(U)) dHaarΛ(U),    z ∈ ℂ.
```

Keeping real probability measures separate from complex analytic functions
prevents accidental use of a complex density as a probability law.

Principal files:
[`Gauge/FiniteVolume.lean`](YangMills/Gauge/FiniteVolume.lean) and
[`Gauge/ComplexFiniteVolume.lean`](YangMills/Gauge/ComplexFiniteVolume.lean).

### Wilson action and Wilson loops

`ContinuousUnitaryRepData G n` packages a monoid homomorphism
`ρ : G → U(n)`, its continuity, and a proof `0 < n`.  It neither assumes nor
derives irreducibility.  Its normalized character is

```text
χρ(g) = Tr(ρ(g)) / n,
```

and satisfies `‖χρ(g)‖ ≤ 1`.  The Wilson plaquette potential and the Wilson
observable of a closed path `C` are

```text
Φρ(g) = Re χρ(g),
Wρ(C,A) = χρ(Hol(A,C)).
```

Both are gauge invariant.

#### FiniteCenterChargeData

`CenterChargeData` records a central element that
acts in the representation by a nontrivial scalar phase.  Explicitly, it
supplies `z : G` and `ω : ℂ` such that `zg = gz` for every `g`, `‖ω‖ = 1`,
`ω ≠ 1`, and

```text
ρ(z) = ω I.
```

`FiniteCenterChargeData` additionally supplies an integer `q ≥ 2` with
`ω^q = 1`.  Thus the scalar center phase has finite nontrivial order; the
formalization does not assume that `ρ` is irreducible and does not invoke
Schur's lemma.  This is the precise hypothesis used by the center-selection
and area-law arguments.

Conceptually, this data witnesses a nontrivial one-dimensional character of
the cyclic central subgroup generated by `z`, as seen by `ρ`.  Twisting one
integrated link variable by `z` preserves Haar measure, while a Wilson or
Taylor monomial acquires a power of `ω`.  If that net power is nontrivial, the
integral equals the same nontrivial phase times itself and therefore vanishes.
The finite-order witness lets the proof record these charges modulo the actual
multiplicative order `orderOf ω` and feed the resulting selection rule into
the cubical filling argument.

The supplied `q` need not be the least such exponent; the proofs use
`orderOf ω`.  Nor does the structure assert that `z` itself has finite order.
It asserts only that the scalar by which `z` acts in this representation has
finite nontrivial order.  Supplying `κ : FiniteCenterChargeData ρ` is an
explicit theorem hypothesis: groups with trivial center, and representations
on which every central element acts trivially, do not satisfy it.

Principal files:
[`Wilson/Representation.lean`](YangMills/Wilson/Representation.lean),
[`Wilson/Loop.lean`](YangMills/Wilson/Loop.lean), and
[`Wilson/CenterSelection.lean`](YangMills/Wilson/CenterSelection.lean).

## Polymer and cluster expansion

### Abstract hard-core gas

`FinitePolymerModel P` consists of a finite polymer type, a symmetric
reflexive incompatibility relation, a decision procedure for that relation,
and complex activities `z(γ)`.  Reflexivity records that two occurrences of
the same polymer are incompatible; compatibility of a `Finset` tests only
distinct members.  For a finite restriction `S`, the partition function is

```text
Zpoly(S) = ∑ Γ ⊆ S, Γ compatible, ∏ γ ∈ Γ, z(γ).
```

`partitionFunction` is `Zpoly(univ)`.  The generic `Polymer/` directory is
independent of the Yang--Mills model: its finite and countable models know
nothing about lattices, groups, Haar measure, or Gibbs specifications.

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
occurrence is a separate labelled vertex.  The associated incompatibility
graph joins distinct occurrences whose polymer values are incompatible.  If
`X` is a multi-index, the Ursell coefficient and symmetry-normalized cluster
term are

```text
φᵀ(X) = ∑ H connected spanning subgraph, (-1)^|E(H)|,

c(X) = φᵀ(X) / (∏γ X(γ)!) · ∏γ z(γ)^X(γ).
```

Here `∏γ X(γ)!` is the automorphism factor that forgets the labels among equal
polymer occurrences.  Disconnected incompatibility graphs have zero Ursell
coefficient.  The formal theorem is unconditional: in the multivariate
formal-power-series ring, the compatible-family partition series is the
exponential of the symmetric connected series.  Evaluation at numerical
activities is a separate theorem and requires summability, supplied below by
the KP certificate.  The resulting analytic logarithm is the branch
normalized by `Z(0)=1`; it is not identified with the global principal
`Complex.log`.

### KP certificate and explicit disk

The standard finite KP hypothesis formalized by
`KoteckyPreissCertificate` is

```text
(∀ γ, 0 ≤ a(γ)) ∧
∀ γ ∈ S,
  ∑ δ ∈ S, δ incompatible with γ, ‖z(δ)‖ exp(a(δ)) ≤ a(γ),
```

for a restricted finite polymer set `S`.  Since incompatibility is reflexive,
the sum includes `δ = γ` when `γ ∈ S`.  The plaquette gas takes `S = univ`
and uses

```text
a(γ) = |γ| log 2.
```

Write

```text
perturbationMajorant Φ β = exp(‖β‖ Φ.bound) - 1,

dobrushinThreshold(D,C)
  = min(1/8, 1/(16(C+1)), log(2)/(16(D+1))),

certifiedStrongCouplingRadius(D,C,B)
  = log(1 + dobrushinThreshold(D,C)) / (B + 1),

latticeStrongCouplingRadius(d, Φ.bound)
  = certifiedStrongCouplingRadius(16d, 2^(16d), Φ.bound).
```

Inside the disk
`‖β‖ < latticeStrongCouplingRadius d Φ.bound`, lattice-animal counting
proves the KP certificate uniformly in the finite volume and exterior field.
The formalization derives, uniformly in `Λ` and its frozen exterior field:

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

The reusable output of this layer is stronger than the application displayed
here.  The same finite/countable Mayer normalization, connected-graph
cancellation, tree bound, rooted summability, and one-/two-colour source
extraction can be instantiated by any hard-core polymer model that supplies
activities and a KP certificate.  The plaquette adjacency graph, lattice-
animal count, perturbation majorant, and concrete radius are the
Yang--Mills-specific inputs.

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

Concretely, if

```text
hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound,
```

then `centeredInfiniteVolumeMeasure η Φ β hβ` is a regular Borel probability
and, for every `F : LocalObservable d G`,

```text
localExpectation(centeredGibbsSequence η Φ β n, F)
  ⟶ ∫ A, F(A) ∂ centeredInfiniteVolumeMeasure η Φ β hβ.
```

The same limit holds along every cofinal subsequence of centered boxes.

The resulting `centeredInfiniteVolumeMeasure` is independent of the exterior
sequence, invariant under every site gauge transformation, translation
invariant, regular, and exponentially clustering.  More precisely, for local
observables `F,H`, the code proves an explicit estimate of the form

```text
‖μ(FH) - μ(F) μ(H)‖
  ≤ A(F,H,Φ,β) exp(-m(Φ,β) · dist(supp F, supp H)),
```

where `m(Φ,β)>0` follows from the strict KP tilt.

In the exact declaration, `dist` is
`centeredClusterSupportDistance F.support H.support`: it is the global
plaquette-incidence separation when the recorded supports are disjoint, and
zero otherwise.  The amplitude is an explicit sum of the two-root decorated
cluster majorant and the trivial observable-norm terms.  It contains no
dependence on the separation distance.  Its current explicit formula uses the
sup norms and recorded support cardinalities of `F`, `H`, and `F.mul H`; the
last support is bounded in size by `|supp F| + |supp H|`.  Consequently one
fixed constant applies while two disjoint observables are translated farther
apart.  A constant uniform over arbitrarily large supports and depending only
on `‖F‖∞` and `‖H‖∞` is not claimed.  The mass is

```text
centeredClusterMass Φ β = -log(plaquetteClusterDecayRate Φ β) > 0.
```

The current uniqueness theorem is deliberately scoped: it proves uniqueness
of the probability measure representing this cluster-expanded local state and
independence of centered cofinal boundary sequences.  It does **not** yet
assert uniqueness among all possible infinite-volume DLR measures.

Principal files:
[`StrongCoupling/CenteredInfiniteVolume.lean`](YangMills/StrongCoupling/CenteredInfiniteVolume.lean) and
[`StrongCoupling/ExponentialClustering.lean`](YangMills/StrongCoupling/ExponentialClustering.lean).

### Analytic infinite-volume local expectations

For fixed `F`, `η`, and `Φ`,
`centeredComplexLocalExpectationSequence F η Φ n` is the finite centered
complex Gibbs expectation.  Finite-volume zero-freeness makes each term
analytic on the explicit disk.  The decorated one-root KP estimate supplies a
volume-independent bound on every smaller closed disk, while the preceding
real-coupling theorem gives pointwise convergence on the real diameter.
Mathlib's analytic normal-family infrastructure, packaged here as a disk
Vitali theorem, yields a unique analytic limit

```text
analyticInfiniteVolumeLocalExpectation F η Φ : ℂ → ℂ
```

with

```text
AnalyticOnNhd ℂ (analyticInfiniteVolumeLocalExpectation F η Φ)
  (Metric.ball 0 (latticeStrongCouplingRadius d Φ.bound)).
```

The finite expectations converge locally uniformly on that disk.  On every
real `β` in it, the analytic value equals the integral against
`centeredInfiniteVolumeMeasure`; it is independent of `η`.  Thus analyticity
is not inferred from clustering alone: both conclusions use the same
decorated KP majorant, and the analytic passage additionally uses locally
uniform boundedness and Vitali convergence.

Principal file:
[`StrongCoupling/ThermodynamicAnalyticity.lean`](YangMills/StrongCoupling/ThermodynamicAnalyticity.lean).

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

The two normalizations are deliberately distinct:

```text
anchoredPressurePerSite Φ β
  = ∑ ordered orientations o at 0, ∑' rooted clusters X, rootedTerm(o,X),

anchoredPressure Φ β
  = (number of ordered orientations)⁻¹ * anchoredPressurePerSite Φ β.
```

`tendsto_normalized_symmetricMayerSum_centeredBasePlaquettes` divides by the
number of active ordered plaquettes and converges to `anchoredPressure`.
The companion `..._perSite` theorem divides by the number of base sites and
converges to `anchoredPressurePerSite`.

In statistical-mechanics terminology a free-energy density can be obtained
from pressure after choosing a sign and temperature normalization.  The code
currently formalizes pressure directly; it does not introduce a separate
Lean definition named `freeEnergy`.

Principal files:
[`StrongCoupling/ThermodynamicCluster.lean`](YangMills/StrongCoupling/ThermodynamicCluster.lean) and
[`StrongCoupling/ThermodynamicPressure.lean`](YangMills/StrongCoupling/ThermodynamicPressure.lean).

### Center selection and the rectangular area law

For a representation with [`FiniteCenterChargeData`](#finitecenterchargedata),
first expand the Wilson
Boltzmann factor into labelled plaquette-character Taylor words.  Twisting one
integrated edge by the chosen central element preserves product Haar measure,
while each labelled word is an eigenfunction whose phase is its net center
charge at that edge.  A nontrivial phase forces that word's Haar integral to
vanish.  The cubical screening argument shows that a nonzero word screening an
`R`-by-`T` rectangle has at least `R*T` letters.  Hence every lower Taylor
coefficient vanishes.  This is an exact finite-volume statement, not an
asymptotic estimate.

Completed centered boxes integrate every edge read by the action and by the
loop.  Conditioning the added coordinates reduces their local expectations
to ordinary centered specifications with induced exterior fields.  The
one-root boundary estimate therefore identifies their limit with the already
constructed infinite-volume state.  Schwarz's analytic estimate applied on a
circle of radius `r` converts the Taylor zero of order `R*T` into

```text
‖∫ Wrectangle(x,i,j,R,T,A) dμ∞(A)‖
  ≤ K(Φ,r)^(2*(R+T))
      * exp(-log(r/|β|) * (R*T)).
```

Here `i,j : Fin d` are distinct coordinate axes.  Starting from the base site
`x`, the boundary path takes `R` positive `i`-steps, `T` positive `j`-steps,
and then the corresponding negative runs back to `x`.  Thus `R*T` is the
filling area and `2*(R+T)` is the perimeter.

The exponential perimeter factor comes from the present decorated
observable-root KP bound: on the analytic circle `|β| = r`, its uniform bound
grows exponentially with the Wilson-loop support cardinality, which is at
most the loop length.  The center-selection argument supplies the separate
area power `(|β|/r)^(R*T)`.  Consequently the displayed estimate is
equivalently `exp(-σ area + c perimeter)`, a standard area law with an explicit
boundary correction.  The perimeter term is not asserted to be optimal or
intrinsically necessary; removing it would require a sharper Wilson-loop
source bound than is currently formalized.

The Lean theorem `norm_integral_wilsonRectangle_le_areaLaw` assumes
`i ≠ j`, `0 < r`, `r < latticeStrongCouplingRadius d Φ.bound`, and
`|β| < r`.  Lean's real division and logarithm are total at `β = 0`, and the
proof treats that algebraic case separately; the usual positive string-tension
interpretation uses `0 < |β| < r`.  The theorem concerns normalized rectangular
Wilson loops with the stated finite nontrivial center charge; it does not claim
an area law for arbitrary loop geometry or representations with trivial center
charge.

Principal files:
[`Wilson/CenterSelection.lean`](YangMills/Wilson/CenterSelection.lean),
[`StrongCoupling/WilsonTaylorJets.lean`](YangMills/StrongCoupling/WilsonTaylorJets.lean),
and
[`StrongCoupling/WilsonAreaLaw.lean`](YangMills/StrongCoupling/WilsonAreaLaw.lean).

### Integer-hyperplane reflection and positive algebra

For a coordinate `τ` and integer `k`, site reflection is

```text
(θx)τ = 2k - xτ,
(θx)i = xi  for i ≠ τ.
```

The construction is extended to signed directions, signed and stored edges,
paths, plaquettes, configurations, and holonomy.  Edges perpendicular to the
plane acquire the inversion dictated by the stored-positive-edge convention.

For full-lattice local observables, the anti-linear reflection and pairing are

```text
(ΘF)(A)  = conj(F(θA)),
⟨F,H⟩θ,μ = ∫ (ΘF)(A) * H(A) dμ(A).
```

`F.SupportedInSitePositiveHalf τ k` means exactly
`∀ e ∈ F.support, k ≤ e.source τ`.  `SiteReflectionPositive μ τ k` says the
self-pairing has zero imaginary part and nonnegative real part for every such
`F`.  `SiteReflectionCauchySchwarz` says

```text
normSq(⟨F,H⟩θ,μ) ≤ re(⟨F,F⟩θ,μ) * re(⟨H,H⟩θ,μ).
```

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

Principal files:
[`Gauge/SiteReflection.lean`](YangMills/Gauge/SiteReflection.lean),
[`Gauge/SiteReflectionPositivity.lean`](YangMills/Gauge/SiteReflectionPositivity.lean),
[`Gauge/SiteReflectionBridge.lean`](YangMills/Gauge/SiteReflectionBridge.lean),
and
[`StrongCoupling/ConcreteSiteReflectionPositivity.lean`](YangMills/StrongCoupling/ConcreteSiteReflectionPositivity.lean).

### Half-integer/link-hyperplane reflection

Link reflection through `xτ = k + 1/2` exchanges the two open half-lattices
and inverts the stored perpendicular edges crossing the plane.  Its positive
algebra consists of local observables supported on the positive side and,
unlike the site and diagonal cases, requires gauge invariance.

The implemented support predicate is
`∀ e ∈ F.support, k < e.target τ`; in particular it includes perpendicular
links crossing the plane.  Both reflection positivity and Cauchy--Schwarz
quantify over observables satisfying this predicate and full local gauge
invariance.

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

It permutes stored positive edges without inversion.  The positive-half
predicate requires both endpoints of every recorded edge to lie
in the closed half-space:

```text
∀ e ∈ F.support,
  k ≤ e.source τ - e.source σ ∧ k ≤ e.target τ - e.target σ.
```

The finite labelled normal form consists of common plane variables `U₀` and
two strict-side fields `U₋,U₊`.  At fixed `U₀`, every cut-plaquette term has
the Wilson form

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

## Reusable layers and specialization boundaries

The directory names reflect mathematical dependencies and reuse boundaries.
A result at a higher row in this table can be reused without importing the
rows below it.

| Layer | Mathematical input | Reusable output | First model-specific ingredient |
|---|---|---|---|
| `Basic/` and graph combinatorics | Finite types, finite sets, simple graphs, formal power series, analytic functions | Endpoint paths, analytic-limit lemmas, connected-graph cancellation | None |
| `Polymer/` | A polymer type, symmetric reflexive incompatibility, complex activities | Finite/countable hard-core partition functions, symmetric Mayer normalization, formal exponential formula, Whitney tree bound, KP/rooted summability, decorated one-/two-root extraction | None; this layer has no Yang--Mills import |
| `Probability/FiniteProductGibbs` | Arbitrary finite coordinate type, one-site probability, bounded measurable energy | Product gluing, normalized finite Gibbs kernels, finite-product DLR consistency | No lattice or group; only the upstream specification interface is imported |
| `Gauge/ProductHaar`, `Specification`, and `FiniteVolume` | Measurable/topological group, Haar probability, finite edge/plaquette data, invariant potential | Product Haar factorization, exterior gluing, gauge-covariant finite Gibbs theory | Gauge holonomy and plaquette potentials, but not cubic boxes |
| `StrongCoupling/Plaquette*` | Cubic plaquette incidence, connected plaquette subsets, lattice-animal bounds | Exact plaquette gas, explicit radius, uniform KP certificate | The constants `16*d` and `2^(16*d)` and the plaquette perturbation majorant |
| Centered thermodynamic modules | Translation action of `ℤ^d`, centered cofinal boxes, local-observable density | Boundary-independent local limit, representing measure, clustering, analytic pressure | Cubic translations and the selected centered exhaustion |
| Wilson area and reflection modules | Unitary matrix representation, finite center charge, or reflected Wilson action decomposition | Rectangle selection/area law and site/link/diagonal positivity | Center screening, matrix-coefficient Taylor expansions, and reflection geometry |

Consequently the abstract polymer results are applicable, without any gauge
theory definitions, to hard-core contour models, lattice gases, defect gases,
and other cluster expansions once the caller supplies an incompatibility
relation and a KP certificate.  The decorated-root APIs similarly apply to
insertions and truncated correlations in such models.  What does **not**
generalize automatically is the proof of the certificate: animal counting,
spatial separation, and boundary geometry must be supplied by each model.

The finite-product probability layer is independently reusable for finite
spin systems with a general single-site probability.  `ProductHaar` then adds
the group-specific transformations needed for gauge theory.  The site
reflection labelled theorem is more general than Wilson theory once an action
decomposition of the displayed form is supplied; the current concrete link
and diagonal Gram theorems specialize to the Wilson potential because their
proof expands unitary matrix traces.

There are two intentionally separate strong-coupling routes in the repository:

```text
project-native cubic plaquette gas
  → KP/tree cluster expansion
  → thermodynamic limit, clustering, analyticity, pressure, area law,
    and infinite-volume reflection positivity;

pinned periodic-torus LGT baseline
  → Dobrushin influence estimates
  → optional regression theorem.
```

No theorem in the first chain imports the Douglas compatibility layer or uses
the Dobrushin mass-gap theorem.

## Main theorem index

| Result | Representative declarations |
|---|---|
| Holonomy covariance and Wilson gauge invariance | `holonomy_gaugeTransform`, `ContinuousUnitaryRepData.wilsonLoop_gaugeInvariant` |
| Finite-volume gauge invariance | `FiniteVolume.action_gaugeInvariant`, `FiniteVolume.gibbsExpectation_gaugeTransform`, `FiniteVolume.integral_gibbsMeasure_gaugeTransformExterior_complex` |
| Finite-volume probability and DLR | `FiniteVolume.partitionFunction_pos`, `gibbsMeasure_isGibbs_box` |
| Entire finite partition function | `FiniteVolume.complexPartitionFunction_entire` |
| Exact plaquette-polymer representation | `complexPartitionFunction_eq_polymerPartition` |
| Unconditional formal Mayer logarithm | `plaquetteRestrictedSymmetricMayerPowerSeries_eq_formalMayerLog` |
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
`Classical.choice`, and `Quot.sound`; the theorem regression files run
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
├── theorem tests and axiom audits
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
baseline and the full theorem and axiom-audit suite, run:

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

The project-owned modules compile without warnings under the public, default,
and comprehensive regression targets.  A clean comprehensive build may still
display warnings emitted by the pinned Douglas dependencies; those diagnostics
are upstream and are kept separate from the project-native warning policy.

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
  Tests/           theorem, axiom, and critical-review regressions
```

The generic `Polymer/` layer does not depend on Yang--Mills modules.  Core
`Basic/`, `Lattice/`, `Gauge/`, and `Wilson/` modules do not depend on the
Douglas compatibility layer.

## Sources, provenance, and bibliography

The formalization was guided by several sources in different senses.  To
avoid conflating mathematical guidance with code reuse, this table records
the role of each source explicitly.

| Source | How it was followed here | What was not taken from it |
|---|---|---|
| Seiler's monograph | Principal mathematical guide for the constructive strong-coupling program: lattice gauge fields, expansion methods, thermodynamic control, analyticity, and confinement | No theorem was translated line by line; the Lean interfaces, explicit radius, and estimates are project-specific |
| Osterwalder--Seiler | Foundational guide for the lattice formulation, physical/reflection positivity, strong-coupling infinite volume, and confinement | The present three concrete reflection bridges and their exact support predicates are new Lean proofs |
| Menotti--Pelissetto | Targeted guide for reflection positivity through hyperplanes containing lattice sites | The labelled action-decomposition API and infinite-volume KP transfer are project-native |
| Kotecký--Preiss | Source of the abstract activity-sum convergence criterion and rooted polymer-expansion strategy | The symmetric multi-index normalization, formal Mayer exponential, Whitney/tree implementation, decorated sources, and cubic certificate were proved in this repository |
| Whitney and Penrose | Classical combinatorial background for broken-circuit cancellation and tree-graph regrouping | No external formal proof or code was reused; the finite sign-reversing involution is project-native |
| Douglas--Rajasekaran `LGT` | Direct Lean source for the two adaptations identified below and an imported periodic-torus Dobrushin regression baseline | It is not the proof route for the project-native cluster expansion, thermodynamic limit, clustering, analyticity, area law, or reflection limits |
| Mathlib and `MarkovSemigroups` | Foundational Lean APIs; the latter supplies the generic specification interface used by `FiniteProductGibbs` and the optional Dobrushin baseline | Neither dependency supplied an abstract polymer, Ursell, KP, or tree-graph library at the audited revisions |

Thus “followed” means proof architecture or mathematical organization unless a
file header explicitly says “adapted.”  The implementation was checked against
the cited mathematics, but it proves the displayed Lean statements from the
definitions in this repository; published claims are not imported as axioms.

### Direct Lean reuse: the Douglas--Rajasekaran LGT repository

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

### Bibliography

1. Erhard Seiler, *Gauge Theories as a Problem of Constructive Quantum Field
   Theory and Statistical Mechanics*, Lecture Notes in Physics **159**,
   Springer, Berlin--Heidelberg, 1982.
   [doi:10.1007/3-540-11559-5](https://doi.org/10.1007/3-540-11559-5).

2. Konrad Osterwalder and Erhard Seiler, “Gauge Field Theories on a Lattice,”
   *Annals of Physics* **110** (1978), 440--471.
   [doi:10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8).

3. Pietro Menotti and Andrea Pelissetto, “General Proof of
   Osterwalder--Schrader Positivity for the Wilson Action,” *Communications in
   Mathematical Physics* **113** (1987), 369--373.
   [doi:10.1007/BF01221251](https://doi.org/10.1007/BF01221251).

4. Roman Kotecký and David Preiss, “Cluster Expansion for Abstract Polymer
   Models,” *Communications in Mathematical Physics* **103** (1986), 491--498.
   [doi:10.1007/BF01211762](https://doi.org/10.1007/BF01211762).

5. Hassler Whitney, “A Logical Expansion in Mathematics,” *Bulletin of the
   American Mathematical Society* **38** (1932), 572--579.
   [doi:10.1090/S0002-9904-1932-05460-X](https://doi.org/10.1090/S0002-9904-1932-05460-X).

6. Oliver Penrose, “Convergence of Fugacity Expansions for Classical
   Systems,” in T. A. Bak (ed.), *Statistical Mechanics: Foundations and
   Applications*, W. A. Benjamin, New York--Amsterdam, 1967, 101--109.

7. Michael R. Douglas and Fred Rajasekaran, *Lattice Gauge Theory in Lean 4*,
   [`mrdouglasny/lgt`](https://github.com/mrdouglasny/lgt), Apache-2.0,
   commit `b8793ccf6a51e00e9e2b1685ba191b8626e37137`.

8. Michael R. Douglas, *markov-semigroups*,
   [`mrdouglasny/markov-semigroups`](https://github.com/mrdouglasny/markov-semigroups),
   Apache-2.0, commit `acf649108ea2222f4a8544a2782f448cb502492a`.

9. The Mathlib Community, *Mathlib for Lean 4*,
   [`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4),
   Apache-2.0, commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`
   (toolchain `v4.30.0`).

The first four items are the principal mathematical references for the lattice
gauge, cluster-expansion, and reflection-positivity arguments.  Items 5--6
document the named graph methods used in the generic Mayer proof.  Items 7--9
are software/formalization sources rather than substitutes for the
mathematical references.  Exact dependency pins, including transitive
packages, are in [`lake-manifest.json`](lake-manifest.json).

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
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for dependency rules;
- [`docs/DEPENDENCY_AUDIT.md`](docs/DEPENDENCY_AUDIT.md) for the public and
  regression import closures;
- [`CONTRIBUTING.md`](CONTRIBUTING.md) for the development workflow.

The project is released under the [Apache License 2.0](LICENSE).
