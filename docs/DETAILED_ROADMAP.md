# Lean Formalization Roadmap for Strong-Coupling Lattice Yang–Mills Theory

**Status:** implementation plan, not yet a theorem file
**Primary references:** Seiler's constructive gauge-theory monograph; Osterwalder–Seiler on lattice gauge theory and reflection positivity; Menotti–Pelissetto for reflection through hyperplanes containing lattice sites
**Intended executor:** Codex working inside a pinned Lean 4 + Mathlib repository
**Quality target:** small reviewable modules, no `sorry`, no `admit`, no custom axioms, and reusable generic infrastructure separated from Yang–Mills-specific arguments

---

## 1. Purpose and end state

The project should formalize a mathematically clean strong-coupling construction of pure lattice Yang–Mills theory on the cubic lattice. The intended theorem chain is:

1. define finite-volume lattice gauge theory for a general compact gauge group and a general bounded conjugation-invariant plaquette potential;
2. prove covariance of holonomy and gauge invariance of the finite-volume Gibbs measure and gauge-invariant observables;
3. specialize to a Wilson action arising from a finite-dimensional continuous unitary representation;
4. prove a convergent high-temperature/strong-coupling polymer expansion for sufficiently small inverse coupling `β`;
5. deduce exponential insensitivity to boundary conditions;
6. construct a unique infinite-volume Gibbs state and then an infinite-volume probability measure;
7. prove exponential decay of truncated correlations, which is the primary formal meaning of “mass gap” in this project;
8. prove analyticity of local expectations and the pressure/free energy in a complex neighborhood of `β = 0`;
9. for Wilson loops carrying nontrivial center charge, prove a strong-coupling area-law estimate;
10. prove reflection positivity for the Wilson action across both:
    - integer hyperplanes, which contain lattice sites, and
    - half-integer hyperplanes, which cut links;
11. pass both reflection-positivity statements to the strong-coupling infinite-volume limit.

The initial deliverable should be an internally consistent library proving the above for deliberately nonoptimal small-coupling constants. Sharp constants are not a goal.

---

## 2. Important scope corrections

These corrections should be encoded in theorem statements from the beginning.

### 2.1 Strong coupling means small `β`

Use the convention

\[
  d\mu_{\Lambda,\beta}(U)
  = \frac{1}{Z_{\Lambda}(\beta)}
    \exp\!\left(\beta\sum_{p\in P_\Lambda}\Phi(U_p)\right)
    \prod_{e\in E_\Lambda} d\mu_H(U_e),
\]

where `μ_H` is normalized Haar measure. Thus `β = 0` is the independent-Haar point and the strong-coupling theorem is a small-`|β|` theorem.

Do not switch later to the physics convention in which a bare coupling `g` appears and `β` is proportional to `g⁻²` without an explicit conversion lemma.

### 2.2 The area law is representation-dependent

A nontrivial center alone does **not** imply an area law for every Wilson representation. A center-neutral representation has no center-charge selection rule.

The formal theorem should assume explicit data:

- a compact gauge group `G`;
- a finite-dimensional continuous unitary representation `ρ`;
- a central element `z : G`;
- a unit complex number `ω ≠ 1` such that
  \[
    \rho(z)=\omega I.
  \]

The resulting Wilson loop is said to have nontrivial center charge. The first theorem may assume that `ω` has finite order. A later generalization can replace this by the quotient of `ℤ` by the kernel of `n ↦ ω^n`.

### 2.3 “Mass gap” has two possible meanings

The main strong-coupling theorem should be named `exponential_clustering` and should assert a bound of the form

\[
 |\langle FG\rangle-\langle F\rangle\langle G\rangle|
 \le C\,\|F\|_\infty\|G\|_\infty
       |\operatorname{supp}F|\,|\operatorname{supp}G|
       e^{-m\,\operatorname{dist}(\operatorname{supp}F,\operatorname{supp}G)}.
\]

This is the Euclidean mass-gap statement used in constructive statistical mechanics.

A spectral gap for a reconstructed Hamiltonian is a stronger, optional endpoint. It requires an Osterwalder–Schrader Hilbert-space/transfer-operator construction in addition to reflection positivity. Do not call the spectral theorem proved merely because exponential clustering has been proved.

### 2.4 Reflection positivity is not restricted to strong coupling in finite volume

Finite-volume reflection positivity for the Wilson action should be proved for all real `β ≥ 0`. The infinite-volume reflection-positive measure constructed in this project is initially available only in the strong-coupling regime because that is where uniqueness and convergence have been formalized.

---

## 3. Guiding design decisions

### 3.1 Use two mathematical layers

Build:

1. a small abstract finite oriented two-complex API for the definition of gauge fields, gauge transformations, paths, holonomy, plaquette actions, and finite-volume Gibbs measures;
2. a concrete cubic-lattice API for boxes, distances, plaquette counting, fillings, translations, and reflections.

Do not attempt to formalize arbitrary CW complexes or full cellular homology before the finite gauge-theory definitions compile. The abstract layer only needs the data actually used by lattice gauge theory.

### 3.2 Store only positively oriented edge variables

For the cubic lattice, store a configuration on canonical positive edges

\[
 E_+ = \mathbb Z^d \times \{0,\ldots,d-1\}.
\]

An oriented edge is a positive edge plus an orientation sign. Evaluation on the reverse edge is defined by group inverse. This makes product Haar measure canonical and prevents repeated equality constraints of the form `U_{-e}=U_e⁻¹`.

### 3.3 Separate real probability theory from complex analyticity

Use two objects:

- a real finite-volume probability measure for real `β` and real-valued plaquette potential;
- a complex unnormalized partition function and complex expectation numerator for complex `β`.

The analytic proof should not pretend that a complex density defines a probability measure.

### 3.4 Prove a general polymer theorem before applying it to gauge theory

The polymer expansion should be a generic finite hard-core polymer-gas theorem. The Yang–Mills application then supplies:

- polymers: connected finite sets of plaquettes;
- incompatibility: overlap in an integrated edge, or a slightly enlarged local-overlap relation chosen once and used consistently;
- activities: Haar integrals of products of plaquette perturbations;
- activity bound: a power of `q(β)=exp(|β| M)-1`;
- connected-set counting on the cubic plaquette adjacency graph.

This is the most reusable and most likely Mathlib-quality component of the project.

### 3.5 Avoid Peter–Weyl theory in the first strong-coupling proof

The basic cluster expansion needs only bounded local plaquette interactions and product Haar measure. It does not need character orthogonality or a complete representation-theoretic expansion.

For the center area law, use an explicit Taylor expansion of the Wilson Boltzmann factor and an edgewise center-change-of-variables selection lemma. This requires only the chosen representation and its center phase, not the full Peter–Weyl theorem.

### 3.6 Use intentionally loose geometric constants

For example, if two plaquettes are adjacent when they share an unoriented edge, it is enough to prove a bound such as

\[
  \deg(p) \le 8(d-1)
\]

rather than optimize the exact degree. Likewise, prove a connected-animal count of the form

\[
  N_n(p) \le C_d^{n-1}
\]

using an explicit encoding by rooted walks or rooted trees. A larger but easy-to-formalize `C_d` is preferable to a sharp informal argument.

---


## 3A. Integration with Michael R. Douglas's `lgt` repository

Michael R. Douglas and collaborators have already formalized a substantial finite-volume strong-coupling lattice-gauge-theory stack in the public repository
[`mrdouglasny/lgt`](https://github.com/mrdouglasny/lgt). As of 4 August 2026, its README reports axiom-clean proofs of a finite-periodic-torus Dobrushin mass-gap theorem for the Wilson action, together with the underlying Yang–Mills measure, Gibbs specification, DLR identity, influence estimates, and lattice-distance machinery. This should materially shorten the project, but it should be used as a **pinned upstream baseline and source of reusable lemmas**, not treated as a complete replacement for this roadmap.

### 3A.1 What is already available and should be reused

The initial audit should inspect and, where version-compatible, import or adapt the following declarations and proof patterns.

| Douglas component | Representative declarations/files | Recommended use here |
|---|---|---|
| Periodic lattice geometry | `LGT/Lattice/CellComplex.lean`, `LGT/Lattice/LatticeDistance.lean`; `LatticeLink`, `LatticePlaquette`, `boundaryLinks`, `linkGraphDist`, `linkGraphDist_support` | Reuse incidence, neighbor-count, and graph-distance proofs for torus regression tests; port the generic bounded-degree arguments to boxes and the infinite lattice. |
| Plaquette connection and covariance | `LGT/GaugeField/Connection.lean`; `GaugeConnection`, `plaquetteHolonomy`, `gaugeTransformConnection`, `holonomy_gauge_covariant` | Reuse the four-link plaquette calculations and gauge-covariance simp lemmas. General path holonomy still needs to be built in this project. |
| Finite Yang–Mills measure | `LGT/MassGap/YMMeasure.lean`; `productHaar`, `wilsonAction`, `partitionFn`, `ymMeasure`, `ymMeasure_isProbabilityMeasure` | Reuse or generalize the measure-theoretic plumbing, positivity, density, and expectation-to-integral bridge. |
| Locality under product measures | `LGT/MassGap/Locality.lean`; `plaquetteHolonomy_dependsOn`, `plaqObs_dependsOn`, `integral_mul_of_disjoint_dependsOn` | Adopt the use of Mathlib's `DependsOn`; generalize from plaquette observables to the project's local-observable API. |
| Conditional kernels and DLR | `LGT/Gibbs/YMSpec.lean`, `LGT/Gibbs/YMIsGibbs.lean`; `gluedConfig`, `ymGibbsSpec`, `glue_measurePreserving`, `integral_glue_split_eq`, `ymMeasure_isGibbs` | High-value reusable infrastructure for fixed exterior configurations, conditional measures, and eventual DLR uniqueness. |
| Strong-coupling Dobrushin verification | `LGT/Gibbs/YMDobrushin.lean`, `LGT/MassGap/StrongCoupling.lean`; `ymDobrushinCondition`, `ym_mass_gap_strong_coupling`, `ym_mass_gap_exponential_decay`, `ym_mass_gap_rate_exists` | Import as an early verified baseline for periodic tori and plaquette two-point functions; use it as a regression theorem and as a possible independent route to boundary mixing. |
| Abstract Dobrushin library | sibling `markov-semigroups` dependency | Reuse maximal coupling, Gibbs-specification, DLR, Neumann-series, and covariance machinery rather than reproving it. |

Before copying any implementation, inspect the exact current declarations, commits, and licenses. The repository is Apache-2.0 licensed; copied or substantially adapted source must retain the required attribution and license notice. Prefer a Lake dependency, git submodule, or a clearly documented generalization over unattributed copy-and-paste.

### 3A.2 What does **not** yet solve our project

The Douglas development is currently optimized for a different endpoint:

1. its principal geometry is the finite periodic torus `(ZMod N)^d`, whereas this project needs abstract finite gauge complexes, finite boxes with exterior boundary conditions, the full lattice, and reflection-symmetric exhaustions;
2. the implemented holonomy is plaquette-specific; the inspected generic `Holonomy.lean` and `GaugeTransformation.lean` files are stubs, so paths, open Wilson lines, arbitrary loops, and their support theory still have to be formalized;
3. its `HasGaugeTrace` layer is intentionally lightweight and should not automatically replace the more structured continuous unitary representation and center-charge API required here;
4. its `HasHaarProbability` class packages a supplied probability measure but does not by itself eliminate the need to audit Mathlib's normalized Haar construction, left/right invariance, inversion invariance, and uniqueness;
5. the headline theorem is a finite-periodic-torus exponential-decay result for plaquette trace observables obtained by Dobrushin methods; it is not yet the general local-observable cluster theorem or the infinite-volume construction targeted here;
6. it does not supply the abstract hard-core polymer expansion, zero-free complex disk, pressure analyticity, center-selection area law, or either integer- or half-integer-plane reflection positivity.

Therefore the project should **reuse the foundations and retain both proof routes**:

- **Dobrushin route:** gives an early, already kernel-checked mass-gap baseline and may yield boundary mixing and Gibbs uniqueness after adapting the specification to boxes;
- **polymer/cluster route:** remains required for the requested Seiler/Osterwalder–Seiler-style expansion, complex analyticity, pressure, charged-defect expansion, and area law.

Neither route should be presented as subsuming the other until precise implication theorems have been formalized.

### 3A.3 Version and dependency policy

The inspected repository reports Lean/Mathlib `v4.29.0` and depends on sibling repositories `markov-semigroups` and `gaussian-field`. Before adding imports:

1. pin the exact `lgt`, `markov-semigroups`, `gaussian-field`, Mathlib, and Lean commits in `DOUGLAS_REUSE_AUDIT.md`;
2. build all three upstream projects unchanged;
3. run `#print axioms` on the imported headline declarations;
4. determine whether this project can share the same toolchain or whether a controlled port is needed;
5. never mix declarations compiled against incompatible Mathlib commits;
6. record whether each reused result is imported unchanged, wrapped, generalized, or reproved.

A proposed compatibility layer is:

```text
YangMills/
  Compat/
    DouglasLGT.lean
    DouglasGeometry.lean
    DouglasGibbs.lean
    DouglasDobrushin.lean
  Baseline/
    PeriodicTorusMassGap.lean
```

`Compat/` must contain narrow adapters and equivalence lemmas, not a second fork of the complete upstream codebase.

### 3A.4 Required reuse audit

Create `DOUGLAS_REUSE_AUDIT.md` with one row per candidate declaration:

```text
Upstream repository and commit:
Upstream file and declaration:
License/provenance:
Exact type:
Dependencies:
Axiom footprint:
Our corresponding abstraction:
Decision: import / wrap / generalize / do not use
Reason:
Porting work still required:
Regression test:
```

At minimum, audit:

```text
LatticeLink
LatticePlaquette
boundaryLinks
plaquetteHolonomy
holonomy_gauge_covariant
productHaar
partitionFn
ymMeasure
ymMeasure_isProbabilityMeasure
plaquetteHolonomy_dependsOn
integral_mul_of_disjoint_dependsOn
gluedConfig
glue_measurePreserving
integral_glue_split_eq
ymGibbsSpec
ymMeasure_isGibbs
ymDobrushinCondition
linkGraphDist
linkGraphDist_support
boundary_sum_bound
ym_mass_gap_exponential_decay
ym_mass_gap_rate_exists
```

### 3A.5 Revised implementation strategy

The fastest sound route is:

1. reproduce the Douglas periodic-torus build as a baseline;
2. import or wrap its measure/Gibbs/DLR and `DependsOn` infrastructure;
3. build this roadmap's general path, boundary-box, representation, center-charge, and reflection APIs without forcing them into the torus-specific definitions;
4. prove equivalence lemmas on finite tori, so the upstream mass-gap theorem becomes a regression theorem for the new API;
5. generalize only the upstream lemmas that genuinely remove work—for example gluing, product-measure change of variables, DLR consistency, and bounded-degree distance estimates;
6. proceed with the independent abstract polymer expansion and its Yang–Mills specialization;
7. compare the Dobrushin and cluster-expansion decay bounds on their common domain.

This integration should save substantial work in finite-volume probability theory and deliver an early nontrivial theorem, while avoiding an architectural lock-in that would obstruct the later area-law and reflection-positivity phases.

---

## 4. Proposed repository layout

The names below are provisional. Before creating files, inspect the repository's namespace and naming conventions.

```text
YangMills/
  Compat/
    DouglasLGT.lean
    DouglasGeometry.lean
    DouglasGibbs.lean
    DouglasDobrushin.lean

  Baseline/
    PeriodicTorusMassGap.lean

  Basic/
    Orientation.lean
    FiniteGaugeComplex.lean
    Path.lean
    Holonomy.lean

  Lattice/
    Site.lean
    Edge.lean
    Plaquette.lean
    Box.lean
    Region.lean
    Incidence.lean
    Distance.lean
    Translation.lean
    Reflection.lean
    Filling.lean
    Counting.lean

  Gauge/
    HaarProbability.lean
    Configuration.lean
    Transform.lean
    Observable.lean
    BoundaryCondition.lean
    FiniteVolume.lean
    GaugeInvariance.lean

  Wilson/
    Representation.lean
    Character.lean
    Action.lean
    CenterCharge.lean
    TaylorExpansion.lean

  Polymer/
    Basic.lean
    CompatibleFamily.lean
    PartitionFunction.lean
    DeletionRecursion.lean
    ConnectedGraph.lean
    Ursell.lean
    TreeGraphBound.lean
    KoteckyPreiss.lean
    Analytic.lean
    Marked.lean
    InfluenceDecay.lean

  StrongCoupling/
    PlaquettePolymer.lean
    Activity.lean
    ActivityBound.lean
    GeometricCriterion.lean
    BoundarySensitivity.lean
    InfiniteVolumeState.lean
    InfiniteVolumeMeasure.lean
    Clustering.lean
    Pressure.lean
    Analyticity.lean
    CenterSelection.lean
    AreaLaw.lean

  ReflectionPositivity/
    Basic.lean
    SiteReflection.lean
    LinkReflection.lean
    GaugeFixing.lean
    WilsonCone.lean
    InfiniteVolume.lean

  Reconstruction/                 # optional later project
    OSHilbertSpace.lean
    TimeTranslation.lean
    TransferOperator.lean
    SpectralGap.lean

  Examples/
    FiniteCyclic.lean
    U1.lean
    Rectangle.lean

  Tests/
    OnePlaquette.lean
    GaugeCovariance.lean
    Reflection.lean
    CenterSelection.lean

STATUS.md
```

Generic `Polymer/` files should avoid importing any Yang–Mills module. Once stable, they are candidates for independent upstream pull requests.

---

## 5. Mathematical foundations and conventions

### 5.1 Gauge-group assumptions

A Lean-friendly first interface is to pass normalized bi-invariant Haar probability as explicit data rather than repeatedly reconstructing it from typeclasses.

Illustrative structure:

```lean
structure GaugeHaarProbability (G : Type*) where
  measure : Measure G
  isProbability : IsProbabilityMeasure measure
  map_mul_left : ∀ g, Measure.map (fun x => g * x) measure = measure
  map_mul_right : ∀ g, Measure.map (fun x => x * g) measure = measure
  map_inv : Measure.map Inv.inv measure = measure
```

The exact fields should be adjusted to current Mathlib APIs, perhaps using `MeasurePreserving` rather than direct map equalities.

Then prove a constructor from normalized Haar measure under suitable assumptions, expected to include:

- group and topological-group structure;
- compact Hausdorff topology;
- Borel measurability assumptions sufficient for Haar integration;
- second countability or metrizability where Mathlib's integration theorems require it.

The proof should proceed as follows:

1. take Mathlib's left Haar measure;
2. prove it has finite, nonzero total mass on a compact group;
3. normalize to total mass one;
4. obtain right invariance from uniqueness of normalized left Haar measure, using the pushforward under right multiplication;
5. obtain inversion invariance similarly.

Before implementing, inspect exact existing lemmas. Do not duplicate an existing normalized compact Haar API.

### 5.2 Abstract finite gauge complex

Define only the minimum data:

```lean
structure FiniteGaugeComplex where
  Vertex : Type
  Edge : Type                 -- canonical positive edges
  Plaquette : Type
  [vertexFintype : Fintype Vertex]
  [edgeFintype : Fintype Edge]
  [plaquetteFintype : Fintype Plaquette]
  src tgt : Edge → Vertex
  boundary : Plaquette → List (Edge × Orientation)
  boundary_closed : ...
```

`Orientation` can be a two-element type with involution and multiplication. Avoid identifying it with `Bool` throughout proofs unless that substantially simplifies code.

A signed-edge evaluator is

```lean
def edgeValue (A : K.Edge → G) : K.Edge × Orientation → G
```

with negative orientation mapped to inverse.

A path should contain:

- a list or vector of signed edges;
- a proof that successive endpoints agree;
- source and target vertices.

Do not quotient paths by cancellation or reparametrization. Those equivalences are unnecessary for the first theorem chain.

### 5.3 Cubic lattice

Use

```lean
def Site (d : ℕ) := Fin d → ℤ
structure PosEdge (d : ℕ) where
  base : Site d
  dir : Fin d
```

with target `base + unitVector dir`.

A canonical plaquette can be

```lean
structure Plaquette (d : ℕ) where
  base : Site d
  dir₁ dir₂ : Fin d
  lt_dir : dir₁ < dir₂
```

and its positively oriented boundary is the ordered four-edge word

\[
 (x,\mu),\quad (x+e_\mu,\nu),\quad
 (x+e_\nu,\mu)^{-1},\quad (x,\nu)^{-1}.
\]

Prove immediately:

- the boundary is composable and closed;
- translation commutes with source, target, and boundary;
- reversing plaquette orientation inverts plaquette holonomy;
- every edge occurs in at most `2(d-1)` coordinate plaquettes with a fixed geometric location;
- the chosen plaquette adjacency graph has a finite explicit degree bound.

Require `2 ≤ d` only for lemmas that genuinely need plaquettes.

### 5.4 Regions and boundary conditions

A finite-volume specification should not be tied too early to one notion of boundary. Use:

```lean
structure FiniteSpecification (d : ℕ) where
  dynamicEdges : Finset (PosEdge d)
  activePlaquettes : Finset (Plaquette d)
  exterior : PosEdge d → G
```

Evaluation of an edge uses the dynamic configuration inside `dynamicEdges` and `exterior` outside. Add a locality proof showing that only finitely many values of `exterior` are read.

Later define standard constructors:

- `freeBoxSpecification n`: all edges used by active plaquettes are dynamic;
- `fixedBoxSpecification n η`: only designated interior edges are dynamic and all remaining edge values are supplied by `η`;
- symmetric boxes adapted to integer and half-integer reflections.

Boundary comparison theorems should allow two exterior configurations that differ on an arbitrary set and should measure the distance from an observable to the **boundary-disagreement set**, not merely to the geometric boundary.

---

## 6. Gauge transformations, holonomy, and observables

### 6.1 Gauge action

For `g : Vertex → G` and `A : Edge → G`, define

\[
  (g\cdot A)_e = g_{s(e)} A_e g_{t(e)}^{-1}.
\]

The first core lemma is path-holonomy covariance:

\[
  \operatorname{Hol}_{g\cdot A}(\gamma)
  =g_{s(\gamma)}\operatorname{Hol}_A(\gamma)g_{t(\gamma)}^{-1}.
\]

Prove this by induction on the path list. Make reversal and concatenation lemmas available first:

```lean
holonomy_nil
holonomy_cons
holonomy_append
holonomy_reverse
holonomy_gaugeTransform
```

For a loop based at `x`, conclude conjugation covariance. Therefore every class function of loop holonomy is gauge invariant.

### 6.2 Local observables

On the infinite configuration space

```lean
def InfiniteConfig (d : ℕ) (G : Type*) := PosEdge d → G
```

define a local continuous observable as an actual continuous function together with the proposition that it depends on only finitely many edges:

```lean
def DependsOn (S : Finset (PosEdge d))
    (F : C(InfiniteConfig d G, ℂ)) : Prop :=
  ∀ A B, (∀ e ∈ S, A e = B e) → F A = F B

structure LocalObservable where
  toContinuousMap : C(InfiniteConfig d G, ℂ)
  support : Finset (PosEdge d)
  dependsOn_support : DependsOn support toContinuousMap
```

Do not claim that `support` is minimal. Prove support enlargement lemmas so users can replace it by a convenient finite set.

Add:

- constants;
- addition, multiplication, conjugation;
- pullback under translations, gauge transformations, and reflections;
- sup-norm bounds;
- Wilson loop constructors.

### 6.3 Gauge invariance of product Haar measure

For a finite edge set, the gauge transformation acts coordinatewise by a left and right multiplication depending on edge endpoints. Prove it preserves the finite product Haar measure by:

1. proving each coordinate map preserves Haar probability;
2. applying a finite-product measure-preserving theorem;
3. handling the reindexing between a finite set and its subtype explicitly.

Then prove:

```lean
theorem finiteVolume_integral_gaugeTransform ...
theorem finiteVolume_partition_gaugeInvariant ...
theorem finiteVolume_expectation_gaugeInvariant ...
```

For fixed boundary conditions, restrict to gauge transformations that are the identity at vertices whose transformation would alter frozen edge values. State this subgroup explicitly instead of claiming full boundary gauge invariance.

---

## 7. General plaquette model

### 7.1 Real plaquette potential

Use a structure such as:

```lean
structure RealPlaquettePotential (G : Type*) where
  φ : C(G, ℝ)
  conj_invariant : ∀ a g, φ (a * g * a⁻¹) = φ g
  inv_invariant : ∀ g, φ g⁻¹ = φ g
```

Conjugation invariance gives gauge invariance. Inversion invariance makes the action independent of the canonical orientation chosen for a plaquette and is useful for reflections.

Continuity plus compactness supplies a finite sup norm. For the first cluster theorem it is acceptable to assume an explicit bound `M` with `|φ(g)| ≤ M`, then later define `M = ‖φ‖`.

### 7.2 Finite-volume objects

For a specification `Λ`, define

\[
 S_\Lambda(A;\eta)=\sum_{p\in P_\Lambda}\Phi(U_p(A;\eta)),
\]

\[
 w_{\Lambda,\beta}(A;\eta)=e^{\beta S_\Lambda(A;\eta)},
\]

\[
 Z_{\Lambda,\beta}^{\eta}=\int w_{\Lambda,\beta}(A;\eta)\,d\mu_H^{E_\Lambda}(A),
\]

and normalized expectations.

Prove:

- measurability and continuity of all integrands;
- integrability from compactness/boundedness;
- positivity of `Z` for real `β`;
- `Z(0)=1` for normalized product Haar;
- expectation norm bound `|E[F]| ≤ ‖F‖∞`;
- gauge invariance under admissible gauge transformations.

Use `Real.exp` for the probability measure and `Complex.exp` only in the complex analytic layer.

### 7.3 Complexified finite-volume functions

For `β : ℂ`, define

\[
 Z_\Lambda(\beta)=\int
 \exp\!\left(\beta\sum_p\Phi(U_p)\right)d\mu_H.
\]

Prove it is entire in finite volume either by:

- differentiating under the integral using a bounded entire integrand; or
- a uniformly convergent power series on compact `β`-balls.

This finite-volume analyticity is easy and should be completed before the infinite-volume cluster expansion.

---

## 8. Wilson action

### 8.1 Representation data

Do not depend on a broad representation-theory framework unless it already fits. A purpose-built structure may initially be easier:

```lean
structure ContinuousUnitaryRepData (G : Type*) (n : ℕ) where
  ρ : G →* Matrix.unitaryGroup (Fin n) ℂ
  continuous_ρ : Continuous ρ
```

The exact codomain should follow current Mathlib definitions. An equivalent continuous monoid homomorphism into unitary linear equivalences is acceptable.

Define the character and normalized Wilson potential

\[
 \chi_\rho(g)=\operatorname{Tr}(\rho(g)),\qquad
 \Phi_\rho(g)=\frac{1}{n}\operatorname{Re}\chi_\rho(g).
\]

Prove:

- continuity;
- conjugation invariance;
- `χ(g⁻¹)=conj(χ(g))` from unitarity;
- inversion invariance of `Re χ`;
- `|χ(g)| ≤ n` and hence `|Φρ(g)| ≤ 1`.

The last bound gives the clean perturbation estimate

\[
 |e^{\beta\Phi_\rho(g)}-1|\le e^{|\beta|}-1.
\]

### 8.2 Wilson loops

For a closed path `C`, define

\[
 W_\rho(C;A)=\frac{1}{n}\chi_\rho(\operatorname{Hol}_A(C)).
\]

Prove locality, continuity, gauge invariance, orientation reversal, and `|Wρ(C)| ≤ 1`.

Do not quotient loops by backtrack erasure. Instead prove that inserting an immediate edge/reverse-edge pair leaves holonomy and the Wilson observable unchanged.

---

## 9. Abstract finite polymer gas

This is the central generic component.

### 9.1 Basic definitions

For a finite polymer type `P`, use a symmetric incompatibility relation. It is often convenient to make it reflexive so a polymer is incompatible with itself.

```lean
structure PolymerModel where
  Polymer : Type
  [polymerFintype : Fintype Polymer]
  incompatible : Polymer → Polymer → Prop
  symmetric_incompatible : Symmetric incompatible
  self_incompatible : ∀ γ, incompatible γ γ
  activity : Polymer → ℂ
```

A compatible family is a `Finset Polymer` whose distinct elements are pairwise compatible. Define

\[
 Z=\sum_{\Gamma\text{ compatible}}\prod_{\gamma\in\Gamma}z(\gamma).
\]

Prove the deletion identity for any polymer `γ`:

\[
 Z(P)=Z(P\setminus\{\gamma\})
      +z(\gamma)Z(P\setminus N[\gamma]).
\]

This finite identity is a good first milestone because it gives a recursion useful for both nonvanishing and influence estimates.

### 9.2 Kotecký–Preiss criterion

Formalize a theorem of the form:

If `a : P → ℝ≥0` and

\[
 \sum_{\gamma'\not\sim\gamma}
 |z(\gamma')|e^{a(\gamma')}
 \le a(\gamma)
\]

for every `γ`, then:

- the partition function is nonzero;
- a logarithm normalized by `Log Z(0)=0` exists along analytic activity families;
- connected cluster coefficients are absolutely summable;
- the total weight of clusters connected to a marked polymer is bounded by `e^{a(γ)}-1` or another explicit safe constant;
- weighted versions yield exponential spatial decay.

The exact constants may differ from the classical optimal statement. Record the theorem actually proved and derive the lattice threshold from it.

### 9.3 Recommended proof order

Implement the abstract polymer theory in this order:

1. compatible families and finite partition sums;
2. deletion recursion;
3. an inductive Dobrushin/KP ratio estimate proving nonvanishing;
4. ordered tuples of polymers and incompatibility graphs;
5. connected graph sums/Ursell coefficients;
6. exponential formula relating `log Z` to connected clusters;
7. a tree-graph bound;
8. absolute convergence and marked-cluster bounds;
9. analytic activity families and normal convergence.

The deletion-recursion proof supplies useful results even if the full Ursell formalization takes longer.

### 9.4 Ursell coefficients

For an ordered tuple `γ : Fin n → P`, define its incompatibility graph. The Ursell coefficient is

\[
 \varphi^T(\gamma_1,\ldots,\gamma_n)
 =\sum_{H\subseteq G_\gamma\atop H\text{ connected spanning}}
   (-1)^{|E(H)|}.
\]

Formalization tasks:

- finite simple graphs on `Fin n`;
- spanning connected subgraphs;
- permutation invariance of `φᵀ`;
- vanishing when the incompatibility graph is disconnected;
- the finite exponential formula for `Z`;
- a bound by the number of spanning trees or by a safe tree-graph majorant.

A Penrose partition identity is elegant but potentially expensive in Lean. A cruder bound obtained by summing over rooted trees and additional edges is acceptable if it still closes the KP criterion.

### 9.5 Analytic families

Define an analytic activity family `z : ℂ → P → ℂ`. On a disk `|β|<r`, assume a uniform KP majorant. Prove locally uniform convergence of the connected-cluster series, hence analyticity.

Avoid choosing the global complex logarithm. Define the cluster-series logarithm and prove:

```lean
Complex.exp (clusterLog β) = partitionFunction β
clusterLog 0 = 0
```

on the small disk. This also proves nonvanishing there.

### 9.6 Marked clusters

Develop a root/marked version with one or two distinguished finite supports. This should yield:

- response to changing activities in a remote set;
- ratios of partition functions with local defects;
- one-point local expectations;
- truncated two-point functions.

The main combinatorial statement is that after vacuum clusters cancel, any surviving marked cluster is connected to every marked support it influences.

---

## 10. From plaquettes to polymers

### 10.1 Plaquette perturbation

Write

\[
 e^{\beta\Phi(U_p)}=1+u_p(\beta,U),
 \qquad
 u_p=e^{\beta\Phi(U_p)}-1.
\]

Expanding over subsets of active plaquettes gives

\[
 Z_\Lambda(\beta)
 =\sum_{X\subseteq P_\Lambda}
   \int\prod_{p\in X}u_p\,d\mu_H.
\]

Define two plaquettes to be adjacent when their factors share a dynamic edge. The connected components of `X` are polymers. Product Haar measure gives exact factorization over components:

\[
 \int\prod_{p\in X}u_p
 =\prod_{\gamma\in\operatorname{Comp}(X)}
   \int\prod_{p\in\gamma}u_p.
\]

This is the bridge from the original gauge model to a hard-core polymer gas.

### 10.2 Polymer activity

For a connected nonempty finite set `γ` of plaquettes, define

\[
 z_{\Lambda,\eta}(\gamma;\beta)
 =\int\prod_{p\in\gamma}
   \bigl(e^{\beta\Phi(U_p)}-1\bigr)
   \prod_{e\in E(\gamma)\cap E_\Lambda}d\mu_H(U_e),
\]

with exterior edge values supplied by `η`.

Prove:

- the activity depends only on edges incident to `γ`;
- translation covariance for translation-invariant boundary-free systems;
- analyticity in `β`;
- the uniform bound
  \[
    |z(\gamma;\beta)|
    \le q(\beta)^{|\gamma|},
    \qquad q(\beta)=e^{|\beta|M}-1;
  \]
- if two boundary conditions agree on all exterior edges touching `γ`, their activities agree;
- in general
  \[
    |z_\eta(\gamma)-z_{\eta'}(\gamma)|
    \le 2q(\beta)^{|\gamma|}.
  \]

### 10.3 Exact polymer representation

Prove a finite identity, not merely an asymptotic expansion:

```lean
theorem partition_eq_polymerPartition ... :
  gaugePartition Λ η β = polymerPartition (plaquettePolymerModel Λ η β)
```

The key proof decomposes every plaquette subset into connected components and uses Haar-product factorization. Separate this into reusable lemmas:

- finite-set connected-component partition;
- no shared dynamic edge between different components;
- functions depending on disjoint coordinate sets integrate multiplicatively;
- product over a disjoint union equals product over components.

### 10.4 Geometric KP criterion

Choose `a(γ)=a₀|γ|`, for instance `a₀=1`. If `C_d` bounds connected plaquette animals through a root plaquette, show

\[
 \sum_{\gamma'\not\sim\gamma}
 |z(\gamma')|e^{|\gamma'|}
 \le |\gamma|\,B_d
      \sum_{n\ge1}C_d^{n-1}
      \bigl(e q(\beta)\bigr)^n.
\]

Pick an explicit condition such as

\[
 C'_d e q(\beta)\le \frac14,
\]

where `C'_d` absorbs all incidence constants. Define

```lean
def betaStrong (d : ℕ) (M : ℝ≥0) : ℝ := ...
```

and prove that `|β| < betaStrong d M` implies the abstract KP hypothesis.

Do not expose a complicated closed form unless needed. It is acceptable to state the theorem using the simple sufficient inequality `C'_d e (exp(|β|M)-1) < 1/4`.

---

## 11. Connected plaquette-set counting

This deserves its own module and tests.

Let `Δ_d` be a proved upper bound on the plaquette adjacency degree. Establish a lemma:

```lean
theorem card_connected_finsets_containing_le
    (p : Plaquette d) (n : ℕ) :
  #{γ : Finset (Plaquette d) |
      γ.Connected ∧ p ∈ γ ∧ γ.card = n} ≤ C d ^ (n - 1)
```

Possible proof routes, in increasing sophistication:

1. encode a connected set by a depth-first traversal of a rooted spanning tree of length at most `2(n-1)` and bound walks by `Δ_d^(2(n-1))`;
2. choose a canonical breadth-first tree using a fixed total order, then encode parent choices;
3. use a general graph-animal count already available in Mathlib, if found during the audit.

Route 1 is likely easiest. It overcounts heavily but is completely explicit.

Also prove weighted tail bounds:

\[
 \sum_{\gamma\ni p,\ |\gamma|\ge r} q^{|\gamma|}
 \le \frac{q(C_d q)^{r-1}}{1-C_dq}.
\]

These geometric-series lemmas will be used repeatedly in boundary sensitivity, clustering, and area law.

---

## 12. Boundary-condition sensitivity

### 12.1 Target theorem

For a local observable `F` supported on edges `S`, two exterior conditions `η,η'`, and a finite region containing `S`, prove under the strong-coupling criterion:

\[
 |\langle F\rangle_{\Lambda,\eta}
  -\langle F\rangle_{\Lambda,\eta'}|
 \le C_d\|F\|_\infty |S|
 e^{-m_d\,\operatorname{dist}(S,D(\eta,\eta'))}.
\]

Here `D(η,η')` is the set of active plaquettes whose activity can see an exterior edge on which the two conditions differ. For arbitrary boundary conditions one may replace this by the set of boundary-touching plaquettes.

### 12.2 Proof architecture

1. Expand numerator and denominator as polymer gases.
2. Treat insertion of `F` as a marked root supported on the plaquettes/edges meeting `S`.
3. Compare the two marked polymer series.
4. Activities not touching the boundary-disagreement set agree exactly.
5. Every noncanceling difference therefore contains a connected incompatibility chain from the root to the disagreement set.
6. A chain spanning graph distance `r` has total polymer size at least `c r` for an explicit lattice constant `c`.
7. Apply an exponentially weighted KP estimate or sum the connected-animal tail.

The theorem should first be proved for `‖F‖∞ ≤ 1`, then scaled.

### 12.3 Recommended intermediate theorem

Prove an abstract influence-decay theorem for polymer gases. Let two activity functions agree outside a set `B`. Then the difference of a marked observable at root `R` is bounded by the total weight of clusters connecting `R` to `B`. This makes the Yang–Mills theorem mostly geometry.

---

## 13. Infinite-volume state and measure

### 13.1 Thermodynamic sequence

Choose nested cubic boxes `Λ_n` with an explicit convention and prove:

- every finite edge support lies in `Λ_n` for all sufficiently large `n`;
- distance from a fixed support to the boundary tends to infinity;
- boxes are preserved by the needed integer or half-integer reflections along suitable subsequences;
- boundary/volume ratios tend to zero for pressure arguments.

### 13.2 Limit of local expectations

For a local observable `F`, boundary sensitivity makes

\[
 \langle F\rangle_{\Lambda_n,\eta_n}
\]

Cauchy, uniformly over all boundary conditions. Define

\[
 \omega_\beta(F)=\lim_{n\to\infty}
 \langle F\rangle_{\Lambda_n,\eta_n}.
\]

Prove:

- independence of box sequence within a cofinal class;
- independence of boundary conditions;
- linearity;
- `ωβ(1)=1`;
- positivity on real nonnegative local observables;
- `|ωβ(F)|≤‖F‖∞`;
- gauge invariance;
- translation invariance;
- reflection invariance;
- consistency with finite-volume limits.

Call this the **infinite-volume local state**.

### 13.3 Constructing the probability measure

The safest route is real Riesz–Markov.

1. Work on the compact product configuration space `X=(E_+→G)`.
2. Show real-valued local continuous functions form a unital separating subalgebra of `C(X,ℝ)`.
3. Use Stone–Weierstrass to prove uniform density.
4. Extend `ωβ` uniquely by continuity to a positive norm-one functional on `C(X,ℝ)`.
5. Apply the real Riesz–Markov–Kakutani theorem to obtain a regular Borel probability measure `μβ`.
6. Recover complex expectations by real and imaginary parts.

This route avoids needing a general Kolmogorov extension theorem for interacting projective marginals.

An alternative is to extend every finite-volume Gibbs measure to the full product by independent Haar variables outside the box and prove weak convergence. Use this only if Mathlib's compactness API for probability measures is substantially easier than the Stone–Weierstrass/Riesz route.

### 13.4 Gibbs/DLR property

The first infinite-volume milestone need only construct the unique limit state. A later theorem should prove the Dobrushin–Lanford–Ruelle specification property:

\[
 \int F\,d\mu_\beta
 =\int \bigl(\mathbb E_{\Lambda}^{\eta}[F]\bigr)
       \,d\mu_\beta(\eta).
\]

Uniqueness among all DLR measures then follows from the same boundary-influence estimate. Keep DLR machinery in a separate module so it does not block the first thermodynamic-limit theorem.

---

## 14. Exponential clustering and mass gap

### 14.1 Target theorem

For bounded local observables `F,G`, prove

\[
 |\omega_\beta(FG)-\omega_\beta(F)\omega_\beta(G)|
 \le C_d\|F\|_\infty\|G\|_\infty
       |S_F|\,|S_G|e^{-m_d\operatorname{dist}(S_F,S_G)}.
\]

The constant and distance may first be stated in the plaquette-incidence graph and later converted to `ℓ¹` lattice distance.

### 14.2 Proof

Use a two-root marked cluster expansion. Vacuum clusters and clusters touching only one root cancel in the truncated correlation. Every remaining cluster connects the two supports. Its total size is at least proportional to their distance. The weighted KP bound gives the exponential tail.

Formalize first:

```lean
theorem finiteVolume_truncatedCorrelation_bound ...
```

uniformly in region and boundary condition. Then pass to the infinite-volume state.

### 14.3 Optional spectral-gap project

After reflection positivity is available, build:

1. the positive-time local algebra;
2. the sesquilinear form `⟨F,G⟩OS = ω(ΘF · G)`;
3. the quotient by its null space and Hilbert completion;
4. the time-translation contraction or transfer operator;
5. a theorem converting exponential time-correlation decay into a spectral gap on the orthogonal complement of the vacuum.

This should be a separate project because it requires substantial functional analysis and reconstruction infrastructure.

---

## 15. Analyticity

### 15.1 Local expectations

On a complex disk satisfying a uniform KP condition, the marked cluster series for a local observable converges normally. Prove that

\[
 \beta\mapsto\omega_\beta(F)
\]

is complex analytic there. For real `β` in the disk, this analytic function agrees with the probabilistic expectation.

Recommended theorem order:

1. finite-volume entire numerator and partition function;
2. uniform nonvanishing of `ZΛ` on a small disk;
3. analytic finite-volume normalized expectations;
4. locally uniform convergence of expectations as `Λ ↑ ℤ^d`;
5. analyticity of the limit by a uniform-limit theorem for analytic functions or directly by the marked cluster series.

### 15.2 Pressure/free energy

Define the cluster logarithm in finite volume and prove

\[
 \log Z_\Lambda(\beta)
 =\sum_{\text{connected clusters in }\Lambda}w(C;\beta).
\]

For boxes, show

\[
 p(\beta)=\lim_{n\to\infty}\frac{1}{|P_{\Lambda_n}|}
             \log Z_{\Lambda_n}(\beta)
\]

exists and is analytic.

A formalization-friendly proof is:

1. assign every finite connected cluster a canonical anchor, such as its lexicographically least plaquette;
2. define the infinite rooted cluster sum at the origin;
3. prove absolute and locally uniform convergence;
4. write the finite-volume log partition function as the sum over translates whose support lies in the box;
5. bound missing translates by a boundary-layer estimate;
6. divide by volume and pass to the limit.

Do not use a complex branch of `log` independently in every box. The connected-cluster series fixes the branch by requiring value zero at `β=0`.

### 15.3 Derivatives

Once analyticity is proved, add identities such as

\[
 p'(\beta)=\lim_{\Lambda}
 \frac1{|P_\Lambda|}\left\langle\sum_{p\in P_\Lambda}\Phi(U_p)\right\rangle,
\]

and derivatives of local expectations as sums of truncated correlations. These are consequences, not prerequisites.

---

## 16. Center selection and the strong-coupling area law

### 16.1 Center-charge data

Use explicit data recording

```lean
structure CenterChargeData (ρ : ContinuousUnitaryRepData G n) where
  z : G
  central_z : ∀ g, z * g = g * z
  omega : ℂ
  norm_omega : ‖omega‖ = 1
  nontrivial : omega ≠ 1
  rho_z : ρ.ρ z = omega • 1
```

For the first theorem, add a natural number `m ≥ 2` and prove `omega^m=1`, preferably together with exact order if needed.

The first implementation may use the same representation for the Wilson action and the inserted loop. Keep the definitions modular enough to later separate an action representation `σ` from an observable representation `ρ`; then the plaquette charges come from `σ` and the loop charge comes from `ρ`.

### 16.2 Edgewise selection lemma

Let `f : G → ℂ` satisfy

\[
 f(zg)=\omega^q f(g).
\]

Haar left invariance gives

\[
 \int f(g)d\mu_H(g)
 =\omega^q\int f(g)d\mu_H(g).
\]

Thus if `ω^q ≠ 1`, the integral vanishes.

Formalize this as a standalone lemma for any measure-preserving transformation and eigenfunction, then instantiate it with center multiplication. This general lemma will be useful elsewhere.

### 16.3 Taylor expansion of the Wilson weight

With `t=β/(2n)` and `χ=χρ`, use

\[
 e^{\beta\operatorname{Re}\chi(g)/n}
 =e^{t\chi(g)}e^{t\overline{\chi(g)}}
 =\sum_{a,b\ge0}
   \frac{t^{a+b}}{a!b!}\chi(g)^a\overline{\chi(g)}^b.
\]

For a finite set of plaquettes this becomes a sum over two multiplicity fields

\[
 a,b:P_\Lambda\to\mathbb N.
\]

Justify termwise integration by absolute convergence and the bound `|χ|≤n`.

Each `χ(U_p)` insertion carries one oriented center charge around `∂p`; each conjugate insertion carries the opposite charge. The Wilson loop insertion contributes its charge along the loop.

### 16.4 Discrete charge conservation

Define an additive charge group

\[
 A_\omega=\mathbb Z/\ker(n\mapsto\omega^n).
\]

For a finite-order first version, use `ZMod m`.

A multiplicity pair `(a,b)` defines a plaquette 2-chain with coefficient `a(p)-b(p)` in `Aω`. Its cellular boundary is an edge 1-chain. Edgewise Haar selection proves:

> A Taylor monomial has zero integral unless the boundary of its plaquette charge equals the negative center-charge 1-chain of the inserted Wilson loop.

This is the exact algebraic core of the area law.

Build only the small cubical chain API needed here:

- finitely supported `A`-valued functions on positive edges and plaquettes;
- oriented incidence signs;
- boundary of a plaquette;
- linear extension to finite 2-chains;
- `boundary_boundary = 0` if later useful;
- loop 1-chain;
- compatibility with translations and reflections.

Do not block the project on a general singular-homology library.

### 16.5 Center filling area

Define

\[
 A_\omega(C)=\min\left\{
   \sum_p \bigl(a(p)+b(p)\bigr):
   \partial(a-b)=-q_\rho[C]
 \right\}.
\]

For a finite loop this minimum is over finite-support fields and is finite when the loop is a plaquette boundary chain. It is the exact combinatorial quantity forced by the selection rule.

First prove the area law in terms of `Aω(C)`. Then prove geometric comparison lemmas:

- for a positively oriented `R×T` coordinate rectangle carrying nonzero charge, `Aω(C) ≥ RT`;
- the obvious planar filling realizes equality under the expected charge assumptions;
- for general planar simple loops, compare `Aω(C)` with the number of enclosed plaquettes;
- for arbitrary loops, retain the minimal filling-area formulation.

### 16.6 Area-law estimate

After vacuum clusters cancel against the denominator, every contributing defect cluster screening the Wilson loop has total Taylor order at least `Aω(C)`. Sum the tail using the strong-coupling majorant to obtain a bound such as

\[
 |\omega_\beta(W_\rho(C))|
 \le K^{|C|}\exp(-\sigma A_\omega(C)).
\]

A perimeter prefactor is acceptable in the first general theorem. For coordinate rectangles, absorb it into the area exponent after decreasing the strong-coupling threshold or prove a cleaner rectangle-specific bound

\[
 |\omega_\beta(W_\rho(\partial R_{L,T}))|
 \le C e^{-\sigma LT}.
\]

Do not claim an area law for a center-neutral representation.

### 16.7 Suggested staging

1. finite cyclic gauge group example, where the selection rule is elementary;
2. abstract compact group with an explicit finite-order center phase;
3. rectangle area lower bound;
4. general center filling area;
5. optional infinite-order center phase, including charged `U(1)` representations.

---

## 17. Reflection geometry

Fix a time coordinate `τ : Fin d`.

For integer `k`, define site reflection

\[
 \theta_k(x)_\tau=2k-x_\tau,
 \qquad \theta_k(x)_j=x_j\ (j\ne\tau).
\]

For half-integer `k+1/2`, define link reflection

\[
 \theta_{k+1/2}(x)_\tau=2k+1-x_\tau.
\]

A reflected positive edge may become negatively oriented. Therefore define reflection first on signed edges, prove source/target reversal relations, and only then define the induced action on positive-edge configurations using inversion when necessary.

Required geometry lemmas:

- site and link reflections are involutions on sites;
- induced signed-edge reflection is involutive;
- reflection sends paths to reflected paths with the correct order/orientation convention;
- reflected holonomy is the corresponding holonomy of reflected configuration;
- plaquettes map to plaquettes, possibly with reversed canonical orientation;
- symmetric boxes and their edge/plaquette partitions are stable under reflection;
- positive, negative, fixed, and crossing sets form the required disjoint unions.

Define the anti-linear reflection on observables by

\[
 (\Theta F)(A)=\overline{F(\theta A)}.
\]

Prove:

```lean
Theta_add
Theta_mul
Theta_smul_conj
Theta_conj
Theta_involutive
Theta_preserves_norm
```

---

## 18. Reflection positivity: abstract formulation

For a state `ω` and a positive-side algebra `A₊`, define

\[
 \operatorname{RP}(\omega,\Theta,A_+)
 \iff
 \forall F\in A_+,\quad
 \omega((\Theta F)F)\in\mathbb R_{\ge0}.
\]

In Lean it may be easiest to state:

```lean
∀ F, PositiveSupported F →
  Complex.im (ω (Theta F * F)) = 0 ∧
  0 ≤ Complex.re (ω (Theta F * F))
```

and later package this into a sesquilinear positive-semidefinite form.

Prove closure of positive-supported observables under algebra operations and clarify treatment of variables lying exactly in an integer reflection plane.

---

## 19. Integer/site-hyperplane reflection positivity

This is the reflection through a plane containing lattice sites.

### 19.1 Finite-volume decomposition

Begin with free boundary conditions on a reflection-symmetric box, so every edge read by the action is integrated. A later extension may allow explicitly reflection-invariant fixed boundary data. Split variables into

- positive-side variables `A₊`;
- negative-side variables `A₋=θA₊`;
- variables `A₀` lying in the reflection plane.

Decompose the Wilson action as

\[
 S=S_+ + \Theta S_+ + S_0,
\]

where `S₀` depends only on plane variables and is real.

Then for a positive-side observable `F`, Fubini and reflection invariance of product Haar give

\[
 \int (\Theta F)F e^S d\mu
 =\int e^{S_0(A_0)}
   \left|\int F(A_+,A_0)e^{S_+(A_+,A_0)}d\mu_+(A_+)\right|^2
   d\mu_0(A_0)\ge0.
\]

This proof should work without gauge fixing and, once the geometry is set correctly, for the full positive local algebra rather than only gauge-invariant observables.

### 19.2 Formalization tasks

1. prove a measurable equivalence/reindexing of the full finite configuration product into `(A₋,A₀,A₊)`;
2. prove product measure factorization under this equivalence;
3. prove the action decomposition plaquette by plaquette;
4. identify the negative-side integral with the complex conjugate of the positive-side integral;
5. conclude nonnegativity;
6. divide by the positive partition function.

Keep the unnormalized positivity lemma separate; normalized reflection positivity then follows immediately.

---

## 20. Half-integer/link-hyperplane reflection positivity

This reflection cuts links and is the subtler Osterwalder–Seiler argument.

### 20.1 Baseline theorem scope

First target reflection positivity on the gauge-invariant positive-time algebra. A later strengthening to all observables should be attempted only after checking the exact finite-volume formulation and whether the chosen gauge-fixing step preserves the required class.

### 20.2 Temporal gauge fixing

Choose a reflection-compatible forest consisting of crossing time-like edges and prove a finite tree-gauge lemma:

> For every gauge-invariant integrable function, integration against product Haar is unchanged if edge variables on the chosen forest are fixed to the identity and the redundant gauge variables are integrated out.

Prove this by leaf elimination on a finite rooted forest:

1. choose a leaf vertex and its parent edge;
2. change gauge variables to absorb the parent-edge value;
3. use Haar invariance;
4. remove that edge and vertex;
5. iterate.

This is a reusable finite gauge-fixing theorem and should live outside the reflection module.

### 20.3 Reflection-positive cone

Define the cone generated by finite sums of terms

\[
 f\,\Theta f
\]

with `f` positive-side. Prove it is closed under:

- addition with nonnegative real coefficients;
- multiplication;
- finite products;
- limits of uniformly convergent sequences, at least at the level needed for exponentials.

For a plaquette crossing the reflection plane, temporal gauge makes its holonomy have the form `g · θ(g)⁻¹` up to the fixed convention. Unitarity gives the matrix-coefficient factorization

\[
 \chi_\rho(g\theta(g)^{-1})
 =\sum_{i,j}\rho(g)_{ij}
   \overline{\rho(\theta(g))_{ij}}
 =\sum_{i,j} f_{ij}\Theta f_{ij}.
\]

Handle the real Wilson term by adding the orientation-reversed/conjugate character term. Therefore the cross-plane interaction lies in the reflection-positive cone.

Since `β≥0`, its exponential also lies in the cone by the power series with nonnegative coefficients. Multiplying by the purely positive and negative action factors preserves positivity.

### 20.4 Finite-volume theorem

Prove first for a reflection-symmetric finite volume with free boundary conditions and real `β≥0`:

```lean
theorem wilson_link_reflection_positive
    (F : LocalObservable ...)
    (hF : GaugeInvariant F)
    (hplus : SupportedInPositiveHalf F) :
  0 ≤ Complex.re (expectation Λ β ((Theta F) * F))
```

Also prove the expectation is real in this expression.

---

## 21. Infinite-volume reflection positivity

Once finite-volume reflection positivity and the unique local-state limit are available, the passage to infinite volume is short.

For a local positive-side `F`:

1. choose a nested sequence of symmetric boxes containing its support;
2. apply finite-volume reflection positivity in each box;
3. use convergence of the local observable `(ΘF)F`;
4. pass the real nonnegative inequality to the limit.

Produce separate theorems:

```lean
theorem infiniteVolume_site_reflection_positive ...
theorem infiniteVolume_link_reflection_positive ...
```

The link-reflection theorem should retain the gauge-invariance hypothesis if that is what the finite-volume proof establishes.

Translation invariance then transfers positivity from the planes at `0` and `1/2` to all integer and half-integer parallel hyperplanes.

---

## 22. Recommended milestone and pull-request sequence

Each milestone must compile with no placeholders and should update `STATUS.md` with:

- declarations completed;
- theorem names and files;
- exact remaining blockers;
- commands used to test;
- any conventions changed.

### Milestone 0 — Repository and Mathlib audit

**Tasks**

- pin Lean and Mathlib revisions;
- pin and build the exact current commits of `mrdouglasny/lgt`, `markov-semigroups`, and `gaussian-field`;
- create `DOUGLAS_REUSE_AUDIT.md` using Section 3A.4 and record licenses and provenance;
- inspect exact Haar, finite-product measure, compactness, continuous-representation, analytic-function, graph, Stone–Weierstrass, and Riesz–Markov APIs;
- create tiny `#check`/smoke-test files for both Mathlib and the imported Douglas declarations;
- run `#print axioms` on the Douglas mass-gap, Gibbs/DLR, and measure declarations selected for reuse;
- search the pinned Mathlib tree and upstream dependencies for existing polymer or cluster-expansion infrastructure;
- document every exact imported module and declaration to be reused.

**Exit criterion**

`lake build` succeeds for this project and for the pinned Douglas dependency stack; `STATUS.md` and `DOUGLAS_REUSE_AUDIT.md` record the audit. No theorem architecture should depend on guessed declaration names.

### Milestone 0A — Douglas compatibility baseline

**Tasks**

- add the chosen pinned dependency/submodule arrangement;
- create narrow adapters in `YangMills/Compat/`;
- import and re-export only the declarations selected in the reuse audit;
- prove a smoke theorem invoking `ym_mass_gap_exponential_decay` on its native periodic-torus model;
- prove at least one compatibility lemma between the upstream plaquette support/distance definitions and this project's planned interfaces;
- document every remaining specialization to periodic boundary conditions or plaquette observables.

**Exit criterion**

The upstream strong-coupling theorem compiles unchanged in a local regression file, its axiom footprint is checked, and no copied code lacks provenance. This milestone does not count as completion of the project-wide mass-gap theorem.

### Milestone 1 — Cubic lattice and paths

**Tasks**

- sites, positive/signed edges, source/target;
- plaquettes and their boundary words;
- paths, reversal, concatenation;
- translations;
- finite boxes.

**Exit criterion**

One-plaquette and rectangle boundaries compute definitionally or through short proved simp lemmas.

### Milestone 2 — Haar probability and finite products

**Tasks**

- `GaugeHaarProbability` interface;
- compact-group constructor;
- left/right/inversion invariance;
- finite product integration and coordinate reindexing;
- disjoint-coordinate integral factorization.

**Exit criterion**

A test theorem proves that independent Haar edge variables remain product Haar after a finite gauge transformation.

### Milestone 3 — Gauge action and holonomy

**Tasks**

- configurations;
- gauge action;
- path holonomy;
- covariance, loop conjugation, class-function invariance;
- local observable API.

**Exit criterion**

Gauge invariance of a one-plaquette class-function observable and a Wilson loop is fully proved.

### Milestone 4 — General finite-volume model

**Tasks**

- regions/specifications and exterior values;
- real potential;
- action, partition function, Gibbs expectation;
- positivity, normalization, integrability;
- finite-volume gauge invariance;
- complex finite-volume partition function and entire analyticity.

**Exit criterion**

The general finite-volume model works for arbitrary finite specifications and gives `Z(0)=1`.

### Milestone 5 — Wilson representation layer

**Tasks**

- continuous unitary representation wrapper;
- character identities and bounds;
- Wilson action and loops;
- center-phase data.

**Exit criterion**

Prove `|W(C)|≤1`, gauge invariance, and the center transformation law.

### Milestone 6 — Finite abstract polymer gas

**Tasks**

- compatible families;
- partition function;
- deletion recursion;
- ratio/nonvanishing estimate under a finite KP condition.

**Exit criterion**

A standalone example polymer model compiles and the nonvanishing theorem has no Yang–Mills imports.

### Milestone 7 — Connected clusters and analytic KP theorem

**Tasks**

- incompatibility graphs;
- connected graph sums;
- Ursell coefficients;
- exponential formula;
- tree-graph bound;
- marked clusters;
- analytic activity families.

**Exit criterion**

Obtain a theorem giving absolute convergence, nonvanishing, and analytic marked cluster sums under an explicit KP hypothesis.

### Milestone 8 — Plaquette polymer representation

**Tasks**

- plaquette adjacency and connected polymers;
- activity definition;
- exact factorization identity;
- activity bounds;
- boundary-locality of activities.

**Exit criterion**

Finite-volume Yang–Mills partition functions are exactly identified with the abstract polymer partition function.

### Milestone 9 — Lattice counting and strong-coupling criterion

**Tasks**

- adjacency degree bound;
- connected-animal count;
- geometric-series tails;
- explicit sufficient small-`β` theorem.

**Exit criterion**

A theorem with a concrete, nonzero strong-coupling radius discharges the abstract KP hypothesis uniformly in finite volume and boundary condition.

### Milestone 10 — Boundary decay

**Tasks**

- abstract polymer influence theorem;
- marked Yang–Mills expansion;
- distance conversion;
- exponential boundary sensitivity.

**Exit criterion**

Uniform boundary-condition sensitivity for every bounded local observable.

### Milestone 11 — Infinite-volume local state

**Tasks**

- nested boxes;
- Cauchy convergence;
- independence of boundary and sequence;
- positivity and invariances.

**Exit criterion**

A unique translation- and gauge-invariant state on local continuous observables.

### Milestone 12 — Infinite-volume measure

**Tasks**

- density of local real continuous functions;
- continuous extension;
- Riesz–Markov representation;
- agreement of measure integrals with the local state;
- optional DLR property and uniqueness.

**Exit criterion**

A regular Borel probability measure on the full configuration space represents the state.

### Milestone 13 — Exponential clustering

**Tasks**

- two-root cluster cancellation;
- finite-volume uniform covariance estimate;
- infinite-volume limit.

**Exit criterion**

The Euclidean mass-gap/exponential-clustering theorem is proved with explicit positive decay rate.

### Milestone 14 — Analyticity and pressure

**Tasks**

- locally uniform analytic local-state series;
- anchored cluster pressure;
- boundary/volume estimate;
- analytic thermodynamic pressure.

**Exit criterion**

Local expectations and pressure are analytic on an explicit complex disk.

### Milestone 15 — Center selection

**Tasks**

- center eigenfunction Haar lemma;
- Wilson Taylor expansion;
- finite-support cubical chains;
- charge-conservation selection rule;
- center filling area.

**Exit criterion**

Every nonzero Taylor term screening a charged loop has order at least its center filling area.

### Milestone 16 — Area law

**Tasks**

- defect marked-cluster bound;
- tail estimate from minimum filling order;
- rectangle filling-area comparison;
- infinite-volume charged Wilson-loop estimate.

**Exit criterion**

A strong-coupling area law for every explicitly supplied nontrivial center-charged Wilson representation, with a clean rectangle corollary.

### Milestone 17 — Site reflection positivity

**Tasks**

- integer reflection geometry;
- variable partition and product-measure equivalence;
- action decomposition;
- squared-modulus proof.

**Exit criterion**

Finite-volume site reflection positivity for the Wilson action at every `β≥0`.

### Milestone 18 — Link reflection positivity

**Tasks**

- half-integer geometry;
- finite forest gauge fixing;
- reflection-positive cone;
- matrix-coefficient factorization;
- exponential closure.

**Exit criterion**

Finite-volume link reflection positivity, at least on the gauge-invariant positive algebra, at every `β≥0`.

### Milestone 19 — Infinite-volume reflection positivity

**Tasks**

- symmetric cofinal boxes;
- limit passage;
- translation to all parallel integer/half-integer planes.

**Exit criterion**

Both reflection-positivity statements hold for the constructed strong-coupling infinite-volume state and measure.

### Milestone 20 — Optional OS reconstruction

**Tasks**

- OS quotient Hilbert space;
- time translations;
- transfer operator;
- spectral-gap consequence of exponential time clustering.

**Exit criterion**

A genuine Hamiltonian/transfer-operator spectral-gap theorem, clearly distinguished from the earlier Euclidean result.

---

## 23. High-risk points and fallback plans

### 23.1 Haar API friction

**Risk:** normalized right-invariant Haar probability is not available in exactly the desired packaged form.

**Fallback:** carry `GaugeHaarProbability` as explicit data throughout the general development and prove the compact-group constructor later. This does not weaken the finite-volume or cluster arguments.

### 23.2 No existing cluster-expansion library

**Risk:** the full Ursell/tree-graph formalization is the largest new generic component.

**Fallback:** first prove nonvanishing and influence decay by a finite deletion-recursion/Dobrushin induction. Then add explicit connected-cluster coefficients for analyticity and pressure. Do not block the model definition on the final cluster combinatorics.

### 23.3 Infinite-volume measure construction

**Risk:** extending a state on cylinder functions to all continuous functions may require nontrivial Stone–Weierstrass packaging.

**Fallback:** retain the local state as the principal infinite-volume object while separately formalizing the measure representation. All local physical consequences and reflection positivity can already be stated at the state level.

### 23.4 Representation theory

**Risk:** existing continuous representation APIs may not make matrix coefficients and trace estimates convenient.

**Fallback:** introduce a narrow wrapper around a continuous homomorphism into finite unitary matrices. Prove only trace, unitarity, conjugation, and center-scalar lemmas needed by Wilson theory. Avoid building Peter–Weyl theory.

### 23.5 Link-reflection gauge fixing

**Risk:** a monolithic temporal-gauge proof becomes unmanageable.

**Fallback:** first prove a general tree-gauge-fixing integral theorem by induction on a finite forest, with no reflections. Test it on a path and a star. Only then instantiate the reflection-compatible forest.

### 23.6 Geometric filling theory

**Risk:** general minimal surfaces in `ℤ^d` become a separate topology project.

**Fallback:** define the area law using the algebraically natural center filling area and prove the geometric equality only for coordinate rectangles and simple planar loops. This already captures the standard confinement statement.

### 23.7 Upstream version and abstraction mismatch

**Risk:** importing `lgt` pulls in a pinned Lean/Mathlib version and torus-specific abstractions that conflict with the general box/path APIs.

**Fallback:** keep `lgt` in a sibling regression workspace and port only isolated lemmas with Apache-2.0 attribution. Never weaken the general architecture merely to make its types definitionally equal to `LatticeLink` or `LatticePlaquette`. Use explicit equivalences and adapter lemmas.

### 23.8 Mistaking the Dobrushin baseline for the requested cluster expansion

**Risk:** because the imported theorem already proves exponential plaquette correlation decay, Codex may skip the polymer expansion or claim analyticity and area law without the required connected expansion.

**Fallback:** retain separate theorem manifests for `DobrushinBaseline` and `PolymerStrongCoupling`. The completion checklist for analyticity, pressure, and area law must depend on the polymer declarations, not merely on `ym_mass_gap_exponential_decay`.

### 23.9 Complex logarithms

**Risk:** branch management obscures the cluster proof.

**Fallback:** define `clusterLog` directly by its absolutely convergent connected series and prove its exponential equals the partition function. Never invoke an arbitrary global branch.

---

## 24. Codex operating protocol

For every milestone, Codex should follow this protocol.

1. **Audit before coding.** Use repository search and `#check` to identify exact current declarations and module paths. Never invent Mathlib names from memory. For overlapping finite-volume or Dobrushin work, search the pinned Douglas repositories before writing a new declaration.
2. **Preserve provenance.** Record the source file, commit, and Apache-2.0 attribution for any copied or adapted Douglas proof. Prefer imports and adapter lemmas.
3. **State conventions in the file header.** In particular: positive-edge convention, plaquette orientation, matrix multiplication order, action sign, and reflection pullback convention.
4. **Prove the smallest reusable lemma first.** Avoid a 1,000-line theorem proof with hidden local facts.
5. **Compile continuously.** Run the narrow target and then `lake build` after each coherent group of lemmas.
6. **No placeholders.** Do not commit `sorry`, `admit`, `by_contra!` without a completed proof, `unsafe` proof shortcuts, or additional axioms.
7. **No silent weakening.** If the requested theorem is blocked, preserve its statement in `STATUS.md`, prove the strongest honest intermediate result, and identify the exact missing lemma.
8. **Keep generic dependencies one-way.** `Polymer/` must not import `YangMills/StrongCoupling`; lattice geometry must not import probability theory unless necessary.
9. **Write executable examples.** Every major abstraction should have a finite test case.
10. **Document mathematical lemmas.** Each nontrivial theorem should have a docstring explaining its paper-level statement and role.
11. **Update `STATUS.md`.** Record successful commands, theorem names, remaining gaps, and changed conventions.

A good Codex task should be one milestone or a small portion of one milestone, not “formalize the entire strong-coupling theorem.”

---

## 25. First concrete Codex assignments

The first assignment should establish the reusable upstream baseline before new foundational code is written.

> Create `STATUS.md` and `DOUGLAS_REUSE_AUDIT.md`. Pin the exact commits of `mrdouglasny/lgt`, `markov-semigroups`, `gaussian-field`, Lean, and Mathlib, and build them unchanged. Locate and `#check` every declaration listed in Section 3A.4. Run `#print axioms` on `ymMeasure_isProbabilityMeasure`, `ymMeasure_isGibbs`, `ymDobrushinCondition`, `ym_mass_gap_exponential_decay`, and `ym_mass_gap_rate_exists`. Create a minimal regression module that imports and invokes the periodic-torus mass-gap theorem. For every candidate declaration, record whether it will be imported, wrapped, generalized, or rejected, and why. Do not copy source code during this assignment. Report exact version conflicts or missing declarations rather than guessing replacements.

The second assignment should implement the foundational path layer while reusing upstream plaquette calculations where appropriate.

> Create the initial modules for cubic-lattice sites, positive and signed edges, coordinate plaquettes, finite paths, and holonomy. Fix and document all orientation and multiplication conventions. Prove source/target formulas, signed-edge reversal involutivity, path concatenation and reversal formulas, the explicit four-edge plaquette boundary is closed, and holonomy of a reversed path is the inverse. Then define finite gauge transformations and prove path-holonomy covariance by induction. Add equivalence lemmas showing that, on a finite periodic torus, the new plaquette holonomy agrees with Douglas's `plaquetteHolonomy` under the selected edge/plaquette equivalence. Add a one-plaquette example and run `lake build`. Do not yet implement the polymer expansion or reflection positivity.

The third assignment should adapt or wrap the upstream normalized Haar/product measure and Gibbs gluing/DLR infrastructure. Only after these assignments compile should work begin on the general finite-volume box model and the polymer expansion.

---

## 26. Suggested regression tests

Maintain small examples that compile quickly.

1. **Douglas baseline:** the pinned regression module invokes `ym_mass_gap_exponential_decay` and has the recorded axiom footprint.
2. **Backtracking path:** holonomy of `e · e⁻¹` is `1`.
3. **One plaquette:** its boundary is closed and its holonomy transforms by conjugation.
4. **`β=0`:** partition function is `1`; disjoint edge observables factor under product Haar.
5. **Gauge change of variables:** finite product Haar is preserved.
6. **Two disconnected plaquette sets:** the corresponding perturbation integral factors.
7. **Single-polymer gas:** abstract partition function is `1+z` and deletion recursion is exact.
8. **Finite cyclic center selection:** a nontrivial character monomial integrates to zero.
9. **Rectangle chain:** boundary of the sum of enclosed plaquettes is the rectangle loop chain.
10. **Site reflection:** `F=1` and a simple cylinder function give a nonnegative reflected expectation.
11. **Link reflection:** one cross-plane plaquette character has the matrix-coefficient cone decomposition.

---

## 27. Mathlib audit checklist

On the pinned revision, inspect at least the following areas before implementation:

- `mrdouglasny/lgt`, `markov-semigroups`, and `gaussian-field`, including their exact commits, Lake package names, imports, licenses, and transitive Mathlib pins;
- the exact types and axiom footprints of the declarations listed in Section 3A.4;
- whether the Douglas `HasHaarProbability`, `HasGaugeTrace`, `GaugeConnection`, and torus geometry should be imported, wrapped, or replaced by more structured interfaces;
- Haar measure and uniqueness of Haar measure;
- normalized finite measures and probability measures;
- finite product measures and product integration/Fubini;
- compactness of arbitrary products;
- continuous maps and compact-open/sup-norm structures;
- finite-support functions and `Finsupp` over `ℤ`, `ZMod m`, and general additive groups;
- simple graph connectivity, spanning trees, and finite connected components;
- analytic functions and power series in normed algebras;
- complex exponential and factorial estimates;
- continuous finite-dimensional representations and unitary matrices;
- Stone–Weierstrass for real continuous functions;
- real Riesz–Markov–Kakutani representation;
- weak convergence/Portmanteau, in case the alternative measure route is used.

At the time this roadmap was prepared, current Mathlib documentation included Haar-measure, finite product-measure, analytic-function, continuous-representation, graph-connectivity, Portmanteau, and real Riesz–Markov components. No dedicated abstract polymer/cluster-expansion module was identified in the documentation audit, so that part should be treated as new infrastructure and checked again against the pinned source tree.

---

## 28. Theorem bundle to aim for

The signatures below are mathematical design targets, not exact Lean syntax.

```lean
-- Imported Douglas regression baseline
douglas_periodicTorus_massGap_regression
douglas_ymMeasure_isGibbs_regression

-- General model
finiteVolume_partition_pos
finiteVolume_expectation_norm_le
gaugeAction_preserves_productHaar
holonomy_gauge_covariant
finiteVolume_expectation_gauge_invariant

-- Polymer expansion
partition_eq_plaquettePolymerPartition
plaquetteActivity_norm_le
strongCoupling_koteckyPreiss
clusterSeries_absolutelyConvergent
partition_ne_zero_of_strongCoupling

-- Consequences
boundaryCondition_sensitivity_exp
infiniteVolume_localExpectation_exists
infiniteVolume_localExpectation_boundaryIndependent
infiniteVolume_measure_exists
infiniteVolume_measure_unique_DLR
truncatedCorrelation_exp_decay
localExpectation_analytic
pressure_exists
pressure_analytic

-- Center confinement
haarIntegral_eq_zero_of_centerCharge
wilsonTaylorTerm_chargeConservation
wilsonTerm_order_ge_centerFillingArea
wilsonLoop_areaLaw
rectangleWilsonLoop_areaLaw

-- Reflection positivity
siteReflection_action_decomposition
finiteVolume_site_reflection_positive
forestGaugeFixing_integral
crossPlaquette_mem_reflectionPositiveCone
finiteVolume_link_reflection_positive
infiniteVolume_site_reflection_positive
infiniteVolume_link_reflection_positive

-- Optional reconstruction
osTransferOperator_exists
osTransferOperator_spectralGap
```

---

## 29. Reference map

### Existing Lean implementation to reuse

- M. R. Douglas et al., [`mrdouglasny/lgt`](https://github.com/mrdouglasny/lgt), *Lattice Gauge Theory in Lean 4*. Inspect and pin an exact commit. As of 4 August 2026, the repository reports axiom-clean finite-periodic-torus Yang–Mills measures, Gibbs/DLR infrastructure, Dobrushin verification, and strong-coupling plaquette-correlation decay. The source is Apache-2.0 licensed and depends on `markov-semigroups` and `gaussian-field`. Treat it as the primary implementation baseline for overlapping finite-volume and Dobrushin work, subject to the reuse audit in Section 3A.

### Foundational lattice gauge theory and strong coupling

- E. Seiler, *Gauge Theories as a Problem of Constructive Quantum Field Theory and Statistical Mechanics*, Lecture Notes in Physics **159**, Springer, 1982. Use especially the setup of lattice gauge fields, expansion methods, thermodynamic-limit control, and constructive consequences. DOI: [10.1007/3-540-11559-5](https://doi.org/10.1007/3-540-11559-5).

- K. Osterwalder and E. Seiler, “Gauge Field Theories on a Lattice,” *Annals of Physics* **110** (1978), 440–471. This is the principal source for the lattice formulation, positivity properties, and strong-coupling construction. DOI: [10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8).

### Reflection through site hyperplanes

- P. Menotti and A. Pelissetto, “General proof of Osterwalder–Schrader positivity for the Wilson action,” *Communications in Mathematical Physics* **113** (1987), 369–373. Use this as the targeted supplement for planes containing lattice sites. DOI: [10.1007/BF01221251](https://doi.org/10.1007/BF01221251).

### Abstract polymer expansion

- R. Kotecký and D. Preiss, “Cluster expansion for abstract polymer models,” *Communications in Mathematical Physics* **103** (1986), 491–498. DOI: [10.1007/BF01211762](https://doi.org/10.1007/BF01211762).

The Lean proof need not reproduce the sharpest published constants. It should isolate a finite abstract theorem with explicit hypotheses and derive a safe cubic-lattice small-`β` criterion.

---

## 30. Definition of project completion

The project is complete at the requested level when:

- the Douglas reuse audit is complete, every imported or adapted declaration has pinned provenance, and the periodic-torus baseline theorem remains compiling as a regression test;
- all modules compile on a pinned Lean/Mathlib revision;
- no proof placeholders or additional axioms remain;
- a general compact-group finite-volume model and gauge invariance are formalized;
- the Wilson action is instantiated from explicit continuous unitary representation data;
- an exact plaquette-to-polymer identity and a proved small-`β` convergence criterion are present;
- boundary sensitivity, infinite-volume uniqueness, exponential clustering, and analyticity are proved;
- a charged-center Wilson-loop area law is proved, with at least a coordinate-rectangle geometric corollary;
- finite-volume integer- and half-integer-plane reflection positivity are proved in their correctly stated observable classes;
- both positivity statements pass to the strong-coupling infinite-volume state;
- `STATUS.md` accurately records theorem names, assumptions, constants, and any optional uncompleted reconstruction work.

A Hamiltonian spectral gap is an optional extension and should not be listed as complete unless the OS reconstruction and transfer-operator spectral theorem have actually been formalized.
