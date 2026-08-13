# Douglas LGT reuse audit

Audit date: 2026-08-04

The upstream project identifies its human authors as Michael R. Douglas, with
Fred Rajasekaran.  In this repository it is cited as: Michael R. Douglas and
Fred Rajasekaran, *Lattice Gauge Theory in Lean 4*, Apache-2.0, pinned at the
commit below.

The candidate/decision table records the Milestone 0 audit that guided the
subsequent implementation.  Present theorem status is documented in
`README.md` and `STATUS.md`; future-tense entries below are historical design
decisions, not a list of current gaps.

## Pinned upstream stack

| Repository | Commit | Package | License | Toolchain |
|---|---|---|---|---|
| `mrdouglasny/lgt` | `b8793ccf6a51e00e9e2b1685ba191b8626e37137` | `LGT` | Apache-2.0 | Lean 4.30.0 |
| `mrdouglasny/markov-semigroups` | `acf649108ea2222f4a8544a2782f448cb502492a` | `MarkovSemigroups` | Apache-2.0 | inherited |
| `mrdouglasny/gaussian-field` | `dc2b3b8378b2b7e33eaa8b61d6e943de11ff3f33` | `GaussianField` | Apache-2.0 | inherited |
| `leanprover-community/mathlib4` | `c5ea00351c28e24afc9f0f84379aa41082b1188f` | `mathlib` | Apache-2.0 | Lean 4.30.0 |

The roadmap mentioned Lean/Mathlib 4.29.0. Upstream `LGT` moved to 4.30.0 in
June 2026, so this project follows the current compatible stack.

## Candidate declarations

All candidates were imported unchanged during Milestone 0. The clean build and
axiom audit completed successfully. The exact elaborated types remain executable
documentation in `YangMills/Audit/DouglasAxioms.lean`; the table records the
architectural decisions that follow from those types.

| Declaration | Upstream file | Corresponding abstraction | Decision | Reason / remaining work |
|---|---|---|---|---|
| `LatticeLink` | `LGT/Lattice/CellComplex.lean` | positive periodic link | wrap | Regression geometry only; general boxes use `ℤ^d`. |
| `LatticePlaquette` | `LGT/Lattice/CellComplex.lean` | periodic coordinate plaquette | wrap | Prove an explicit torus equivalence after Milestone 1. |
| `boundaryLinks` | `LGT/Lattice/CellComplex.lean` | signed four-edge boundary | generalize | Upstream stores four positive links with signs handled in holonomy. |
| `plaquetteHolonomy` | `LGT/GaugeField/Connection.lean` | path holonomy on a plaquette | wrap | Prove equality with generic path holonomy on the torus. |
| `holonomy_gauge_covariant` | `LGT/GaugeField/Connection.lean` | path covariance | generalize | Reuse proof pattern; new theorem is by induction on paths. |
| `productHaar` | `LGT/MassGap/YMMeasure.lean` | finite product Haar | wrap | Audit assumptions and coordinate reindexing API. |
| `partitionFn` | `LGT/MassGap/YMMeasure.lean` | real finite-volume partition function | generalize | New API supports boxes, exterior data, and general potentials. |
| `ymMeasure` | `LGT/MassGap/YMMeasure.lean` | finite-volume Gibbs measure | generalize | Retain upstream theorem for periodic regression. |
| `ymMeasure_isProbabilityMeasure` | `LGT/MassGap/YMMeasure.lean` | probability normalization | wrap | High-value measure-theoretic plumbing. |
| `plaquetteHolonomy_dependsOn` | `LGT/MassGap/Locality.lean` | local-observable support | generalize | Extend from plaquettes to arbitrary finite paths. |
| `integral_mul_of_disjoint_dependsOn` | `LGT/MassGap/Locality.lean` | disjoint-coordinate factorization | wrap | Candidate generic product-measure lemma. |
| `gluedConfig` | `LGT/Gibbs/YMSpec.lean` | interior/exterior configuration glue | generalize | Adapt from a finite torus to arbitrary finite specifications. |
| `glue_measurePreserving` | `LGT/Gibbs/YMIsGibbs.lean` | gluing change of variables | wrap | Reuse where type-compatible; otherwise port with attribution. |
| `integral_glue_split_eq` | `LGT/Gibbs/YMIsGibbs.lean` | inside/outside Fubini identity | wrap | High-value DLR infrastructure. |
| `ymGibbsSpec` | `LGT/Gibbs/YMSpec.lean` | finite-volume Gibbs specification | generalize | Current declaration is periodic Wilson-specific. |
| `ymMeasure_isGibbs` | `LGT/Gibbs/YMIsGibbs.lean` | DLR consistency | wrap | Keep as a baseline and reuse proof architecture. |
| `ymDobrushinCondition` | `LGT/Gibbs/YMDobrushin.lean` | finite-volume mixing criterion | wrap | Independent early route to boundary mixing. |
| `linkGraphDist` | `LGT/Lattice/LatticeDistance.lean` | support graph distance | generalize | Port bounded-degree arguments to boxes and `ℤ^d`. |
| `linkGraphDist_support` | `LGT/MassGap/StrongCoupling.lean` | decay support theorem | wrap | Periodic regression theorem. |
| `boundary_sum_bound` | `LGT/MassGap/StrongCoupling.lean` | geometric boundary sum | wrap | Periodic geometry; compare later with box estimates. |
| `ym_mass_gap_exponential_decay` | `LGT/MassGap/StrongCoupling.lean` | periodic plaquette clustering | import | Axiom-audited regression baseline, not project completion. |
| `ym_mass_gap_rate_exists` | `LGT/MassGap/StrongCoupling.lean` | periodic exponential rate | import | Same scope limitation as the preceding theorem. |

## Axiom footprint

The executable audit is `YangMills/Audit/DouglasAxioms.lean`. A clean local build
on 2026-08-04 verified the following declarations:

| Declaration | Axiom footprint |
|---|---|
| `ymMeasure_isProbabilityMeasure` | `propext`, `Classical.choice`, `Quot.sound` |
| `ymMeasure_isGibbs` | `propext`, `Classical.choice`, `Quot.sound` |
| `ymDobrushinCondition` | `propext`, `Classical.choice`, `Quot.sound` |
| `ym_mass_gap_exponential_decay` | `propext`, `Classical.choice`, `Quot.sound` |
| `ym_mass_gap_rate_exists` | `propext`, `Classical.choice`, `Quot.sound` |
| `douglas_periodicTorus_massGap_regression` | `propext`, `Classical.choice`, `Quot.sound` |
| `douglas_ymMeasure_isGibbs_regression` | `propext`, `Classical.choice`, `Quot.sound` |

No project axiom or proof placeholder appears in these results.

Milestone 0A also verified the compatibility theorems below with the same
standard footprint:

| Declaration | Axiom footprint |
|---|---|
| `periodicPlaquetteSupportSet_eq_upstream` | `propext`, `Classical.choice`, `Quot.sound` |
| `periodicPlaquetteDistance_support_lowerBound` | `propext`, `Classical.choice`, `Quot.sound` |

## Compatibility boundaries

Milestone 0A split reuse into three narrow modules:

| Project adapter | Upstream area |
|---|---|
| `YangMills.Compat.DouglasGeometry` | periodic geometry, locality support, and distance |
| `YangMills.Compat.DouglasGibbs` | Haar measure, Yang--Mills measure, gluing, and DLR |
| `YangMills.Compat.DouglasDobrushin` | Dobrushin influence and periodic mass-gap results |

`YangMills.Compat.DouglasLGT` is a convenience umbrella only. Regression
modules import the narrowest adapter they need, and core layers do not import
`YangMills.Compat`. The specialization boundary is recorded in
`docs/DOUGLAS_SCOPE.md`.

## Polymer infrastructure search

A source search of the pinned Mathlib, `LGT`, `MarkovSemigroups`, and
`GaussianField` trees found no implementation of an abstract polymer gas,
Kotecky--Preiss criterion, Ursell coefficients, or a tree-graph bound. The
search therefore justified treating the `Polymer/` layer as new generic
infrastructure; that project-native layer has since been implemented.

## Provenance policy

- Prefer imports and adapter lemmas to copied source.
- Every adapted proof records repository, commit, file, and declaration in its
  file header.
- Apache-2.0 notices are retained for copied or substantially adapted source.
- `YangMills/Compat/` remains a narrow boundary, not a fork of `LGT`.
