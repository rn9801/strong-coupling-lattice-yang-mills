# Dependency and build audit

Last updated: 2026-08-13.

## Purpose and method

This audit asks two different questions:

1. Which modules are on a dependency path to the project-native headline
   theorems through Milestone 17?
2. Which optional theorem families unnecessarily enlarged the default build?

The analysis parses local `import YangMills...` declarations and computes
their transitive closure.  Its native headline roots are:

- `StrongCoupling.CenteredInfiniteVolume`;
- `StrongCoupling.InfiniteVolumeMeasure`;
- `StrongCoupling.ThermodynamicCluster`;
- `StrongCoupling.ThermodynamicPressure`;
- `StrongCoupling.ThermodynamicAnalyticity`;
- `StrongCoupling.WilsonAreaLaw`;
- `Gauge.SiteReflectionPositivity`.

Import reachability is a conservative module-level test.  It shows that a
module is needed to elaborate a headline root, but it does not prove that
every declaration in that module occurs in a final kernel term.  The audit
therefore also parsed the generated `.ilean` declaration/reference data for
the existing production artifacts and followed the declarations printed by
the milestone axiom regressions.  This is stronger evidence, but tactic and
syntax dependencies can still be absent from `.ilean` declaration references;
every proposed deletion must therefore be confirmed by recompilation of all
reverse dependencies.

## Result

Of the 88 project-native production modules (excluding `Tests`, `Audit`,
`Baseline`, and `Compat`), 83 are transitively imported by the seven headline
roots.  The five outside that closure were:

| Module | Role | Decision |
|---|---|---|
| `Gauge.FiniteEdgeHaar` | Foundational finite-edge gauge-invariance theorem and Milestone 2 result | Keep in the public root |
| `Polymer.Influence` | Generic Neumann influence bound for the older comparison route | Keep, but regression-only |
| `StrongCoupling.AbstractBoundaryDecay` | Generic Dobrushin boundary comparison | Keep, but regression-only |
| `StrongCoupling.BoundaryDecay` | Finite-box Dobrushin boundary estimate | Keep, but regression-only |
| `StrongCoupling.BoxDobrushin` | Model-specific Dobrushin verification | Keep, but regression-only |

The four Dobrushin modules are proved, useful independent comparisons and
Milestone 10 artifacts.  They are not dead code, but they are not dependencies
of the cluster-expansion thermodynamic-limit, clustering, analyticity,
pressure, or area-law proofs.  They should not be deleted merely to improve
build time.

Running the same closure from all milestone tests, axiom audits, and baseline
roots reaches 108 of the 109 source modules.  The only exception is the
convenience umbrella `Compat.DouglasLGT`; its three narrow adapters are tested
directly.  The umbrella remains available for explicit compatibility users
but no longer belongs in the default public root.

At declaration level, all 219 distinct milestone `#print axioms` roots resolve
uniquely in the rebuilt artifacts, including all six Milestone 17 reflection
roots.  Their transitive declaration-reference closure reaches at least one
declaration in every one of the 88 project-native production modules.  A
smaller collection of terminal headline theorems for the thermodynamic limit,
clustering, analyticity, pressure, area law, gauge invariance, and Mayer/KP
theory reaches 1,726 of 2,465 production declarations.  The remaining
declarations include private helpers, stable intermediate APIs, and alternative
regression endpoints; they are not automatically dead code.

## Headline dependency chart

The chart suppresses many small combinatorial submodules but records the
important mathematical flow:

```text
Lattice geometry + Haar + gauge fields + finite specifications
                         │
                         ├── finite Gibbs measure and DLR
                         │
                         ├── Wilson representations, loops, and center charge
                         │
                         └── exact plaquette-subset expansion
                                      │
                                      ▼
                              plaquette polymers
                                      │
       generic Mayer normalization + Whitney tree graph + KP certificate
                                      │
                                      ▼
                 exact finite connected cluster expansion
                         │                         │
                         │                         ├── countable rooted clusters
                         │                         │          │
                         │                         │          └── analytic pressure
                         │                         │
                         ├── decorated one-root clusters
                         │          │
                         │          ├── boundary decay + Gibbs tower
                         │          │          │
                         │          │          └── infinite-volume measure
                         │          │                     │
                         │          │                     ├── gauge/translation invariance
                         │          │                     └── analytic local expectations
                         │          │
                         │          └── Wilson Taylor/source bounds
                         │                     │
                         │                     └── center selection + area law
                         │
                         └── bigraded two-root clusters
                                    │
                                    ├── connected support geometry
                                    └── exponential clustering

Site reflection geometry ── product-Haar split ── half-amplitude L² pairing
                                                     │
                                                     ├── reflection positivity
                                                     └── reflection Cauchy--Schwarz
```

The older comparison branch is independent of that chain:

```text
markov-semigroups influence matrices
        └── Polymer.Influence
              └── AbstractBoundaryDecay
                    └── BoxDobrushin + BoundaryDecay

pinned LGT
        └── Compat.Douglas{Geometry,Gibbs,Dobrushin}
              └── Baseline.PeriodicTorusMassGap
```

## Default and regression roots

Before this audit, `YangMills.lean` directly imported nearly every internal
module, the Douglas compatibility umbrella, the periodic-torus baseline, the
Mathlib smoke audit, and the older Dobrushin route.  Thus `lake build` treated
all of them as dependencies of the public root.

The public root now has four direct imports:

```text
YangMills
├── Gauge.FiniteEdgeHaar
├── Gauge.SiteReflectionPositivity
├── StrongCoupling.ThermodynamicPressure
└── StrongCoupling.WilsonAreaLaw
```

Their transitive closure contains 84 of the 88 native production modules and
all project-native headline results.  The separate `YangMills.Regression`
root imports:

- all milestone regression files;
- both audit modules;
- the Douglas periodic-torus baseline and compatibility umbrella;
- the older Dobrushin comparison route.

Recommended commands are therefore:

```sh
# Ordinary project-native build
lake build

# Comprehensive pre-merge or release regression
lake build +YangMills.Regression
```

This changes build reachability, not mathematical content.  No theorem or
proof module was deleted in this pass.

## Large modules and future cleanup

Several modules are large because they close genuinely long combinatorial or
analytic arguments.  The largest source/artifact pairs observed in this audit
were:

| Module | Source lines | `.olean` size |
|---|---:|---:|
| `StrongCoupling.MarkedComponentExpansion` | 4,228 | 4.56 MiB |
| `StrongCoupling.SpatialClusterExpansion` | 2,231 | 3.66 MiB |
| `Lattice.Counting` | 1,434 | 2.21 MiB |
| `StrongCoupling.SpatialClusterGeometry` | 1,536 | 1.80 MiB |
| `StrongCoupling.ThermodynamicCluster` | 1,821 | 1.75 MiB |
| `Polymer.LabelledTreeSummation` | 2,062 | 1.52 MiB |

Every one lies on a headline theorem path.  The two lowest-reach native
combinatorial modules were `RootedForestEnumeration` and
`RootedForestPartition`, but the declarations reached from them are essential
to the KP/tree proof.  These observations point to coherent file splits and
internal API cleanup, not deletion.

Two direct imports merit a future narrow-build experiment:
`FiniteClusterExpansion` imports `ObservableRootPolymer`, and
`ThermodynamicAnalyticity` imports `ClusterBoundaryExpansion`, while their
current `.ilean` files record no direct declaration reference to those
modules.  They may merely be transitive import sources; removing them in this
pass would be premature because declaration data does not record every
elaboration dependency.

Safe future cleanup should proceed in this order:

1. use Lean's declaration environment or generated documentation to record
   reverse declaration dependencies for a proposed deletion;
2. distinguish private proof helpers from stable public declarations;
3. move coherent baselines to clearly named modules before deleting them;
4. build every reverse-dependent narrow target;
5. run `lake build +YangMills.Regression`.

The current evidence supports import-root cleanup and documentation cleanup,
not wholesale deletion of cluster-expansion infrastructure.
