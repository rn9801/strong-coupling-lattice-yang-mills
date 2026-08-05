# Strong-Coupling Lattice Yang--Mills in Lean

This repository develops a Lean 4 formalization of constructive lattice
Yang--Mills theory at strong coupling. The long-term targets are a general
compact-group finite-volume model, a reusable polymer expansion, an
infinite-volume Gibbs state, exponential clustering, analyticity, charged
Wilson-loop area laws, and reflection positivity.

The project starts from a pinned, axiom-audited compatibility baseline with
Michael R. Douglas and collaborators' Apache-2.0-licensed
[`mrdouglasny/lgt`](https://github.com/mrdouglasny/lgt) development. The
periodic-torus Dobrushin theorem is retained as a regression result; it does not
replace the independent box, path, polymer, area-law, or reflection-positivity
work planned here.

## Status

Milestones 0 through 9 (including 0A) are complete; Milestone 10 (boundary
decay) is next. The repository now includes an independent
cubic-lattice geometry, normalized bi-invariant Haar probability, a genuine
gauge action, typed path holonomy with endpoint covariance, finitely supported
continuous observables, and a general finite-volume plaquette model with real
Gibbs expectations and an entire complex partition function. Continuous
unitary representations now supply bounded Wilson actions and loops with
explicit center-charge covariance. A standalone finite polymer gas, connected
cluster layer, exact plaquette-polymer representation, uniform lattice-animal
count, and explicit positive strong-coupling zero-free disk are now available.
See [`STATUS.md`](STATUS.md),
[`DOUGLAS_REUSE_AUDIT.md`](DOUGLAS_REUSE_AUDIT.md), and
[`docs/DOUGLAS_SCOPE.md`](docs/DOUGLAS_SCOPE.md) for exact progress, provenance,
and the boundary between reused periodic results and new project work.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake build
lake build YangMills.Audit.DouglasAxioms
```

The first build downloads pinned dependencies and Mathlib artifacts.

## Architecture

The source tree is organized by mathematical dependency:

```text
YangMills/
  Audit/       exact upstream and Mathlib API checks
  Compat/      narrow adapters to pinned external developments
  Baseline/    regression theorems in upstream models
  Basic/       finite gauge complexes, orientations, paths, holonomy
  Lattice/     cubic-lattice geometry, boxes, distance, reflection
  Gauge/       Haar probability, configurations, observables, Gibbs measures
  Wilson/      unitary representations, characters, center charge
  Polymer/     model-independent hard-core polymer expansion
  StrongCoupling/
  ReflectionPositivity/
  Examples/
  Tests/
```

Generic layers must not depend on later Yang--Mills-specific layers. In
particular, `Polymer/` will remain independent of `StrongCoupling/`.

## Standards

- pinned Lean, Mathlib, and upstream commits;
- no `sorry`, `admit`, custom axioms, or unsafe proof shortcuts;
- small reviewable modules with paper-level theorem docstrings;
- explicit provenance for imported or adapted results;
- narrow-target builds followed by `lake build`;
- honest theorem names: exponential clustering is not labeled a Hamiltonian
  spectral gap without an Osterwalder--Schrader reconstruction.

See the [detailed formalization roadmap](docs/DETAILED_ROADMAP.md),
the [Milestone 1 API summary](docs/MILESTONE1.md),
the [Milestone 2 API summary](docs/MILESTONE2.md),
the [Milestone 3 API summary](docs/MILESTONE3.md),
the [Milestone 4 API summary](docs/MILESTONE4.md),
the [Milestone 5 API summary](docs/MILESTONE5.md),
the [Milestone 6 API summary](docs/MILESTONE6.md),
the [Milestone 7 API summary](docs/MILESTONE7.md),
the [Milestone 8 API summary](docs/MILESTONE8.md),
the [Milestone 9 API summary](docs/MILESTONE9.md),
[`CONTRIBUTING.md`](CONTRIBUTING.md) for the development workflow, and
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for dependency rules. The project
is released under the [Apache License 2.0](LICENSE).
