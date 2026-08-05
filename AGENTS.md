# Repository instructions

## Goal

Formalize constructive strong-coupling lattice Yang--Mills theory in Lean 4,
following `docs/ROADMAP.md` and the exact progress in `STATUS.md`.

## Required workflow

- Audit Mathlib and pinned Douglas sources before introducing new APIs.
- Preserve Apache-2.0 provenance for imported or adapted upstream work.
- Fix conventions in file headers before proving dependent lemmas.
- Build the narrow target, then run `lake build`.
- Never add `sorry`, `admit`, custom axioms, or unsafe proof shortcuts.
- Update `STATUS.md` after every coherent milestone.

## Dependency rules

- `Polymer/` must remain independent of Yang--Mills modules.
- Core `Basic/`, `Lattice/`, `Gauge/`, and `Wilson/` modules must not depend on
  the Douglas compatibility layer.
- `Compat/` contains narrow adapters, never a copied upstream fork.
- Keep the Dobrushin baseline distinct from the polymer theorem family.

## Conventions

- Strong coupling is small `|β|` around `β = 0`.
- Cubic configurations store positive edges only; reversal uses group inverse.
- Real Gibbs measures and complex analytic functions are separate objects.
- "Mass gap" defaults to exponential clustering unless OS reconstruction is
  actually present.
