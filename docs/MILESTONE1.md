# Milestone 1: cubic lattice and paths

Milestone 1 supplies the geometry on which the finite-volume gauge theory will
be built. These modules are independent of `YangMills.Compat` and the periodic
Douglas model.

## Reused foundation

The project reuses Mathlib's `Quiver.Path` as its typed composable path. Thus
path endpoints and edge composability are enforced by Lean's type checker.
Concatenation is `Quiver.Path.comp`, reversal is `Quiver.Path.reverse`, and
translation uses `Prefunctor.mapPath`. Mathlib's pointwise locally finite order
on `Fin d → ℤ` supplies finite coordinate intervals.

## Public modules

| Module | Main declarations |
|---|---|
| `YangMills.Basic.OrientedPath` | `OrientedPath`, endpoint casts |
| `YangMills.Lattice.Cubic` | `Site`, `PositiveEdge`, `SignedEdge`, source/target, reversal, translations |
| `YangMills.Lattice.Path` | cubic `Path`, direction words, straight segments, translated paths |
| `YangMills.Lattice.Plaquette` | `Plaquette`, plaquette boundary, general rectangle boundary |
| `YangMills.Lattice.Box` | finite box sites and internal positive edges |
| `YangMills.Tests.Milestone1` | executable exit-criterion and axiom regressions |

## Fixed conventions

- `Site d` is `Fin d → ℤ`.
- A positive edge is identified by its source and positive coordinate axis.
- A signed edge records a source and signed direction, but
  `SignedEdge.positive` recovers the unique stored positive edge.
- Reversing a signed edge preserves that positive representative.
- A plaquette boundary traverses `+i`, `+j`, `-i`, `-j`.
- A box is an inclusive coordinate interval with a proof that its lower corner
  is at most its upper corner.

## Exit criterion

The following simp theorems are the executable boundary computations required
by the roadmap:

- `Plaquette.directions_boundary` computes the one-plaquette boundary to its
  signed four-edge word;
- `Path.directions_rectangleBoundary` computes an arbitrary rectangle to four
  replicated signed runs;
- `Path.rectangle_closes` proves that the constructed rectangle returns to its
  base site;
- `Path.length_rectangleBoundary` proves its perimeter formula.

`YangMills.Tests.Milestone1` verifies these declarations and prints their axiom
footprints. The build reports only `propext` and `Quot.sound` for the three key
boundary theorems.
