# Milestone 6: finite abstract polymer gas

Milestone 6 introduces a model-independent finite hard-core gas in
`YangMills.Polymer.FiniteGas`.  The module imports Mathlib only; in particular,
it has no dependency on the lattice, gauge, Wilson, or strong-coupling layers.

The public API provides:

- finite symmetric reflexive incompatibility models with complex activities;
- compatible families and restricted or full partition functions;
- exact deletion recursion;
- a finite deletion-ratio KP certificate;
- restricted and full nonvanishing theorems.

`YangMills.Tests.Milestone6` constructs a standalone one-polymer model and
checks its certificate and nonvanishing theorem.  The deletion-ratio condition
is intentionally finite and induction-ready.  Milestone 7 supplies the
connected-cluster estimates that turn explicit activity bounds into the
stronger analytic conclusions needed later.
