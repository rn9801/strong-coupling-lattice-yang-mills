# Milestone 10: boundary decay

Status: complete.

## Completed foundation

| Module | Result |
|---|---|
| `YangMills.Polymer.Influence` | Marked root/defect influence certificates and a finite-range Neumann bound with decay `α^r / (1-α)`; the whole defect set is controlled without a boundary-cardinality factor. |
| `YangMills.StrongCoupling.MarkedExpansion` | Complex local-observable numerator and expectation, exact marked plaquette-subset expansion, sup-norm marked-weight bound, and marked exterior locality. |
| `YangMills.StrongCoupling.BoundaryGeometry` | Exact observable-root and boundary-disagreement sets, the uniform `4d |support(F)|` root count, equality away from the defect set, and connected-set graph-distance conversion. |

The abstract Neumann backend is reused from the pinned Apache-2.0
`markov-semigroups` dependency.  The new polymer-facing wrapper is independent
of all Yang--Mills modules.

## Completed exit bridge

The milestone is completed through the roadmap's compact-spin Dobrushin route.
`YangMills.Probability.FiniteProductGibbs` constructs a genuine finite-product
Gibbs specification and proves its DLR equations.  The construction and its
gluing proof are adapted from Michael R. Douglas' Apache-2.0 LGT development.

`YangMills.StrongCoupling.BoxDobrushin` proves finite-range one-edge influence,
at most `16d` interacting edge neighbors, both Dobrushin row and column bounds,
and the explicit positive radius `boxDobrushinRadius`.  Its contraction
constant is `boxDobrushinAlpha`, algebraically
`256 d² ‖Φ‖∞ |β|`.

`YangMills.StrongCoupling.BoundaryDecay` then identifies the exact dynamic
defect edges, proves the two singleton specifications coincide off that set,
and declares `complexGibbsExpectation_boundaryDecay`.  For observable support
`R`, defect set `D`, and interaction-graph separation at least `r`, it gives

```text
‖⟨F⟩η - ⟨F⟩η'‖
  ≤ 4 ‖F‖∞ |support(F)| α^r / (1-α).
```

The prefactor is uniform in the volume and has no `|D|` factor.  The marked
polymer foundations remain available for a later genuine Ursell/tree-graph
implementation; the earlier audit correctly prevents treating the current
Milestone 7 connected-family API as that missing identity.
