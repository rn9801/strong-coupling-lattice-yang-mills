# Milestone 7: connected clusters and analytic finite KP

`YangMills.Polymer.Cluster` remains independent of the Yang--Mills layers and
adds the connected combinatorics required by finite-volume cluster arguments:

- ordered-tuple incompatibility graphs;
- signed connected spanning-graph sums (Ursell coefficients);
- vanishing on disconnected incompatibility graphs;
- a safe all-graph majorant and a conservative spanning-tree-indexed bound;
- analytic activity families and analytic partition functions;
- connected marked-family sums and their absolute summability;
- a normalized logarithm with an exact exponential formula on the KP
  zero-free domain;
- one theorem packaging nonvanishing, analyticity, absolute convergence, and
  marked-cluster analyticity under an explicit local Dobrushin--KP inequality.

The tree-indexed majorant encodes every connected spanning subgraph by a
contained spanning tree and the subgraph. It is deliberately weaker than the
optimized Penrose cancellation inequality, but it is a proved finite bound
with no hidden combinatorial assumption. `YangMills.Polymer.Dobrushin` proves
the explicit local deletion-ratio criterion used by the analytic package and
later quantitative layers.
