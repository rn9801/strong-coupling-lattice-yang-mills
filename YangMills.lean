/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Audit.MathlibSmoke
import YangMills.Baseline.PeriodicTorusMassGap
import YangMills.Compat.DouglasLGT
import YangMills.Gauge.ComplexFiniteVolume
import YangMills.Gauge.FiniteEdgeHaar
import YangMills.Gauge.Observable
import YangMills.Lattice.Box
import YangMills.Lattice.Plaquette
import YangMills.Polymer.Cluster
import YangMills.Polymer.Dobrushin
import YangMills.Polymer.FiniteGas
import YangMills.Polymer.Influence
import YangMills.Probability.FiniteProductGibbs
import YangMills.StrongCoupling.AbstractBoundaryDecay
import YangMills.StrongCoupling.BoundaryDecay
import YangMills.StrongCoupling.BoundaryGeometry
import YangMills.StrongCoupling.BoxDobrushin
import YangMills.StrongCoupling.BoxGibbs
import YangMills.StrongCoupling.Counting
import YangMills.StrongCoupling.MarkedExpansion
import YangMills.StrongCoupling.PlaquettePolymer
import YangMills.Wilson.Loop

/-!
# Strong-coupling lattice Yang--Mills theory

The root import for the project. Stable public modules should be added here only
after their dependencies and theorem statements have settled.
-/
