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
import YangMills.Polymer.FiniteMayer
import YangMills.Polymer.FiniteGas
import YangMills.Polymer.GraphExponential
import YangMills.Polymer.Influence
import YangMills.Polymer.KoteckyPreiss
import YangMills.Polymer.LabelledMayerExponential
import YangMills.Polymer.LabelledRootedForestSpecies
import YangMills.Polymer.LabelledTreeSummation
import YangMills.Polymer.Mayer
import YangMills.Polymer.MayerNormalization
import YangMills.Polymer.MayerPowerSeries
import YangMills.Polymer.Penrose
import YangMills.Polymer.PowerSeriesLog
import YangMills.Polymer.RootedForestEnumeration
import YangMills.Polymer.RootedForestPartition
import YangMills.Polymer.RootedTreeDecomposition
import YangMills.Polymer.SourcePowerSeries
import YangMills.Polymer.BivariateSourcePowerSeries
import YangMills.Polymer.BigradedSource
import YangMills.Polymer.TwoRootSource
import YangMills.Polymer.WeightedOrderedPartition
import YangMills.Polymer.Whitney
import YangMills.Polymer.Augmented
import YangMills.Probability.FiniteProductGibbs
import YangMills.StrongCoupling.AbstractBoundaryDecay
import YangMills.StrongCoupling.BoundaryDecay
import YangMills.StrongCoupling.BoundaryGeometry
import YangMills.StrongCoupling.BoxDobrushin
import YangMills.StrongCoupling.BoxGibbs
import YangMills.StrongCoupling.ClusterState
import YangMills.StrongCoupling.CenteredBoundaryExpansion
import YangMills.StrongCoupling.CenteredClusterGeometry
import YangMills.StrongCoupling.CenteredInfiniteVolume
import YangMills.StrongCoupling.ClusterBoundaryExpansion
import YangMills.StrongCoupling.Counting
import YangMills.StrongCoupling.ExponentialClustering
import YangMills.StrongCoupling.FiniteSpecificationGibbsTower
import YangMills.StrongCoupling.InfiniteVolumeMeasure
import YangMills.StrongCoupling.ObservableRootPolymer
import YangMills.StrongCoupling.FiniteClusterExpansion
import YangMills.StrongCoupling.MarkedExpansion
import YangMills.StrongCoupling.MarkedComponentExpansion
import YangMills.StrongCoupling.PlaquettePolymer
import YangMills.StrongCoupling.SpatialClusterExpansion
import YangMills.StrongCoupling.SpatialClusterGeometry
import YangMills.StrongCoupling.ThermodynamicBoxes
import YangMills.Wilson.Loop

/-!
# Strong-coupling lattice Yang--Mills theory

The root import for the project. Stable public modules should be added here only
after their dependencies and theorem statements have settled.
-/
