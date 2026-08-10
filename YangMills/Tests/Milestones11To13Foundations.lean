/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.ThermodynamicBoxes
import YangMills.Polymer.Mayer
import YangMills.StrongCoupling.FiniteClusterExpansion

/-! Executable regressions for the cluster-expansion thermodynamic-limit backbone. -/

open MeasureTheory

namespace YangMills.Tests

open Gauge Lattice.Cubic StrongCoupling

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

example (S : Finset (PositiveEdge d)) :
    ∃ N, ∀ n, N ≤ n → S ⊆ (centeredBox d n).positiveEdges :=
  finiteSupport_subset_centeredBox_eventually S

example {μ : ℕ → ProbabilityMeasure (Configuration d G)}
    (C : ClusterLimitCertificate μ) (F : LocalObservable d G) :
    ∫ A, F A ∂C.infiniteVolumeMeasure = C.localState F :=
  C.integral_infiniteVolumeMeasure F

example {sequence : ℕ → ProbabilityMeasure (Configuration d G)}
    (C : ClusterLimitCertificate sequence)
    (μ : Measure (Configuration d G)) [IsProbabilityMeasure μ]
    (hμ : ∀ F : LocalObservable d G, ∫ A, F A ∂μ = C.localState F) :
    μ = C.infiniteVolumeMeasure :=
  C.infiniteVolumeMeasure_unique μ hμ

example {μ ν : ℕ → ProbabilityMeasure (Configuration d G)}
    (Cμ : ClusterLimitCertificate μ) (Cν : ClusterLimitCertificate ν)
    (X : ClusterComparisonCertificate μ ν) (F : LocalObservable d G) :
    Cμ.localState F = Cν.localState F :=
  X.localState_eq Cμ Cν F

example {μ : ℕ → ProbabilityMeasure (Configuration d G)}
    (C : TwoRootClusterCertificate μ) (F H : LocalObservable d G) :
    ‖C.toClusterLimitCertificate.stateTruncatedCorrelation F H‖ ≤
      C.prefactor * ‖F.toBoundedContinuousMap‖ *
        ‖H.toBoundedContinuousMap‖ *
        (F.support.card : ℝ) * (H.support.card : ℝ) *
        Real.exp (-C.clusteringMass *
          (C.supportDistance F.support H.support : ℝ)) :=
  C.exponential_clustering_exp F H

#print axioms YangMills.StrongCoupling.finiteSupport_subset_centeredBox_eventually
#print axioms YangMills.StrongCoupling.ClusterLimitCertificate.localState_add
#print axioms YangMills.StrongCoupling.ClusterLimitCertificate.integral_infiniteVolumeMeasure
#print axioms YangMills.StrongCoupling.ClusterLimitCertificate.infiniteVolumeMeasure_unique
#print axioms YangMills.StrongCoupling.ClusterComparisonCertificate.localState_eq
#print axioms YangMills.Polymer.FinitePolymerModel.mayerClusterTerm_scaleActivityAt_scaleActivityAt
#print axioms YangMills.Polymer.FinitePolymerModel.exp_finiteMayerSum_eq_partitionFunction_of_dobrushin
#print axioms YangMills.Polymer.FinitePolymerModel.norm_pinnedPartitionRatio_le_of_dobrushin
#print axioms YangMills.StrongCoupling.exp_plaquetteFiniteMayerSum_eq_complexPartitionFunction
#print axioms YangMills.StrongCoupling.plaquetteWeightedPinnedTreeBound
#print axioms YangMills.StrongCoupling.twoObservableRootModel_distinct_roots_compatible
#print axioms YangMills.StrongCoupling.twoObservable_connectedCoefficient
#print axioms YangMills.StrongCoupling.TwoRootClusterCertificate.exponential_clustering_exp

end

end YangMills.Tests
