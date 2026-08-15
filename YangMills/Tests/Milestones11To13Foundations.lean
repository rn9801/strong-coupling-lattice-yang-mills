/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.ThermodynamicBoxes
import YangMills.Polymer.Mayer
import YangMills.Polymer.MayerNormalization
import YangMills.Polymer.MayerPowerSeries
import YangMills.Polymer.Penrose
import YangMills.Polymer.Whitney
import YangMills.Polymer.LabelledRootedForestSpecies
import YangMills.Polymer.LabelledMayerExponential
import YangMills.Polymer.LabelledTreeSummation
import YangMills.Polymer.PowerSeriesLog
import YangMills.Polymer.RootedForestEnumeration
import YangMills.Polymer.RootedForestPartition
import YangMills.Polymer.RootedTreeDecomposition
import YangMills.StrongCoupling.FiniteClusterExpansion
import YangMills.StrongCoupling.MarkedComponentExpansion
import YangMills.StrongCoupling.SpatialClusterExpansion
import YangMills.StrongCoupling.SpatialClusterGeometry
import YangMills.StrongCoupling.CenteredBoundaryExpansion
import YangMills.StrongCoupling.CenteredClusterGeometry
import YangMills.StrongCoupling.CenteredInfiniteVolume

/-! Executable regressions for the cluster-expansion thermodynamic-limit backbone. -/

-- Axiom-audit commands below use fully qualified theorem names that cannot be
-- split internally without changing the identifiers being checked.
set_option linter.style.longLine false

open MeasureTheory

namespace YangMills.Tests

open Gauge Lattice.Cubic StrongCoupling
open YangMills.Polymer

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

example (S : Finset (PositiveEdge d)) :
    ∃ N, ∀ n, N ≤ n → S ⊆ (centeredBox d n).positiveEdges :=
  finiteSupport_subset_centeredBox_eventually S

example (F : LocalObservable d G) (r : ℕ) :
    ∃ N, ∀ n, N ≤ n → ∀ η η' : Configuration d G,
      F.support ⊆ (centeredSpecification n η).dynamicEdges ∧
      ∀ p ∈ boundaryDisagreementPlaquettes
          (centeredSpecification n η) η η',
        (bivariateObservableSpatialGraph F F
          (centeredSpecification n η)).Reachable
            (Sum.inr 0) (Sum.inl p) →
          r + 1 ≤ (bivariateObservableSpatialGraph F F
            (centeredSpecification n η)).dist
              (Sum.inr 0) (Sum.inl p) :=
  centered_boundaryDisagreement_distance_eventually F r

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

example (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound) :
    IsProbabilityMeasure (centeredInfiniteVolumeMeasure η Φ β hβ) :=
  inferInstance

example (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound) :
    (centeredInfiniteVolumeMeasure η Φ β hβ).Regular :=
  inferInstance

example (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (g : GaugeTransformation d G) :
    Measure.map (gaugeTransform g)
        (centeredInfiniteVolumeMeasure η Φ β hβ) =
      centeredInfiniteVolumeMeasure η Φ β hβ :=
  centeredInfiniteVolumeMeasure_map_gaugeTransform η Φ β hβ g

example (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (g : GaugeTransformation d G) :
    MeasurePreserving (gaugeTransform g)
      (centeredInfiniteVolumeMeasure η Φ β hβ)
      (centeredInfiniteVolumeMeasure η Φ β hβ) :=
  centeredInfiniteVolumeMeasure_measurePreserving_gaugeTransform η Φ β hβ g

#print axioms YangMills.StrongCoupling.finiteSupport_subset_centeredBox_eventually
#print axioms YangMills.StrongCoupling.ClusterLimitCertificate.localState_add
#print axioms YangMills.StrongCoupling.ClusterLimitCertificate.integral_infiniteVolumeMeasure
#print axioms YangMills.StrongCoupling.ClusterLimitCertificate.infiniteVolumeMeasure_unique
#print axioms YangMills.StrongCoupling.ClusterComparisonCertificate.localState_eq
#print axioms YangMills.Polymer.FinitePolymerModel.mayerClusterTerm_scaleActivityAt_scaleActivityAt
#print axioms YangMills.Polymer.FinitePolymerModel.mayerUrsellGraph_eq_moebius_cancellation
#print axioms YangMills.Polymer.FinitePolymerModel.labelledMayerDegreeSum_eq_symmetricMayerDegreeSum
#print axioms
  FinitePolymerModel.natCast_div_mayerSymmetryFactor_eq_inv_pinned
#print axioms
  FinitePolymerModel.sum_pinnedSymmetricMayerDegreeSum
#print axioms YangMills.Polymer.GraphPenroseScheme.abs_connectedSpanningGraphSum_le_card_trees
#print axioms YangMills.Polymer.Whitney.abs_connectedSpanningGraphSum_le_card_trees
#print axioms YangMills.Polymer.FinitePolymerModel.norm_mayerClusterTerm_le_mayerTreeMajorant
#print axioms YangMills.Polymer.FinitePolymerModel.pinned_norm_mayerClusterTerm_le_tree
#print axioms FinitePolymerModel.sum_pinnedNormMayerDegreeSum
#print axioms FinitePolymerModel.summable_normMayerDegreeSum_succ_of_pinned
#print axioms YangMills.Polymer.FinitePolymerModel.hasSum_kpMayerForestDegreeSum
#print axioms
  YangMills.Polymer.FinitePolymerModel.card_graphSpanningTrees_eq_of_iso
#print axioms
  YangMills.Polymer.FinitePolymerModel.card_labelingsWithHistogram_eq_countPerms
#print axioms
  YangMills.Polymer.FinitePolymerModel.factorialNormalizedLabelledPinnedTreeDegreeSum_eq_residual
#print axioms YangMills.Polymer.range_orderedAwayComponentPartition_emb
#print axioms YangMills.Polymer.orderedAwayComponentGraph_isTree
#print axioms
  YangMills.Polymer.FinitePolymerModel.orderedAwayComponentGraph_mem_graphSpanningTrees
#print axioms
  YangMills.Polymer.FinitePolymerModel.factorialNormalizedLabelledAttachedComponentDegreeSum_succ
#print axioms
  YangMills.Polymer.FinitePolymerModel.labelledRootedTreeRecurrence_iff_orbitRecurrence
#print axioms YangMills.Polymer.sum_factorialNormalized_orderedFinpartitionWeight_le_exp
#print axioms
  YangMills.Polymer.FinitePolymerModel.fixedLabelledRootedTreeToForestCode_injective
#print axioms
  YangMills.Polymer.FinitePolymerModel.sum_fixedLabelledRootedForestCodeWeight
#print axioms
  YangMills.Polymer.FinitePolymerModel.labelledRootedTreeRecurrence
#print axioms
  YangMills.Polymer.FinitePolymerModel.rootedTreeOrbitBound
#print axioms
  YangMills.Polymer.FinitePolymerModel.summable_normMayerDegreeSum_succ_of_koteckyPreiss_certified
#print axioms
  YangMills.Polymer.FinitePolymerModel.restrictedSymmetricMayerPowerSeries_eq_formalMayerLog
#print axioms
  YangMills.Polymer.FinitePolymerModel.fixedLabelledPinnedTreeOrbitDegreeSum_eq_residual
#print axioms
  YangMills.Polymer.FinitePolymerModel.pinnedMayerTreeDegreeSum_succ_eq_residual
#print axioms
  YangMills.Polymer.FinitePolymerModel.summable_normMayerDegreeSum_succ_of_koteckyPreiss
#print axioms
  YangMills.Polymer.FinitePolymerModel.tsum_kpMayerForestDegreeSum_le_exp_of_koteckyPreiss
#print axioms YangMills.Polymer.PowerSeriesBridge.expOf_logOf
#print axioms YangMills.Polymer.PowerSeriesBridge.logOf_expOf
#print axioms YangMills.Polymer.IsTree.existsUnique_adj_root_in_awayComponent
#print axioms YangMills.Polymer.IsTree.rootDecomposition
#print axioms YangMills.Polymer.rootedGraphEquiv
#print axioms YangMills.Polymer.card_validComponentAttachmentFinsets
#print axioms YangMills.Polymer.sum_rootedForestData_eq_sum_forest_prod_component
#print axioms YangMills.Polymer.forestComponentData_injective
#print axioms
  YangMills.Polymer.sum_spanningForestGraphsAway_le_sum_treeComponentFamiliesBelow
#print axioms
  YangMills.Polymer.sum_treeComponentFamiliesBelow_prod_le_exp_sum
#print axioms
  YangMills.Polymer.sum_rootedForestData_vertex_attachment_prod_le_exp
#print axioms
  YangMills.Polymer.card_spanningTreeGraphs_mul_prod_away_le_exp
#print axioms
  YangMills.Polymer.card_spanningTreeGraphs_mul_prod_away_le_exp_rootedChoices
#print axioms
  YangMills.Polymer.FinitePolymerModel.sum_mayerChildMultiIndex_add_root
#print axioms
  YangMills.Polymer.FinitePolymerModel.histogramWeight_mayerChild_factorization
#print axioms
  YangMills.Polymer.FinitePolymerModel.kpChildWeight_childRoot_eq
#print axioms
  YangMills.Polymer.FinitePolymerModel.pinned_norm_mayerClusterTerm_le_componentTreeExp
#print axioms
  YangMills.Polymer.FinitePolymerModel.mayerSpanningTree_residual_le_exp_rootedChoices
#print axioms
  YangMills.Polymer.FinitePolymerModel.expOf_formalMayerLog_eq_partitionPowerSeries
#print axioms
  FinitePolymerModel.sum_partitionDegreeCoefficient_range
#print axioms
  FinitePolymerModel.restrictedSymmetricMayerPowerSeries_eq_formalMayerLog_of_expOf_eq
#print axioms
  YangMills.Polymer.FinitePolymerModel.exp_finiteMayerSum_eq_partitionFunction_of_dobrushin
#print axioms YangMills.Polymer.FinitePolymerModel.tsum_norm_mayerInsertionTerm_le_of_dobrushin
#print axioms YangMills.Polymer.FinitePolymerModel.norm_pinnedPartitionRatio_le_of_dobrushin
#print axioms YangMills.StrongCoupling.exp_plaquetteFiniteMayerSum_eq_complexPartitionFunction
#print axioms YangMills.StrongCoupling.plaquetteWeightedPinnedTreeBound
#print axioms YangMills.StrongCoupling.plaquettePolymerModel_koteckyPreiss_of_norm_lt_latticeRadius
#print axioms YangMills.StrongCoupling.tsum_plaquetteKPTreeLayer_le
#print axioms YangMills.StrongCoupling.summable_plaquetteNormMayerDegreeSum_succ
#print axioms YangMills.StrongCoupling.plaquetteWeightedPinnedTreeOrbitBound
#print axioms
  YangMills.StrongCoupling.plaquetteRestrictedSymmetricMayerPowerSeries_eq_formalMayerLog
#print axioms YangMills.StrongCoupling.plaquetteAbsolutePinnedMayerSeriesBound
#print axioms YangMills.StrongCoupling.twoObservableRootModel_distinct_roots_compatible
#print axioms
  YangMills.Polymer.FinitePolymerModel.koteckyPreissCertificate_augmentRoots_zero
#print axioms
  YangMills.Polymer.FinitePolymerModel.koteckyPreissCertificate_augmentExclusiveRoots_zero
#print axioms
  YangMills.Polymer.FinitePolymerModel.augmentExclusiveRoots_partitionFunction
#print axioms
  YangMills.Polymer.FinitePolymerModel.mayerClusterTerm_augmentExclusiveRoots_mul
#print axioms
  YangMills.Polymer.FinitePolymerModel.symmetricMayerDegreeSum_augmentExclusiveRoots_mul
#print axioms
  YangMills.Polymer.FinitePolymerModel.norm_exclusiveRootLinearMayerDegreeSum_succ_le
#print axioms YangMills.StrongCoupling.oneObservableRootModel_koteckyPreiss_zero
#print axioms YangMills.StrongCoupling.twoObservableRootModel_koteckyPreiss_zero
#print axioms
  YangMills.StrongCoupling.oneObservableRootKPWeight_root_le_support
#print axioms
  YangMills.StrongCoupling.twoObservableRootKPWeight_first_root_le_support
#print axioms
  YangMills.StrongCoupling.twoObservableRootKPWeight_second_root_le_support
#print axioms
  YangMills.StrongCoupling.oneObservableRootModel_restrictedSymmetricMayerPowerSeries_eq_formalMayerLog
#print axioms
  YangMills.StrongCoupling.twoObservableRootModel_restrictedSymmetricMayerPowerSeries_eq_formalMayerLog
#print axioms
  YangMills.StrongCoupling.oneObservableRootModel_tsum_kpMayerForestDegreeSum_le
#print axioms
  YangMills.StrongCoupling.twoObservableRootModel_tsum_kpMayerForestDegreeSum_le
#print axioms
  YangMills.StrongCoupling.oneObservableRootModel_tsum_residualSymmetricPinnedTreeDegreeSum_le_support
#print axioms
  YangMills.StrongCoupling.twoObservableRootModel_first_tsum_residualSymmetricPinnedTreeDegreeSum_le_support
#print axioms
  YangMills.StrongCoupling.twoObservableRootModel_second_tsum_residualSymmetricPinnedTreeDegreeSum_le_support
#print axioms YangMills.StrongCoupling.oneObservableRootModel_pinnedTreeBound
#print axioms YangMills.StrongCoupling.twoObservableRootModel_pinnedTreeBound
#print axioms YangMills.StrongCoupling.twoObservable_connectedCoefficient
#print axioms
  YangMills.Polymer.BivariateSourcePowerSeries.mixedCoefficient_expOf
#print axioms
  YangMills.Polymer.FinitePolymerModel.expOf_twoRootSourceMayerPowerSeries
#print axioms
  YangMills.Polymer.FinitePolymerModel.coeff_mixedCoefficient_twoRootSourceMayerPowerSeries
#print axioms
  YangMills.Polymer.FinitePolymerModel.twoRootMixed_nonzero_connected_nonadjacent
#print axioms
  YangMills.Polymer.FinitePolymerModel.twoRootMixedPartitionCoefficient_eq_vacuum_mul_connected
#print axioms
  YangMills.Polymer.FinitePolymerModel.twoRootMixedMayerTreeDegreeSum_add_two
#print axioms
  YangMills.Polymer.FinitePolymerModel.norm_twoRootMixedMayerDegreeSum_le_scaled
#print axioms
  YangMills.Polymer.FinitePolymerModel.summable_norm_twoRootMixedMayerDegreeSum_succ_of_scaled
#print axioms
  YangMills.StrongCoupling.twoObservableRootSource_mixedCoefficient
#print axioms
  YangMills.StrongCoupling.plaquettePolymerModel_kp_incompatible_sum_le_quarter
#print axioms
  YangMills.StrongCoupling.twoObservableRootModel_koteckyPreiss_regularized
#print axioms
  YangMills.StrongCoupling.twoObservableRootModel_regularized_summable_pinnedMayerTreeDegreeSum_succ
#print axioms
  YangMills.StrongCoupling.twoObservableRootModel_summable_norm_twoRootMixedMayerDegreeSum_succ
#print axioms
  YangMills.StrongCoupling.twoObservableRootModel_mixedMayerTreeDegreeSum_add_two
#print axioms
  YangMills.StrongCoupling.twoObservableRootModel_mixedPartitionCoefficient_eq_vacuum_mul_connected
#print axioms
  YangMills.StrongCoupling.summable_norm_decoratedObservableTruncatedMayerDegreeSum
#print axioms
  YangMills.StrongCoupling.complexGibbsTruncatedCorrelation_eq_tsum_decoratedCumulant
#print axioms
  YangMills.Polymer.FinitePolymerModel.expOf_bigradedSourceMayerPowerSeries
#print axioms
  YangMills.Polymer.FinitePolymerModel.bigradedPartitionCoefficients_eq_connected
#print axioms
  YangMills.StrongCoupling.bivariateDecoratedObservableRootModel_partitionFunction
#print axioms
  YangMills.StrongCoupling.bivariateDecoratedObservableRootModel_koteckyPreiss_regularized
#print axioms
  YangMills.StrongCoupling.bivariateDecorated_mixed_nonzero_spanning_witness
#print axioms
  YangMills.StrongCoupling.complexGibbsTruncatedCorrelation_eq_tsum_bivariateDecoratedMixed
#print axioms
  YangMills.StrongCoupling.markedSubsetWeight_eq_rootComponentWeight_mul_awayFamilyWeight
#print axioms
  YangMills.StrongCoupling.complexObservableNumerator_eq_sum_rootComponentWeight_mul_awayFamilyWeight
#print axioms
  YangMills.StrongCoupling.decoratedObservableRootCoefficient_eq_complexObservableNumerator
#print axioms
  YangMills.StrongCoupling.decoratedObservableSourcePartition_eq_oneObservableSourcePartition
#print axioms
  YangMills.StrongCoupling.decoratedObservableRootModel_partitionFunction
#print axioms
  YangMills.StrongCoupling.decoratedObservableRootModel_partitionFunction_eq_oneObservableSourcePartition
#print axioms
  YangMills.StrongCoupling.decoratedObservableRootModel_mayerClusterTerm_source
#print axioms
  YangMills.StrongCoupling.decoratedObservableRootModel_symmetricMayerDegreeSum_source
#print axioms
  YangMills.StrongCoupling.decoratedObservableRootModel_koteckyPreiss_zero
#print axioms
  YangMills.StrongCoupling.decoratedObservableRootKPWeight_root_le_support_add_decoration
#print axioms
  YangMills.StrongCoupling.sum_observableRoot_tiltedAnimalWeight_le
#print axioms
  YangMills.StrongCoupling.sum_norm_markedSubsetWeight_mul_exp_decoratedRootKPWeight_le
#print axioms
  YangMills.StrongCoupling.decoratedObservableRootModel_tsum_residualSymmetricPinnedTreeDegreeSum_le
#print axioms
  YangMills.StrongCoupling.norm_decoratedObservableRootLinearMayerDegreeSum_succ_le
#print axioms
  YangMills.StrongCoupling.summable_norm_decoratedObservableRootLinearMayerDegreeSum_succ
#print axioms
  YangMills.StrongCoupling.tsum_norm_decoratedObservableRootLinearMayerDegreeSum_succ_le
#print axioms
  YangMills.Polymer.SourcePowerSeries.sourceDerivative_expOf
#print axioms
  YangMills.Polymer.FinitePolymerModel.expOf_exclusiveRootSourceMayerPowerSeries
#print axioms
  YangMills.Polymer.FinitePolymerModel.linearCoefficient_exclusiveRootSourcePartitionPowerSeries
#print axioms
  YangMills.Polymer.FinitePolymerModel.exclusiveRootPartitionCoefficient_eq_partitionFunction_mul_tsum
#print axioms
  YangMills.StrongCoupling.complexObservableNumerator_eq_polymerPartition_mul_tsum_connectedRoot
#print axioms
  YangMills.StrongCoupling.complexGibbsExpectation_eq_tsum_connectedDecoratedRoot
#print axioms
  YangMills.StrongCoupling.decoratedObservableRootModel_restrictedSymmetricMayerPowerSeries_eq_formalMayerLog
#print axioms
  YangMills.StrongCoupling.plaquettePolymerModel_cardinalityTilt_koteckyPreiss
#print axioms
  YangMills.StrongCoupling.bivariateDecoratedObservableCardinalityTiltedModel_koteckyPreiss_regularized
#print axioms
  YangMills.StrongCoupling.bivariateDecoratedObservableCardinalityTiltedModel_summable_pinnedMayerTreeDegreeSum_succ
#print axioms
  YangMills.StrongCoupling.summable_bivariateDecoratedObservableMixedCardinalityWeightedNormDegreeSum_succ
#print axioms
  YangMills.StrongCoupling.bivariateDecorated_mixed_nonzero_spatialSeparation_le_weightedMultiplicity
#print axioms
  YangMills.Polymer.FinitePolymerModel.bigradedMixedNormDegreeSum_le_sum_firstGrading_pinnedMayerTreeDegreeSum
#print axioms
  YangMills.Polymer.FinitePolymerModel.tsum_pinnedMayerTreeDegreeSum_succ_le_of_koteckyPreiss_certified
#print axioms
  YangMills.StrongCoupling.bivariateDecoratedObservableCardinalityTiltSourceMass_le_uniformBudget
#print axioms
  YangMills.StrongCoupling.bivariateDecoratedObservableCardinalityTiltUniformRegularization_le
#print axioms
  YangMills.StrongCoupling.pow_spatialSeparation_mul_norm_complexGibbsTruncatedCorrelation_le_uniformPinnedTreeBudget
#print axioms YangMills.StrongCoupling.TwoRootClusterCertificate.exponential_clustering_exp
#print axioms
  YangMills.StrongCoupling.pow_mul_norm_complexGibbsExpectation_withExterior_sub_le_boundaryBudget
#print axioms
  YangMills.StrongCoupling.tendsto_centered_complexGibbsExpectation_boundary_sub_zero
#print axioms
  YangMills.StrongCoupling.centeredClusterLimit_exponential_clustering_exp
#print axioms
  YangMills.StrongCoupling.FiniteSubspecification.complexGibbsExpectation_eq_integral_induced
#print axioms
  YangMills.StrongCoupling.FiniteSubspecification.norm_complexGibbsExpectation_large_sub_small_le_of_uniform
#print axioms
  YangMills.StrongCoupling.cauchySeq_centered_localExpectation
#print axioms
  YangMills.StrongCoupling.tendsto_centered_localExpectation_infiniteVolume
#print axioms
  YangMills.StrongCoupling.tendsto_centered_localExpectation_infiniteVolume_along
#print axioms
  YangMills.StrongCoupling.centeredInfiniteVolumeMeasure_boundary_independent
#print axioms
  YangMills.StrongCoupling.centeredInfiniteVolumeMeasure_unique
#print axioms
  YangMills.StrongCoupling.centeredInfiniteVolume_integral_gaugePullback
#print axioms
  YangMills.StrongCoupling.centeredInfiniteVolumeMeasure_map_gaugeTransform
#print axioms
  YangMills.StrongCoupling.centeredInfiniteVolumeMeasure_measurePreserving_gaugeTransform
#print axioms
  YangMills.StrongCoupling.centeredInfiniteVolume_integral_translatePullback
#print axioms
  YangMills.StrongCoupling.centeredInfiniteVolume_exponential_clustering
#print axioms
  YangMills.StrongCoupling.centeredInfiniteVolume_clusteringMass_pos

end

end YangMills.Tests
