/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.ThermodynamicAnalyticity
import YangMills.StrongCoupling.ThermodynamicPressure

/-! Executable regressions for Milestone 14: analyticity and pressure. -/

namespace YangMills.Tests

open Gauge Lattice.Cubic StrongCoupling Polymer
open Filter Metric MeasureTheory
open scoped Topology

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

example (F : LocalObservable d G) (η : ℕ → Configuration d G)
    (Φ : RealPlaquettePotential G) :
    AnalyticOnNhd ℂ (analyticInfiniteVolumeLocalExpectation F η Φ)
      (ball 0 (latticeStrongCouplingRadius d Φ.bound)) :=
  analyticOnNhd_analyticInfiniteVolumeLocalExpectation F η Φ

example (F : LocalObservable d G) (η : ℕ → Configuration d G)
    (Φ : RealPlaquettePotential G) :
    TendstoLocallyUniformlyOn
      (centeredComplexLocalExpectationSequence F η Φ)
      (analyticInfiniteVolumeLocalExpectation F η Φ) atTop
      (ball 0 (latticeStrongCouplingRadius d Φ.bound)) :=
  tendstoLocallyUniformlyOn_centeredComplexLocalExpectationSequence F η Φ

example (F : LocalObservable d G) (η : ℕ → Configuration d G)
    (Φ : RealPlaquettePotential G) (x : ℝ)
    (hx : ‖(x : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound) :
    analyticInfiniteVolumeLocalExpectation F η Φ (x : ℂ) =
      ∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ x hx :=
  analyticInfiniteVolumeLocalExpectation_ofReal F η Φ x hx

example (F : LocalObservable d G)
    (η η' : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) :
    Set.EqOn (analyticInfiniteVolumeLocalExpectation F η Φ)
      (analyticInfiniteVolumeLocalExpectation F η' Φ)
      (ball 0 (latticeStrongCouplingRadius d Φ.bound)) :=
  analyticInfiniteVolumeLocalExpectation_boundary_independent F η η' Φ

example (Φ : RealPlaquettePotential G) :
    AnalyticOnNhd ℂ (anchoredPressure (d := d) Φ)
      (ball 0 (latticeStrongCouplingRadius d Φ.bound)) :=
  analyticOnNhd_anchoredPressure Φ

example (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Tendsto (fun n ↦
      (((centeredBasePlaquettes d n).card : ℂ)⁻¹) *
        ((infinitePlaquettePolymerModel (d := d) Φ β).restrict
          (InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G)
            (centeredBasePlaquettes d n))).symmetricMayerSum) atTop
      (nhds (anchoredPressure (d := d) Φ β)) :=
  tendsto_normalized_symmetricMayerSum_centeredBasePlaquettes Φ hβ

example (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Tendsto (fun n ↦
      (((centeredBox d n).sites.card : ℂ)⁻¹) *
        ((infinitePlaquettePolymerModel (d := d) Φ β).restrict
          (InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G)
            (centeredBasePlaquettes d n))).symmetricMayerSum) atTop
      (nhds (anchoredPressurePerSite (d := d) Φ β)) :=
  tendsto_normalized_symmetricMayerSum_centeredBasePlaquettes_perSite Φ hβ

example (X : CountablePolymerModel.MayerMultiIndex
    (InfinitePlaquettePolymer d)) :
    Tendsto (fun n ↦ centeredClusterFitFraction n X) atTop (nhds 1) :=
  tendsto_centeredClusterFitFraction X

#print axioms YangMills.VitaliOnDisk.analytic_limit_and_tendstoLocallyUniformlyOn
#print axioms
  YangMills.StrongCoupling.centeredComplexLocalExpectationSequence_eq_tsum_connectedDecoratedRoot
#print axioms
  YangMills.StrongCoupling.norm_centeredComplexLocalExpectationSequence_le_bound
#print axioms
  YangMills.StrongCoupling.analyticOnNhd_analyticInfiniteVolumeLocalExpectation
#print axioms
  YangMills.StrongCoupling.tendstoLocallyUniformlyOn_centeredComplexLocalExpectationSequence
#print axioms
  YangMills.StrongCoupling.analyticInfiniteVolumeLocalExpectation_ofReal
#print axioms
  YangMills.StrongCoupling.analyticInfiniteVolumeLocalExpectation_boundary_independent
#print axioms YangMills.StrongCoupling.tendsto_centeredBox_inner_outer_ratio
#print axioms YangMills.StrongCoupling.tendsto_centeredClusterFitFraction
#print axioms
  YangMills.StrongCoupling.tendsto_normalized_symmetricMayerSum_centeredBasePlaquettes
#print axioms
  YangMills.StrongCoupling.tendsto_normalized_symmetricMayerSum_centeredBasePlaquettes_perSite
#print axioms YangMills.StrongCoupling.analyticOnNhd_anchoredPressure
#print axioms
  YangMills.StrongCoupling.exp_symmetricMayerSum_centeredBasePlaquettes_eq_partitionFunction

end

end YangMills.Tests
