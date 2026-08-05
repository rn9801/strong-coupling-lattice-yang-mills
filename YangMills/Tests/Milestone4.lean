/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.ComplexFiniteVolume

/-!
# Milestone 4 executable regressions

These examples exercise arbitrary finite specifications, positivity and
normalization, bounded Gibbs expectations, admissible finite-volume gauge
invariance, and entire complex finite-volume partition functions.
-/

open MeasureTheory

namespace YangMills.Tests.Milestone4

open YangMills.Gauge
open YangMills.Gauge.FiniteVolume
open YangMills.Lattice.Cubic

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

example (Λ : FiniteSpecification d G) (U : DynamicConfiguration Λ)
    (e : PositiveEdge d) (he : e ∉ Λ.dynamicEdges) :
    Λ.evaluate U e = Λ.exterior e :=
  Λ.evaluate_of_not_mem U e he

example (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ) :
    0 < partitionFunction Λ Φ β :=
  partitionFunction_pos Λ Φ β

/-- Milestone 4 normalization exit criterion for every finite specification. -/
example (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) :
    partitionFunction Λ Φ 0 = 1 := by
  simp

example (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β C : ℝ)
    (F : DynamicConfiguration Λ → ℝ)
    (hF : AEStronglyMeasurable F Λ.haarMeasure)
    (hC : ∀ U, ‖F U‖ ≤ C) :
    ‖gibbsExpectation Λ Φ β F‖ ≤ C :=
  norm_gibbsExpectation_le Λ Φ β F C hF hC

example (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) :
    complexPartitionFunction Λ Φ 0 = 1 := by
  simp

example (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) :
    AnalyticOnNhd ℂ (complexPartitionFunction Λ Φ) Set.univ :=
  complexPartitionFunction_entire Λ Φ

section GaugeInvariance

variable [MeasurableMul G]

example (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (g : GaugeTransformation d G) (hg : Λ.BoundaryCompatible g) :
    (∫ U, boltzmannWeight Λ Φ β (Λ.gaugeTransformDynamic g U) ∂Λ.haarMeasure) =
      partitionFunction Λ Φ β :=
  partitionFunction_gaugeInvariant Λ Φ β g hg

end GaugeInvariance

#print axioms YangMills.Gauge.FiniteVolume.partitionFunction_zero
#print axioms YangMills.Gauge.FiniteVolume.norm_gibbsExpectation_le
#print axioms YangMills.Gauge.FiniteVolume.partitionFunction_gaugeInvariant
#print axioms YangMills.Gauge.FiniteVolume.complexPartitionFunction_entire

end YangMills.Tests.Milestone4
