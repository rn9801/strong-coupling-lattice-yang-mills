/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.Observable
import YangMills.StrongCoupling.PlaquettePolymer

/-!
# Marked plaquette expansion

A bounded local observable is inserted before expanding the Boltzmann factor.
The resulting numerator is an exact finite sum of marked plaquette-subset
weights.  This is the numerator companion to
`complexPartitionFunction_eq_sum_subsetWeight` and is valid for every complex
coupling and every frozen exterior configuration.
-/

open MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume
open scoped BigOperators

noncomputable section

local instance markedExpansionDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- The local observable multiplied by the perturbations in a plaquette
subset. -/
def markedSubsetIntegrand (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) (U : DynamicConfiguration Λ) : ℂ :=
  F (Λ.evaluate U) * subsetIntegrand Λ Φ β X U

/-- Haar-integrated marked weight of a plaquette subset. -/
def markedSubsetWeight (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) : ℂ :=
  ∫ U, markedSubsetIntegrand F Λ Φ β X U ∂Λ.haarMeasure

/-- Unnormalized complex expectation of a local observable. -/
def complexObservableNumerator (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ) : ℂ :=
  ∫ U, complexBoltzmannWeight Λ Φ β U * F (Λ.evaluate U) ∂Λ.haarMeasure

/-- Normalized complex finite-volume expectation on the zero-free domain. -/
def complexGibbsExpectation (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ) : ℂ :=
  (complexPartitionFunction Λ Φ β)⁻¹ * complexObservableNumerator F Λ Φ β

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
theorem continuous_markedSubsetIntegrand (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) :
    Continuous (markedSubsetIntegrand F Λ Φ β X) := by
  exact (F.toContinuousMap.continuous.comp Λ.continuous_evaluate).mul
    (continuous_subsetIntegrand Λ Φ β X)

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Uniform marked-integrand bound. -/
theorem norm_markedSubsetIntegrand_le (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) (U : DynamicConfiguration Λ) :
    ‖markedSubsetIntegrand F Λ Φ β X U‖ ≤
      ‖F.toBoundedContinuousMap‖ * perturbationMajorant Φ β ^ X.card := by
  rw [markedSubsetIntegrand, norm_mul]
  exact mul_le_mul (F.norm_apply_le (Λ.evaluate U))
    (norm_subsetIntegrand_le Λ Φ β X U) (norm_nonneg _) (norm_nonneg _)

theorem integrable_markedSubsetIntegrand (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) :
    Integrable (markedSubsetIntegrand F Λ Φ β X) Λ.haarMeasure := by
  apply Integrable.of_bound
    (continuous_markedSubsetIntegrand F Λ Φ β X).aestronglyMeasurable
    (‖F.toBoundedContinuousMap‖ * perturbationMajorant Φ β ^ X.card)
  exact ae_of_all _ fun U => norm_markedSubsetIntegrand_le F Λ Φ β X U

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] in
/-- Marked weights inherit the product cardinality bound, with the observable
sup norm as prefactor. -/
theorem norm_markedSubsetWeight_le (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) :
    ‖markedSubsetWeight F Λ Φ β X‖ ≤
      ‖F.toBoundedContinuousMap‖ * perturbationMajorant Φ β ^ X.card := by
  unfold markedSubsetWeight
  simpa using
    (norm_integral_le_of_norm_le_const (μ := Λ.haarMeasure)
      (ae_of_all _ fun U => norm_markedSubsetIntegrand_le F Λ Φ β X U))

/-- Exact marked expansion of the unnormalized observable numerator. -/
theorem complexObservableNumerator_eq_sum_markedSubsetWeight
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    complexObservableNumerator F Λ Φ β =
      ∑ X ∈ Λ.activePlaquettes.powerset, markedSubsetWeight F Λ Φ β X := by
  unfold complexObservableNumerator markedSubsetWeight
  simp_rw [complexBoltzmannWeight_eq_sum_subsetIntegrand Λ Φ β,
    Finset.sum_mul, markedSubsetIntegrand]
  have hint : ∀ X ∈ Λ.activePlaquettes.powerset,
      Integrable (fun U => subsetIntegrand Λ Φ β X U * F (Λ.evaluate U))
        Λ.haarMeasure := by
    intro X _
    have h := integrable_markedSubsetIntegrand F Λ Φ β X
    convert h using 1
    funext U
    exact mul_comm _ _
  rw [integral_finsetSum Λ.activePlaquettes.powerset hint]
  apply Finset.sum_congr rfl
  intro X _
  apply integral_congr_ae
  exact ae_of_all _ fun U => mul_comm _ _

/-- Exact ratio form of the normalized marked expansion. -/
theorem complexGibbsExpectation_eq_markedExpansion
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    complexGibbsExpectation F Λ Φ β =
      (complexPartitionFunction Λ Φ β)⁻¹ *
        ∑ X ∈ Λ.activePlaquettes.powerset, markedSubsetWeight F Λ Φ β X := by
  rw [complexGibbsExpectation, complexObservableNumerator_eq_sum_markedSubsetWeight]

/-- At real coupling, the complex marked expectation is the ordinary
Bochner integral of the local observable against the Gibbs probability
measure. -/
theorem complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℝ) :
    complexGibbsExpectation F Λ Φ (β : ℂ) =
      ∫ U, F (Λ.evaluate U) ∂gibbsMeasure Λ Φ β := by
  rw [complexGibbsExpectation, complexPartitionFunction_ofReal,
    gibbsMeasure, integral_tilted]
  simp only [smul_eq_mul, Complex.ofReal_inv, complexObservableNumerator,
    complexBoltzmannWeight_ofReal, boltzmannWeight, partitionFunction]
  rw [← integral_const_mul]
  congr 1
  funext U
  rw [Complex.real_smul]
  push_cast
  ring

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- If the recorded observable support is dynamic, its value after gluing is
independent of the frozen exterior configuration. -/
theorem localObservable_evaluate_withExterior_eq
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (η η' : Gauge.Configuration d G) (U : DynamicConfiguration Λ)
    (hF : F.support ⊆ Λ.dynamicEdges) :
    F ((withExterior Λ η).evaluate U) =
      F ((withExterior Λ η').evaluate U) := by
  apply F.dependsOn_support
  intro e he
  simp [FiniteSpecification.evaluate, withExterior, hF he]

omit [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- A marked subset weight sees exterior data only on frozen boundary edges
of the selected plaquettes.  The observable itself contributes no exterior
dependence when its support is contained in the dynamic edges. -/
theorem markedSubsetWeight_withExterior_eq_of_eqOn
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (X : Finset (Plaquette d))
    (η η' : Gauge.Configuration d G) (hF : F.support ⊆ Λ.dynamicEdges)
    (hη : ∀ p ∈ X, ∀ e ∈ p.boundary.edgeSupport,
      e ∉ Λ.dynamicEdges → η e = η' e) :
    markedSubsetWeight F (withExterior Λ η) Φ β X =
      markedSubsetWeight F (withExterior Λ η') Φ β X := by
  apply integral_congr_ae
  exact ae_of_all _ fun U => by
    unfold markedSubsetIntegrand
    rw [localObservable_evaluate_withExterior_eq F Λ η η' U hF]
    congr 1
    unfold subsetIntegrand
    apply Finset.prod_congr rfl
    intro p hp
    unfold plaquettePerturbation plaquetteHolonomy
    have hhol : Gauge.holonomy ((withExterior Λ η).evaluate U) p.boundary =
        Gauge.holonomy ((withExterior Λ η').evaluate U) p.boundary := by
      apply Gauge.holonomy_eq_of_eqOn_edgeSupport
      intro e he
      by_cases hedyn : e ∈ Λ.dynamicEdges
      · simp [FiniteSpecification.evaluate, withExterior, hedyn]
      · simp [FiniteSpecification.evaluate, withExterior, hedyn,
          hη p hp e he hedyn]
    rw [hhol]

end

end YangMills.StrongCoupling
