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

open Filter MeasureTheory
open scoped Topology

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

/-- Dynamic coordinates on which the glued evaluation of a local observable
can depend.  Exterior support edges are frozen and therefore do not appear. -/
def observableCoordinateSupport (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) : Finset Λ.dynamicEdges :=
  Finset.univ.filter fun e => e.1 ∈ F.support

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
omit [Group G] [CompactSpace G] in
/-- The observable after gluing depends only on its dynamic support
coordinates. -/
theorem localObservable_evaluate_dependsOn (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) :
    DependsOn (fun U : DynamicConfiguration Λ => F (Λ.evaluate U))
      (observableCoordinateSupport F Λ : Set Λ.dynamicEdges) := by
  intro U V hUV
  apply F.dependsOn_support
  intro e heF
  by_cases heΛ : e ∈ Λ.dynamicEdges
  · rw [Λ.evaluate_of_mem U e heΛ, Λ.evaluate_of_mem V e heΛ]
    apply hUV ⟨e, heΛ⟩
    simp only [observableCoordinateSupport]
    simpa using heF
  · rw [Λ.evaluate_of_not_mem U e heΛ, Λ.evaluate_of_not_mem V e heΛ]

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] [CompactSpace G] in
/-- A marked subset integrand reads the union of the observable coordinates
and the selected plaquette coordinates. -/
theorem markedSubsetIntegrand_dependsOn (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) :
    DependsOn (markedSubsetIntegrand F Λ Φ β X)
      ((observableCoordinateSupport F Λ : Set Λ.dynamicEdges) ∪
        (subsetCoordinateSupport Λ X : Set Λ.dynamicEdges)) := by
  intro U V hUV
  unfold markedSubsetIntegrand
  have hF := localObservable_evaluate_dependsOn F Λ
    (fun e he => hUV e (Set.mem_union_left _ he))
  have hX := subsetIntegrand_dependsOn Λ Φ β X
    (fun e he => hUV e (Set.mem_union_right _ he))
  exact congrArg₂ (· * ·) hF hX

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] [CompactSpace G] in
/-- Splitting off a disjoint plaquette block factors the marked integrand
pointwise into a marked part and an unmarked part. -/
theorem markedSubsetIntegrand_union_of_disjoint (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (A B : Finset (Plaquette d)) (hAB : Disjoint A B)
    (U : DynamicConfiguration Λ) :
    markedSubsetIntegrand F Λ Φ β (A ∪ B) U =
      markedSubsetIntegrand F Λ Φ β A U * subsetIntegrand Λ Φ β B U := by
  unfold markedSubsetIntegrand subsetIntegrand
  rw [Finset.prod_union hAB]
  ring

/-- Haar-integrated marked weight of a plaquette subset. -/
def markedSubsetWeight (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) : ℂ :=
  ∫ U, markedSubsetIntegrand F Λ Φ β X U ∂Λ.haarMeasure

/-- Pointwise derivative of a marked subset integrand. -/
def markedSubsetIntegrandDerivative (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) (U : DynamicConfiguration Λ) : ℂ :=
  F (Λ.evaluate U) * subsetIntegrandDerivative Λ Φ β X U

/-- Unnormalized complex expectation of a local observable. -/
def complexObservableNumerator (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ) : ℂ :=
  ∫ U, complexBoltzmannWeight Λ Φ β U * F (Λ.evaluate U) ∂Λ.haarMeasure

/-- Normalized complex finite-volume expectation on the zero-free domain. -/
def complexGibbsExpectation (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ) : ℂ :=
  (complexPartitionFunction Λ Φ β)⁻¹ * complexObservableNumerator F Λ Φ β

/-- Pointwise derivative of the observable-weighted complex Boltzmann
integrand. -/
def complexObservableNumeratorDerivative (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (U : DynamicConfiguration Λ) : ℂ :=
  complexBoltzmannDerivative Λ Φ β U * F (Λ.evaluate U)

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G] [CompactSpace G] in
theorem hasDerivAt_complexObservableIntegrand (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (U : DynamicConfiguration Λ) :
    HasDerivAt
      (fun z => complexBoltzmannWeight Λ Φ z U * F (Λ.evaluate U))
      (complexObservableNumeratorDerivative F Λ Φ β U) β := by
  simpa only [complexObservableNumeratorDerivative] using
    (hasDerivAt_complexBoltzmannWeight Λ Φ β U).mul_const (F (Λ.evaluate U))

/-- Differentiation under the observable-weighted finite-volume integral is
valid at every complex coupling. -/
theorem hasDerivAt_complexObservableNumerator (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β₀ : ℂ) :
    HasDerivAt (complexObservableNumerator F Λ Φ)
      (∫ U, complexObservableNumeratorDerivative F Λ Φ β₀ U ∂Λ.haarMeasure) β₀ := by
  let B := actionBound Λ Φ
  let R := ‖β₀‖ + 1
  let C := Real.exp (R * B) * B * ‖F.toBoundedContinuousMap‖
  have hB : 0 ≤ B := actionBound_nonneg Λ Φ
  have hmeas : ∀ᶠ β in 𝓝 β₀,
      AEStronglyMeasurable
        (fun U => complexBoltzmannWeight Λ Φ β U * F (Λ.evaluate U))
        Λ.haarMeasure :=
    Filter.Eventually.of_forall fun β =>
      ((continuous_complexBoltzmannWeight Λ Φ β).mul
        (F.toContinuousMap.continuous.comp Λ.continuous_evaluate)).aestronglyMeasurable
  have hbaseInt : Integrable
      (fun U => complexBoltzmannWeight Λ Φ β₀ U * F (Λ.evaluate U))
      Λ.haarMeasure := by
    apply Integrable.of_bound
      ((continuous_complexBoltzmannWeight Λ Φ β₀).mul
        (F.toContinuousMap.continuous.comp Λ.continuous_evaluate)).aestronglyMeasurable
      (Real.exp (‖β₀‖ * B) * ‖F.toBoundedContinuousMap‖)
    exact ae_of_all _ fun U => by
      change ‖complexBoltzmannWeight Λ Φ β₀ U * F (Λ.evaluate U)‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul
        (norm_complexBoltzmannWeight_le Λ Φ β₀ U)
        (F.norm_apply_le (Λ.evaluate U)) (norm_nonneg _) (Real.exp_pos _).le
  have hderivMeas : AEStronglyMeasurable
      (complexObservableNumeratorDerivative F Λ Φ β₀) Λ.haarMeasure := by
    apply Continuous.aestronglyMeasurable
    exact ((continuous_complexBoltzmannWeight Λ Φ β₀).mul
      (Complex.continuous_ofReal.comp (continuous_action Λ Φ))).mul
        (F.toContinuousMap.continuous.comp Λ.continuous_evaluate)
  have hbound : ∀ᵐ U ∂Λ.haarMeasure, ∀ β ∈ Metric.ball β₀ 1,
      ‖complexObservableNumeratorDerivative F Λ Φ β U‖ ≤ C := by
    refine ae_of_all _ fun U β hβ => ?_
    have hβnorm : ‖β‖ ≤ R := by
      calc
        ‖β‖ = ‖β₀ + (β - β₀)‖ := by ring_nf
        _ ≤ ‖β₀‖ + ‖β - β₀‖ := norm_add_le _ _
        _ ≤ ‖β₀‖ + 1 := by
          exact add_le_add (le_refl ‖β₀‖) ((show ‖β - β₀‖ < 1 by
            simpa only [Metric.mem_ball, dist_eq_norm] using hβ).le)
        _ = R := rfl
    rw [complexObservableNumeratorDerivative, norm_mul]
    have hderiv : ‖complexBoltzmannDerivative Λ Φ β U‖ ≤
        Real.exp (‖β‖ * B) * B := by
      calc
        ‖complexBoltzmannDerivative Λ Φ β U‖ =
            ‖complexBoltzmannWeight Λ Φ β U‖ *
              ‖(action Λ Φ U : ℂ)‖ := by
          simp [complexBoltzmannDerivative, complexBoltzmannWeight]
        _ ≤ Real.exp (‖β‖ * B) * B := by
          exact mul_le_mul
            (norm_complexBoltzmannWeight_le Λ Φ β U)
            (by simpa only [B, Complex.norm_real] using norm_action_le Λ Φ U)
            (norm_nonneg _) (Real.exp_pos _).le
    calc
      _ ≤ (Real.exp (‖β‖ * B) * B) * ‖F.toBoundedContinuousMap‖ := by
        exact mul_le_mul hderiv (F.norm_apply_le (Λ.evaluate U))
          (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hB)
      _ ≤ (Real.exp (R * B) * B) * ‖F.toBoundedContinuousMap‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_right _ hB
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβnorm hB)
      _ = C := rfl
  have hboundIntegrable : Integrable
      (fun _ : DynamicConfiguration Λ => C) Λ.haarMeasure := integrable_const C
  have hdiff : ∀ᵐ U ∂Λ.haarMeasure, ∀ β ∈ Metric.ball β₀ 1,
      HasDerivAt
        (fun z => complexBoltzmannWeight Λ Φ z U * F (Λ.evaluate U))
        (complexObservableNumeratorDerivative F Λ Φ β U) β :=
    ae_of_all _ fun U β _ => hasDerivAt_complexObservableIntegrand F Λ Φ β U
  simpa only [complexObservableNumerator] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun β U => complexBoltzmannWeight Λ Φ β U * F (Λ.evaluate U))
      (F' := complexObservableNumeratorDerivative F Λ Φ)
      (bound := fun _ => C)
      (Metric.ball_mem_nhds β₀ (by norm_num : (0 : ℝ) < 1))
      hmeas hbaseInt hderivMeas hbound hboundIntegrable hdiff).2

/-- The unnormalized finite-volume numerator of every local observable is
entire. -/
theorem complexObservableNumerator_entire (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) :
    AnalyticOnNhd ℂ (complexObservableNumerator F Λ Φ) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  intro β
  exact (hasDerivAt_complexObservableNumerator F Λ Φ β).differentiableAt

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
theorem continuous_markedSubsetIntegrand (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) :
    Continuous (markedSubsetIntegrand F Λ Φ β X) := by
  exact (F.toContinuousMap.continuous.comp Λ.continuous_evaluate).mul
    (continuous_subsetIntegrand Λ Φ β X)

omit [CompactSpace G] in
/-- A disjoint plaquette block whose dynamic coordinates avoid both the
observable and the marked block factors completely out of the marked Haar
weight. -/
theorem markedSubsetWeight_union_of_disjoint (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (A B : Finset (Plaquette d)) (hAB : Disjoint A B)
    (hedges : Disjoint
      ((observableCoordinateSupport F Λ : Set Λ.dynamicEdges) ∪
        (subsetCoordinateSupport Λ A : Set Λ.dynamicEdges))
      (subsetCoordinateSupport Λ B : Set Λ.dynamicEdges)) :
    markedSubsetWeight F Λ Φ β (A ∪ B) =
      markedSubsetWeight F Λ Φ β A * subsetWeight Λ Φ β B := by
  have hfactor := Gauge.ProductHaar.integral_mul_of_disjoint_dependsOn
    (G := G) (𝕜 := ℂ)
    (markedSubsetIntegrand F Λ Φ β A) (subsetIntegrand Λ Φ β B)
    ((observableCoordinateSupport F Λ : Set Λ.dynamicEdges) ∪
      (subsetCoordinateSupport Λ A : Set Λ.dynamicEdges))
    (subsetCoordinateSupport Λ B : Set Λ.dynamicEdges)
    (markedSubsetIntegrand_dependsOn F Λ Φ β A)
    (subsetIntegrand_dependsOn Λ Φ β B) hedges
    (continuous_markedSubsetIntegrand F Λ Φ β A).measurable
    (continuous_subsetIntegrand Λ Φ β B).measurable
  rw [markedSubsetWeight, markedSubsetWeight, subsetWeight]
  rw [show markedSubsetIntegrand F Λ Φ β (A ∪ B) =
      fun U => markedSubsetIntegrand F Λ Φ β A U *
        subsetIntegrand Λ Φ β B U by
    funext U
    exact markedSubsetIntegrand_union_of_disjoint F Λ Φ β A B hAB U]
  simpa only [FiniteSpecification.haarMeasure] using hfactor

omit [CompactSpace G] in
/-- Two marked blocks with disjoint complete coordinate supports factor into
the product of their separate marked Haar weights.  This is the local
factorization behind two-observable cluster cancellation. -/
theorem markedSubsetWeight_mul_union_of_disjoint
    (F H : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (A B : Finset (Plaquette d)) (hAB : Disjoint A B)
    (hedges : Disjoint
      ((observableCoordinateSupport F Λ : Set Λ.dynamicEdges) ∪
        (subsetCoordinateSupport Λ A : Set Λ.dynamicEdges))
      ((observableCoordinateSupport H Λ : Set Λ.dynamicEdges) ∪
        (subsetCoordinateSupport Λ B : Set Λ.dynamicEdges))) :
    markedSubsetWeight (F.mul H) Λ Φ β (A ∪ B) =
      markedSubsetWeight F Λ Φ β A * markedSubsetWeight H Λ Φ β B := by
  have hfactor := Gauge.ProductHaar.integral_mul_of_disjoint_dependsOn
    (G := G) (𝕜 := ℂ)
    (markedSubsetIntegrand F Λ Φ β A) (markedSubsetIntegrand H Λ Φ β B)
    ((observableCoordinateSupport F Λ : Set Λ.dynamicEdges) ∪
      (subsetCoordinateSupport Λ A : Set Λ.dynamicEdges))
    ((observableCoordinateSupport H Λ : Set Λ.dynamicEdges) ∪
      (subsetCoordinateSupport Λ B : Set Λ.dynamicEdges))
    (markedSubsetIntegrand_dependsOn F Λ Φ β A)
    (markedSubsetIntegrand_dependsOn H Λ Φ β B) hedges
    (continuous_markedSubsetIntegrand F Λ Φ β A).measurable
    (continuous_markedSubsetIntegrand H Λ Φ β B).measurable
  rw [markedSubsetWeight, markedSubsetWeight, markedSubsetWeight]
  rw [show markedSubsetIntegrand (F.mul H) Λ Φ β (A ∪ B) =
      fun U => markedSubsetIntegrand F Λ Φ β A U *
        markedSubsetIntegrand H Λ Φ β B U by
    funext U
    unfold markedSubsetIntegrand subsetIntegrand LocalObservable.mul
    rw [Finset.prod_union hAB]
    simp only [ContinuousMap.mul_apply]
    ring]
  simpa only [FiniteSpecification.haarMeasure] using hfactor

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

/-- Differentiation under the finite Haar integral is valid for each fixed
marked plaquette subset. -/
theorem hasDerivAt_markedSubsetWeight (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (X : Finset (Plaquette d)) (β₀ : ℂ) :
    HasDerivAt (fun β ↦ markedSubsetWeight F Λ Φ β X)
      (∫ U, markedSubsetIntegrandDerivative F Λ Φ β₀ X U ∂Λ.haarMeasure) β₀ := by
  let R := ‖β₀‖ + 1
  let C := ‖F.toBoundedContinuousMap‖ *
    ((X.card : ℝ) * (Real.exp (R * Φ.bound) + 1) ^ X.card *
      Real.exp (R * Φ.bound) * Φ.bound)
  have hR : 0 ≤ R := by positivity
  have hmeas : ∀ᶠ β in 𝓝 β₀,
      AEStronglyMeasurable (markedSubsetIntegrand F Λ Φ β X)
        Λ.haarMeasure := Filter.Eventually.of_forall fun β ↦
    (continuous_markedSubsetIntegrand F Λ Φ β X).aestronglyMeasurable
  have hbase : Integrable (markedSubsetIntegrand F Λ Φ β₀ X)
      Λ.haarMeasure := integrable_markedSubsetIntegrand F Λ Φ β₀ X
  have hderivMeas : AEStronglyMeasurable
      (markedSubsetIntegrandDerivative F Λ Φ β₀ X) Λ.haarMeasure := by
    exact ((F.toContinuousMap.continuous.comp Λ.continuous_evaluate).mul
      (continuous_subsetIntegrandDerivative Λ Φ β₀ X)).aestronglyMeasurable
  have hbound : ∀ᵐ U ∂Λ.haarMeasure, ∀ β ∈ Metric.ball β₀ 1,
      ‖markedSubsetIntegrandDerivative F Λ Φ β X U‖ ≤ C := by
    refine ae_of_all _ fun U β hβ ↦ ?_
    have hβR : ‖β‖ ≤ R := by
      calc
        ‖β‖ = ‖β₀ + (β - β₀)‖ := by ring_nf
        _ ≤ ‖β₀‖ + ‖β - β₀‖ := norm_add_le _ _
        _ ≤ ‖β₀‖ + 1 := add_le_add_right
          ((show ‖β - β₀‖ < 1 by
            simpa only [Metric.mem_ball, dist_eq_norm] using hβ).le) _
        _ = R := rfl
    rw [markedSubsetIntegrandDerivative, norm_mul]
    exact mul_le_mul
      (F.norm_apply_le (Λ.evaluate U))
      (norm_subsetIntegrandDerivative_le Λ Φ R hR β hβR X U)
      (norm_nonneg _)
      (norm_nonneg _)
  have hdiff : ∀ᵐ U ∂Λ.haarMeasure, ∀ β ∈ Metric.ball β₀ 1,
      HasDerivAt (fun z ↦ markedSubsetIntegrand F Λ Φ z X U)
        (markedSubsetIntegrandDerivative F Λ Φ β X U) β := by
    refine ae_of_all _ fun U β _ ↦ ?_
    simpa only [markedSubsetIntegrand, markedSubsetIntegrandDerivative] using
      (hasDerivAt_subsetIntegrand Λ Φ β X U).const_mul
        (F (Λ.evaluate U))
  simpa only [markedSubsetWeight] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun β U ↦ markedSubsetIntegrand F Λ Φ β X U)
      (F' := fun β U ↦ markedSubsetIntegrandDerivative F Λ Φ β X U)
      (bound := fun _ ↦ C)
      (Metric.ball_mem_nhds β₀ (by norm_num : (0 : ℝ) < 1))
      hmeas hbase hderivMeas hbound (integrable_const C) hdiff).2

/-- Every fixed marked plaquette-subset weight is entire. -/
theorem markedSubsetWeight_entire (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (X : Finset (Plaquette d)) :
    AnalyticOnNhd ℂ (fun β ↦ markedSubsetWeight F Λ Φ β X) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  intro β
  exact (hasDerivAt_markedSubsetWeight F Λ Φ X β).differentiableAt

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

omit [CompactSpace G] in
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
  simp only [complexObservableNumerator, complexBoltzmannWeight_ofReal,
    boltzmannWeight, partitionFunction]
  rw [← integral_const_mul]
  congr 1
  funext U
  rw [Complex.real_smul]
  push_cast
  ring

omit [CompactSpace G] in
/-- At real coupling, translating the finite specification converts the
expectation of `F` into the expectation of its inverse-translation pullback.
This is exact coordinate relabeling, prior to any thermodynamic limit. -/
theorem complexGibbsExpectation_translate_ofReal
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℝ) (v : Site d) :
    complexGibbsExpectation F (Λ.translate v) Φ (β : ℂ) =
      complexGibbsExpectation (F.translatePullback (-v)) Λ Φ (β : ℂ) := by
  rw [complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  have htranslate := Gauge.FiniteVolume.integral_gibbsMeasure_translate
    Λ Φ β v (fun V => F ((Λ.translate v).evaluate V))
    (F.toContinuousMap.continuous.measurable.comp
      (Λ.translate v).continuous_evaluate.measurable)
  simpa only [LocalObservable.translatePullback_apply,
    Λ.translate_evaluate_translateDynamic,
    LocalObservable.translateConfiguration] using htranslate

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
