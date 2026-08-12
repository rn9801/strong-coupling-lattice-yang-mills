/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.BoxGibbs
import YangMills.StrongCoupling.MarkedExpansion

/-!
# Gibbs towers for nested finite specifications

This file isolates the geometry-free conditioning argument used for a finite
specification nested inside a larger one.  The smaller active set must contain
every plaquette incident to a smaller dynamic edge.  Under that hypothesis,
the action outside the smaller active set is constant on each conditional
fiber, so the finite-product Gibbs tower identifies the conditional law with
the smaller Yang--Mills Gibbs law carrying the induced exterior field.
-/

open MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume
open YangMills.Probability

noncomputable section

local instance finiteSpecificationTowerDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Data saying that `small` is a geometrically complete sub-specification of
`large`. -/
structure FiniteSubspecification
    (small large : FiniteSpecification d G) : Prop where
  dynamic_subset : small.dynamicEdges ⊆ large.dynamicEdges
  active_subset : small.activePlaquettes ⊆ large.activePlaquettes
  boundary_disjoint_of_not_active : ∀ p, p ∉ small.activePlaquettes →
    Disjoint p.boundary.edgeSupport small.dynamicEdges

namespace FiniteSubspecification

variable {small large : FiniteSpecification d G}

/-- The smaller dynamic coordinates as a region of the larger coordinate
family. -/
def region (h : FiniteSubspecification small large) :
    Finset large.dynamicEdges :=
  Finset.univ.filter fun e => e.1 ∈ small.dynamicEdges

@[simp]
theorem mem_region (h : FiniteSubspecification small large)
    (e : large.dynamicEdges) :
    e ∈ h.region ↔ e.1 ∈ small.dynamicEdges := by
  rw [region, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ e)

/-- The smaller specification with exterior induced by a larger dynamic
configuration. -/
def induced (_h : FiniteSubspecification small large)
    (σ : DynamicConfiguration large) : FiniteSpecification d G where
  dynamicEdges := small.dynamicEdges
  activePlaquettes := small.activePlaquettes
  exterior := large.evaluate σ

@[simp]
theorem induced_dynamicEdges (h : FiniteSubspecification small large)
    (σ : DynamicConfiguration large) :
    (h.induced σ).dynamicEdges = small.dynamicEdges :=
  rfl

@[simp]
theorem induced_activePlaquettes (h : FiniteSubspecification small large)
    (σ : DynamicConfiguration large) :
    (h.induced σ).activePlaquettes = small.activePlaquettes :=
  rfl

/-- Gluing inside the smaller region agrees with evaluating the induced
smaller specification after coordinate restriction. -/
theorem evaluate_glue (h : FiniteSubspecification small large)
    (σ u : DynamicConfiguration large) :
    (h.induced σ).evaluate
        (Gauge.ProductHaar.restrictOfFinsetSubset (G := G)
          h.dynamic_subset u) =
      large.evaluate (glue h.region u σ) := by
  funext e
  by_cases hes : e ∈ small.dynamicEdges
  · have hel : e ∈ large.dynamicEdges := h.dynamic_subset hes
    rw [(h.induced σ).evaluate_of_mem _ e hes,
      large.evaluate_of_mem _ e hel]
    rw [glue_inside h.region u σ ⟨e, hel⟩ ((h.mem_region ⟨e, hel⟩).2 hes)]
    rfl
  · rw [(h.induced σ).evaluate_of_not_mem _ e hes]
    by_cases hel : e ∈ large.dynamicEdges
    · change large.evaluate σ e = large.evaluate (glue h.region u σ) e
      rw [large.evaluate_of_mem _ e hel, large.evaluate_of_mem _ e hel]
      rw [glue_outside h.region u σ ⟨e, hel⟩
        (by simpa only [h.mem_region] using hes)]
    · change large.evaluate σ e = large.evaluate (glue h.region u σ) e
      rw [large.evaluate_of_not_mem _ e hel,
        large.evaluate_of_not_mem _ e hel]

/-- Plaquettes outside the smaller active set are constant on a smaller
conditional fiber. -/
theorem plaquetteHolonomy_glue_of_not_active
    (h : FiniteSubspecification small large)
    (σ u : DynamicConfiguration large) (p : Plaquette d)
    (hp : p ∉ small.activePlaquettes) :
    plaquetteHolonomy large (glue h.region u σ) p =
      plaquetteHolonomy large σ p := by
  unfold plaquetteHolonomy
  apply Gauge.holonomy_eq_of_eqOn_edgeSupport
  intro e hep
  by_cases hel : e ∈ large.dynamicEdges
  · rw [large.evaluate_of_mem _ e hel, large.evaluate_of_mem _ e hel]
    have hes : e ∉ small.dynamicEdges := by
      intro hes
      exact (Finset.disjoint_left.mp
        (h.boundary_disjoint_of_not_active p hp)) hep hes
    rw [glue_outside h.region u σ ⟨e, hel⟩
      (by simpa only [h.mem_region] using hes)]
  · rw [large.evaluate_of_not_mem _ e hel,
      large.evaluate_of_not_mem _ e hel]

/-- Contribution of the large active plaquettes outside the smaller active
set. -/
def outerAction (h : FiniteSubspecification small large)
    (Φ : RealPlaquettePotential G) (σ : DynamicConfiguration large) : ℝ :=
  ∑ p ∈ large.activePlaquettes \ small.activePlaquettes,
    Φ (plaquetteHolonomy large σ p)

/-- Action splitting on a conditional fiber. -/
theorem action_glue (h : FiniteSubspecification small large)
    (Φ : RealPlaquettePotential G)
    (σ u : DynamicConfiguration large) :
    action large Φ (glue h.region u σ) =
      action (h.induced σ) Φ
        (Gauge.ProductHaar.restrictOfFinsetSubset (G := G)
          h.dynamic_subset u) + h.outerAction Φ σ := by
  classical
  let V := Gauge.ProductHaar.restrictOfFinsetSubset (G := G)
    h.dynamic_subset u
  have hsmall : ∀ p ∈ small.activePlaquettes,
      plaquetteHolonomy large (glue h.region u σ) p =
        plaquetteHolonomy (h.induced σ) V p := by
    intro p _hp
    unfold plaquetteHolonomy
    apply congrArg (fun A => Gauge.holonomy A p.boundary)
    simpa only [V] using (h.evaluate_glue σ u).symm
  have houter : ∀ p ∈ large.activePlaquettes \ small.activePlaquettes,
      plaquetteHolonomy large (glue h.region u σ) p =
        plaquetteHolonomy large σ p := by
    intro p hp
    exact h.plaquetteHolonomy_glue_of_not_active σ u p
      (Finset.mem_sdiff.mp hp).2
  change (∑ p ∈ large.activePlaquettes,
      Φ (plaquetteHolonomy large (glue h.region u σ) p)) =
    (∑ p ∈ small.activePlaquettes,
      Φ (plaquetteHolonomy (h.induced σ) V p)) +
      ∑ p ∈ large.activePlaquettes \ small.activePlaquettes,
        Φ (plaquetteHolonomy large σ p)
  calc
    (∑ p ∈ large.activePlaquettes,
        Φ (plaquetteHolonomy large (glue h.region u σ) p)) =
        (∑ p ∈ large.activePlaquettes \ small.activePlaquettes,
          Φ (plaquetteHolonomy large (glue h.region u σ) p)) +
          ∑ p ∈ small.activePlaquettes,
            Φ (plaquetteHolonomy large (glue h.region u σ) p) :=
      (Finset.sum_sdiff h.active_subset).symm
    _ = (∑ p ∈ large.activePlaquettes \ small.activePlaquettes,
          Φ (plaquetteHolonomy large σ p)) +
        ∑ p ∈ small.activePlaquettes,
          Φ (plaquetteHolonomy (h.induced σ) V p) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro p hp
        rw [houter p hp]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [hsmall p hp]
    _ = _ := add_comm _ _

theorem restrict_glue (h : FiniteSubspecification small large)
    (σ u : DynamicConfiguration large) :
    Gauge.ProductHaar.restrictOfFinsetSubset (G := G) h.dynamic_subset
        (glue h.region u σ) =
      Gauge.ProductHaar.restrictOfFinsetSubset (G := G) h.dynamic_subset u := by
  funext e
  change glue h.region u σ ⟨e.1, h.dynamic_subset e.2⟩ =
    u ⟨e.1, h.dynamic_subset e.2⟩
  rw [glue_inside h.region u σ ⟨e.1, h.dynamic_subset e.2⟩
    ((h.mem_region ⟨e.1, h.dynamic_subset e.2⟩).2 e.2)]

/-- The induced smaller energy pulled back to the large coordinate family. -/
def innerEnergy (h : FiniteSubspecification small large)
    (Φ : RealPlaquettePotential G) (β : ℝ)
    (σ : DynamicConfiguration large) :
    FiniteEnergy large.dynamicEdges G where
  energy := fun u => β * action (h.induced σ) Φ
    (Gauge.ProductHaar.restrictOfFinsetSubset (G := G) h.dynamic_subset u)
  measurable_energy := measurable_const.mul
    ((continuous_action (h.induced σ) Φ).measurable.comp
      (Gauge.ProductHaar.measurePreserving_restrictOfFinsetSubset
        (G := G) h.dynamic_subset).measurable)
  bound := |β| * actionBound (h.induced σ) Φ
  bound_nonneg := mul_nonneg (abs_nonneg _) (actionBound_nonneg _ _)
  norm_energy_le := fun u => by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_action_le _ _ _) (abs_nonneg β)

@[simp]
theorem innerEnergy_apply (h : FiniteSubspecification small large)
    (Φ : RealPlaquettePotential G) (β : ℝ)
    (σ u : DynamicConfiguration large) :
    h.innerEnergy Φ β σ u = β * action (h.induced σ) Φ
      (Gauge.ProductHaar.restrictOfFinsetSubset (G := G)
        h.dynamic_subset u) :=
  rfl

/-- The large conditional law is the pulled-back induced smaller Gibbs law. -/
theorem conditionalMeasure_boxEnergy_eq_innerEnergy
    (h : FiniteSubspecification small large)
    (Φ : RealPlaquettePotential G) (β : ℝ)
    (σ : DynamicConfiguration large) :
    (boxEnergy large Φ β).conditionalMeasure
        (GaugeHaarProbability.haar G) h.region σ =
      (h.innerEnergy Φ β σ).conditionalMeasure
        (GaugeHaarProbability.haar G) h.region σ := by
  apply (boxEnergy large Φ β).conditionalMeasure_eq_of_add_const
    (GaugeHaarProbability.haar G) (h.innerEnergy Φ β σ)
    h.region σ (β * h.outerAction Φ σ)
  intro u
  rw [boxEnergy_apply, innerEnergy_apply, h.action_glue Φ σ u]
  have hrestrict := h.restrict_glue σ u
  have haction := congrArg (action (h.induced σ) Φ) hrestrict
  rw [mul_add]
  exact congrArg (fun x : ℝ => β * x + β * h.outerAction Φ σ) haction.symm

/-- Conditional expectations are induced smaller finite-volume Gibbs
expectations. -/
theorem integral_conditionalMeasure_eq_complexGibbsExpectation
    (h : FiniteSubspecification small large)
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (σ : DynamicConfiguration large) :
    ∫ τ, F (large.evaluate τ)
        ∂(boxEnergy large Φ β).conditionalMeasure
          (GaugeHaarProbability.haar G) h.region σ =
      complexGibbsExpectation F (h.induced σ) Φ (β : ℂ) := by
  let Λs := h.induced σ
  let R : DynamicConfiguration large → DynamicConfiguration Λs :=
    Gauge.ProductHaar.restrictOfFinsetSubset (G := G) h.dynamic_subset
  let Ein := h.innerEnergy Φ β σ
  have hfmeas : Measurable (fun τ : DynamicConfiguration large =>
      F (large.evaluate τ)) :=
    F.toContinuousMap.continuous.measurable.comp large.continuous_evaluate.measurable
  rw [h.conditionalMeasure_boxEnergy_eq_innerEnergy Φ β σ]
  rw [Ein.integral_conditionalMeasure_complex_eq_div
    (GaugeHaarProbability.haar G) h.region σ
    (fun τ => F (large.evaluate τ)) hfmeas
    ‖F.toBoundedContinuousMap‖ (fun τ => F.norm_apply_le (large.evaluate τ))]
  have hden : Ein.conditionalZ (GaugeHaarProbability.haar G) h.region σ =
      partitionFunction Λs Φ β := by
    change (∫ u, Real.exp (Ein (glue h.region u σ)) ∂large.haarMeasure) =
      partitionFunction Λs Φ β
    calc
      (∫ u, Real.exp (Ein (glue h.region u σ)) ∂large.haarMeasure) =
          ∫ u, boltzmannWeight Λs Φ β (R u) ∂large.haarMeasure := by
        apply integral_congr_ae
        exact ae_of_all _ fun u => by
          change Real.exp (β * action Λs Φ (R (glue h.region u σ))) =
            Real.exp (β * action Λs Φ (R u))
          have hr : R (glue h.region u σ) = R u := by
            simpa only [R, Λs] using h.restrict_glue σ u
          rw [hr]
      _ = ∫ v, boltzmannWeight Λs Φ β v ∂Λs.haarMeasure := by
        exact Gauge.ProductHaar.integral_restrictOfFinsetSubset
          (G := G) h.dynamic_subset (boltzmannWeight Λs Φ β)
          (continuous_boltzmannWeight Λs Φ β).measurable
      _ = partitionFunction Λs Φ β := rfl
  have hnum :
      (∫ u, (Real.exp (Ein (glue h.region u σ)) : ℂ) *
          F (large.evaluate (glue h.region u σ)) ∂large.haarMeasure) =
        complexObservableNumerator F Λs Φ (β : ℂ) := by
    calc
      (∫ u, (Real.exp (Ein (glue h.region u σ)) : ℂ) *
          F (large.evaluate (glue h.region u σ)) ∂large.haarMeasure) =
          ∫ u, complexBoltzmannWeight Λs Φ (β : ℂ) (R u) *
            F (Λs.evaluate (R u)) ∂large.haarMeasure := by
        apply integral_congr_ae
        exact ae_of_all _ fun u => by
          have hr : R (glue h.region u σ) = R u := h.restrict_glue σ u
          have ha := congrArg (action Λs Φ) hr
          have heval : Λs.evaluate (R u) =
              large.evaluate (glue h.region u σ) := by
            simpa only [Λs, R] using h.evaluate_glue σ u
          change (Real.exp (β * action Λs Φ (R (glue h.region u σ))) : ℂ) *
              F (large.evaluate (glue h.region u σ)) =
            complexBoltzmannWeight Λs Φ (β : ℂ) (R u) *
              F (Λs.evaluate (R u))
          rw [complexBoltzmannWeight_ofReal]
          exact congrArg₂ (fun x y : ℂ => x * y)
            (congrArg (fun x : ℝ => (Real.exp (β * x) : ℂ)) ha)
            (congrArg F heval.symm)
      _ = ∫ v, complexBoltzmannWeight Λs Φ (β : ℂ) v *
          F (Λs.evaluate v) ∂Λs.haarMeasure := by
        exact Gauge.ProductHaar.integral_restrictOfFinsetSubset
          (G := G) h.dynamic_subset
          (fun v => complexBoltzmannWeight Λs Φ (β : ℂ) v *
            F (Λs.evaluate v))
          ((continuous_complexBoltzmannWeight Λs Φ (β : ℂ)).mul
            (F.toContinuousMap.continuous.comp Λs.continuous_evaluate)).measurable
      _ = complexObservableNumerator F Λs Φ (β : ℂ) := rfl
  rw [hden]
  change (∫ u, (Real.exp (Ein (glue h.region u σ)) : ℂ) *
      F (large.evaluate (glue h.region u σ)) ∂large.haarMeasure) /
      partitionFunction Λs Φ β = complexGibbsExpectation F Λs Φ (β : ℂ)
  rw [hnum, complexGibbsExpectation, complexPartitionFunction_ofReal]
  ring

/-- A large expectation is the Gibbs average of induced smaller
expectations. -/
theorem complexGibbsExpectation_eq_integral_induced
    (h : FiniteSubspecification small large)
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℝ) :
    complexGibbsExpectation F large Φ (β : ℂ) =
      ∫ σ, complexGibbsExpectation F (h.induced σ) Φ (β : ℂ)
        ∂gibbsMeasure large Φ β := by
  let E := boxEnergy large Φ β
  let f : DynamicConfiguration large → ℂ := fun τ => F (large.evaluate τ)
  have hf : Measurable f :=
    F.toContinuousMap.continuous.measurable.comp large.continuous_evaluate.measurable
  have hB : ∀ τ, ‖f τ‖ ≤ ‖F.toBoundedContinuousMap‖ :=
    fun τ => F.norm_apply_le (large.evaluate τ)
  have htower := E.integral_conditionalMeasure_gibbsMeasure_complex
    (GaugeHaarProbability.haar G) h.region f hf
    ‖F.toBoundedContinuousMap‖ hB
  rw [boxEnergy_gibbsMeasure_eq] at htower
  have hcond : (fun σ => ∫ τ, f τ
      ∂E.conditionalMeasure (GaugeHaarProbability.haar G) h.region σ) =
      fun σ => complexGibbsExpectation F (h.induced σ) Φ (β : ℂ) := by
    funext σ
    simpa only [E, f] using
      h.integral_conditionalMeasure_eq_complexGibbsExpectation F Φ β σ
  rw [hcond] at htower
  rw [complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact htower.symm

/-- A uniform boundary comparison for the smaller geometry controls its
difference from a containing finite-volume expectation. -/
theorem norm_complexGibbsExpectation_large_sub_small_le_of_uniform
    (h : FiniteSubspecification small large)
    (ηsmall : Configuration d G) (F : LocalObservable d G)
    (Φ : RealPlaquettePotential G) (β : ℝ) (C : ℝ)
    (hC : ∀ ξ : Configuration d G,
      ‖complexGibbsExpectation F
          { small with exterior := ξ } Φ (β : ℂ) -
        complexGibbsExpectation F
          { small with exterior := ηsmall } Φ (β : ℂ)‖ ≤ C) :
    ‖complexGibbsExpectation F large Φ (β : ℂ) -
        complexGibbsExpectation F
          { small with exterior := ηsmall } Φ (β : ℂ)‖ ≤ C := by
  let μ := gibbsMeasure large Φ β
  let g : DynamicConfiguration large → ℂ := fun σ =>
    complexGibbsExpectation F (h.induced σ) Φ (β : ℂ)
  let c := complexGibbsExpectation F
    { small with exterior := ηsmall } Φ (β : ℂ)
  have hrepr := h.complexGibbsExpectation_eq_integral_induced F Φ β
  have hgc : ∀ σ, ‖g σ - c‖ ≤ C := fun σ => by
    simpa only [g, c, induced] using hC (large.evaluate σ)
  have hgmeas : Measurable g := by
    let E := boxEnergy large Φ β
    let f : DynamicConfiguration large → ℂ := fun τ => F (large.evaluate τ)
    have hf : Measurable f :=
      F.toContinuousMap.continuous.measurable.comp large.continuous_evaluate.measurable
    have hre : (fun σ => (g σ).re) = fun σ =>
        ∫ τ, (f τ).re ∂E.conditionalMeasure
          (GaugeHaarProbability.haar G) h.region σ := by
      funext σ
      have hfiber := h.integral_conditionalMeasure_eq_complexGibbsExpectation
        F Φ β σ
      have hfint : Integrable f
          (E.conditionalMeasure (GaugeHaarProbability.haar G) h.region σ) := by
        apply Integrable.of_bound hf.aestronglyMeasurable
          ‖F.toBoundedContinuousMap‖
        exact ae_of_all _ fun τ => F.norm_apply_le (large.evaluate τ)
      change (g σ).re = _
      calc
        (g σ).re = (∫ τ, f τ ∂E.conditionalMeasure
            (GaugeHaarProbability.haar G) h.region σ).re :=
          congrArg Complex.re hfiber.symm
        _ = ∫ τ, (f τ).re ∂E.conditionalMeasure
            (GaugeHaarProbability.haar G) h.region σ := (integral_re hfint).symm
    have him : (fun σ => (g σ).im) = fun σ =>
        ∫ τ, (f τ).im ∂E.conditionalMeasure
          (GaugeHaarProbability.haar G) h.region σ := by
      funext σ
      have hfiber := h.integral_conditionalMeasure_eq_complexGibbsExpectation
        F Φ β σ
      have hfint : Integrable f
          (E.conditionalMeasure (GaugeHaarProbability.haar G) h.region σ) := by
        apply Integrable.of_bound hf.aestronglyMeasurable
          ‖F.toBoundedContinuousMap‖
        exact ae_of_all _ fun τ => F.norm_apply_le (large.evaluate τ)
      change (g σ).im = _
      calc
        (g σ).im = (∫ τ, f τ ∂E.conditionalMeasure
            (GaugeHaarProbability.haar G) h.region σ).im :=
          congrArg Complex.im hfiber.symm
        _ = ∫ τ, (f τ).im ∂E.conditionalMeasure
            (GaugeHaarProbability.haar G) h.region σ := (integral_im hfint).symm
    have hre_meas : Measurable fun σ => (g σ).re := by
      rw [hre]
      exact E.measurable_integral_conditionalMeasure
        (GaugeHaarProbability.haar G) h.region
        (fun τ => (f τ).re) (Complex.measurable_re.comp hf)
    have him_meas : Measurable fun σ => (g σ).im := by
      rw [him]
      exact E.measurable_integral_conditionalMeasure
        (GaugeHaarProbability.haar G) h.region
        (fun τ => (f τ).im) (Complex.measurable_im.comp hf)
    have hcomplex : g = fun σ => ((g σ).re : ℂ) +
        ((g σ).im : ℂ) * Complex.I := by
      funext σ
      apply Complex.ext <;> simp
    rw [hcomplex]
    exact hre_meas.complex_ofReal.add
      (him_meas.complex_ofReal.mul measurable_const)
  have hgint : Integrable g μ := by
    apply Integrable.of_bound hgmeas.aestronglyMeasurable
      ‖F.toBoundedContinuousMap‖
    exact ae_of_all _ fun σ => by
      rw [show g σ = ∫ τ, F (large.evaluate τ)
          ∂(boxEnergy large Φ β).conditionalMeasure
            (GaugeHaarProbability.haar G) h.region σ by
        symm
        exact h.integral_conditionalMeasure_eq_complexGibbsExpectation
          F Φ β σ]
      simpa using norm_integral_le_of_norm_le_const
        (μ := (boxEnergy large Φ β).conditionalMeasure
          (GaugeHaarProbability.haar G) h.region σ)
        (ae_of_all _ fun τ => F.norm_apply_le (large.evaluate τ))
  rw [hrepr]
  change ‖∫ σ, g σ ∂μ - c‖ ≤ C
  have hcint : Integrable (fun _ : DynamicConfiguration large => c) μ :=
    integrable_const c
  have hc : (∫ _ : DynamicConfiguration large, c ∂μ) = c := by simp [μ]
  rw [← hc, ← integral_sub hgint hcint]
  simpa [μ] using norm_integral_le_of_norm_le_const
    (μ := μ) (ae_of_all μ hgc)

end FiniteSubspecification

end

end YangMills.StrongCoupling
