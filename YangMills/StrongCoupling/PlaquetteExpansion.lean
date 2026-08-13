/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.ComplexFiniteVolume
import YangMills.Polymer.Cluster
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact plaquette-subset expansion

The Boltzmann factor is written as a product of single-plaquette perturbations
and expanded over subsets of active plaquettes.  All definitions use the
original finite-volume Haar integral, so the resulting identity is exact at
every complex coupling and for every exterior configuration.
-/

open MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic
open Gauge.FiniteVolume
open scoped BigOperators

noncomputable section

local instance {d : ℕ} : DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Dynamic edges read by a plaquette factor. -/
def plaquetteDynamicSupport (Λ : FiniteSpecification d G) (p : Plaquette d) :
    Finset (PositiveEdge d) :=
  Λ.dynamicEdges.filter fun e => e ∈ p.boundary.edgeSupport

/-- Dynamic edges read by all factors in a plaquette subset. -/
def subsetDynamicSupport (Λ : FiniteSpecification d G) (X : Finset (Plaquette d)) :
    Finset (PositiveEdge d) :=
  X.biUnion (plaquetteDynamicSupport Λ)

/-- Typed dynamic coordinates read by one plaquette factor. -/
def plaquetteCoordinateSupport (Λ : FiniteSpecification d G) (p : Plaquette d) :
    Finset Λ.dynamicEdges :=
  Finset.univ.filter fun e => e.1 ∈ p.boundary.edgeSupport

/-- Typed dynamic coordinates read by a plaquette subset. -/
def subsetCoordinateSupport (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) : Finset Λ.dynamicEdges :=
  X.biUnion (plaquetteCoordinateSupport Λ)

/-- The `exp(β Φ)-1` factor attached to one plaquette. -/
def plaquettePerturbation (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (p : Plaquette d)
    (U : DynamicConfiguration Λ) : ℂ :=
  Complex.exp (β * (Φ (plaquetteHolonomy Λ U p) : ℂ)) - 1

/-- Product of perturbations over an active plaquette subset. -/
def subsetIntegrand (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (X : Finset (Plaquette d))
    (U : DynamicConfiguration Λ) : ℂ :=
  ∏ p ∈ X, plaquettePerturbation Λ Φ β p U

/-- Haar-integrated weight of a plaquette subset. -/
def subsetWeight (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (X : Finset (Plaquette d)) : ℂ :=
  ∫ U, subsetIntegrand Λ Φ β X U ∂Λ.haarMeasure

/-! ## Entire dependence of subset weights -/

/-- Pointwise derivative of the finite plaquette-subset integrand. -/
def subsetIntegrandDerivative (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (X : Finset (Plaquette d))
    (U : DynamicConfiguration Λ) : ℂ :=
  ∑ p ∈ X,
    (∏ q ∈ X.erase p, plaquettePerturbation Λ Φ β q U) *
      Complex.exp (β * (Φ (plaquetteHolonomy Λ U p) : ℂ)) *
        (Φ (plaquetteHolonomy Λ U p) : ℂ)

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G] in
theorem hasDerivAt_plaquettePerturbation
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (p : Plaquette d) (U : DynamicConfiguration Λ) :
    HasDerivAt (fun z ↦ plaquettePerturbation Λ Φ z p U)
      (Complex.exp (β * (Φ (plaquetteHolonomy Λ U p) : ℂ)) *
        (Φ (plaquetteHolonomy Λ U p) : ℂ)) β := by
  unfold plaquettePerturbation
  convert (((hasDerivAt_id β).mul_const
    (Φ (plaquetteHolonomy Λ U p) : ℂ)).cexp.sub_const 1) using 1 <;>
    simp [mul_comm]

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G] in
theorem hasDerivAt_subsetIntegrand
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (X : Finset (Plaquette d)) (U : DynamicConfiguration Λ) :
    HasDerivAt (fun z ↦ subsetIntegrand Λ Φ z X U)
      (subsetIntegrandDerivative Λ Φ β X U) β := by
  unfold subsetIntegrand subsetIntegrandDerivative
  convert HasDerivAt.fun_finsetProd
    (u := X) (x := β) (f := fun p z ↦ plaquettePerturbation Λ Φ z p U)
    (f' := fun p ↦ Complex.exp
      (β * (Φ (plaquetteHolonomy Λ U p) : ℂ)) *
        (Φ (plaquetteHolonomy Λ U p) : ℂ))
    (fun p _ ↦ hasDerivAt_plaquettePerturbation Λ Φ β p U) using 1
  simp [smul_eq_mul, mul_assoc]

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [GaugeHaarProbability G] in
theorem continuous_subsetIntegrandDerivative
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (X : Finset (Plaquette d)) :
    Continuous (subsetIntegrandDerivative Λ Φ β X) := by
  unfold subsetIntegrandDerivative plaquettePerturbation
  apply continuous_finsetSum
  intro p _
  have hΦp : Continuous (fun U ↦
      (Φ (plaquetteHolonomy Λ U p) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Φ.toContinuousMap.continuous.comp
        (continuous_plaquetteHolonomy Λ p))
  have hprod : Continuous (fun U ↦
      ∏ q ∈ X.erase p, plaquettePerturbation Λ Φ β q U) := by
    apply continuous_finsetProd
    intro q _
    exact (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (Φ.toContinuousMap.continuous.comp
          (continuous_plaquetteHolonomy Λ q))))).sub continuous_const
  have hexp : Continuous (fun U ↦ Complex.exp
      (β * (Φ (plaquetteHolonomy Λ U p) : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul hΦp)
  exact (hprod.mul hexp).mul hΦp

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- A single plaquette perturbation depends only on the dynamic edges in its
boundary. -/
theorem plaquettePerturbation_dependsOn
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (p : Plaquette d) :
    DependsOn (plaquettePerturbation Λ Φ β p)
      (plaquetteCoordinateSupport Λ p : Set Λ.dynamicEdges) := by
  intro U V hUV
  unfold plaquettePerturbation plaquetteHolonomy
  have hhol : Gauge.holonomy (Λ.evaluate U) p.boundary =
      Gauge.holonomy (Λ.evaluate V) p.boundary := by
    apply Gauge.holonomy_eq_of_eqOn_edgeSupport
    intro e he
    by_cases hedyn : e ∈ Λ.dynamicEdges
    · rw [Λ.evaluate_of_mem U e hedyn, Λ.evaluate_of_mem V e hedyn]
      exact hUV ⟨e, hedyn⟩ (by
        simp [plaquetteCoordinateSupport, he])
    · rw [Λ.evaluate_of_not_mem U e hedyn, Λ.evaluate_of_not_mem V e hedyn]
  rw [hhol]

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- A subset integrand depends only on the union of its dynamic plaquette
supports. -/
theorem subsetIntegrand_dependsOn
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) :
    DependsOn (subsetIntegrand Λ Φ β X)
      (subsetCoordinateSupport Λ X : Set Λ.dynamicEdges) := by
  intro U V hUV
  unfold subsetIntegrand
  apply Finset.prod_congr rfl
  intro p hp
  apply plaquettePerturbation_dependsOn Λ Φ β p
  intro e he
  exact hUV e (Finset.mem_biUnion.mpr ⟨p, hp, he⟩)

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
@[simp]
theorem subsetIntegrand_empty (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (U : DynamicConfiguration Λ) :
    subsetIntegrand Λ Φ β ∅ U = 1 := by
  simp [subsetIntegrand]

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] in
@[simp]
theorem subsetWeight_empty (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    subsetWeight Λ Φ β ∅ = 1 := by
  simp [subsetWeight]

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Pointwise finite binomial expansion of the complex Boltzmann factor. -/
theorem complexBoltzmannWeight_eq_sum_subsetIntegrand
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (U : DynamicConfiguration Λ) :
    complexBoltzmannWeight Λ Φ β U =
      ∑ X ∈ Λ.activePlaquettes.powerset, subsetIntegrand Λ Φ β X U := by
  classical
  rw [complexBoltzmannWeight, action]
  have harg : β * ((∑ p ∈ Λ.activePlaquettes,
      Φ (plaquetteHolonomy Λ U p) : ℝ) : ℂ) =
      ∑ p ∈ Λ.activePlaquettes,
        β * (Φ (plaquetteHolonomy Λ U p) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
  rw [harg, Complex.exp_sum]
  calc
    ∏ p ∈ Λ.activePlaquettes,
        Complex.exp (β * (Φ (plaquetteHolonomy Λ U p) : ℂ)) =
        ∏ p ∈ Λ.activePlaquettes,
          (plaquettePerturbation Λ Φ β p U + 1) := by
      apply Finset.prod_congr rfl
      intro p _
      simp [plaquettePerturbation]
    _ = ∑ X ∈ Λ.activePlaquettes.powerset,
        subsetIntegrand Λ Φ β X U := by
      rw [Finset.prod_add]
      simp [subsetIntegrand]

/-- Uniform single-plaquette perturbation majorant. -/
def perturbationMajorant (Φ : RealPlaquettePotential G) (β : ℂ) : ℝ :=
  Real.exp (‖β‖ * Φ.bound) - 1

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
theorem perturbationMajorant_nonneg (Φ : RealPlaquettePotential G) (β : ℂ) :
    0 ≤ perturbationMajorant Φ β := by
  unfold perturbationMajorant
  exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg (norm_nonneg _) Φ.bound_nonneg))

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
theorem norm_plaquettePerturbation_le
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (p : Plaquette d) (U : DynamicConfiguration Λ) :
    ‖plaquettePerturbation Λ Φ β p U‖ ≤ perturbationMajorant Φ β := by
  unfold plaquettePerturbation perturbationMajorant
  calc
    ‖Complex.exp (β * (Φ (plaquetteHolonomy Λ U p) : ℂ)) - 1‖ ≤
        Real.exp ‖β * (Φ (plaquetteHolonomy Λ U p) : ℂ)‖ - 1 := by
      simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum
        (β * (Φ (plaquetteHolonomy Λ U p) : ℂ)) 1
    _ ≤ Real.exp (‖β‖ * Φ.bound) - 1 := by
      gcongr
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left
        (Φ.norm_le_bound (plaquetteHolonomy Λ U p)) (norm_nonneg β)

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G] in
theorem norm_subsetIntegrandDerivative_le
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (R : ℝ) (hR : 0 ≤ R) (β : ℂ) (hβ : ‖β‖ ≤ R)
    (X : Finset (Plaquette d)) (U : DynamicConfiguration Λ) :
    ‖subsetIntegrandDerivative Λ Φ β X U‖ ≤
      (X.card : ℝ) * (Real.exp (R * Φ.bound) + 1) ^ X.card *
        Real.exp (R * Φ.bound) * Φ.bound := by
  let Q := Real.exp (R * Φ.bound) + 1
  have hQ : 0 ≤ Q := by positivity
  have hQone : 1 ≤ Q := le_add_of_nonneg_left (Real.exp_pos _).le
  unfold subsetIntegrandDerivative
  calc
    ‖∑ p ∈ X,
        (∏ q ∈ X.erase p, plaquettePerturbation Λ Φ β q U) *
          Complex.exp (β * (Φ (plaquetteHolonomy Λ U p) : ℂ)) *
            (Φ (plaquetteHolonomy Λ U p) : ℂ)‖ ≤
        ∑ p ∈ X, ‖(∏ q ∈ X.erase p,
          plaquettePerturbation Λ Φ β q U) *
            Complex.exp (β * (Φ (plaquetteHolonomy Λ U p) : ℂ)) *
              (Φ (plaquetteHolonomy Λ U p) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ X,
        Q ^ X.card * Real.exp (R * Φ.bound) * Φ.bound := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul, norm_mul, norm_prod, Complex.norm_exp, Complex.norm_real]
      have hprod : ∏ q ∈ X.erase p,
          ‖plaquettePerturbation Λ Φ β q U‖ ≤ Q ^ X.card := by
        calc
          ∏ q ∈ X.erase p, ‖plaquettePerturbation Λ Φ β q U‖ ≤
              ∏ _q ∈ X.erase p, Q := by
            apply Finset.prod_le_prod
            · exact fun _ _ ↦ norm_nonneg _
            · intro q _
              calc
                ‖plaquettePerturbation Λ Φ β q U‖ ≤
                    perturbationMajorant Φ β :=
                  norm_plaquettePerturbation_le Λ Φ β q U
                _ ≤ Q := by
                  unfold perturbationMajorant Q
                  have hexp : Real.exp (‖β‖ * Φ.bound) ≤
                      Real.exp (R * Φ.bound) := by
                    apply Real.exp_le_exp.mpr
                    exact mul_le_mul_of_nonneg_right hβ Φ.bound_nonneg
                  linarith
          _ = Q ^ (X.erase p).card := by simp
          _ ≤ Q ^ X.card :=
            pow_le_pow_right₀ hQone (Finset.card_erase_le (s := X))
      have hexp : Real.exp
          (β * (Φ (plaquetteHolonomy Λ U p) : ℂ)).re ≤
          Real.exp (R * Φ.bound) := by
        apply Real.exp_le_exp.mpr
        calc
          (β * (Φ (plaquetteHolonomy Λ U p) : ℂ)).re ≤
              ‖β * (Φ (plaquetteHolonomy Λ U p) : ℂ)‖ :=
            Complex.re_le_norm _
          _ = ‖β‖ * ‖(Φ (plaquetteHolonomy Λ U p) : ℂ)‖ := norm_mul _ _
          _ ≤ R * Φ.bound := by
            rw [Complex.norm_real]
            exact mul_le_mul hβ
              (Φ.norm_le_bound (plaquetteHolonomy Λ U p))
              (norm_nonneg _) hR
      have hQpow : 0 ≤ Q ^ X.card := pow_nonneg hQ _
      exact mul_le_mul
        (mul_le_mul hprod hexp (Real.exp_pos _).le hQpow)
        (Φ.norm_le_bound (plaquetteHolonomy Λ U p))
        (norm_nonneg _) (mul_nonneg hQpow (Real.exp_pos _).le)
    _ = (X.card : ℝ) * Q ^ X.card *
        Real.exp (R * Φ.bound) * Φ.bound := by simp [mul_assoc]
    _ = (X.card : ℝ) * (Real.exp (R * Φ.bound) + 1) ^ X.card *
        Real.exp (R * Φ.bound) * Φ.bound := rfl

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Product activity bound before integration. -/
theorem norm_subsetIntegrand_le
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (X : Finset (Plaquette d)) (U : DynamicConfiguration Λ) :
    ‖subsetIntegrand Λ Φ β X U‖ ≤ perturbationMajorant Φ β ^ X.card := by
  rw [subsetIntegrand, norm_prod]
  exact (Finset.prod_le_prod (fun p _ => norm_nonneg (plaquettePerturbation Λ Φ β p U))
    (fun p _ => norm_plaquettePerturbation_le Λ Φ β p U)).trans_eq (by simp)

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- A fixed subset integrand is continuous in the dynamic edge variables. -/
theorem continuous_subsetIntegrand (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (X : Finset (Plaquette d)) :
    Continuous (subsetIntegrand Λ Φ β X) := by
  unfold subsetIntegrand plaquettePerturbation
  apply continuous_finsetProd
  intro p _
  exact (Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (Φ.toContinuousMap.continuous.comp (continuous_plaquetteHolonomy Λ p))))).sub
        continuous_const

theorem integrable_subsetIntegrand (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (X : Finset (Plaquette d)) :
    Integrable (subsetIntegrand Λ Φ β X) Λ.haarMeasure := by
  apply Integrable.of_bound
    (continuous_subsetIntegrand Λ Φ β X).aestronglyMeasurable
    (perturbationMajorant Φ β ^ X.card)
  exact ae_of_all _ fun U => norm_subsetIntegrand_le Λ Φ β X U

/-- Differentiation under the finite Haar integral is valid for every
plaquette-subset activity. -/
theorem hasDerivAt_subsetWeight
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (X : Finset (Plaquette d)) (β₀ : ℂ) :
    HasDerivAt (fun β ↦ subsetWeight Λ Φ β X)
      (∫ U, subsetIntegrandDerivative Λ Φ β₀ X U ∂Λ.haarMeasure) β₀ := by
  let R := ‖β₀‖ + 1
  let C := (X.card : ℝ) * (Real.exp (R * Φ.bound) + 1) ^ X.card *
    Real.exp (R * Φ.bound) * Φ.bound
  have hR : 0 ≤ R := by positivity
  have hmeas : ∀ᶠ β in nhds β₀,
      AEStronglyMeasurable (subsetIntegrand Λ Φ β X) Λ.haarMeasure :=
    Filter.Eventually.of_forall fun β ↦
      (continuous_subsetIntegrand Λ Φ β X).aestronglyMeasurable
  have hderivMeas : AEStronglyMeasurable
      (subsetIntegrandDerivative Λ Φ β₀ X) Λ.haarMeasure :=
    (continuous_subsetIntegrandDerivative Λ Φ β₀ X).aestronglyMeasurable
  have hbound : ∀ᵐ U ∂Λ.haarMeasure, ∀ β ∈ Metric.ball β₀ 1,
      ‖subsetIntegrandDerivative Λ Φ β X U‖ ≤ C := by
    refine ae_of_all _ fun U β hβ ↦ ?_
    apply norm_subsetIntegrandDerivative_le Λ Φ R hR β
    calc
      ‖β‖ = ‖β₀ + (β - β₀)‖ := by ring_nf
      _ ≤ ‖β₀‖ + ‖β - β₀‖ := norm_add_le _ _
      _ ≤ ‖β₀‖ + 1 := by
        have hnorm : ‖β - β₀‖ ≤ 1 := by
          exact (show ‖β - β₀‖ < 1 by
            simpa only [Metric.mem_ball, dist_eq_norm] using hβ).le
        exact add_le_add_right hnorm _
      _ = R := rfl
  have hdiff : ∀ᵐ U ∂Λ.haarMeasure, ∀ β ∈ Metric.ball β₀ 1,
      HasDerivAt (fun z ↦ subsetIntegrand Λ Φ z X U)
        (subsetIntegrandDerivative Λ Φ β X U) β :=
    ae_of_all _ fun U β _ ↦ hasDerivAt_subsetIntegrand Λ Φ β X U
  simpa only [subsetWeight] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun β U ↦ subsetIntegrand Λ Φ β X U)
      (F' := fun β U ↦ subsetIntegrandDerivative Λ Φ β X U)
      (bound := fun _ ↦ C)
      (Metric.ball_mem_nhds β₀ (by norm_num : (0 : ℝ) < 1))
      hmeas (integrable_subsetIntegrand Λ Φ β₀ X) hderivMeas hbound
      (integrable_const C) hdiff).2

/-- Every finite connected-polymer activity is entire in the complex
coupling. -/
theorem subsetWeight_entire
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (X : Finset (Plaquette d)) :
    AnalyticOnNhd ℂ (fun β ↦ subsetWeight Λ Φ β X) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  intro β
  exact (hasDerivAt_subsetWeight Λ Φ X β).differentiableAt

/-! ## Translation covariance -/

omit [BorelSpace G] [SecondCountableTopology G] in
/-- Translating the plaquette set and relabeling all dynamic variables leaves
the subset integrand unchanged. -/
theorem subsetIntegrand_translate
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (X : Finset (Plaquette d)) (v : Site d)
    (U : DynamicConfiguration Λ) :
    subsetIntegrand (Λ.translate v) Φ β
        (X.map (Plaquette.translationEquiv v).toEmbedding)
        (Λ.translateDynamic v U) =
      subsetIntegrand Λ Φ β X U := by
  classical
  unfold subsetIntegrand
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro p hp
  change plaquettePerturbation (Λ.translate v) Φ β (p.translate v)
      (Λ.translateDynamic v U) = plaquettePerturbation Λ Φ β p U
  unfold plaquettePerturbation
  rw [Gauge.FiniteVolume.plaquetteHolonomy_translate]

/-- Haar-integrated subset weights are invariant under simultaneous lattice
translation of the finite specification and the plaquette support. -/
theorem subsetWeight_translate
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (X : Finset (Plaquette d)) (v : Site d) :
    subsetWeight (Λ.translate v) Φ β
        (X.map (Plaquette.translationEquiv v).toEmbedding) =
      subsetWeight Λ Φ β X := by
  let f : DynamicConfiguration (Λ.translate v) → ℂ :=
    subsetIntegrand (Λ.translate v) Φ β
      (X.map (Plaquette.translationEquiv v).toEmbedding)
  let e := Λ.translateDynamicEquiv v
  let T := ProductHaar.reindexEquiv (G := G) e
  have hT := ProductHaar.measurePreserving_reindex (G := G) e
  have heq : Λ.translateDynamic v = T := by
    funext U j
    change U (e.symm j) = T U j
    symm
    exact ProductHaar.reindex_apply e U j
  have h := hT.integral_comp' f
  rw [← heq] at h
  simpa only [subsetWeight, f, subsetIntegrand_translate] using h.symm

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- The integrand over a pairwise-disjoint family of plaquette sets is the
product of the component integrands. -/
theorem subsetIntegrand_biUnion
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (s : Finset (Finset (Plaquette d)))
    (hpair : (s : Set (Finset (Plaquette d))).Pairwise Disjoint)
    (U : DynamicConfiguration Λ) :
    subsetIntegrand Λ Φ β (s.biUnion id) U =
      ∏ X ∈ s, subsetIntegrand Λ Φ β X U := by
  classical
  unfold subsetIntegrand
  exact Finset.prod_biUnion hpair

/-- Haar integration factors over a pairwise-disjoint family of plaquette
sets whose dynamic edge supports are pairwise disjoint. -/
theorem subsetWeight_biUnion
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (s : Finset (Finset (Plaquette d)))
    (hplaquettes : (s : Set (Finset (Plaquette d))).Pairwise Disjoint)
    (hedges : (s : Set (Finset (Plaquette d))).Pairwise fun X Y =>
      Disjoint (subsetCoordinateSupport Λ X : Set Λ.dynamicEdges)
        (subsetCoordinateSupport Λ Y : Set Λ.dynamicEdges)) :
    subsetWeight Λ Φ β (s.biUnion id) =
      ∏ X ∈ s, subsetWeight Λ Φ β X := by
  classical
  rw [subsetWeight]
  simp_rw [subsetIntegrand_biUnion Λ Φ β s hplaquettes]
  simpa only [subsetWeight, FiniteSpecification.haarMeasure] using
    (Gauge.ProductHaar.integral_prod_of_pairwise_disjoint_dependsOn
      (G := G) (𝕜 := ℂ) s
      (fun X => subsetIntegrand Λ Φ β X)
      (fun X => (subsetCoordinateSupport Λ X : Set Λ.dynamicEdges))
      hedges
      (fun X _ => subsetIntegrand_dependsOn Λ Φ β X)
      (fun X _ => (continuous_subsetIntegrand Λ Φ β X).measurable))

/-- Exact plaquette-subset expansion of the finite-volume Yang--Mills
partition function. -/
theorem complexPartitionFunction_eq_sum_subsetWeight
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ) :
    complexPartitionFunction Λ Φ β =
      ∑ X ∈ Λ.activePlaquettes.powerset, subsetWeight Λ Φ β X := by
  rw [complexPartitionFunction]
  simp_rw [complexBoltzmannWeight_eq_sum_subsetIntegrand Λ Φ β]
  rw [integral_finsetSum]
  · rfl
  · intro X _
    exact integrable_subsetIntegrand Λ Φ β X

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] in
/-- Integrated subset weights obey the same cardinality majorant. -/
theorem norm_subsetWeight_le
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (X : Finset (Plaquette d)) :
    ‖subsetWeight Λ Φ β X‖ ≤ perturbationMajorant Φ β ^ X.card := by
  unfold subsetWeight
  simpa using norm_integral_le_of_norm_le_const (μ := Λ.haarMeasure)
    (ae_of_all _ fun U => norm_subsetIntegrand_le Λ Φ β X U)

end

end YangMills.StrongCoupling
