/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.Specification
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# General real finite-volume plaquette model

This module defines a bounded continuous real plaquette potential, its action
on an arbitrary finite specification, the positive Boltzmann weight, partition
function, and normalized Gibbs expectation. All bounds are explicit and the
probabilistic layer uses `Real.exp` only.
-/

open MeasureTheory

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

/-- A bounded continuous real plaquette potential with the symmetries needed
for gauge theory and orientation independence. -/
structure RealPlaquettePotential (G : Type*) [Group G] [TopologicalSpace G] where
  toContinuousMap : C(G, ℝ)
  conj_invariant : ∀ a x, toContinuousMap (a * x * a⁻¹) = toContinuousMap x
  inv_invariant : ∀ x, toContinuousMap x⁻¹ = toContinuousMap x
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le_bound : ∀ x, ‖toContinuousMap x‖ ≤ bound

namespace RealPlaquettePotential

variable {G : Type*} [Group G] [TopologicalSpace G]

instance : CoeFun (RealPlaquettePotential G) fun _ => G → ℝ :=
  ⟨fun Φ => Φ.toContinuousMap⟩

@[simp]
theorem coe_apply (Φ : RealPlaquettePotential G) (x : G) :
    Φ.toContinuousMap x = Φ x :=
  rfl

end RealPlaquettePotential

namespace FiniteVolume

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Holonomy of an active plaquette after gluing dynamic and exterior values. -/
def plaquetteHolonomy (Λ : FiniteSpecification d G) (U : DynamicConfiguration Λ)
    (p : Plaquette d) : G :=
  holonomy (Λ.evaluate U) p.boundary

/-- Sum of the plaquette potential over the active plaquettes. -/
def action (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (U : DynamicConfiguration Λ) : ℝ :=
  ∑ p ∈ Λ.activePlaquettes, Φ (plaquetteHolonomy Λ U p)

omit [IsTopologicalGroup G] in
/-- Uniform action bound supplied by the number of active plaquettes. -/
def actionBound (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) : ℝ :=
  Λ.activePlaquettes.card * Φ.bound

omit [IsTopologicalGroup G] in
theorem actionBound_nonneg (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) :
    0 ≤ actionBound Λ Φ := by
  exact mul_nonneg (Nat.cast_nonneg _) Φ.bound_nonneg

/-- A fixed plaquette holonomy is continuous in the dynamic variables. -/
theorem continuous_plaquetteHolonomy (Λ : FiniteSpecification d G) (p : Plaquette d) :
    Continuous (fun U => plaquetteHolonomy Λ U p) :=
  (continuous_holonomy p.boundary).comp Λ.continuous_evaluate

/-- The finite-volume action is continuous. -/
theorem continuous_action (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) :
    Continuous (action Λ Φ) := by
  unfold action
  exact continuous_finsetSum Λ.activePlaquettes fun p _ =>
    Φ.toContinuousMap.continuous.comp (continuous_plaquetteHolonomy Λ p)

section TranslationCovariance

/-- Plaquette holonomy is unchanged after translating the specification,
dynamic variables, and plaquette together. -/
theorem plaquetteHolonomy_translate
    (Λ : FiniteSpecification d G) (v : Site d)
    (U : DynamicConfiguration Λ) (p : Plaquette d) :
    plaquetteHolonomy (Λ.translate v) (Λ.translateDynamic v U)
        (p.translate v) =
      plaquetteHolonomy Λ U p := by
  unfold plaquetteHolonomy
  rw [Λ.translate_evaluate_translateDynamic]
  change holonomy (fun e => Λ.evaluate U (e.translate (-v)))
      (p.translate v).boundary = holonomy (Λ.evaluate U) p.boundary
  rw [holonomy_plaquette_translate]
  rw [Plaquette.translate_neg_self]

/-- The finite-volume action is unchanged by lattice translation. -/
theorem action_translate
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (v : Site d) (U : DynamicConfiguration Λ) :
    action (Λ.translate v) Φ (Λ.translateDynamic v U) = action Λ Φ U := by
  unfold action
  rw [FiniteSpecification.translate_activePlaquettes,
    Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p hp
  change Φ (plaquetteHolonomy (Λ.translate v) (Λ.translateDynamic v U)
      (p.translate v)) = Φ (plaquetteHolonomy Λ U p)
  rw [plaquetteHolonomy_translate]

end TranslationCovariance

omit [IsTopologicalGroup G] in
/-- Absolute value of the action is controlled uniformly. -/
theorem norm_action_le (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (U : DynamicConfiguration Λ) :
    ‖action Λ Φ U‖ ≤ actionBound Λ Φ := by
  unfold action actionBound
  calc
    ‖∑ p ∈ Λ.activePlaquettes, Φ (plaquetteHolonomy Λ U p)‖ ≤
        ∑ p ∈ Λ.activePlaquettes, ‖Φ (plaquetteHolonomy Λ U p)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ Λ.activePlaquettes, Φ.bound := by
      exact Finset.sum_le_sum fun p _ => Φ.norm_le_bound (plaquetteHolonomy Λ U p)
    _ = Λ.activePlaquettes.card * Φ.bound := by
      simp [nsmul_eq_mul]

/-- Real finite-volume Boltzmann weight. -/
def boltzmannWeight (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (U : DynamicConfiguration Λ) : ℝ :=
  Real.exp (β * action Λ Φ U)

omit [IsTopologicalGroup G] in
theorem boltzmannWeight_pos (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (U : DynamicConfiguration Λ) :
    0 < boltzmannWeight Λ Φ β U :=
  Real.exp_pos _

/-- The Boltzmann weight is continuous. -/
theorem continuous_boltzmannWeight
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ) :
    Continuous (boltzmannWeight Λ Φ β) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_action Λ Φ))

omit [IsTopologicalGroup G] in
/-- A uniform exponential bound for the Boltzmann weight. -/
theorem boltzmannWeight_le
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (U : DynamicConfiguration Λ) :
    boltzmannWeight Λ Φ β U ≤ Real.exp (|β| * actionBound Λ Φ) := by
  apply Real.exp_le_exp.mpr
  calc
    β * action Λ Φ U ≤ |β * action Λ Φ U| := le_abs_self _
    _ = |β| * |action Λ Φ U| := abs_mul _ _
    _ ≤ |β| * actionBound Λ Φ := by
      gcongr
      simpa only [Real.norm_eq_abs] using norm_action_le Λ Φ U

section Haar

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Every real Boltzmann weight is integrable against finite product Haar. -/
theorem integrable_boltzmannWeight
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ) :
    Integrable (boltzmannWeight Λ Φ β) Λ.haarMeasure := by
  apply Integrable.of_bound (continuous_boltzmannWeight Λ Φ β).aestronglyMeasurable
    (Real.exp (|β| * actionBound Λ Φ))
  exact ae_of_all _ fun U => by
    rw [Real.norm_eq_abs, abs_of_pos (boltzmannWeight_pos Λ Φ β U)]
    exact boltzmannWeight_le Λ Φ β U

/-- A bounded measurable observable remains integrable after multiplication by
the finite-volume Boltzmann weight. -/
theorem integrable_boltzmannWeight_mul_of_norm_le
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (F : DynamicConfiguration Λ → ℝ) (C : ℝ)
    (hF : AEStronglyMeasurable F Λ.haarMeasure)
    (hC : ∀ U, ‖F U‖ ≤ C) :
    Integrable (fun U => boltzmannWeight Λ Φ β U * F U) Λ.haarMeasure := by
  apply Integrable.of_bound
    ((continuous_boltzmannWeight Λ Φ β).aestronglyMeasurable.mul hF)
    (Real.exp (|β| * actionBound Λ Φ) * C)
  exact ae_of_all _ fun U => by
    change ‖boltzmannWeight Λ Φ β U * F U‖ ≤
      Real.exp (|β| * actionBound Λ Φ) * C
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_pos (boltzmannWeight_pos Λ Φ β U)]
    exact mul_le_mul (boltzmannWeight_le Λ Φ β U) (hC U)
      (norm_nonneg _) (Real.exp_pos _).le

/-- The real finite-volume partition function. -/
noncomputable def partitionFunction
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ) : ℝ :=
  ∫ U, boltzmannWeight Λ Φ β U ∂Λ.haarMeasure

/-- The real partition function is strictly positive. -/
theorem partitionFunction_pos
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ) :
    0 < partitionFunction Λ Φ β := by
  unfold partitionFunction boltzmannWeight
  exact integral_exp_pos (integrable_boltzmannWeight Λ Φ β)

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] in
/-- At zero coupling, every arbitrary finite specification has partition function one. -/
@[simp]
theorem partitionFunction_zero
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) :
    partitionFunction Λ Φ 0 = 1 := by
  simp [partitionFunction, boltzmannWeight]

/-- Normalized Gibbs expectation of a real finite-volume observable. -/
noncomputable def gibbsExpectation
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (F : DynamicConfiguration Λ → ℝ) : ℝ :=
  (partitionFunction Λ Φ β)⁻¹ *
    ∫ U, boltzmannWeight Λ Φ β U * F U ∂Λ.haarMeasure

/-- The finite-volume Gibbs probability measure, packaged as the exponential
tilt of product Haar by the action. -/
noncomputable def gibbsMeasure
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ) :
    Measure (DynamicConfiguration Λ) :=
  Λ.haarMeasure.tilted fun U => β * action Λ Φ U

instance instIsProbabilityMeasureGibbsMeasure
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ) :
    IsProbabilityMeasure (gibbsMeasure Λ Φ β) := by
  apply isProbabilityMeasure_tilted
  simpa only [boltzmannWeight] using integrable_boltzmannWeight Λ Φ β

/-- Ratio-of-Haar-integrals expectations are ordinary integrals against the
finite-volume Gibbs probability measure. -/
theorem gibbsExpectation_eq_integral_gibbsMeasure
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (F : DynamicConfiguration Λ → ℝ) :
    gibbsExpectation Λ Φ β F = ∫ U, F U ∂gibbsMeasure Λ Φ β := by
  rw [gibbsMeasure, integral_tilted]
  simp only [smul_eq_mul, boltzmannWeight, gibbsExpectation, partitionFunction]
  have hZ : (∫ U, Real.exp (β * action Λ Φ U) ∂Λ.haarMeasure) ≠ 0 :=
    (partitionFunction_pos Λ Φ β).ne'
  rw [← integral_const_mul]
  congr 1
  funext U
  field_simp

/-- Translation covariance of complex-valued Gibbs integrals. -/
theorem integral_gibbsMeasure_translate
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (v : Site d) (F : DynamicConfiguration (Λ.translate v) → ℂ)
    (hF : Measurable F) :
    ∫ V, F V ∂gibbsMeasure (Λ.translate v) Φ β =
      ∫ U, F (Λ.translateDynamic v U) ∂gibbsMeasure Λ Φ β := by
  let T := Λ.translateDynamic v
  let e := Λ.translateDynamicEquiv v
  let Tmeas := ProductHaar.reindexEquiv (G := G) e
  have hTmeas := ProductHaar.measurePreserving_reindex (G := G) e
  have hTeq : T = Tmeas := by
    funext U j
    change U (e.symm j) = Tmeas U j
    symm
    exact ProductHaar.reindex_apply e U j
  rw [gibbsMeasure, gibbsMeasure, integral_tilted, integral_tilted]
  let Z := ∫ U, Real.exp (β * action Λ Φ U) ∂Λ.haarMeasure
  have hZ : (∫ V, Real.exp (β * action (Λ.translate v) Φ V)
      ∂(Λ.translate v).haarMeasure) = Z := by
    have hchange := hTmeas.integral_comp'
      (fun V => Real.exp (β * action (Λ.translate v) Φ V))
    rw [← hTeq] at hchange
    simpa only [T, action_translate, Z] using hchange.symm
  rw [hZ]
  let H : DynamicConfiguration (Λ.translate v) → ℂ := fun V =>
    (Real.exp (β * action (Λ.translate v) Φ V) / Z : ℝ) • F V
  have hchange := hTmeas.integral_comp' H
  rw [← hTeq] at hchange
  simpa only [H, T, action_translate] using hchange.symm

/-- Gibbs expectation is normalized on the constant-one observable. -/
@[simp]
theorem gibbsExpectation_one
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ) :
    gibbsExpectation Λ Φ β (fun _ => 1) = 1 := by
  unfold gibbsExpectation partitionFunction
  simp only [mul_one]
  exact inv_mul_cancel₀ (partitionFunction_pos Λ Φ β).ne'

/-- The normalized expectation of an observable bounded by `C` is also
bounded by `C`. -/
theorem norm_gibbsExpectation_le
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (F : DynamicConfiguration Λ → ℝ) (C : ℝ)
    (hF : AEStronglyMeasurable F Λ.haarMeasure)
    (hC : ∀ U, ‖F U‖ ≤ C) :
    ‖gibbsExpectation Λ Φ β F‖ ≤ C := by
  let w := boltzmannWeight Λ Φ β
  let Z := partitionFunction Λ Φ β
  have hZ : 0 < Z := partitionFunction_pos Λ Φ β
  have hwF : Integrable (fun U => w U * F U) Λ.haarMeasure :=
    integrable_boltzmannWeight_mul_of_norm_le Λ Φ β F C hF hC
  have hCw : Integrable (fun U => C * w U) Λ.haarMeasure :=
    (integrable_boltzmannWeight Λ Φ β).const_mul C
  have hnum : ‖∫ U, w U * F U ∂Λ.haarMeasure‖ ≤ C * Z := by
    calc
      ‖∫ U, w U * F U ∂Λ.haarMeasure‖ ≤
          ∫ U, ‖w U * F U‖ ∂Λ.haarMeasure :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ U, C * w U ∂Λ.haarMeasure := by
        apply integral_mono hwF.norm hCw
        intro U
        change ‖w U * F U‖ ≤ C * w U
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos (boltzmannWeight_pos Λ Φ β U)]
        simpa only [w, mul_comm] using
          (mul_le_mul_of_nonneg_left (hC U) (boltzmannWeight_pos Λ Φ β U).le)
      _ = C * Z := by
        simp only [integral_const_mul, w, Z, partitionFunction]
  rw [gibbsExpectation, Real.norm_eq_abs, abs_mul, abs_inv,
    abs_of_pos hZ, ← Real.norm_eq_abs] at *
  calc
    Z⁻¹ * ‖∫ U, w U * F U ∂Λ.haarMeasure‖ ≤ Z⁻¹ * (C * Z) :=
      mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hZ.le)
    _ = C := by field_simp

section GaugeInvariance

variable [MeasurableMul G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G]
    [MeasurableMul G] in
/-- Boundary-compatible transformations conjugate every active plaquette holonomy. -/
theorem plaquetteHolonomy_gaugeTransform
    (Λ : FiniteSpecification d G) (g : GaugeTransformation d G)
    (hg : Λ.BoundaryCompatible g) (U : DynamicConfiguration Λ) (p : Plaquette d) :
    plaquetteHolonomy Λ (Λ.gaugeTransformDynamic g U) p =
      g p.base * plaquetteHolonomy Λ U p * (g p.base)⁻¹ := by
  unfold plaquetteHolonomy
  rw [Λ.evaluate_gaugeTransformDynamic g hg U]
  exact holonomy_loop_gaugeTransform g (Λ.evaluate U) p.boundary

/-- Transforming both dynamic and exterior data conjugates every plaquette
holonomy, without a boundary-compatibility restriction. -/
theorem plaquetteHolonomy_gaugeTransformExterior
    (Λ : FiniteSpecification d G) (g : GaugeTransformation d G)
    (U : DynamicConfiguration Λ) (p : Plaquette d) :
    plaquetteHolonomy (Λ.gaugeTransformExterior g)
        (Λ.gaugeTransformDynamic g U) p =
      g p.base * plaquetteHolonomy Λ U p * (g p.base)⁻¹ := by
  unfold plaquetteHolonomy
  rw [Λ.gaugeTransformExterior_evaluate_gaugeTransformDynamic g U]
  exact holonomy_loop_gaugeTransform g (Λ.evaluate U) p.boundary

/-- The action is covariant when the frozen exterior field is transformed
together with the dynamic variables. -/
theorem action_gaugeTransformExterior
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (g : GaugeTransformation d G) (U : DynamicConfiguration Λ) :
    action (Λ.gaugeTransformExterior g) Φ (Λ.gaugeTransformDynamic g U) =
      action Λ Φ U := by
  unfold action
  apply Finset.sum_congr rfl
  intro p hp
  rw [plaquetteHolonomy_gaugeTransformExterior Λ g U p]
  exact Φ.conj_invariant (g p.base) (plaquetteHolonomy Λ U p)

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G] [MeasurableMul G] in
/-- The finite-volume action is invariant under boundary-compatible gauge transformations. -/
theorem action_gaugeInvariant
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (g : GaugeTransformation d G) (hg : Λ.BoundaryCompatible g)
    (U : DynamicConfiguration Λ) :
    action Λ Φ (Λ.gaugeTransformDynamic g U) = action Λ Φ U := by
  unfold action
  apply Finset.sum_congr rfl
  intro p hp
  rw [plaquetteHolonomy_gaugeTransform Λ g hg U p]
  exact Φ.conj_invariant (g p.base) (plaquetteHolonomy Λ U p)

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G] [MeasurableMul G] in
/-- The real Boltzmann weight is gauge invariant. -/
theorem boltzmannWeight_gaugeInvariant
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (g : GaugeTransformation d G) (hg : Λ.BoundaryCompatible g)
    (U : DynamicConfiguration Λ) :
    boltzmannWeight Λ Φ β (Λ.gaugeTransformDynamic g U) =
      boltzmannWeight Λ Φ β U := by
  simp only [boltzmannWeight, action_gaugeInvariant Λ Φ g hg U]

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G]
    [MeasurableMul G] in
/-- The partition integrand is unchanged after a boundary-compatible gauge change of variables. -/
theorem partitionFunction_gaugeInvariant
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (g : GaugeTransformation d G) (hg : Λ.BoundaryCompatible g) :
    (∫ U, boltzmannWeight Λ Φ β (Λ.gaugeTransformDynamic g U) ∂Λ.haarMeasure) =
      partitionFunction Λ Φ β := by
  unfold partitionFunction
  apply integral_congr_ae
  exact ae_of_all _ fun U => boltzmannWeight_gaugeInvariant Λ Φ β g hg U

/-- Gibbs expectations are invariant under transforming their observable argument. -/
theorem gibbsExpectation_gaugeTransform
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (g : GaugeTransformation d G) (hg : Λ.BoundaryCompatible g)
    (F : DynamicConfiguration Λ → ℝ)
    (hF : AEStronglyMeasurable F Λ.haarMeasure) :
    gibbsExpectation Λ Φ β (fun U => F (Λ.gaugeTransformDynamic g U)) =
      gibbsExpectation Λ Φ β F := by
  unfold gibbsExpectation
  congr 1
  let H := fun U => boltzmannWeight Λ Φ β U * F U
  have hH : AEStronglyMeasurable H Λ.haarMeasure :=
    (continuous_boltzmannWeight Λ Φ β).aestronglyMeasurable.mul hF
  rw [← Λ.integral_gaugeTransformDynamic g H hH]
  apply integral_congr_ae
  exact ae_of_all _ fun U => by
    simp only [H, boltzmannWeight_gaugeInvariant Λ Φ β g hg U]

/-- Complex local-observable expectations are invariant under every
boundary-compatible finite-volume gauge transformation. -/
theorem integral_gibbsMeasure_gaugeTransform_complex
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (g : GaugeTransformation d G) (hg : Λ.BoundaryCompatible g)
    (F : DynamicConfiguration Λ → ℂ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ U, ‖F U‖ ≤ C) :
    ∫ U, F (Λ.gaugeTransformDynamic g U) ∂gibbsMeasure Λ Φ β =
      ∫ U, F U ∂gibbsMeasure Λ Φ β := by
  rw [gibbsMeasure, integral_tilted, integral_tilted]
  let Z := ∫ U, Real.exp (β * action Λ Φ U) ∂Λ.haarMeasure
  let H : DynamicConfiguration Λ → ℂ := fun U =>
    (Real.exp (β * action Λ Φ U) / Z : ℝ) • F U
  have hH : AEStronglyMeasurable H Λ.haarMeasure := by
    exact ((measurable_const.mul (continuous_action Λ Φ).measurable).exp.div_const _)
      |>.aestronglyMeasurable.smul hF.aestronglyMeasurable
  rw [← Λ.integral_gaugeTransformDynamic_complex g H hH]
  apply integral_congr_ae
  exact ae_of_all _ fun U => by
    change (Real.exp (β * action Λ Φ U) / Z : ℝ) •
        F (Λ.gaugeTransformDynamic g U) =
      (Real.exp (β * action Λ Φ (Λ.gaugeTransformDynamic g U)) / Z : ℝ) •
        F (Λ.gaugeTransformDynamic g U)
    rw [action_gaugeInvariant Λ Φ g hg U]

/-- Gauge covariance of complex local-observable expectations when the
frozen exterior field is transformed together with the observable. -/
theorem integral_gibbsMeasure_gaugeTransformExterior_complex
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (g : GaugeTransformation d G)
    (F : Configuration d G → ℂ) (hF : Measurable F) :
    ∫ V, F ((Λ.gaugeTransformExterior g).evaluate V)
        ∂gibbsMeasure (Λ.gaugeTransformExterior g) Φ β =
      ∫ U, F (gaugeTransform g (Λ.evaluate U))
        ∂gibbsMeasure Λ Φ β := by
  let T := Λ.gaugeTransformDynamic g
  have hT := Λ.measurePreserving_gaugeTransformDynamic g
  rw [gibbsMeasure, gibbsMeasure, integral_tilted, integral_tilted]
  let Z := ∫ U, Real.exp (β * action Λ Φ U) ∂Λ.haarMeasure
  have hZ : (∫ V, Real.exp
      (β * action (Λ.gaugeTransformExterior g) Φ V)
        ∂(Λ.gaugeTransformExterior g).haarMeasure) = Z := by
    have hmeas : AEStronglyMeasurable
        (fun V => Real.exp (β * action (Λ.gaugeTransformExterior g) Φ V))
        (Λ.gaugeTransformExterior g).haarMeasure :=
      (measurable_const.mul
        (continuous_action (Λ.gaugeTransformExterior g) Φ).measurable).exp
        |>.aestronglyMeasurable
    have hchange := Λ.integral_gaugeTransformDynamic g
      (fun V => Real.exp
        (β * action (Λ.gaugeTransformExterior g) Φ V)) hmeas
    simpa only [FiniteSpecification.gaugeTransformExterior_dynamicEdges,
      FiniteSpecification.haarMeasure, T,
      action_gaugeTransformExterior Λ Φ g] using hchange.symm
  rw [hZ]
  have hmeas : AEStronglyMeasurable
      (fun V : DynamicConfiguration (Λ.gaugeTransformExterior g) =>
        (Real.exp (β * action (Λ.gaugeTransformExterior g) Φ V) / Z : ℝ) •
          F ((Λ.gaugeTransformExterior g).evaluate V))
      (Λ.gaugeTransformExterior g).haarMeasure := by
    exact ((measurable_const.mul
      (continuous_action (Λ.gaugeTransformExterior g) Φ).measurable).exp.div_const _)
      |>.aestronglyMeasurable.smul
        ((hF.comp (Λ.gaugeTransformExterior g).continuous_evaluate.measurable)
          |>.aestronglyMeasurable)
  have hchange := Λ.integral_gaugeTransformDynamic_complex g
    (fun V : DynamicConfiguration (Λ.gaugeTransformExterior g) =>
      (Real.exp (β * action (Λ.gaugeTransformExterior g) Φ V) / Z : ℝ) •
        F ((Λ.gaugeTransformExterior g).evaluate V)) hmeas
  simpa only [FiniteSpecification.gaugeTransformExterior_dynamicEdges,
    FiniteSpecification.haarMeasure, T,
    action_gaugeTransformExterior Λ Φ g,
    FiniteSpecification.gaugeTransformExterior_evaluate_gaugeTransformDynamic]
    using hchange.symm

end GaugeInvariance

end Haar

end FiniteVolume

end

end YangMills.Gauge
