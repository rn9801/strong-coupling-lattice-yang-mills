/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.FiniteVolume
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Complex finite-volume partition function

The complexified partition function uses `Complex.exp` and is kept separate
from the real Gibbs-probability API. An explicit finite action bound justifies
differentiation under the integral on a neighborhood of every complex
coupling, proving that the finite-volume partition function is entire.
-/

open Filter MeasureTheory Set Metric
open scoped Topology

namespace YangMills.Gauge.FiniteVolume

open Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Complexified Boltzmann weight. -/
def complexBoltzmannWeight
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (U : DynamicConfiguration Λ) : ℂ :=
  Complex.exp (β * (action Λ Φ U : ℂ))

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
@[simp]
theorem complexBoltzmannWeight_ofReal
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (U : DynamicConfiguration Λ) :
    complexBoltzmannWeight Λ Φ (β : ℂ) U =
      (boltzmannWeight Λ Φ β U : ℂ) := by
  simp [complexBoltzmannWeight, boltzmannWeight]

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [GaugeHaarProbability G] in
/-- The complex weight is continuous in the dynamic variables. -/
theorem continuous_complexBoltzmannWeight
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ) :
    Continuous (complexBoltzmannWeight Λ Φ β) :=
  Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_action Λ Φ)))

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Uniform norm bound at a fixed complex coupling. -/
theorem norm_complexBoltzmannWeight_le
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (U : DynamicConfiguration Λ) :
    ‖complexBoltzmannWeight Λ Φ β U‖ ≤
      Real.exp (‖β‖ * actionBound Λ Φ) := by
  rw [complexBoltzmannWeight, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (β * (action Λ Φ U : ℂ)).re ≤ ‖β * (action Λ Φ U : ℂ)‖ :=
      Complex.re_le_norm _
    _ = ‖β‖ * ‖(action Λ Φ U : ℂ)‖ := norm_mul _ _
    _ ≤ ‖β‖ * actionBound Λ Φ := by
      gcongr
      simpa only [Complex.norm_real] using norm_action_le Λ Φ U

/-- Complex weights are integrable at every coupling. -/
theorem integrable_complexBoltzmannWeight
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ) :
    Integrable (complexBoltzmannWeight Λ Φ β) Λ.haarMeasure := by
  apply Integrable.of_bound (continuous_complexBoltzmannWeight Λ Φ β).aestronglyMeasurable
    (Real.exp (‖β‖ * actionBound Λ Φ))
  exact ae_of_all _ fun U => norm_complexBoltzmannWeight_le Λ Φ β U

/-- Complex finite-volume partition function. -/
def complexPartitionFunction
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ) : ℂ :=
  ∫ U, complexBoltzmannWeight Λ Φ β U ∂Λ.haarMeasure

@[simp]
theorem complexPartitionFunction_ofReal
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ) :
    complexPartitionFunction Λ Φ (β : ℂ) =
      (partitionFunction Λ Φ β : ℂ) := by
  simp only [complexPartitionFunction, complexBoltzmannWeight_ofReal,
    partitionFunction]
  exact integral_ofReal

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] in
/-- The complex partition function also equals one at zero coupling. -/
@[simp]
theorem complexPartitionFunction_zero
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) :
    complexPartitionFunction Λ Φ 0 = 1 := by
  simp [complexPartitionFunction, complexBoltzmannWeight]

/-- Pointwise complex derivative of the Boltzmann weight. -/
def complexBoltzmannDerivative
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (U : DynamicConfiguration Λ) : ℂ :=
  Complex.exp (β * (action Λ Φ U : ℂ)) * (action Λ Φ U : ℂ)

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G] in
theorem hasDerivAt_complexBoltzmannWeight
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℂ) (U : DynamicConfiguration Λ) :
    HasDerivAt (fun z => complexBoltzmannWeight Λ Φ z U)
      (complexBoltzmannDerivative Λ Φ β U) β := by
  simpa only [complexBoltzmannWeight, complexBoltzmannDerivative, id_eq, one_mul] using
    ((hasDerivAt_id β).mul_const (action Λ Φ U : ℂ)).cexp

/-- Differentiation under the finite-volume integral is valid at every coupling. -/
theorem hasDerivAt_complexPartitionFunction
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β₀ : ℂ) :
    HasDerivAt (complexPartitionFunction Λ Φ)
      (∫ U, complexBoltzmannDerivative Λ Φ β₀ U ∂Λ.haarMeasure) β₀ := by
  let B := actionBound Λ Φ
  let R := ‖β₀‖ + 1
  let C := B * Real.exp (R * B)
  have hB : 0 ≤ B := actionBound_nonneg Λ Φ
  have hmeas : ∀ᶠ β in 𝓝 β₀,
      AEStronglyMeasurable (complexBoltzmannWeight Λ Φ β) Λ.haarMeasure :=
    Filter.Eventually.of_forall fun β =>
      (continuous_complexBoltzmannWeight Λ Φ β).aestronglyMeasurable
  have hderivMeas : AEStronglyMeasurable
      (complexBoltzmannDerivative Λ Φ β₀) Λ.haarMeasure := by
    apply Continuous.aestronglyMeasurable
    exact (continuous_complexBoltzmannWeight Λ Φ β₀).mul
      (Complex.continuous_ofReal.comp (continuous_action Λ Φ))
  have hbound : ∀ᵐ U ∂Λ.haarMeasure, ∀ β ∈ ball β₀ 1,
      ‖complexBoltzmannDerivative Λ Φ β U‖ ≤ C := by
    refine ae_of_all _ fun U β hβ => ?_
    have hβnorm : ‖β‖ ≤ R := by
      calc
        ‖β‖ = ‖β₀ + (β - β₀)‖ := by ring_nf
        _ ≤ ‖β₀‖ + ‖β - β₀‖ := norm_add_le _ _
        _ ≤ ‖β₀‖ + 1 := by
          exact add_le_add (le_refl ‖β₀‖) ((show ‖β - β₀‖ < 1 by
            simpa only [mem_ball, dist_eq_norm] using hβ).le)
        _ = R := rfl
    calc
      ‖complexBoltzmannDerivative Λ Φ β U‖ =
          ‖complexBoltzmannWeight Λ Φ β U‖ * ‖(action Λ Φ U : ℂ)‖ := by
        simp [complexBoltzmannDerivative, complexBoltzmannWeight]
      _ ≤ Real.exp (‖β‖ * B) * B := by
        gcongr
        · exact norm_complexBoltzmannWeight_le Λ Φ β U
        · simpa only [B, Complex.norm_real] using norm_action_le Λ Φ U
      _ ≤ Real.exp (R * B) * B := by
        gcongr
      _ = C := by simp [C, mul_comm]
  have hboundIntegrable : Integrable (fun _ : DynamicConfiguration Λ => C) Λ.haarMeasure :=
    integrable_const C
  have hdiff : ∀ᵐ U ∂Λ.haarMeasure, ∀ β ∈ ball β₀ 1,
      HasDerivAt (fun z => complexBoltzmannWeight Λ Φ z U)
        (complexBoltzmannDerivative Λ Φ β U) β :=
    ae_of_all _ fun U β _ => hasDerivAt_complexBoltzmannWeight Λ Φ β U
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := complexBoltzmannWeight Λ Φ)
    (F' := complexBoltzmannDerivative Λ Φ)
    (bound := fun _ => C)
    (ball_mem_nhds β₀ (by norm_num : (0 : ℝ) < 1))
    hmeas (integrable_complexBoltzmannWeight Λ Φ β₀) hderivMeas
    hbound hboundIntegrable hdiff).2

/-- The complex finite-volume partition function is entire. -/
theorem complexPartitionFunction_entire
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) :
    AnalyticOnNhd ℂ (complexPartitionFunction Λ Φ) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  intro β
  exact (hasDerivAt_complexPartitionFunction Λ Φ β).differentiableAt

end
end YangMills.Gauge.FiniteVolume
