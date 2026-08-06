/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Probability.FiniteProductGibbs
import YangMills.StrongCoupling.BoundaryGeometry

/-!
# Gibbs specifications for arbitrary finite Yang--Mills boxes

This module instantiates the finite-product Gibbs construction with the
project's arbitrary finite specification, selected Haar probability, and
bounded plaquette action.  It supplies a genuine DLR specification on the
dynamic edges, not merely a periodic-torus surrogate.
-/

open MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The bounded energy `β A(U)` of an arbitrary finite Yang--Mills
specification. -/
def boxEnergy (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) : Probability.FiniteEnergy Λ.dynamicEdges G where
  energy := fun U => β * action Λ Φ U
  measurable_energy :=
    measurable_const.mul (continuous_action Λ Φ).measurable
  bound := |β| * actionBound Λ Φ
  bound_nonneg := mul_nonneg (abs_nonneg _) (actionBound_nonneg Λ Φ)
  norm_energy_le := fun U => by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_action_le Λ Φ U) (abs_nonneg β)

@[simp]
theorem boxEnergy_apply (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℝ)
    (U : DynamicConfiguration Λ) :
    boxEnergy Λ Φ β U = β * action Λ Φ U :=
  rfl

/-- The arbitrary-box Gibbs specification on dynamic edges. -/
def boxGibbsSpec (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℝ) :
    GibbsSpec Λ.dynamicEdges G :=
  (boxEnergy Λ Φ β).gibbsSpec (GaugeHaarProbability.haar G)

/-- The generic finite-product Gibbs law is definitionally the same tilt as
the project's finite-volume Gibbs measure. -/
theorem boxEnergy_gibbsMeasure_eq
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ) :
    (boxEnergy Λ Φ β).gibbsMeasure (GaugeHaarProbability.haar G) =
      gibbsMeasure Λ Φ β :=
  rfl

/-- Every arbitrary finite-volume Yang--Mills measure satisfies the full DLR
equations for `boxGibbsSpec`. -/
theorem gibbsMeasure_isGibbs_box
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℝ) :
    IsGibbsMeasure (boxGibbsSpec Λ Φ β) (gibbsMeasure Λ Φ β) := by
  simpa only [boxGibbsSpec, boxEnergy_gibbsMeasure_eq] using
    (boxEnergy Λ Φ β).gibbsMeasure_isGibbs (GaugeHaarProbability.haar G)

end

end YangMills.StrongCoupling
