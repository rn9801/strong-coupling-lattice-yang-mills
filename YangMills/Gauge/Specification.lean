/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.Holonomy
import YangMills.Gauge.ProductHaar
import YangMills.Lattice.Plaquette

/-!
# Arbitrary finite-volume specifications

A finite specification chooses the positive edges integrated over, the
plaquettes entering the action, and an explicit exterior configuration used on
every frozen edge. No geometric boundary convention is built into this layer.
-/

open MeasureTheory

namespace YangMills.Gauge

open Lattice.Cubic

/-- Dynamic edges, active plaquettes, and frozen exterior edge values. -/
structure FiniteSpecification (d : ℕ) (G : Type*) where
  dynamicEdges : Finset (PositiveEdge d)
  activePlaquettes : Finset (Plaquette d)
  exterior : Configuration d G

/-- The finite product of group variables integrated by a specification. -/
abbrev DynamicConfiguration {d : ℕ} {G : Type*} (Λ : FiniteSpecification d G) :=
  Λ.dynamicEdges → G

namespace FiniteSpecification

variable {d : ℕ} {G : Type*}

/-- Glue dynamic variables to the fixed exterior configuration. -/
def evaluate (Λ : FiniteSpecification d G) (U : DynamicConfiguration Λ) :
    Configuration d G :=
  fun e => if he : e ∈ Λ.dynamicEdges then U ⟨e, he⟩ else Λ.exterior e

@[simp]
theorem evaluate_of_mem (Λ : FiniteSpecification d G) (U : DynamicConfiguration Λ)
    (e : PositiveEdge d) (he : e ∈ Λ.dynamicEdges) :
    Λ.evaluate U e = U ⟨e, he⟩ := by
  simp [evaluate, he]

@[simp]
theorem evaluate_of_not_mem (Λ : FiniteSpecification d G) (U : DynamicConfiguration Λ)
    (e : PositiveEdge d) (he : e ∉ Λ.dynamicEdges) :
    Λ.evaluate U e = Λ.exterior e := by
  simp [evaluate, he]

section Topology

variable [TopologicalSpace G]

/-- Exterior gluing is continuous in the finite dynamic variables. -/
theorem continuous_evaluate (Λ : FiniteSpecification d G) :
    Continuous Λ.evaluate := by
  apply continuous_pi
  intro e
  by_cases he : e ∈ Λ.dynamicEdges
  · simpa only [evaluate, he, dif_pos] using
      (continuous_apply (⟨e, he⟩ : Λ.dynamicEdges))
  · simpa only [evaluate, he, dif_neg] using
      (continuous_const : Continuous fun _ : DynamicConfiguration Λ => Λ.exterior e)

end Topology

section GaugeAction

variable [Group G]

/-- The coordinatewise action on the dynamic variables of a specification. -/
def gaugeTransformDynamic (Λ : FiniteSpecification d G)
    (g : GaugeTransformation d G) (U : DynamicConfiguration Λ) :
    DynamicConfiguration Λ :=
  fun e => g e.1.source * U e * (g e.1.target)⁻¹

/-- A site field is compatible with fixed exterior data when it fixes every
frozen edge value. This is the precise admissibility condition used below. -/
def BoundaryCompatible (Λ : FiniteSpecification d G)
    (g : GaugeTransformation d G) : Prop :=
  ∀ e, e ∉ Λ.dynamicEdges →
    g e.source * Λ.exterior e * (g e.target)⁻¹ = Λ.exterior e

/-- Gluing commutes with every boundary-compatible gauge transformation. -/
theorem evaluate_gaugeTransformDynamic
    (Λ : FiniteSpecification d G) (g : GaugeTransformation d G)
    (hg : Λ.BoundaryCompatible g) (U : DynamicConfiguration Λ) :
    Λ.evaluate (Λ.gaugeTransformDynamic g U) = gaugeTransform g (Λ.evaluate U) := by
  funext e
  by_cases he : e ∈ Λ.dynamicEdges
  · simp [evaluate, gaugeTransformDynamic, gaugeTransform, he]
  · simp [evaluate, gaugeTransform, he, hg e he]

end GaugeAction

section Haar

variable [Group G] [MeasurableSpace G] [GaugeHaarProbability G]

/-- Product Haar probability on the dynamic variables. -/
noncomputable abbrev haarMeasure (Λ : FiniteSpecification d G) :
    Measure (DynamicConfiguration Λ) :=
  ProductHaar.measure G Λ.dynamicEdges

variable [MeasurableMul G]

/-- Dynamic gauge transformations preserve finite product Haar probability. -/
theorem measurePreserving_gaugeTransformDynamic
    (Λ : FiniteSpecification d G) (g : GaugeTransformation d G) :
    MeasurePreserving (Λ.gaugeTransformDynamic g) Λ.haarMeasure Λ.haarMeasure := by
  simpa only [haarMeasure, gaugeTransformDynamic, ProductHaar.measure] using
    (ProductHaar.measurePreserving_coordinatewise
      (G := G) (fun _ : Λ.dynamicEdges => GaugeHaarProbability.haar G)
      (fun e x => g e.1.source * x * (g e.1.target)⁻¹)
      (fun e => GaugeHaarProbability.measurePreserving_mulLeft_mulRight G
        (g e.1.source) (g e.1.target)⁻¹))

/-- Change variables by a finite dynamic gauge transformation. -/
theorem integral_gaugeTransformDynamic
    (Λ : FiniteSpecification d G) (g : GaugeTransformation d G)
    (F : DynamicConfiguration Λ → ℝ) (hF : AEStronglyMeasurable F Λ.haarMeasure) :
    ∫ U, F (Λ.gaugeTransformDynamic g U) ∂Λ.haarMeasure =
      ∫ U, F U ∂Λ.haarMeasure := by
  let T := Λ.gaugeTransformDynamic g
  have hT := Λ.measurePreserving_gaugeTransformDynamic g
  have hFmap : AEStronglyMeasurable F (Measure.map T Λ.haarMeasure) := by
    rw [hT.map_eq]
    exact hF
  calc
    ∫ U, F (T U) ∂Λ.haarMeasure = ∫ U, F U ∂Measure.map T Λ.haarMeasure :=
      (MeasureTheory.integral_map hT.measurable.aemeasurable hFmap).symm
    _ = ∫ U, F U ∂Λ.haarMeasure := by rw [hT.map_eq]

end Haar

end FiniteSpecification

end YangMills.Gauge
