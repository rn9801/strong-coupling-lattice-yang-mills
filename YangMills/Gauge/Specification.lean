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

/-- Transform only the frozen exterior field of a finite specification. -/
def gaugeTransformExterior (Λ : FiniteSpecification d G)
    (g : GaugeTransformation d G) : FiniteSpecification d G where
  dynamicEdges := Λ.dynamicEdges
  activePlaquettes := Λ.activePlaquettes
  exterior := gaugeTransform g Λ.exterior

@[simp]
theorem gaugeTransformExterior_dynamicEdges
    (Λ : FiniteSpecification d G) (g : GaugeTransformation d G) :
    (Λ.gaugeTransformExterior g).dynamicEdges = Λ.dynamicEdges := rfl

@[simp]
theorem gaugeTransformExterior_activePlaquettes
    (Λ : FiniteSpecification d G) (g : GaugeTransformation d G) :
    (Λ.gaugeTransformExterior g).activePlaquettes = Λ.activePlaquettes := rfl

/-- Simultaneously transforming the dynamic variables and frozen exterior
field transforms the evaluated full configuration pointwise. -/
theorem gaugeTransformExterior_evaluate_gaugeTransformDynamic
    (Λ : FiniteSpecification d G) (g : GaugeTransformation d G)
    (U : DynamicConfiguration Λ) :
    (Λ.gaugeTransformExterior g).evaluate (Λ.gaugeTransformDynamic g U) =
      gaugeTransform g (Λ.evaluate U) := by
  funext e
  by_cases he : e ∈ Λ.dynamicEdges
  · simp [FiniteSpecification.evaluate, gaugeTransformDynamic,
      gaugeTransformExterior, gaugeTransform, he]
  · simp [FiniteSpecification.evaluate, gaugeTransformExterior,
      gaugeTransform, he]

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

section Translation

/-- Translate every geometric datum in a finite specification.  The
exterior field is pulled back so that evaluating the translated dynamic
variables gives the translated full configuration. -/
def translate (Λ : FiniteSpecification d G) (v : Site d) :
    FiniteSpecification d G where
  dynamicEdges := Λ.dynamicEdges.map (PositiveEdge.translationEquiv v).toEmbedding
  activePlaquettes :=
    Λ.activePlaquettes.map (Plaquette.translationEquiv v).toEmbedding
  exterior := fun e => Λ.exterior (e.translate (-v))

@[simp]
theorem translate_dynamicEdges (Λ : FiniteSpecification d G) (v : Site d) :
    (Λ.translate v).dynamicEdges =
      Λ.dynamicEdges.map (PositiveEdge.translationEquiv v).toEmbedding :=
  rfl

@[simp]
theorem translate_activePlaquettes (Λ : FiniteSpecification d G) (v : Site d) :
    (Λ.translate v).activePlaquettes =
      Λ.activePlaquettes.map (Plaquette.translationEquiv v).toEmbedding :=
  rfl

/-- The finite dynamic coordinate families of a specification and its
translate are canonically equivalent. -/
def translateDynamicEquiv (Λ : FiniteSpecification d G) (v : Site d) :
    Λ.dynamicEdges ≃ (Λ.translate v).dynamicEdges where
  toFun e := ⟨e.1.translate v, by
    exact Finset.mem_map.mpr ⟨e.1, e.2, rfl⟩⟩
  invFun e := ⟨e.1.translate (-v), by
    have he : e.1 ∈
        Λ.dynamicEdges.map (PositiveEdge.translationEquiv v).toEmbedding := by
      exact e.2
    rw [Finset.mem_map_equiv] at he
    simpa using he⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/-- Relabel dynamic variables along a translation. -/
def translateDynamic (Λ : FiniteSpecification d G) (v : Site d)
    (U : DynamicConfiguration Λ) : DynamicConfiguration (Λ.translate v) :=
  fun e => U ((Λ.translateDynamicEquiv v).symm e)

@[simp]
theorem translateDynamic_apply (Λ : FiniteSpecification d G) (v : Site d)
    (U : DynamicConfiguration Λ) (e : (Λ.translate v).dynamicEdges) :
    Λ.translateDynamic v U e = U ⟨e.1.translate (-v), by
      have he : e.1 ∈
          Λ.dynamicEdges.map (PositiveEdge.translationEquiv v).toEmbedding := e.2
      rw [Finset.mem_map_equiv] at he
      simpa using he⟩ := by
  rfl

/-- Evaluation commutes with finite-volume translation and coordinate
relabeling. -/
theorem translate_evaluate_translateDynamic
    (Λ : FiniteSpecification d G) (v : Site d)
    (U : DynamicConfiguration Λ) :
    (Λ.translate v).evaluate (Λ.translateDynamic v U) =
      fun e => Λ.evaluate U (e.translate (-v)) := by
  funext e
  by_cases he : e ∈ (Λ.translate v).dynamicEdges
  · rw [(Λ.translate v).evaluate_of_mem _ e he]
    simp only [translateDynamic_apply]
    have hpre : e.translate (-v) ∈ Λ.dynamicEdges := by
      rw [translate_dynamicEdges, Finset.mem_map_equiv] at he
      simpa using he
    rw [Λ.evaluate_of_mem _ (e.translate (-v)) hpre]
  · rw [(Λ.translate v).evaluate_of_not_mem _ e he]
    have hpre : e.translate (-v) ∉ Λ.dynamicEdges := by
      intro hmem
      apply he
      rw [translate_dynamicEdges, Finset.mem_map_equiv]
      simpa using hmem
    rw [Λ.evaluate_of_not_mem _ (e.translate (-v)) hpre]
    rfl

end Translation

section Haar

variable [Group G] [MeasurableSpace G] [GaugeHaarProbability G]

/-- Product Haar probability on the dynamic variables. -/
noncomputable abbrev haarMeasure (Λ : FiniteSpecification d G) :
    Measure (DynamicConfiguration Λ) :=
  ProductHaar.measure G Λ.dynamicEdges

variable [MeasurableMul G]

/-- Translation relabeling preserves finite product Haar probability. -/
theorem measurePreserving_translateDynamic
    (Λ : FiniteSpecification d G) (v : Site d) :
    MeasurePreserving (Λ.translateDynamic v) Λ.haarMeasure
      (Λ.translate v).haarMeasure := by
  let e := Λ.translateDynamicEquiv v
  let T := ProductHaar.reindexEquiv (G := G) e
  have hT := ProductHaar.measurePreserving_reindex (G := G) e
  have heq : Λ.translateDynamic v = T := by
    funext U j
    change U (e.symm j) = T U j
    symm
    exact ProductHaar.reindex_apply e U j
  rw [heq]
  exact hT

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

/-- Complex-valued change of variables by a finite dynamic gauge
transformation. -/
theorem integral_gaugeTransformDynamic_complex
    (Λ : FiniteSpecification d G) (g : GaugeTransformation d G)
    (F : DynamicConfiguration Λ → ℂ)
    (hF : AEStronglyMeasurable F Λ.haarMeasure) :
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
