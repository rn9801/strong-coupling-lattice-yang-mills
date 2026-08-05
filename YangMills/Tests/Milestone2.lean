/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.FiniteEdgeHaar

/-!
# Milestone 2 executable regressions

These examples lock the compact-group constructor, coordinate reindexing,
disjoint-support factorization, and the finite gauge-invariance exit theorem.
-/

open MeasureTheory

namespace YangMills.Tests.Milestone2

open YangMills.Gauge
open YangMills.Lattice.Cubic

section CompactConstructor

variable (K : Type*) [Group K] [TopologicalSpace K] [MeasurableSpace K]
  [IsTopologicalGroup K] [CompactSpace K] [BorelSpace K]

noncomputable example : GaugeHaarProbability K :=
  GaugeHaarProbability.ofCompact K

end CompactConstructor

section ProductHaar

variable {G : Type*} [Group G] [MeasurableSpace G] [GaugeHaarProbability G]

example {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    Measure.map (ProductHaar.reindexEquiv (G := G) e) (ProductHaar.measure G ι) =
      ProductHaar.measure G κ :=
  (ProductHaar.measurePreserving_reindex (G := G) e).map_eq

example {ι : Type*} [Fintype ι]
    (f g : (ι → G) → ℝ) (S T : Set ι)
    (hf : DependsOn f S) (hg : DependsOn g T)
    (hST : Disjoint S T) (hfm : Measurable f) (hgm : Measurable g) :
    ∫ U, f U * g U ∂ProductHaar.measure G ι =
      (∫ U, f U ∂ProductHaar.measure G ι) *
        ∫ U, g U ∂ProductHaar.measure G ι :=
  ProductHaar.integral_mul_of_disjoint_dependsOn f g S T hf hg hST hfm hgm

end ProductHaar

section GaugeTransform

variable {G : Type*} [Group G] [MeasurableSpace G] [GaugeHaarProbability G]
  [MeasurableMul G]

/-- The Milestone 2 exit criterion: independent Haar edge variables remain
product Haar after an arbitrary finite gauge transformation. -/
example {d : ℕ} (b : Box d) (g : FiniteEdgeHaar.SiteField b G) :
    Measure.map (FiniteEdgeHaar.gaugeTransform b g)
        (FiniteEdgeHaar.edgeMeasure (G := G) b) =
      FiniteEdgeHaar.edgeMeasure (G := G) b :=
  FiniteEdgeHaar.productHaar_map_gaugeTransform b g

end GaugeTransform

#print axioms YangMills.Gauge.GaugeHaarProbability.ofCompact
#print axioms YangMills.Gauge.ProductHaar.integral_mul_of_disjoint_dependsOn
#print axioms YangMills.Gauge.FiniteEdgeHaar.productHaar_map_gaugeTransform

end YangMills.Tests.Milestone2
