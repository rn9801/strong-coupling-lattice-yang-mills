/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar probability data for gauge groups

`GaugeHaarProbability G` packages a selected probability measure on a
measurable group together with left, right, and inversion invariance. The
measure is explicit data so later finite products do not depend on a global
`MeasureSpace G` instance.

For a compact Hausdorff topological group with its Borel measurable structure,
`GaugeHaarProbability.ofCompact` constructs this data from Mathlib's Haar
measure normalized on the whole group. Right and inversion invariance are
derived from uniqueness of Haar probability, so the constructor applies to
noncommutative compact groups.
-/

open MeasureTheory Set

namespace YangMills.Gauge

/-- A chosen bi-invariant Haar probability measure for a measurable group. -/
class GaugeHaarProbability (G : Type*) [Group G] [MeasurableSpace G] where
  measure : Measure G
  isProbability : IsProbabilityMeasure measure
  isLeftInvariant : Measure.IsMulLeftInvariant measure
  isRightInvariant : Measure.IsMulRightInvariant measure
  isInvInvariant : Measure.IsInvInvariant measure

attribute [instance] GaugeHaarProbability.isProbability
  GaugeHaarProbability.isLeftInvariant GaugeHaarProbability.isRightInvariant
  GaugeHaarProbability.isInvInvariant

namespace GaugeHaarProbability

variable (G : Type*) [Group G] [MeasurableSpace G] [GaugeHaarProbability G]

/-- The selected Haar probability measure. -/
abbrev haar : Measure G := GaugeHaarProbability.measure

instance : IsProbabilityMeasure (haar G) := GaugeHaarProbability.isProbability
instance : Measure.IsMulLeftInvariant (haar G) := GaugeHaarProbability.isLeftInvariant
instance : Measure.IsMulRightInvariant (haar G) := GaugeHaarProbability.isRightInvariant
instance : Measure.IsInvInvariant (haar G) := GaugeHaarProbability.isInvInvariant

section MeasurableMul

variable [MeasurableMul G]

/-- Left multiplication preserves the selected Haar probability. -/
theorem measurePreserving_mulLeft (g : G) :
    MeasurePreserving (g * ·) (haar G) (haar G) :=
  MeasureTheory.measurePreserving_mul_left (haar G) g

/-- Right multiplication preserves the selected Haar probability. -/
theorem measurePreserving_mulRight (g : G) :
    MeasurePreserving (· * g) (haar G) (haar G) :=
  MeasureTheory.measurePreserving_mul_right (haar G) g

/-- Multiplication on the left and right by fixed group elements preserves Haar. -/
theorem measurePreserving_mulLeft_mulRight (a b : G) :
    MeasurePreserving (fun x => a * x * b) (haar G) (haar G) :=
  (measurePreserving_mulRight G b).comp (measurePreserving_mulLeft G a)

end MeasurableMul

section MeasurableInv

variable [MeasurableInv G]

/-- Inversion preserves the selected Haar probability. -/
theorem measurePreserving_inv :
    MeasurePreserving Inv.inv (haar G) (haar G) :=
  Measure.measurePreserving_inv (haar G)

end MeasurableInv

section CompactConstructor

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]

/-- The whole compact group, regarded as a positive compact set. -/
private noncomputable abbrev compactWhole : TopologicalSpace.PositiveCompacts G :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Mathlib's Haar measure normalized to give the whole compact group mass one. -/
private noncomputable abbrev compactHaar : Measure G :=
  Measure.haarMeasure (compactWhole G)

private instance compactHaar_isProbability : IsProbabilityMeasure (compactHaar G) where
  measure_univ := by
    exact Measure.haarMeasure_self (K₀ := compactWhole G)

private instance compactHaar_isRightInvariant : Measure.IsMulRightInvariant (compactHaar G) where
  map_mul_right_eq_self g := by
    letI : IsProbabilityMeasure (Measure.map (· * g) (compactHaar G)) :=
      Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure
      (Measure.map (· * g) (compactHaar G)) (compactHaar G)

private instance compactHaarInv_isHaar : Measure.IsHaarMeasure (compactHaar G).inv where
  toIsFiniteMeasureOnCompacts := inferInstance
  toIsMulLeftInvariant := inferInstance
  toIsOpenPosMeasure := inferInstance

private instance compactHaar_isInvInvariant : Measure.IsInvInvariant (compactHaar G) where
  inv_eq_self := by
    letI : IsProbabilityMeasure (compactHaar G).inv :=
      Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure
      (compactHaar G).inv (compactHaar G)

/-- Every compact Borel topological group has a bi-invariant Haar probability. -/
@[implicit_reducible] noncomputable def ofCompact : GaugeHaarProbability G where
  measure := compactHaar G
  isProbability := inferInstance
  isLeftInvariant := inferInstance
  isRightInvariant := inferInstance
  isInvInvariant := inferInstance

end CompactConstructor

end GaugeHaarProbability

end YangMills.Gauge
