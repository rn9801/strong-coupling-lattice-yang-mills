/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.Influence
import YangMills.StrongCoupling.BoundaryDecay
import YangMills.StrongCoupling.BoundaryGeometry

/-! # Milestone 10 foundation regression tests -/

namespace YangMills.Tests.Milestone10Foundations

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Polymer
open YangMills.Gauge.FiniteVolume YangMills.StrongCoupling

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The marked numerator has the exact plaquette-subset expansion. -/
example (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    complexObservableNumerator F Λ Φ β =
      ∑ X ∈ Λ.activePlaquettes.powerset, markedSubsetWeight F Λ Φ β X :=
  complexObservableNumerator_eq_sum_markedSubsetWeight F Λ Φ β

/-- Observable roots are uniformly linear in the recorded edge support. -/
example (F : LocalObservable d G) (Λ : FiniteSpecification d G) :
    (observableRootPlaquettes Λ F).card ≤ 4 * d * F.support.card :=
  card_observableRootPlaquettes_le Λ F

/-- The Dobrushin strong-coupling disk is always genuinely positive. -/
example (Φ : RealPlaquettePotential G) :
    0 < boxDobrushinRadius d Φ.bound :=
  boxDobrushinRadius_pos Φ.bound Φ.bound_nonneg

/-- Selected plaquettes away from the exact disagreement set have identical
marked activities for both exterior configurations. -/
example (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (X : Finset (Plaquette d))
    (η η' : Configuration d G) (hF : F.support ⊆ Λ.dynamicEdges)
    (hX : X ⊆ Λ.activePlaquettes)
    (hdisjoint : Disjoint (activeSubset Λ X)
      (boundaryDisagreementPlaquettes Λ η η')) :
    markedSubsetWeight F (withExterior Λ η) Φ β X =
      markedSubsetWeight F (withExterior Λ η') Φ β X :=
  markedSubsetWeight_withExterior_eq_of_disjoint_defects
    F Λ Φ β X η η' hF hX hdisjoint

#print axioms YangMills.Polymer.neumannInfluenceToSet_le_exponential
#print axioms YangMills.StrongCoupling.complexObservableNumerator_eq_sum_markedSubsetWeight
#print axioms YangMills.StrongCoupling.plaquette_dist_lt_card_of_connected_subset
#print axioms YangMills.StrongCoupling.box_dobrushinCondition_of_abs_lt_radius
#print axioms YangMills.StrongCoupling.complexGibbsExpectation_boundaryDecay

end

end YangMills.Tests.Milestone10Foundations
