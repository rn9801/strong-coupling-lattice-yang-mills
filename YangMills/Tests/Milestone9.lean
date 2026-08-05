/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.Counting

/-! # Milestone 9 regression tests -/

namespace YangMills.Tests.Milestone9

open MeasureTheory
open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Polymer
open YangMills.Gauge.FiniteVolume YangMills.StrongCoupling

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- The plaquette degree bound is independent of the finite specification. -/
example (Λ : FiniteSpecification d G) (p : ActivePlaquette Λ) :
    (plaquetteAdjacencyGraph Λ).degree p ≤ 16 * d :=
  plaquetteAdjacency_degree_le Λ p

/-- The automatically constructed animal certificate has dimension-only
constants. -/
example (Λ : FiniteSpecification d G) :
    (cubicPlaquetteAnimalCertificate Λ).animalConstant = 2 ^ (16 * d) := rfl

/-- The strong-coupling disk has strictly positive radius. -/
example (Φ : RealPlaquettePotential G) :
    0 < latticeStrongCouplingRadius d Φ.bound :=
  latticeStrongCouplingRadius_pos d Φ.bound_nonneg

/-- Milestone 9 exit theorem: uniform finite-volume zero-freeness. -/
example (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    {β : ℂ} (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    complexPartitionFunction Λ Φ β ≠ 0 :=
  complexPartitionFunction_ne_zero_of_norm_lt_latticeRadius Λ Φ hβ

#print axioms YangMills.StrongCoupling.card_rootedAnimals_le_pow_degree
#print axioms YangMills.StrongCoupling.plaquetteAdjacency_degree_le
#print axioms YangMills.StrongCoupling.complexPartitionFunction_ne_zero_of_norm_lt_latticeRadius

end

end YangMills.Tests.Milestone9
