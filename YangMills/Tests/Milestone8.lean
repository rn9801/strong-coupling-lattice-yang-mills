/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.PlaquettePolymer

/-! # Milestone 8 regression tests -/

namespace YangMills.Tests.Milestone8

open MeasureTheory
open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Polymer
open YangMills.Gauge.FiniteVolume YangMills.StrongCoupling

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Connected-component factorization is derived from product Haar locality. -/
example (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ) :
    HasExactComponentFactorization Λ Φ β :=
  hasExactComponentFactorization Λ Φ β

/-- Milestone 8 exit theorem: exact equality with the abstract polymer gas. -/
example (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ) :
    complexPartitionFunction Λ Φ β =
      (plaquettePolymerModel Λ Φ β).partitionFunction :=
  complexPartitionFunction_eq_polymerPartition Λ Φ β

#print axioms YangMills.StrongCoupling.hasExactComponentFactorization
#print axioms YangMills.StrongCoupling.complexPartitionFunction_eq_polymerPartition

end

end YangMills.Tests.Milestone8
