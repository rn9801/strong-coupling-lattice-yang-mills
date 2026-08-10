/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.FiniteMayer
import YangMills.StrongCoupling.ObservableRootPolymer

/-!
# Finite strong-coupling cluster expansion

This file instantiates the abstract finite Mayer logarithm and its weighted
pinned estimate with the explicit plaquette-animal Dobrushin certificate.  It
is the cluster-expansion bridge used by the thermodynamic-limit and
correlation layers; it does not use the Douglas influence-matrix baseline.
-/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Polymer

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- The explicit lattice disk supplies the Dobrushin certificate in exactly
the form consumed by the finite Mayer theorem. -/
theorem plaquettePolymerModel_dobrushin_of_norm_lt_latticeRadius
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    (plaquettePolymerModel Λ Φ β).DobrushinCertificate Finset.univ
      (plaquetteDobrushinWeight (perturbationMajorant Φ β)) := by
  apply plaquettePolymerModel_dobrushin Λ Φ β
    (cubicPlaquetteAnimalCertificate Λ)
  exact perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
    (16 * d) (2 ^ (16 * d)) hβ

/-- Finite-volume Mayer/log-partition identity for the plaquette gas at the
explicit strong-coupling radius.  The right side is the exact Yang--Mills
partition function, not merely a majorant. -/
theorem exp_plaquetteFiniteMayerSum_eq_complexPartitionFunction
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Complex.exp ((plaquettePolymerModel Λ Φ β).finiteMayerSum Finset.univ) =
      complexPartitionFunction Λ Φ β := by
  rw [complexPartitionFunction_eq_polymerPartition]
  exact (plaquettePolymerModel Λ Φ β).exp_finiteMayerSum_eq_partitionFunction_of_dobrushin
      (plaquetteDobrushinWeight (perturbationMajorant Φ β))
      (plaquettePolymerModel_dobrushin_of_norm_lt_latticeRadius Λ Φ hβ)

/-- Explicit weighted one-root/pinned tree bound for the plaquette gas.  It
is uniform in the finite specification and its frozen exterior condition. -/
theorem plaquetteWeightedPinnedTreeBound
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (γ : PlaquettePolymer Λ) :
    ‖(plaquettePolymerModel Λ Φ β).activity γ *
        ((plaquettePolymerModel Λ Φ β).partitionOn
            ((plaquettePolymerModel Λ Φ β).compatibleWith
              ((Finset.univ : Finset (PlaquettePolymer Λ)).erase γ) γ) /
          (plaquettePolymerModel Λ Φ β).partitionOn
            ((Finset.univ : Finset (PlaquettePolymer Λ)).erase γ))‖ ≤
      1 - Real.exp
        (-plaquetteDobrushinWeight (perturbationMajorant Φ β) γ) := by
  exact (plaquettePolymerModel Λ Φ β).norm_pinnedPartitionRatio_le_of_dobrushin Finset.univ
      (plaquetteDobrushinWeight (perturbationMajorant Φ β))
      (plaquettePolymerModel_dobrushin_of_norm_lt_latticeRadius Λ Φ hβ)
      Finset.univ (Finset.Subset.rfl) (Finset.mem_univ γ)

/-- Weighted telescope form used when a rooted connected tree deletes a
finite set of polymers. -/
theorem plaquetteWeightedDeletionTreeBound
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (U V : Finset (PlaquettePolymer Λ)) (hVU : V ⊆ U) :
    ‖(plaquettePolymerModel Λ Φ β).partitionOn V /
        (plaquettePolymerModel Λ Φ β).partitionOn U‖ ≤
      Real.exp (∑ δ ∈ U \ V,
        plaquetteDobrushinWeight (perturbationMajorant Φ β) δ) := by
  let M := plaquettePolymerModel Λ Φ β
  exact M.norm_partitionOn_subset_div_le_exp_sum_of_dobrushin Finset.univ
      (plaquetteDobrushinWeight (perturbationMajorant Φ β))
      (plaquettePolymerModel_dobrushin_of_norm_lt_latticeRadius Λ Φ hβ)
      U V (Finset.subset_univ U) hVU

end

end YangMills.StrongCoupling
