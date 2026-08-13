/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.FiniteMayer
import YangMills.Polymer.LabelledMayerExponential
import YangMills.Polymer.LabelledRootedForestSpecies
import YangMills.Polymer.MayerEvaluation
import YangMills.StrongCoupling.ObservableRootPolymer

/-!
# Finite strong-coupling cluster expansion

This file instantiates the symmetric finite Mayer logarithm and its genuine
weighted KP/tree estimate with the explicit plaquette-animal certificate.  It
is the cluster-expansion bridge used by the thermodynamic-limit and
correlation layers; it does not use the Douglas influence-matrix baseline.

The older deletion-ratio consequences are retained below as a separately
named finite-volume baseline.  The symmetric logarithm and summability
theorems do not depend on that route.
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

/-- The explicit lattice disk also supplies the genuine Kotecký--Preiss
activity-sum certificate used by the Penrose/rooted-tree expansion. -/
theorem plaquettePolymerModel_koteckyPreiss_of_norm_lt_latticeRadius
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    (plaquettePolymerModel Λ Φ β).KoteckyPreissCertificate Finset.univ
      plaquetteKPWeight := by
  apply plaquettePolymerModel_koteckyPreiss Λ Φ β
    (cubicPlaquetteAnimalCertificate Λ)
  exact perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
    (16 * d) (2 ^ (16 * d)) hβ

/-- Absolute summability of the genuine rooted-tree height layers on the
explicit strong-coupling disk. -/
theorem summable_plaquetteKPTreeLayer
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (γ : PlaquettePolymer Λ) :
    Summable ((plaquettePolymerModel Λ Φ β).kpTreeLayer Finset.univ γ) := by
  exact (plaquettePolymerModel Λ Φ β).summable_kpTreeLayer_of_koteckyPreiss
      Finset.univ plaquetteKPWeight
      (plaquettePolymerModel_koteckyPreiss_of_norm_lt_latticeRadius Λ Φ hβ)
      γ (Finset.mem_univ γ)

/-- Explicit rooted-tree KP budget.  Since `a(γ)=|γ| log 2`, the total
tree layer mass is at most `2^|γ|-1`. -/
theorem tsum_plaquetteKPTreeLayer_le
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (γ : PlaquettePolymer Λ) :
    ∑' n : ℕ,
        (plaquettePolymerModel Λ Φ β).kpTreeLayer Finset.univ γ n ≤
      (2 : ℝ) ^ γ.1.card - 1 := by
  have h := (plaquettePolymerModel Λ Φ β).tsum_kpTreeLayer_le_exp_sub_one_of_koteckyPreiss
      Finset.univ
      plaquetteKPWeight
      (plaquettePolymerModel_koteckyPreiss_of_norm_lt_latticeRadius Λ Φ hβ)
      γ (Finset.mem_univ γ)
  simpa [plaquetteKPWeight, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h

/-- Genuine KP/tree absolute summability of the full positive-degree
plaquette Mayer expansion, uniformly in the finite specification and frozen
exterior field. -/
theorem summable_plaquetteNormMayerDegreeSum_succ
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable (fun n : ℕ ↦
      (plaquettePolymerModel Λ Φ β).normMayerDegreeSum (n + 1)) := by
  exact (plaquettePolymerModel Λ Φ β).summable_normMayerDegreeSum_succ_of_koteckyPreiss_certified
      plaquetteKPWeight
      (plaquettePolymerModel_koteckyPreiss_of_norm_lt_latticeRadius
        Λ Φ hβ)

/-- Explicit symmetry-normalized pinned tree budget supplied by the genuine
KP certificate.  The left side is the residual rooted Mayer-tree orbit sum,
not a deletion ratio. -/
theorem plaquetteWeightedPinnedTreeOrbitBound
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (γ : PlaquettePolymer Λ) :
    ∑' n : ℕ,
        (plaquettePolymerModel Λ Φ β).residualSymmetricPinnedTreeDegreeSum γ n ≤
      (2 : ℝ) ^ γ.1.card := by
  have h := (plaquettePolymerModel Λ Φ β).tsum_residualSymmetricPinnedTreeDegreeSum_le_of_koteckyPreiss_certified
      plaquetteKPWeight
      (plaquettePolymerModel_koteckyPreiss_of_norm_lt_latticeRadius
        Λ Φ hβ) γ
  simpa [plaquetteKPWeight, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h

/-- Exact finite connected Mayer/log identity in the canonical formal
branch.  Unlike the deletion-ordered scalar theorem below, this theorem is
purely the fixed-labelled cluster exponential formula and has no Dobrushin
hypothesis. -/
theorem plaquetteRestrictedSymmetricMayerPowerSeries_eq_formalMayerLog
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ) :
    (plaquettePolymerModel Λ Φ β).restrictedSymmetricMayerPowerSeries Finset.univ =
      (plaquettePolymerModel Λ Φ β).formalMayerLog Finset.univ := by
  exact (plaquettePolymerModel Λ Φ β).restrictedSymmetricMayerPowerSeries_eq_formalMayerLog
    Finset.univ

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

/-- The genuine symmetry-normalized connected cluster sum exponentiates to
the exact finite Yang--Mills partition function.  This is the scalar
evaluation of the labelled Mayer exponential formula using only the explicit
KP certificate. -/
theorem exp_plaquetteSymmetricMayerSum_eq_complexPartitionFunction
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Complex.exp ((plaquettePolymerModel Λ Φ β).symmetricMayerSum) =
      complexPartitionFunction Λ Φ β := by
  rw [complexPartitionFunction_eq_polymerPartition]
  exact FinitePolymerModel.exp_symmetricMayerSum_eq_partitionFunction_of_koteckyPreiss
      (plaquettePolymerModel Λ Φ β)
      plaquetteKPWeight
      (plaquettePolymerModel_koteckyPreiss_of_norm_lt_latticeRadius Λ Φ hβ)

/-- Zero-freeness on the explicit disk, derived from the genuine KP/Mayer
exponential identity rather than from the deletion/Dobrushin baseline. -/
theorem complexPartitionFunction_ne_zero_of_norm_lt_latticeRadius_koteckyPreiss
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    complexPartitionFunction Λ Φ β ≠ 0 := by
  rw [← exp_plaquetteSymmetricMayerSum_eq_complexPartitionFunction Λ Φ hβ]
  exact Complex.exp_ne_zero _

/-- Every normalized finite-volume local expectation is analytic throughout
the explicit zero-free strong-coupling disk. -/
theorem analyticOnNhd_complexGibbsExpectation
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) :
    AnalyticOnNhd ℂ (complexGibbsExpectation F Λ Φ)
      (Metric.ball 0 (latticeStrongCouplingRadius d Φ.bound)) := by
  have hnum : AnalyticOnNhd ℂ (complexObservableNumerator F Λ Φ)
      (Metric.ball 0 (latticeStrongCouplingRadius d Φ.bound)) :=
    (complexObservableNumerator_entire F Λ Φ).mono (Set.subset_univ _)
  have hden : AnalyticOnNhd ℂ (complexPartitionFunction Λ Φ)
      (Metric.ball 0 (latticeStrongCouplingRadius d Φ.bound)) :=
    (complexPartitionFunction_entire Λ Φ).mono (Set.subset_univ _)
  have hquot := hnum.div hden (fun β hβ =>
    complexPartitionFunction_ne_zero_of_norm_lt_latticeRadius_koteckyPreiss Λ Φ (by
      simpa only [Metric.mem_ball, dist_zero_right] using hβ))
  change AnalyticOnNhd ℂ (fun β ↦
    (complexPartitionFunction Λ Φ β)⁻¹ * complexObservableNumerator F Λ Φ β)
      (Metric.ball 0 (latticeStrongCouplingRadius d Φ.bound))
  simpa only [div_eq_mul_inv, mul_comm] using hquot

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

/-- Absolute pinned Mayer-series bound on the explicit lattice disk.  Unlike
the pointwise partition-ratio estimate above, this controls the sum of the
norms of every repeated insertion term and places the whole rooted logarithm
inside its Dobrushin weight budget. -/
theorem plaquetteAbsolutePinnedMayerSeriesBound
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (T : Finset (PlaquettePolymer Λ)) {γ : PlaquettePolymer Λ}
    (hγT : γ ∉ T) :
    ∑' n : ℕ,
        ‖(plaquettePolymerModel Λ Φ β).mayerInsertionTerm γ T n‖ ≤
      plaquetteDobrushinWeight (perturbationMajorant Φ β) γ := by
  exact (plaquettePolymerModel Λ Φ β).tsum_norm_mayerInsertionTerm_le_of_dobrushin
      Finset.univ
      (plaquetteDobrushinWeight (perturbationMajorant Φ β))
      (plaquettePolymerModel_dobrushin_of_norm_lt_latticeRadius Λ Φ hβ)
      T (Finset.subset_univ T) hγT (Finset.mem_univ γ)

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
