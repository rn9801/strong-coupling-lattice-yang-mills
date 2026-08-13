/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Basic.AnalyticLimit
import YangMills.StrongCoupling.CenteredInfiniteVolume
import YangMills.StrongCoupling.ClusterBoundaryExpansion
import YangMills.StrongCoupling.ThermodynamicCluster
import YangMills.StrongCoupling.FiniteClusterExpansion

/-!
# Analytic infinite-volume local expectations

This file completes the local-observable half of Milestone 14 by applying a
disk Vitali theorem to finite-volume complex Gibbs expectations.  The normal-
family input is not an abstract compactness assumption: it is the explicit,
volume-independent decorated observable-root KP/tree estimate.  On the real
diameter, the limit is identified with the cluster-expansion infinite-volume
probability from Milestones 11--13.

Thus analyticity is derived from the same decorated cluster expansion and
uniform KP/tree estimates used for the thermodynamic limit.
-/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Polymer
open Filter Metric Set MeasureTheory
open scoped Topology BigOperators

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Finite centered complex expectations, the analytic sequence whose
thermodynamic limit is selected by the decorated cluster expansion. -/
def centeredComplexLocalExpectationSequence
    (F : LocalObservable d G) (η : ℕ → Configuration d G)
    (Φ : RealPlaquettePotential G) (n : ℕ) (z : ℂ) : ℂ :=
  complexGibbsExpectation F (centeredSpecification n (η n)) Φ z

/-- Explicit volume-independent decorated KP majorant on a closed complex
subdisk. -/
def centeredComplexLocalExpectationBound
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) (r : ℝ) : ℝ :=
  ‖F.toBoundedContinuousMap‖ *
    Real.exp (((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2) *
    Real.exp
      (((4 * d * F.support.card : ℕ) : ℝ) *
        ((2 * perturbationMajorant Φ (r : ℂ)) /
          (1 - (2 ^ (16 * d) : ℝ) *
            (2 * perturbationMajorant Φ (r : ℂ)))))

theorem centeredComplexLocalExpectationBound_nonneg
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) (r : ℝ) :
    0 ≤ centeredComplexLocalExpectationBound F Φ r := by
  unfold centeredComplexLocalExpectationBound
  positivity

private theorem twice_majorant_fraction_mono
    (C q Q : ℝ) (hC0 : 0 ≤ C) (hqQ : q ≤ Q)
    (hCQ : C * (2 * Q) < 1) :
    (2 * q) / (1 - C * (2 * q)) ≤
      (2 * Q) / (1 - C * (2 * Q)) := by
  have hdenQ : 0 < 1 - C * (2 * Q) := sub_pos.mpr hCQ
  have hCq : C * (2 * q) ≤ C * (2 * Q) := by gcongr
  have hdenq : 0 < 1 - C * (2 * q) := sub_pos.mpr (hCq.trans_lt hCQ)
  rw [div_le_div_iff₀ hdenq hdenQ]
  nlinarith

/-- The decorated one-root KP/tree majorant is independent of the finite
geometry and its frozen exterior field.  The centered-box estimate below is
just the principal thermodynamic application of this general bound. -/
theorem norm_complexGibbsExpectation_le_centeredBound
    (F : LocalObservable d G) (Lambda : FiniteSpecification d G)
    (Phi : RealPlaquettePotential G) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < latticeStrongCouplingRadius d Phi.bound)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) :
    ‖complexGibbsExpectation F Lambda Phi z‖ ≤
      centeredComplexLocalExpectationBound F Phi r := by
  have hzr : ‖z‖ ≤ r := by
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hzsmall : ‖z‖ < latticeStrongCouplingRadius d Phi.bound := hzr.trans_lt hr
  let c : ℕ → ℂ := fun k ↦
    decoratedObservableRootLinearMayerDegreeSum F Lambda Phi z k
  have hnorm : Summable (fun k ↦ ‖c k‖) :=
    summable_norm_decoratedObservableRootLinearMayerDegreeSum F Lambda Phi hzsmall
  have hshift : Summable (fun k ↦ ‖c (k + 1)‖) :=
    summable_norm_decoratedObservableRootLinearMayerDegreeSum_succ F Lambda Phi hzsmall
  have hseries : complexGibbsExpectation F Lambda Phi z =
      ∑' k : ℕ, c (k + 1) := by
    rw [complexGibbsExpectation_eq_tsum_connectedDecoratedRoot F Lambda Phi hzsmall
      (complexPartitionFunction_ne_zero_of_norm_lt_latticeRadius_koteckyPreiss
        Lambda Phi hzsmall)]
    have hsplit := hnorm.of_norm.sum_add_tsum_nat_add 1
    have hzero : c 0 = 0 := by simp [c]
    simp only [Finset.sum_range_one, hzero, zero_add] at hsplit
    exact hsplit.symm
  have hq : perturbationMajorant Phi z ≤ perturbationMajorant Phi (r : ℂ) :=
    perturbationMajorant_le_of_norm_le_real Phi z r hzr
  have hrnorm : ‖(r : ℂ)‖ < latticeStrongCouplingRadius d Phi.bound := by
    simpa [Complex.norm_real, abs_of_nonneg hr0] using hr
  have hCsmall := animalConstant_mul_two_mul_perturbationMajorant_lt_one Phi hrnorm
  have hfrac := twice_majorant_fraction_mono
    (2 ^ (16 * d) : ℝ) (perturbationMajorant Phi z)
      (perturbationMajorant Phi (r : ℂ))
      (by positivity) hq hCsmall
  have hcard : ((observableRootPlaquettes Lambda F).card : ℝ) ≤
      ((4 * d * F.support.card : ℕ) : ℝ) := by
    exact_mod_cast card_observableRootPlaquettes_le Lambda F
  rw [hseries]
  apply (norm_tsum_le_tsum_norm hshift).trans
  calc
    (∑' k : ℕ, ‖c (k + 1)‖) ≤
        ‖F.toBoundedContinuousMap‖ *
          Real.exp (((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2) *
          Real.exp
            (((observableRootPlaquettes Lambda F).card : ℝ) *
              ((2 * perturbationMajorant Phi z) /
                (1 - (2 ^ (16 * d) : ℝ) *
                  (2 * perturbationMajorant Phi z)))) := by
      simpa [c] using
        tsum_norm_decoratedObservableRootLinearMayerDegreeSum_succ_le
          F Lambda Phi hzsmall
    _ ≤ centeredComplexLocalExpectationBound F Phi r := by
      unfold centeredComplexLocalExpectationBound
      have hfrac0 : 0 ≤ (2 * perturbationMajorant Phi z) /
          (1 - (2 ^ (16 * d) : ℝ) *
            (2 * perturbationMajorant Phi z)) := by
        have hCq : (2 ^ (16 * d) : ℝ) *
            (2 * perturbationMajorant Phi z) < 1 := by
          exact (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hq (by norm_num)) (by positivity)).trans_lt hCsmall
        exact div_nonneg (mul_nonneg (by norm_num) (perturbationMajorant_nonneg Phi z))
          (sub_nonneg.mpr hCq.le)
      have hexp : Real.exp
          (((observableRootPlaquettes Lambda F).card : ℝ) *
            ((2 * perturbationMajorant Phi z) /
              (1 - (2 ^ (16 * d) : ℝ) *
                (2 * perturbationMajorant Phi z)))) ≤
        Real.exp
          (((4 * d * F.support.card : ℕ) : ℝ) *
            ((2 * perturbationMajorant Phi (r : ℂ)) /
              (1 - (2 ^ (16 * d) : ℝ) *
                (2 * perturbationMajorant Phi (r : ℂ))))) := by
        apply Real.exp_le_exp.mpr
        exact (mul_le_mul hcard hfrac hfrac0 (Nat.cast_nonneg _))
      gcongr

/-- Every member of the analytic sequence is exactly the absolutely
convergent connected decorated observable-root Mayer series, with its
zero-degree term removed. -/
theorem centeredComplexLocalExpectationSequence_eq_tsum_connectedDecoratedRoot
    (F : LocalObservable d G) (η : ℕ → Configuration d G)
    (Φ : RealPlaquettePotential G) {n : ℕ} {z : ℂ}
    (hz : ‖z‖ < latticeStrongCouplingRadius d Φ.bound) :
    centeredComplexLocalExpectationSequence F η Φ n z =
      ∑' k : ℕ, decoratedObservableRootLinearMayerDegreeSum F
        (centeredSpecification n (η n)) Φ z (k + 1) := by
  let Λ := centeredSpecification n (η n)
  let c : ℕ → ℂ := fun k ↦
    decoratedObservableRootLinearMayerDegreeSum F Λ Φ z k
  have hnorm : Summable (fun k ↦ ‖c k‖) :=
    summable_norm_decoratedObservableRootLinearMayerDegreeSum F Λ Φ hz
  rw [centeredComplexLocalExpectationSequence,
    complexGibbsExpectation_eq_tsum_connectedDecoratedRoot F Λ Φ hz
      (complexPartitionFunction_ne_zero_of_norm_lt_latticeRadius_koteckyPreiss Λ Φ hz)]
  have hsplit := hnorm.of_norm.sum_add_tsum_nat_add 1
  have hzero : c 0 = 0 := by simp [c]
  simp only [Finset.sum_range_one, hzero, zero_add] at hsplit
  exact hsplit.symm

theorem norm_centeredComplexLocalExpectationSequence_le_bound
    (F : LocalObservable d G) (η : ℕ → Configuration d G)
    (Φ : RealPlaquettePotential G) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < latticeStrongCouplingRadius d Φ.bound)
    (n : ℕ) (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) :
    ‖centeredComplexLocalExpectationSequence F η Φ n z‖ ≤
      centeredComplexLocalExpectationBound F Φ r := by
  have hzr : ‖z‖ ≤ r := by
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hzsmall : ‖z‖ < latticeStrongCouplingRadius d Φ.bound := hzr.trans_lt hr
  let Λ := centeredSpecification n (η n)
  let c : ℕ → ℂ := fun k ↦
    decoratedObservableRootLinearMayerDegreeSum F Λ Φ z k
  have hnorm : Summable (fun k ↦ ‖c k‖) :=
    summable_norm_decoratedObservableRootLinearMayerDegreeSum F Λ Φ hzsmall
  have hshift : Summable (fun k ↦ ‖c (k + 1)‖) :=
    summable_norm_decoratedObservableRootLinearMayerDegreeSum_succ F Λ Φ hzsmall
  have hseries : centeredComplexLocalExpectationSequence F η Φ n z =
      ∑' k : ℕ, c (k + 1) := by
    exact centeredComplexLocalExpectationSequence_eq_tsum_connectedDecoratedRoot
      F η Φ hzsmall
  have hq : perturbationMajorant Φ z ≤ perturbationMajorant Φ (r : ℂ) :=
    perturbationMajorant_le_of_norm_le_real Φ z r hzr
  have hrnorm : ‖(r : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound := by
    simpa [Complex.norm_real, abs_of_nonneg hr0] using hr
  have hCsmall := animalConstant_mul_two_mul_perturbationMajorant_lt_one Φ hrnorm
  have hfrac := twice_majorant_fraction_mono
    (2 ^ (16 * d) : ℝ) (perturbationMajorant Φ z)
      (perturbationMajorant Φ (r : ℂ))
      (by positivity) hq hCsmall
  have hcard : ((observableRootPlaquettes Λ F).card : ℝ) ≤
      ((4 * d * F.support.card : ℕ) : ℝ) := by
    exact_mod_cast card_observableRootPlaquettes_le Λ F
  rw [hseries]
  apply (norm_tsum_le_tsum_norm hshift).trans
  calc
    (∑' k : ℕ, ‖c (k + 1)‖) ≤
        ‖F.toBoundedContinuousMap‖ *
          Real.exp (((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2) *
          Real.exp
            (((observableRootPlaquettes Λ F).card : ℝ) *
              ((2 * perturbationMajorant Φ z) /
                (1 - (2 ^ (16 * d) : ℝ) *
                  (2 * perturbationMajorant Φ z)))) := by
      simpa [c] using
        tsum_norm_decoratedObservableRootLinearMayerDegreeSum_succ_le
          F Λ Φ hzsmall
    _ ≤ centeredComplexLocalExpectationBound F Φ r := by
      unfold centeredComplexLocalExpectationBound
      have hfrac0 : 0 ≤ (2 * perturbationMajorant Φ z) /
          (1 - (2 ^ (16 * d) : ℝ) *
            (2 * perturbationMajorant Φ z)) := by
        have hCq : (2 ^ (16 * d) : ℝ) *
            (2 * perturbationMajorant Φ z) < 1 := by
          exact (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hq (by norm_num)) (by positivity)).trans_lt hCsmall
        exact div_nonneg (mul_nonneg (by norm_num) (perturbationMajorant_nonneg Φ z))
          (sub_nonneg.mpr hCq.le)
      have hexp : Real.exp
          (((observableRootPlaquettes Λ F).card : ℝ) *
            ((2 * perturbationMajorant Φ z) /
              (1 - (2 ^ (16 * d) : ℝ) *
                (2 * perturbationMajorant Φ z)))) ≤
        Real.exp
          (((4 * d * F.support.card : ℕ) : ℝ) *
            ((2 * perturbationMajorant Φ (r : ℂ)) /
              (1 - (2 ^ (16 * d) : ℝ) *
                (2 * perturbationMajorant Φ (r : ℂ))))) := by
        apply Real.exp_le_exp.mpr
        exact (mul_le_mul hcard hfrac hfrac0 (Nat.cast_nonneg _))
      gcongr

/-- The strong-coupling analytic continuation of the infinite-volume local
expectation, selected as the Vitali limit of the decorated finite-volume
cluster series. -/
def analyticInfiniteVolumeLocalExpectation
    (F : LocalObservable d G) (η : ℕ → Configuration d G)
    (Φ : RealPlaquettePotential G) (z : ℂ) : ℂ :=
  YangMills.VitaliOnDisk.limit
    (centeredComplexLocalExpectationSequence F η Φ) z

/-- The physical real-axis local state, extended by zero outside the disk only
so that it can serve as the uniqueness set in the Vitali theorem. -/
def centeredInfiniteVolumeLocalExpectationOnReal
    (F : LocalObservable d G) (η : ℕ → Configuration d G)
    (Φ : RealPlaquettePotential G) (x : ℝ) : ℂ :=
  if hx : ‖(x : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound then
    ∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ x hx
  else 0

/-- The full Milestone 14 Vitali conclusion.  Its local boundedness input is
the explicit decorated observable-root KP/tree majorant above, while its
real-axis uniqueness input is the cluster-expansion thermodynamic limit. -/
theorem analyticInfiniteVolumeLocalExpectation_properties
    (F : LocalObservable d G) (η : ℕ → Configuration d G)
    (Φ : RealPlaquettePotential G) :
    AnalyticOnNhd ℂ (analyticInfiniteVolumeLocalExpectation F η Φ)
        (ball 0 (latticeStrongCouplingRadius d Φ.bound)) ∧
      TendstoLocallyUniformlyOn
        (centeredComplexLocalExpectationSequence F η Φ)
        (analyticInfiniteVolumeLocalExpectation F η Φ) atTop
        (ball 0 (latticeStrongCouplingRadius d Φ.bound)) ∧
      ∀ x : ℝ, |x| < latticeStrongCouplingRadius d Φ.bound →
        analyticInfiniteVolumeLocalExpectation F η Φ (x : ℂ) =
          centeredInfiniteVolumeLocalExpectationOnReal F η Φ x := by
  have hreal (x : ℝ) (hx : |x| < latticeStrongCouplingRadius d Φ.bound) :
      Tendsto (fun n ↦ centeredComplexLocalExpectationSequence F η Φ n (x : ℂ))
        atTop (nhds (centeredInfiniteVolumeLocalExpectationOnReal F η Φ x)) := by
    have hxcomplex : ‖(x : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound := by
      simpa [Complex.norm_real] using hx
    have h := tendsto_centered_localExpectation_infiniteVolume η Φ x hxcomplex F
    simpa only [centeredComplexLocalExpectationSequence,
      centeredGibbsSequence, localExpectation_fullGibbsProbability,
      centeredInfiniteVolumeLocalExpectationOnReal, dif_pos hxcomplex] using h
  exact YangMills.VitaliOnDisk.analytic_limit_and_tendstoLocallyUniformlyOn
    (latticeStrongCouplingRadius_pos d Φ.bound_nonneg)
    (fun n ↦ analyticOnNhd_complexGibbsExpectation F
      (centeredSpecification n (η n)) Φ)
    (fun r hr0 hr ↦ ⟨centeredComplexLocalExpectationBound F Φ r,
      centeredComplexLocalExpectationBound_nonneg F Φ r,
      fun n z hz ↦ norm_centeredComplexLocalExpectationSequence_le_bound
        F η Φ hr0 hr n z hz⟩)
    (centeredInfiniteVolumeLocalExpectationOnReal F η Φ) hreal

theorem analyticOnNhd_analyticInfiniteVolumeLocalExpectation
    (F : LocalObservable d G) (η : ℕ → Configuration d G)
    (Φ : RealPlaquettePotential G) :
    AnalyticOnNhd ℂ (analyticInfiniteVolumeLocalExpectation F η Φ)
      (ball 0 (latticeStrongCouplingRadius d Φ.bound)) :=
  (analyticInfiniteVolumeLocalExpectation_properties F η Φ).1

theorem tendstoLocallyUniformlyOn_centeredComplexLocalExpectationSequence
    (F : LocalObservable d G) (η : ℕ → Configuration d G)
    (Φ : RealPlaquettePotential G) :
    TendstoLocallyUniformlyOn
      (centeredComplexLocalExpectationSequence F η Φ)
      (analyticInfiniteVolumeLocalExpectation F η Φ) atTop
      (ball 0 (latticeStrongCouplingRadius d Φ.bound)) :=
  (analyticInfiniteVolumeLocalExpectation_properties F η Φ).2.1

/-- On real coupling the analytic continuation is exactly expectation against
the boundary-independent infinite-volume Gibbs probability from Milestones
11--13. -/
theorem analyticInfiniteVolumeLocalExpectation_ofReal
    (F : LocalObservable d G) (η : ℕ → Configuration d G)
    (Φ : RealPlaquettePotential G) (x : ℝ)
    (hx : ‖(x : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound) :
    analyticInfiniteVolumeLocalExpectation F η Φ (x : ℂ) =
      ∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ x hx := by
  have hxabs : |x| < latticeStrongCouplingRadius d Φ.bound := by
    simpa [Complex.norm_real] using hx
  rw [(analyticInfiniteVolumeLocalExpectation_properties F η Φ).2.2 x hxabs]
  unfold centeredInfiniteVolumeLocalExpectationOnReal
  rw [dif_pos hx]

/-- Although the analytic continuation was selected from an arbitrary
centered exterior sequence, it is independent of that choice throughout the
strong-coupling disk. -/
theorem analyticInfiniteVolumeLocalExpectation_boundary_independent
    (F : LocalObservable d G)
    (η η' : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) :
    Set.EqOn (analyticInfiniteVolumeLocalExpectation F η Φ)
      (analyticInfiniteVolumeLocalExpectation F η' Φ)
      (ball 0 (latticeStrongCouplingRadius d Φ.bound)) := by
  have hR := latticeStrongCouplingRadius_pos d Φ.bound_nonneg
  apply AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (analyticOnNhd_analyticInfiniteVolumeLocalExpectation F η Φ)
      (analyticOnNhd_analyticInfiniteVolumeLocalExpectation F η' Φ)
      isPreconnected_ball (mem_ball_self hR)
  let a : ℕ → ℝ := fun n ↦
    (latticeStrongCouplingRadius d Φ.bound / 2) *
      (1 / ((n + 1 : ℕ) : ℝ))
  have ha0 : Tendsto a atTop (nhds 0) := by
    simpa [a] using (tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (nhds 0)))
  have hac : Tendsto (fun n ↦ (a n : ℂ)) atTop (nhds 0) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp ha0
  apply mem_closure_of_tendsto hac
  filter_upwards [] with n
  have ha_pos : 0 < a n := by
    dsimp [a]
    positivity
  have ha_norm : ‖(a n : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha_pos]
    have hone : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by norm_num)
    calc
      a n ≤ latticeStrongCouplingRadius d Φ.bound / 2 := by
        dsimp [a]
        simpa using mul_le_mul_of_nonneg_left hone
          (div_nonneg hR.le (by norm_num))
      _ < latticeStrongCouplingRadius d Φ.bound := by linarith
  constructor
  · change analyticInfiniteVolumeLocalExpectation F η Φ (a n : ℂ) =
      analyticInfiniteVolumeLocalExpectation F η' Φ (a n : ℂ)
    rw [analyticInfiniteVolumeLocalExpectation_ofReal F η Φ (a n) ha_norm,
      analyticInfiniteVolumeLocalExpectation_ofReal F η' Φ (a n) ha_norm,
      centeredInfiniteVolumeMeasure_boundary_independent η η' Φ (a n) ha_norm]
  · simpa using ha_pos.ne'

end

end YangMills.StrongCoupling
