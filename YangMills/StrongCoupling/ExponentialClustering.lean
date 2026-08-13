/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.InfiniteVolumeMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential clustering from the two-root cluster expansion

The finite-volume input in this file is precisely the linked two-root cluster
bound: vacuum clusters and clusters meeting only one insertion have cancelled,
so every surviving cluster joins the two recorded supports.  The bound is
uniform in volume and boundary condition.  Passing to the one-root cluster
limit proves infinite-volume exponential clustering.

The result is a direct consequence of the convergent two-root cluster
expansion and its uniform spatially weighted bound.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Finite-volume truncated correlation. -/
def truncatedCorrelation
    (μ : ProbabilityMeasure (Configuration d G))
    (F H : LocalObservable d G) : ℂ :=
  localExpectation μ (F.mul H) - localExpectation μ F * localExpectation μ H

/-- Infinite-volume truncated correlation of the local cluster state. -/
def ClusterLimitCertificate.stateTruncatedCorrelation
    {measure : ℕ → ProbabilityMeasure (Configuration d G)}
    (C : ClusterLimitCertificate measure)
    (F H : LocalObservable d G) : ℂ :=
  C.localState (F.mul H) - C.localState F * C.localState H

/-- A uniform two-root linked-cluster certificate.

`supportDistance` may initially be the plaquette-incidence distance; a later
geometry lemma can replace it by lattice `ℓ¹` distance.  `rate < 1` is the
explicit positive-decay condition obtained from the weighted KP bound. -/
structure TwoRootClusterCertificate
    (measure : ℕ → ProbabilityMeasure (Configuration d G))
    extends ClusterLimitCertificate measure where
  supportDistance : Finset (PositiveEdge d) → Finset (PositiveEdge d) → ℕ
  prefactor : ℝ
  prefactor_nonneg : 0 ≤ prefactor
  rate : ℝ
  rate_pos : 0 < rate
  rate_lt_one : rate < 1
  finite_truncatedCorrelation_bound : ∀ n F H,
    ‖truncatedCorrelation (measure n) F H‖ ≤
      prefactor * ‖F.toBoundedContinuousMap‖ *
        ‖H.toBoundedContinuousMap‖ *
        (F.support.card : ℝ) * (H.support.card : ℝ) *
        rate ^ supportDistance F.support H.support

namespace TwoRootClusterCertificate

variable {measure : ℕ → ProbabilityMeasure (Configuration d G)}

/-- Finite-volume truncated correlations converge to the truncated
correlation of the local cluster state. -/
theorem tendsto_truncatedCorrelation
    (C : TwoRootClusterCertificate measure)
    (F H : LocalObservable d G) :
    Tendsto (fun n => truncatedCorrelation (measure n) F H) atTop
      (nhds (C.toClusterLimitCertificate.stateTruncatedCorrelation F H)) := by
  exact (C.toClusterLimitCertificate.tendsto_localState (F.mul H)).sub
    ((C.toClusterLimitCertificate.tendsto_localState F).mul
      (C.toClusterLimitCertificate.tendsto_localState H))

/-- **Infinite-volume exponential clustering.**

The geometric factor has an explicit rate strictly between zero and one.  It
is the direct infinite-volume limit of the uniform two-root linked-cluster
bound. -/
theorem exponential_clustering
    (C : TwoRootClusterCertificate measure)
    (F H : LocalObservable d G) :
    ‖C.toClusterLimitCertificate.stateTruncatedCorrelation F H‖ ≤
      C.prefactor * ‖F.toBoundedContinuousMap‖ *
        ‖H.toBoundedContinuousMap‖ *
        (F.support.card : ℝ) * (H.support.card : ℝ) *
        C.rate ^ C.supportDistance F.support H.support := by
  apply le_of_tendsto (C.tendsto_truncatedCorrelation F H).norm
  exact Eventually.of_forall fun n =>
    C.finite_truncatedCorrelation_bound n F H

/-- The positive mass associated with the geometric cluster rate. -/
def clusteringMass (C : TwoRootClusterCertificate measure) : ℝ :=
  -Real.log C.rate

theorem clusteringMass_pos (C : TwoRootClusterCertificate measure) :
    0 < C.clusteringMass := by
  exact neg_pos.mpr (Real.log_neg C.rate_pos C.rate_lt_one)

/-- The geometric decay factor is literally an exponential with the positive
mass `clusteringMass`. -/
theorem rate_pow_eq_exp_neg_mass
    (C : TwoRootClusterCertificate measure) (n : ℕ) :
    C.rate ^ n = Real.exp (-C.clusteringMass * (n : ℝ)) := by
  calc
    C.rate ^ n = (Real.exp (Real.log C.rate)) ^ n := by
      rw [Real.exp_log C.rate_pos]
    _ = Real.exp ((n : ℝ) * Real.log C.rate) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp (-C.clusteringMass * (n : ℝ)) := by
      congr 1
      simp only [clusteringMass]
      ring

/-- Exponential form of `exponential_clustering`, with an explicit positive
decay mass. -/
theorem exponential_clustering_exp
    (C : TwoRootClusterCertificate measure)
    (F H : LocalObservable d G) :
    ‖C.toClusterLimitCertificate.stateTruncatedCorrelation F H‖ ≤
      C.prefactor * ‖F.toBoundedContinuousMap‖ *
        ‖H.toBoundedContinuousMap‖ *
        (F.support.card : ℝ) * (H.support.card : ℝ) *
        Real.exp (-C.clusteringMass *
          (C.supportDistance F.support H.support : ℝ)) := by
  rw [← C.rate_pow_eq_exp_neg_mass]
  exact C.exponential_clustering F H

end TwoRootClusterCertificate

/-! ## Exponential clustering with an explicit observable amplitude -/

/-- A two-root cluster certificate in which the distance-independent
amplitude is allowed to depend explicitly on the two finite observables.
This is the natural interface for complete marked-root decorations: the
amplitude may grow with support size, while the decay rate remains uniform in
the observables, volume, and boundary condition. -/
structure ObservableAmplitudeClusterCertificate
    (measure : ℕ → ProbabilityMeasure (Configuration d G))
    extends ClusterLimitCertificate measure where
  supportDistance : Finset (PositiveEdge d) → Finset (PositiveEdge d) → ℕ
  amplitude : LocalObservable d G → LocalObservable d G → ℝ
  amplitude_nonneg : ∀ F H, 0 ≤ amplitude F H
  rate : ℝ
  rate_pos : 0 < rate
  rate_lt_one : rate < 1
  eventual_truncatedCorrelation_bound : ∀ F H, ∃ N, ∀ n, N ≤ n →
    ‖truncatedCorrelation (measure n) F H‖ ≤
      amplitude F H * rate ^ supportDistance F.support H.support

namespace ObservableAmplitudeClusterCertificate

variable {measure : ℕ → ProbabilityMeasure (Configuration d G)}

theorem tendsto_truncatedCorrelation
    (C : ObservableAmplitudeClusterCertificate measure)
    (F H : LocalObservable d G) :
    Tendsto (fun n => truncatedCorrelation (measure n) F H) atTop
      (nhds (C.toClusterLimitCertificate.stateTruncatedCorrelation F H)) := by
  exact (C.toClusterLimitCertificate.tendsto_localState (F.mul H)).sub
    ((C.toClusterLimitCertificate.tendsto_localState F).mul
      (C.toClusterLimitCertificate.tendsto_localState H))

/-- Infinite-volume exponential clustering with an explicit finite-support
amplitude. -/
theorem exponential_clustering
    (C : ObservableAmplitudeClusterCertificate measure)
    (F H : LocalObservable d G) :
    ‖C.toClusterLimitCertificate.stateTruncatedCorrelation F H‖ ≤
      C.amplitude F H *
        C.rate ^ C.supportDistance F.support H.support := by
  apply le_of_tendsto (C.tendsto_truncatedCorrelation F H).norm
  obtain ⟨N, hN⟩ := C.eventual_truncatedCorrelation_bound F H
  exact eventually_atTop.2 ⟨N, fun n hn => hN n hn⟩

/-- Positive mass associated with the uniform geometric decay rate. -/
def clusteringMass (C : ObservableAmplitudeClusterCertificate measure) : ℝ :=
  -Real.log C.rate

theorem clusteringMass_pos
    (C : ObservableAmplitudeClusterCertificate measure) :
    0 < C.clusteringMass := by
  exact neg_pos.mpr (Real.log_neg C.rate_pos C.rate_lt_one)

theorem rate_pow_eq_exp_neg_mass
    (C : ObservableAmplitudeClusterCertificate measure) (n : ℕ) :
    C.rate ^ n = Real.exp (-C.clusteringMass * (n : ℝ)) := by
  calc
    C.rate ^ n = (Real.exp (Real.log C.rate)) ^ n := by
      rw [Real.exp_log C.rate_pos]
    _ = Real.exp ((n : ℝ) * Real.log C.rate) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp (-C.clusteringMass * (n : ℝ)) := by
      congr 1
      simp only [clusteringMass]
      ring

theorem exponential_clustering_exp
    (C : ObservableAmplitudeClusterCertificate measure)
    (F H : LocalObservable d G) :
    ‖C.toClusterLimitCertificate.stateTruncatedCorrelation F H‖ ≤
      C.amplitude F H *
        Real.exp (-C.clusteringMass *
          (C.supportDistance F.support H.support : ℝ)) := by
  rw [← C.rate_pow_eq_exp_neg_mass]
  exact C.exponential_clustering F H

end ObservableAmplitudeClusterCertificate

end

end YangMills.StrongCoupling
