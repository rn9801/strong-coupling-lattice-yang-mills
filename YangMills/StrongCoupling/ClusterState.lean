/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.MarkedExpansion
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Local thermodynamic limits from cluster tails

This file fixes the proof architecture for Milestone 11.  Its only convergence
input is a uniform tail estimate for the marked linked-cluster expansion.  In
particular, this module does not import the Douglas compatibility layer or any
Dobrushin comparison theorem.

`ClusterLimitCertificate.compare` is the finite-volume conclusion supplied by
one-root cluster cancellation: after cluster radius `N`, two finite-volume
expectations differ by at most `tail F N`, uniformly in both volumes and their
boundary conditions.  The tail tends to zero.  The resulting local state is
therefore the ordinary Cauchy limit of finite-volume expectations.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- A finite-volume Gibbs probability, before it is embedded in the full
configuration space. -/
def dynamicGibbsProbability (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℝ) :
    ProbabilityMeasure (DynamicConfiguration Λ) :=
  ⟨gibbsMeasure Λ Φ β,
    Gauge.FiniteVolume.instIsProbabilityMeasureGibbsMeasure Λ Φ β⟩

/-- Push a finite-volume Gibbs law to the full configuration space by gluing
its frozen exterior configuration. -/
def fullGibbsProbability (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℝ) :
    ProbabilityMeasure (Configuration d G) :=
  (dynamicGibbsProbability Λ Φ β).map
    Λ.continuous_evaluate.measurable.aemeasurable

/-- Expectation of a local observable under a full-space probability law. -/
def localExpectation (μ : ProbabilityMeasure (Configuration d G))
    (F : LocalObservable d G) : ℂ :=
  ∫ A, F A ∂(μ : Measure (Configuration d G))

theorem integrable_localObservable
    (μ : ProbabilityMeasure (Configuration d G))
    (F : LocalObservable d G) :
    Integrable F (μ : Measure (Configuration d G)) := by
  apply Integrable.of_bound F.toContinuousMap.continuous.measurable.aestronglyMeasurable
    ‖F.toBoundedContinuousMap‖
  exact ae_of_all _ F.norm_apply_le

/-- Finite-volume expectations are norm-one functionals. -/
theorem norm_localExpectation_le
    (μ : ProbabilityMeasure (Configuration d G))
    (F : LocalObservable d G) :
    ‖localExpectation μ F‖ ≤ ‖F.toBoundedContinuousMap‖ := by
  rw [localExpectation]
  simpa using norm_integral_le_of_norm_le_const
    (μ := (μ : Measure (Configuration d G)))
    (ae_of_all _ F.norm_apply_le)

/-- The pushed-forward law reproduces the previously defined finite-volume
complex Gibbs expectation at real coupling. -/
theorem localExpectation_fullGibbsProbability
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℝ) :
    localExpectation (fullGibbsProbability Λ Φ β) F =
      complexGibbsExpectation F Λ Φ (β : ℂ) := by
  rw [complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  unfold localExpectation fullGibbsProbability dynamicGibbsProbability
  rw [ProbabilityMeasure.toMeasure_map]
  exact MeasureTheory.integral_map
    Λ.continuous_evaluate.measurable.aemeasurable
    F.toContinuousMap.continuous.measurable.aestronglyMeasurable

/-- A uniform one-root linked-cluster tail certificate.

The sequence `measure n` may use different volumes and different frozen
exterior configurations.  The estimate is deliberately stated with a common
cluster radius `N`; this is the form produced after cancellation of all
clusters not joining the marked support to the changed far-away region. -/
structure ClusterLimitCertificate
    (measure : ℕ → ProbabilityMeasure (Configuration d G)) where
  tail : LocalObservable d G → ℕ → ℝ
  tail_nonneg : ∀ F N, 0 ≤ tail F N
  tail_tendsto_zero : ∀ F, Tendsto (tail F) atTop (nhds 0)
  compare : ∀ F N m n, N ≤ m → N ≤ n →
    ‖localExpectation (measure m) F - localExpectation (measure n) F‖ ≤
      tail F N

namespace ClusterLimitCertificate

variable {measure : ℕ → ProbabilityMeasure (Configuration d G)}

/-- The cluster tail makes every local expectation sequence Cauchy. -/
theorem cauchySeq_localExpectation
    (C : ClusterLimitCertificate measure) (F : LocalObservable d G) :
    CauchySeq (fun n => localExpectation (measure n) F) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hevent : ∀ᶠ N in atTop, C.tail F N < ε :=
    C.tail_tendsto_zero F (gt_mem_nhds hε)
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  exact (C.compare F N m n hm hn).trans_lt (hN N le_rfl)

/-- The boundary-independent infinite-volume local expectation. -/
def localState (C : ClusterLimitCertificate measure)
    (F : LocalObservable d G) : ℂ :=
  limUnder atTop (fun n => localExpectation (measure n) F)

/-- Finite-volume local expectations converge to the cluster state. -/
theorem tendsto_localState (C : ClusterLimitCertificate measure)
    (F : LocalObservable d G) :
    Tendsto (fun n => localExpectation (measure n) F) atTop
      (nhds (C.localState F)) :=
  (C.cauchySeq_localExpectation F).tendsto_limUnder

/-- The cluster state is additive. -/
theorem localState_add (C : ClusterLimitCertificate measure)
    (F H : LocalObservable d G) :
    C.localState (F.add H) = C.localState F + C.localState H := by
  apply tendsto_nhds_unique (C.tendsto_localState (F.add H))
  convert (C.tendsto_localState F).add (C.tendsto_localState H) using 1
  funext n
  unfold localExpectation
  change (∫ A, F A + H A ∂(measure n : Measure (Configuration d G))) = _
  rw [integral_add (integrable_localObservable (measure n) F)
    (integrable_localObservable (measure n) H)]

/-- The cluster state is complex homogeneous. -/
theorem localState_smul (C : ClusterLimitCertificate measure)
    (z : ℂ) (F : LocalObservable d G) :
    C.localState (LocalObservable.smul z F) = z * C.localState F := by
  apply tendsto_nhds_unique
    (C.tendsto_localState (LocalObservable.smul z F))
  convert (C.tendsto_localState F).const_mul z using 1
  funext n
  simp only [localExpectation, LocalObservable.smul_apply, integral_const_mul]

/-- The cluster state is normalized. -/
theorem localState_one (C : ClusterLimitCertificate measure) :
    C.localState (LocalObservable.const (d := d) (G := G) 1) = 1 := by
  apply tendsto_nhds_unique
    (C.tendsto_localState (LocalObservable.const (d := d) (G := G) 1))
  simpa [localExpectation, LocalObservable.const] using
    (tendsto_const_nhds : Tendsto (fun _n : ℕ => (1 : ℂ)) atTop (nhds 1))

/-- The infinite-volume state retains the finite-volume sup-norm bound. -/
theorem norm_localState_le (C : ClusterLimitCertificate measure)
    (F : LocalObservable d G) :
    ‖C.localState F‖ ≤ ‖F.toBoundedContinuousMap‖ := by
  apply le_of_tendsto (C.tendsto_localState F).norm
  exact Eventually.of_forall fun n => norm_localExpectation_le (measure n) F

/-- Any other proposed local limit agreeing with the finite-volume sequence
is equal to the cluster state.  This is the basic sequence- and
boundary-independence principle used by later concrete exhaustions. -/
theorem eq_localState_of_tendsto (C : ClusterLimitCertificate measure)
    (F : LocalObservable d G) (z : ℂ)
    (hz : Tendsto (fun n => localExpectation (measure n) F) atTop (nhds z)) :
    z = C.localState F :=
  tendsto_nhds_unique hz (C.tendsto_localState F)

/-- Asymptotic finite-volume equality implies equality in the cluster state.
This is the reusable route to translation, gauge, and reflection invariance:
the concrete cluster expansion proves that the displayed difference tends to
zero after the transformed boundary recedes. -/
theorem localState_eq_of_tendsto_sub_zero
    (C : ClusterLimitCertificate measure) (F H : LocalObservable d G)
    (h : Tendsto (fun n =>
      localExpectation (measure n) F - localExpectation (measure n) H)
      atTop (nhds 0)) :
    C.localState F = C.localState H := by
  have hlim := (C.tendsto_localState F).sub (C.tendsto_localState H)
  have hz : C.localState F - C.localState H = 0 :=
    tendsto_nhds_unique hlim h
  exact sub_eq_zero.mp hz

end ClusterLimitCertificate

/-! ## Independence of exhaustion and boundary sequence -/

/-- A cross-sequence one-root linked-cluster comparison.  Unlike the Cauchy
certificate for one fixed sequence, this compares two independently chosen
finite-volume exhaustions (and hence two independently chosen boundary
conditions).  Concrete cluster cancellation supplies it with the same rooted
tail: only clusters reaching the complement of both finite volumes survive. -/
structure ClusterComparisonCertificate
    (measure₁ measure₂ : ℕ → ProbabilityMeasure (Configuration d G)) where
  tail : LocalObservable d G → ℕ → ℝ
  tail_nonneg : ∀ F N, 0 ≤ tail F N
  tail_tendsto_zero : ∀ F, Tendsto (tail F) atTop (nhds 0)
  compare : ∀ F N m n, N ≤ m → N ≤ n →
    ‖localExpectation (measure₁ m) F - localExpectation (measure₂ n) F‖ ≤
      tail F N

namespace ClusterComparisonCertificate

variable {measure₁ measure₂ : ℕ → ProbabilityMeasure (Configuration d G)}

/-- Two thermodynamic-limit states linked by a vanishing rooted-cluster tail
agree on every local continuous observable. -/
theorem localState_eq
    (C₁ : ClusterLimitCertificate measure₁)
    (C₂ : ClusterLimitCertificate measure₂)
    (X : ClusterComparisonCertificate measure₁ measure₂)
    (F : LocalObservable d G) :
    C₁.localState F = C₂.localState F := by
  have hdiff : Tendsto (fun n =>
      localExpectation (measure₁ n) F - localExpectation (measure₂ n) F)
      atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hevent : ∀ᶠ N in atTop, X.tail F N < ε :=
      X.tail_tendsto_zero F (gt_mem_nhds hε)
    rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_zero_right]
    exact (X.compare F N n n hn hn).trans_lt (hN N le_rfl)
  have hstates := (C₁.tendsto_localState F).sub (C₂.tendsto_localState F)
  exact sub_eq_zero.mp (tendsto_nhds_unique hstates hdiff)

end ClusterComparisonCertificate

/-! ## Symmetries after the boundary recedes -/

/-- A one-root cluster certificate together with the two asymptotic symmetry
comparisons required by the Milestone 11 exit criterion.  In the concrete
box construction these estimates come from translating or gauge-transforming
the marked expansion and observing that only clusters reaching the receding
boundary can differ. -/
structure InvariantClusterLimitCertificate
    (measure : ℕ → ProbabilityMeasure (Configuration d G))
    extends ClusterLimitCertificate measure where
  translation_difference : ∀ (v : Site d) (F : LocalObservable d G),
    Tendsto (fun n =>
      localExpectation (measure n) (F.translatePullback v) -
        localExpectation (measure n) F) atTop (nhds 0)
  gauge_difference : ∀ (g : GaugeTransformation d G)
      (F : LocalObservable d G),
    Tendsto (fun n =>
      localExpectation (measure n) (F.gaugePullback g) -
        localExpectation (measure n) F) atTop (nhds 0)

namespace InvariantClusterLimitCertificate

variable {measure : ℕ → ProbabilityMeasure (Configuration d G)}

/-- Translation invariance of the boundary-independent cluster state. -/
theorem localState_translate
    (C : InvariantClusterLimitCertificate measure)
    (v : Site d) (F : LocalObservable d G) :
    C.toClusterLimitCertificate.localState (F.translatePullback v) =
      C.toClusterLimitCertificate.localState F :=
  C.toClusterLimitCertificate.localState_eq_of_tendsto_sub_zero
    (F.translatePullback v) F (C.translation_difference v F)

/-- Gauge invariance of the boundary-independent cluster state. -/
theorem localState_gauge
    (C : InvariantClusterLimitCertificate measure)
    (g : GaugeTransformation d G) (F : LocalObservable d G) :
    C.toClusterLimitCertificate.localState (F.gaugePullback g) =
      C.toClusterLimitCertificate.localState F :=
  C.toClusterLimitCertificate.localState_eq_of_tendsto_sub_zero
    (F.gaugePullback g) F (C.gauge_difference g F)

end InvariantClusterLimitCertificate

end

end YangMills.StrongCoupling
