/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.CenteredGibbsTower
import YangMills.StrongCoupling.CenteredTranslation
import YangMills.StrongCoupling.CenteredClusterGeometry

/-!
# The centered strong-coupling infinite-volume Yang--Mills measure

The one-root KP cluster boundary estimate and the finite-product Gibbs tower
give a Cauchy limit for every local observable, uniformly over arbitrary
exterior data. Compactness represents that local state by a unique Borel
probability measure. The augmented two-root expansion then gives exponential
clustering with the explicit positive KP mass.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- The concrete one-root thermodynamic-limit certificate supplied entirely
by the cluster expansion and the centered Gibbs tower. -/
def centeredClusterLimitCertificate
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound) :
    ClusterLimitCertificate (centeredGibbsSequence η Φ β) :=
  clusterLimitCertificateOfCauchy (centeredGibbsSequence η Φ β)
    (fun F => cauchySeq_centered_localExpectation η Φ β hβ F)

/-- The strong-coupling infinite-volume Yang--Mills probability obtained as
the unique representing measure of the centered cluster state. -/
def centeredInfiniteVolumeProbability
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound) :
    ProbabilityMeasure (Configuration d G) :=
  (centeredClusterLimitCertificate η Φ β hβ).infiniteVolumeProbability

/-- The corresponding Borel probability measure. -/
def centeredInfiniteVolumeMeasure
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound) :
    Measure (Configuration d G) :=
  centeredInfiniteVolumeProbability η Φ β hβ

instance centeredInfiniteVolumeMeasure_isProbability
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound) :
    IsProbabilityMeasure (centeredInfiniteVolumeMeasure η Φ β hβ) :=
  (centeredInfiniteVolumeProbability η Φ β hβ).property

/-- The representing Borel probability is regular. -/
instance centeredInfiniteVolumeMeasure_regular
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound) :
    (centeredInfiniteVolumeMeasure η Φ β hβ).Regular :=
  inferInstance

/-- Every local expectation converges along arbitrary centered exterior data
to its expectation under the concrete infinite-volume probability. -/
theorem tendsto_centered_localExpectation_infiniteVolume
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (F : LocalObservable d G) :
    Tendsto (fun n => localExpectation (centeredGibbsSequence η Φ β n) F)
      atTop (nhds (∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ)) := by
  let C := centeredClusterLimitCertificate η Φ β hβ
  have hrepr : ∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ =
      C.localState F := by
    exact C.integral_infiniteVolumeMeasure F
  rw [hrepr]
  exact C.tendsto_localState F

/-- Every cofinal subsequence of centered boxes has the same local-observable
limit.  Together with boundary independence, this is the concrete exhaustion-
sequence independence statement for the centered cofinal class. -/
theorem tendsto_centered_localExpectation_infiniteVolume_along
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (u : ℕ → ℕ) (hu : Tendsto u atTop atTop)
    (F : LocalObservable d G) :
    Tendsto (fun n => localExpectation (centeredGibbsSequence η Φ β (u n)) F)
      atTop (nhds (∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ)) :=
  (tendsto_centered_localExpectation_infiniteVolume η Φ β hβ F).comp hu

/-- Boundary independence: all centered exterior sequences produce the same
infinite-volume Borel probability. -/
theorem centeredInfiniteVolumeMeasure_boundary_independent
    (η η' : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound) :
    centeredInfiniteVolumeMeasure η Φ β hβ =
      centeredInfiniteVolumeMeasure η' Φ β hβ := by
  apply measure_eq_of_integral_localObservable_eq
  intro F
  have hη := tendsto_centered_localExpectation_infiniteVolume η Φ β hβ F
  have hη' := tendsto_centered_localExpectation_infiniteVolume η' Φ β hβ F
  have hdiff := tendsto_centered_complexGibbsExpectation_boundary_sub_zero
    F Φ hβ η η'
  have hlim := hη.sub hη'
  have hzero :
      (∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ) -
        (∫ A, F A ∂centeredInfiniteVolumeMeasure η' Φ β hβ) = 0 := by
    apply tendsto_nhds_unique hlim
    simpa only [centeredGibbsSequence,
      localExpectation_fullGibbsProbability] using hdiff
  exact sub_eq_zero.mp hzero

/-- The centered infinite-volume measure is the unique probability
representing the local cluster state. -/
theorem centeredInfiniteVolumeMeasure_unique
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (μ : Measure (Configuration d G)) [IsProbabilityMeasure μ]
    (hμ : ∀ F : LocalObservable d G,
      ∫ A, F A ∂μ =
        (centeredClusterLimitCertificate η Φ β hβ).localState F) :
    μ = centeredInfiniteVolumeMeasure η Φ β hβ := by
  exact (centeredClusterLimitCertificate η Φ β hβ).infiniteVolumeMeasure_unique μ hμ

/-- A finite centered expectation of a gauge-pulled observable is the
expectation of the original observable with gauge-transformed exterior data. -/
theorem complexGibbsExpectation_gaugePullback_eq_transformedExterior
    (n : ℕ) (η : Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (g : GaugeTransformation d G) (F : LocalObservable d G) :
    complexGibbsExpectation (F.gaugePullback g)
        (centeredSpecification n η) Φ (β : ℂ) =
      complexGibbsExpectation F
        (centeredSpecification n (gaugeTransform g η)) Φ (β : ℂ) := by
  rw [complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  change (∫ U, F (gaugeTransform g
      ((centeredSpecification n η).evaluate U))
      ∂Gauge.FiniteVolume.gibbsMeasure (centeredSpecification n η) Φ β) = _
  symm
  simpa only [centeredSpecification_gaugeTransformExterior] using
    Gauge.FiniteVolume.integral_gibbsMeasure_gaugeTransformExterior_complex
      (centeredSpecification n η) Φ β g F
      F.toContinuousMap.continuous.measurable

/-- Full gauge invariance of the infinite-volume local state.  Finite volume
is gauge covariant after transforming the exterior field, and the one-root
cluster boundary theorem removes that transformed exterior in the limit. -/
theorem centeredInfiniteVolume_integral_gaugePullback
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (g : GaugeTransformation d G) (F : LocalObservable d G) :
    ∫ A, F (gaugeTransform g A)
        ∂centeredInfiniteVolumeMeasure η Φ β hβ =
      ∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ := by
  let ηg : ℕ → Configuration d G := fun n => gaugeTransform g (η n)
  have hleft := tendsto_centered_localExpectation_infiniteVolume
    η Φ β hβ (F.gaugePullback g)
  have hright := tendsto_centered_localExpectation_infiniteVolume
    ηg Φ β hβ F
  have heq : (fun n => localExpectation (centeredGibbsSequence η Φ β n)
      (F.gaugePullback g)) =
      fun n => localExpectation (centeredGibbsSequence ηg Φ β n) F := by
    funext n
    simp only [centeredGibbsSequence, localExpectation_fullGibbsProbability,
      ηg]
    exact complexGibbsExpectation_gaugePullback_eq_transformedExterior
      n (η n) Φ β g F
  rw [heq] at hleft
  have hlimits := tendsto_nhds_unique hleft hright
  have hboundary := centeredInfiniteVolumeMeasure_boundary_independent
    ηg η Φ β hβ
  change (∫ A, (F.gaugePullback g) A
      ∂centeredInfiniteVolumeMeasure η Φ β hβ) = _
  calc
    ∫ A, (F.gaugePullback g) A
        ∂centeredInfiniteVolumeMeasure η Φ β hβ =
        ∫ A, F A ∂centeredInfiniteVolumeMeasure ηg Φ β hβ := hlimits
    _ = ∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ := by
      rw [hboundary]

/-- The infinite-volume Yang--Mills probability is literally invariant under
every sitewise gauge transformation.  This is the pushforward-measure form of
`centeredInfiniteVolume_integral_gaugePullback`; local continuous observables
determine Borel probability measures on the compact configuration space. -/
theorem centeredInfiniteVolumeMeasure_map_gaugeTransform
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (g : GaugeTransformation d G) :
    Measure.map (gaugeTransform g)
        (centeredInfiniteVolumeMeasure η Φ β hβ) =
      centeredInfiniteVolumeMeasure η Φ β hβ := by
  have hg : Measurable (gaugeTransform g) :=
    (LocalObservable.gaugeTransformContinuous g).continuous.measurable
  letI : IsProbabilityMeasure
      (Measure.map (gaugeTransform g)
        (centeredInfiniteVolumeMeasure η Φ β hβ)) :=
    Measure.isProbabilityMeasure_map hg.aemeasurable
  apply measure_eq_of_integral_localObservable_eq
  intro F
  rw [MeasureTheory.integral_map hg.aemeasurable
    F.toContinuousMap.continuous.aestronglyMeasurable]
  exact centeredInfiniteVolume_integral_gaugePullback η Φ β hβ g F

/-- A fixed sitewise gauge transformation preserves the strong-coupling
infinite-volume Yang--Mills probability. -/
theorem centeredInfiniteVolumeMeasure_measurePreserving_gaugeTransform
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (g : GaugeTransformation d G) :
    MeasurePreserving (gaugeTransform g)
      (centeredInfiniteVolumeMeasure η Φ β hβ)
      (centeredInfiniteVolumeMeasure η Φ β hβ) := by
  refine ⟨(LocalObservable.gaugeTransformContinuous g).continuous.measurable, ?_⟩
  exact centeredInfiniteVolumeMeasure_map_gaugeTransform η Φ β hβ g

/-- Translation invariance of the infinite-volume local state.  This follows
from the translated-box finite Gibbs tower and the one-root KP boundary tail;
no periodic-lattice or Douglas-limit argument is used. -/
theorem centeredInfiniteVolume_integral_translatePullback
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (v : Site d) (F : LocalObservable d G) :
    ∫ A, F (LocalObservable.translateConfiguration v A)
        ∂centeredInfiniteVolumeMeasure η Φ β hβ =
      ∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ := by
  let k := siteTranslationRadius (-v)
  let ηlarge : ℕ → Configuration d G := fun m => η (m + k)
  have htranslated := tendsto_centered_localExpectation_infiniteVolume
    η Φ β hβ (F.translatePullback v)
  have hcentered := tendsto_centered_localExpectation_infiniteVolume
    η Φ β hβ F
  have hshifted : Tendsto (fun m =>
      localExpectation (centeredGibbsSequence η Φ β (m + k)) F)
      atTop (nhds (∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ)) := by
    exact (Filter.tendsto_add_atTop_iff_nat k).2 hcentered
  have hdiff := tendsto_centered_translationPullback_difference_zero
    F Φ β hβ v η ηlarge
  have hlimits := hshifted.sub htranslated
  have hzero :
      (∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ) -
        (∫ A, (F.translatePullback v) A
          ∂centeredInfiniteVolumeMeasure η Φ β hβ) = 0 := by
    apply tendsto_nhds_unique hlimits
    simpa only [centeredGibbsSequence,
      localExpectation_fullGibbsProbability, k, ηlarge] using hdiff
  change (∫ A, (F.translatePullback v) A
      ∂centeredInfiniteVolumeMeasure η Φ β hβ) = _
  exact (sub_eq_zero.mp hzero).symm

/-- Infinite-volume exponential clustering with the explicit augmented-root
amplitude and the positive mass coming from the strict KP tilt. -/
theorem centeredInfiniteVolume_exponential_clustering
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (F H : LocalObservable d G) :
    ‖(∫ A, (F.mul H) A ∂centeredInfiniteVolumeMeasure η Φ β hβ) -
        (∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ) *
          (∫ A, H A ∂centeredInfiniteVolumeMeasure η Φ β hβ)‖ ≤
      centeredClusterObservableAmplitude F H Φ (β : ℂ) *
        Real.exp (-centeredClusterMass (d := d) Φ (β : ℂ) *
          (centeredClusterSupportDistance F.support H.support : ℝ)) := by
  let C := centeredClusterLimitCertificate η Φ β hβ
  have hcluster := centeredClusterLimit_exponential_clustering_exp
    η Φ β hβ C F H
  have hF : (∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ) =
      C.localState F := C.integral_infiniteVolumeMeasure F
  have hH : (∫ A, H A ∂centeredInfiniteVolumeMeasure η Φ β hβ) =
      C.localState H := C.integral_infiniteVolumeMeasure H
  have hFH : (∫ A, (F.mul H) A
      ∂centeredInfiniteVolumeMeasure η Φ β hβ) =
      C.localState (F.mul H) := C.integral_infiniteVolumeMeasure (F.mul H)
  rw [hF, hH, hFH]
  exact hcluster

/-- The clustering mass in the preceding theorem is strictly positive. -/
theorem centeredInfiniteVolume_clusteringMass_pos
    (Φ : RealPlaquettePotential G) {β : ℝ}
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound) :
    0 < centeredClusterMass (d := d) Φ (β : ℂ) :=
  centeredClusterMass_pos Φ hβ

end

end YangMills.StrongCoupling
