/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills

/-!
# Critical-review smoke tests

These tests use the public API to derive small, familiar consequences of the
headline theorems.  They are intentionally downstream of the implementation:
their purpose is to catch vacuous strong-coupling domains, lost probability
normalizations, incompatible Wilson-loop conventions, or incorrectly scaled
reflection pairings.

The examples cover an explicitly empty finite specification, constant Gibbs
observables, empty and constant Wilson loops, the zero-coupling KP/Mayer
certificate, infinite-volume boundary and gauge invariance, a zero-action
reflection model, and the zero-area specialization of the rectangle area law.
-/

namespace YangMills.Tests.ReviewerSmoke

open MeasureTheory
open Gauge Gauge.FiniteVolume Gauge.SiteReflection
open Lattice.Cubic Polymer StrongCoupling Wilson

noncomputable section

/-! ## Finite-volume normalization -/

/-- A genuine finite specification with no integrated edges and no active
plaquettes.  The exterior field is the identity configuration. -/
def emptySpecification (d : ℕ) (G : Type*) [One G] :
    FiniteSpecification d G where
  dynamicEdges := ∅
  activePlaquettes := ∅
  exterior := fun _ => 1

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [CompactSpace G] [T2Space G]
  [GaugeHaarProbability G]

@[simp]
theorem emptySpecification_action (Phi : RealPlaquettePotential G)
    (U : DynamicConfiguration (emptySpecification d G)) :
    action (emptySpecification d G) Phi U = 0 := by
  simp [action, emptySpecification]

/-- With no active plaquettes, the real partition function is one at every
coupling, not merely at zero coupling. -/
@[simp]
theorem emptySpecification_partitionFunction
    (Phi : RealPlaquettePotential G) (beta : ℝ) :
    partitionFunction (emptySpecification d G) Phi beta = 1 := by
  simp [partitionFunction, boltzmannWeight]

/-- The same empty-volume normalization holds for complex coupling. -/
@[simp]
theorem emptySpecification_complexPartitionFunction
    (Phi : RealPlaquettePotential G) (beta : ℂ) :
    complexPartitionFunction (emptySpecification d G) Phi beta = 1 := by
  simp [complexPartitionFunction, complexBoltzmannWeight]

/-- Normalization of the Gibbs probability fixes every real constant. -/
@[simp]
theorem gibbsExpectation_const (Lambda : FiniteSpecification d G)
    (Phi : RealPlaquettePotential G) (beta c : ℝ) :
    gibbsExpectation Lambda Phi beta (fun _ => c) = c := by
  rw [gibbsExpectation_eq_integral_gibbsMeasure]
  simp

/-! ## Wilson-loop conventions -/

variable {rho : ContinuousUnitaryRepData G n}

/-- The normalized Wilson observable of the empty based loop is exactly one. -/
@[simp]
theorem wilsonLoop_nil (rho : ContinuousUnitaryRepData G n) (x : Site d)
    (A : Configuration d G) :
    rho.wilsonLoop (.nil : Lattice.Cubic.Path x x) A = 1 := by
  simp

/-- The empty loop also records the expected empty support. -/
@[simp]
theorem wilsonLoop_nil_support (rho : ContinuousUnitaryRepData G n)
    (x : Site d) :
    (rho.wilsonLoop (.nil : Lattice.Cubic.Path x x)).support = ∅ := by
  simp

/-- A fully explicit constant-one class function gives a gauge-invariant
Wilson observable with value one on every loop. -/
theorem constantOneWilsonLoop_isGaugeInvariant {x : Site d}
    (C : Lattice.Cubic.Path x x) :
    IsGaugeInvariant
      (LocalObservable.wilsonLoop
        (ContinuousClassFunction.const (G := G) 1) C) :=
  LocalObservable.wilsonLoop_gaugeInvariant
    (ContinuousClassFunction.const (G := G) 1) C

@[simp]
theorem constantOneWilsonLoop_apply {x : Site d}
    (C : Lattice.Cubic.Path x x)
    (A : Configuration d G) :
    LocalObservable.wilsonLoop
        (ContinuousClassFunction.const (G := G) 1) C A = 1 := by
  simp [LocalObservable.wilsonLoop, ContinuousClassFunction.const]

/-! ## Non-vacuity and normalization of the cluster expansion -/

/-- Positivity of the explicit radius makes zero coupling an actual point of
the strong-coupling domain. -/
theorem zeroCoupling_mem_latticeStrongCouplingDisk
    (Phi : RealPlaquettePotential G) :
    ‖(0 : ℂ)‖ < latticeStrongCouplingRadius d Phi.bound := by
  simpa using latticeStrongCouplingRadius_pos d Phi.bound_nonneg

/-- The explicit KP certificate specializes at zero coupling for every finite
specification and exterior field. -/
theorem zeroCoupling_koteckyPreissCertificate
    (Lambda : FiniteSpecification d G) (Phi : RealPlaquettePotential G) :
    (plaquettePolymerModel Lambda Phi 0).KoteckyPreissCertificate Finset.univ
      plaquetteKPWeight :=
  plaquettePolymerModel_koteckyPreiss_of_norm_lt_latticeRadius Lambda Phi
    (zeroCoupling_mem_latticeStrongCouplingDisk Phi)

/-- Every nonempty plaquette subset has zero activity at zero coupling. -/
theorem subsetWeight_zeroCoupling_of_nonempty
    (Lambda : FiniteSpecification d G) (Phi : RealPlaquettePotential G)
    {X : Finset (Plaquette d)} (hX : X.Nonempty) :
    subsetWeight Lambda Phi 0 X = 0 := by
  obtain ⟨p, hp⟩ := hX
  unfold subsetWeight subsetIntegrand
  have hintegrand (U : DynamicConfiguration Lambda) :
      ∏ q ∈ X, plaquettePerturbation Lambda Phi 0 q U = 0 := by
    apply Finset.prod_eq_zero hp
    simp [plaquettePerturbation]
  simp_rw [hintegrand]
  simp

/-- Consequently every connected plaquette-polymer activity vanishes at the
independent-Haar point. -/
theorem plaquettePolymer_activity_zeroCoupling
    (Lambda : FiniteSpecification d G) (Phi : RealPlaquettePotential G)
    (gamma : PlaquettePolymer Lambda) :
    (plaquettePolymerModel Lambda Phi 0).activity gamma = 0 :=
  subsetWeight_zeroCoupling_of_nonempty Lambda Phi gamma.support_nonempty

/-- The chosen symmetric Mayer logarithm is itself zero at the origin.  This
is stronger than merely knowing that its exponential is one. -/
theorem symmetricMayerSum_zeroCoupling
    (Lambda : FiniteSpecification d G) (Phi : RealPlaquettePotential G) :
    (plaquettePolymerModel Lambda Phi 0).symmetricMayerSum = 0 := by
  let M := plaquettePolymerModel Lambda Phi 0
  have hterm (X : FinitePolymerModel.MayerMultiIndex (PlaquettePolymer Lambda))
      (hdegree : 0 < FinitePolymerModel.mayerDegree X) :
      M.mayerClusterTerm X = 0 := by
    classical
    rw [FinitePolymerModel.mayerDegree] at hdegree
    obtain ⟨gamma, _, hgamma⟩ :=
      Finset.sum_pos_iff.mp hdegree
    have hmonomial : M.mayerActivityMonomial X = 0 := by
      unfold FinitePolymerModel.mayerActivityMonomial
      apply Finset.prod_eq_zero (Finset.mem_univ gamma)
      rw [show M.activity gamma = 0 by
        exact plaquettePolymer_activity_zeroCoupling Lambda Phi gamma]
      exact zero_pow hgamma.ne'
    simp [FinitePolymerModel.mayerClusterTerm, hmonomial]
  have hdegreeSum (k : ℕ) : M.symmetricMayerDegreeSum k = 0 := by
    cases k with
    | zero => exact M.symmetricMayerDegreeSum_zero
    | succ k =>
        unfold FinitePolymerModel.symmetricMayerDegreeSum
        apply Finset.sum_eq_zero
        intro X hX
        apply hterm X
        rw [(FinitePolymerModel.mem_mayerMultiIndicesOfDegree (k + 1) X).mp hX]
        omega
  change M.symmetricMayerSum = 0
  calc
    M.symmetricMayerSum = ∑' k, M.symmetricMayerDegreeSum k := rfl
    _ = ∑' _k : ℕ, (0 : ℂ) := tsum_congr hdegreeSum
    _ = 0 := tsum_zero

/-- The symmetry-normalized Mayer exponential has the correct value at the
origin.  This checks the branch normalization without incorrectly assuming
global injectivity of the complex exponential. -/
theorem exp_symmetricMayerSum_zeroCoupling
    (Lambda : FiniteSpecification d G) (Phi : RealPlaquettePotential G) :
    Complex.exp ((plaquettePolymerModel Lambda Phi 0).symmetricMayerSum) = 1 := by
  rw [exp_plaquetteSymmetricMayerSum_eq_complexPartitionFunction Lambda Phi
    (zeroCoupling_mem_latticeStrongCouplingDisk Phi)]
  simp

/-- In particular, the KP zero-free theorem is non-vacuous at the origin. -/
theorem complexPartitionFunction_zeroCoupling_ne_zero
    (Lambda : FiniteSpecification d G) (Phi : RealPlaquettePotential G) :
    complexPartitionFunction Lambda Phi 0 ≠ 0 :=
  complexPartitionFunction_ne_zero_of_norm_lt_latticeRadius_koteckyPreiss
    Lambda Phi (zeroCoupling_mem_latticeStrongCouplingDisk Phi)

/-! ## Infinite-volume consequences -/

/-- Boundary independence can be evaluated at the explicit point `beta = 0`. -/
theorem analyticInfiniteVolume_zeroCoupling_boundary_independent
    (F : LocalObservable d G) (eta eta' : ℕ → Configuration d G)
    (Phi : RealPlaquettePotential G) :
    analyticInfiniteVolumeLocalExpectation F eta Phi 0 =
      analyticInfiniteVolumeLocalExpectation F eta' Phi 0 :=
  analyticInfiniteVolumeLocalExpectation_boundary_independent F eta eta' Phi
    (Metric.mem_ball_self
      (latticeStrongCouplingRadius_pos d Phi.bound_nonneg))

/-- Combining the general infinite-volume gauge theorem with the Wilson-loop
constructor gives gauge invariance of Wilson expectations without imposing a
gauge-invariance hypothesis on the measure theorem itself. -/
theorem infiniteVolume_wilsonLoop_gaugePullback
    (eta : ℕ → Configuration d G) (beta : ℝ)
    (hbeta : ‖(beta : ℂ)‖ <
      latticeStrongCouplingRadius d rho.wilsonPotential.bound)
    (g : GaugeTransformation d G) {x : Site d}
    (C : Lattice.Cubic.Path x x) :
    ∫ A, rho.wilsonLoop C (gaugeTransform g A)
        ∂centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta hbeta =
      ∫ A, rho.wilsonLoop C A
        ∂centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta hbeta :=
  centeredInfiniteVolume_integral_gaugePullback eta rho.wilsonPotential beta
    hbeta g (rho.wilsonLoop C)

/-- A probability measure has zero covariance with a constant observable;
this sanity-checks the normalization used by the clustering statement. -/
theorem infiniteVolume_const_covariance_eq_zero
    (eta : ℕ → Configuration d G) (Phi : RealPlaquettePotential G)
    (beta : ℝ)
    (hbeta : ‖(beta : ℂ)‖ < latticeStrongCouplingRadius d Phi.bound)
    (z : ℂ) (H : LocalObservable d G) :
    (∫ A, ((LocalObservable.const (d := d) (G := G) z).mul H) A
        ∂centeredInfiniteVolumeMeasure eta Phi beta hbeta) -
      (∫ A, LocalObservable.const (d := d) (G := G) z A
        ∂centeredInfiniteVolumeMeasure eta Phi beta hbeta) *
      (∫ A, H A
        ∂centeredInfiniteVolumeMeasure eta Phi beta hbeta) = 0 := by
  simp only [LocalObservable.const, LocalObservable.mul,
    ContinuousMap.mul_apply, ContinuousMap.const_apply]
  rw [integral_const_mul]
  simp

/-! ## Reflection normalization -/

/-- A nonempty test fixture for the reflection-positivity API: both halves
and the reflection plane carry zero action. -/
def zeroActionDecomposition (G P O : Type*) [TopologicalSpace G] :
    WilsonActionDecomposition G P O where
  positiveAction := 0
  planeAction := 0

variable {P O : Type*} [Fintype P] [Fintype O]

@[simp]
theorem zeroAction_partitionFunction (beta : ℝ) :
    (zeroActionDecomposition G P O).partitionFunction beta = 1 := by
  have haction (U : ReflectedConfiguration G P O) :
      (zeroActionDecomposition G P O).action U = 0 := by
    simp [WilsonActionDecomposition.action, zeroActionDecomposition]
  unfold WilsonActionDecomposition.partitionFunction
  simp_rw [WilsonActionDecomposition.boltzmannWeight, haction]
  simp

/-- For the zero action, the normalized reflection norm of the constant-one
positive observable is exactly one. -/
@[simp]
theorem zeroAction_reflectionInnerProduct_one (beta : ℝ) :
    (zeroActionDecomposition G P O).reflectionInnerProduct beta
      (1 : PositiveObservable G P O) 1 = 1 := by
  rw [WilsonActionDecomposition.reflectionInnerProduct,
    zeroAction_partitionFunction]
  simp only [Complex.ofReal_one, inv_one, one_mul]
  rw [WilsonActionDecomposition.gibbsReflectionPairing_eq_factorized]
  simp [WilsonActionDecomposition.factorizedPairing,
    WilsonActionDecomposition.halfAmplitude, zeroActionDecomposition]

/-! ## A simple area-law specialization -/

/-- A rectangle with one zero side has zero area, so the area-law factor is
one and only the explicit perimeter prefactor remains. -/
theorem norm_analyticInfiniteVolumeWilsonRectangle_zeroHeight_le_perimeter
    (kappa : FiniteCenterChargeData rho) (x : Site d)
    (i j : Fin d) (hij : i ≠ j) (R : ℕ)
    (eta : ℕ → Configuration d G) {r : ℝ} (hr0 : 0 < r)
    (hr : r < latticeStrongCouplingRadius d rho.wilsonPotential.bound)
    (beta : ℂ) (hbeta : ‖beta‖ < r) :
    ‖analyticInfiniteVolumeLocalExpectation
        (rho.wilsonLoop (Path.rectangleBoundary x i j R 0))
        eta rho.wilsonPotential beta‖ ≤
      wilsonAreaPerimeterConstant (d := d) rho.wilsonPotential r ^ (2 * R) := by
  simpa using norm_analyticInfiniteVolumeWilsonRectangle_le_areaLaw
    kappa x i j hij R 0 eta hr0 hr beta hbeta

end

end YangMills.Tests.ReviewerSmoke
