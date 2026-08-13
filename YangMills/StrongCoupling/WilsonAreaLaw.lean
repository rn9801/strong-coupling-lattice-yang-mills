/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.WilsonTaylorJets
import YangMills.StrongCoupling.ThermodynamicAnalyticity
import YangMills.StrongCoupling.CenteredBoundaryExpansion
import Mathlib.Analysis.Complex.Schwarz

/-!
# Strong-coupling Wilson area law

This file passes the exact finite-volume center-selection rule to the
cluster-expansion infinite-volume state.  We use completed centered boxes:
their action contains the usual centered active plaquettes, while every edge
read by those plaquettes and by the Wilson loop is integrated.  Conditioning
the added coordinates gives the ordinary centered box with an induced frozen
exterior field.  The existing one-root KP boundary tail therefore identifies
the completed-box limit with the already constructed infinite-volume state.

No Douglas compatibility or Dobrushin uniqueness theorem enters the proof.
-/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Wilson
open Filter Metric Set
open scoped Topology BigOperators

noncomputable section

local instance wilsonAreaLawDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [CompactSpace G] [T2Space G]
  [GaugeHaarProbability G]
  {rho : ContinuousUnitaryRepData G n}

/-! ## Completed centered boxes -/

/-- A centered box completed by integrating every edge read by its active
plaquettes and every edge read by the marked Wilson loop.  The action itself
is unchanged: its active plaquettes are exactly `centeredActivePlaquettes`.
-/
def completedCenteredWilsonSpecification {x : Site d}
    (C : Lattice.Cubic.Path x x) (m : ℕ) : FiniteSpecification d G where
  dynamicEdges :=
    (centeredBox d m).positiveEdges ∪
      (centeredActivePlaquettes d m).biUnion
        (fun p ↦ p.boundary.edgeSupport) ∪ C.edgeSupport
  activePlaquettes := centeredActivePlaquettes d m
  exterior := fun _ ↦ 1

@[simp]
theorem completedCenteredWilsonSpecification_dynamicEdges {x : Site d}
    (C : Lattice.Cubic.Path x x) (m : ℕ) :
    (completedCenteredWilsonSpecification (G := G) C m).dynamicEdges =
      (centeredBox d m).positiveEdges ∪
        (centeredActivePlaquettes d m).biUnion
          (fun p ↦ p.boundary.edgeSupport) ∪ C.edgeSupport :=
  rfl

@[simp]
theorem completedCenteredWilsonSpecification_activePlaquettes {x : Site d}
    (C : Lattice.Cubic.Path x x) (m : ℕ) :
    (completedCenteredWilsonSpecification (G := G) C m).activePlaquettes =
      centeredActivePlaquettes d m :=
  rfl

theorem loopSupport_subset_completedCenteredWilsonSpecification {x : Site d}
    (C : Lattice.Cubic.Path x x) (m : ℕ) :
    C.edgeSupport ⊆
      (completedCenteredWilsonSpecification (G := G) C m).dynamicEdges := by
  intro e he
  exact Finset.mem_union_right _ he

theorem activeBoundary_subset_completedCenteredWilsonSpecification {x : Site d}
    (C : Lattice.Cubic.Path x x) (m : ℕ) :
    ∀ p ∈ (completedCenteredWilsonSpecification (G := G) C m).activePlaquettes,
      p.boundary.edgeSupport ⊆
        (completedCenteredWilsonSpecification (G := G) C m).dynamicEdges := by
  intro p hp e he
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨p, hp, he⟩))

/-- The ordinary centered specification is a complete conditional subsystem
of the corresponding completed Wilson box. -/
def centeredToCompletedWilsonSubspecification {x : Site d}
    (C : Lattice.Cubic.Path x x) (m : ℕ) (eta : Configuration d G) :
    FiniteSubspecification (centeredSpecification m eta)
      (completedCenteredWilsonSpecification C m) where
  dynamic_subset := by
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  active_subset := by
    intro p hp
    exact hp
  boundary_disjoint_of_not_active := by
    intro p hp
    exact boundary_disjoint_centeredBox_of_not_active hp

/-! ## The one-root cluster bridge -/

/-- The existing one-root KP boundary tail compares a completed box to the
ordinary centered box, uniformly in the centered exterior field. -/
theorem norm_completedCenteredWilson_sub_centered_le_eventually
    {x : Site d} (C : Lattice.Cubic.Path x x)
    (Phi : RealPlaquettePotential G) (beta : ℝ)
    (hbeta : ‖(beta : ℂ)‖ < latticeStrongCouplingRadius d Phi.bound)
    (r : ℕ) :
    ∃ N, ∀ m, N ≤ m → ∀ eta : Configuration d G,
      ‖complexGibbsExpectation (rho.wilsonLoop C)
          (completedCenteredWilsonSpecification C m) Phi (beta : ℂ) -
        complexGibbsExpectation (rho.wilsonLoop C)
          (centeredSpecification m eta) Phi (beta : ℂ)‖ ≤
      2 * observableCardinalityTiltDecorationBudget (d := d)
          (rho.wilsonLoop C) Phi (beta : ℂ) *
        plaquetteClusterDecayRate (d := d) Phi (beta : ℂ) ^ r := by
  obtain ⟨N, hN⟩ :=
    norm_centered_complexGibbsExpectation_boundary_sub_le_eventually
      (rho.wilsonLoop C) Phi hbeta r
  refine ⟨N, fun m hm eta ↦ ?_⟩
  let small := centeredSpecification m eta
  let large := completedCenteredWilsonSpecification (G := G) C m
  let h : FiniteSubspecification small large :=
    centeredToCompletedWilsonSubspecification C m eta
  apply h.norm_complexGibbsExpectation_large_sub_small_le_of_uniform
    eta (rho.wilsonLoop C) Phi beta _
  intro xi
  simpa only [small, centeredSpecification] using hN m hm xi eta

/-- Completed and ordinary centered expectations have the same real
thermodynamic limit.  This is precisely the conditioning argument above plus
the geometric one-root KP tail tending to zero. -/
theorem tendsto_completedCenteredWilson_sub_centered_zero
    {x : Site d} (C : Lattice.Cubic.Path x x)
    (Phi : RealPlaquettePotential G) (beta : ℝ)
    (hbeta : ‖(beta : ℂ)‖ < latticeStrongCouplingRadius d Phi.bound)
    (eta : ℕ → Configuration d G) :
    Tendsto (fun m ↦
      complexGibbsExpectation (rho.wilsonLoop C)
          (completedCenteredWilsonSpecification C m) Phi (beta : ℂ) -
        complexGibbsExpectation (rho.wilsonLoop C)
          (centeredSpecification m (eta m)) Phi (beta : ℂ))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let B := 2 * observableCardinalityTiltDecorationBudget (d := d)
    (rho.wilsonLoop C) Phi (beta : ℂ)
  let q := plaquetteClusterDecayRate (d := d) Phi (beta : ℂ)
  have hq0 : 0 ≤ q := (plaquetteClusterDecayRate_pos Phi hbeta).le
  have hq1 : q < 1 := plaquetteClusterDecayRate_lt_one Phi hbeta
  have hmajorant : Tendsto (fun r : ℕ ↦ B * q ^ r) atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul B
  have hevent : ∀ᶠ r in atTop, B * q ^ r < epsilon :=
    hmajorant (gt_mem_nhds hepsilon)
  obtain ⟨r, hr⟩ := eventually_atTop.1 hevent
  obtain ⟨N, hN⟩ := norm_completedCenteredWilson_sub_centered_le_eventually
    (rho := rho) C Phi beta hbeta r
  refine ⟨max N r, fun m hm ↦ ?_⟩
  rw [dist_zero_right]
  exact (hN m ((Nat.le_max_left N r).trans hm) (eta m)).trans_lt
    (by simpa [B, q] using hr r le_rfl)

/-- The completed-box analytic sequence. -/
def completedCenteredWilsonExpectationSequence {x : Site d}
    (C : Lattice.Cubic.Path x x) (Phi : RealPlaquettePotential G)
    (m : ℕ) (z : ℂ) : ℂ :=
  complexGibbsExpectation (rho.wilsonLoop C)
    (completedCenteredWilsonSpecification C m) Phi z

/-- The Vitali limit of completed boxes. -/
def analyticCompletedCenteredWilsonExpectation {x : Site d}
    (C : Lattice.Cubic.Path x x) (Phi : RealPlaquettePotential G)
    (z : ℂ) : ℂ :=
  YangMills.VitaliOnDisk.limit
    (completedCenteredWilsonExpectationSequence (rho := rho) C Phi) z

theorem analyticCompletedCenteredWilsonExpectation_properties
    {x : Site d} (C : Lattice.Cubic.Path x x)
    (eta : ℕ → Configuration d G) (Phi : RealPlaquettePotential G) :
    AnalyticOnNhd ℂ (analyticCompletedCenteredWilsonExpectation (rho := rho) C Phi)
        (ball 0 (latticeStrongCouplingRadius d Phi.bound)) ∧
      TendstoLocallyUniformlyOn
        (completedCenteredWilsonExpectationSequence (rho := rho) C Phi)
        (analyticCompletedCenteredWilsonExpectation (rho := rho) C Phi) atTop
        (ball 0 (latticeStrongCouplingRadius d Phi.bound)) ∧
      ∀ beta : ℝ, |beta| < latticeStrongCouplingRadius d Phi.bound →
        analyticCompletedCenteredWilsonExpectation (rho := rho) C Phi (beta : ℂ) =
          centeredInfiniteVolumeLocalExpectationOnReal
            (rho.wilsonLoop C) eta Phi beta := by
  have hreal (beta : ℝ) (hbeta : |beta| < latticeStrongCouplingRadius d Phi.bound) :
      Tendsto (fun m ↦ completedCenteredWilsonExpectationSequence
          (rho := rho) C Phi m (beta : ℂ)) atTop
        (nhds (centeredInfiniteVolumeLocalExpectationOnReal
          (rho.wilsonLoop C) eta Phi beta)) := by
    have hbetaComplex : ‖(beta : ℂ)‖ < latticeStrongCouplingRadius d Phi.bound := by
      simpa [Complex.norm_real] using hbeta
    have hdiff := tendsto_completedCenteredWilson_sub_centered_zero
      (rho := rho) C Phi beta hbetaComplex eta
    have hcentered : Tendsto (fun m ↦
        complexGibbsExpectation (rho.wilsonLoop C)
          (centeredSpecification m (eta m)) Phi (beta : ℂ)) atTop
        (nhds (centeredInfiniteVolumeLocalExpectationOnReal
          (rho.wilsonLoop C) eta Phi beta)) := by
      have h := tendsto_centered_localExpectation_infiniteVolume
        eta Phi beta hbetaComplex (rho.wilsonLoop C)
      simpa only [centeredGibbsSequence, localExpectation_fullGibbsProbability,
        centeredInfiniteVolumeLocalExpectationOnReal, dif_pos hbetaComplex] using h
    convert hdiff.add hcentered using 1
    · ext m
      simp [completedCenteredWilsonExpectationSequence]
    · simp
  exact YangMills.VitaliOnDisk.analytic_limit_and_tendstoLocallyUniformlyOn
    (latticeStrongCouplingRadius_pos d Phi.bound_nonneg)
    (fun m ↦ analyticOnNhd_complexGibbsExpectation (rho.wilsonLoop C)
      (completedCenteredWilsonSpecification C m) Phi)
    (fun r hr0 hr ↦ ⟨centeredComplexLocalExpectationBound
        (rho.wilsonLoop C) Phi r,
      centeredComplexLocalExpectationBound_nonneg (rho.wilsonLoop C) Phi r,
      fun m z hz ↦ norm_complexGibbsExpectation_le_centeredBound
        (rho.wilsonLoop C) (completedCenteredWilsonSpecification C m)
          Phi hr0 hr z hz⟩)
    (centeredInfiniteVolumeLocalExpectationOnReal (rho.wilsonLoop C) eta Phi)
    hreal

/-! ## Identification and passage of the zero jets -/

/-- The completed-box and ordinary analytic limits coincide on the whole
strong-coupling disk because the one-root cluster bridge identifies them on
the real diameter. -/
theorem analyticCompletedCenteredWilsonExpectation_eq_infiniteVolume
    {x : Site d} (C : Lattice.Cubic.Path x x)
    (eta : ℕ → Configuration d G) (Phi : RealPlaquettePotential G) :
    Set.EqOn (analyticCompletedCenteredWilsonExpectation (rho := rho) C Phi)
      (analyticInfiniteVolumeLocalExpectation (rho.wilsonLoop C) eta Phi)
      (ball 0 (latticeStrongCouplingRadius d Phi.bound)) := by
  have hR := latticeStrongCouplingRadius_pos d Phi.bound_nonneg
  apply AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (analyticCompletedCenteredWilsonExpectation_properties C eta Phi).1
      (analyticOnNhd_analyticInfiniteVolumeLocalExpectation
        (rho.wilsonLoop C) eta Phi)
      isPreconnected_ball (mem_ball_self hR)
  let a : ℕ → ℝ := fun m ↦
    (latticeStrongCouplingRadius d Phi.bound / 2) *
      (1 / ((m + 1 : ℕ) : ℝ))
  have ha0 : Tendsto a atTop (nhds 0) := by
    simpa [a] using (tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun m : ℕ ↦ (1 : ℝ) / (m + 1)) atTop (nhds 0)))
  have hac : Tendsto (fun m ↦ (a m : ℂ)) atTop (nhds 0) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp ha0
  apply mem_closure_of_tendsto hac
  filter_upwards [] with m
  have haPos : 0 < a m := by
    dsimp [a]
    positivity
  have haNorm : ‖(a m : ℂ)‖ < latticeStrongCouplingRadius d Phi.bound := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos haPos]
    have hone : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by norm_num)
    calc
      a m ≤ latticeStrongCouplingRadius d Phi.bound / 2 := by
        dsimp [a]
        simpa using mul_le_mul_of_nonneg_left hone
          (div_nonneg hR.le (by norm_num))
      _ < latticeStrongCouplingRadius d Phi.bound := by linarith
  constructor
  · change analyticCompletedCenteredWilsonExpectation (rho := rho) C Phi (a m : ℂ) =
      analyticInfiniteVolumeLocalExpectation (rho.wilsonLoop C) eta Phi (a m : ℂ)
    rw [(analyticCompletedCenteredWilsonExpectation_properties C eta Phi).2.2
      (a m) (by simpa [Complex.norm_real] using haNorm),
      analyticInfiniteVolumeLocalExpectation_ofReal
        (rho.wilsonLoop C) eta Phi (a m) haNorm]
    unfold centeredInfiniteVolumeLocalExpectationOnReal
    rw [dif_pos haNorm]
  · simpa using haPos.ne'

/-- Locally uniform convergence of analytic functions passes to every
iterated complex derivative. -/
theorem tendstoLocallyUniformlyOn_iteratedDeriv
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (h : TendstoLocallyUniformlyOn f g atTop U)
    (hf : ∀ m, AnalyticOnNhd ℂ (f m) U) (hU : IsOpen U) (N : ℕ) :
    TendstoLocallyUniformlyOn (fun m ↦ iteratedDeriv N (f m))
      (iteratedDeriv N g) atTop U := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
      have hd := ih.deriv
        (Eventually.of_forall fun m ↦ by
          simpa only [iteratedDeriv_eq_iterate] using
            (hf m).iterated_deriv N |>.differentiableOn) hU
      simpa only [Nat.succ_eq_add_one, iteratedDeriv_succ, Function.comp_apply] using hd

/-- Every infinite-volume Wilson jet below the algebraic filling area
vanishes.  This is the exact cluster-order selection statement used by the
area estimate. -/
theorem iteratedDeriv_analyticInfiniteVolumeWilsonLoop_zero_of_lt_fillingArea
    (kappa : FiniteCenterChargeData rho) {x : Site d}
    (C : Lattice.Cubic.Path x x) (eta : ℕ → Configuration d G)
    (N : ℕ) (hN : N < Lattice.Cubic.centerFillingArea
      (orderOf kappa.toCenterChargeData.omega) C) :
    iteratedDeriv N
      (analyticInfiniteVolumeLocalExpectation (rho.wilsonLoop C) eta
        rho.wilsonPotential) 0 = 0 := by
  let R := latticeStrongCouplingRadius d rho.wilsonPotential.bound
  let f : ℕ → ℂ → ℂ :=
    completedCenteredWilsonExpectationSequence (rho := rho) C rho.wilsonPotential
  let g : ℂ → ℂ :=
    analyticCompletedCenteredWilsonExpectation (rho := rho) C rho.wilsonPotential
  have hloc : TendstoLocallyUniformlyOn f g atTop (ball 0 R) :=
    (analyticCompletedCenteredWilsonExpectation_properties C eta
      rho.wilsonPotential).2.1
  have hf : ∀ m, AnalyticOnNhd ℂ (f m) (ball 0 R) := fun m ↦
    analyticOnNhd_complexGibbsExpectation (rho.wilsonLoop C)
      (completedCenteredWilsonSpecification C m) rho.wilsonPotential
  have hderiv := tendstoLocallyUniformlyOn_iteratedDeriv hloc hf isOpen_ball N
  have hzero : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (nhds 0) := tendsto_const_nhds
  have hfinite : ∀ m, iteratedDeriv N (f m) 0 = 0 := by
    intro m
    exact iteratedDeriv_complexGibbsExpectation_wilsonLoop_zero_of_lt_fillingArea
      kappa (completedCenteredWilsonSpecification C m) C N
        (loopSupport_subset_completedCenteredWilsonSpecification C m)
        (activeBoundary_subset_completedCenteredWilsonSpecification C m) hN
  have hlimit : iteratedDeriv N g 0 = 0 := by
    apply tendsto_nhds_unique (hderiv.tendsto_at (mem_ball_self
      (latticeStrongCouplingRadius_pos d rho.wilsonPotential.bound_nonneg)))
    exact hzero.congr' (Eventually.of_forall fun m ↦ (hfinite m).symm)
  have heq := analyticCompletedCenteredWilsonExpectation_eq_infiniteVolume
    (rho := rho) C eta rho.wilsonPotential
  have hjets := heq.iteratedDeriv_of_isOpen isOpen_ball N
  exact (hjets (mem_ball_self
    (latticeStrongCouplingRadius_pos d rho.wilsonPotential.bound_nonneg))).symm.trans hlimit

/-- Every infinite-volume Taylor jet below the geometric area of a coordinate
rectangle vanishes.  The finite-volume input is the cut-flux theorem, and the
passage to infinite volume is the same locally uniform cluster-expansion
limit used for general local observables. -/
theorem iteratedDeriv_analyticInfiniteVolumeWilsonRectangle_zero_of_lt_area
    (kappa : FiniteCenterChargeData rho) (x : Site d)
    (i j : Fin d) (hij : i ≠ j) (R T : ℕ)
    (eta : ℕ → Configuration d G) (N : ℕ) (hN : N < R * T) :
    iteratedDeriv N
      (analyticInfiniteVolumeLocalExpectation
        (rho.wilsonLoop (Lattice.Cubic.Path.rectangleBoundary x i j R T))
        eta rho.wilsonPotential) 0 = 0 := by
  let C := Lattice.Cubic.Path.rectangleBoundary x i j R T
  let rad := latticeStrongCouplingRadius d rho.wilsonPotential.bound
  let f : ℕ → ℂ → ℂ :=
    completedCenteredWilsonExpectationSequence (rho := rho) C rho.wilsonPotential
  let g : ℂ → ℂ :=
    analyticCompletedCenteredWilsonExpectation (rho := rho) C rho.wilsonPotential
  have hloc : TendstoLocallyUniformlyOn f g atTop (ball 0 rad) :=
    (analyticCompletedCenteredWilsonExpectation_properties C eta
      rho.wilsonPotential).2.1
  have hf : ∀ m, AnalyticOnNhd ℂ (f m) (ball 0 rad) := fun m ↦
    analyticOnNhd_complexGibbsExpectation (rho.wilsonLoop C)
      (completedCenteredWilsonSpecification C m) rho.wilsonPotential
  have hderiv := tendstoLocallyUniformlyOn_iteratedDeriv hloc hf isOpen_ball N
  have hzero : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (nhds 0) := tendsto_const_nhds
  have hfinite : ∀ m, iteratedDeriv N (f m) 0 = 0 := by
    intro m
    exact iteratedDeriv_complexGibbsExpectation_wilsonRectangle_zero_of_lt_area
      kappa (completedCenteredWilsonSpecification C m) x i j hij R T N
        (loopSupport_subset_completedCenteredWilsonSpecification C m)
        (activeBoundary_subset_completedCenteredWilsonSpecification C m) hN
  have hlimit : iteratedDeriv N g 0 = 0 := by
    apply tendsto_nhds_unique (hderiv.tendsto_at (mem_ball_self
      (latticeStrongCouplingRadius_pos d rho.wilsonPotential.bound_nonneg)))
    exact hzero.congr' (Eventually.of_forall fun m ↦ (hfinite m).symm)
  have heq := analyticCompletedCenteredWilsonExpectation_eq_infiniteVolume
    (rho := rho) C eta rho.wilsonPotential
  have hjets := heq.iteratedDeriv_of_isOpen isOpen_ball N
  exact (hjets (mem_ball_self
    (latticeStrongCouplingRadius_pos d rho.wilsonPotential.bound_nonneg))).symm.trans hlimit

/-! ## Quantitative analytic area estimate -/

/-- The explicit one-root KP bound passes to the analytic infinite-volume
state on every smaller closed disk. -/
theorem norm_analyticInfiniteVolumeLocalExpectation_le_centeredBound
    (F : LocalObservable d G) (eta : ℕ → Configuration d G)
    (Phi : RealPlaquettePotential G) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < latticeStrongCouplingRadius d Phi.bound)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) :
    ‖analyticInfiniteVolumeLocalExpectation F eta Phi z‖ ≤
      centeredComplexLocalExpectationBound F Phi r := by
  have hzr : ‖z‖ < latticeStrongCouplingRadius d Phi.bound := by
    have : ‖z‖ ≤ r := by
      simpa only [mem_closedBall, dist_zero_right] using hz
    exact this.trans_lt hr
  have ht := (tendstoLocallyUniformlyOn_centeredComplexLocalExpectationSequence
    F eta Phi).tendsto_at (by
      simpa only [mem_ball, dist_zero_right] using hzr)
  apply le_of_tendsto ht.norm
  exact Eventually.of_forall fun m ↦
    norm_centeredComplexLocalExpectationSequence_le_bound
      F eta Phi hr0 hr m z hz

/-- An analytic function whose first `A` Taylor coefficients vanish is
little-oh of the `(A-1)`st radial power.  This is the exact hypothesis needed
by Mathlib's higher-order Schwarz lemma. -/
theorem analytic_isLittleO_norm_pow_of_iteratedDeriv_eq_zero
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) {A : ℕ} (hA : 0 < A)
    (hjet : ∀ N < A, iteratedDeriv N f 0 = 0) :
    (f · - f 0) =o[nhds 0] (fun z : ℂ ↦ ‖z - 0‖ ^ (A - 1)) := by
  obtain ⟨F, hFanalytic, hfactor⟩ := hf.exists_eventuallyEq_sum_add_pow_mul A
  have hf0 : f 0 = 0 := by
    simpa using hjet 0 hA
  have hsum : ∀ z : ℂ,
      (∑ i ∈ Finset.range A,
        (z ^ i / i.factorial) • iteratedDeriv i f 0) = 0 := by
    intro z
    apply Finset.sum_eq_zero
    intro i hi
    simp [hjet i (Finset.mem_range.mp hi)]
  have hFbig : F =O[nhds 0] (fun _ : ℂ ↦ (1 : ℂ)) :=
    hFanalytic.continuousAt.tendsto.isBigO_one ℂ
  have hpow : (fun z : ℂ ↦ z ^ A) =o[nhds 0]
      (fun z : ℂ ↦ z ^ (A - 1)) := by
    exact Asymptotics.isLittleO_pow_pow (by omega)
  have hproduct : (fun z : ℂ ↦ z ^ A * F z) =o[nhds 0]
      (fun z : ℂ ↦ z ^ (A - 1) * 1) := hpow.mul_isBigO hFbig
  have hproductNorm : (fun z : ℂ ↦ z ^ A * F z) =o[nhds 0]
      (fun z : ℂ ↦ ‖z - 0‖ ^ (A - 1)) := by
    apply hproduct.norm_right.congr_right
    intro z
    simp [norm_pow]
  apply hproductNorm.congr'
  · filter_upwards [hfactor] with z hz
    rw [hz, hsum, hf0]
    simp
  · exact Eventually.of_forall fun _ ↦ rfl

/-- Strong-coupling area estimate in terms of the center filling area.  The
prefactor is the existing explicit one-root KP/tree certificate and the
small parameter is the ratio to any enclosing strong-coupling disk. -/
theorem norm_analyticInfiniteVolumeWilsonLoop_le_fillingAreaPower
    (kappa : FiniteCenterChargeData rho) {x : Site d}
    (C : Lattice.Cubic.Path x x) (eta : ℕ → Configuration d G)
    {r : ℝ} (hr0 : 0 < r)
    (hr : r < latticeStrongCouplingRadius d rho.wilsonPotential.bound)
    (beta : ℂ) (hbeta : ‖beta‖ < r) :
    ‖analyticInfiniteVolumeLocalExpectation (rho.wilsonLoop C) eta
        rho.wilsonPotential beta‖ ≤
      centeredComplexLocalExpectationBound (rho.wilsonLoop C)
          rho.wilsonPotential r *
        (‖beta‖ / r) ^ Lattice.Cubic.centerFillingArea
          (orderOf kappa.toCenterChargeData.omega) C := by
  let f := analyticInfiniteVolumeLocalExpectation
    (rho.wilsonLoop C) eta rho.wilsonPotential
  let A := Lattice.Cubic.centerFillingArea
    (orderOf kappa.toCenterChargeData.omega) C
  let M := centeredComplexLocalExpectationBound
    (rho.wilsonLoop C) rho.wilsonPotential r
  have hf : AnalyticOnNhd ℂ f
      (ball 0 (latticeStrongCouplingRadius d rho.wilsonPotential.bound)) :=
    analyticOnNhd_analyticInfiniteVolumeLocalExpectation
      (rho.wilsonLoop C) eta rho.wilsonPotential
  have hdiff : DifferentiableOn ℂ f (ball 0 r) :=
    hf.differentiableOn.mono (ball_subset_ball hr.le)
  by_cases hAzero : A = 0
  · have hareaZero : Lattice.Cubic.centerFillingArea
        (orderOf kappa.toCenterChargeData.omega) C = 0 := hAzero
    have hnorm := norm_analyticInfiniteVolumeLocalExpectation_le_centeredBound
      (rho.wilsonLoop C) eta rho.wilsonPotential hr0.le hr beta
      (ball_subset_closedBall (by
        simpa only [mem_ball, dist_zero_right] using hbeta))
    simpa [f, M, hareaZero] using hnorm
  · have hApos : 0 < A := Nat.pos_of_ne_zero hAzero
    have hjet : ∀ N < A, iteratedDeriv N f 0 = 0 := by
      intro N hN
      exact iteratedDeriv_analyticInfiniteVolumeWilsonLoop_zero_of_lt_fillingArea
        kappa C eta N hN
    have hf0 : f 0 = 0 := by simpa using hjet 0 hApos
    have hmaps : MapsTo f (ball 0 r) (closedBall (f 0) M) := by
      intro z hz
      have hnorm := norm_analyticInfiniteVolumeLocalExpectation_le_centeredBound
        (rho.wilsonLoop C) eta rho.wilsonPotential hr0.le hr z
          (ball_subset_closedBall hz)
      simpa [mem_closedBall, dist_eq_norm, hf0, M] using hnorm
    have hlittle := analytic_isLittleO_norm_pow_of_iteratedDeriv_eq_zero
      (hf 0 (by
        exact mem_ball_self (latticeStrongCouplingRadius_pos d
          rho.wilsonPotential.bound_nonneg))) hApos hjet
    have hschwarz := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
      hdiff hmaps hlittle (by
        simpa only [mem_ball, dist_zero_right] using hbeta)
    simpa [f, A, M, hf0, dist_eq_norm, Nat.sub_add_cancel hApos] using hschwarz

/-- Rectangle specialization with the genuine geometric exponent `R * T`.
The zero-size cases are retained so the theorem has no auxiliary positivity
assumption on the side lengths. -/
theorem norm_analyticInfiniteVolumeWilsonRectangle_le_areaPower
    (kappa : FiniteCenterChargeData rho) (x : Site d)
    (i j : Fin d) (hij : i ≠ j) (R T : ℕ)
    (eta : ℕ → Configuration d G) {r : ℝ} (hr0 : 0 < r)
    (hr : r < latticeStrongCouplingRadius d rho.wilsonPotential.bound)
    (beta : ℂ) (hbeta : ‖beta‖ < r) :
    ‖analyticInfiniteVolumeLocalExpectation
        (rho.wilsonLoop (Lattice.Cubic.Path.rectangleBoundary x i j R T))
        eta rho.wilsonPotential beta‖ ≤
      centeredComplexLocalExpectationBound
          (rho.wilsonLoop (Lattice.Cubic.Path.rectangleBoundary x i j R T))
          rho.wilsonPotential r * (‖beta‖ / r) ^ (R * T) := by
  let C := Lattice.Cubic.Path.rectangleBoundary x i j R T
  let f := analyticInfiniteVolumeLocalExpectation
    (rho.wilsonLoop C) eta rho.wilsonPotential
  let A := R * T
  let M := centeredComplexLocalExpectationBound
    (rho.wilsonLoop C) rho.wilsonPotential r
  have hf : AnalyticOnNhd ℂ f
      (ball 0 (latticeStrongCouplingRadius d rho.wilsonPotential.bound)) :=
    analyticOnNhd_analyticInfiniteVolumeLocalExpectation
      (rho.wilsonLoop C) eta rho.wilsonPotential
  have hdiff : DifferentiableOn ℂ f (ball 0 r) :=
    hf.differentiableOn.mono (ball_subset_ball hr.le)
  by_cases hAzero : A = 0
  · have hnorm := norm_analyticInfiniteVolumeLocalExpectation_le_centeredBound
      (rho.wilsonLoop C) eta rho.wilsonPotential hr0.le hr beta
      (ball_subset_closedBall (by
        simpa only [mem_ball, dist_zero_right] using hbeta))
    simpa [C, f, A, M, hAzero] using hnorm
  · have hApos : 0 < A := Nat.pos_of_ne_zero hAzero
    have hjet : ∀ N < A, iteratedDeriv N f 0 = 0 := by
      intro N hN
      exact iteratedDeriv_analyticInfiniteVolumeWilsonRectangle_zero_of_lt_area
        kappa x i j hij R T eta N hN
    have hf0 : f 0 = 0 := by simpa using hjet 0 hApos
    have hmaps : MapsTo f (ball 0 r) (closedBall (f 0) M) := by
      intro z hz
      have hnorm := norm_analyticInfiniteVolumeLocalExpectation_le_centeredBound
        (rho.wilsonLoop C) eta rho.wilsonPotential hr0.le hr z
          (ball_subset_closedBall hz)
      simpa [mem_closedBall, dist_eq_norm, hf0, M] using hnorm
    have hlittle := analytic_isLittleO_norm_pow_of_iteratedDeriv_eq_zero
      (hf 0 (by
        exact mem_ball_self (latticeStrongCouplingRadius_pos d
          rho.wilsonPotential.bound_nonneg))) hApos hjet
    have hschwarz := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
      hdiff hmaps hlittle (by
        simpa only [mem_ball, dist_zero_right] using hbeta)
    simpa [C, f, A, M, hf0, dist_eq_norm, Nat.sub_add_cancel hApos] using hschwarz

/-- The explicit exponential perimeter constant appearing when the
observable-root KP budget is separated from the loop support cardinality. -/
def wilsonAreaPerimeterConstant
    (Phi : RealPlaquettePotential G) (r : ℝ) : ℝ :=
  Real.exp (4 * d * Real.log 2) *
    Real.exp
      ((4 * d : ℝ) *
        ((2 * perturbationMajorant Phi (r : ℂ)) /
          (1 - (2 ^ (16 * d) : ℝ) *
            (2 * perturbationMajorant Phi (r : ℂ)))))

/-- The Wilson observable sup norm is at most one. -/
theorem norm_wilsonLoop_toBoundedContinuousMap_le_one {x : Site d}
    (C : Lattice.Cubic.Path x x) :
    ‖(rho.wilsonLoop C).toBoundedContinuousMap‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le zero_le_one]
  intro A
  exact rho.norm_wilsonLoop_le_one C A

/-- The explicit decorated-root KP prefactor is at most an exponential in
the loop perimeter. -/
theorem centeredWilsonBound_le_perimeterPower {x : Site d}
    (C : Lattice.Cubic.Path x x) (Phi : RealPlaquettePotential G) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < latticeStrongCouplingRadius d Phi.bound) :
    centeredComplexLocalExpectationBound (rho.wilsonLoop C) Phi r ≤
      wilsonAreaPerimeterConstant (d := d) Phi r ^ C.length := by
  let q := perturbationMajorant Phi (r : ℂ)
  let D := 1 - (2 ^ (16 * d) : ℝ) * (2 * q)
  let s := (2 * q) / D
  let a := (4 * d : ℝ) * Real.log 2
  let b := (4 * d : ℝ) * s
  have hrnorm : ‖(r : ℂ)‖ < latticeStrongCouplingRadius d Phi.bound := by
    simpa [Complex.norm_real, abs_of_nonneg hr0] using hr
  have hD : 0 < D := by
    dsimp [D, q]
    exact sub_pos.mpr
      (animalConstant_mul_two_mul_perturbationMajorant_lt_one Phi hrnorm)
  have hs0 : 0 ≤ s := by
    exact div_nonneg (mul_nonneg (by norm_num) (perturbationMajorant_nonneg Phi (r : ℂ))) hD.le
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb0 : 0 ≤ b := by
    dsimp [b]
    positivity
  have hcard : ((rho.wilsonLoop C).support.card : ℝ) ≤ C.length := by
    rw [rho.wilsonLoop_support]
    exact_mod_cast Lattice.Cubic.Path.card_edgeSupport_le_length C
  have hexpa : Real.exp (((4 * d * (rho.wilsonLoop C).support.card : ℕ) : ℝ) *
      Real.log 2) ≤ Real.exp a ^ C.length := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      (((4 * d * (rho.wilsonLoop C).support.card : ℕ) : ℝ) * Real.log 2) =
          (4 * (d : ℝ) * ((rho.wilsonLoop C).support.card : ℝ)) *
            Real.log 2 := by push_cast; ring
      _ ≤ (4 * (d : ℝ) * C.length) * Real.log 2 := by
        gcongr
      _ = (C.length : ℝ) * a := by dsimp [a]; ring
  have hexpb : Real.exp (((4 * d * (rho.wilsonLoop C).support.card : ℕ) : ℝ) * s) ≤
      Real.exp b ^ C.length := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      (((4 * d * (rho.wilsonLoop C).support.card : ℕ) : ℝ) * s) =
          (4 * (d : ℝ) * ((rho.wilsonLoop C).support.card : ℝ)) * s := by
            push_cast
            ring
      _ ≤ (4 * (d : ℝ) * C.length) * s := by gcongr
      _ = (C.length : ℝ) * b := by dsimp [b]; ring
  unfold centeredComplexLocalExpectationBound wilsonAreaPerimeterConstant
  change ‖(rho.wilsonLoop C).toBoundedContinuousMap‖ *
      Real.exp (((4 * d * (rho.wilsonLoop C).support.card : ℕ) : ℝ) * Real.log 2) *
      Real.exp (((4 * d * (rho.wilsonLoop C).support.card : ℕ) : ℝ) * s) ≤
    (Real.exp a * Real.exp b) ^ C.length
  rw [mul_pow]
  calc
    _ ≤ 1 * (Real.exp a ^ C.length) * (Real.exp b ^ C.length) := by
      gcongr
      exact norm_wilsonLoop_toBoundedContinuousMap_le_one C
    _ = _ := by ring

/-- General center-charged Wilson-loop area law with the roadmap-permitted
exponential perimeter prefactor.  The string tension is explicit and
positive whenever `‖beta‖ < r`. -/
theorem norm_analyticInfiniteVolumeWilsonLoop_le_areaLaw
    (kappa : FiniteCenterChargeData rho) {x : Site d}
    (C : Lattice.Cubic.Path x x) (eta : ℕ → Configuration d G)
    {r : ℝ} (hr0 : 0 < r)
    (hr : r < latticeStrongCouplingRadius d rho.wilsonPotential.bound)
    (beta : ℂ) (hbeta : ‖beta‖ < r) :
    ‖analyticInfiniteVolumeLocalExpectation (rho.wilsonLoop C) eta
        rho.wilsonPotential beta‖ ≤
      wilsonAreaPerimeterConstant (d := d) rho.wilsonPotential r ^ C.length *
        Real.exp (-Real.log (r / ‖beta‖) *
          Lattice.Cubic.centerFillingArea
            (orderOf kappa.toCenterChargeData.omega) C) := by
  by_cases hbeta0 : ‖beta‖ = 0
  · have hpow := norm_analyticInfiniteVolumeWilsonLoop_le_fillingAreaPower
      kappa C eta hr0 hr beta hbeta
    have hpref := centeredWilsonBound_le_perimeterPower
      (rho := rho) C rho.wilsonPotential hr0.le hr
    calc
      _ ≤ centeredComplexLocalExpectationBound (rho.wilsonLoop C)
          rho.wilsonPotential r *
          (‖beta‖ / r) ^ Lattice.Cubic.centerFillingArea
            (orderOf kappa.toCenterChargeData.omega) C := hpow
      _ ≤ wilsonAreaPerimeterConstant (d := d) rho.wilsonPotential r ^ C.length *
          (‖beta‖ / r) ^ Lattice.Cubic.centerFillingArea
            (orderOf kappa.toCenterChargeData.omega) C := by
        gcongr
      _ ≤ wilsonAreaPerimeterConstant (d := d) rho.wilsonPotential r ^ C.length := by
        rw [hbeta0]
        apply mul_le_of_le_one_right
        · unfold wilsonAreaPerimeterConstant
          positivity
        · exact pow_le_one₀ (by positivity) (by simp)
      _ = _ := by simp [hbeta0]
  · have hpow := norm_analyticInfiniteVolumeWilsonLoop_le_fillingAreaPower
      kappa C eta hr0 hr beta hbeta
    have hpref := centeredWilsonBound_le_perimeterPower
      (rho := rho) C rho.wilsonPotential hr0.le hr
    have hbetaPos : 0 < ‖beta‖ :=
      lt_of_le_of_ne (norm_nonneg beta) (Ne.symm hbeta0)
    have hratio : 0 < r / ‖beta‖ := div_pos hr0 hbetaPos
    have hexp : Real.exp (-Real.log (r / ‖beta‖) *
        Lattice.Cubic.centerFillingArea
          (orderOf kappa.toCenterChargeData.omega) C) =
        (‖beta‖ / r) ^ Lattice.Cubic.centerFillingArea
          (orderOf kappa.toCenterChargeData.omega) C := by
      rw [show -Real.log (r / ‖beta‖) *
          (Lattice.Cubic.centerFillingArea
            (orderOf kappa.toCenterChargeData.omega) C : ℝ) =
          (Lattice.Cubic.centerFillingArea
            (orderOf kappa.toCenterChargeData.omega) C : ℝ) *
            (-Real.log (r / ‖beta‖)) by ring]
      rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hratio]
      congr 1
      field_simp
    rw [hexp]
    exact hpow.trans (mul_le_mul_of_nonneg_right hpref (pow_nonneg (by positivity) _))

/-- Strong-coupling area law for an `R`-by-`T` coordinate rectangle.  The
string tension is `log (r / ‖beta‖) > 0`; the only geometric correction is
the explicit exponential perimeter prefactor already supplied by the
one-root KP/tree bound. -/
theorem norm_analyticInfiniteVolumeWilsonRectangle_le_areaLaw
    (kappa : FiniteCenterChargeData rho) (x : Site d)
    (i j : Fin d) (hij : i ≠ j) (R T : ℕ)
    (eta : ℕ → Configuration d G) {r : ℝ} (hr0 : 0 < r)
    (hr : r < latticeStrongCouplingRadius d rho.wilsonPotential.bound)
    (beta : ℂ) (hbeta : ‖beta‖ < r) :
    ‖analyticInfiniteVolumeLocalExpectation
        (rho.wilsonLoop (Lattice.Cubic.Path.rectangleBoundary x i j R T))
        eta rho.wilsonPotential beta‖ ≤
      wilsonAreaPerimeterConstant (d := d) rho.wilsonPotential r ^
          (2 * (R + T)) *
        Real.exp (-Real.log (r / ‖beta‖) * (R * T)) := by
  let C := Lattice.Cubic.Path.rectangleBoundary x i j R T
  have hpref := centeredWilsonBound_le_perimeterPower
    (rho := rho) C rho.wilsonPotential hr0.le hr
  have hlen : C.length = 2 * (R + T) := by
    simp [C]
    omega
  rw [hlen] at hpref
  have hpow := norm_analyticInfiniteVolumeWilsonRectangle_le_areaPower
    kappa x i j hij R T eta hr0 hr beta hbeta
  by_cases hbeta0 : ‖beta‖ = 0
  · calc
      _ ≤ centeredComplexLocalExpectationBound (rho.wilsonLoop C)
          rho.wilsonPotential r * (‖beta‖ / r) ^ (R * T) := by
            simpa [C] using hpow
      _ ≤ wilsonAreaPerimeterConstant (d := d) rho.wilsonPotential r ^
          (2 * (R + T)) * (‖beta‖ / r) ^ (R * T) := by gcongr
      _ ≤ wilsonAreaPerimeterConstant (d := d) rho.wilsonPotential r ^
          (2 * (R + T)) := by
        rw [hbeta0]
        apply mul_le_of_le_one_right
        · unfold wilsonAreaPerimeterConstant
          positivity
        · exact pow_le_one₀ (by positivity) (by simp)
      _ = _ := by simp [hbeta0]
  · have hbetaPos : 0 < ‖beta‖ :=
      lt_of_le_of_ne (norm_nonneg beta) (Ne.symm hbeta0)
    have hratio : 0 < r / ‖beta‖ := div_pos hr0 hbetaPos
    have hexp : Real.exp (-Real.log (r / ‖beta‖) * (R * T)) =
        (‖beta‖ / r) ^ (R * T) := by
      rw [← Nat.cast_mul]
      rw [show -Real.log (r / ‖beta‖) * ((R * T : ℕ) : ℝ) =
          ((R * T : ℕ) : ℝ) * (-Real.log (r / ‖beta‖)) by ring]
      rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hratio]
      congr 1
      field_simp
    rw [hexp]
    exact hpow.trans (mul_le_mul_of_nonneg_right hpref (pow_nonneg (by positivity) _))

/-- Physical real-coupling form of the rectangular area law for the concrete
infinite-volume probability measure. -/
theorem norm_integral_wilsonRectangle_le_areaLaw
    (kappa : FiniteCenterChargeData rho) (x : Site d)
    (i j : Fin d) (hij : i ≠ j) (R T : ℕ)
    (eta : ℕ → Configuration d G) {r : ℝ} (hr0 : 0 < r)
    (hr : r < latticeStrongCouplingRadius d rho.wilsonPotential.bound)
    (beta : ℝ) (hbeta : |beta| < r) :
    ‖∫ A, rho.wilsonLoop (Lattice.Cubic.Path.rectangleBoundary x i j R T) A
        ∂centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta
          (by simpa [Complex.norm_real] using hbeta.trans hr)‖ ≤
      wilsonAreaPerimeterConstant (d := d) rho.wilsonPotential r ^
          (2 * (R + T)) *
        Real.exp (-Real.log (r / |beta|) * (R * T)) := by
  have hbetaComplex : ‖(beta : ℂ)‖ < r := by
    simpa [Complex.norm_real] using hbeta
  have hbetaRadius : ‖(beta : ℂ)‖ <
      latticeStrongCouplingRadius d rho.wilsonPotential.bound :=
    hbetaComplex.trans hr
  have h := norm_analyticInfiniteVolumeWilsonRectangle_le_areaLaw
    kappa x i j hij R T eta hr0 hr (beta : ℂ) hbetaComplex
  rw [analyticInfiniteVolumeLocalExpectation_ofReal
    (rho.wilsonLoop (Lattice.Cubic.Path.rectangleBoundary x i j R T))
    eta rho.wilsonPotential beta hbetaRadius] at h
  simpa [Complex.norm_real] using h

end

end YangMills.StrongCoupling
