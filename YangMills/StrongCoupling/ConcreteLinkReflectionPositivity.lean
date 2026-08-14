/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.LinkReflectionBridge
import YangMills.StrongCoupling.InfiniteVolumeReflectionPositivity
import YangMills.StrongCoupling.SymmetricReflectionBoxes

/-!
# Concrete link-reflection positivity at strong coupling

The box `[-n,n]^(d-1) × [-n,n+1]` is symmetric through the link plane at
`1/2`.  We complete its incident-plaquette action by making every edge read
by an active plaquette dynamic.  The finite one-sided gauge fix then applies
exactly.  A finite-specification Gibbs tower and the one-root KP boundary
estimate identify this completed exhaustion with the centered infinite-volume
state.  Gauge invariance is required only for the reflected observables.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

local instance concreteLinkDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Plaquettes incident to the internal edges of the link-symmetric box. -/
def linkSymmetricActivePlaquettes (d n : ℕ) (τ : Fin d) :
    Finset (Plaquette d) :=
  (linkSymmetricBox d n τ).positiveEdges.biUnion incidentPlaquettes

/-- Completed free-boundary link-symmetric specification.  The first union
keeps all box edges available to local observables; the second makes every
edge read by the action dynamic. -/
def linkSymmetricSpecification (G : Type*) [Group G]
    (d n : ℕ) (τ : Fin d) : FiniteSpecification d G where
  activePlaquettes := linkSymmetricActivePlaquettes d n τ
  dynamicEdges := (linkSymmetricBox d n τ).positiveEdges ∪
    (linkSymmetricActivePlaquettes d n τ).biUnion
      fun p => p.boundary.edgeSupport
  exterior := 1

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- Reflection preserves the internal edges of a link-symmetric box. -/
theorem linkReflect_mem_linkSymmetricBox_positiveEdges_iff
    (n : ℕ) (τ : Fin d) (e : PositiveEdge d) :
    e.linkReflect τ 0 ∈ (linkSymmetricBox d n τ).positiveEdges ↔
      e ∈ (linkSymmetricBox d n τ).positiveEdges := by
  rw [Box.mem_positiveEdges, Box.mem_positiveEdges]
  change ((e.linkReflect τ 0).source ∈ (linkSymmetricBox d n τ).sites ∧
      (e.linkReflect τ 0).target ∈ (linkSymmetricBox d n τ).sites) ↔
    (e.source ∈ (linkSymmetricBox d n τ).sites ∧
      e.target ∈ (linkSymmetricBox d n τ).sites)
  rcases PositiveEdge.linkReflect_endpoints τ 0 e with h | h
  · rw [h.1, h.2, linkReflection_mem_linkSymmetricBox_iff,
      linkReflection_mem_linkSymmetricBox_iff]
  · rw [h.1, h.2, linkReflection_mem_linkSymmetricBox_iff,
      linkReflection_mem_linkSymmetricBox_iff]
    exact and_comm

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem linkReflect_mem_linkSymmetricActivePlaquettes_of_mem
    (n : ℕ) (τ : Fin d) (p : Plaquette d) :
    p ∈ linkSymmetricActivePlaquettes d n τ →
      p.linkReflect τ 0 ∈ linkSymmetricActivePlaquettes d n τ := by
  simp only [linkSymmetricActivePlaquettes, Finset.mem_biUnion]
  rintro ⟨e, hebox, hep⟩
  refine ⟨e.linkReflect τ 0, ?_, ?_⟩
  · rw [linkReflect_mem_linkSymmetricBox_positiveEdges_iff]
    exact hebox
  · rw [mem_incidentPlaquettes_iff_mem_boundary] at hep ⊢
    exact (Gauge.FiniteSpecification.linkReflect_mem_plaquette_boundary_iff
      τ 0 e p).mpr hep

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem linkReflect_mem_linkSymmetricActivePlaquettes_iff
    (n : ℕ) (τ : Fin d) (p : Plaquette d) :
    p.linkReflect τ 0 ∈ linkSymmetricActivePlaquettes d n τ ↔
      p ∈ linkSymmetricActivePlaquettes d n τ := by
  constructor
  · intro hp
    have href := linkReflect_mem_linkSymmetricActivePlaquettes_of_mem n τ
      (p.linkReflect τ 0) hp
    rw [Plaquette.linkReflect_linkReflect] at href
    exact href
  · exact linkReflect_mem_linkSymmetricActivePlaquettes_of_mem n τ p

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem linkReflect_mem_linkSymmetricDynamicEdges_of_mem
    (n : ℕ) (τ : Fin d) (e : PositiveEdge d) :
    e ∈ (linkSymmetricSpecification G d n τ).dynamicEdges →
      e.linkReflect τ 0 ∈
        (linkSymmetricSpecification G d n τ).dynamicEdges := by
  intro he
  rw [linkSymmetricSpecification, Finset.mem_union] at he ⊢
  rcases he with hebox | heact
  · exact Or.inl ((linkReflect_mem_linkSymmetricBox_positiveEdges_iff
      n τ e).mpr hebox)
  · right
    rw [Finset.mem_biUnion] at heact ⊢
    obtain ⟨p, hp, hep⟩ := heact
    refine ⟨p.linkReflect τ 0,
      (linkReflect_mem_linkSymmetricActivePlaquettes_iff n τ p).mpr hp, ?_⟩
    exact (Gauge.FiniteSpecification.linkReflect_mem_plaquette_boundary_iff
      τ 0 e p).mpr hep

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- The completed link-symmetric specification has the exact geometric and
exterior symmetry required by the finite bridge. -/
theorem linkSymmetricSpecification_linkSymmetric
    (n : ℕ) (τ : Fin d) :
    (linkSymmetricSpecification G d n τ).LinkSymmetric τ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    constructor
    · exact linkReflect_mem_linkSymmetricDynamicEdges_of_mem n τ e
    · intro he
      have href := linkReflect_mem_linkSymmetricDynamicEdges_of_mem n τ
        (e.linkReflect τ 0) he
      simpa using href
  · intro p
    exact (linkReflect_mem_linkSymmetricActivePlaquettes_iff n τ p).symm
  · funext e
    simp [linkReflectConfiguration, linkSymmetricSpecification]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- Every active plaquette of the completed specification reads only dynamic
edges. -/
theorem linkSymmetricSpecification_plaquetteClosed
    (n : ℕ) (τ : Fin d) :
    (linkSymmetricSpecification G d n τ).PlaquetteClosed := by
  intro p hp e he
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, hp, he⟩)

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem linkSymmetricBox_sites_mono {m n : ℕ} (hmn : m ≤ n)
    (τ : Fin d) :
    (linkSymmetricBox d m τ).sites ⊆ (linkSymmetricBox d n τ).sites := by
  intro x hx
  rw [mem_linkSymmetricBox_sites] at hx ⊢
  have hcast : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
  exact ⟨(neg_le_neg hcast).trans hx.1,
    hx.2.1.trans (by omega), fun i hi =>
      ⟨(neg_le_neg hcast).trans (hx.2.2 i hi).1,
        (hx.2.2 i hi).2.trans hcast⟩⟩

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem linkSymmetricBox_positiveEdges_mono {m n : ℕ} (hmn : m ≤ n)
    (τ : Fin d) :
    (linkSymmetricBox d m τ).positiveEdges ⊆
      (linkSymmetricBox d n τ).positiveEdges := by
  intro e he
  rw [Box.mem_positiveEdges] at he ⊢
  exact ⟨linkSymmetricBox_sites_mono hmn τ he.1,
    linkSymmetricBox_sites_mono hmn τ he.2⟩

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem centeredBox_positiveEdges_subset_linkSymmetricBox
    (n : ℕ) (τ : Fin d) :
    (centeredBox d n).positiveEdges ⊆
      (linkSymmetricBox d n τ).positiveEdges := by
  intro e he
  rw [Box.mem_positiveEdges] at he ⊢
  change (e.source ∈ (centeredBox d n).sites ∧
      e.target ∈ (centeredBox d n).sites) at he
  change e.source ∈ (linkSymmetricBox d n τ).sites ∧
    e.target ∈ (linkSymmetricBox d n τ).sites
  simp only [mem_centeredBox_sites] at he
  constructor
  · rw [mem_linkSymmetricBox_sites]
    exact ⟨(he.1 τ).1, (he.1 τ).2.trans (by omega),
      fun i _ => he.1 i⟩
  · rw [mem_linkSymmetricBox_sites]
    exact ⟨(he.2 τ).1, (he.2 τ).2.trans (by omega),
      fun i _ => he.2 i⟩

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem centeredActivePlaquettes_subset_linkSymmetricActivePlaquettes
    (n : ℕ) (τ : Fin d) :
    centeredActivePlaquettes d n ⊆ linkSymmetricActivePlaquettes d n τ := by
  intro p hp
  rw [centeredActivePlaquettes, Finset.mem_biUnion] at hp
  rw [linkSymmetricActivePlaquettes, Finset.mem_biUnion]
  obtain ⟨e, he, hp⟩ := hp
  exact ⟨e, centeredBox_positiveEdges_subset_linkSymmetricBox n τ he, hp⟩

/-- The ordinary centered box is a complete conditional subsystem of the
completed link-symmetric box of the same radius. -/
def centeredToLinkSymmetricSubspecification
    (n : ℕ) (τ : Fin d) (η : Configuration d G) :
    FiniteSubspecification (centeredSpecification n η)
      (linkSymmetricSpecification G d n τ) where
  dynamic_subset := by
    intro e he
    exact Finset.mem_union_left _
      (centeredBox_positiveEdges_subset_linkSymmetricBox n τ he)
  active_subset := centeredActivePlaquettes_subset_linkSymmetricActivePlaquettes
    n τ
  boundary_disjoint_of_not_active := by
    intro p hp
    exact boundary_disjoint_centeredBox_of_not_active hp

/-- The one-root KP boundary tail compares the completed link-symmetric box
with an ordinary centered box, uniformly in the centered exterior field. -/
theorem norm_linkSymmetric_sub_centered_le_eventually
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (r : ℕ) :
    ∃ N, ∀ n, N ≤ n → ∀ η : Configuration d G,
      ‖complexGibbsExpectation F (linkSymmetricSpecification G d n τ)
          Φ (β : ℂ) -
        complexGibbsExpectation F (centeredSpecification n η) Φ (β : ℂ)‖ ≤
      2 * observableCardinalityTiltDecorationBudget (d := d) F Φ (β : ℂ) *
        plaquetteClusterDecayRate (d := d) Φ (β : ℂ) ^ r := by
  obtain ⟨N, hN⟩ :=
    norm_centered_complexGibbsExpectation_boundary_sub_le_eventually
      F Φ hβ r
  refine ⟨N, fun n hn η => ?_⟩
  let small := centeredSpecification n η
  let large := linkSymmetricSpecification G d n τ
  let h : FiniteSubspecification small large :=
    centeredToLinkSymmetricSubspecification n τ η
  apply h.norm_complexGibbsExpectation_large_sub_small_le_of_uniform
    η F Φ β _
  intro ξ
  simpa only [small, centeredSpecification] using hN n hn ξ η

/-- Completed link-symmetric and centered expectations have the same local
thermodynamic limit.  This is the explicit one-root KP tail passed through
the finite-specification Gibbs tower. -/
theorem tendsto_linkSymmetric_sub_centered_zero
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (η : ℕ → Configuration d G) :
    Tendsto (fun n =>
      complexGibbsExpectation F (linkSymmetricSpecification G d n τ)
          Φ (β : ℂ) -
        complexGibbsExpectation F (centeredSpecification n (η n))
          Φ (β : ℂ)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let B := 2 * observableCardinalityTiltDecorationBudget (d := d)
    F Φ (β : ℂ)
  let q := plaquetteClusterDecayRate (d := d) Φ (β : ℂ)
  have hq0 : 0 ≤ q := (plaquetteClusterDecayRate_pos Φ hβ).le
  have hq1 : q < 1 := plaquetteClusterDecayRate_lt_one Φ hβ
  have hmajorant : Tendsto (fun r : ℕ => B * q ^ r) atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul B
  have hevent : ∀ᶠ r in atTop, B * q ^ r < ε :=
    hmajorant (gt_mem_nhds hε)
  obtain ⟨r, hr⟩ := eventually_atTop.1 hevent
  obtain ⟨N, hN⟩ := norm_linkSymmetric_sub_centered_le_eventually
    F Φ β hβ τ r
  refine ⟨max N r, fun n hn => ?_⟩
  rw [dist_zero_right]
  exact (hN n ((Nat.le_max_left N r).trans hn) (η n)).trans_lt
    (by simpa [B, q] using hr r le_rfl)

/-- Gibbs probability on the completed link-symmetric box. -/
def linkSymmetricGibbsSequence
    (Φ : RealPlaquettePotential G) (β : ℝ) (τ : Fin d) (n : ℕ) :
    ProbabilityMeasure (Configuration d G) :=
  fullGibbsProbability (linkSymmetricSpecification G d n τ) Φ β

/-- The completed link-symmetric exhaustion converges on every local
observable to the cluster-constructed centered infinite-volume measure. -/
theorem tendsto_linkSymmetric_localExpectation_infiniteVolume
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (F : LocalObservable d G) :
    Tendsto (fun n => localExpectation
      (linkSymmetricGibbsSequence Φ β τ n) F) atTop
      (nhds (∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ)) := by
  have hdiff := tendsto_linkSymmetric_sub_centered_zero F Φ β hβ τ η
  have hcentered := tendsto_centered_localExpectation_infiniteVolume
    η Φ β hβ F
  have hadd := hdiff.add hcentered
  convert hadd using 1
  · ext n
    simp [linkSymmetricGibbsSequence, centeredGibbsSequence,
      localExpectation_fullGibbsProbability]
  · simp

/-- Every finite observable support is eventually dynamic in the completed
link-symmetric exhaustion. -/
theorem support_subset_linkSymmetricSpecification_eventually
    (τ : Fin d) (F : LocalObservable d G) :
  ∀ᶠ n in atTop,
      F.support ⊆ (linkSymmetricSpecification G d n τ).dynamicEdges := by
  obtain ⟨N, hN⟩ := finiteSupport_subset_linkSymmetricBox τ F.support
  refine Filter.eventually_atTop.2 ⟨N, fun n hn e he => ?_⟩
  exact Finset.mem_union_left _
    (linkSymmetricBox_positiveEdges_mono hn τ (hN he))

/-- Finite completed link-symmetric Gibbs laws are positive on each
gauge-invariant positive observable whose support is already dynamic. -/
theorem linkSymmetricGibbsSequence_reflectionPositive_of_support
    {nρ : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G nρ)
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (τ : Fin d)
    (F : LocalObservable d G)
    (hFhalf : F.SupportedInLinkPositiveHalf τ 0)
    (hFgauge : Gauge.IsGaugeInvariant F)
    (hFdyn : F.support ⊆
      (linkSymmetricSpecification G d n τ).dynamicEdges) :
    Complex.im (localExpectation
      (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n)
        (F.linkReflectionProduct τ 0 F)) = 0 ∧
      0 ≤ Complex.re (localExpectation
        (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n)
          (F.linkReflectionProduct τ 0 F)) := by
  let Λ := linkSymmetricSpecification G d n τ
  have hfinite := Λ.linkReflectionPositive_gibbsMeasure τ 0
    (linkSymmetricSpecification_linkSymmetric n τ)
    (linkSymmetricSpecification_plaquetteClosed n τ)
    ρ hβ F hFhalf hFgauge hFdyn
  change Complex.im (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (F.linkReflectionProduct τ 0 F)) = 0 ∧
    0 ≤ Complex.re (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (F.linkReflectionProduct τ 0 F))
  rw [localExpectation_fullGibbsProbability,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact hfinite

/-- Strong-coupling link reflection positivity through the plane at `1/2`.
The passage to infinite volume uses the completed-box KP comparison above. -/
theorem centeredInfiniteVolume_linkReflectionPositive_half
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    (τ : Fin d) :
    LinkReflectionPositive
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) τ 0 := by
  intro F hFhalf hFgauge
  let O := F.linkReflectionProduct τ 0 F
  have hO := tendsto_linkSymmetric_localExpectation_infiniteVolume
    η ρ.wilsonPotential β hβ τ O
  have hre : Tendsto (fun n => Complex.re (localExpectation
      (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n) O)) atTop
      (nhds (Complex.re (∫ A, O A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ))) :=
    Complex.continuous_re.continuousAt.tendsto.comp hO
  have him : Tendsto (fun n => Complex.im (localExpectation
      (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n) O)) atTop
      (nhds (Complex.im (∫ A, O A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ))) :=
    Complex.continuous_im.continuousAt.tendsto.comp hO
  have hsupport := support_subset_linkSymmetricSpecification_eventually τ F
  have hfinite : ∀ᶠ n in atTop,
      Complex.im (localExpectation
        (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n) O) = 0 ∧
      0 ≤ Complex.re (localExpectation
        (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n) O) :=
    hsupport.mono fun n hn =>
      linkSymmetricGibbsSequence_reflectionPositive_of_support
        ρ hβ0 n τ F hFhalf hFgauge hn
  have himZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have heventIm : (fun n => Complex.im (localExpectation
      (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n) O)) =ᶠ[atTop]
      fun _ => (0 : ℝ) := hfinite.mono fun _ hn => hn.1
  have him' : Tendsto (fun n => Complex.im (localExpectation
      (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n) O)) atTop
      (nhds 0) := himZero.congr' heventIm.symm
  constructor
  · exact tendsto_nhds_unique him him'
  · exact isClosed_Ici.mem_of_tendsto hre <| hfinite.mono fun _ hn => hn.2

/-- Finite completed link-symmetric Gibbs laws satisfy reflected
Cauchy--Schwarz once both observable supports are dynamic. -/
theorem linkSymmetricGibbsSequence_reflectionCauchySchwarz_of_support
    {nρ : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G nρ)
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (τ : Fin d)
    (F H : LocalObservable d G)
    (hFhalf : F.SupportedInLinkPositiveHalf τ 0)
    (hHhalf : H.SupportedInLinkPositiveHalf τ 0)
    (hFgauge : Gauge.IsGaugeInvariant F)
    (hHgauge : Gauge.IsGaugeInvariant H)
    (hFdyn : F.support ⊆
      (linkSymmetricSpecification G d n τ).dynamicEdges)
    (hHdyn : H.support ⊆
      (linkSymmetricSpecification G d n τ).dynamicEdges) :
    Complex.normSq (localExpectation
      (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n)
        (F.linkReflectionProduct τ 0 H)) ≤
      Complex.re (localExpectation
        (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n)
          (F.linkReflectionProduct τ 0 F)) *
      Complex.re (localExpectation
        (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n)
          (H.linkReflectionProduct τ 0 H)) := by
  let Λ := linkSymmetricSpecification G d n τ
  have hfinite :=
    Λ.normSq_integral_gibbsMeasure_linkReflectionProduct_le τ 0
      (linkSymmetricSpecification_linkSymmetric n τ)
      (linkSymmetricSpecification_plaquetteClosed n τ)
      ρ hβ F H hFhalf hHhalf hFgauge hHgauge hFdyn hHdyn
  change Complex.normSq (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (F.linkReflectionProduct τ 0 H)) ≤
    Complex.re (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (F.linkReflectionProduct τ 0 F)) *
    Complex.re (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (H.linkReflectionProduct τ 0 H))
  rw [localExpectation_fullGibbsProbability,
    localExpectation_fullGibbsProbability,
    localExpectation_fullGibbsProbability,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact hfinite

/-- Strong-coupling link-reflection Cauchy--Schwarz through the plane at
`1/2`, obtained from the same completed-box KP limit. -/
theorem centeredInfiniteVolume_linkReflectionCauchySchwarz_half
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    (τ : Fin d) :
    LinkReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) τ 0 := by
  intro F H hFhalf hHhalf hFgauge hHgauge
  let OFH := F.linkReflectionProduct τ 0 H
  let OFF := F.linkReflectionProduct τ 0 F
  let OHH := H.linkReflectionProduct τ 0 H
  have hFH := tendsto_linkSymmetric_localExpectation_infiniteVolume
    η ρ.wilsonPotential β hβ τ OFH
  have hFF := tendsto_linkSymmetric_localExpectation_infiniteVolume
    η ρ.wilsonPotential β hβ τ OFF
  have hHH := tendsto_linkSymmetric_localExpectation_infiniteVolume
    η ρ.wilsonPotential β hβ τ OHH
  have hlhs : Tendsto (fun n => Complex.normSq (localExpectation
      (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n) OFH)) atTop
      (nhds (Complex.normSq (∫ A, OFH A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ))) :=
    Complex.continuous_normSq.continuousAt.tendsto.comp hFH
  have hrhs : Tendsto (fun n =>
      Complex.re (localExpectation
        (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n) OFF) *
      Complex.re (localExpectation
        (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n) OHH)) atTop
      (nhds (Complex.re (∫ A, OFF A
          ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) *
        Complex.re (∫ A, OHH A
          ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ))) :=
    (Complex.continuous_re.continuousAt.tendsto.comp hFF).mul
      (Complex.continuous_re.continuousAt.tendsto.comp hHH)
  have hsupportF := support_subset_linkSymmetricSpecification_eventually τ F
  have hsupportH := support_subset_linkSymmetricSpecification_eventually τ H
  have hfinite : ∀ᶠ n in atTop,
      Complex.normSq (localExpectation
        (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n) OFH) ≤
      Complex.re (localExpectation
        (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n) OFF) *
      Complex.re (localExpectation
        (linkSymmetricGibbsSequence ρ.wilsonPotential β τ n) OHH) := by
    filter_upwards [hsupportF, hsupportH] with n hFn hHn
    exact linkSymmetricGibbsSequence_reflectionCauchySchwarz_of_support
      ρ hβ0 n τ F H hFhalf hHhalf hFgauge hHgauge hFn hHn
  exact le_of_tendsto_of_tendsto hlhs hrhs hfinite

/-- Concrete strong-coupling link-reflection positivity on every affine
half-integer coordinate plane. -/
theorem centeredInfiniteVolume_linkReflectionPositive
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    (τ : Fin d) (k : ℤ) :
    LinkReflectionPositive
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) τ k := by
  exact centeredInfiniteVolume_linkReflectionPositive_all_planes
    η ρ.wilsonPotential β hβ τ
      (centeredInfiniteVolume_linkReflectionPositive_half
        η ρ β hβ0 hβ τ) k

/-- Concrete strong-coupling link-reflection Cauchy--Schwarz on every affine
half-integer coordinate plane. -/
theorem centeredInfiniteVolume_linkReflectionCauchySchwarz
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    (τ : Fin d) (k : ℤ) :
    LinkReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) τ k := by
  exact centeredInfiniteVolume_linkReflectionCauchySchwarz_all_planes
    η ρ.wilsonPotential β hβ τ
      (centeredInfiniteVolume_linkReflectionCauchySchwarz_half
        η ρ β hβ0 hβ τ) k

end

end YangMills.StrongCoupling
