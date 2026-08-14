/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.SiteReflectionBridge
import YangMills.StrongCoupling.InfiniteVolumeReflectionPositivity
import YangMills.StrongCoupling.SymmetricReflectionBoxes

/-!
# Concrete site-reflection positivity at strong coupling

Centered boxes with identity exterior data are symmetric through every
coordinate plane through the origin.  The finite geometric bridge identifies
their Wilson Gibbs laws with the site-reflection normal form.  Reflection
positivity then passes to the cluster-constructed thermodynamic limit, and
the one-root KP boundary theorem removes the identity exterior condition.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem siteReflect_mem_centeredBox_positiveEdges_iff (n : ℕ) (τ : Fin d)
    (e : PositiveEdge d) :
    e.siteReflect τ 0 ∈ (centeredBox d n).positiveEdges ↔
      e ∈ (centeredBox d n).positiveEdges := by
  rw [Box.mem_positiveEdges, Box.mem_positiveEdges]
  change ((e.siteReflect τ 0).source ∈ (centeredBox d n).sites ∧
      (e.siteReflect τ 0).target ∈ (centeredBox d n).sites) ↔
    (e.source ∈ (centeredBox d n).sites ∧
      e.target ∈ (centeredBox d n).sites)
  rcases Gauge.FiniteSpecification.siteReflect_endpoints τ 0 e with h | h <;>
    rw [h.1, h.2, siteReflection_mem_centeredBox_iff,
      siteReflection_mem_centeredBox_iff]
  exact and_comm

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem siteReflect_mem_centeredActivePlaquettes_of_mem (n : ℕ) (τ : Fin d)
    (p : Plaquette d) :
    p ∈ centeredActivePlaquettes d n →
      p.siteReflect τ 0 ∈ centeredActivePlaquettes d n := by
  simp only [centeredActivePlaquettes, Finset.mem_biUnion]
  rintro ⟨e, hebox, hep⟩
  refine ⟨e.siteReflect τ 0, ?_, ?_⟩
  · rw [siteReflect_mem_centeredBox_positiveEdges_iff]
    exact hebox
  · rw [mem_incidentPlaquettes_iff_mem_boundary] at hep ⊢
    exact Gauge.FiniteSpecification.siteReflect_mem_plaquette_boundary_of_mem
      τ 0 e p hep

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem siteReflect_mem_centeredActivePlaquettes_iff (n : ℕ) (τ : Fin d)
    (p : Plaquette d) :
    p.siteReflect τ 0 ∈ centeredActivePlaquettes d n ↔
      p ∈ centeredActivePlaquettes d n := by
  constructor
  · intro hp
    have href := siteReflect_mem_centeredActivePlaquettes_of_mem n τ
      (p.siteReflect τ 0) hp
    rw [Plaquette.siteReflect_siteReflect] at href
    exact href
  · exact siteReflect_mem_centeredActivePlaquettes_of_mem n τ p

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- Every centered specification with identity exterior data has the exact
site-reflection symmetry required by the finite normal-form bridge. -/
theorem centeredSpecification_one_siteSymmetric (n : ℕ) (τ : Fin d) :
    (centeredSpecification n (1 : Configuration d G)).SiteSymmetric τ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    exact (siteReflect_mem_centeredBox_positiveEdges_iff n τ e).symm
  · intro p
    exact (siteReflect_mem_centeredActivePlaquettes_iff n τ p).symm
  · funext e
    simp [siteReflectConfiguration, centeredSpecification]

/-- Every finite centered Gibbs law with identity exterior is site-reflection
positive through the origin coordinate plane, for every real coupling. -/
theorem centeredGibbsSequence_one_siteReflectionPositive
    (Φ : RealPlaquettePotential G) (β : ℝ) (n : ℕ) (τ : Fin d) :
    SiteReflectionPositive
      (centeredGibbsSequence (fun _ => (1 : Configuration d G)) Φ β n :
        Measure (Configuration d G)) τ 0 := by
  intro F hF
  let Λ := centeredSpecification n (1 : Configuration d G)
  have hfinite := Λ.siteReflectionPositive_gibbsMeasure τ 0
    (centeredSpecification_one_siteSymmetric n τ) Φ β F hF
  change Complex.im (localExpectation
      (fullGibbsProbability Λ Φ β) (F.siteReflectionProduct τ 0 F)) = 0 ∧
    0 ≤ Complex.re (localExpectation
      (fullGibbsProbability Λ Φ β) (F.siteReflectionProduct τ 0 F))
  rw [localExpectation_fullGibbsProbability,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact hfinite

/-- Finite centered identity-exterior Gibbs laws satisfy Cauchy--Schwarz for
the site-reflection pairing. -/
theorem centeredGibbsSequence_one_siteReflectionCauchySchwarz
    (Φ : RealPlaquettePotential G) (β : ℝ) (n : ℕ) (τ : Fin d) :
    SiteReflectionCauchySchwarz
      (centeredGibbsSequence (fun _ => (1 : Configuration d G)) Φ β n :
        Measure (Configuration d G)) τ 0 := by
  intro F H hF hH
  let Λ := centeredSpecification n (1 : Configuration d G)
  have hfinite := Λ.normSq_integral_gibbsMeasure_siteReflectionProduct_le
    τ 0 (centeredSpecification_one_siteSymmetric n τ) Φ β F H hF hH
  unfold siteReflectionPairing
  simp only [centeredGibbsSequence]
  change Complex.normSq (localExpectation
      (fullGibbsProbability Λ Φ β) (F.siteReflectionProduct τ 0 H)) ≤
    Complex.re (localExpectation
      (fullGibbsProbability Λ Φ β) (F.siteReflectionProduct τ 0 F)) *
    Complex.re (localExpectation
      (fullGibbsProbability Λ Φ β) (H.siteReflectionProduct τ 0 H))
  rw [localExpectation_fullGibbsProbability,
    localExpectation_fullGibbsProbability,
    localExpectation_fullGibbsProbability,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact hfinite

/-- Milestone 17, concrete form: the cluster-constructed strong-coupling
measure is site-reflection positive through every integer coordinate plane,
with no hypothesis on the chosen exterior sequence. -/
theorem centeredInfiniteVolume_siteReflectionPositive
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ) :
    SiteReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k := by
  let oneExterior : ℕ → Configuration d G := fun _ => 1
  have hzeroOne : SiteReflectionPositive
      (centeredInfiniteVolumeMeasure oneExterior Φ β hβ) τ 0 := by
    apply centeredInfiniteVolume_siteReflectionPositive_of_eventually
    exact Filter.Eventually.of_forall fun n =>
      centeredGibbsSequence_one_siteReflectionPositive Φ β n τ
  have hzero := centeredInfiniteVolume_siteReflectionPositive_boundary_independent
    oneExterior η Φ β hβ τ 0 hzeroOne
  exact centeredInfiniteVolume_siteReflectionPositive_all_planes
    η Φ β hβ τ hzero k

/-- Strong-coupling infinite-volume Cauchy--Schwarz for every integer
coordinate reflection plane and arbitrary exterior sequence. -/
theorem centeredInfiniteVolume_siteReflectionCauchySchwarz
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ) :
    SiteReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k := by
  let oneExterior : ℕ → Configuration d G := fun _ => 1
  have hzeroOne : SiteReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure oneExterior Φ β hβ) τ 0 := by
    apply centeredInfiniteVolume_siteReflectionCauchySchwarz_of_eventually
    exact Filter.Eventually.of_forall fun n =>
      centeredGibbsSequence_one_siteReflectionCauchySchwarz Φ β n τ
  have hzero :=
    centeredInfiniteVolume_siteReflectionCauchySchwarz_boundary_independent
      oneExterior η Φ β hβ τ 0 hzeroOne
  exact centeredInfiniteVolume_siteReflectionCauchySchwarz_all_planes
    η Φ β hβ τ hzero k

end

end YangMills.StrongCoupling
