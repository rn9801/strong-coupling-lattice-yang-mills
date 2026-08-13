/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.InfiniteVolumeReflectionPositivity
import YangMills.StrongCoupling.SymmetricReflectionBoxes

/-!
# Milestone 19 regression: the infinite-volume limit passage

These checks exercise the infinite-lattice reflection involutions, the two
positive-algebra predicates, closedness of reflection positivity under local
expectation limits, boundary independence, and translation from the basic
planes to all parallel planes.
-/

open Filter MeasureTheory
open YangMills.Gauge YangMills.Lattice.Cubic
open YangMills.StrongCoupling

namespace YangMills.Tests.Milestone19

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- The constant observable belongs to every integer positive algebra. -/
example (τ : Fin d) (k : ℤ) (z : ℂ) :
    (LocalObservable.const (d := d) (G := G) z).SupportedInSitePositiveHalf τ k := by
  intro e he
  simp [LocalObservable.const] at he

/-- The constant observable belongs to every half-integer positive algebra. -/
example (τ : Fin d) (k : ℤ) (z : ℂ) :
    (LocalObservable.const (d := d) (G := G) z).SupportedInLinkPositiveHalf τ k := by
  intro e he
  simp [LocalObservable.const] at he

/-- Integer reflection is genuinely an involution on local values. -/
example (τ : Fin d) (k : ℤ) (F : LocalObservable d G)
    (A : Configuration d G) :
    (F.siteTheta τ k).siteTheta τ k A = F A := by
  simp

/-- The centered exhaustion is genuinely symmetric about the basic site
plane, not merely cofinal. -/
example (τ : Fin d) (n : ℕ) (x : Site d) :
    siteReflection τ 0 x ∈ (centeredBox d n).sites ↔
      x ∈ (centeredBox d n).sites :=
  siteReflection_mem_centeredBox_iff τ x

/-- The shifted exhaustion is genuinely symmetric about the basic link
plane. -/
example (τ : Fin d) (n : ℕ) (x : Site d) :
    linkReflection τ 0 x ∈ (linkSymmetricBox d n τ).sites ↔
      x ∈ (linkSymmetricBox d n τ).sites :=
  linkReflection_mem_linkSymmetricBox_iff τ x

/-- Link-symmetric boxes still exhaust every finite observable support. -/
example (τ : Fin d) (S : Finset (PositiveEdge d)) :
    ∃ n, S ⊆ (linkSymmetricBox d n τ).positiveEdges :=
  finiteSupport_subset_linkSymmetricBox τ S

/-- Half-integer reflection is genuinely an involution on local values. -/
example (τ : Fin d) (k : ℤ) (F : LocalObservable d G)
    (A : Configuration d G) :
    (F.linkTheta τ k).linkTheta τ k A = F A := by
  simp

/-- The abstract site limit-passage theorem has exactly the advertised
closed-condition interface. -/
example (μn : ℕ → ProbabilityMeasure (Configuration d G))
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ)
    (hlim : ∀ O : LocalObservable d G,
      Tendsto (fun n => localExpectation (μn n) O) atTop
        (nhds (∫ A, O A ∂μ)))
    (hfinite : ∀ᶠ n in atTop,
      SiteReflectionPositive (μn n : Measure (Configuration d G)) τ k) :
    SiteReflectionPositive μ τ k :=
  siteReflectionPositive_of_localExpectation_tendsto μn μ τ k hlim hfinite

/-- The abstract link limit passage retains gauge invariance. -/
example (μn : ℕ → ProbabilityMeasure (Configuration d G))
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ)
    (hlim : ∀ O : LocalObservable d G,
      Tendsto (fun n => localExpectation (μn n) O) atTop
        (nhds (∫ A, O A ∂μ)))
    (hfinite : ∀ᶠ n in atTop,
      LinkReflectionPositive (μn n : Measure (Configuration d G)) τ k) :
    LinkReflectionPositive μ τ k :=
  linkReflectionPositive_of_localExpectation_tendsto μn μ τ k hlim hfinite

/-- The cluster-constructed limit theorem consumes eventual finite site
positivity of centered approximants and no Dobrushin hypothesis. -/
example (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ)
    (hfinite : ∀ᶠ n in atTop,
      SiteReflectionPositive
        (centeredGibbsSequence η Φ β n : Measure (Configuration d G)) τ k) :
    SiteReflectionPositive (centeredInfiniteVolumeMeasure η Φ β hβ) τ k :=
  centeredInfiniteVolume_siteReflectionPositive_of_eventually
    η Φ β hβ τ k hfinite

/-- The link analogue has the same cluster-expansion limit interface. -/
example (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ)
    (hfinite : ∀ᶠ n in atTop,
      LinkReflectionPositive
        (centeredGibbsSequence η Φ β n : Measure (Configuration d G)) τ k) :
    LinkReflectionPositive (centeredInfiniteVolumeMeasure η Φ β hβ) τ k :=
  centeredInfiniteVolume_linkReflectionPositive_of_eventually
    η Φ β hβ τ k hfinite

/-- Translation invariance carries site positivity at zero to an arbitrary
integer plane. -/
example (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d)
    (hzero : SiteReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ 0) (k : ℤ) :
    SiteReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k :=
  centeredInfiniteVolume_siteReflectionPositive_all_planes
    η Φ β hβ τ hzero k

/-- Translation invariance carries link positivity at one half to an
arbitrary parallel half-integer plane. -/
example (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d)
    (hhalf : LinkReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ 0) (k : ℤ) :
    LinkReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k :=
  centeredInfiniteVolume_linkReflectionPositive_all_planes
    η Φ β hβ τ hhalf k

#print axioms Gauge.LocalObservable.siteTheta_siteTheta_apply
#print axioms Gauge.LocalObservable.linkTheta_linkTheta_apply
#print axioms siteReflectionPositive_of_localExpectation_tendsto
#print axioms linkReflectionPositive_of_localExpectation_tendsto
#print axioms centeredInfiniteVolume_siteReflectionPositive_of_eventually
#print axioms centeredInfiniteVolume_linkReflectionPositive_of_eventually
#print axioms centeredInfiniteVolume_siteReflectionPositive_all_planes
#print axioms centeredInfiniteVolume_linkReflectionPositive_all_planes

end

end YangMills.Tests.Milestone19
