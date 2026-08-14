/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.InfiniteReflection
import YangMills.StrongCoupling.CenteredInfiniteVolume
import YangMills.StrongCoupling.SymmetricReflectionBoxes

/-!
# Reflection positivity and local-state limits

Reflection positivity is a closed condition on local expectations.  This file
formalizes that fact and applies the cluster-expansion convergence theorem to
the centered strong-coupling measure.  The resulting transfer theorems take
an eventual finite-volume reflection-positivity statement as their only
geometric input.

That input is intentionally explicit.  The site-reflection hypothesis is
discharged for concrete centered cubic specifications in
`ConcreteSiteReflectionPositivity`; the link-reflection bridge remains
separate.  No Dobrushin or Douglas infinite-volume theorem is used here.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Reflection positivity of a measure through the integer plane `x τ = k`,
tested on the full local positive algebra. -/
def SiteReflectionPositive
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ) : Prop :=
  ∀ F : LocalObservable d G, F.SupportedInSitePositiveHalf τ k →
    Complex.im (∫ A, F.siteReflectionProduct τ k F A ∂μ) = 0 ∧
      0 ≤ Complex.re (∫ A, F.siteReflectionProduct τ k F A ∂μ)

/-- The site-reflection pairing of two local observables. -/
def siteReflectionPairing
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) : ℂ :=
  ∫ A, F.siteReflectionProduct τ k H A ∂μ

/-- Cauchy--Schwarz for the site-reflection pairing on the full positive local
algebra. -/
def SiteReflectionCauchySchwarz
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ) : Prop :=
  ∀ F H : LocalObservable d G,
    F.SupportedInSitePositiveHalf τ k →
    H.SupportedInSitePositiveHalf τ k →
    Complex.normSq (siteReflectionPairing μ τ k F H) ≤
      Complex.re (siteReflectionPairing μ τ k F F) *
        Complex.re (siteReflectionPairing μ τ k H H)

/-- Reflection positivity through `x τ = k + 1/2`, restricted to the
gauge-invariant local positive algebra required by link reflection. -/
def LinkReflectionPositive
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ) : Prop :=
  ∀ F : LocalObservable d G, F.SupportedInLinkPositiveHalf τ k →
    Gauge.IsGaugeInvariant F →
    Complex.im (∫ A, F.linkReflectionProduct τ k F A ∂μ) = 0 ∧
      0 ≤ Complex.re (∫ A, F.linkReflectionProduct τ k F A ∂μ)

/-- The half-integer/link-reflection pairing of two local observables. -/
def linkReflectionPairing
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) : ℂ :=
  ∫ A, F.linkReflectionProduct τ k H A ∂μ

/-- Cauchy--Schwarz for the half-integer reflection pairing on the
gauge-invariant positive local algebra. -/
def LinkReflectionCauchySchwarz
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ) : Prop :=
  ∀ F H : LocalObservable d G,
    F.SupportedInLinkPositiveHalf τ k →
    H.SupportedInLinkPositiveHalf τ k →
    Gauge.IsGaugeInvariant F → Gauge.IsGaugeInvariant H →
    Complex.normSq (linkReflectionPairing μ τ k F H) ≤
      Complex.re (linkReflectionPairing μ τ k F F) *
        Complex.re (linkReflectionPairing μ τ k H H)

omit [CompactSpace G] [T2Space G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Finite-volume site reflection positivity is preserved by any local-state
limit.  Only convergence of local observables is used. -/
theorem siteReflectionPositive_of_localExpectation_tendsto
    (μn : ℕ → ProbabilityMeasure (Configuration d G))
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ)
    (hlim : ∀ O : LocalObservable d G,
      Tendsto (fun n => localExpectation (μn n) O) atTop
        (nhds (∫ A, O A ∂μ)))
    (hfinite : ∀ᶠ n in atTop,
      SiteReflectionPositive (μn n : Measure (Configuration d G)) τ k) :
    SiteReflectionPositive μ τ k := by
  intro F hF
  let O := F.siteReflectionProduct τ k F
  have hO := hlim O
  have hre : Tendsto (fun n => Complex.re (localExpectation (μn n) O))
      atTop (nhds (Complex.re (∫ A, O A ∂μ))) :=
    Complex.continuous_re.continuousAt.tendsto.comp hO
  have him : Tendsto (fun n => Complex.im (localExpectation (μn n) O))
      atTop (nhds (Complex.im (∫ A, O A ∂μ))) :=
    Complex.continuous_im.continuousAt.tendsto.comp hO
  have himZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have heventIm : (fun n => Complex.im (localExpectation (μn n) O)) =ᶠ[atTop]
      fun _ => (0 : ℝ) := by
    filter_upwards [hfinite] with n hn
    exact (hn F hF).1
  have him' : Tendsto (fun n => Complex.im (localExpectation (μn n) O))
      atTop (nhds 0) := himZero.congr' heventIm.symm
  constructor
  · exact tendsto_nhds_unique him him'
  · exact isClosed_Ici.mem_of_tendsto hre <|
      hfinite.mono fun n hn => hn F hF |>.2

omit [CompactSpace G] [T2Space G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- Site-reflection Cauchy--Schwarz is closed under convergence of all local
expectations. -/
theorem siteReflectionCauchySchwarz_of_localExpectation_tendsto
    (μn : ℕ → ProbabilityMeasure (Configuration d G))
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ)
    (hlim : ∀ O : LocalObservable d G,
      Tendsto (fun n => localExpectation (μn n) O) atTop
        (nhds (∫ A, O A ∂μ)))
    (hfinite : ∀ᶠ n in atTop,
      SiteReflectionCauchySchwarz
        (μn n : Measure (Configuration d G)) τ k) :
    SiteReflectionCauchySchwarz μ τ k := by
  intro F H hF hH
  let OFH := F.siteReflectionProduct τ k H
  let OFF := F.siteReflectionProduct τ k F
  let OHH := H.siteReflectionProduct τ k H
  have hFH := hlim OFH
  have hFF := hlim OFF
  have hHH := hlim OHH
  have hlhs : Tendsto
      (fun n => Complex.normSq (localExpectation (μn n) OFH)) atTop
      (nhds (Complex.normSq (∫ A, OFH A ∂μ))) :=
    Complex.continuous_normSq.continuousAt.tendsto.comp hFH
  have hrhs : Tendsto
      (fun n => Complex.re (localExpectation (μn n) OFF) *
        Complex.re (localExpectation (μn n) OHH)) atTop
      (nhds (Complex.re (∫ A, OFF A ∂μ) *
        Complex.re (∫ A, OHH A ∂μ))) :=
    (Complex.continuous_re.continuousAt.tendsto.comp hFF).mul
      (Complex.continuous_re.continuousAt.tendsto.comp hHH)
  exact le_of_tendsto_of_tendsto hlhs hrhs <|
    hfinite.mono fun n hn => hn F H hF hH

omit [CompactSpace G] [T2Space G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Finite-volume link reflection positivity is preserved by any local-state
limit, with the gauge-invariance hypothesis unchanged. -/
theorem linkReflectionPositive_of_localExpectation_tendsto
    (μn : ℕ → ProbabilityMeasure (Configuration d G))
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ)
    (hlim : ∀ O : LocalObservable d G,
      Tendsto (fun n => localExpectation (μn n) O) atTop
        (nhds (∫ A, O A ∂μ)))
    (hfinite : ∀ᶠ n in atTop,
      LinkReflectionPositive (μn n : Measure (Configuration d G)) τ k) :
    LinkReflectionPositive μ τ k := by
  intro F hF hGauge
  let O := F.linkReflectionProduct τ k F
  have hO := hlim O
  have hre : Tendsto (fun n => Complex.re (localExpectation (μn n) O))
      atTop (nhds (Complex.re (∫ A, O A ∂μ))) :=
    Complex.continuous_re.continuousAt.tendsto.comp hO
  have him : Tendsto (fun n => Complex.im (localExpectation (μn n) O))
      atTop (nhds (Complex.im (∫ A, O A ∂μ))) :=
    Complex.continuous_im.continuousAt.tendsto.comp hO
  have himZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have heventIm : (fun n => Complex.im (localExpectation (μn n) O)) =ᶠ[atTop]
      fun _ => (0 : ℝ) := by
    filter_upwards [hfinite] with n hn
    exact (hn F hF hGauge).1
  have him' : Tendsto (fun n => Complex.im (localExpectation (μn n) O))
      atTop (nhds 0) := himZero.congr' heventIm.symm
  constructor
  · exact tendsto_nhds_unique him him'
  · exact isClosed_Ici.mem_of_tendsto hre <|
      hfinite.mono fun n hn => hn F hF hGauge |>.2

omit [CompactSpace G] [T2Space G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Link-reflection Cauchy--Schwarz is closed under convergence of all local
expectations. -/
theorem linkReflectionCauchySchwarz_of_localExpectation_tendsto
    (μn : ℕ → ProbabilityMeasure (Configuration d G))
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ)
    (hlim : ∀ O : LocalObservable d G,
      Tendsto (fun n => localExpectation (μn n) O) atTop
        (nhds (∫ A, O A ∂μ)))
    (hfinite : ∀ᶠ n in atTop,
      LinkReflectionCauchySchwarz
        (μn n : Measure (Configuration d G)) τ k) :
    LinkReflectionCauchySchwarz μ τ k := by
  intro F H hF hH hGaugeF hGaugeH
  let OFH := F.linkReflectionProduct τ k H
  let OFF := F.linkReflectionProduct τ k F
  let OHH := H.linkReflectionProduct τ k H
  have hFH := hlim OFH
  have hFF := hlim OFF
  have hHH := hlim OHH
  have hlhs : Tendsto
      (fun n => Complex.normSq (localExpectation (μn n) OFH)) atTop
      (nhds (Complex.normSq (∫ A, OFH A ∂μ))) :=
    Complex.continuous_normSq.continuousAt.tendsto.comp hFH
  have hrhs : Tendsto
      (fun n => Complex.re (localExpectation (μn n) OFF) *
        Complex.re (localExpectation (μn n) OHH)) atTop
      (nhds (Complex.re (∫ A, OFF A ∂μ) *
        Complex.re (∫ A, OHH A ∂μ))) :=
    (Complex.continuous_re.continuousAt.tendsto.comp hFF).mul
      (Complex.continuous_re.continuousAt.tendsto.comp hHH)
  exact le_of_tendsto_of_tendsto hlhs hrhs <|
    hfinite.mono fun n hn => hn F H hF hH hGaugeF hGaugeH

/-- Cluster-expansion passage from eventual centered finite-volume site
reflection positivity to the constructed infinite-volume measure. -/
theorem centeredInfiniteVolume_siteReflectionPositive_of_eventually
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ)
    (hfinite : ∀ᶠ n in atTop,
      SiteReflectionPositive
        (centeredGibbsSequence η Φ β n : Measure (Configuration d G)) τ k) :
    SiteReflectionPositive (centeredInfiniteVolumeMeasure η Φ β hβ) τ k := by
  exact siteReflectionPositive_of_localExpectation_tendsto
    (centeredGibbsSequence η Φ β)
    (centeredInfiniteVolumeMeasure η Φ β hβ) τ k
    (tendsto_centered_localExpectation_infiniteVolume η Φ β hβ) hfinite

/-- Cluster-expansion passage of site-reflection Cauchy--Schwarz to the
constructed infinite-volume measure. -/
theorem centeredInfiniteVolume_siteReflectionCauchySchwarz_of_eventually
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ)
    (hfinite : ∀ᶠ n in atTop,
      SiteReflectionCauchySchwarz
        (centeredGibbsSequence η Φ β n : Measure (Configuration d G)) τ k) :
    SiteReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k := by
  exact siteReflectionCauchySchwarz_of_localExpectation_tendsto
    (centeredGibbsSequence η Φ β)
    (centeredInfiniteVolumeMeasure η Φ β hβ) τ k
    (tendsto_centered_localExpectation_infiniteVolume η Φ β hβ) hfinite

/-- Cluster-expansion passage from eventual centered finite-volume link
reflection positivity to the constructed infinite-volume measure. -/
theorem centeredInfiniteVolume_linkReflectionPositive_of_eventually
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ)
    (hfinite : ∀ᶠ n in atTop,
      LinkReflectionPositive
        (centeredGibbsSequence η Φ β n : Measure (Configuration d G)) τ k) :
    LinkReflectionPositive (centeredInfiniteVolumeMeasure η Φ β hβ) τ k := by
  exact linkReflectionPositive_of_localExpectation_tendsto
    (centeredGibbsSequence η Φ β)
    (centeredInfiniteVolumeMeasure η Φ β hβ) τ k
    (tendsto_centered_localExpectation_infiniteVolume η Φ β hβ) hfinite

/-- Cluster-expansion passage of link-reflection Cauchy--Schwarz to the
constructed infinite-volume measure. -/
theorem centeredInfiniteVolume_linkReflectionCauchySchwarz_of_eventually
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ)
    (hfinite : ∀ᶠ n in atTop,
      LinkReflectionCauchySchwarz
        (centeredGibbsSequence η Φ β n : Measure (Configuration d G)) τ k) :
    LinkReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k := by
  exact linkReflectionCauchySchwarz_of_localExpectation_tendsto
    (centeredGibbsSequence η Φ β)
    (centeredInfiniteVolumeMeasure η Φ β hβ) τ k
    (tendsto_centered_localExpectation_infiniteVolume η Φ β hβ) hfinite

/-- Site reflection positivity is independent of the exterior sequence used
to construct the centered strong-coupling measure. -/
theorem centeredInfiniteVolume_siteReflectionPositive_boundary_independent
    (η η' : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ)
    (h : SiteReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k) :
    SiteReflectionPositive
      (centeredInfiniteVolumeMeasure η' Φ β hβ) τ k := by
  rw [centeredInfiniteVolumeMeasure_boundary_independent η' η Φ β hβ]
  exact h

/-- Site-reflection Cauchy--Schwarz is independent of the exterior sequence. -/
theorem centeredInfiniteVolume_siteReflectionCauchySchwarz_boundary_independent
    (η η' : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ)
    (h : SiteReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k) :
    SiteReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η' Φ β hβ) τ k := by
  rw [centeredInfiniteVolumeMeasure_boundary_independent η' η Φ β hβ]
  exact h

/-- Link reflection positivity is independent of the exterior sequence used
to construct the centered strong-coupling measure. -/
theorem centeredInfiniteVolume_linkReflectionPositive_boundary_independent
    (η η' : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ)
    (h : LinkReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k) :
    LinkReflectionPositive
      (centeredInfiniteVolumeMeasure η' Φ β hβ) τ k := by
  rw [centeredInfiniteVolumeMeasure_boundary_independent η' η Φ β hβ]
  exact h

/-- Link-reflection Cauchy--Schwarz is independent of the exterior sequence. -/
theorem centeredInfiniteVolume_linkReflectionCauchySchwarz_boundary_independent
    (η η' : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ)
    (h : LinkReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k) :
    LinkReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η' Φ β hβ) τ k := by
  rw [centeredInfiniteVolumeMeasure_boundary_independent η' η Φ β hβ]
  exact h

/-- Translation invariance transfers integer reflection positivity from the
origin plane to every parallel integer plane. -/
theorem centeredInfiniteVolume_siteReflectionPositive_all_planes
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d)
    (hzero : SiteReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ 0) :
    ∀ k : ℤ, SiteReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k := by
  intro k F hF
  let v := axisTranslation τ (-k)
  let Ft := F.translatePullback v
  have hFt : Ft.SupportedInSitePositiveHalf τ 0 := by
    intro e he
    simp only [Ft, LocalObservable.translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hF a ha
    change 0 ≤ Lattice.Cubic.translate v a.source τ
    simp [Lattice.Cubic.translate, v, axisTranslation]
    omega
  have hpos := hzero Ft hFt
  have htranslate := centeredInfiniteVolume_integral_translatePullback
    η Φ β hβ v (F.siteReflectionProduct τ k F)
  have hintegrand : ∀ A : Configuration d G,
      (F.siteReflectionProduct τ k F).translatePullback v A =
        Ft.siteReflectionProduct τ 0 Ft A := by
    intro A
    change star (F (siteReflectConfiguration τ k
        (LocalObservable.translateConfiguration v A))) *
          F (LocalObservable.translateConfiguration v A) =
      star (F (LocalObservable.translateConfiguration v
        (siteReflectConfiguration τ 0 A))) *
          F (LocalObservable.translateConfiguration v A)
    rw [translateConfiguration_siteReflect_axis_neg]
  have heq :
      ∫ A, F.siteReflectionProduct τ k F A
          ∂centeredInfiniteVolumeMeasure η Φ β hβ =
        ∫ A, Ft.siteReflectionProduct τ 0 Ft A
          ∂centeredInfiniteVolumeMeasure η Φ β hβ := by
    rw [← htranslate]
    apply integral_congr_ae
    exact ae_of_all _ hintegrand
  rw [heq]
  exact hpos

/-- Translation invariance transfers site-reflection Cauchy--Schwarz from the
origin plane to every parallel integer plane. -/
theorem centeredInfiniteVolume_siteReflectionCauchySchwarz_all_planes
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d)
    (hzero : SiteReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ 0) :
    ∀ k : ℤ, SiteReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k := by
  intro k F H hF hH
  let v := axisTranslation τ (-k)
  let Ft := F.translatePullback v
  let Ht := H.translatePullback v
  have translateSupport (K : LocalObservable d G)
      (hK : K.SupportedInSitePositiveHalf τ k) :
      (K.translatePullback v).SupportedInSitePositiveHalf τ 0 := by
    intro e he
    simp only [LocalObservable.translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hK a ha
    change 0 ≤ Lattice.Cubic.translate v a.source τ
    simp [Lattice.Cubic.translate, v, axisTranslation]
    omega
  have hFt := translateSupport F hF
  have hHt := translateSupport H hH
  have hCS := hzero Ft Ht hFt hHt
  have pairing_translate (K L : LocalObservable d G) :
      siteReflectionPairing
          (centeredInfiniteVolumeMeasure η Φ β hβ) τ k K L =
        siteReflectionPairing
          (centeredInfiniteVolumeMeasure η Φ β hβ) τ 0
            (K.translatePullback v) (L.translatePullback v) := by
    have htranslate := centeredInfiniteVolume_integral_translatePullback
      η Φ β hβ v (K.siteReflectionProduct τ k L)
    rw [siteReflectionPairing, siteReflectionPairing, ← htranslate]
    apply integral_congr_ae
    exact ae_of_all _ fun A => by
      change star (K (siteReflectConfiguration τ k
          (LocalObservable.translateConfiguration v A))) *
            L (LocalObservable.translateConfiguration v A) =
        star (K (LocalObservable.translateConfiguration v
          (siteReflectConfiguration τ 0 A))) *
            L (LocalObservable.translateConfiguration v A)
      rw [translateConfiguration_siteReflect_axis_neg]
  rw [pairing_translate F H, pairing_translate F F, pairing_translate H H]
  exact hCS

/-- Translation invariance transfers half-integer reflection positivity from
the plane at `1/2` to every parallel half-integer plane. -/
theorem centeredInfiniteVolume_linkReflectionPositive_all_planes
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d)
    (hhalf : LinkReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ 0) :
    ∀ k : ℤ, LinkReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k := by
  intro k F hF hGauge
  let v := axisTranslation τ (-k)
  let Ft := F.translatePullback v
  have hFt : Ft.SupportedInLinkPositiveHalf τ 0 := by
    intro e he
    simp only [Ft, LocalObservable.translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hF a ha
    rw [PositiveEdge.target_translate]
    simp [Lattice.Cubic.translate, v, axisTranslation]
    omega
  have hGaugeFt : Gauge.IsGaugeInvariant Ft :=
    LocalObservable.IsGaugeInvariant.translatePullback hGauge v
  have hpos := hhalf Ft hFt hGaugeFt
  have htranslate := centeredInfiniteVolume_integral_translatePullback
    η Φ β hβ v (F.linkReflectionProduct τ k F)
  have hintegrand : ∀ A : Configuration d G,
      (F.linkReflectionProduct τ k F).translatePullback v A =
        Ft.linkReflectionProduct τ 0 Ft A := by
    intro A
    change star (F (linkReflectConfiguration τ k
        (LocalObservable.translateConfiguration v A))) *
          F (LocalObservable.translateConfiguration v A) =
      star (F (LocalObservable.translateConfiguration v
        (linkReflectConfiguration τ 0 A))) *
          F (LocalObservable.translateConfiguration v A)
    rw [translateConfiguration_linkReflect_axis_neg]
  have heq :
      ∫ A, F.linkReflectionProduct τ k F A
          ∂centeredInfiniteVolumeMeasure η Φ β hβ =
        ∫ A, Ft.linkReflectionProduct τ 0 Ft A
          ∂centeredInfiniteVolumeMeasure η Φ β hβ := by
    rw [← htranslate]
    apply integral_congr_ae
    exact ae_of_all _ hintegrand
  rw [heq]
  exact hpos

/-- Translation invariance transfers link-reflection Cauchy--Schwarz from
the plane at `1/2` to every parallel half-integer plane. -/
theorem centeredInfiniteVolume_linkReflectionCauchySchwarz_all_planes
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d)
    (hhalf : LinkReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ 0) :
    ∀ k : ℤ, LinkReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k := by
  intro k F H hF hH hGaugeF hGaugeH
  let v := axisTranslation τ (-k)
  let Ft := F.translatePullback v
  let Ht := H.translatePullback v
  have translateSupport (K : LocalObservable d G)
      (hK : K.SupportedInLinkPositiveHalf τ k) :
      (K.translatePullback v).SupportedInLinkPositiveHalf τ 0 := by
    intro e he
    simp only [LocalObservable.translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hK a ha
    rw [PositiveEdge.target_translate]
    simp [Lattice.Cubic.translate, v, axisTranslation]
    omega
  have hFt := translateSupport F hF
  have hHt := translateSupport H hH
  have hGaugeFt : Gauge.IsGaugeInvariant Ft :=
    LocalObservable.IsGaugeInvariant.translatePullback hGaugeF v
  have hGaugeHt : Gauge.IsGaugeInvariant Ht :=
    LocalObservable.IsGaugeInvariant.translatePullback hGaugeH v
  have hCS := hhalf Ft Ht hFt hHt hGaugeFt hGaugeHt
  have pairing_translate (K L : LocalObservable d G) :
      linkReflectionPairing
          (centeredInfiniteVolumeMeasure η Φ β hβ) τ k K L =
        linkReflectionPairing
          (centeredInfiniteVolumeMeasure η Φ β hβ) τ 0
            (K.translatePullback v) (L.translatePullback v) := by
    have htranslate := centeredInfiniteVolume_integral_translatePullback
      η Φ β hβ v (K.linkReflectionProduct τ k L)
    rw [linkReflectionPairing, linkReflectionPairing, ← htranslate]
    apply integral_congr_ae
    exact ae_of_all _ fun A => by
      change star (K (linkReflectConfiguration τ k
          (LocalObservable.translateConfiguration v A))) *
            L (LocalObservable.translateConfiguration v A) =
        star (K (LocalObservable.translateConfiguration v
          (linkReflectConfiguration τ 0 A))) *
            L (LocalObservable.translateConfiguration v A)
      rw [translateConfiguration_linkReflect_axis_neg]
  rw [pairing_translate F H, pairing_translate F F, pairing_translate H H]
  exact hCS

end

end YangMills.StrongCoupling
