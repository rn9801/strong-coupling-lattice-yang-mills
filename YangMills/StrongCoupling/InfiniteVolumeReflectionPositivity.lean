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

That input is intentionally explicit.  The finite reflection files presently
work with fixed labelled-variable normal forms; identifying a cofinal family
of symmetric cubic specifications with those normal forms is the remaining
finite geometric bridge.  No Dobrushin or Douglas infinite-volume theorem is
used here.
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

/-- Reflection positivity through `x τ = k + 1/2`, restricted to the
gauge-invariant local positive algebra required by link reflection. -/
def LinkReflectionPositive
    (μ : Measure (Configuration d G)) (τ : Fin d) (k : ℤ) : Prop :=
  ∀ F : LocalObservable d G, F.SupportedInLinkPositiveHalf τ k →
    Gauge.IsGaugeInvariant F →
    Complex.im (∫ A, F.linkReflectionProduct τ k F A ∂μ) = 0 ∧
      0 ≤ Complex.re (∫ A, F.linkReflectionProduct τ k F A ∂μ)

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
    simp only [Ft, translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hF a ha
    change 0 ≤ Lattice.Cubic.translate v a.source τ
    simp only [Lattice.Cubic.translate, v, axisTranslation_apply_eq]
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
    simp only [Ft, translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hF a ha
    change 0 < Lattice.Cubic.translate v a.target τ
    simp only [Lattice.Cubic.translate, v, axisTranslation_apply_eq]
    omega
  have hGaugeFt : Gauge.IsGaugeInvariant Ft := hGauge.translatePullback v
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

end

end YangMills.StrongCoupling
