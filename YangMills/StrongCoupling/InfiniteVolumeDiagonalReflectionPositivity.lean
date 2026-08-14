/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.DiagonalReflectionPositivity
import YangMills.StrongCoupling.CenteredInfiniteVolume

/-!
# Infinite-volume diagonal reflection positivity

Diagonal reflection positivity and its Cauchy--Schwarz inequality are closed
conditions on local expectations.  The specializations below therefore pass
them from reflection-symmetric finite approximants to the unique
strong-coupling measure using the KP cluster-expansion convergence theorem.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Reflection positivity through the affine diagonal plane
`x τ - x σ = k`, tested on the full positive local algebra. -/
def DiagonalReflectionPositive
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ) : Prop :=
  τ ≠ σ → ∀ F : LocalObservable d G,
    F.SupportedInDiagonalPositiveHalf τ σ k →
    Complex.im (∫ A, F.diagonalReflectionProduct τ σ k F A ∂μ) = 0 ∧
      0 ≤ Complex.re (∫ A, F.diagonalReflectionProduct τ σ k F A ∂μ)

/-- The unnormalized diagonal reflection pairing of two local observables. -/
def diagonalReflectionPairing
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) : ℂ :=
  ∫ A, F.diagonalReflectionProduct τ σ k H A ∂μ

/-- Cauchy--Schwarz for the diagonal reflection pairing on the full positive
local algebra. -/
def DiagonalReflectionCauchySchwarz
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ) : Prop :=
  τ ≠ σ → ∀ F H : LocalObservable d G,
    F.SupportedInDiagonalPositiveHalf τ σ k →
    H.SupportedInDiagonalPositiveHalf τ σ k →
    Complex.normSq (diagonalReflectionPairing μ τ σ k F H) ≤
      Complex.re (diagonalReflectionPairing μ τ σ k F F) *
        Complex.re (diagonalReflectionPairing μ τ σ k H H)

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Finite-volume diagonal reflection positivity is preserved by convergence
of all local expectations. -/
theorem diagonalReflectionPositive_of_localExpectation_tendsto
    (μn : ℕ → ProbabilityMeasure (Configuration d G))
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ)
    (hlim : ∀ O : LocalObservable d G,
      Tendsto (fun n => localExpectation (μn n) O) atTop
        (nhds (∫ A, O A ∂μ)))
    (hfinite : ∀ᶠ n in atTop,
      DiagonalReflectionPositive (μn n : Measure (Configuration d G)) τ σ k) :
    DiagonalReflectionPositive μ τ σ k := by
  intro hτσ F hF
  let O := F.diagonalReflectionProduct τ σ k F
  have hO := hlim O
  have hre : Tendsto (fun n => Complex.re (localExpectation (μn n) O))
      atTop (nhds (Complex.re (∫ A, O A ∂μ))) :=
    Complex.continuous_re.continuousAt.tendsto.comp hO
  have him : Tendsto (fun n => Complex.im (localExpectation (μn n) O))
      atTop (nhds (Complex.im (∫ A, O A ∂μ))) :=
    Complex.continuous_im.continuousAt.tendsto.comp hO
  have heventIm : (fun n => Complex.im (localExpectation (μn n) O)) =ᶠ[atTop]
      fun _ => (0 : ℝ) := by
    filter_upwards [hfinite] with n hn
    exact (hn hτσ F hF).1
  constructor
  · exact tendsto_nhds_unique him
      (tendsto_const_nhds.congr' heventIm.symm)
  · exact isClosed_Ici.mem_of_tendsto hre <|
      hfinite.mono fun n hn => (hn hτσ F hF).2

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Cauchy--Schwarz for finite diagonal pairings is preserved by convergence
of all local expectations. -/
theorem diagonalReflectionCauchySchwarz_of_localExpectation_tendsto
    (μn : ℕ → ProbabilityMeasure (Configuration d G))
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ)
    (hlim : ∀ O : LocalObservable d G,
      Tendsto (fun n => localExpectation (μn n) O) atTop
        (nhds (∫ A, O A ∂μ)))
    (hfinite : ∀ᶠ n in atTop,
      DiagonalReflectionCauchySchwarz
        (μn n : Measure (Configuration d G)) τ σ k) :
    DiagonalReflectionCauchySchwarz μ τ σ k := by
  intro hτσ F H hF hH
  let OFH := F.diagonalReflectionProduct τ σ k H
  let OFF := F.diagonalReflectionProduct τ σ k F
  let OHH := H.diagonalReflectionProduct τ σ k H
  have hFH := hlim OFH
  have hFF := hlim OFF
  have hHH := hlim OHH
  let lhs : ℕ → ℝ := fun n => Complex.normSq (localExpectation (μn n) OFH)
  let rhs : ℕ → ℝ := fun n =>
    Complex.re (localExpectation (μn n) OFF) *
      Complex.re (localExpectation (μn n) OHH)
  have hlhs : Tendsto lhs atTop
      (nhds (Complex.normSq (∫ A, OFH A ∂μ))) :=
    Complex.continuous_normSq.continuousAt.tendsto.comp hFH
  have hrhs : Tendsto rhs atTop
      (nhds (Complex.re (∫ A, OFF A ∂μ) *
        Complex.re (∫ A, OHH A ∂μ))) :=
    ((Complex.continuous_re.continuousAt.tendsto.comp hFF).mul
      (Complex.continuous_re.continuousAt.tendsto.comp hHH))
  exact le_of_tendsto_of_tendsto hlhs hrhs <|
    hfinite.mono fun n hn => hn hτσ F H hF hH

/-- Cluster-expansion passage from eventual centered finite-volume diagonal
reflection positivity to the constructed infinite-volume measure. -/
theorem centeredInfiniteVolume_diagonalReflectionPositive_of_eventually
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ σ : Fin d) (k : ℤ)
    (hfinite : ∀ᶠ n in atTop,
      DiagonalReflectionPositive
        (centeredGibbsSequence η Φ β n : Measure (Configuration d G)) τ σ k) :
    DiagonalReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k := by
  exact diagonalReflectionPositive_of_localExpectation_tendsto
    (centeredGibbsSequence η Φ β)
    (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k
    (tendsto_centered_localExpectation_infiniteVolume η Φ β hβ) hfinite

/-- Cluster-expansion passage of diagonal reflection Cauchy--Schwarz to the
constructed infinite-volume measure. -/
theorem centeredInfiniteVolume_diagonalReflectionCauchySchwarz_of_eventually
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ σ : Fin d) (k : ℤ)
    (hfinite : ∀ᶠ n in atTop,
      DiagonalReflectionCauchySchwarz
        (centeredGibbsSequence η Φ β n : Measure (Configuration d G)) τ σ k) :
    DiagonalReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k := by
  exact diagonalReflectionCauchySchwarz_of_localExpectation_tendsto
    (centeredGibbsSequence η Φ β)
    (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k
    (tendsto_centered_localExpectation_infiniteVolume η Φ β hβ) hfinite

/-- Diagonal reflection positivity is independent of the exterior sequence
used to construct the centered strong-coupling measure. -/
theorem centeredInfiniteVolume_diagonalReflectionPositive_boundary_independent
    (η η' : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ σ : Fin d) (k : ℤ)
    (h : DiagonalReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k) :
    DiagonalReflectionPositive
      (centeredInfiniteVolumeMeasure η' Φ β hβ) τ σ k := by
  rw [centeredInfiniteVolumeMeasure_boundary_independent η' η Φ β hβ]
  exact h

/-- Diagonal reflection Cauchy--Schwarz is independent of the exterior
sequence. -/
theorem centeredInfiniteVolume_diagonalReflectionCauchySchwarz_boundary_independent
    (η η' : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ σ : Fin d) (k : ℤ)
    (h : DiagonalReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k) :
    DiagonalReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η' Φ β hβ) τ σ k := by
  rw [centeredInfiniteVolumeMeasure_boundary_independent η' η Φ β hβ]
  exact h

/-- Translation invariance transfers diagonal reflection positivity from the
plane `x τ = x σ` to every parallel affine diagonal plane. -/
theorem centeredInfiniteVolume_diagonalReflectionPositive_all_planes
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    {τ σ : Fin d} (hτσ : τ ≠ σ)
    (hzero : DiagonalReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ 0) :
    ∀ k : ℤ, DiagonalReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k := by
  intro k _ F hF
  let v := axisTranslation τ (-k)
  let Ft := F.translatePullback v
  have hFt : Ft.SupportedInDiagonalPositiveHalf τ σ 0 := by
    intro e he
    simp only [Ft, LocalObservable.translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hF a ha
    constructor
    · change 0 ≤ translate v a.source τ - translate v a.source σ
      simp [translate, v, axisTranslation, hτσ.symm]
      omega
    · rw [PositiveEdge.target_translate]
      simp [translate, v, axisTranslation, hτσ.symm]
      omega
  have hpos := hzero hτσ Ft hFt
  have htranslate := centeredInfiniteVolume_integral_translatePullback
    η Φ β hβ v (F.diagonalReflectionProduct τ σ k F)
  have hintegrand : ∀ A : Configuration d G,
      (F.diagonalReflectionProduct τ σ k F).translatePullback v A =
        Ft.diagonalReflectionProduct τ σ 0 Ft A := by
    intro A
    change star (F (diagonalReflectConfiguration τ σ k
        (LocalObservable.translateConfiguration v A))) *
          F (LocalObservable.translateConfiguration v A) =
      star (F (LocalObservable.translateConfiguration v
        (diagonalReflectConfiguration τ σ 0 A))) *
          F (LocalObservable.translateConfiguration v A)
    rw [translateConfiguration_diagonalReflect_axis_neg hτσ]
  have heq :
      ∫ A, F.diagonalReflectionProduct τ σ k F A
          ∂centeredInfiniteVolumeMeasure η Φ β hβ =
        ∫ A, Ft.diagonalReflectionProduct τ σ 0 Ft A
          ∂centeredInfiniteVolumeMeasure η Φ β hβ := by
    rw [← htranslate]
    apply integral_congr_ae
    exact ae_of_all _ hintegrand
  rw [heq]
  exact hpos

/-- Translation invariance transfers diagonal reflection Cauchy--Schwarz from
`x τ = x σ` to every parallel affine diagonal plane. -/
theorem centeredInfiniteVolume_diagonalReflectionCauchySchwarz_all_planes
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    {τ σ : Fin d} (hτσ : τ ≠ σ)
    (hzero : DiagonalReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ 0) :
    ∀ k : ℤ, DiagonalReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k := by
  intro k _ F H hF hH
  let v := axisTranslation τ (-k)
  let Ft := F.translatePullback v
  let Ht := H.translatePullback v
  have translateSupport (K : LocalObservable d G)
      (hK : K.SupportedInDiagonalPositiveHalf τ σ k) :
      (K.translatePullback v).SupportedInDiagonalPositiveHalf τ σ 0 := by
    intro e he
    simp only [LocalObservable.translatePullback] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have ha' := hK a ha
    constructor
    · change 0 ≤ translate v a.source τ - translate v a.source σ
      simp [translate, v, axisTranslation, hτσ.symm]
      omega
    · rw [PositiveEdge.target_translate]
      simp [translate, v, axisTranslation, hτσ.symm]
      omega
  have hFt := translateSupport F hF
  have hHt := translateSupport H hH
  have hCS := hzero hτσ Ft Ht hFt hHt
  have pairing_translate (K L : LocalObservable d G) :
      diagonalReflectionPairing
          (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k K L =
        diagonalReflectionPairing
          (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ 0
            (K.translatePullback v) (L.translatePullback v) := by
    have htranslate := centeredInfiniteVolume_integral_translatePullback
      η Φ β hβ v (K.diagonalReflectionProduct τ σ k L)
    rw [diagonalReflectionPairing, diagonalReflectionPairing, ← htranslate]
    apply integral_congr_ae
    apply ae_of_all
    intro A
    change star (K (diagonalReflectConfiguration τ σ k
        (LocalObservable.translateConfiguration v A))) *
          L (LocalObservable.translateConfiguration v A) =
      star (K (LocalObservable.translateConfiguration v
        (diagonalReflectConfiguration τ σ 0 A))) *
          L (LocalObservable.translateConfiguration v A)
    rw [translateConfiguration_diagonalReflect_axis_neg hτσ]
  rw [pairing_translate F H, pairing_translate F F, pairing_translate H H]
  exact hCS

end

end YangMills.StrongCoupling
