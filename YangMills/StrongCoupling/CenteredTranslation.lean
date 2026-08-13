/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.CenteredBoundaryExpansion
import YangMills.StrongCoupling.FiniteSpecificationGibbsTower

/-!
# Translation covariance of the centered cluster limit

A translated centered box is a geometrically complete sub-specification of a
slightly larger centered box.  The generic finite-specification Gibbs tower
then compares the translated finite-volume expectation with the centered one.
The one-root cluster boundary tail makes this comparison vanish, proving
translation invariance of the thermodynamic limit.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume

noncomputable section

local instance centeredTranslationDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- The translate of a centered specification retains the defining property
that its active plaquettes are exactly those incident to a dynamic edge. -/
theorem centeredSpecification_translate_active_eq_biUnion
    (m : ℕ) (η : Configuration d G) (v : Site d) :
    ((centeredSpecification m η).translate v).activePlaquettes =
      ((centeredSpecification m η).translate v).dynamicEdges.biUnion
        incidentPlaquettes := by
  classical
  ext p
  constructor
  · intro hp
    rw [FiniteSpecification.translate_activePlaquettes] at hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    rw [centeredSpecification_activePlaquettes, centeredActivePlaquettes,
      Finset.mem_biUnion] at hq
    obtain ⟨e, he, hqe⟩ := hq
    rw [Finset.mem_biUnion]
    refine ⟨e.translate v, ?_, ?_⟩
    · rw [FiniteSpecification.translate_dynamicEdges]
      exact Finset.mem_map.mpr ⟨e, he, rfl⟩
    · rw [incidentPlaquettes_translate]
      exact Finset.mem_map.mpr ⟨q, hqe, rfl⟩
  · intro hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨e, he, hpe⟩ := hp
    rw [FiniteSpecification.translate_dynamicEdges] at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    change p ∈ incidentPlaquettes (a.translate v) at hpe
    rw [incidentPlaquettes_translate] at hpe
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hpe
    rw [FiniteSpecification.translate_activePlaquettes]
    apply Finset.mem_map.mpr
    refine ⟨q, ?_, rfl⟩
    rw [centeredSpecification_activePlaquettes, centeredActivePlaquettes,
      Finset.mem_biUnion]
    exact ⟨a, ha, hq⟩

/-- Every translated dynamic edge of the radius-`m` centered specification
lies in the centered box enlarged by the translation radius. -/
theorem centeredSpecification_translate_dynamic_subset
    (m : ℕ) (η : Configuration d G) (v : Site d) :
    ((centeredSpecification m η).translate v).dynamicEdges ⊆
      (centeredSpecification (m + siteTranslationRadius v) η).dynamicEdges := by
  classical
  intro e he
  rw [FiniteSpecification.translate_dynamicEdges] at he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
  exact positiveEdge_translate_mem_centeredBox_add_radius v ha

/-- A translated centered specification is a complete sub-specification of
the centered specification enlarged by the translation radius. -/
def translatedCenteredSubspecification
    (m : ℕ) (ηsmall ηlarge : Configuration d G) (v : Site d) :
    FiniteSubspecification
      ((centeredSpecification m ηsmall).translate v)
      (centeredSpecification (m + siteTranslationRadius v) ηlarge) where
  dynamic_subset := centeredSpecification_translate_dynamic_subset m ηsmall v
  active_subset := by
    intro p hp
    rw [centeredSpecification_translate_active_eq_biUnion] at hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨e, he, hpe⟩ := hp
    rw [centeredSpecification_activePlaquettes, centeredActivePlaquettes,
      Finset.mem_biUnion]
    exact ⟨e,
      centeredSpecification_translate_dynamic_subset m ηsmall v he, hpe⟩
  boundary_disjoint_of_not_active := by
    intro p hp
    rw [Finset.disjoint_left]
    intro e hep he
    apply hp
    rw [centeredSpecification_translate_active_eq_biUnion,
      Finset.mem_biUnion]
    exact ⟨e, he, mem_incidentPlaquettes_of_mem_boundary e p hep⟩

/-- Replacing the exterior of a translated centered specification is the
same as first translating that exterior back to the original geometry and
then translating the whole specification. -/
theorem withExterior_centeredSpecification_translate
    (m : ℕ) (η ξ : Configuration d G) (v : Site d) :
    withExterior ((centeredSpecification m η).translate v) ξ =
      (centeredSpecification m
        (LocalObservable.translateConfiguration v ξ)).translate v := by
  change
    FiniteSpecification.mk
      ((centeredBox d m).positiveEdges.map
        (PositiveEdge.translationEquiv v).toEmbedding)
      ((centeredActivePlaquettes d m).map
        (Plaquette.translationEquiv v).toEmbedding) ξ =
    FiniteSpecification.mk
      ((centeredBox d m).positiveEdges.map
        (PositiveEdge.translationEquiv v).toEmbedding)
      ((centeredActivePlaquettes d m).map
        (Plaquette.translationEquiv v).toEmbedding)
      (fun e =>
        LocalObservable.translateConfiguration v ξ (e.translate (-v)))
  congr 1
  funext e
  simp [LocalObservable.translateConfiguration]

/-- The generic Gibbs tower and the one-root KP boundary estimate compare a
translated radius-`m` box with the containing centered box. -/
theorem norm_centered_add_radius_sub_translated_le_eventually
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (v : Site d) (r : ℕ) :
    ∃ N, ∀ m, N ≤ m → ∀ ηsmall ηlarge : Configuration d G,
      ‖complexGibbsExpectation F
          (centeredSpecification (m + siteTranslationRadius v) ηlarge)
          Φ (β : ℂ) -
        complexGibbsExpectation F
          ((centeredSpecification m ηsmall).translate v) Φ (β : ℂ)‖ ≤
      2 * observableCardinalityTiltDecorationBudget (d := d)
          (F.translatePullback (-v)) Φ (β : ℂ) *
        plaquetteClusterDecayRate (d := d) Φ (β : ℂ) ^ r := by
  obtain ⟨N, hN⟩ :=
    norm_centered_complexGibbsExpectation_boundary_sub_le_eventually
      (F.translatePullback (-v)) Φ hβ r
  refine ⟨N, fun m hm ηsmall ηlarge => ?_⟩
  let small := (centeredSpecification m ηsmall).translate v
  let large := centeredSpecification (m + siteTranslationRadius v) ηlarge
  let h : FiniteSubspecification small large :=
    translatedCenteredSubspecification m ηsmall ηlarge v
  apply h.norm_complexGibbsExpectation_large_sub_small_le_of_uniform
    small.exterior F Φ β _
  intro ξ
  rw [show { small with exterior := ξ } =
      (centeredSpecification m
        (LocalObservable.translateConfiguration v ξ)).translate v by
    simpa only [small] using
      withExterior_centeredSpecification_translate m ηsmall ξ v]
  rw [show { small with exterior := small.exterior } = small by
    rfl]
  rw [show small = (centeredSpecification m ηsmall).translate v by rfl]
  rw [complexGibbsExpectation_translate_ofReal,
    complexGibbsExpectation_translate_ofReal]
  exact hN m hm (LocalObservable.translateConfiguration v ξ) ηsmall

/-- A centered expectation and the corresponding translated-box expectation
become equal in the thermodynamic limit.  The convergence is the explicit
one-root KP tail passed through the finite-specification Gibbs tower. -/
theorem tendsto_centered_add_radius_sub_translated_zero
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (v : Site d) (ηsmall ηlarge : ℕ → Configuration d G) :
    Tendsto (fun m =>
      complexGibbsExpectation F
          (centeredSpecification (m + siteTranslationRadius v) (ηlarge m))
          Φ (β : ℂ) -
        complexGibbsExpectation F
          ((centeredSpecification m (ηsmall m)).translate v) Φ (β : ℂ))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let B := 2 * observableCardinalityTiltDecorationBudget (d := d)
    (F.translatePullback (-v)) Φ (β : ℂ)
  let q := plaquetteClusterDecayRate (d := d) Φ (β : ℂ)
  have hq0 : 0 ≤ q := (plaquetteClusterDecayRate_pos Φ hβ).le
  have hq1 : q < 1 := plaquetteClusterDecayRate_lt_one Φ hβ
  have hmajorant : Tendsto (fun r : ℕ => B * q ^ r) atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul B
  have hevent : ∀ᶠ r in atTop, B * q ^ r < ε :=
    hmajorant (gt_mem_nhds hε)
  obtain ⟨r, hr⟩ := eventually_atTop.1 hevent
  obtain ⟨N, hN⟩ :=
    norm_centered_add_radius_sub_translated_le_eventually
      F Φ β hβ v r
  refine ⟨N, fun m hm => ?_⟩
  rw [dist_zero_right]
  exact (hN m hm (ηsmall m) (ηlarge m)).trans_lt
    (by simpa [B, q] using hr r le_rfl)

/-- Exact finite-volume translation covariance turns the preceding
translated-box comparison into a comparison of a translated observable with
an enlarged centered-box expectation. -/
theorem tendsto_centered_translationPullback_difference_zero
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (v : Site d) (ηsmall ηlarge : ℕ → Configuration d G) :
    Tendsto (fun m =>
      complexGibbsExpectation F
          (centeredSpecification
            (m + siteTranslationRadius (-v)) (ηlarge m)) Φ (β : ℂ) -
        complexGibbsExpectation (F.translatePullback v)
          (centeredSpecification m (ηsmall m)) Φ (β : ℂ))
      atTop (nhds 0) := by
  have h := tendsto_centered_add_radius_sub_translated_zero
    F Φ β hβ (-v) ηsmall ηlarge
  simpa only [neg_neg] using h.congr' (Filter.Eventually.of_forall fun m => by
    rw [complexGibbsExpectation_translate_ofReal]
    simp)

end

end YangMills.StrongCoupling
