/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.BoxDobrushin
import YangMills.StrongCoupling.AbstractBoundaryDecay
import YangMills.StrongCoupling.MarkedExpansion

/-!
# Uniform boundary decay for finite-volume Yang--Mills theory

This module supplies the concrete Milestone 10 exit theorem.  It compares two
arbitrary finite boxes with the same dynamic edges and active plaquettes but
different frozen exterior fields.  At sufficiently small real coupling, the
difference of any bounded local observable decays geometrically in its
interaction-graph distance from the exact exterior-disagreement set, with no
factor proportional to the size of that set.
-/

open MeasureTheory ProbabilityTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume
open YangMills.Probability

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Dynamic edges on which the observable is recorded to depend. -/
def observableRootEdges (Λ : FiniteSpecification d G)
    (F : LocalObservable d G) : Finset Λ.dynamicEdges :=
  Finset.univ.filter fun x => x.1 ∈ F.support

/-- Dynamic edges whose singleton action reads at least one frozen edge on
which the two exterior configurations disagree. -/
def boundaryDefectEdges (Λ : FiniteSpecification d G)
    (η η' : Configuration d G) : Finset Λ.dynamicEdges := by
  classical
  exact Finset.univ.filter fun x =>
    ∃ p ∈ Λ.activePlaquettes,
      x.1 ∈ p.boundary.edgeSupport ∧
      ∃ e ∈ p.boundary.edgeSupport,
        e ∉ Λ.dynamicEdges ∧ η e ≠ η' e

@[simp]
theorem mem_observableRootEdges
    (Λ : FiniteSpecification d G) (F : LocalObservable d G)
    (x : Λ.dynamicEdges) :
    x ∈ observableRootEdges Λ F ↔ x.1 ∈ F.support := by
  simp [observableRootEdges]

@[simp]
theorem mem_boundaryDefectEdges
    (Λ : FiniteSpecification d G) (η η' : Configuration d G)
    (x : Λ.dynamicEdges) :
    x ∈ boundaryDefectEdges Λ η η' ↔
      ∃ p ∈ Λ.activePlaquettes,
        x.1 ∈ p.boundary.edgeSupport ∧
        ∃ e ∈ p.boundary.edgeSupport,
          e ∉ Λ.dynamicEdges ∧ η e ≠ η' e := by
  simp [boundaryDefectEdges]

theorem card_observableRootEdges_le
    (Λ : FiniteSpecification d G) (F : LocalObservable d G) :
    (observableRootEdges Λ F).card ≤ F.support.card := by
  classical
  let valEmbedding : Λ.dynamicEdges ↪ PositiveEdge d :=
    ⟨Subtype.val, Subtype.val_injective⟩
  calc
    (observableRootEdges Λ F).card =
        ((observableRootEdges Λ F).map valEmbedding).card := by simp
    _ ≤ F.support.card := by
      apply Finset.card_le_card
      intro e he
      rcases Finset.mem_map.mp he with ⟨x, hx, rfl⟩
      exact (mem_observableRootEdges Λ F x).mp hx

/-- Away from the exact defect set, the incident plaquette action is
identical for the two frozen exterior fields. -/
theorem actionAtEdge_withExterior_eq_of_not_defect
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (η η' : Configuration d G) (x : Λ.dynamicEdges)
    (hx : x ∉ boundaryDefectEdges Λ η η')
    (U : DynamicConfiguration Λ) :
    actionAtEdge (withExterior Λ η) Φ x U =
      actionAtEdge (withExterior Λ η') Φ x U := by
  classical
  unfold actionAtEdge
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  unfold plaquetteHolonomy
  apply Gauge.holonomy_eq_of_eqOn_edgeSupport
  intro e he
  by_cases hedyn : e ∈ Λ.dynamicEdges
  · rw [(withExterior Λ η).evaluate_of_mem _ e hedyn,
      (withExterior Λ η').evaluate_of_mem _ e hedyn]
    rfl
  · rw [(withExterior Λ η).evaluate_of_not_mem _ e hedyn,
      (withExterior Λ η').evaluate_of_not_mem _ e hedyn]
    change η e = η' e
    by_contra hne
    apply hx
    rw [mem_boundaryDefectEdges]
    exact ⟨p, (Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2, e, he, hedyn, hne⟩

/-- Singleton conditional laws agree away from the exact boundary-defect
edges.  Exterior-dependent plaquettes not incident to the resampled edge
contribute only a fiber-constant normalization, which cancels. -/
theorem boxGibbsSpec_withExterior_condDist_eq_of_not_defect
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (η η' : Configuration d G) (x : Λ.dynamicEdges)
    (hx : x ∉ boundaryDefectEdges Λ η η')
    (σ : DynamicConfiguration Λ) :
    (boxGibbsSpec (withExterior Λ η) Φ β).condDist {x} σ =
      (boxGibbsSpec (withExterior Λ η') Φ β).condDist {x} σ := by
  let c : ℝ := β *
    (actionAwayFromEdge (withExterior Λ η) Φ x σ -
      actionAwayFromEdge (withExterior Λ η') Φ x σ)
  apply (boxEnergy (withExterior Λ η) Φ β).conditionalMeasure_eq_of_add_const
    (GaugeHaarProbability.haar G)
    (boxEnergy (withExterior Λ η') Φ β) {x} σ c
  intro u
  change β * action (withExterior Λ η) Φ (glue {x} u σ) =
    β * action (withExterior Λ η') Φ (glue {x} u σ) + c
  have hawayη :
      actionAwayFromEdge (withExterior Λ η) Φ x (glue {x} u σ) =
        actionAwayFromEdge (withExterior Λ η) Φ x σ :=
    actionAwayFromEdge_glue_singleton (withExterior Λ η) Φ x u σ
  have hawayη' :
      actionAwayFromEdge (withExterior Λ η') Φ x (glue {x} u σ) =
        actionAwayFromEdge (withExterior Λ η') Φ x σ :=
    actionAwayFromEdge_glue_singleton (withExterior Λ η') Φ x u σ
  rw [action_eq_atEdge_add_away (withExterior Λ η) Φ x,
    action_eq_atEdge_add_away (withExterior Λ η') Φ x,
    hawayη, hawayη',
    actionAtEdge_withExterior_eq_of_not_defect Λ Φ η η' x hx]
  dsimp [c]
  ring_nf
  exact add_comm
    (β * actionAtEdge (withExterior Λ η') Φ x (glue {x} u σ))
    (β * actionAwayFromEdge (withExterior Λ η) Φ x σ)

/-- **Uniform boundary sensitivity at strong coupling.**

For two arbitrary frozen exterior configurations, a bounded local observable
supported on dynamic edges changes by at most a geometric Dobrushin tail in
the interaction-graph separation from the exact defect set.  The prefactor is
linear in the observable's recorded support and independent of the box volume
and of the number of boundary defects. -/
theorem complexGibbsExpectation_boundaryDecay
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℝ)
    (η η' : Configuration d G)
    (hF : F.support ⊆ Λ.dynamicEdges)
    (hsmall : boxDobrushinAlpha d Φ.bound β < 1)
    (r : ℕ)
    (hseparated : ∀ root ∈ observableRootEdges Λ F,
      ∀ defect ∈ boundaryDefectEdges Λ η η',
        r ≤ completedGraphDist (H := edgeInteractionGraph Λ) root defect) :
    ‖complexGibbsExpectation F (withExterior Λ η) Φ (β : ℂ) -
        complexGibbsExpectation F (withExterior Λ η') Φ (β : ℂ)‖ ≤
      4 * ‖F.toBoundedContinuousMap‖ * (F.support.card : ℝ) *
        (boxDobrushinAlpha d Φ.bound β ^ r /
          (1 - boxDobrushinAlpha d Φ.bound β)) := by
  classical
  let Λ₁ := withExterior Λ η
  let Λ₂ := withExterior Λ η'
  let γ : GibbsSpec Λ.dynamicEdges G := boxGibbsSpec Λ₁ Φ β
  let μ₁ : Measure (DynamicConfiguration Λ) := gibbsMeasure Λ₁ Φ β
  let μ₂ : Measure (DynamicConfiguration Λ) := gibbsMeasure Λ₂ Φ β
  let roots := observableRootEdges Λ F
  let defects := boundaryDefectEdges Λ η η'
  let H := edgeInteractionGraph Λ
  let g : DynamicConfiguration Λ → ℂ := fun U => F (Λ₁.evaluate U)
  haveI : IsProbabilityMeasure μ₁ := by
    dsimp [μ₁]
    exact Gauge.FiniteVolume.instIsProbabilityMeasureGibbsMeasure Λ₁ Φ β
  haveI : IsProbabilityMeasure μ₂ := by
    dsimp [μ₂]
    exact Gauge.FiniteVolume.instIsProbabilityMeasureGibbsMeasure Λ₂ Φ β
  haveI : IsFiniteMeasure μ₁ :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure μ₁
  haveI : IsFiniteMeasure μ₂ :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure μ₂
  let hD : DobrushinCondition γ :=
    box_dobrushinCondition Λ₁ Φ β hsmall
  have hg_meas : Measurable g :=
    (F.toContinuousMap.continuous.comp Λ₁.continuous_evaluate).measurable
  have hg_bound : ∀ U, ‖g U‖ ≤ ‖F.toBoundedContinuousMap‖ :=
    fun U => F.norm_apply_le (Λ₁.evaluate U)
  have hg_int₁ : Integrable g μ₁ := by
    apply Integrable.of_bound hg_meas.aestronglyMeasurable
      ‖F.toBoundedContinuousMap‖
    exact ae_of_all _ hg_bound
  have hg_int₂ : Integrable g μ₂ := by
    apply Integrable.of_bound hg_meas.aestronglyMeasurable
      ‖F.toBoundedContinuousMap‖
    exact ae_of_all _ hg_bound
  have hg_local : ∀ σ τ, (∀ x ∈ roots, σ x = τ x) → g σ = g τ := by
    intro σ τ hστ
    apply F.dependsOn_support
    intro e he
    have he' : e ∈ F.support := by simpa using he
    have hedyn : e ∈ Λ.dynamicEdges := hF he'
    rw [Λ₁.evaluate_of_mem _ e hedyn, Λ₁.evaluate_of_mem _ e hedyn]
    exact hστ ⟨e, hedyn⟩ (by
      simp [roots, observableRootEdges, he'])
  have hDLR₁ : ∀ z, z ∉ defects →
      ∀ A : Set (DynamicConfiguration Λ), MeasurableSet A →
        (μ₁ A).toReal =
          ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₁ := by
    intro z _ A hA
    exact (gibbsMeasure_isGibbs_box Λ₁ Φ β).dlr {z} A hA
  have hDLR₂ : ∀ z, z ∉ defects →
      ∀ A : Set (DynamicConfiguration Λ), MeasurableSet A →
        (μ₂ A).toReal =
          ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂ := by
    intro z hz A hA
    calc
      (μ₂ A).toReal =
          ∫ σ, ((boxGibbsSpec Λ₂ Φ β).condDist {z} σ A).toReal ∂μ₂ :=
        (gibbsMeasure_isGibbs_box Λ₂ Φ β).dlr {z} A hA
      _ = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂ := by
        apply integral_congr_ae
        exact ae_of_all _ fun σ => by
          change (((boxGibbsSpec (withExterior Λ η') Φ β).condDist
              {z} σ) A).toReal =
            (((boxGibbsSpec (withExterior Λ η) Φ β).condDist
              {z} σ) A).toReal
          rw [boxGibbsSpec_withExterior_condDist_eq_of_not_defect
            Λ Φ β η η' z hz σ]
          rfl
  have habstract :
      ‖(∫ σ, g σ ∂μ₁) - ∫ σ, g σ ∂μ₂‖ ≤
        4 * ‖F.toBoundedContinuousMap‖ * (roots.card : ℝ) *
          (hD.α ^ r / (1 - hD.α)) := by
    apply complexLocalExpectation_boundaryDecay γ hD μ₁ μ₂
      roots defects g hg_meas ‖F.toBoundedContinuousMap‖
      (norm_nonneg _) hg_bound hg_int₁ hg_int₂ hg_local hDLR₁ hDLR₂
      (finiteInfluenceSupport γ)
      (fun z A hA σ τ hστ => finiteInfluence_dependency γ z A hA σ τ hστ)
      (completedGraphDist (H := H)) (completedGraphDist_self H)
      (fun x y z => completedGraphDist_triangle H x z y)
      (fun x y hxy =>
        box_influenceCoeff_eq_zero_of_completedGraphDist_gt_one
          Λ₁ Φ β x y hxy)
      r hseparated
  have hobs : ∀ U : DynamicConfiguration Λ,
      F (Λ₁.evaluate U) = F (Λ₂.evaluate U) := by
    intro U
    apply F.dependsOn_support
    intro e he
    have he' : e ∈ F.support := by simpa using he
    have hedyn : e ∈ Λ.dynamicEdges := hF he'
    rw [Λ₁.evaluate_of_mem _ e hedyn, Λ₂.evaluate_of_mem _ e hedyn]
    rfl
  rw [complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  change ‖(∫ σ, g σ ∂μ₁) -
      ∫ σ, F (Λ₂.evaluate σ) ∂μ₂‖ ≤ _
  rw [show (∫ σ, F (Λ₂.evaluate σ) ∂μ₂) =
      ∫ σ, g σ ∂μ₂ by
    apply integral_congr_ae
    exact ae_of_all _ fun U => (hobs U).symm]
  calc
    ‖(∫ σ, g σ ∂μ₁) - ∫ σ, g σ ∂μ₂‖ ≤
        4 * ‖F.toBoundedContinuousMap‖ * (roots.card : ℝ) *
          (hD.α ^ r / (1 - hD.α)) := habstract
    _ ≤ 4 * ‖F.toBoundedContinuousMap‖ * (F.support.card : ℝ) *
        (hD.α ^ r / (1 - hD.α)) := by
      have htail : 0 ≤ hD.α ^ r / (1 - hD.α) := by
        exact div_nonneg (pow_nonneg hD.hα_pos _)
          (sub_nonneg.mpr hD.hα_lt.le)
      gcongr
      exact_mod_cast card_observableRootEdges_le Λ F
    _ = 4 * ‖F.toBoundedContinuousMap‖ * (F.support.card : ℝ) *
        (boxDobrushinAlpha d Φ.bound β ^ r /
          (1 - boxDobrushinAlpha d Φ.bound β)) := by
      rw [show hD.α = boxDobrushinAlpha d Φ.bound β by rfl]

end

end YangMills.StrongCoupling
