/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.BoxGibbs
import YangMills.StrongCoupling.Counting
import MarkovSemigroups.Dobrushin.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Uniform Dobrushin bounds for arbitrary Yang--Mills boxes

The sites are the dynamic positive edges.  Two sites interact when an active
plaquette contains both.  This module proves the finite-range support and an
explicit, volume-independent influence bound from the bounded plaquette
potential.
-/

open MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume
open YangMills.Probability

noncomputable section

local instance boxDobrushinDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- Active plaquettes containing a given dynamic edge. -/
def edgePlaquettes (Λ : FiniteSpecification d G) (x : Λ.dynamicEdges) :
    Finset (Plaquette d) :=
  Λ.activePlaquettes.filter fun p => x.1 ∈ p.boundary.edgeSupport

/-- Two dynamic edges share an active plaquette. -/
def sharesActivePlaquette (Λ : FiniteSpecification d G)
    (x y : Λ.dynamicEdges) : Prop :=
  ∃ p ∈ Λ.activePlaquettes,
    x.1 ∈ p.boundary.edgeSupport ∧ y.1 ∈ p.boundary.edgeSupport

theorem sharesActivePlaquette_symm (Λ : FiniteSpecification d G) :
    Symmetric (sharesActivePlaquette Λ) := by
  rintro x y ⟨p, hp, hx, hy⟩
  exact ⟨p, hp, hy, hx⟩

/-- Plaquette action terms that can depend on the site `x`. -/
def actionAtEdge (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (x : Λ.dynamicEdges) (U : DynamicConfiguration Λ) : ℝ :=
  ∑ p ∈ edgePlaquettes Λ x, Φ (plaquetteHolonomy Λ U p)

/-- The complementary action, constant along a singleton `x` fiber. -/
def actionAwayFromEdge (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (x : Λ.dynamicEdges)
    (U : DynamicConfiguration Λ) : ℝ :=
  ∑ p ∈ Λ.activePlaquettes.filter
      (fun p => x.1 ∉ p.boundary.edgeSupport),
    Φ (plaquetteHolonomy Λ U p)

theorem action_eq_atEdge_add_away (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (x : Λ.dynamicEdges)
    (U : DynamicConfiguration Λ) :
    action Λ Φ U = actionAtEdge Λ Φ x U + actionAwayFromEdge Λ Φ x U := by
  classical
  unfold action actionAtEdge actionAwayFromEdge edgePlaquettes
  rw [← Finset.sum_filter_add_sum_filter_not Λ.activePlaquettes
    (fun p => x.1 ∈ p.boundary.edgeSupport)
    (fun p => Φ (plaquetteHolonomy Λ U p))]

theorem card_edgePlaquettes_le (Λ : FiniteSpecification d G)
    (x : Λ.dynamicEdges) :
    (edgePlaquettes Λ x).card ≤ 4 * d := by
  classical
  apply (Finset.card_le_card ?_).trans (card_incidentPlaquettes_le x.1)
  intro p hp
  exact mem_incidentPlaquettes_of_mem_boundary x.1 p
    (Finset.mem_filter.mp hp).2

/-- Glued singleton configurations whose boundaries differ only at `y` still
differ only at `y`. -/
theorem glue_singleton_eq_off
    (Λ : FiniteSpecification d G) (x y : Λ.dynamicEdges)
    (u σ τ : DynamicConfiguration Λ)
    (hστ : ∀ z, z ≠ y → σ z = τ z) :
    ∀ z, z ≠ y → glue {x} u σ z = glue {x} u τ z := by
  intro z hz
  by_cases hzx : z = x
  · subst z
    simp [glue]
  · simp [glue, hzx, hστ z hz]

theorem plaquetteHolonomy_glue_eq_of_not_mem
    (Λ : FiniteSpecification d G) (x y : Λ.dynamicEdges)
    (u σ τ : DynamicConfiguration Λ)
    (hστ : ∀ z, z ≠ y → σ z = τ z)
    (p : Plaquette d) (hy : y.1 ∉ p.boundary.edgeSupport) :
    plaquetteHolonomy Λ (glue {x} u σ) p =
      plaquetteHolonomy Λ (glue {x} u τ) p := by
  unfold plaquetteHolonomy
  apply Gauge.holonomy_eq_of_eqOn_edgeSupport
  intro e he
  by_cases hedyn : e ∈ Λ.dynamicEdges
  · rw [Λ.evaluate_of_mem _ e hedyn, Λ.evaluate_of_mem _ e hedyn]
    apply glue_singleton_eq_off Λ x y u σ τ hστ
    intro heq
    apply hy
    have hval : e = y.1 := congrArg Subtype.val heq
    simpa [hval] using he
  · rw [Λ.evaluate_of_not_mem _ e hedyn, Λ.evaluate_of_not_mem _ e hedyn]

theorem norm_actionAtEdge_glue_sub_le
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (x y : Λ.dynamicEdges) (u σ τ : DynamicConfiguration Λ)
    (_hστ : ∀ z, z ≠ y → σ z = τ z) :
    ‖actionAtEdge Λ Φ x (glue {x} u τ) -
        actionAtEdge Λ Φ x (glue {x} u σ)‖ ≤
      8 * d * Φ.bound := by
  classical
  unfold actionAtEdge
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p ∈ edgePlaquettes Λ x,
        (Φ (plaquetteHolonomy Λ (glue {x} u τ) p) -
          Φ (plaquetteHolonomy Λ (glue {x} u σ) p))‖ ≤
      ∑ p ∈ edgePlaquettes Λ x,
        ‖Φ (plaquetteHolonomy Λ (glue {x} u τ) p) -
          Φ (plaquetteHolonomy Λ (glue {x} u σ) p)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ edgePlaquettes Λ x, 2 * Φ.bound := by
      apply Finset.sum_le_sum
      intro p _
      calc
        ‖Φ (plaquetteHolonomy Λ (glue {x} u τ) p) -
            Φ (plaquetteHolonomy Λ (glue {x} u σ) p)‖ ≤
            ‖Φ (plaquetteHolonomy Λ (glue {x} u τ) p)‖ +
              ‖Φ (plaquetteHolonomy Λ (glue {x} u σ) p)‖ := norm_sub_le _ _
        _ ≤ Φ.bound + Φ.bound := add_le_add
          (Φ.norm_le_bound _) (Φ.norm_le_bound _)
        _ = 2 * Φ.bound := by ring
    _ = (edgePlaquettes Λ x).card * (2 * Φ.bound) := by simp
    _ ≤ (4 * d) * (2 * Φ.bound) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_edgePlaquettes_le Λ x
      · exact mul_nonneg (by norm_num) Φ.bound_nonneg
    _ = 8 * d * Φ.bound := by ring

/-- If `x` and `y` share no active plaquette, the centered singleton energy
is exactly insensitive to changing `y`. -/
theorem actionAtEdge_glue_eq_of_not_shares
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (x y : Λ.dynamicEdges) (u σ τ : DynamicConfiguration Λ)
    (hστ : ∀ z, z ≠ y → σ z = τ z)
    (hshare : ¬sharesActivePlaquette Λ x y) :
    actionAtEdge Λ Φ x (glue {x} u τ) =
      actionAtEdge Λ Φ x (glue {x} u σ) := by
  unfold actionAtEdge
  apply Finset.sum_congr rfl
  intro p hp
  have hxp : x.1 ∈ p.boundary.edgeSupport := by
    exact (Finset.mem_filter.mp hp).2
  have hyp : y.1 ∉ p.boundary.edgeSupport := by
    intro hyp
    exact hshare ⟨p, (Finset.mem_filter.mp hp).1, hxp, hyp⟩
  rw [plaquetteHolonomy_glue_eq_of_not_mem Λ x y u σ τ hστ p hyp]

/-- The action terms not incident to `x` are constant when `x` is
resampled. -/
theorem actionAwayFromEdge_glue_singleton
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (x : Λ.dynamicEdges) (u σ : DynamicConfiguration Λ) :
    actionAwayFromEdge Λ Φ x (glue {x} u σ) =
      actionAwayFromEdge Λ Φ x σ := by
  unfold actionAwayFromEdge
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  unfold plaquetteHolonomy
  apply Gauge.holonomy_eq_of_eqOn_edgeSupport
  intro e he
  by_cases hedyn : e ∈ Λ.dynamicEdges
  · rw [Λ.evaluate_of_mem _ e hedyn, Λ.evaluate_of_mem _ e hedyn]
    have hxp : x.1 ∉ p.boundary.edgeSupport := (Finset.mem_filter.mp hp).2
    have hne : (⟨e, hedyn⟩ : Λ.dynamicEdges) ≠ x := by
      intro h
      apply hxp
      have hval : e = x.1 := congrArg Subtype.val h
      simpa [hval] using he
    simp [glue, hne]
  · rw [Λ.evaluate_of_not_mem _ e hedyn, Λ.evaluate_of_not_mem _ e hedyn]

/-- After removing the fiber-constant part of the action, changing one
boundary edge changes a singleton energy by at most `8 d ‖Φ‖∞ |β|`. -/
theorem boxEnergy_centered_singleton_sub_le
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (x y : Λ.dynamicEdges) (u σ τ : DynamicConfiguration Λ)
    (hστ : ∀ z, z ≠ y → σ z = τ z) :
    |((boxEnergy Λ Φ β) (glue {x} u τ) -
          β * actionAwayFromEdge Λ Φ x τ) -
        ((boxEnergy Λ Φ β) (glue {x} u σ) -
          β * actionAwayFromEdge Λ Φ x σ)| ≤
      |β| * (8 * d * Φ.bound) := by
  change |(β * action Λ Φ (glue {x} u τ) -
      β * actionAwayFromEdge Λ Φ x τ) -
    (β * action Λ Φ (glue {x} u σ) -
      β * actionAwayFromEdge Λ Φ x σ)| ≤
    |β| * (8 * d * Φ.bound)
  rw [action_eq_atEdge_add_away, action_eq_atEdge_add_away,
    actionAwayFromEdge_glue_singleton, actionAwayFromEdge_glue_singleton]
  rw [show β * (actionAtEdge Λ Φ x (glue {x} u τ) +
        actionAwayFromEdge Λ Φ x τ) - β * actionAwayFromEdge Λ Φ x τ -
      (β * (actionAtEdge Λ Φ x (glue {x} u σ) +
        actionAwayFromEdge Λ Φ x σ) - β * actionAwayFromEdge Λ Φ x σ) =
      β * (actionAtEdge Λ Φ x (glue {x} u τ) -
        actionAtEdge Λ Φ x (glue {x} u σ)) by ring]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_actionAtEdge_glue_sub_le Λ Φ x y u σ τ hστ) (abs_nonneg β)

/-- The centered singleton energy is exactly unchanged away from the
finite-range interaction neighborhood. -/
theorem boxEnergy_centered_singleton_eq_of_not_shares
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (x y : Λ.dynamicEdges) (u σ τ : DynamicConfiguration Λ)
    (hστ : ∀ z, z ≠ y → σ z = τ z)
    (hshare : ¬sharesActivePlaquette Λ x y) :
    (boxEnergy Λ Φ β) (glue {x} u τ) -
        β * actionAwayFromEdge Λ Φ x τ =
      (boxEnergy Λ Φ β) (glue {x} u σ) -
        β * actionAwayFromEdge Λ Φ x σ := by
  change β * action Λ Φ (glue {x} u τ) -
      β * actionAwayFromEdge Λ Φ x τ =
    β * action Λ Φ (glue {x} u σ) -
      β * actionAwayFromEdge Λ Φ x σ
  rw [action_eq_atEdge_add_away, action_eq_atEdge_add_away,
    actionAwayFromEdge_glue_singleton, actionAwayFromEdge_glue_singleton,
    actionAtEdge_glue_eq_of_not_shares Λ Φ x y u σ τ hστ hshare]
  ring

/-! ## Ratio bounds without a countability assumption on the spin space -/

/-- The elementary probability estimate used in the cylinder-ratio argument.
This local copy removes an unnecessary countability hypothesis from the
upstream theorem, which is essential for compact Lie-group spins. -/
private lemma abs_sub_le_one_sub_exp_neg_nocount
    {p q C : ℝ} (hC : 0 ≤ C)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h1 : Real.exp (-C) * q ≤ p)
    (h2 : Real.exp (-C) * (1 - q) ≤ 1 - p) :
    |p - q| ≤ 1 - Real.exp (-C) := by
  have hexp_le : Real.exp (-C) ≤ 1 := by
    rw [Real.exp_neg]
    exact inv_le_one_of_one_le₀ (Real.one_le_exp hC)
  rw [abs_le]
  constructor
  · have h : q * (1 - Real.exp (-C)) ≤ 1 - Real.exp (-C) :=
      mul_le_of_le_one_left (sub_nonneg.mpr hexp_le) hq1
    nlinarith
  · have h : (1 - q) * (1 - Real.exp (-C)) ≤
        1 - Real.exp (-C) :=
      mul_le_of_le_one_left (sub_nonneg.mpr hexp_le) (by linarith)
    nlinarith

private lemma prob_compl_toReal_eq_nocount
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (A : Set X) (hA : MeasurableSet A) :
    (μ Aᶜ).toReal = 1 - (μ A).toReal := by
  rw [prob_compl_eq_one_sub hA,
    ENNReal.toReal_sub_of_le (prob_le_one (s := A)) ENNReal.one_ne_top]
  simp

/-- A cylinder probability ratio controls Dobrushin influence for arbitrary
measurable spin spaces with measurable singletons.  This is the proof of the
upstream countable-spin result, with the unused `[Countable S]` assumption
removed. -/
theorem influenceCoeff_le_of_cylinder_ratio_bound_nocount
    {I S : Type*} [DecidableEq I]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (x y : I)
    (C : ℝ) (hC : 0 ≤ C)
    (hRatio : ∀ (σ τ : SpinConfig I S),
      (∀ z, z ≠ y → σ z = τ z) →
      ∀ (B : Set S), MeasurableSet B →
        (γ.condDist {x} τ ((fun ρ => ρ x) ⁻¹' B)).toReal ≤
          Real.exp C *
            (γ.condDist {x} σ ((fun ρ => ρ x) ⁻¹' B)).toReal) :
    influenceCoeff γ x y ≤ 1 - Real.exp (-C) := by
  unfold influenceCoeff
  by_cases hne : {c : ℝ | ∃ (σ τ : SpinConfig I S),
      (∀ z, z ≠ y → σ z = τ z) ∧
      c = tvDist (marginalAtSite (γ.condDist {x} σ) x)
        (marginalAtSite (γ.condDist {x} τ) x)}.Nonempty
  · apply csSup_le hne
    rintro c ⟨σ, τ, hdiff, rfl⟩
    apply csSup_le (tvDist_set_nonempty _ _)
    rintro c' ⟨B, hB, rfl⟩
    rw [marginalAtSite_apply _ _ hB, marginalAtSite_apply _ _ hB]
    set A := (fun ρ : SpinConfig I S => ρ x) ⁻¹' B
    have hA : MeasurableSet A := (measurable_pi_apply x) hB
    have hexp_inv :
        Real.exp (-C) * (γ.condDist {x} τ A).toReal ≤
          (γ.condDist {x} σ A).toReal := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos C)]
      exact hRatio σ τ hdiff B hB
    have hexp_compl :
        Real.exp (-C) * (1 - (γ.condDist {x} τ A).toReal) ≤
          1 - (γ.condDist {x} σ A).toReal := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos C)]
      have hBc : MeasurableSet Bᶜ := hB.compl
      have h := hRatio σ τ hdiff Bᶜ hBc
      rwa [Set.preimage_compl,
        prob_compl_toReal_eq_nocount _ _ hA,
        prob_compl_toReal_eq_nocount _ _ hA] at h
    exact abs_sub_le_one_sub_exp_neg_nocount hC
      ENNReal.toReal_nonneg (condDist_toReal_le_one γ x τ _)
      hexp_inv hexp_compl
  · simp only [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sSup_empty]
    have h : Real.exp (-C) ≤ 1 := by
      rw [Real.exp_neg]
      exact inv_le_one_of_one_le₀ (Real.one_le_exp hC)
    linarith

/-- A site's conditional marginal is independent of the incoming value at
that same site, hence its self-influence vanishes. -/
theorem influenceCoeff_self_eq_zero_nocount
    {I S : Type*} [DecidableEq I]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (x : I) : influenceCoeff γ x x = 0 := by
  have hle : influenceCoeff γ x x ≤ 1 - Real.exp (-0) := by
    apply influenceCoeff_le_of_cylinder_ratio_bound_nocount γ x x 0 le_rfl
    intro σ τ hστ B hB
    have heq : γ.condDist {x} τ = γ.condDist {x} σ := by
      apply γ.consistent
      intro z hz
      exact (hστ z (by simpa using hz)).symm
    simp [heq]
  exact le_antisymm (by simpa using hle) (influenceCoeff_nonneg γ x x)

/-! ## Explicit one-edge influences -/

/-- The uniform upper bound for one potentially interacting edge pair. -/
def boxPairInfluenceBound (d : ℕ) (B β : ℝ) : ℝ :=
  16 * d * B * |β|

theorem boxPairInfluenceBound_nonneg
    (B β : ℝ) (hB : 0 ≤ B) :
    0 ≤ boxPairInfluenceBound d B β := by
  unfold boxPairInfluenceBound
  positivity

/-- One-site influence is bounded uniformly in the box volume. -/
theorem box_influenceCoeff_le
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (x y : Λ.dynamicEdges) :
    influenceCoeff (boxGibbsSpec Λ Φ β) x y ≤
      boxPairInfluenceBound d Φ.bound β := by
  let δ : ℝ := |β| * (8 * d * Φ.bound)
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact mul_nonneg (abs_nonneg β)
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) Φ.bound_nonneg)
  calc
    influenceCoeff (boxGibbsSpec Λ Φ β) x y ≤
        1 - Real.exp (-(2 * δ)) := by
      apply influenceCoeff_le_of_cylinder_ratio_bound_nocount _ x y
        (2 * δ) (mul_nonneg (by norm_num) hδ)
      intro σ τ hστ B hB
      exact (boxEnergy Λ Φ β).conditionalMeasure_cylinder_ratio_centered
        (GaugeHaarProbability.haar G) x σ τ
        (β * actionAwayFromEdge Λ Φ x σ)
        (β * actionAwayFromEdge Λ Φ x τ) δ hδ
        (fun u => boxEnergy_centered_singleton_sub_le
          Λ Φ β x y u σ τ hστ) B hB
    _ ≤ 2 * δ := by
      have h := Real.one_sub_le_exp_neg (2 * δ)
      linarith
    _ = boxPairInfluenceBound d Φ.bound β := by
      dsimp [δ, boxPairInfluenceBound]
      ring

/-- Noninteracting edge pairs have zero Dobrushin influence. -/
theorem box_influenceCoeff_eq_zero_of_not_shares
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (x y : Λ.dynamicEdges)
    (hshare : ¬sharesActivePlaquette Λ x y) :
    influenceCoeff (boxGibbsSpec Λ Φ β) x y = 0 := by
  have hle : influenceCoeff (boxGibbsSpec Λ Φ β) x y ≤
      1 - Real.exp (-0) := by
    apply influenceCoeff_le_of_cylinder_ratio_bound_nocount
      (boxGibbsSpec Λ Φ β) x y 0 le_rfl
    intro σ τ hστ B hB
    simpa [boxGibbsSpec] using
      ((boxEnergy Λ Φ β).conditionalMeasure_cylinder_ratio_centered
        (GaugeHaarProbability.haar G) x σ τ
        (β * actionAwayFromEdge Λ Φ x σ)
        (β * actionAwayFromEdge Λ Φ x τ) 0 le_rfl
        (fun u => by
          rw [boxEnergy_centered_singleton_eq_of_not_shares
            Λ Φ β x y u σ τ hστ hshare]
          simp) B hB)
  apply le_antisymm
  · simpa using hle
  · exact influenceCoeff_nonneg _ _ _

/-! ## Interaction graph and row/column sums -/

/-- All positive edges occurring in an active plaquette incident to `x`. -/
def edgeNeighborCandidates (Λ : FiniteSpecification d G)
    (x : Λ.dynamicEdges) : Finset (PositiveEdge d) :=
  (edgePlaquettes Λ x).biUnion fun p => p.boundary.edgeSupport

theorem card_edgeNeighborCandidates_le
    (Λ : FiniteSpecification d G) (x : Λ.dynamicEdges) :
    (edgeNeighborCandidates Λ x).card ≤ 16 * d := by
  classical
  calc
    (edgeNeighborCandidates Λ x).card ≤
        ∑ p ∈ edgePlaquettes Λ x, p.boundary.edgeSupport.card := by
      simpa [edgeNeighborCandidates] using
        (Finset.card_biUnion_le (s := edgePlaquettes Λ x)
          (t := fun p => p.boundary.edgeSupport))
    _ ≤ ∑ _p ∈ edgePlaquettes Λ x, 4 := by
      apply Finset.sum_le_sum
      intro p _
      rw [plaquette_boundary_edgeSupport]
      exact Finset.card_le_four
    _ = (edgePlaquettes Λ x).card * 4 := by simp
    _ ≤ (4 * d) * 4 := Nat.mul_le_mul_right 4 (card_edgePlaquettes_le Λ x)
    _ = 16 * d := by omega

/-- Dynamic neighbors of `x`, excluding `x` itself. -/
def edgeNeighbors (Λ : FiniteSpecification d G)
    (x : Λ.dynamicEdges) : Finset Λ.dynamicEdges := by
  classical
  exact Finset.univ.filter fun y => y ≠ x ∧ sharesActivePlaquette Λ x y

theorem card_edgeNeighbors_le
    (Λ : FiniteSpecification d G) (x : Λ.dynamicEdges) :
    (edgeNeighbors Λ x).card ≤ 16 * d := by
  classical
  let valEmbedding : Λ.dynamicEdges ↪ PositiveEdge d :=
    ⟨Subtype.val, Subtype.val_injective⟩
  calc
    (edgeNeighbors Λ x).card =
        ((edgeNeighbors Λ x).map valEmbedding).card := by simp
    _ ≤ (edgeNeighborCandidates Λ x).card := by
      apply Finset.card_le_card
      intro e he
      rcases Finset.mem_map.mp he with ⟨y, hy, rfl⟩
      rcases (Finset.mem_filter.mp hy).2.2 with ⟨p, hp, hxp, hyp⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hxp⟩, hyp⟩
    _ ≤ 16 * d := card_edgeNeighborCandidates_le Λ x

theorem mem_edgeNeighbors_symm
    (Λ : FiniteSpecification d G) (x y : Λ.dynamicEdges) :
    y ∈ edgeNeighbors Λ x ↔ x ∈ edgeNeighbors Λ y := by
  classical
  constructor
  · intro h
    have h' := (Finset.mem_filter.mp h).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, h'.1.symm, sharesActivePlaquette_symm Λ h'.2⟩
  · intro h
    have h' := (Finset.mem_filter.mp h).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, h'.1.symm, sharesActivePlaquette_symm Λ h'.2⟩

/-- The finite simple graph generated by active plaquette interactions. -/
def edgeInteractionGraph (Λ : FiniteSpecification d G) :
    SimpleGraph Λ.dynamicEdges where
  Adj x y := x ≠ y ∧ sharesActivePlaquette Λ x y
  symm _ _ h := ⟨h.1.symm, sharesActivePlaquette_symm Λ h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (Λ : FiniteSpecification d G) :
    DecidableRel (edgeInteractionGraph Λ).Adj := Classical.decRel _

theorem box_influenceCoeff_le_neighborIndicator
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (x y : Λ.dynamicEdges) :
    influenceCoeff (boxGibbsSpec Λ Φ β) x y ≤
      if y ∈ edgeNeighbors Λ x then
        boxPairInfluenceBound d Φ.bound β else 0 := by
  classical
  by_cases hxy : y = x
  · subst y
    simp [edgeNeighbors, influenceCoeff_self_eq_zero_nocount]
  · by_cases hshare : sharesActivePlaquette Λ x y
    · have hy : y ∈ edgeNeighbors Λ x :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy, hshare⟩
      rw [if_pos hy]
      exact box_influenceCoeff_le Λ Φ β x y
    · simp [edgeNeighbors, hxy, hshare,
        box_influenceCoeff_eq_zero_of_not_shares Λ Φ β x y]

/-- A volume-independent Dobrushin contraction constant. -/
def boxDobrushinAlpha (d : ℕ) (B β : ℝ) : ℝ :=
  (16 * d) * boxPairInfluenceBound d B β

/-- An explicit positive radius ensuring the arbitrary-box Dobrushin
criterion.  The harmless `1 +` makes the radius positive even when the
interaction bound vanishes. -/
def boxDobrushinRadius (d : ℕ) (B : ℝ) : ℝ :=
  (1 + (16 * d : ℝ) * (16 * d * B))⁻¹

theorem boxDobrushinRadius_pos (B : ℝ) (hB : 0 ≤ B) :
    0 < boxDobrushinRadius d B := by
  apply inv_pos.mpr
  have : 0 ≤ (16 * d : ℝ) * (16 * d * B) := by positivity
  linarith

theorem boxDobrushinAlpha_lt_one_of_abs_lt_radius
    (B β : ℝ) (hB : 0 ≤ B)
    (hβ : |β| < boxDobrushinRadius d B) :
    boxDobrushinAlpha d B β < 1 := by
  let K : ℝ := (16 * d : ℝ) * (16 * d * B)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have halpha : boxDobrushinAlpha d B β = K * |β| := by
    dsimp [boxDobrushinAlpha, boxPairInfluenceBound, K]
    ring
  have hradius : boxDobrushinRadius d B = (1 + K)⁻¹ := by
    rfl
  rw [hradius] at hβ
  rw [halpha]
  by_cases hKzero : K = 0
  · simp [hKzero]
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
    calc
      K * |β| < K * (1 + K)⁻¹ :=
        mul_lt_mul_of_pos_left hβ hKpos
      _ = K / (1 + K) := by rw [div_eq_mul_inv]
      _ < 1 := (div_lt_one (by linarith)).2 (by linarith)

theorem boxDobrushinAlpha_nonneg (B β : ℝ) (hB : 0 ≤ B) :
    0 ≤ boxDobrushinAlpha d B β := by
  unfold boxDobrushinAlpha
  exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
    (boxPairInfluenceBound_nonneg B β hB)

theorem box_influence_row_sum_le
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (x : Λ.dynamicEdges) :
    ∑' y, influenceCoeff (boxGibbsSpec Λ Φ β) x y ≤
      boxDobrushinAlpha d Φ.bound β := by
  classical
  rw [tsum_fintype]
  calc
    ∑ y, influenceCoeff (boxGibbsSpec Λ Φ β) x y ≤
        ∑ y, if y ∈ edgeNeighbors Λ x then
          boxPairInfluenceBound d Φ.bound β else 0 := by
      apply Finset.sum_le_sum
      intro y _
      exact box_influenceCoeff_le_neighborIndicator Λ Φ β x y
    _ = (edgeNeighbors Λ x).card *
        boxPairInfluenceBound d Φ.bound β := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul]
      rw [show ({y | y ∈ edgeNeighbors Λ x} : Finset Λ.dynamicEdges) =
          edgeNeighbors Λ x by ext y; simp]
    _ ≤ (16 * d) * boxPairInfluenceBound d Φ.bound β := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_edgeNeighbors_le Λ x
      · exact boxPairInfluenceBound_nonneg Φ.bound β Φ.bound_nonneg
    _ = boxDobrushinAlpha d Φ.bound β := rfl

theorem box_influence_column_sum_le
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (y : Λ.dynamicEdges) :
    ∑' x, influenceCoeff (boxGibbsSpec Λ Φ β) x y ≤
      boxDobrushinAlpha d Φ.bound β := by
  classical
  rw [tsum_fintype]
  calc
    ∑ x, influenceCoeff (boxGibbsSpec Λ Φ β) x y ≤
        ∑ x, if x ∈ edgeNeighbors Λ y then
          boxPairInfluenceBound d Φ.bound β else 0 := by
      apply Finset.sum_le_sum
      intro x _
      simpa only [mem_edgeNeighbors_symm Λ x y] using
        (box_influenceCoeff_le_neighborIndicator Λ Φ β x y)
    _ = (edgeNeighbors Λ y).card *
        boxPairInfluenceBound d Φ.bound β := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul]
      rw [show ({x | x ∈ edgeNeighbors Λ y} : Finset Λ.dynamicEdges) =
          edgeNeighbors Λ y by ext x; simp]
    _ ≤ (16 * d) * boxPairInfluenceBound d Φ.bound β := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_edgeNeighbors_le Λ y
      · exact boxPairInfluenceBound_nonneg Φ.bound β Φ.bound_nonneg
    _ = boxDobrushinAlpha d Φ.bound β := rfl

/-- The arbitrary-box Yang--Mills specification satisfies Dobrushin's
criterion whenever the explicit volume-independent constant is below one. -/
def box_dobrushinCondition
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (hsmall : boxDobrushinAlpha d Φ.bound β < 1) :
    DobrushinCondition (boxGibbsSpec Λ Φ β) where
  α := boxDobrushinAlpha d Φ.bound β
  hα_pos := boxDobrushinAlpha_nonneg Φ.bound β Φ.bound_nonneg
  hα_lt := hsmall
  col_summable := fun _ => summable_of_hasFiniteSupport (Set.toFinite _)
  column_bound := box_influence_column_sum_le Λ Φ β
  row_summable := fun _ => summable_of_hasFiniteSupport (Set.toFinite _)
  row_bound := box_influence_row_sum_le Λ Φ β

/-- Dobrushin certificate under the explicit positive-radius hypothesis. -/
def box_dobrushinCondition_of_abs_lt_radius
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (hβ : |β| < boxDobrushinRadius d Φ.bound) :
    DobrushinCondition (boxGibbsSpec Λ Φ β) :=
  box_dobrushinCondition Λ Φ β
    (boxDobrushinAlpha_lt_one_of_abs_lt_radius
      Φ.bound β Φ.bound_nonneg hβ)

/-! ## A genuine finite graph metric -/

/-- Shortest-path distance, with different connected components placed at
distance `|V|`.  Unlike `SimpleGraph.dist` itself, this is a genuine
finite-valued metric even for a disconnected finite graph. -/
def completedGraphDist {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (x y : V) : ℕ :=
  if H.Reachable x y then H.dist x y else Fintype.card V

theorem completedGraphDist_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x y : V) :
    completedGraphDist (H := H) x y ≤ Fintype.card V := by
  classical
  by_cases hxy : H.Reachable x y
  · rw [completedGraphDist, if_pos hxy]
    obtain ⟨p, hp⟩ := hxy.exists_isPath
    exact (H.dist_le p).trans (Nat.le_of_lt hp.length_lt)
  · simp [completedGraphDist, hxy]

@[simp]
theorem completedGraphDist_self {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x : V) :
    completedGraphDist (H := H) x x = 0 := by
  simp [completedGraphDist]

theorem completedGraphDist_triangle {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x y z : V) :
    completedGraphDist (H := H) x z ≤
      completedGraphDist (H := H) x y + completedGraphDist (H := H) y z := by
  classical
  by_cases hxy : H.Reachable x y
  · by_cases hyz : H.Reachable y z
    · have hxz : H.Reachable x z := hxy.trans hyz
      simp only [completedGraphDist, if_pos hxy, if_pos hyz, if_pos hxz]
      exact hyz.dist_triangle_right x
    · calc
        completedGraphDist (H := H) x z ≤ Fintype.card V :=
          completedGraphDist_le_card H x z
        _ ≤ completedGraphDist (H := H) x y +
            completedGraphDist (H := H) y z := by
          simp [completedGraphDist, hxy, hyz]
  · calc
      completedGraphDist (H := H) x z ≤ Fintype.card V :=
        completedGraphDist_le_card H x z
      _ ≤ completedGraphDist (H := H) x y +
          completedGraphDist (H := H) y z := by
        simp [completedGraphDist, hxy]

theorem box_influenceCoeff_eq_zero_of_completedGraphDist_gt_one
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G)
    (β : ℝ) (x y : Λ.dynamicEdges)
    (hxy : completedGraphDist (H := edgeInteractionGraph Λ) x y > 1) :
    influenceCoeff (boxGibbsSpec Λ Φ β) x y = 0 := by
  apply box_influenceCoeff_eq_zero_of_not_shares
  intro hshare
  have hne : x ≠ y := by
    intro h
    subst y
    simp at hxy
  have hadj : (edgeInteractionGraph Λ).Adj x y := ⟨hne, hshare⟩
  have hreach : (edgeInteractionGraph Λ).Reachable x y := hadj.reachable
  have hdist : (edgeInteractionGraph Λ).dist x y = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  rw [completedGraphDist, if_pos hreach, hdist] at hxy
  omega

end

end YangMills.StrongCoupling
