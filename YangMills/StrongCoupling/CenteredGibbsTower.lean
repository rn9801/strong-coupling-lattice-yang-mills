/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.CenteredBoundaryExpansion
import YangMills.StrongCoupling.BoxGibbs

/-!
# Gibbs towers for nested centered boxes

This file identifies a conditional fiber of a centered-box Gibbs law with
the Gibbs law in a smaller centered box, with the large configuration as its
frozen exterior field.  Together with the finite-product Gibbs tower, this
is the bridge from the uniform one-root cluster boundary estimate to a
genuine cross-volume Cauchy estimate.
-/

open MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume
open YangMills.Probability

noncomputable section

local instance centeredGibbsTowerDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- Centered active-plaquette sets are nested. -/
theorem centeredActivePlaquettes_mono {m n : ℕ} (hmn : m ≤ n) :
    centeredActivePlaquettes d m ⊆ centeredActivePlaquettes d n := by
  classical
  intro p hp
  rw [centeredActivePlaquettes, Finset.mem_biUnion] at hp ⊢
  obtain ⟨e, he, hep⟩ := hp
  exact ⟨e, centeredBox_positiveEdges_mono hmn he, hep⟩

/-- The coordinates of the radius-`m` box, regarded as a region inside the
dynamic coordinates of the radius-`n` box. -/
def centeredSubregion (m n : ℕ) (η : Configuration d G) :
    Finset (centeredSpecification n η).dynamicEdges :=
  Finset.univ.filter fun e => e.1 ∈ (centeredBox d m).positiveEdges

@[simp]
theorem mem_centeredSubregion {m n : ℕ} {η : Configuration d G}
    (e : (centeredSpecification n η).dynamicEdges) :
    e ∈ centeredSubregion m n η ↔
      e.1 ∈ (centeredBox d m).positiveEdges := by
  rw [centeredSubregion, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ e)

/-- Gluing a resampled smaller box inside a larger dynamic configuration is
the same full configuration as evaluating the smaller box with the induced
large-volume exterior field. -/
theorem evaluate_glue_centeredSubregion {m n : ℕ} (hmn : m ≤ n)
    (η : Configuration d G)
    (σ u : DynamicConfiguration (centeredSpecification n η)) :
    (centeredSpecification m
        ((centeredSpecification n η).evaluate σ)).evaluate
          (Gauge.ProductHaar.restrictOfFinsetSubset (G := G)
            (centeredBox_positiveEdges_mono hmn) u) =
      (centeredSpecification n η).evaluate
        (glue (centeredSubregion m n η) u σ) := by
  funext e
  by_cases hem : e ∈ (centeredBox d m).positiveEdges
  · have hen : e ∈ (centeredBox d n).positiveEdges :=
      centeredBox_positiveEdges_mono hmn hem
    rw [(centeredSpecification m
        ((centeredSpecification n η).evaluate σ)).evaluate_of_mem _ e hem,
      (centeredSpecification n η).evaluate_of_mem _ e hen]
    rw [glue_inside (centeredSubregion m n η) u σ
      ⟨e, hen⟩ ((mem_centeredSubregion ⟨e, hen⟩).2 hem)]
    rfl
  · rw [(centeredSpecification m
        ((centeredSpecification n η).evaluate σ)).evaluate_of_not_mem _ e hem]
    by_cases hen : e ∈ (centeredBox d n).positiveEdges
    · change (centeredSpecification n η).evaluate σ e =
        (centeredSpecification n η).evaluate
          (glue (centeredSubregion m n η) u σ) e
      rw [(centeredSpecification n η).evaluate_of_mem _ e hen,
        (centeredSpecification n η).evaluate_of_mem _ e hen]
      rw [glue_outside (centeredSubregion m n η) u σ
        ⟨e, hen⟩ (by simpa only [mem_centeredSubregion] using hem)]
    · change (centeredSpecification n η).evaluate σ e =
        (centeredSpecification n η).evaluate
          (glue (centeredSubregion m n η) u σ) e
      rw [(centeredSpecification n η).evaluate_of_not_mem _ e hen,
        (centeredSpecification n η).evaluate_of_not_mem _ e hen]

/-- A plaquette outside the smaller active set contains no smaller-box
dynamic edge. -/
theorem boundary_disjoint_centeredBox_of_not_active
    {m : ℕ} {p : Plaquette d} (hp : p ∉ centeredActivePlaquettes d m) :
    Disjoint p.boundary.edgeSupport (centeredBox d m).positiveEdges := by
  rw [Finset.disjoint_left]
  intro e hep hem
  apply hp
  rw [centeredActivePlaquettes, Finset.mem_biUnion]
  exact ⟨e, hem, mem_incidentPlaquettes_of_mem_boundary e p hep⟩

/-- Plaquette holonomies outside the smaller active set are constant along
the corresponding conditional fiber. -/
theorem plaquetteHolonomy_glue_centeredSubregion_of_not_active
    {m n : ℕ} (η : Configuration d G)
    (σ u : DynamicConfiguration (centeredSpecification n η))
    (p : Plaquette d) (hp : p ∉ centeredActivePlaquettes d m) :
    plaquetteHolonomy (centeredSpecification n η)
        (glue (centeredSubregion m n η) u σ) p =
      plaquetteHolonomy (centeredSpecification n η) σ p := by
  unfold plaquetteHolonomy
  apply Gauge.holonomy_eq_of_eqOn_edgeSupport
  intro e hep
  by_cases hen : e ∈ (centeredBox d n).positiveEdges
  · rw [(centeredSpecification n η).evaluate_of_mem _ e hen,
      (centeredSpecification n η).evaluate_of_mem _ e hen]
    have hem : e ∉ (centeredBox d m).positiveEdges := by
      intro hem
      exact (Finset.disjoint_left.mp
        (boundary_disjoint_centeredBox_of_not_active hp)) hep hem
    rw [glue_outside (centeredSubregion m n η) u σ
      ⟨e, hen⟩ (by simpa only [mem_centeredSubregion] using hem)]
  · rw [(centeredSpecification n η).evaluate_of_not_mem _ e hen,
      (centeredSpecification n η).evaluate_of_not_mem _ e hen]

/-- The contribution of large-box plaquettes outside the smaller centered
active set.  It is constant on a smaller-box conditional fiber. -/
def centeredOuterAction (m n : ℕ) (η : Configuration d G)
    (Φ : RealPlaquettePotential G)
    (σ : DynamicConfiguration (centeredSpecification n η)) : ℝ :=
  ∑ p ∈ centeredActivePlaquettes d n \ centeredActivePlaquettes d m,
    Φ (plaquetteHolonomy (centeredSpecification n η) σ p)

/-- The large action on a smaller-box conditional fiber is the induced
smaller action plus a fiber-constant outer contribution. -/
theorem action_glue_centeredSubregion {m n : ℕ} (hmn : m ≤ n)
    (η : Configuration d G) (Φ : RealPlaquettePotential G)
    (σ u : DynamicConfiguration (centeredSpecification n η)) :
    action (centeredSpecification n η) Φ
        (glue (centeredSubregion m n η) u σ) =
      action (centeredSpecification m
        ((centeredSpecification n η).evaluate σ)) Φ
          (Gauge.ProductHaar.restrictOfFinsetSubset (G := G)
            (centeredBox_positiveEdges_mono hmn) u) +
        centeredOuterAction m n η Φ σ := by
  classical
  let small := centeredActivePlaquettes d m
  let large := centeredActivePlaquettes d n
  let V := Gauge.ProductHaar.restrictOfFinsetSubset (G := G)
    (centeredBox_positiveEdges_mono hmn) u
  have hsub : small ⊆ large := centeredActivePlaquettes_mono hmn
  have hsmall : ∀ p ∈ small,
      plaquetteHolonomy (centeredSpecification n η)
          (glue (centeredSubregion m n η) u σ) p =
        plaquetteHolonomy (centeredSpecification m
          ((centeredSpecification n η).evaluate σ)) V p := by
    intro p _hp
    unfold plaquetteHolonomy
    apply congrArg (fun A => Gauge.holonomy A p.boundary)
    simpa only [V] using
      (evaluate_glue_centeredSubregion hmn η σ u).symm
  have houter : ∀ p ∈ large \ small,
      plaquetteHolonomy (centeredSpecification n η)
          (glue (centeredSubregion m n η) u σ) p =
        plaquetteHolonomy (centeredSpecification n η) σ p := by
    intro p hp
    exact plaquetteHolonomy_glue_centeredSubregion_of_not_active
      η σ u p (Finset.mem_sdiff.mp hp).2
  have houtsum :
      (∑ p ∈ large \ small,
        Φ (plaquetteHolonomy (centeredSpecification n η)
          (glue (centeredSubregion m n η) u σ) p)) =
        ∑ p ∈ large \ small,
          Φ (plaquetteHolonomy (centeredSpecification n η) σ p) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [houter p hp]
  have hsmallsum :
      (∑ p ∈ small,
        Φ (plaquetteHolonomy (centeredSpecification n η)
          (glue (centeredSubregion m n η) u σ) p)) =
        ∑ p ∈ small,
          Φ (plaquetteHolonomy (centeredSpecification m
            ((centeredSpecification n η).evaluate σ)) V p) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hsmall p hp]
  change (∑ p ∈ large,
      Φ (plaquetteHolonomy (centeredSpecification n η)
        (glue (centeredSubregion m n η) u σ) p)) =
    (∑ p ∈ small,
      Φ (plaquetteHolonomy (centeredSpecification m
        ((centeredSpecification n η).evaluate σ)) V p)) +
      ∑ p ∈ large \ small,
        Φ (plaquetteHolonomy (centeredSpecification n η) σ p)
  calc
    (∑ p ∈ large, Φ (plaquetteHolonomy (centeredSpecification n η)
        (glue (centeredSubregion m n η) u σ) p)) =
        (∑ p ∈ large \ small,
          Φ (plaquetteHolonomy (centeredSpecification n η)
            (glue (centeredSubregion m n η) u σ) p)) +
          ∑ p ∈ small,
            Φ (plaquetteHolonomy (centeredSpecification n η)
              (glue (centeredSubregion m n η) u σ) p) :=
      (Finset.sum_sdiff hsub).symm
    _ = (∑ p ∈ large \ small,
          Φ (plaquetteHolonomy (centeredSpecification n η) σ p)) +
        ∑ p ∈ small,
          Φ (plaquetteHolonomy (centeredSpecification m
            ((centeredSpecification n η).evaluate σ)) V p) := by
      rw [houtsum, hsmallsum]
    _ = _ := add_comm _ _

/-- Restricting after gluing the smaller region simply recovers the
restricted resampling configuration. -/
theorem restrict_glue_centeredSubregion {m n : ℕ} (hmn : m ≤ n)
    (η : Configuration d G)
    (σ u : DynamicConfiguration (centeredSpecification n η)) :
    Gauge.ProductHaar.restrictOfFinsetSubset (G := G)
        (centeredBox_positiveEdges_mono hmn)
        (glue (centeredSubregion m n η) u σ) =
      Gauge.ProductHaar.restrictOfFinsetSubset (G := G)
        (centeredBox_positiveEdges_mono hmn) u := by
  funext e
  change glue (centeredSubregion m n η) u σ
      ⟨e.1, centeredBox_positiveEdges_mono hmn e.2⟩ =
    u ⟨e.1, centeredBox_positiveEdges_mono hmn e.2⟩
  rw [glue_inside (centeredSubregion m n η) u σ
    ⟨e.1, centeredBox_positiveEdges_mono hmn e.2⟩
    ((mem_centeredSubregion
      ⟨e.1, centeredBox_positiveEdges_mono hmn e.2⟩).2 e.2)]

/-- The smaller centered-box energy, pulled back to the larger dynamic
coordinate family by coordinate restriction. -/
def centeredInnerEnergy {m n : ℕ} (hmn : m ≤ n)
    (η : Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (σ : DynamicConfiguration (centeredSpecification n η)) :
    FiniteEnergy (centeredSpecification n η).dynamicEdges G where
  energy := fun u => β * action
    (centeredSpecification m ((centeredSpecification n η).evaluate σ)) Φ
    (Gauge.ProductHaar.restrictOfFinsetSubset (G := G)
      (centeredBox_positiveEdges_mono hmn) u)
  measurable_energy := measurable_const.mul
    ((continuous_action
      (centeredSpecification m ((centeredSpecification n η).evaluate σ)) Φ).measurable.comp
        (Gauge.ProductHaar.measurePreserving_restrictOfFinsetSubset
          (G := G) (centeredBox_positiveEdges_mono hmn)).measurable)
  bound := |β| * actionBound
    (centeredSpecification m ((centeredSpecification n η).evaluate σ)) Φ
  bound_nonneg := mul_nonneg (abs_nonneg _)
    (actionBound_nonneg _ _)
  norm_energy_le := fun u => by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_action_le _ _ _) (abs_nonneg β)

@[simp]
theorem centeredInnerEnergy_apply {m n : ℕ} (hmn : m ≤ n)
    (η : Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (σ u : DynamicConfiguration (centeredSpecification n η)) :
    centeredInnerEnergy hmn η Φ β σ u =
      β * action
        (centeredSpecification m ((centeredSpecification n η).evaluate σ)) Φ
        (Gauge.ProductHaar.restrictOfFinsetSubset (G := G)
          (centeredBox_positiveEdges_mono hmn) u) :=
  rfl

/-- Removing the fiber-constant outer action identifies the large conditional
law with the pulled-back smaller-box energy. -/
theorem conditionalMeasure_boxEnergy_eq_centeredInnerEnergy
    {m n : ℕ} (hmn : m ≤ n)
    (η : Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (σ : DynamicConfiguration (centeredSpecification n η)) :
    (boxEnergy (centeredSpecification n η) Φ β).conditionalMeasure
        (GaugeHaarProbability.haar G) (centeredSubregion m n η) σ =
      (centeredInnerEnergy hmn η Φ β σ).conditionalMeasure
        (GaugeHaarProbability.haar G) (centeredSubregion m n η) σ := by
  apply (boxEnergy (centeredSpecification n η) Φ β).conditionalMeasure_eq_of_add_const
    (GaugeHaarProbability.haar G)
    (centeredInnerEnergy hmn η Φ β σ)
    (centeredSubregion m n η) σ
    (β * centeredOuterAction m n η Φ σ)
  intro u
  rw [boxEnergy_apply, centeredInnerEnergy_apply,
    action_glue_centeredSubregion hmn η Φ σ u]
  have hrestrict := restrict_glue_centeredSubregion hmn η σ u
  have haction := congrArg
    (action (centeredSpecification m
      ((centeredSpecification n η).evaluate σ)) Φ) hrestrict
  rw [mul_add]
  exact congrArg (fun x : ℝ =>
    β * x + β * centeredOuterAction m n η Φ σ) haction.symm

/-- A conditional expectation in the large centered box is exactly the
smaller centered-box Gibbs expectation with the large configuration as its
induced exterior field. -/
theorem integral_conditionalMeasure_eq_centered_complexGibbsExpectation
    {m n : ℕ} (hmn : m ≤ n)
    (η : Configuration d G) (F : LocalObservable d G)
    (Φ : RealPlaquettePotential G) (β : ℝ)
    (σ : DynamicConfiguration (centeredSpecification n η)) :
    ∫ τ, F ((centeredSpecification n η).evaluate τ)
        ∂(boxEnergy (centeredSpecification n η) Φ β).conditionalMeasure
          (GaugeHaarProbability.haar G) (centeredSubregion m n η) σ =
      complexGibbsExpectation F
        (centeredSpecification m
          ((centeredSpecification n η).evaluate σ)) Φ (β : ℂ) := by
  let Λn := centeredSpecification n η
  let Λm := centeredSpecification m (Λn.evaluate σ)
  let R : DynamicConfiguration Λn → DynamicConfiguration Λm :=
    Gauge.ProductHaar.restrictOfFinsetSubset (G := G)
      (centeredBox_positiveEdges_mono hmn)
  let Ein := centeredInnerEnergy hmn η Φ β σ
  have hfmeas : Measurable (fun τ : DynamicConfiguration Λn =>
      F (Λn.evaluate τ)) :=
    F.toContinuousMap.continuous.measurable.comp Λn.continuous_evaluate.measurable
  rw [conditionalMeasure_boxEnergy_eq_centeredInnerEnergy hmn η Φ β σ]
  rw [Ein.integral_conditionalMeasure_complex_eq_div
    (GaugeHaarProbability.haar G) (centeredSubregion m n η) σ
    (fun τ => F (Λn.evaluate τ)) hfmeas
    ‖F.toBoundedContinuousMap‖ (fun τ => F.norm_apply_le (Λn.evaluate τ))]
  have hden : Ein.conditionalZ (GaugeHaarProbability.haar G)
      (centeredSubregion m n η) σ = partitionFunction Λm Φ β := by
    change (∫ u, Real.exp (Ein
      (glue (centeredSubregion m n η) u σ)) ∂Λn.haarMeasure) =
        partitionFunction Λm Φ β
    calc
      (∫ u, Real.exp (Ein
          (glue (centeredSubregion m n η) u σ)) ∂Λn.haarMeasure) =
          ∫ u, boltzmannWeight Λm Φ β (R u) ∂Λn.haarMeasure := by
        apply integral_congr_ae
        exact ae_of_all _ fun u => by
          change Real.exp (β * action Λm Φ
              (R (glue (centeredSubregion m n η) u σ))) =
            Real.exp (β * action Λm Φ (R u))
          apply congrArg Real.exp
          apply congrArg (fun x : ℝ => β * x)
          exact congrArg (action Λm Φ)
            (restrict_glue_centeredSubregion hmn η σ u)
      _ = ∫ v, boltzmannWeight Λm Φ β v ∂Λm.haarMeasure := by
        exact Gauge.ProductHaar.integral_restrictOfFinsetSubset
          (G := G) (centeredBox_positiveEdges_mono hmn)
          (boltzmannWeight Λm Φ β)
          (continuous_boltzmannWeight Λm Φ β).measurable
      _ = partitionFunction Λm Φ β := rfl
  have hnum :
      (∫ u, (Real.exp (Ein
          (glue (centeredSubregion m n η) u σ)) : ℂ) *
          F (Λn.evaluate (glue (centeredSubregion m n η) u σ))
          ∂Λn.haarMeasure) =
        complexObservableNumerator F Λm Φ (β : ℂ) := by
    calc
      (∫ u, (Real.exp (Ein
          (glue (centeredSubregion m n η) u σ)) : ℂ) *
          F (Λn.evaluate (glue (centeredSubregion m n η) u σ))
          ∂Λn.haarMeasure) =
          ∫ u, complexBoltzmannWeight Λm Φ (β : ℂ) (R u) *
            F (Λm.evaluate (R u)) ∂Λn.haarMeasure := by
        apply integral_congr_ae
        exact ae_of_all _ fun u => by
          have hr : R (glue (centeredSubregion m n η) u σ) = R u := by
            simpa only [R, Λn, Λm] using
              restrict_glue_centeredSubregion hmn η σ u
          have ha := congrArg (action Λm Φ) hr
          have heval : Λm.evaluate (R u) =
              Λn.evaluate (glue (centeredSubregion m n η) u σ) := by
            simpa only [Λm, Λn, R] using
              evaluate_glue_centeredSubregion hmn η σ u
          change (Real.exp (β * action Λm Φ
              (R (glue (centeredSubregion m n η) u σ))) : ℂ) *
              F (Λn.evaluate
                (glue (centeredSubregion m n η) u σ)) =
            complexBoltzmannWeight Λm Φ (β : ℂ) (R u) *
              F (Λm.evaluate (R u))
          rw [complexBoltzmannWeight_ofReal]
          exact congrArg₂ (fun x y : ℂ => x * y)
            (congrArg (fun x : ℝ => (Real.exp (β * x) : ℂ)) ha)
            (congrArg F heval.symm)
      _ = ∫ v, complexBoltzmannWeight Λm Φ (β : ℂ) v *
          F (Λm.evaluate v) ∂Λm.haarMeasure := by
        exact Gauge.ProductHaar.integral_restrictOfFinsetSubset
          (G := G) (centeredBox_positiveEdges_mono hmn)
          (fun v => complexBoltzmannWeight Λm Φ (β : ℂ) v *
            F (Λm.evaluate v))
          ((continuous_complexBoltzmannWeight Λm Φ (β : ℂ)).mul
            (F.toContinuousMap.continuous.comp Λm.continuous_evaluate)).measurable
      _ = complexObservableNumerator F Λm Φ (β : ℂ) := rfl
  rw [hden]
  change (∫ u, (Real.exp (Ein
      (glue (centeredSubregion m n η) u σ)) : ℂ) *
      F (Λn.evaluate (glue (centeredSubregion m n η) u σ))
      ∂Λn.haarMeasure) / partitionFunction Λm Φ β =
    complexGibbsExpectation F Λm Φ (β : ℂ)
  rw [hnum, complexGibbsExpectation, complexPartitionFunction_ofReal]
  ring

/-- A larger centered-box expectation is the Gibbs average of smaller-box
expectations over the induced random exterior field. -/
theorem complexGibbsExpectation_eq_integral_centered_inducedExterior
    {m n : ℕ} (hmn : m ≤ n)
    (η : Configuration d G) (F : LocalObservable d G)
    (Φ : RealPlaquettePotential G) (β : ℝ) :
    complexGibbsExpectation F (centeredSpecification n η) Φ (β : ℂ) =
      ∫ σ, complexGibbsExpectation F
          (centeredSpecification m
            ((centeredSpecification n η).evaluate σ)) Φ (β : ℂ)
        ∂gibbsMeasure (centeredSpecification n η) Φ β := by
  let Λn := centeredSpecification n η
  let E := boxEnergy Λn Φ β
  let f : DynamicConfiguration Λn → ℂ := fun τ => F (Λn.evaluate τ)
  have hf : Measurable f :=
    F.toContinuousMap.continuous.measurable.comp Λn.continuous_evaluate.measurable
  have hB : ∀ τ, ‖f τ‖ ≤ ‖F.toBoundedContinuousMap‖ := fun τ =>
    F.norm_apply_le (Λn.evaluate τ)
  have htower := E.integral_conditionalMeasure_gibbsMeasure_complex
    (GaugeHaarProbability.haar G) (centeredSubregion m n η) f hf
    ‖F.toBoundedContinuousMap‖ hB
  rw [boxEnergy_gibbsMeasure_eq] at htower
  have hcond : (fun σ => ∫ τ, f τ
      ∂E.conditionalMeasure (GaugeHaarProbability.haar G)
        (centeredSubregion m n η) σ) =
      fun σ => complexGibbsExpectation F
        (centeredSpecification m (Λn.evaluate σ)) Φ (β : ℂ) := by
    funext σ
    simpa only [Λn, E, f] using
      integral_conditionalMeasure_eq_centered_complexGibbsExpectation
        hmn η F Φ β σ
  rw [hcond] at htower
  rw [complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact htower.symm

/-- Comparing a larger centered box with any prescribed boundary condition
in a smaller centered box costs only the uniform smaller-box boundary tail. -/
theorem norm_complexGibbsExpectation_large_sub_centered_le_of_uniform
    {m n : ℕ} (hmn : m ≤ n)
    (ηn ηm : Configuration d G) (F : LocalObservable d G)
    (Φ : RealPlaquettePotential G) (β : ℝ) (C : ℝ)
    (hC : ∀ ξ : Configuration d G,
      ‖complexGibbsExpectation F (centeredSpecification m ξ) Φ (β : ℂ) -
        complexGibbsExpectation F (centeredSpecification m ηm) Φ (β : ℂ)‖ ≤ C) :
    ‖complexGibbsExpectation F (centeredSpecification n ηn) Φ (β : ℂ) -
        complexGibbsExpectation F (centeredSpecification m ηm) Φ (β : ℂ)‖ ≤ C := by
  let Λn := centeredSpecification n ηn
  let μ := gibbsMeasure Λn Φ β
  let g : DynamicConfiguration Λn → ℂ := fun σ =>
    complexGibbsExpectation F
      (centeredSpecification m (Λn.evaluate σ)) Φ (β : ℂ)
  let c := complexGibbsExpectation F (centeredSpecification m ηm) Φ (β : ℂ)
  have hrepr := complexGibbsExpectation_eq_integral_centered_inducedExterior
    hmn ηn F Φ β
  have hgc : ∀ σ, ‖g σ - c‖ ≤ C := fun σ => hC (Λn.evaluate σ)
  have hgmeas : Measurable g := by
    let E := boxEnergy Λn Φ β
    let f : DynamicConfiguration Λn → ℂ := fun τ => F (Λn.evaluate τ)
    have hf : Measurable f :=
      F.toContinuousMap.continuous.measurable.comp Λn.continuous_evaluate.measurable
    have hre : (fun σ => (g σ).re) = fun σ =>
        ∫ τ, (f τ).re ∂E.conditionalMeasure
          (GaugeHaarProbability.haar G) (centeredSubregion m n ηn) σ := by
      funext σ
      have hfiber :=
        integral_conditionalMeasure_eq_centered_complexGibbsExpectation
          hmn ηn F Φ β σ
      have hfint : Integrable f
          (E.conditionalMeasure (GaugeHaarProbability.haar G)
            (centeredSubregion m n ηn) σ) := by
        apply Integrable.of_bound hf.aestronglyMeasurable
          ‖F.toBoundedContinuousMap‖
        exact ae_of_all _ fun τ => F.norm_apply_le (Λn.evaluate τ)
      change (g σ).re = _
      calc
        (g σ).re =
            (∫ τ, f τ ∂E.conditionalMeasure
              (GaugeHaarProbability.haar G)
              (centeredSubregion m n ηn) σ).re := by
          exact congrArg Complex.re hfiber.symm
        _ = ∫ τ, (f τ).re ∂E.conditionalMeasure
              (GaugeHaarProbability.haar G)
              (centeredSubregion m n ηn) σ := (integral_re hfint).symm
    have him : (fun σ => (g σ).im) = fun σ =>
        ∫ τ, (f τ).im ∂E.conditionalMeasure
          (GaugeHaarProbability.haar G) (centeredSubregion m n ηn) σ := by
      funext σ
      have hfiber :=
        integral_conditionalMeasure_eq_centered_complexGibbsExpectation
          hmn ηn F Φ β σ
      have hfint : Integrable f
          (E.conditionalMeasure (GaugeHaarProbability.haar G)
            (centeredSubregion m n ηn) σ) := by
        apply Integrable.of_bound hf.aestronglyMeasurable
          ‖F.toBoundedContinuousMap‖
        exact ae_of_all _ fun τ => F.norm_apply_le (Λn.evaluate τ)
      change (g σ).im = _
      calc
        (g σ).im =
            (∫ τ, f τ ∂E.conditionalMeasure
              (GaugeHaarProbability.haar G)
              (centeredSubregion m n ηn) σ).im := by
          exact congrArg Complex.im hfiber.symm
        _ = ∫ τ, (f τ).im ∂E.conditionalMeasure
              (GaugeHaarProbability.haar G)
              (centeredSubregion m n ηn) σ := (integral_im hfint).symm
    have hre_meas : Measurable fun σ => (g σ).re := by
      rw [hre]
      exact E.measurable_integral_conditionalMeasure
        (GaugeHaarProbability.haar G) (centeredSubregion m n ηn)
        (fun τ => (f τ).re) (Complex.measurable_re.comp hf)
    have him_meas : Measurable fun σ => (g σ).im := by
      rw [him]
      exact E.measurable_integral_conditionalMeasure
        (GaugeHaarProbability.haar G) (centeredSubregion m n ηn)
        (fun τ => (f τ).im) (Complex.measurable_im.comp hf)
    have hrepr : g = fun σ => ((g σ).re : ℂ) +
        ((g σ).im : ℂ) * Complex.I := by
      funext σ
      apply Complex.ext <;> simp
    rw [hrepr]
    exact hre_meas.complex_ofReal.add
      (him_meas.complex_ofReal.mul measurable_const)
  have hgint : Integrable g μ := by
    apply Integrable.of_bound hgmeas.aestronglyMeasurable
      ‖F.toBoundedContinuousMap‖
    exact ae_of_all _ fun σ => by
      rw [show g σ = ∫ τ, F (Λn.evaluate τ)
          ∂(boxEnergy Λn Φ β).conditionalMeasure
            (GaugeHaarProbability.haar G) (centeredSubregion m n ηn) σ by
        symm
        exact integral_conditionalMeasure_eq_centered_complexGibbsExpectation
          hmn ηn F Φ β σ]
      simpa using norm_integral_le_of_norm_le_const
        (μ := (boxEnergy Λn Φ β).conditionalMeasure
          (GaugeHaarProbability.haar G) (centeredSubregion m n ηn) σ)
        (ae_of_all _ fun τ => F.norm_apply_le (Λn.evaluate τ))
  rw [hrepr]
  change ‖∫ σ, g σ ∂μ - c‖ ≤ C
  have hcint : Integrable (fun _ : DynamicConfiguration Λn => c) μ :=
    integrable_const c
  have hc : (∫ _ : DynamicConfiguration Λn, c ∂μ) = c := by simp [μ]
  rw [← hc, ← integral_sub hgint hcint]
  simpa [μ] using norm_integral_le_of_norm_le_const
    (μ := μ) (ae_of_all μ hgc)

/-- The cluster boundary tail controls two independently chosen centered
volumes and exterior fields once both volumes contain the prescribed ambient
cluster ball. -/
theorem norm_centered_complexGibbsExpectation_crossVolume_le_eventually
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound) (r : ℕ) :
    ∃ N, ∀ m n, N ≤ m → N ≤ n →
      ∀ ηm ηn : Configuration d G,
      ‖complexGibbsExpectation F (centeredSpecification m ηm) Φ (β : ℂ) -
        complexGibbsExpectation F (centeredSpecification n ηn) Φ (β : ℂ)‖ ≤
      2 * observableCardinalityTiltDecorationBudget (d := d) F Φ (β : ℂ) *
        plaquetteClusterDecayRate (d := d) Φ (β : ℂ) ^ r := by
  obtain ⟨N, hN⟩ :=
    norm_centered_complexGibbsExpectation_boundary_sub_le_eventually
      F Φ hβ r
  refine ⟨N, fun m n hm hn ηm ηn => ?_⟩
  by_cases hmn : m ≤ n
  · rw [norm_sub_rev]
    exact norm_complexGibbsExpectation_large_sub_centered_le_of_uniform
      hmn ηn ηm F Φ β _ (fun ξ => hN m hm ξ ηm)
  · have hnm : n ≤ m := Nat.le_of_not_ge hmn
    exact norm_complexGibbsExpectation_large_sub_centered_le_of_uniform
      hnm ηm ηn F Φ β _ (fun ξ => hN n hn ξ ηn)

/-- Local expectations along arbitrary centered exterior data form a Cauchy
sequence.  This is the direct thermodynamic-limit consequence of the
one-root cluster expansion and the centered Gibbs tower. -/
theorem cauchySeq_centered_localExpectation
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (F : LocalObservable d G) :
    CauchySeq (fun n => localExpectation (centeredGibbsSequence η Φ β n) F) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let B := 2 * observableCardinalityTiltDecorationBudget
    (d := d) F Φ (β : ℂ)
  let q := plaquetteClusterDecayRate (d := d) Φ (β : ℂ)
  have hq0 : 0 ≤ q := (plaquetteClusterDecayRate_pos Φ hβ).le
  have hq1 : q < 1 := plaquetteClusterDecayRate_lt_one Φ hβ
  have hmajorant : Filter.Tendsto (fun r : ℕ => B * q ^ r)
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul B
  have hevent : ∀ᶠ r in Filter.atTop, B * q ^ r < ε :=
    hmajorant (gt_mem_nhds hε)
  obtain ⟨r, hr⟩ := Filter.eventually_atTop.1 hevent
  obtain ⟨N, hN⟩ :=
    norm_centered_complexGibbsExpectation_crossVolume_le_eventually
      F Φ β hβ r
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  simpa only [centeredGibbsSequence,
    localExpectation_fullGibbsProbability, B, q] using
    (hN m n hm hn (η m) (η n)).trans_lt (hr r le_rfl)

end

end YangMills.StrongCoupling
