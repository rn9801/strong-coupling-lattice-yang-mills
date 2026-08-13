/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import MarkovSemigroups.Dobrushin.Specification
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Gibbs specifications on finite product probability spaces

This file isolates the measure-theoretic construction needed for arbitrary
finite Yang--Mills boxes.  Given a finite set of coordinates, a one-site
probability measure, and a bounded measurable energy, it defines the
conditional law obtained by resampling a region, gluing in the exterior
configuration, and exponentially tilting by the energy.

The gluing and product-measure arguments are adapted from Michael R. Douglas
and Fred Rajasekaran's Apache-2.0-licensed `LGT.Gibbs.YMSpec` and
`LGT.Gibbs.YMIsGibbs` modules at commit
`b8793ccf6a51e00e9e2b1685ba191b8626e37137`, in particular the upstream
`gluedConfig`, `glue_measurePreserving`, and `integral_glue_split_eq`
construction.  They are stated here without lattice- or gauge-specific
assumptions.
-/

open MeasureTheory

namespace YangMills.Probability

noncomputable section

variable {I S : Type*} [Fintype I] [DecidableEq I]
  [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The iid product of a one-site probability measure. -/
def productMeasure (ν : Measure S) : Measure (I → S) :=
  Measure.pi fun _ : I => ν

instance instIsProbabilityMeasureProductMeasure (ν : Measure S)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (productMeasure (I := I) ν) := by
  rw [productMeasure]
  infer_instance

/-- Replace the coordinates in `region` by those of `u`, retaining `σ`
outside the region.  Integrating a full iid configuration is intentional:
the unused coordinates have total mass one. -/
def glue (region : Finset I) (u σ : I → S) : I → S :=
  fun i => if i ∈ region then u i else σ i

@[simp]
theorem glue_inside (region : Finset I) (u σ : I → S)
    (i : I) (hi : i ∈ region) : glue region u σ i = u i := by
  simp [glue, hi]

@[simp]
theorem glue_outside (region : Finset I) (u σ : I → S)
    (i : I) (hi : i ∉ region) : glue region u σ i = σ i := by
  simp [glue, hi]

theorem glue_self (region : Finset I) (σ : I → S) :
    glue region σ σ = σ := by
  ext i
  simp [glue]

/-- Measurability in the resampled configuration. -/
theorem measurable_glue (region : Finset I) (σ : I → S) :
    Measurable (fun u : I → S => glue region u σ) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i ∈ region
  · simpa [glue, hi] using measurable_pi_apply i
  · simpa [glue, hi] using (measurable_const : Measurable fun _ : I → S => σ i)

/-- Joint measurability of gluing. -/
theorem measurable_glue_joint (region : Finset I) :
    Measurable (fun p : (I → S) × (I → S) => glue region p.2 p.1) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i ∈ region
  · simpa [glue, hi] using (measurable_pi_apply i).comp measurable_snd
  · simpa [glue, hi] using (measurable_pi_apply i).comp measurable_fst

/-- The iid product law is invariant under taking the coordinates in a
region from one independent sample and the remaining coordinates from a
second sample. -/
theorem measurePreserving_glue (ν : Measure S) [IsProbabilityMeasure ν]
    (region : Finset I) :
    MeasurePreserving
      (fun p : (I → S) × (I → S) => glue region p.2 p.1)
      ((productMeasure (I := I) ν).prod (productMeasure (I := I) ν))
      (productMeasure (I := I) ν) := by
  classical
  let γ : (I → S) × (I → S) → I → S :=
    fun p => glue region p.2 p.1
  have hγ : Measurable γ := measurable_glue_joint region
  refine ⟨hγ, ?_⟩
  show Measure.map γ
      ((Measure.pi fun _ : I => ν).prod (Measure.pi fun _ : I => ν)) =
        Measure.pi fun _ : I => ν
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  let a : I → Set S := fun i => if i ∈ region then Set.univ else s i
  let b : I → Set S := fun i => if i ∈ region then s i else Set.univ
  have ha : ∀ i, MeasurableSet (a i) := by
    intro i
    simp only [a]
    split_ifs
    · exact MeasurableSet.univ
    · exact hs i
  have hb : ∀ i, MeasurableSet (b i) := by
    intro i
    simp only [b]
    split_ifs
    · exact hs i
    · exact MeasurableSet.univ
  have hpre :
      γ ⁻¹' Set.pi Set.univ s =
        (Set.pi Set.univ a) ×ˢ (Set.pi Set.univ b) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_prod, a, b]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i ∈ region
        · simp [hi]
        · simp [hi]
          simpa [γ, glue, hi] using h i
      · by_cases hi : i ∈ region
        · simp [hi]
          simpa [γ, glue, hi] using h i
        · simp [hi]
    · rintro ⟨hp, hq⟩ i
      by_cases hi : i ∈ region
      · have := hq i
        simp [hi] at this
        simpa [γ, glue, hi] using this
      · have := hp i
        simp [hi] at this
        simpa [γ, glue, hi] using this
  calc
    (Measure.map γ ((Measure.pi fun _ : I => ν).prod
        (Measure.pi fun _ : I => ν))) (Set.univ.pi s) =
        ((Measure.pi fun _ : I => ν).prod (Measure.pi fun _ : I => ν))
          (γ ⁻¹' Set.univ.pi s) :=
      Measure.map_apply hγ (MeasurableSet.univ_pi hs)
    _ = ((Measure.pi fun _ : I => ν).prod (Measure.pi fun _ : I => ν))
          ((Set.pi Set.univ a) ×ˢ (Set.pi Set.univ b)) := by rw [hpre]
    _ = (Measure.pi fun _ : I => ν) (Set.pi Set.univ a) *
          (Measure.pi fun _ : I => ν) (Set.pi Set.univ b) :=
      Measure.prod_prod _ _
    _ = (∏ i, ν (a i)) * (∏ i, ν (b i)) := by
      rw [Measure.pi_pi, Measure.pi_pi]
    _ = ∏ i, ν (s i) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ region <;> simp [a, b, hi]

/-- Fubini through the coordinate-gluing map. -/
theorem integral_glue (ν : Measure S) [IsProbabilityMeasure ν]
    (region : Finset I) (f : (I → S) → ℝ)
    (hf : Integrable f (productMeasure (I := I) ν)) :
    ∫ σ, (∫ u, f (glue region u σ) ∂productMeasure (I := I) ν)
        ∂productMeasure (I := I) ν =
      ∫ U, f U ∂productMeasure (I := I) ν := by
  let γ : ((I → S) × (I → S)) → I → S :=
    fun p => glue region p.2 p.1
  have hγ : MeasurePreserving γ
      ((productMeasure (I := I) ν).prod (productMeasure (I := I) ν))
      (productMeasure (I := I) ν) := by
    simpa only [γ] using measurePreserving_glue (I := I) ν region
  have hcomp : Integrable (fun p => f (γ p))
      ((productMeasure (I := I) ν).prod (productMeasure (I := I) ν)) :=
    hγ.integrable_comp_of_integrable hf
  have hmap : productMeasure (I := I) ν =
      Measure.map γ ((productMeasure (I := I) ν).prod
        (productMeasure (I := I) ν)) := hγ.map_eq.symm
  have hchange :
      ∫ p, f (γ p) ∂((productMeasure (I := I) ν).prod
        (productMeasure (I := I) ν)) =
        ∫ U, f U ∂productMeasure (I := I) ν := by
    have hfm : AEStronglyMeasurable f
        (Measure.map γ ((productMeasure (I := I) ν).prod
          (productMeasure (I := I) ν))) := by
      rw [← hmap]
      exact hf.aestronglyMeasurable
    calc
      ∫ p, f (γ p) ∂((productMeasure (I := I) ν).prod
          (productMeasure (I := I) ν)) =
          ∫ U, f U ∂Measure.map γ
            ((productMeasure (I := I) ν).prod
              (productMeasure (I := I) ν)) :=
        (integral_map hγ.measurable.aemeasurable hfm).symm
      _ = ∫ U, f U ∂productMeasure (I := I) ν := by rw [← hmap]
  calc
    ∫ σ, (∫ u, f (glue region u σ) ∂productMeasure (I := I) ν)
        ∂productMeasure (I := I) ν =
      ∫ p, f (γ p) ∂((productMeasure (I := I) ν).prod
        (productMeasure (I := I) ν)) := by
      simpa only [γ] using
        (integral_prod (fun p => f (γ p)) hcomp).symm
    _ = ∫ U, f U ∂productMeasure (I := I) ν := hchange

/-- A bounded measurable energy on a finite product spin space. -/
structure FiniteEnergy (I S : Type*) [MeasurableSpace S] where
  energy : (I → S) → ℝ
  measurable_energy : Measurable energy
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_energy_le : ∀ σ, ‖energy σ‖ ≤ bound

namespace FiniteEnergy

variable (E : FiniteEnergy I S) (ν : Measure S) [IsProbabilityMeasure ν]

instance : CoeFun (FiniteEnergy I S) fun _ => (I → S) → ℝ :=
  ⟨FiniteEnergy.energy⟩

/-- Conditional partition function for resampling `region`. -/
def conditionalZ (region : Finset I) (σ : I → S) : ℝ :=
  ∫ u, Real.exp (E (glue region u σ)) ∂productMeasure (I := I) ν

theorem integrable_exp_glue (region : Finset I) (σ : I → S) :
    Integrable (fun u => Real.exp (E (glue region u σ)))
      (productMeasure (I := I) ν) := by
  apply Integrable.of_bound
    ((E.measurable_energy.comp (measurable_glue region σ)).exp.aestronglyMeasurable)
    (Real.exp E.bound)
  exact ae_of_all _ fun u => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using E.norm_energy_le (glue region u σ))

theorem conditionalZ_pos (region : Finset I) (σ : I → S) :
    0 < E.conditionalZ ν region σ := by
  exact integral_exp_pos (E.integrable_exp_glue ν region σ)

theorem conditionalZ_measurable (region : Finset I) :
    Measurable (E.conditionalZ ν region) := by
  let J : ((I → S) × (I → S)) → I → S :=
    fun p => glue region p.2 p.1
  have hJ : Measurable J := measurable_glue_joint region
  exact (E.measurable_energy.exp.comp hJ).stronglyMeasurable
    |>.integral_prod_right' |>.measurable

theorem exp_neg_bound_le_conditionalZ (region : Finset I) (σ : I → S) :
    Real.exp (-E.bound) ≤ E.conditionalZ ν region σ := by
  have hconst : Integrable (fun _ : I → S => Real.exp (-E.bound))
      (productMeasure (I := I) ν) := integrable_const _
  calc
    Real.exp (-E.bound) =
        ∫ _u, Real.exp (-E.bound) ∂productMeasure (I := I) ν := by simp
    _ ≤ ∫ u, Real.exp (E (glue region u σ))
          ∂productMeasure (I := I) ν := by
      apply integral_mono hconst (E.integrable_exp_glue ν region σ)
      intro u
      apply Real.exp_le_exp.mpr
      have h := E.norm_energy_le (glue region u σ)
      rw [Real.norm_eq_abs] at h
      exact (neg_le_of_abs_le h)
    _ = E.conditionalZ ν region σ := rfl

theorem conditionalZ_le_exp_bound (region : Finset I) (σ : I → S) :
    E.conditionalZ ν region σ ≤ Real.exp E.bound := by
  have hconst : Integrable (fun _ : I → S => Real.exp E.bound)
      (productMeasure (I := I) ν) := integrable_const _
  calc
    E.conditionalZ ν region σ =
        ∫ u, Real.exp (E (glue region u σ))
          ∂productMeasure (I := I) ν := rfl
    _ ≤ ∫ _u, Real.exp E.bound ∂productMeasure (I := I) ν := by
      apply integral_mono (E.integrable_exp_glue ν region σ) hconst
      intro u
      apply Real.exp_le_exp.mpr
      exact (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs] using E.norm_energy_le (glue region u σ))
    _ = Real.exp E.bound := by simp

/-- Conditional Boltzmann law on full configurations. -/
def conditionalMeasure (region : Finset I) (σ : I → S) :
    Measure (I → S) :=
  ((productMeasure (I := I) ν).map (fun u => glue region u σ)).tilted E.energy

instance instIsProbabilityMeasureConditionalMeasure
    (region : Finset I) (σ : I → S) :
    IsProbabilityMeasure (E.conditionalMeasure ν region σ) := by
  let μ := productMeasure (I := I) ν
  let g : (I → S) → I → S := fun u => glue region u σ
  letI : IsProbabilityMeasure (μ.map g) :=
    Measure.isProbabilityMeasure_map (measurable_glue region σ).aemeasurable
  apply isProbabilityMeasure_tilted
  have hmap : Integrable (fun U => Real.exp (E U))
      (μ.map g) := by
    apply (integrable_map_measure E.measurable_energy.exp.aestronglyMeasurable
      (measurable_glue region σ).aemeasurable).mpr
    simpa only [Function.comp_apply, g] using E.integrable_exp_glue ν region σ
  simpa only [conditionalMeasure, μ, g] using hmap

theorem conditionalMeasure_consistent (region : Finset I) (σ τ : I → S)
    (hστ : ∀ i, i ∉ region → σ i = τ i) :
    E.conditionalMeasure ν region σ = E.conditionalMeasure ν region τ := by
  have hglue : (fun u : I → S => glue region u σ) =
      fun u : I → S => glue region u τ := by
    funext u i
    by_cases hi : i ∈ region
    · simp [glue, hi]
    · simp [glue, hi, hστ i hi]
  simp only [conditionalMeasure, hglue]

theorem measurableSet_agreesOutside (region : Finset I) (σ : I → S) :
    MeasurableSet {τ : I → S | ∀ i, i ∉ region → τ i = σ i} := by
  have hset : {τ : I → S | ∀ i, i ∉ region → τ i = σ i} =
      ⋂ i ∈ (Finset.univ \ region : Finset I),
        (fun τ : I → S => τ i) ⁻¹' {σ i} := by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_sdiff,
      Finset.mem_univ, true_and, Set.mem_preimage, Set.mem_singleton_iff]
  rw [hset]
  exact MeasurableSet.biInter (Finset.univ \ region).countable_toSet
    (fun i _ => (measurable_pi_apply i) (measurableSet_singleton (σ i)))

theorem conditionalMeasure_proper (region : Finset I) (σ : I → S) :
    E.conditionalMeasure ν region σ
      {τ | ∀ i, i ∉ region → τ i = σ i} = 1 := by
  let A : Set (I → S) := {τ | ∀ i, i ∉ region → τ i = σ i}
  have hA : MeasurableSet A := measurableSet_agreesOutside region σ
  have hbase : ((productMeasure (I := I) ν).map
      (fun u => glue region u σ)) Aᶜ = 0 := by
    rw [Measure.map_apply (measurable_glue region σ) hA.compl]
    have hpre : (fun u : I → S => glue region u σ) ⁻¹' Aᶜ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hu (fun i hi => glue_outside region u σ i hi)
    rw [hpre, measure_empty]
  have htilt : E.conditionalMeasure ν region σ ≪
      (productMeasure (I := I) ν).map (fun u => glue region u σ) :=
    tilted_absolutelyContinuous _ _
  have hcomp : E.conditionalMeasure ν region σ Aᶜ = 0 := htilt hbase
  have hunion : A ∪ Aᶜ = Set.univ := Set.union_compl_self A
  have hsum : E.conditionalMeasure ν region σ Set.univ =
      E.conditionalMeasure ν region σ A +
        E.conditionalMeasure ν region σ Aᶜ := by
    rw [← hunion, measure_union disjoint_compl_right hA.compl]
  rw [show E.conditionalMeasure ν region σ Set.univ = 1 by simp,
    hcomp, add_zero] at hsum
  exact hsum.symm

/-- Explicit ratio-of-integrals formula for the conditional law. -/
theorem conditionalMeasure_apply_toReal (region : Finset I) (σ : I → S)
    (A : Set (I → S)) (hA : MeasurableSet A) :
    (E.conditionalMeasure ν region σ A).toReal =
      (∫ u, Set.indicator A (fun U => Real.exp (E U))
          (glue region u σ) ∂productMeasure (I := I) ν) /
        E.conditionalZ ν region σ := by
  let μ := productMeasure (I := I) ν
  let g : (I → S) → I → S := fun u => glue region u σ
  have hg : Measurable g := measurable_glue region σ
  have hden : (∫ U, Real.exp (E U) ∂μ.map g) =
      E.conditionalZ ν region σ := by
    rw [integral_map hg.aemeasurable
      E.measurable_energy.exp.aestronglyMeasurable]
    rfl
  calc
    (E.conditionalMeasure ν region σ A).toReal =
        ∫ U, Set.indicator A (fun _ => (1 : ℝ)) U
          ∂E.conditionalMeasure ν region σ :=
      (integral_indicator_one hA).symm
    _ = ∫ U, (Real.exp (E U) / ∫ V, Real.exp (E V) ∂μ.map g) *
          Set.indicator A (fun _ => (1 : ℝ)) U ∂μ.map g := by
      rw [conditionalMeasure, integral_tilted]
      rfl
    _ = ∫ u, (Real.exp (E (g u)) / ∫ V, Real.exp (E V) ∂μ.map g) *
          Set.indicator A (fun _ => (1 : ℝ)) (g u) ∂μ := by
      rw [integral_map]
      · exact hg.aemeasurable
      · exact ((E.measurable_energy.exp.div_const _).mul
          (measurable_const.indicator hA)).aestronglyMeasurable
    _ = (∫ u, Set.indicator A (fun U => Real.exp (E U))
          (g u) ∂μ) / E.conditionalZ ν region σ := by
      rw [hden]
      calc
        ∫ u, Real.exp (E (g u)) / E.conditionalZ ν region σ *
            Set.indicator A (fun _ => (1 : ℝ)) (g u) ∂μ =
          ∫ u, Set.indicator A (fun U => Real.exp (E U)) (g u) /
            E.conditionalZ ν region σ ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun u => by
            by_cases hu : g u ∈ A
            · simp [Set.indicator_of_mem hu]
            · simp [Set.indicator_of_notMem hu]
        _ = _ := integral_div (E.conditionalZ ν region σ)
          (fun u => Set.indicator A (fun U => Real.exp (E U)) (g u))
    _ = _ := rfl

/-- Measurability of the conditional law as a function of the exterior
configuration. -/
theorem measurable_conditionalMeasure_apply (region : Finset I)
    (A : Set (I → S)) (hA : MeasurableSet A) :
    Measurable fun σ : I → S =>
      (E.conditionalMeasure ν region σ A).toReal := by
  let W : (I → S) → ℝ := fun U => Real.exp (E U)
  have hW : Measurable W := E.measurable_energy.exp
  let J : ((I → S) × (I → S)) → I → S :=
    fun p => glue region p.2 p.1
  have hJ : Measurable J := measurable_glue_joint region
  let numerator : (I → S) → ℝ := fun σ =>
    ∫ u, Set.indicator A W (glue region u σ)
      ∂productMeasure (I := I) ν
  let denominator : (I → S) → ℝ := fun σ =>
    ∫ u, W (glue region u σ) ∂productMeasure (I := I) ν
  have hnum : Measurable numerator := by
    exact ((hW.indicator hA).comp hJ).stronglyMeasurable.integral_prod_right'.measurable
  have hden : Measurable denominator := by
    exact (hW.comp hJ).stronglyMeasurable.integral_prod_right'.measurable
  have hformula : (fun σ : I → S =>
      (E.conditionalMeasure ν region σ A).toReal) =
      fun σ => numerator σ / denominator σ := by
    funext σ
    rw [E.conditionalMeasure_apply_toReal ν region σ A hA]
    rfl
  rw [hformula]
  exact hnum.div hden

/-- The finite-product Gibbs specification generated by a bounded measurable
energy. -/
def gibbsSpec : GibbsSpec I S where
  condDist := fun region σ => E.conditionalMeasure ν region σ
  isProb := fun region σ => E.instIsProbabilityMeasureConditionalMeasure ν region σ
  consistent := fun region σ τ h => E.conditionalMeasure_consistent ν region σ τ h
  proper := fun region σ => E.conditionalMeasure_proper ν region σ
  measurable_condDist := fun region A hA =>
    E.measurable_conditionalMeasure_apply ν region A hA

@[simp]
theorem gibbsSpec_condDist (region : Finset I) (σ : I → S) :
    (E.gibbsSpec ν).condDist region σ = E.conditionalMeasure ν region σ :=
  rfl

/-- A uniform oscillation bound on the one-site conditional energy gives a
pointwise cylinder-probability ratio.  The factor `2` accounts for the
Boltzmann numerator and its normalizing partition function. -/
theorem conditionalMeasure_cylinder_ratio_centered
    (x : I) (σ τ : I → S) (cσ cτ δ : ℝ) (hδ : 0 ≤ δ)
    (henergy : ∀ u : I → S,
      |(E (glue {x} u τ) - cτ) - (E (glue {x} u σ) - cσ)| ≤ δ)
    (B : Set S) (hB : MeasurableSet B) :
    (E.conditionalMeasure ν {x} τ
        ((fun ρ : I → S => ρ x) ⁻¹' B)).toReal ≤
      Real.exp (2 * δ) *
        (E.conditionalMeasure ν {x} σ
          ((fun ρ : I → S => ρ x) ⁻¹' B)).toReal := by
  let A : Set (I → S) := (fun ρ => ρ x) ⁻¹' B
  have hA : MeasurableSet A := (measurable_pi_apply x) hB
  rw [E.conditionalMeasure_apply_toReal ν {x} τ A hA,
    E.conditionalMeasure_apply_toReal ν {x} σ A hA]
  let Nτ : ℝ := ∫ u, Set.indicator A (fun U => Real.exp (E U))
      (glue {x} u τ) ∂productMeasure (I := I) ν
  let Nσ : ℝ := ∫ u, Set.indicator A (fun U => Real.exp (E U))
      (glue {x} u σ) ∂productMeasure (I := I) ν
  let Zτ := E.conditionalZ ν {x} τ
  let Zσ := E.conditionalZ ν {x} σ
  have hmem : ∀ u, glue {x} u τ ∈ A ↔ glue {x} u σ ∈ A := by
    intro u
    simp [A, glue]
  have hweightτσ : ∀ u,
      Real.exp (E (glue {x} u τ)) ≤
        Real.exp (δ + cτ - cσ) * Real.exp (E (glue {x} u σ)) := by
    intro u
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := le_of_abs_le (henergy u)
    linarith
  have hweightστ : ∀ u,
      Real.exp (E (glue {x} u σ)) ≤
        Real.exp (δ + cσ - cτ) * Real.exp (E (glue {x} u τ)) := by
    intro u
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := neg_le_of_abs_le (henergy u)
    linarith
  have hN : Nτ ≤ Real.exp (δ + cτ - cσ) * Nσ := by
    calc
      Nτ = ∫ u, Set.indicator A (fun U => Real.exp (E U))
          (glue {x} u τ) ∂productMeasure (I := I) ν := rfl
      _ ≤ ∫ u, Real.exp (δ + cτ - cσ) *
          Set.indicator A (fun U => Real.exp (E U))
          (glue {x} u σ) ∂productMeasure (I := I) ν := by
        apply integral_mono
        · apply Integrable.mono (E.integrable_exp_glue ν {x} τ)
            ((E.measurable_energy.exp.indicator hA).comp
              (measurable_glue {x} τ)).aestronglyMeasurable
          exact ae_of_all _ fun u => by
            change ‖Set.indicator A (fun U => Real.exp (E U))
                (glue {x} u τ)‖ ≤ ‖Real.exp (E (glue {x} u τ))‖
            exact norm_indicator_le_norm_self
              (s := A) (f := fun U => Real.exp (E U)) (a := glue {x} u τ)
        · apply Integrable.const_mul
          apply Integrable.mono (E.integrable_exp_glue ν {x} σ)
            ((E.measurable_energy.exp.indicator hA).comp
              (measurable_glue {x} σ)).aestronglyMeasurable
          exact ae_of_all _ fun u => by
            change ‖Set.indicator A (fun U => Real.exp (E U))
                (glue {x} u σ)‖ ≤ ‖Real.exp (E (glue {x} u σ))‖
            exact norm_indicator_le_norm_self
              (s := A) (f := fun U => Real.exp (E U)) (a := glue {x} u σ)
        · intro u
          change Set.indicator A (fun U => Real.exp (E U)) (glue {x} u τ) ≤
            Real.exp (δ + cτ - cσ) *
              Set.indicator A (fun U => Real.exp (E U)) (glue {x} u σ)
          by_cases hu : glue {x} u τ ∈ A
          · rw [Set.indicator_of_mem hu,
              Set.indicator_of_mem ((hmem u).mp hu)]
            exact hweightτσ u
          · rw [Set.indicator_of_notMem hu,
              Set.indicator_of_notMem (fun h => hu ((hmem u).mpr h))]
            positivity
      _ = Real.exp (δ + cτ - cσ) * Nσ := by rw [integral_const_mul]
  have hZ : Zσ ≤ Real.exp (δ + cσ - cτ) * Zτ := by
    calc
      Zσ = ∫ u, Real.exp (E (glue {x} u σ))
          ∂productMeasure (I := I) ν := rfl
      _ ≤ ∫ u, Real.exp (δ + cσ - cτ) * Real.exp (E (glue {x} u τ))
          ∂productMeasure (I := I) ν := by
        apply integral_mono (E.integrable_exp_glue ν {x} σ)
          ((E.integrable_exp_glue ν {x} τ).const_mul
            (Real.exp (δ + cσ - cτ)))
        exact hweightστ
      _ = Real.exp (δ + cσ - cτ) * Zτ := by
        simp only [Zτ, conditionalZ, integral_const_mul]
  have hNσ_nonneg : 0 ≤ Nσ := integral_nonneg fun u =>
    Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  have hZτ_pos : 0 < Zτ := E.conditionalZ_pos ν {x} τ
  have hZσ_pos : 0 < Zσ := E.conditionalZ_pos ν {x} σ
  change Nτ / Zτ ≤ Real.exp (2 * δ) * (Nσ / Zσ)
  calc
    Nτ / Zτ ≤ (Real.exp (2 * δ) * Nσ) / Zσ := by
      apply (div_le_div_iff₀ hZτ_pos hZσ_pos).mpr
      calc
        Nτ * Zσ ≤ (Real.exp (δ + cτ - cσ) * Nσ) *
            (Real.exp (δ + cσ - cτ) * Zτ) :=
          mul_le_mul hN hZ hZσ_pos.le
            (mul_nonneg (Real.exp_pos _).le hNσ_nonneg)
        _ = (Real.exp (δ + cτ - cσ) *
              Real.exp (δ + cσ - cτ)) * Nσ * Zτ := by ring
        _ = Real.exp ((δ + cτ - cσ) + (δ + cσ - cτ)) * Nσ * Zτ := by
          rw [Real.exp_add]
        _ = Real.exp (2 * δ) * Nσ * Zτ := by
          congr 2
          ring
    _ = Real.exp (2 * δ) * (Nσ / Zσ) := by ring

/-- Uncentered form of `conditionalMeasure_cylinder_ratio_centered`. -/
theorem conditionalMeasure_cylinder_ratio
    (x : I) (σ τ : I → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (henergy : ∀ u : I → S,
      |E (glue {x} u τ) - E (glue {x} u σ)| ≤ δ)
    (B : Set S) (hB : MeasurableSet B) :
    (E.conditionalMeasure ν {x} τ
        ((fun ρ : I → S => ρ x) ⁻¹' B)).toReal ≤
      Real.exp (2 * δ) *
        (E.conditionalMeasure ν {x} σ
          ((fun ρ : I → S => ρ x) ⁻¹' B)).toReal := by
  exact E.conditionalMeasure_cylinder_ratio_centered ν x σ τ 0 0 δ hδ
    (fun u => by simpa using henergy u) B hB

/-- Adding a constant along one conditional fiber does not change its
normalized conditional law. -/
theorem conditionalMeasure_eq_of_add_const
    (E' : FiniteEnergy I S) (region : Finset I) (σ : I → S) (c : ℝ)
    (henergy : ∀ u : I → S,
      E (glue region u σ) = E' (glue region u σ) + c) :
    E.conditionalMeasure ν region σ =
      E'.conditionalMeasure ν region σ := by
  have hZ : E.conditionalZ ν region σ =
      Real.exp c * E'.conditionalZ ν region σ := by
    change (∫ u, Real.exp (E (glue region u σ))
        ∂productMeasure (I := I) ν) =
      Real.exp c *
        ∫ u, Real.exp (E' (glue region u σ))
          ∂productMeasure (I := I) ν
    calc
      ∫ u, Real.exp (E (glue region u σ))
          ∂productMeasure (I := I) ν =
        ∫ u, Real.exp c * Real.exp (E' (glue region u σ))
          ∂productMeasure (I := I) ν := by
            apply integral_congr_ae
            exact ae_of_all _ fun u => by
              change Real.exp (E (glue region u σ)) =
                Real.exp c * Real.exp (E' (glue region u σ))
              rw [henergy u, Real.exp_add, mul_comm]
      _ = _ := integral_const_mul _ _
  ext A hA
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (E.conditionalMeasure ν region σ) A)
    (measure_ne_top (E'.conditionalMeasure ν region σ) A)).mp
  rw [E.conditionalMeasure_apply_toReal ν region σ A hA,
    E'.conditionalMeasure_apply_toReal ν region σ A hA, hZ]
  have hN :
      (∫ u, Set.indicator A (fun U => Real.exp (E U))
          (glue region u σ) ∂productMeasure (I := I) ν) =
        Real.exp c *
          ∫ u, Set.indicator A (fun U => Real.exp (E' U))
            (glue region u σ) ∂productMeasure (I := I) ν := by
    calc
      ∫ u, Set.indicator A (fun U => Real.exp (E U))
          (glue region u σ) ∂productMeasure (I := I) ν =
        ∫ u, Real.exp c *
          Set.indicator A (fun U => Real.exp (E' U))
            (glue region u σ) ∂productMeasure (I := I) ν := by
          apply integral_congr_ae
          exact ae_of_all _ fun u => by
            change Set.indicator A (fun U => Real.exp (E U))
                (glue region u σ) =
              Real.exp c * Set.indicator A (fun U => Real.exp (E' U))
                (glue region u σ)
            by_cases hu : glue region u σ ∈ A
            · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu,
                henergy u, Real.exp_add, mul_comm]
            · simp [Set.indicator_of_notMem hu]
      _ = _ := integral_const_mul _ _
  rw [hN]
  field_simp [Real.exp_ne_zero]

/-- The globally normalized Gibbs law. -/
def gibbsMeasure : Measure (I → S) :=
  (productMeasure (I := I) ν).tilted E.energy

instance instIsProbabilityMeasureGibbsMeasure :
    IsProbabilityMeasure (E.gibbsMeasure ν) := by
  apply isProbabilityMeasure_tilted
  apply Integrable.of_bound E.measurable_energy.exp.aestronglyMeasurable
    (Real.exp E.bound)
  exact ae_of_all _ fun σ => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using E.norm_energy_le σ))

/-- A function unchanged by resampling `region` depends only on the exterior
coordinates. -/
def ExteriorMeasurable (region : Finset I) (h : (I → S) → ℝ) : Prop :=
  ∀ u σ, h (glue region u σ) = h σ

theorem conditionalZ_exterior (region : Finset I) :
    ExteriorMeasurable region (E.conditionalZ ν region) := by
  intro u σ
  apply integral_congr_ae
  exact ae_of_all _ fun v => by
    change Real.exp (E (glue region v (glue region u σ))) =
      Real.exp (E (glue region v σ))
    congr 1
    apply congrArg E.energy
    ext i
    by_cases hi : i ∈ region <;> simp [glue, hi]

/-- Integration identity behind the DLR cancellation. -/
theorem integral_mul_conditionalZ
    (region : Finset I) (h : (I → S) → ℝ)
    (hh_ext : ExteriorMeasurable region h)
    (hh_meas : Measurable h)
    (hhw_int : Integrable (fun U => h U * Real.exp (E U))
      (productMeasure (I := I) ν)) :
    ∫ σ, h σ * E.conditionalZ ν region σ
        ∂productMeasure (I := I) ν =
      ∫ U, h U * Real.exp (E U) ∂productMeasure (I := I) ν := by
  have hsplit := integral_glue (I := I) ν region
    (fun U => h U * Real.exp (E U)) hhw_int
  calc
    ∫ σ, h σ * E.conditionalZ ν region σ
        ∂productMeasure (I := I) ν =
      ∫ σ, (∫ u, h (glue region u σ) * Real.exp (E (glue region u σ))
          ∂productMeasure (I := I) ν) ∂productMeasure (I := I) ν := by
      apply integral_congr_ae
      exact ae_of_all _ fun σ => by
        change h σ * E.conditionalZ ν region σ = _
        change h σ * E.conditionalZ ν region σ =
          ∫ u, h (glue region u σ) * Real.exp (E (glue region u σ))
            ∂productMeasure (I := I) ν
        rw [show (∫ u, h (glue region u σ) * Real.exp (E (glue region u σ))
            ∂productMeasure (I := I) ν) =
            ∫ u, h σ * Real.exp (E (glue region u σ))
              ∂productMeasure (I := I) ν by
          apply integral_congr_ae
          exact ae_of_all _ fun u => by
            change h (glue region u σ) * Real.exp (E (glue region u σ)) =
              h σ * Real.exp (E (glue region u σ))
            rw [hh_ext u σ]]
        rw [integral_const_mul]
        rfl
    _ = ∫ U, h U * Real.exp (E U) ∂productMeasure (I := I) ν := hsplit

/-- Fiber-normalization cancellation.  A uniform bound is included so all
integrability obligations are discharged inside the reusable theorem. -/
theorem cancellation_identity
    (region : Finset I) (h : (I → S) → ℝ)
    (hh_ext : ExteriorMeasurable region h)
    (hh_meas : Measurable h)
    (B : ℝ) (hB : ∀ σ, |h σ| ≤ B) :
    ∫ σ, h σ * Real.exp (E σ) / E.conditionalZ ν region σ
        ∂productMeasure (I := I) ν =
      ∫ σ, h σ ∂productMeasure (I := I) ν := by
  let Z := E.conditionalZ ν region
  have hZpos : ∀ σ, 0 < Z σ := E.conditionalZ_pos ν region
  have hZmeas : Measurable Z := E.conditionalZ_measurable ν region
  have hquot_ext : ExteriorMeasurable region (fun σ => h σ / Z σ) := by
    intro u σ
    change h (glue region u σ) / Z (glue region u σ) = h σ / Z σ
    rw [hh_ext u σ]
    congr 1
    exact E.conditionalZ_exterior ν region u σ
  have hquot_meas : Measurable (fun σ => h σ / Z σ) := hh_meas.div hZmeas
  have hint : Integrable (fun U => (h U / Z U) * Real.exp (E U))
      (productMeasure (I := I) ν) := by
    apply Integrable.of_bound (hquot_meas.mul E.measurable_energy.exp).aestronglyMeasurable
      (max 0 B * Real.exp (2 * E.bound))
    exact ae_of_all _ fun U => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
        abs_of_pos (Real.exp_pos _), abs_of_pos (hZpos U)]
      have hhB : |h U| ≤ max 0 B := (hB U).trans (le_max_right _ _)
      have hEinv : (Z U)⁻¹ ≤ Real.exp E.bound := by
        calc
          (Z U)⁻¹ ≤ (Real.exp (-E.bound))⁻¹ :=
            (inv_le_inv₀ (hZpos U) (Real.exp_pos (-E.bound))).mpr
              (E.exp_neg_bound_le_conditionalZ ν region U)
          _ = Real.exp E.bound := by
            rw [← Real.exp_neg]
            simp
      have hE : Real.exp (E U) ≤ Real.exp E.bound :=
        Real.exp_le_exp.mpr ((le_abs_self _).trans (by
          simpa only [Real.norm_eq_abs] using E.norm_energy_le U))
      calc
        |h U| / Z U * Real.exp (E U) = |h U| * (Z U)⁻¹ * Real.exp (E U) := by
          rw [div_eq_mul_inv]
        _ ≤ max 0 B * Real.exp E.bound * Real.exp E.bound := by
          gcongr
          exact inv_nonneg.mpr (hZpos U).le
        _ = max 0 B * Real.exp (2 * E.bound) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  have hmain := E.integral_mul_conditionalZ ν region (fun σ => h σ / Z σ)
    hquot_ext hquot_meas hint
  have hlhs :
      ∫ σ, h σ / Z σ * Z σ ∂productMeasure (I := I) ν =
        ∫ σ, h σ ∂productMeasure (I := I) ν := by
    apply integral_congr_ae
    exact ae_of_all _ fun σ => by field_simp [(hZpos σ).ne']
  rw [hlhs] at hmain
  calc
    ∫ σ, h σ * Real.exp (E σ) / Z σ ∂productMeasure (I := I) ν =
        ∫ σ, (h σ / Z σ) * Real.exp (E σ)
          ∂productMeasure (I := I) ν := by
      apply integral_congr_ae
      exact ae_of_all _ fun σ => by ring
    _ = ∫ σ, h σ ∂productMeasure (I := I) ν := hmain.symm

/-- Finite-product Gibbs tower identity for bounded real observables.  A
global Gibbs expectation is the Gibbs average of its normalized conditional
expectations in any finite coordinate region. -/
theorem integral_conditionalMeasure_gibbsMeasure
    (region : Finset I) (f : (I → S) → ℝ)
    (hf : Measurable f) (B : ℝ) (hB : ∀ σ, |f σ| ≤ B) :
    ∫ σ, (∫ τ, f τ ∂E.conditionalMeasure ν region σ)
        ∂E.gibbsMeasure ν =
      ∫ σ, f σ ∂E.gibbsMeasure ν := by
  let μ := productMeasure (I := I) ν
  let W : (I → S) → ℝ := fun U => Real.exp (E U)
  let Z : ℝ := ∫ U, W U ∂μ
  let inner : (I → S) → ℝ := fun σ =>
    ∫ u, W (glue region u σ) * f (glue region u σ) ∂μ
  have hW_meas : Measurable W := E.measurable_energy.exp
  have hW_int : Integrable W μ := by
    apply Integrable.of_bound hW_meas.aestronglyMeasurable (Real.exp E.bound)
    exact ae_of_all _ fun U => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs] using E.norm_energy_le U))
  have hWf_int : Integrable (fun U => W U * f U) μ := by
    apply Integrable.of_bound (hW_meas.mul hf).aestronglyMeasurable
      (Real.exp E.bound * max 0 B)
    exact ae_of_all _ fun U => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      gcongr
      · exact (le_abs_self _).trans (by
          simpa only [Real.norm_eq_abs] using E.norm_energy_le U)
      · exact (hB U).trans (le_max_right _ _)
  have hinner_meas : Measurable inner := by
    let J : ((I → S) × (I → S)) → I → S :=
      fun p => glue region p.2 p.1
    have hJ : Measurable J := measurable_glue_joint region
    exact ((hW_meas.mul hf).comp hJ).stronglyMeasurable
      |>.integral_prod_right' |>.measurable
  have hinner_ext : ExteriorMeasurable region inner := by
    intro u σ
    apply integral_congr_ae
    exact ae_of_all _ fun v => by
      apply congrArg (fun U => W U * f U)
      ext i
      by_cases hi : i ∈ region <;> simp [glue, hi]
  have hinner_bound : ∀ σ, |inner σ| ≤ Real.exp E.bound * max 0 B := by
    intro σ
    rw [← Real.norm_eq_abs]
    change ‖∫ u, W (glue region u σ) * f (glue region u σ) ∂μ‖ ≤
      Real.exp E.bound * max 0 B
    calc
      ‖∫ u, W (glue region u σ) * f (glue region u σ) ∂μ‖ ≤
          (Real.exp E.bound * max 0 B) * μ.real Set.univ := by
        apply norm_integral_le_of_norm_le_const
        exact ae_of_all μ fun u => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul
            (Real.exp_le_exp.mpr ((le_abs_self _).trans (by
              simpa only [Real.norm_eq_abs] using
                E.norm_energy_le (glue region u σ))))
            ((hB (glue region u σ)).trans (le_max_right _ _))
            (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp E.bound * max 0 B := by simp [μ]
  have hcancel :
      ∫ σ, inner σ * W σ / E.conditionalZ ν region σ ∂μ =
        ∫ σ, inner σ ∂μ := by
    simpa only [W] using E.cancellation_identity ν region inner
      hinner_ext hinner_meas (Real.exp E.bound * max 0 B) hinner_bound
  have hsplit : ∫ σ, inner σ ∂μ = ∫ U, W U * f U ∂μ := by
    simpa only [inner, W] using
      integral_glue (I := I) ν region (fun U => W U * f U) hWf_int
  have hcond : ∀ σ,
      ∫ τ, f τ ∂E.conditionalMeasure ν region σ =
        inner σ / E.conditionalZ ν region σ := by
    intro σ
    let g : (I → S) → I → S := fun u => glue region u σ
    have hg : Measurable g := measurable_glue region σ
    have hden : (∫ U, Real.exp (E U)
        ∂μ.map g) = E.conditionalZ ν region σ := by
      rw [integral_map hg.aemeasurable
        E.measurable_energy.exp.aestronglyMeasurable]
      rfl
    rw [conditionalMeasure, integral_tilted]
    rw [integral_map hg.aemeasurable]
    · rw [hden]
      change (∫ u, Real.exp (E (g u)) / E.conditionalZ ν region σ *
        f (g u) ∂μ) = inner σ / E.conditionalZ ν region σ
      rw [← integral_div]
      apply integral_congr_ae
      exact ae_of_all _ fun u => by
        simp only [inner, W, g]
        ring
    · exact ((E.measurable_energy.exp.div_const _).mul hf).aestronglyMeasurable
  have hZpos : 0 < Z := integral_exp_pos hW_int
  rw [gibbsMeasure, integral_tilted, integral_tilted]
  simp_rw [hcond]
  change (∫ σ, (W σ / Z) *
      (inner σ / E.conditionalZ ν region σ) ∂μ) =
    ∫ σ, (W σ / Z) * f σ ∂μ
  calc
    (∫ σ, (W σ / Z) *
        (inner σ / E.conditionalZ ν region σ) ∂μ) =
        (∫ σ, inner σ * W σ /
          E.conditionalZ ν region σ ∂μ) / Z := by
      rw [← integral_div]
      apply integral_congr_ae
      exact ae_of_all _ fun σ => by ring
    _ = (∫ σ, inner σ ∂μ) / Z := by rw [hcancel]
    _ = (∫ U, W U * f U ∂μ) / Z := by rw [hsplit]
    _ = ∫ σ, (W σ / Z) * f σ ∂μ := by
      rw [← integral_div]
      apply integral_congr_ae
      exact ae_of_all _ fun σ => by ring

/-- Measurability of a normalized conditional expectation. -/
theorem measurable_integral_conditionalMeasure
    (region : Finset I) (f : (I → S) → ℝ) (hf : Measurable f) :
    Measurable fun σ => ∫ τ, f τ ∂E.conditionalMeasure ν region σ := by
  let μ := productMeasure (I := I) ν
  let inner : (I → S) → ℝ := fun σ =>
    ∫ u, Real.exp (E (glue region u σ)) * f (glue region u σ) ∂μ
  have hinner_meas : Measurable inner := by
    let J : ((I → S) × (I → S)) → I → S :=
      fun p => glue region p.2 p.1
    have hJ : Measurable J := measurable_glue_joint region
    exact ((E.measurable_energy.exp.mul hf).comp hJ).stronglyMeasurable
      |>.integral_prod_right' |>.measurable
  have hcond : (fun σ => ∫ τ, f τ ∂E.conditionalMeasure ν region σ) =
      fun σ => inner σ / E.conditionalZ ν region σ := by
    funext σ
    let g : (I → S) → I → S := fun u => glue region u σ
    have hg : Measurable g := measurable_glue region σ
    have hden : (∫ U, Real.exp (E U) ∂μ.map g) =
        E.conditionalZ ν region σ := by
      rw [integral_map hg.aemeasurable
        E.measurable_energy.exp.aestronglyMeasurable]
      rfl
    rw [conditionalMeasure, integral_tilted]
    rw [integral_map hg.aemeasurable]
    · rw [hden]
      change (∫ u, Real.exp (E (g u)) /
        E.conditionalZ ν region σ * f (g u) ∂μ) =
          inner σ / E.conditionalZ ν region σ
      rw [← integral_div]
      apply integral_congr_ae
      exact ae_of_all _ fun u => by
        simp only [inner, g]
        ring
    · exact ((E.measurable_energy.exp.div_const _).mul hf).aestronglyMeasurable
  rw [hcond]
  exact hinner_meas.div (E.conditionalZ_measurable ν region)

/-- Complex-valued form of the finite-product Gibbs tower identity. -/
theorem integral_conditionalMeasure_gibbsMeasure_complex
    (region : Finset I) (f : (I → S) → ℂ)
    (hf : Measurable f) (B : ℝ) (hB : ∀ σ, ‖f σ‖ ≤ B) :
    ∫ σ, (∫ τ, f τ ∂E.conditionalMeasure ν region σ)
        ∂E.gibbsMeasure ν =
      ∫ σ, f σ ∂E.gibbsMeasure ν := by
  let g : (I → S) → ℂ := fun σ =>
    ∫ τ, f τ ∂E.conditionalMeasure ν region σ
  let gr : (I → S) → ℝ := fun σ =>
    ∫ τ, (f τ).re ∂E.conditionalMeasure ν region σ
  let gi : (I → S) → ℝ := fun σ =>
    ∫ τ, (f τ).im ∂E.conditionalMeasure ν region σ
  have hfr : Measurable fun σ => (f σ).re := Complex.measurable_re.comp hf
  have hfi : Measurable fun σ => (f σ).im := Complex.measurable_im.comp hf
  have hfcond : ∀ σ, Integrable f (E.conditionalMeasure ν region σ) := by
    intro σ
    apply Integrable.of_bound hf.aestronglyMeasurable B
    exact ae_of_all _ hB
  have hgre : (fun σ => (g σ).re) = gr := by
    funext σ
    exact (integral_re (hfcond σ)).symm
  have hgim : (fun σ => (g σ).im) = gi := by
    funext σ
    exact (integral_im (hfcond σ)).symm
  have hgr_meas : Measurable gr := by
    exact E.measurable_integral_conditionalMeasure ν region
      (fun σ => (f σ).re) hfr
  have hgi_meas : Measurable gi := by
    exact E.measurable_integral_conditionalMeasure ν region
      (fun σ => (f σ).im) hfi
  have hg_repr : g = fun σ => (gr σ : ℂ) + (gi σ : ℂ) * Complex.I := by
    funext σ
    apply Complex.ext
    · simpa using congrFun hgre σ
    · simpa using congrFun hgim σ
  have hg_meas : Measurable g := by
    rw [hg_repr]
    exact hgr_meas.complex_ofReal.add
      (hgi_meas.complex_ofReal.mul measurable_const)
  have hg_bound : ∀ σ, ‖g σ‖ ≤ B := by
    intro σ
    change ‖∫ τ, f τ ∂E.conditionalMeasure ν region σ‖ ≤ B
    simpa using norm_integral_le_of_norm_le_const
      (μ := E.conditionalMeasure ν region σ) (ae_of_all _ hB)
  have hg_int : Integrable g (E.gibbsMeasure ν) := by
    apply Integrable.of_bound hg_meas.aestronglyMeasurable B
    exact ae_of_all _ hg_bound
  have hf_int : Integrable f (E.gibbsMeasure ν) := by
    apply Integrable.of_bound hf.aestronglyMeasurable B
    exact ae_of_all _ hB
  apply Complex.ext
  · change (∫ σ, g σ ∂E.gibbsMeasure ν).re =
      (∫ σ, f σ ∂E.gibbsMeasure ν).re
    calc
      (∫ σ, g σ ∂E.gibbsMeasure ν).re =
          ∫ σ, (g σ).re ∂E.gibbsMeasure ν := (integral_re hg_int).symm
      _ = ∫ σ, gr σ ∂E.gibbsMeasure ν := by rw [hgre]
      _ = ∫ σ, (f σ).re ∂E.gibbsMeasure ν := by
        simpa only [gr] using
          E.integral_conditionalMeasure_gibbsMeasure ν region
            (fun σ => (f σ).re) hfr B
            (fun σ => (Complex.abs_re_le_norm (f σ)).trans (hB σ))
      _ = (∫ σ, f σ ∂E.gibbsMeasure ν).re := integral_re hf_int
  · change (∫ σ, g σ ∂E.gibbsMeasure ν).im =
      (∫ σ, f σ ∂E.gibbsMeasure ν).im
    calc
      (∫ σ, g σ ∂E.gibbsMeasure ν).im =
          ∫ σ, (g σ).im ∂E.gibbsMeasure ν := (integral_im hg_int).symm
      _ = ∫ σ, gi σ ∂E.gibbsMeasure ν := by rw [hgim]
      _ = ∫ σ, (f σ).im ∂E.gibbsMeasure ν := by
        simpa only [gi] using
          E.integral_conditionalMeasure_gibbsMeasure ν region
            (fun σ => (f σ).im) hfi B
            (fun σ => (Complex.abs_im_le_norm (f σ)).trans (hB σ))
      _ = (∫ σ, f σ ∂E.gibbsMeasure ν).im := integral_im hf_int

/-- Explicit ratio-of-integrals formula for a bounded complex observable in
a normalized conditional law. -/
theorem integral_conditionalMeasure_complex_eq_div
    (region : Finset I) (σ : I → S) (f : (I → S) → ℂ)
    (hf : Measurable f) (B : ℝ) (hB : ∀ τ, ‖f τ‖ ≤ B) :
    ∫ τ, f τ ∂E.conditionalMeasure ν region σ =
      (∫ u, (Real.exp (E (glue region u σ)) : ℂ) *
          f (glue region u σ) ∂productMeasure (I := I) ν) /
        E.conditionalZ ν region σ := by
  let μ := productMeasure (I := I) ν
  let g : (I → S) → I → S := fun u => glue region u σ
  have hg : Measurable g := measurable_glue region σ
  have hden : (∫ U, Real.exp (E U) ∂μ.map g) =
      E.conditionalZ ν region σ := by
    rw [integral_map hg.aemeasurable
      E.measurable_energy.exp.aestronglyMeasurable]
    rfl
  rw [conditionalMeasure, integral_tilted]
  rw [integral_map hg.aemeasurable]
  · rw [hden]
    rw [← integral_div]
    apply integral_congr_ae
    exact ae_of_all _ fun u => by
      change (Real.exp (E (glue region u σ)) /
          E.conditionalZ ν region σ : ℝ) • f (glue region u σ) =
        (Real.exp (E (glue region u σ)) : ℂ) *
          f (glue region u σ) / E.conditionalZ ν region σ
      rw [Complex.real_smul]
      push_cast
      ring
  · apply AEStronglyMeasurable.smul
    · exact (E.measurable_energy.exp.div_const _).aestronglyMeasurable
    · exact hf.aestronglyMeasurable

/-- The unnormalized conditional numerator of a measurable event. -/
def conditionalNumerator (region : Finset I) (A : Set (I → S))
    (σ : I → S) : ℝ :=
  ∫ u, Set.indicator A (fun U => Real.exp (E U)) (glue region u σ)
    ∂productMeasure (I := I) ν

theorem conditionalNumerator_measurable (region : Finset I)
    (A : Set (I → S)) (hA : MeasurableSet A) :
    Measurable (E.conditionalNumerator ν region A) := by
  let J : ((I → S) × (I → S)) → I → S :=
    fun p => glue region p.2 p.1
  have hJ : Measurable J := measurable_glue_joint region
  exact ((E.measurable_energy.exp.indicator hA).comp hJ).stronglyMeasurable
    |>.integral_prod_right' |>.measurable

theorem conditionalNumerator_exterior (region : Finset I)
    (A : Set (I → S)) :
    ExteriorMeasurable region (E.conditionalNumerator ν region A) := by
  intro u σ
  apply integral_congr_ae
  exact ae_of_all _ fun v => by
    apply congrArg (Set.indicator A fun U => Real.exp (E U))
    ext i
    by_cases hi : i ∈ region <;> simp [glue, hi]

theorem abs_conditionalNumerator_le_exp_bound (region : Finset I)
    (A : Set (I → S)) (hA : MeasurableSet A) (σ : I → S) :
    |E.conditionalNumerator ν region A σ| ≤ Real.exp E.bound := by
  let f : (I → S) → ℝ := fun u =>
    Set.indicator A (fun U => Real.exp (E U)) (glue region u σ)
  have hf_meas : Measurable f :=
    (E.measurable_energy.exp.indicator hA).comp (measurable_glue region σ)
  have hf_nonneg : ∀ u, 0 ≤ f u := by
    intro u
    exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  have hf_int : Integrable f (productMeasure (I := I) ν) := by
    apply Integrable.of_bound hf_meas.aestronglyMeasurable (Real.exp E.bound)
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg u)]
      change Set.indicator A (fun U => Real.exp (E U))
        (glue region u σ) ≤ Real.exp E.bound
      by_cases hu : glue region u σ ∈ A
      · rw [Set.indicator_of_mem hu]
        exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
          simpa only [Real.norm_eq_abs] using
            E.norm_energy_le (glue region u σ)))
      · rw [Set.indicator_of_notMem hu]
        exact (Real.exp_pos _).le
  have hle : ∫ u, f u ∂productMeasure (I := I) ν ≤ Real.exp E.bound := by
    calc
      ∫ u, f u ∂productMeasure (I := I) ν ≤
          ∫ _u, Real.exp E.bound ∂productMeasure (I := I) ν := by
        apply integral_mono hf_int (integrable_const _)
        intro u
        change Set.indicator A (fun U => Real.exp (E U))
          (glue region u σ) ≤ Real.exp E.bound
        by_cases hu : glue region u σ ∈ A
        · rw [Set.indicator_of_mem hu]
          exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
            simpa only [Real.norm_eq_abs] using
              E.norm_energy_le (glue region u σ)))
        · rw [Set.indicator_of_notMem hu]
          exact (Real.exp_pos _).le
      _ = Real.exp E.bound := by simp
  change |∫ u, f u ∂productMeasure (I := I) ν| ≤ Real.exp E.bound
  rw [abs_of_nonneg (integral_nonneg hf_nonneg)]
  exact hle

/-- The globally tilted finite-product measure satisfies the full DLR
equations for the specification generated by the same energy. -/
theorem gibbsMeasure_isGibbs :
    IsGibbsMeasure (E.gibbsSpec ν) (E.gibbsMeasure ν) := by
  classical
  refine ⟨?_⟩
  intro region A hA
  let μ := productMeasure (I := I) ν
  let W : (I → S) → ℝ := fun U => Real.exp (E U)
  let Z : ℝ := ∫ U, W U ∂μ
  let inner : (I → S) → ℝ := E.conditionalNumerator ν region A
  have hW_meas : Measurable W := E.measurable_energy.exp
  have hW_int : Integrable W μ := by
    apply Integrable.of_bound hW_meas.aestronglyMeasurable (Real.exp E.bound)
    exact ae_of_all _ fun U => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs] using E.norm_energy_le U))
  have hZpos : 0 < Z := integral_exp_pos hW_int
  have hinner_meas : Measurable inner :=
    E.conditionalNumerator_measurable ν region A hA
  have hinner_ext : ExteriorMeasurable region inner :=
    E.conditionalNumerator_exterior ν region A
  have hinner_bound : ∀ σ, |inner σ| ≤ Real.exp E.bound :=
    E.abs_conditionalNumerator_le_exp_bound ν region A hA
  have hcancel :
      ∫ σ, inner σ * W σ / E.conditionalZ ν region σ ∂μ =
        ∫ σ, inner σ ∂μ := by
    simpa only [W] using E.cancellation_identity ν region inner
      hinner_ext hinner_meas (Real.exp E.bound) hinner_bound
  have hsplit : ∫ σ, inner σ ∂μ =
      ∫ U, Set.indicator A W U ∂μ := by
    simpa only [inner, conditionalNumerator, W] using
      integral_glue (I := I) ν region (Set.indicator A W)
        (hW_int.indicator hA)
  have hcond : ∀ σ,
      ((E.gibbsSpec ν).condDist region σ A).toReal =
        inner σ / E.conditionalZ ν region σ := by
    intro σ
    simpa only [gibbsSpec_condDist, inner, conditionalNumerator, W] using
      E.conditionalMeasure_apply_toReal ν region σ A hA
  have hlhs : (E.gibbsMeasure ν A).toReal =
      (∫ U, Set.indicator A W U ∂μ) / Z := by
    calc
      (E.gibbsMeasure ν A).toReal =
          ∫ U, Set.indicator A (fun _ => (1 : ℝ)) U ∂E.gibbsMeasure ν :=
        (integral_indicator_one hA).symm
      _ = ∫ U, (W U / Z) * Set.indicator A (fun _ => (1 : ℝ)) U ∂μ := by
        rw [gibbsMeasure, integral_tilted]
        rfl
      _ = (∫ U, Set.indicator A W U ∂μ) / Z := by
        calc
          ∫ U, (W U / Z) * Set.indicator A (fun _ => (1 : ℝ)) U ∂μ =
              ∫ U, Set.indicator A W U / Z ∂μ := by
            apply integral_congr_ae
            exact ae_of_all _ fun U => by
              by_cases hU : U ∈ A
              · simp [Set.indicator_of_mem hU]
              · simp [Set.indicator_of_notMem hU]
          _ = _ := integral_div Z (fun U => Set.indicator A W U)
  rw [hlhs]
  symm
  calc
    ∫ σ, ((E.gibbsSpec ν).condDist region σ A).toReal
        ∂E.gibbsMeasure ν =
      ∫ σ, (W σ / Z) * (inner σ / E.conditionalZ ν region σ) ∂μ := by
      rw [gibbsMeasure, integral_tilted]
      simp only [smul_eq_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun σ => by
        change (W σ / Z) * ((E.gibbsSpec ν).condDist region σ A).toReal = _
        rw [hcond σ]
    _ = (∫ σ, inner σ * W σ / E.conditionalZ ν region σ ∂μ) / Z := by
      calc
        ∫ σ, (W σ / Z) * (inner σ / E.conditionalZ ν region σ) ∂μ =
            ∫ σ, (inner σ * W σ / E.conditionalZ ν region σ) / Z ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun σ => by ring
        _ = _ := integral_div Z
          (fun σ => inner σ * W σ / E.conditionalZ ν region σ)
    _ = (∫ σ, inner σ ∂μ) / Z := by rw [hcancel]
    _ = (∫ U, Set.indicator A W U ∂μ) / Z := by rw [hsplit]

end FiniteEnergy

end

end YangMills.Probability
