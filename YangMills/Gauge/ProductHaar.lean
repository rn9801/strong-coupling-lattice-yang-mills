/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.HaarProbability
import Mathlib.Logic.Function.DependsOn
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Finite product Haar probability

This module defines product Haar measure on a finite family of gauge variables,
proves coordinatewise measure-preserving transformations and coordinate
reindexing, and establishes integral factorization for measurable functions
with disjoint coordinate supports.

The factorization argument is a type-generic generalization of
`LGT.MassGap.Locality.integral_mul_of_disjoint_dependsOn` from Michael R.
Douglas's `LGT` repository at commit
`b8793ccf6a51e00e9e2b1685ba191b8626e37137` (Apache-2.0). It uses Mathlib's
`DependsOn`, independent coordinate sigma-algebras, and integration theorem;
no periodic-lattice declaration is imported.
-/

open MeasureTheory

namespace YangMills.Gauge

namespace ProductHaar

variable {G : Type*} [MeasurableSpace G]

/-- Independent Haar probability on a finite family of `G`-valued variables. -/
noncomputable def measure (G : Type*) [Group G] [MeasurableSpace G] [GaugeHaarProbability G]
    (ι : Type*) [Fintype ι] : Measure (ι → G) :=
  Measure.pi fun _ : ι => GaugeHaarProbability.haar G

instance instIsProbabilityMeasure [Group G] [GaugeHaarProbability G]
    (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (measure G ι) := by
  unfold measure
  exact Measure.pi.instIsProbabilityMeasure _

instance instIsFiniteMeasure [Group G] [GaugeHaarProbability G]
    (ι : Type*) [Fintype ι] :
    IsFiniteMeasure (measure G ι) :=
  IsZeroOrProbabilityMeasure.toIsFiniteMeasure _

instance instSigmaFinite [Group G] [GaugeHaarProbability G]
    (ι : Type*) [Fintype ι] : SigmaFinite (measure G ι) :=
  IsFiniteMeasure.toSigmaFinite _

/-- Coordinatewise measure-preserving maps preserve the corresponding product measures. -/
theorem measurePreserving_coordinatewise
    [Group G] [GaugeHaarProbability G]
    {ι : Type*} [Fintype ι]
    {H : ι → Type*} [∀ i, MeasurableSpace (H i)]
    (ν : (i : ι) → Measure (H i)) [∀ i, SigmaFinite (ν i)]
    (f : (i : ι) → G → H i)
    (hf : ∀ i, MeasurePreserving (f i) (GaugeHaarProbability.haar G) (ν i)) :
    MeasurePreserving (fun U i => f i (U i)) (measure G ι) (Measure.pi ν) := by
  exact MeasureTheory.measurePreserving_pi _ _ hf

/-- The measurable equivalence that relabels a finite coordinate family. -/
def reindexEquiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    (ι → G) ≃ᵐ (κ → G) :=
  MeasurableEquiv.piCongrLeft (fun _ : κ => G) e

/-- Relabel a configuration along an equivalence of finite index types. -/
def reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (U : ι → G) : κ → G :=
  reindexEquiv (G := G) e U

@[simp]
theorem reindex_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (U : ι → G) (j : κ) :
    reindex (G := G) e U j = U (e.symm j) :=
  by
    simpa only [reindex, Equiv.apply_symm_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : κ => G) e U (e.symm j))

/-- Product Haar probability is invariant under finite coordinate relabeling. -/
theorem measurePreserving_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Group G] [GaugeHaarProbability G]
    (e : ι ≃ κ) :
    MeasurePreserving (reindexEquiv (G := G) e) (measure G ι) (measure G κ) := by
  simpa only [measure, reindexEquiv] using
    (MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : κ => GaugeHaarProbability.haar G) e)

/-- Integrals against product Haar are unchanged by finite coordinate relabeling. -/
theorem integral_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Group G] [GaugeHaarProbability G]
    (e : ι ≃ κ) (f : (κ → G) → ℝ) :
    ∫ U, f (reindex (G := G) e U) ∂measure G ι =
      ∫ V, f V ∂measure G κ := by
  exact (measurePreserving_reindex (G := G) e).integral_comp' f

/-- Restricting a larger finite family of independent Haar variables to a
smaller family preserves product Haar probability. -/
def restrictOfFinsetSubset {ι : Type*} [DecidableEq ι]
    {s t : Finset ι} (hst : s ⊆ t) (U : t → G) : s → G :=
  fun i => U ⟨i.1, hst i.2⟩

theorem measurePreserving_restrictOfFinsetSubset
    {ι : Type*} [DecidableEq ι] [Group G] [GaugeHaarProbability G]
    {s t : Finset ι} (hst : s ⊆ t) :
    MeasurePreserving (restrictOfFinsetSubset (G := G) hst)
      (measure G t) (measure G s) := by
  classical
  let p : t → Prop := fun i => i.1 ∈ s
  let e : s ≃ Subtype p := {
    toFun i := ⟨⟨i.1, hst i.2⟩, i.2⟩
    invFun i := ⟨i.1.1, i.2⟩
    left_inv i := by ext; rfl
    right_inv i := by ext; rfl
  }
  have hsplit : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : t => G) p)
      (measure G t)
      ((measure G (Subtype p)).prod
        (measure G {i : t // ¬p i})) := by
    simpa only [measure] using
      (MeasureTheory.measurePreserving_piEquivPiSubtypeProd
        (fun _ : t => GaugeHaarProbability.haar G) p)
  have hfirst : MeasurePreserving
      (fun U : t → G =>
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : t => G) p U).1)
      (measure G t) (measure G (Subtype p)) := by
    exact (MeasureTheory.measurePreserving_fst
      (μ := measure G (Subtype p))
      (ν := measure G {i : t // ¬p i})).comp hsplit
  have hreindex := measurePreserving_reindex (G := G) e.symm
  have hcomp := hreindex.comp hfirst
  simpa only [restrictOfFinsetSubset, p, e, reindexEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd_apply,
    MeasurableEquiv.piCongrLeft_apply_apply, Function.comp_apply] using hcomp

/-- Integrating a measurable function after restricting independent Haar
coordinates is the same as integrating it directly over the smaller product. -/
theorem integral_restrictOfFinsetSubset
    {ι : Type*} [DecidableEq ι] [Group G] [GaugeHaarProbability G]
    {s t : Finset ι} (hst : s ⊆ t)
    {𝕜 : Type*} [RCLike 𝕜] (f : (s → G) → 𝕜) (hf : Measurable f) :
    ∫ U, f (restrictOfFinsetSubset (G := G) hst U) ∂measure G t =
      ∫ V, f V ∂measure G s := by
  let R := restrictOfFinsetSubset (G := G) hst
  have hR := measurePreserving_restrictOfFinsetSubset (G := G) hst
  have hfmap : AEStronglyMeasurable f (Measure.map R (measure G t)) := by
    rw [hR.map_eq]
    exact hf.aestronglyMeasurable
  calc
    ∫ U, f (R U) ∂measure G t =
        ∫ V, f V ∂Measure.map R (measure G t) :=
      (MeasureTheory.integral_map hR.measurable.aemeasurable hfmap).symm
    _ = ∫ V, f V ∂measure G s := by rw [hR.map_eq]

/-- A measurable function depending on `R` is measurable for the sigma-algebra
generated by the coordinate projections in `R`. -/
private theorem comap_le_iSup_of_dependsOn
    [Group G] {ι : Type*} {𝕜 : Type*} [RCLike 𝕜]
    (h : (ι → G) → 𝕜) (R : Set ι)
    (hDep : DependsOn h R) (hMeas : Measurable h) :
    MeasurableSpace.comap h inferInstance ≤
      ⨆ i ∈ R, MeasurableSpace.comap (fun U : ι → G => U i) inferInstance := by
  classical
  let σ : (R → G) → (ι → G) :=
    fun x i => if hi : i ∈ R then x ⟨i, hi⟩ else 1
  have hσ_meas : Measurable σ := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ∈ R
    · simpa only [σ, hi, dif_pos] using measurable_pi_apply (⟨i, hi⟩ : R)
    · simpa only [σ, hi, dif_neg] using (measurable_const : Measurable fun _ : R → G => (1 : G))
  let h' : (R → G) → 𝕜 := h ∘ σ
  have hh'_meas : Measurable h' := hMeas.comp hσ_meas
  have h_eq : h = h' ∘ R.restrict := by
    ext U
    simp only [h', Function.comp_def]
    exact (hDep (fun i hi => by simp [σ, hi])).symm
  rw [h_eq, ← MeasurableSpace.comap_comp]
  apply le_trans (MeasurableSpace.comap_mono hh'_meas.comap_le)
  change MeasurableSpace.comap (R.restrict (π := fun _ => G)) MeasurableSpace.pi ≤ _
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  apply iSup_le
  intro ⟨j, hj⟩
  have hEval :
      (fun (b : R → G) => b ⟨j, hj⟩) ∘ R.restrict (π := fun _ => G) =
        (fun b : ι → G => b j) := by
    ext b
    simp [Set.restrict]
  rw [hEval]
  exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)

/-- Measurable functions with disjoint coordinate supports factor under product Haar. -/
theorem integral_mul_of_disjoint_dependsOn
    [Group G] [GaugeHaarProbability G] {𝕜 : Type*} [RCLike 𝕜]
    {ι : Type*} [Fintype ι]
    (f g : (ι → G) → 𝕜) (S T : Set ι)
    (hf : DependsOn f S) (hg : DependsOn g T)
    (hST : Disjoint S T) (hfm : Measurable f) (hgm : Measurable g) :
    ∫ U, f U * g U ∂measure G ι =
      (∫ U, f U ∂measure G ι) * (∫ U, g U ∂measure G ι) := by
  classical
  have hindep : ProbabilityTheory.iIndepFun
      (fun (i : ι) (U : ι → G) => U i) (measure G ι) := by
    have h := ProbabilityTheory.iIndepFun_pi
      (Ω := fun _ : ι => G)
      (μ := fun _ => GaugeHaarProbability.haar G)
      (𝓧 := fun _ : ι => G)
      (X := fun _ => id)
      (fun _ => aemeasurable_id)
    simpa only [measure] using h
  have hiIndep : ProbabilityTheory.iIndep
      (fun i => MeasurableSpace.comap (fun U : ι → G => U i) inferInstance)
      (measure G ι) :=
    hindep.iIndep
  have h_le : ∀ i : ι,
      MeasurableSpace.comap (fun U : ι → G => U i) inferInstance ≤
        (inferInstance : MeasurableSpace (ι → G)) :=
    fun i => (measurable_pi_apply i).comap_le
  have hIndepSigma := ProbabilityTheory.indep_iSup_of_disjoint h_le hiIndep hST
  have hIndepFG : ProbabilityTheory.IndepFun f g (measure G ι) := by
    rw [ProbabilityTheory.IndepFun]
    exact ProbabilityTheory.indep_of_indep_of_le_left
      (ProbabilityTheory.indep_of_indep_of_le_right hIndepSigma
        (comap_le_iSup_of_dependsOn g T hg hgm))
      (comap_le_iSup_of_dependsOn f S hf hfm)
  exact hIndepFG.integral_fun_mul_eq_mul_integral
    hfm.aestronglyMeasurable hgm.aestronglyMeasurable

/-- A finite family of measurable functions with pairwise disjoint coordinate
supports factors under product Haar. -/
theorem integral_prod_of_pairwise_disjoint_dependsOn
    [Group G] [GaugeHaarProbability G] {𝕜 : Type*} [RCLike 𝕜]
    {ι J : Type*} [Fintype ι]
    (s : Finset J) (f : J → (ι → G) → 𝕜) (S : J → Set ι)
    (hpair : (s : Set J).Pairwise fun i j => Disjoint (S i) (S j))
    (hdep : ∀ j ∈ s, DependsOn (f j) (S j))
    (hmeas : ∀ j ∈ s, Measurable (f j)) :
    ∫ U, ∏ j ∈ s, f j U ∂measure G ι =
      ∏ j ∈ s, ∫ U, f j U ∂measure G ι := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t hat ih =>
      have hpair_insert : (Set.insert a (t : Set J)).Pairwise
          fun i j => Disjoint (S i) (S j) := by
        simpa only [Finset.coe_insert] using hpair
      have hpair_t : (t : Set J).Pairwise fun i j => Disjoint (S i) (S j) :=
        hpair_insert.mono (Set.subset_insert a t)
      have hdep_t : ∀ j ∈ t, DependsOn (f j) (S j) :=
        fun j hj => hdep j (Finset.mem_insert_of_mem hj)
      have hmeas_t : ∀ j ∈ t, Measurable (f j) :=
        fun j hj => hmeas j (Finset.mem_insert_of_mem hj)
      have ih' := ih hpair_t hdep_t hmeas_t
      let T : Set ι := ⋃ j ∈ (t : Set J), S j
      have hdep_prod : DependsOn (fun U => ∏ j ∈ t, f j U) T := by
        intro U V hUV
        apply Finset.prod_congr rfl
        intro j hj
        apply hdep_t j hj
        intro i hi
        apply hUV i
        exact Set.mem_iUnion_of_mem j (Set.mem_iUnion_of_mem hj hi)
      have hdisj : Disjoint (S a) T := by
        rw [Set.disjoint_iUnion_right]
        intro j
        rw [Set.disjoint_iUnion_right]
        intro hj
        exact hpair (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hj)
          (fun h => hat (h ▸ hj))
      have hmeas_prod : Measurable (fun U => ∏ j ∈ t, f j U) := by
        fun_prop
      simp_rw [Finset.prod_insert hat]
      rw [integral_mul_of_disjoint_dependsOn (f a) (fun U => ∏ j ∈ t, f j U)
        (S a) T (hdep a (Finset.mem_insert_self a t)) hdep_prod hdisj
        (hmeas a (Finset.mem_insert_self a t)) hmeas_prod]
      rw [ih']

end ProductHaar

end YangMills.Gauge
