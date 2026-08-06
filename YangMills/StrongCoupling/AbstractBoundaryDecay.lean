/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.Influence
import MarkovSemigroups.Dobrushin.CovarianceBoundMultisite

/-!
# Abstract boundary decay for finite compact-spin systems

This module turns a local Dobrushin comparison into a boundary-condition
estimate with no factor proportional to the size of the defect set.  It is
the probability-theoretic companion to the polymer-facing Neumann bound in
`YangMills.Polymer.Influence`.

The coupling, multi-source Neumann iteration, and local-observable integral
estimate are reused from Michael R. Douglas' Apache-2.0-licensed
`markov-semigroups` development.  The contribution here is the aggregate
defect-set wiring: the defect sum is placed inside the path-length series, so
the uniform row bound controls all defects at once.
-/

open MeasureTheory ProbabilityTheory
open CovarianceBoundMultisite
open MarkovSemigroups.DobrushinZegarlinski

namespace YangMills.StrongCoupling

noncomputable section

variable {I S : Type*} [DecidableEq I] [Fintype I]
  [TopologicalSpace S] [CompactSpace S] [T2Space S]
  [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]

/-- On a finite site space, every influence row has finite support. -/
def finiteInfluenceSupport (γ : GibbsSpec I S) (z : I) :
    (Function.support (influenceCoeff γ z ·)).Finite :=
  Set.toFinite _

/-- For finite systems, the dependency hypothesis used by the coupling
backend follows automatically from the definition of the influence
coefficients.  Configurations agreeing wherever the coefficient is nonzero
have identical one-site conditional marginals. -/
theorem finiteInfluence_dependency
    (γ : GibbsSpec I S) (z : I) (B : Set S) (hB : MeasurableSet B)
    (σ τ : SpinConfig I S)
    (hστ : ∀ w ∈ (finiteInfluenceSupport γ z).toFinset,
      σ w = τ w) :
    (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
      (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal := by
  classical
  have hsum :
      (∑ w : I, influenceCoeff γ z w *
        (if σ w = τ w then (0 : ℝ) else 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    by_cases hw : σ w = τ w
    · simp [hw]
    · have hnot : w ∉ Function.support (influenceCoeff γ z ·) := by
        intro hmem
        apply hw
        exact hστ w (by
          rw [Set.Finite.mem_toFinset]
          exact hmem)
      have hzero : influenceCoeff γ z w = 0 := by
        simpa [Function.mem_support] using hnot
      simp [hw, hzero]
  have htvle := tvDist_marginal_le_influenceCoeff_sum γ z σ τ
  rw [hsum] at htvle
  have htv :
      tvDist (marginalAtSite (γ.condDist {z} σ) z)
        (marginalAtSite (γ.condDist {z} τ) z) = 0 :=
    le_antisymm htvle (tvDist_nonneg _ _)
  have habs := abs_toReal_sub_le_tvDist
    (marginalAtSite (γ.condDist {z} σ) z)
    (marginalAtSite (γ.condDist {z} τ) z) B hB
  rw [marginalAtSite_apply _ _ hB, marginalAtSite_apply _ _ hB, htv] at habs
  have heq :
      |(γ.condDist {z} σ ((· z) ⁻¹' B)).toReal -
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal| = 0 :=
    le_antisymm habs (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp heq)

/-- Regard a TV Dobrushin condition as the abstract nonnegative influence
matrix used by the aggregate marked-root estimate. -/
def dobrushinInfluenceMatrix (γ : GibbsSpec I S) (hD : DobrushinCondition γ) :
    AbstractInfluenceMatrix I where
  entry := influenceCoeff γ
  α := hD.α
  α_nonneg := hD.hα_pos
  α_lt_one := hD.hα_lt
  entry_nonneg := influenceCoeff_nonneg γ
  col_summable := hD.col_summable
  col_bound := hD.column_bound
  row_summable := hD.row_summable
  row_bound := hD.row_bound

@[simp]
theorem dobrushinInfluenceMatrix_entry (γ : GibbsSpec I S)
    (hD : DobrushinCondition γ) (x y : I) :
    (dobrushinInfluenceMatrix γ hD).entry x y = influenceCoeff γ x y :=
  rfl

@[simp]
theorem dobrushinInfluenceMatrix_alpha (γ : GibbsSpec I S)
    (hD : DobrushinCondition γ) :
    (dobrushinInfluenceMatrix γ hD).α = hD.α :=
  rfl

/-- The two Neumann-iterate implementations agree entrywise. -/
theorem dobrushinInfluenceMatrix_iterate (γ : GibbsSpec I S)
    (hD : DobrushinCondition γ) (n : ℕ) (x y : I) :
    (dobrushinInfluenceMatrix γ hD).iterate n x y =
      iterateInfluence γ n x y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
      rw [AbstractInfluenceMatrix.iterate_succ]
      simp only [iterateInfluence]
      apply tsum_congr
      intro z
      rw [ih x z]
      rfl

/-- A finite defect sum of the TV Neumann coefficients is the aggregate
influence-to-set quantity. -/
theorem sum_neumannSeriesCoeff_eq_influenceToSet
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (root : I) (defects : Finset I) :
    (∑ defect ∈ defects, neumannSeriesCoeff γ root defect) =
    YangMills.Polymer.neumannInfluenceToSet
        (dobrushinInfluenceMatrix γ hD) root defects := by
  have hsumm : ∀ defect ∈ defects,
      Summable (fun n =>
        (dobrushinInfluenceMatrix γ hD).iterate n root defect) := by
    intro defect _
    simpa only [dobrushinInfluenceMatrix_iterate] using
      neumannSeriesCoeff_summable γ hD root defect
  rw [YangMills.Polymer.neumannInfluenceToSet]
  calc
    ∑ defect ∈ defects, neumannSeriesCoeff γ root defect =
        ∑ defect ∈ defects, ∑' n,
          (dobrushinInfluenceMatrix γ hD).iterate n root defect := by
      apply Finset.sum_congr rfl
      intro defect _
      unfold neumannSeriesCoeff
      apply tsum_congr
      intro n
      exact (dobrushinInfluenceMatrix_iterate γ hD n root defect).symm
    _ = ∑' n, ∑ defect ∈ defects,
        (dobrushinInfluenceMatrix γ hD).iterate n root defect :=
      (Summable.tsum_finsetSum hsumm).symm

/-- Uniform finite-volume boundary comparison for a bounded real local
observable.  The two probability measures need only satisfy the same
single-site DLR equations away from `defects`; on the defect sites they may
be arbitrary.  In particular, the constant is independent of the volume and
of `defects.card`.

This is the exact abstract exit theorem needed after a concrete finite-volume
model supplies its Gibbs specification and nearest-neighbor influence bound.
-/
theorem realLocalExpectation_boundaryDecay
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ₁ μ₂ : Measure (SpinConfig I S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (roots defects : Finset I)
    (g : SpinConfig I S → ℝ) (hg_meas : Measurable g)
    (B : ℝ) (hB_nonneg : 0 ≤ B) (hg_bound : ∀ σ, |g σ| ≤ B)
    (hg_int₁ : Integrable g μ₁) (hg_int₂ : Integrable g μ₂)
    (hg_local : ∀ σ τ, (∀ x ∈ roots, σ x = τ x) → g σ = g τ)
    (hDLR₁ : ∀ z, z ∉ defects → ∀ A : Set (SpinConfig I S),
      MeasurableSet A →
        (μ₁ A).toReal =
          ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₁)
    (hDLR₂ : ∀ z, z ∉ defects → ∀ A : Set (SpinConfig I S),
      MeasurableSet A →
        (μ₂ A).toReal =
          ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂)
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep : ∀ (z : I) (A : Set S), MeasurableSet A →
      ∀ σ τ : SpinConfig I S,
        (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' A)).toReal =
          (γ.condDist {z} τ ((· z) ⁻¹' A)).toReal)
    (dist : I → I → ℕ)
    (h_refl : ∀ x, dist x x = 0)
    (h_triangle : ∀ x y z, dist x y ≤ dist x z + dist z y)
    (h_support : ∀ x y, dist x y > 1 → influenceCoeff γ x y = 0)
    (r : ℕ)
    (hseparated : ∀ root ∈ roots, ∀ defect ∈ defects,
      r ≤ dist root defect) :
    |∫ σ, g σ ∂μ₁ - ∫ σ, g σ ∂μ₂| ≤
      2 * B * (roots.card : ℝ) *
        (hD.α ^ r / (1 - hD.α)) := by
  classical
  let T : Set I := {z | z ∉ defects}
  obtain ⟨P, hP, hcontract⟩ :=
    dobrushin_iterated_coupling_exists_compact γ μ₁ μ₂ T
      (fun z hz => hDLR₁ z hz)
      (fun z hz => hDLR₂ z hz) hfinsupp h_dep
  haveI : IsProbabilityMeasure P := hP.isProb
  let disagreement : I → ℝ := fun x =>
    (P {p : SpinConfig I S × SpinConfig I S | p.1 x ≠ p.2 x}).toReal
  have hdisagreement_nonneg : ∀ x, 0 ≤ disagreement x :=
    fun _ => ENNReal.toReal_nonneg
  have hdisagreement_le_one : ∀ x, disagreement x ≤ 1 := by
    intro x
    exact (ENNReal.toReal_mono (by simp)
      (prob_le_one (μ := P)
        (s := {p : SpinConfig I S × SpinConfig I S | p.1 x ≠ p.2 x})))
  have hcontract' : ∀ z, z ∉ defects →
      disagreement z ≤ ∑' w, influenceCoeff γ z w * disagreement w := by
    intro z hz
    exact hcontract z hz
  have hroot : ∀ root, disagreement root ≤
      ∑ defect ∈ defects, neumannSeriesCoeff γ root defect := by
    intro root
    exact abstract_neumann_iteration_finset γ hD defects disagreement
      hdisagreement_nonneg hdisagreement_le_one hcontract' root
  have haggregate : ∀ root ∈ roots,
      disagreement root ≤ hD.α ^ r / (1 - hD.α) := by
    intro root hrootmem
    calc
      disagreement root ≤
          ∑ defect ∈ defects, neumannSeriesCoeff γ root defect := hroot root
      _ = YangMills.Polymer.neumannInfluenceToSet
          (dobrushinInfluenceMatrix γ hD) root defects :=
        sum_neumannSeriesCoeff_eq_influenceToSet γ hD root defects
      _ ≤ (dobrushinInfluenceMatrix γ hD).α ^ r /
          (1 - (dobrushinInfluenceMatrix γ hD).α) :=
        YangMills.Polymer.neumannInfluenceToSet_le_exponential
          (dobrushinInfluenceMatrix γ hD) dist h_refl h_triangle
          (by simpa using h_support) root defects r
          (fun defect hdefect => hseparated root hrootmem defect hdefect)
      _ = hD.α ^ r / (1 - hD.α) := rfl
  have hlocal := local_integral_sub_le_coupling_Ng μ₁ μ₂ P hP g
    hg_meas B hB_nonneg hg_bound hg_int₁ hg_int₂ roots hg_local
  calc
    |∫ σ, g σ ∂μ₁ - ∫ σ, g σ ∂μ₂| ≤
        2 * B * ∑ root ∈ roots, disagreement root := hlocal
    _ ≤ 2 * B * ∑ _root ∈ roots,
        (hD.α ^ r / (1 - hD.α)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hB_nonneg)
      exact Finset.sum_le_sum haggregate
    _ = 2 * B * (roots.card : ℝ) *
        (hD.α ^ r / (1 - hD.α)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Complex-valued version of `realLocalExpectation_boundaryDecay`.  Splitting
into real and imaginary parts costs only a universal factor two, so this form
applies directly to the project's complex local-observable API. -/
theorem complexLocalExpectation_boundaryDecay
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ₁ μ₂ : Measure (SpinConfig I S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (roots defects : Finset I)
    (g : SpinConfig I S → ℂ) (hg_meas : Measurable g)
    (B : ℝ) (hB_nonneg : 0 ≤ B) (hg_bound : ∀ σ, ‖g σ‖ ≤ B)
    (hg_int₁ : Integrable g μ₁) (hg_int₂ : Integrable g μ₂)
    (hg_local : ∀ σ τ, (∀ x ∈ roots, σ x = τ x) → g σ = g τ)
    (hDLR₁ : ∀ z, z ∉ defects → ∀ A : Set (SpinConfig I S),
      MeasurableSet A →
        (μ₁ A).toReal =
          ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₁)
    (hDLR₂ : ∀ z, z ∉ defects → ∀ A : Set (SpinConfig I S),
      MeasurableSet A →
        (μ₂ A).toReal =
          ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂)
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep : ∀ (z : I) (A : Set S), MeasurableSet A →
      ∀ σ τ : SpinConfig I S,
        (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' A)).toReal =
          (γ.condDist {z} τ ((· z) ⁻¹' A)).toReal)
    (dist : I → I → ℕ)
    (h_refl : ∀ x, dist x x = 0)
    (h_triangle : ∀ x y z, dist x y ≤ dist x z + dist z y)
    (h_support : ∀ x y, dist x y > 1 → influenceCoeff γ x y = 0)
    (r : ℕ)
    (hseparated : ∀ root ∈ roots, ∀ defect ∈ defects,
      r ≤ dist root defect) :
    ‖(∫ σ, g σ ∂μ₁) - ∫ σ, g σ ∂μ₂‖ ≤
      4 * B * (roots.card : ℝ) *
        (hD.α ^ r / (1 - hD.α)) := by
  let tail := hD.α ^ r / (1 - hD.α)
  let C := 2 * B * (roots.card : ℝ) * tail
  have hre := realLocalExpectation_boundaryDecay γ hD μ₁ μ₂ roots defects
    (fun σ => (g σ).re) (by fun_prop) B hB_nonneg
    (fun σ => (Complex.abs_re_le_norm (g σ)).trans (hg_bound σ))
    hg_int₁.re hg_int₂.re
    (fun σ τ hστ => congrArg Complex.re (hg_local σ τ hστ))
    hDLR₁ hDLR₂ hfinsupp h_dep dist h_refl h_triangle h_support r hseparated
  have him := realLocalExpectation_boundaryDecay γ hD μ₁ μ₂ roots defects
    (fun σ => (g σ).im) (by fun_prop) B hB_nonneg
    (fun σ => (Complex.abs_im_le_norm (g σ)).trans (hg_bound σ))
    hg_int₁.im hg_int₂.im
    (fun σ τ hστ => congrArg Complex.im (hg_local σ τ hστ))
    hDLR₁ hDLR₂ hfinsupp h_dep dist h_refl h_triangle h_support r hseparated
  have hre' : |((∫ σ, g σ ∂μ₁) - ∫ σ, g σ ∂μ₂).re| ≤ C := by
    rw [Complex.sub_re]
    change |RCLike.re (∫ σ, g σ ∂μ₁) -
      RCLike.re (∫ σ, g σ ∂μ₂)| ≤ C
    rw [← integral_re hg_int₁, ← integral_re hg_int₂]
    simpa only [C, tail] using hre
  have him' : |((∫ σ, g σ ∂μ₁) - ∫ σ, g σ ∂μ₂).im| ≤ C := by
    rw [Complex.sub_im]
    change |RCLike.im (∫ σ, g σ ∂μ₁) -
      RCLike.im (∫ σ, g σ ∂μ₂)| ≤ C
    rw [← integral_im hg_int₁, ← integral_im hg_int₂]
    simpa only [C, tail] using him
  calc
    ‖(∫ σ, g σ ∂μ₁) - ∫ σ, g σ ∂μ₂‖ ≤
        |((∫ σ, g σ ∂μ₁) - ∫ σ, g σ ∂μ₂).re| +
          |((∫ σ, g σ ∂μ₁) - ∫ σ, g σ ∂μ₂).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ C + C := add_le_add hre' him'
    _ = 4 * B * (roots.card : ℝ) *
        (hD.α ^ r / (1 - hD.α)) := by
      simp only [C, tail]
      ring

end

end YangMills.StrongCoupling
