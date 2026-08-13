/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.MayerNormalization
import YangMills.Polymer.Whitney
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The genuine finite Kotecký--Preiss condition

This module records the standard activity-sum hypothesis used by the rooted
tree expansion.  It is intentionally distinct from the deletion-ratio
`DobrushinCertificate`: the latter proves zero-freeness, while this condition
is the one whose iterated tree branching closes absolute Mayer summability.

The Penrose tree-graph inequality and the rooted-tree iteration consume this
certificate.  The concrete plaquette gas discharges it from the same animal
counting estimates and explicit strong-coupling disk.
-/

namespace YangMills.Polymer

open scoped BigOperators
open Filter

noncomputable section

namespace FinitePolymerModel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Standard finite Kotecký--Preiss activity-sum certificate. -/
def KoteckyPreissCertificate (M : FinitePolymerModel P) (S : Finset P)
    (a : P → ℝ) : Prop :=
  (∀ γ, 0 ≤ a γ) ∧
    ∀ γ ∈ S,
      ∑ δ ∈ S.filter (M.incompatible γ),
          ‖M.activity δ‖ * Real.exp (a δ) ≤ a γ

theorem koteckyPreiss_weight_nonneg
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate S a) (γ : P) :
    0 ≤ a γ :=
  hKP.1 γ

theorem sum_incompatible_tiltedActivity_le
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate S a) {γ : P} (hγS : γ ∈ S) :
    ∑ δ ∈ S.filter (M.incompatible γ),
        ‖M.activity δ‖ * Real.exp (a δ) ≤ a γ :=
  hKP.2 γ hγS

/-! ## Mayer terms dominated by the concrete tree graph sum -/

/-- Symmetry-normalized spanning-tree majorant for a Mayer multi-index. -/
def mayerTreeMajorant (M : FinitePolymerModel P)
    (X : MayerMultiIndex P) : ℝ :=
  ((graphSpanningTrees (M.mayerIncompatibilityGraph X)).card : ℝ) /
      (mayerSymmetryFactor X : ℝ) *
    ∏ γ : P, ‖M.activity γ‖ ^ X γ

theorem norm_mayerActivityMonomial
    (M : FinitePolymerModel P) (X : MayerMultiIndex P) :
    ‖M.mayerActivityMonomial X‖ =
      ∏ γ : P, ‖M.activity γ‖ ^ X γ := by
  simp [mayerActivityMonomial, norm_prod, norm_pow]

/-- The unconditional Whitney inequality gives the sharp, termwise Mayer
tree bound, with the exact multi-index symmetry factor. -/
theorem norm_mayerClusterTerm_le_mayerTreeMajorant
    (M : FinitePolymerModel P) (X : MayerMultiIndex P) :
    ‖M.mayerClusterTerm X‖ ≤ M.mayerTreeMajorant X := by
  have htree := Whitney.abs_connectedSpanningGraphSum_le_card_trees
    (M.mayerIncompatibilityGraph X)
  have hursell : ‖(M.mayerUrsell X : ℂ)‖ ≤
      ((graphSpanningTrees (M.mayerIncompatibilityGraph X)).card : ℝ) := by
    rw [mayerUrsell, mayerUrsellGraph, Complex.norm_intCast]
    exact_mod_cast htree
  unfold mayerClusterTerm mayerTreeMajorant
  rw [norm_mul, norm_div, norm_mayerActivityMonomial]
  simp only [Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hursell (Nat.cast_nonneg _))
    (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)

/-- Multiplicity-pinned Mayer terms inherit the same sharp tree majorant. -/
theorem pinned_norm_mayerClusterTerm_le_tree
    (M : FinitePolymerModel P) (root : P) (X : MayerMultiIndex P) :
    (X root : ℝ) * ‖M.mayerClusterTerm X‖ ≤
      (X root : ℝ) * M.mayerTreeMajorant X := by
  exact mul_le_mul_of_nonneg_left
    (M.norm_mayerClusterTerm_le_mayerTreeMajorant X) (Nat.cast_nonneg _)

/-- Absolute degree-`n` Mayer sum. -/
def normMayerDegreeSum (M : FinitePolymerModel P) (n : ℕ) : ℝ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
    ‖M.mayerClusterTerm X‖

/-- Triangle-inequality comparison between the connected coefficient and
the absolute Mayer degree sum. -/
theorem norm_symmetricMayerDegreeSum_le
    (M : FinitePolymerModel P) (n : ℕ) :
    ‖M.symmetricMayerDegreeSum n‖ ≤ M.normMayerDegreeSum n := by
  unfold symmetricMayerDegreeSum normMayerDegreeSum
  exact norm_sum_le _ _

/-- Absolute degree-`n` Mayer sum with one root occurrence distinguished. -/
def pinnedNormMayerDegreeSum
    (M : FinitePolymerModel P) (root : P) (n : ℕ) : ℝ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
    (X root : ℝ) * ‖M.mayerClusterTerm X‖

/-- The exact nonnegative counterpart of
`sum_pinnedSymmetricMayerDegreeSum`: pinned absolute bounds recover the full
absolute degree sum with the factor `n`. -/
theorem sum_pinnedNormMayerDegreeSum
    (M : FinitePolymerModel P) (n : ℕ) :
    ∑ root : P, M.pinnedNormMayerDegreeSum root n =
      (n : ℝ) * M.normMayerDegreeSum n := by
  classical
  unfold pinnedNormMayerDegreeSum normMayerDegreeSum
  calc
    (∑ root : P, ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        (X root : ℝ) * ‖M.mayerClusterTerm X‖) =
        ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
          ∑ root : P, (X root : ℝ) * ‖M.mayerClusterTerm X‖ := by
      rw [Finset.sum_comm]
    _ = ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        (n : ℝ) * ‖M.mayerClusterTerm X‖ := by
      apply Finset.sum_congr rfl
      intro X hX
      rw [← Finset.sum_mul]
      congr 1
      norm_cast
      exact (mem_mayerMultiIndicesOfDegree n X).mp hX
    _ = (n : ℝ) * ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        ‖M.mayerClusterTerm X‖ := by
      rw [Finset.mul_sum]

/-- Summability of every positive-degree pinned absolute series implies
summability of the full positive-degree absolute Mayer series. -/
theorem summable_normMayerDegreeSum_succ_of_pinned
    (M : FinitePolymerModel P)
    (hpin : ∀ root : P,
      Summable (fun n : ℕ => M.pinnedNormMayerDegreeSum root (n + 1))) :
    Summable (fun n : ℕ => M.normMayerDegreeSum (n + 1)) := by
  have hsum : Summable (fun n : ℕ =>
      ∑ root : P, M.pinnedNormMayerDegreeSum root (n + 1)) :=
    summable_sum (s := (Finset.univ : Finset P))
      (fun root _ => hpin root)
  apply Summable.of_nonneg_of_le
    (fun n => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (fun n => ?_) hsum
  have hnonneg : 0 ≤ M.normMayerDegreeSum (n + 1) :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc
    M.normMayerDegreeSum (n + 1) ≤
        ((n + 1 : ℕ) : ℝ) * M.normMayerDegreeSum (n + 1) := by
      apply le_mul_of_one_le_left hnonneg
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    _ = ∑ root : P,
        M.pinnedNormMayerDegreeSum root (n + 1) :=
      (M.sum_pinnedNormMayerDegreeSum (n + 1)).symm

/-! ## Rooted-tree fixed-point majorant -/

/-- Height-truncated rooted-tree generating function.  The exponential is
the symmetry-normalized generating function for an unordered collection of
children, and each child label must be incompatible with its parent. -/
def kpTreeIterate (M : FinitePolymerModel P) (S : Finset P) : ℕ → P → ℝ
  | 0, _ => 1
  | n + 1, γ => Real.exp <|
      ∑ δ ∈ S.filter (M.incompatible γ),
        ‖M.activity δ‖ * M.kpTreeIterate S n δ

@[simp]
theorem kpTreeIterate_zero (M : FinitePolymerModel P) (S : Finset P) (γ : P) :
    M.kpTreeIterate S 0 γ = 1 := rfl

@[simp]
theorem kpTreeIterate_succ (M : FinitePolymerModel P) (S : Finset P)
    (n : ℕ) (γ : P) :
    M.kpTreeIterate S (n + 1) γ = Real.exp
      (∑ δ ∈ S.filter (M.incompatible γ),
        ‖M.activity δ‖ * M.kpTreeIterate S n δ) := rfl

theorem kpTreeIterate_pos (M : FinitePolymerModel P) (S : Finset P)
    (n : ℕ) (γ : P) :
    0 < M.kpTreeIterate S n γ := by
  cases n with
  | zero => simp
  | succ n => simp only [kpTreeIterate_succ]; exact Real.exp_pos _

/-- Adding one more possible tree generation only increases the majorant. -/
theorem kpTreeIterate_le_succ (M : FinitePolymerModel P) (S : Finset P) :
    ∀ n γ, M.kpTreeIterate S n γ ≤ M.kpTreeIterate S (n + 1) γ := by
  intro n
  induction n with
  | zero =>
      intro γ
      rw [kpTreeIterate_zero, kpTreeIterate_succ]
      exact Real.one_le_exp <| Finset.sum_nonneg fun δ _ =>
        mul_nonneg (norm_nonneg _) (M.kpTreeIterate_pos S 0 δ).le
  | succ n ih =>
      intro γ
      rw [kpTreeIterate_succ, kpTreeIterate_succ]
      apply Real.exp_le_exp.mpr
      apply Finset.sum_le_sum
      intro δ _
      exact mul_le_mul_of_nonneg_left (ih δ) (norm_nonneg _)

theorem monotone_kpTreeIterate (M : FinitePolymerModel P) (S : Finset P)
    (γ : P) :
    Monotone (fun n => M.kpTreeIterate S n γ) :=
  monotone_nat_of_le_succ fun n => M.kpTreeIterate_le_succ S n γ

/-- The KP activity inequality closes the rooted-tree iteration at `exp a`. -/
theorem kpTreeIterate_le_exp_of_koteckyPreiss
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate S a) :
    ∀ n, ∀ γ ∈ S, M.kpTreeIterate S n γ ≤ Real.exp (a γ) := by
  intro n
  induction n with
  | zero =>
      intro γ _
      rw [kpTreeIterate_zero]
      exact Real.one_le_exp (hKP.1 γ)
  | succ n ih =>
      intro γ hγS
      rw [kpTreeIterate_succ]
      apply Real.exp_le_exp.mpr
      calc
        ∑ δ ∈ S.filter (M.incompatible γ),
            ‖M.activity δ‖ * M.kpTreeIterate S n δ ≤
            ∑ δ ∈ S.filter (M.incompatible γ),
              ‖M.activity δ‖ * Real.exp (a δ) := by
          apply Finset.sum_le_sum
          intro δ hδ
          exact mul_le_mul_of_nonneg_left
            (ih δ (Finset.mem_filter.mp hδ).1) (norm_nonneg _)
        _ ≤ a γ := hKP.2 γ hγS

/-- Successive height layers in the rooted-tree majorant. -/
def kpTreeLayer (M : FinitePolymerModel P) (S : Finset P)
    (γ : P) (n : ℕ) : ℝ :=
  M.kpTreeIterate S (n + 1) γ - M.kpTreeIterate S n γ

theorem kpTreeLayer_nonneg (M : FinitePolymerModel P) (S : Finset P)
    (γ : P) (n : ℕ) :
    0 ≤ M.kpTreeLayer S γ n :=
  sub_nonneg.mpr (M.kpTreeIterate_le_succ S n γ)

/-- Genuine rooted-tree summability: the nonnegative height layers have a
finite sum bounded by the standard KP budget `exp (a γ) - 1`. -/
theorem summable_kpTreeLayer_of_koteckyPreiss
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate S a) (γ : P) (hγS : γ ∈ S) :
    Summable (M.kpTreeLayer S γ) := by
  let u : ℕ → ℝ := fun n => M.kpTreeIterate S n γ
  have hmono : Monotone u := M.monotone_kpTreeIterate S γ
  have hbdd : BddAbove (Set.range u) := by
    refine ⟨Real.exp (a γ), ?_⟩
    rintro _ ⟨n, rfl⟩
    exact M.kpTreeIterate_le_exp_of_koteckyPreiss S a hKP n γ hγS
  have htend : Tendsto u atTop (nhds (sSup (Set.range u))) :=
    tendsto_atTop_ciSup hmono hbdd
  have htel : (fun n => ∑ i ∈ Finset.range n, M.kpTreeLayer S γ i) =
      fun n => u n - 1 := by
    funext n
    rw [show (∑ i ∈ Finset.range n, M.kpTreeLayer S γ i) =
        u n - u 0 by
      simpa [kpTreeLayer, u] using Finset.sum_range_sub u n]
    simp [u]
  have hpartial : Tendsto
      (fun n => ∑ i ∈ Finset.range n, M.kpTreeLayer S γ i)
      atTop (nhds (sSup (Set.range u) - 1)) := by
    rw [htel]
    exact htend.sub tendsto_const_nhds
  exact ((hasSum_iff_tendsto_nat_of_nonneg
    (M.kpTreeLayer_nonneg S γ) _).mpr hpartial).summable

theorem tsum_kpTreeLayer_le_exp_sub_one_of_koteckyPreiss
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate S a) (γ : P) (hγS : γ ∈ S) :
    ∑' n : ℕ, M.kpTreeLayer S γ n ≤ Real.exp (a γ) - 1 := by
  let u : ℕ → ℝ := fun n => M.kpTreeIterate S n γ
  have hmono : Monotone u := M.monotone_kpTreeIterate S γ
  have hbdd : BddAbove (Set.range u) := by
    refine ⟨Real.exp (a γ), ?_⟩
    rintro _ ⟨n, rfl⟩
    exact M.kpTreeIterate_le_exp_of_koteckyPreiss S a hKP n γ hγS
  have hsup : sSup (Set.range u) ≤ Real.exp (a γ) :=
    csSup_le (Set.range_nonempty u) (by
      rintro _ ⟨n, rfl⟩
      exact M.kpTreeIterate_le_exp_of_koteckyPreiss S a hKP n γ hγS)
  have hsum := M.summable_kpTreeLayer_of_koteckyPreiss S a hKP γ hγS
  have htend : Tendsto u atTop (nhds (sSup (Set.range u))) :=
    tendsto_atTop_ciSup hmono hbdd
  have hhas : HasSum (M.kpTreeLayer S γ) (sSup (Set.range u) - 1) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg
      (M.kpTreeLayer_nonneg S γ) _).mpr
    have htel : (fun n => ∑ i ∈ Finset.range n, M.kpTreeLayer S γ i) =
        fun n => u n - 1 := by
      funext n
      rw [show (∑ i ∈ Finset.range n, M.kpTreeLayer S γ i) =
          u n - u 0 by
        simpa [kpTreeLayer, u] using Finset.sum_range_sub u n]
      simp [u]
    rw [htel]
    exact htend.sub tendsto_const_nhds
  rw [hhas.tsum_eq]
  linarith

end FinitePolymerModel

end

end YangMills.Polymer
