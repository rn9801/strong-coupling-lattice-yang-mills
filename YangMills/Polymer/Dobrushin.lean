/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.FiniteGas
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A finite Dobrushin--Kotecký--Preiss criterion

This file proves a genuinely local zero-free criterion for a finite hard-core
polymer gas.  The proof uses deletion ratios and telescopes them over the
polymers incompatible with a marked polymer.  It is independent of every
Yang--Mills module.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

namespace FinitePolymerModel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Finite Dobrushin criterion in the form naturally used by deletion-ratio
induction. -/
def DobrushinCertificate (M : FinitePolymerModel P) (S : Finset P)
    (a : P → ℝ) : Prop :=
  (∀ γ, 0 ≤ a γ) ∧
    ∀ γ ∈ S,
      ‖M.activity γ‖ * Real.exp
          (∑ δ ∈ S.filter (M.incompatible γ), a δ) ≤
        1 - Real.exp (-a γ)

/-- Telescope deletion ratios from a set `U` down to a subset `V`. -/
private theorem partition_ratio_subset_le
    (M : FinitePolymerModel P) (a : P → ℝ) (T U V : Finset P)
    (hUT : U ⊂ T) (hVU : V ⊆ U)
    (hnonzero : ∀ R ⊂ T, M.partitionOn R ≠ 0)
    (hratio : ∀ R ⊂ T, ∀ δ ∈ R,
      Real.exp (-a δ) ≤ ‖M.partitionOn R / M.partitionOn (R.erase δ)‖) :
    ‖M.partitionOn V / M.partitionOn U‖ ≤
      Real.exp (∑ δ ∈ U \ V, a δ) := by
  classical
  induction U using Finset.strongInductionOn with
  | _ R rec =>
    by_cases hRV : R = V
    · subst R
      simp [hnonzero V hUT]
    · have hdiff : (R \ V).Nonempty :=
        Finset.sdiff_nonempty.mpr (fun h => hRV (Finset.Subset.antisymm h hVU))
      obtain ⟨δ, hδdiff⟩ := hdiff
      have hδR : δ ∈ R := (Finset.mem_sdiff.mp hδdiff).1
      have hδV : δ ∉ V := (Finset.mem_sdiff.mp hδdiff).2
      let R' := R.erase δ
      have hR'R : R' ⊂ R := Finset.erase_ssubset hδR
      have hVR' : V ⊆ R' := by
        intro x hx
        exact Finset.mem_erase.mpr ⟨fun h => hδV (h ▸ hx), hVU hx⟩
      have hR'T : R' ⊂ T := hR'R.trans hUT
      have hrec := rec R' hR'R hR'T hVR'
      have hRzero := hnonzero R hUT
      have hR'zero := hnonzero R' hR'T
      have hratioδ := hratio R hUT δ hδR
      have hreverse : ‖M.partitionOn R' / M.partitionOn R‖ ≤
          Real.exp (a δ) := by
        rw [norm_div] at hratioδ ⊢
        have hposR : 0 < ‖M.partitionOn R‖ := norm_pos_iff.mpr hRzero
        have hposR' : 0 < ‖M.partitionOn R'‖ := norm_pos_iff.mpr hR'zero
        have hmul : Real.exp (-a δ) * ‖M.partitionOn R'‖ ≤
            ‖M.partitionOn R‖ := (le_div_iff₀ hposR').mp hratioδ
        apply (div_le_iff₀ hposR).mpr
        calc
          ‖M.partitionOn R'‖ = Real.exp (a δ) *
              (Real.exp (-a δ) * ‖M.partitionOn R'‖) := by
            rw [← mul_assoc, ← Real.exp_add]
            simp
          _ ≤ Real.exp (a δ) * ‖M.partitionOn R‖ :=
            mul_le_mul_of_nonneg_left hmul (Real.exp_pos _).le
      have hfactor : M.partitionOn V / M.partitionOn R =
          (M.partitionOn V / M.partitionOn R') *
            (M.partitionOn R' / M.partitionOn R) := by
        field_simp
      rw [hfactor, norm_mul]
      calc
        ‖M.partitionOn V / M.partitionOn R'‖ *
            ‖M.partitionOn R' / M.partitionOn R‖ ≤
            Real.exp (∑ x ∈ R' \ V, a x) * Real.exp (a δ) :=
          mul_le_mul hrec hreverse (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (∑ x ∈ R \ V, a x) := by
          rw [← Real.exp_add]
          congr 1
          have hdecomp : R \ V = insert δ (R' \ V) := by
            calc
              R \ V = (insert δ R') \ V := by
                rw [Finset.insert_erase hδR]
              _ = insert δ (R' \ V) := by
                ext x
                by_cases hx : x = δ
                · subst x
                  simp [hδV]
                · simp [hx]
          have hδnot : δ ∉ R' \ V := by simp [R']
          rw [hdecomp, Finset.sum_insert hδnot]
          ring

omit [DecidableEq P] in
/-- The local Dobrushin criterion controls all deletion ratios and, in
particular, makes every restricted partition function nonzero. -/
theorem partitionOn_ne_zero_of_dobrushin
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hD : M.DobrushinCertificate S a) :
    ∀ T ⊆ S, M.partitionOn T ≠ 0 := by
  classical
  have hmain : ∀ T : Finset P, T ⊆ S →
      M.partitionOn T ≠ 0 ∧
        ∀ γ ∈ T, Real.exp (-a γ) ≤
          ‖M.partitionOn T / M.partitionOn (T.erase γ)‖ := by
    intro T
    induction T using Finset.strongInductionOn with
    | _ T ih =>
      intro hTS
      have hproper (R : Finset P) (hRT : R ⊂ T) :
          M.partitionOn R ≠ 0 ∧
            ∀ γ ∈ R, Real.exp (-a γ) ≤
              ‖M.partitionOn R / M.partitionOn (R.erase γ)‖ :=
        ih R hRT (Finset.Subset.trans hRT.1 hTS)
      by_cases hT : T = ∅
      · subst T
        simp
      · have hratioFor : ∀ γ ∈ T, Real.exp (-a γ) ≤
            ‖M.partitionOn T / M.partitionOn (T.erase γ)‖ := by
          intro γ hγ
          let U := T.erase γ
          let V := M.compatibleWith U γ
          have hUT : U ⊂ T := Finset.erase_ssubset hγ
          have hUzero : M.partitionOn U ≠ 0 := (hproper U hUT).1
          have hVU : V ⊆ U := Finset.filter_subset _ _
          have htelescope := partition_ratio_subset_le M a T U V hUT hVU
            (fun R hRT => (hproper R hRT).1)
            (fun R hRT δ hδ => (hproper R hRT).2 δ hδ)
          have hsumSubset : U \ V ⊆ S.filter (M.incompatible γ) := by
            intro δ hδ
            have hδU := (Finset.mem_sdiff.mp hδ).1
            have hδnotV := (Finset.mem_sdiff.mp hδ).2
            have hδT : δ ∈ T := Finset.mem_of_mem_erase hδU
            apply Finset.mem_filter.mpr
            refine ⟨hTS hδT, ?_⟩
            by_contra hcompat
            exact hδnotV (Finset.mem_filter.mpr ⟨hδU, hcompat⟩)
          have hsum : (∑ δ ∈ U \ V, a δ) ≤
              ∑ δ ∈ S.filter (M.incompatible γ), a δ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsumSubset
              (fun δ _ _ => hD.1 δ)
          have hperturb : ‖M.activity γ *
                (M.partitionOn V / M.partitionOn U)‖ ≤
              1 - Real.exp (-a γ) := by
            calc
              _ = ‖M.activity γ‖ * ‖M.partitionOn V / M.partitionOn U‖ :=
                norm_mul _ _
              _ ≤ ‖M.activity γ‖ * Real.exp (∑ δ ∈ U \ V, a δ) :=
                mul_le_mul_of_nonneg_left htelescope (norm_nonneg _)
              _ ≤ ‖M.activity γ‖ * Real.exp
                    (∑ δ ∈ S.filter (M.incompatible γ), a δ) := by
                gcongr
              _ ≤ 1 - Real.exp (-a γ) := hD.2 γ (hTS hγ)
          have hratioEq : M.partitionOn T / M.partitionOn U =
              1 + M.activity γ * (M.partitionOn V / M.partitionOn U) := by
            rw [M.partitionOn_delete T hγ]
            field_simp
            ring
          rw [hratioEq]
          calc
            Real.exp (-a γ) = 1 - (1 - Real.exp (-a γ)) := by ring
            _ ≤ 1 - ‖M.activity γ * (M.partitionOn V / M.partitionOn U)‖ :=
              sub_le_sub_left hperturb 1
            _ ≤ ‖1 + M.activity γ * (M.partitionOn V / M.partitionOn U)‖ := by
              simpa [norm_neg, sub_neg_eq_add] using
                norm_sub_norm_le (1 : ℂ)
                  (-(M.activity γ * (M.partitionOn V / M.partitionOn U)))
        have hTnonzero : M.partitionOn T ≠ 0 := by
          obtain ⟨γ, hγ⟩ := Finset.nonempty_iff_ne_empty.mpr hT
          intro hzero
          have hlower := hratioFor γ hγ
          rw [hzero, zero_div, norm_zero] at hlower
          exact (not_le_of_gt (Real.exp_pos (-a γ))) hlower
        exact ⟨hTnonzero, hratioFor⟩
  exact fun T hTS => (hmain T hTS).1

omit [DecidableEq P] in
/-- Full-partition specialization of the finite Dobrushin theorem. -/
theorem partitionFunction_ne_zero_of_dobrushin
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hD : M.DobrushinCertificate Finset.univ a) :
    M.partitionFunction ≠ 0 := by
  unfold partitionFunction
  exact M.partitionOn_ne_zero_of_dobrushin Finset.univ a hD
    Finset.univ (Finset.subset_univ _)

end FinitePolymerModel

end

end YangMills.Polymer
