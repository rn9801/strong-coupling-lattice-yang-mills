/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.Mayer
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Symmetry normalization for Mayer multi-indices

This file isolates the labelled-to-unlabelled factorial normalization in the
finite Mayer expansion.  A multi-index `X` has `degree! / ∏ X(γ)!` labelled
orderings.  Consequently division of the labelled exponential generating
function by `degree!` produces exactly the Mayer symmetry factor.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

namespace FinitePolymerModel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Total number of labelled polymer occurrences in a Mayer multi-index. -/
def mayerDegree (X : MayerMultiIndex P) : ℕ :=
  ∑ γ : P, X γ

/-- The finite set of multi-indices of a prescribed total degree. -/
def mayerMultiIndicesOfDegree (n : ℕ) : Finset (MayerMultiIndex P) :=
  (Finset.piAntidiag (Finset.univ : Finset P) n).map
    Finsupp.equivFunOnFinite.symm.toEmbedding

@[simp]
theorem mem_mayerMultiIndicesOfDegree (n : ℕ) (X : MayerMultiIndex P) :
    X ∈ mayerMultiIndicesOfDegree (P := P) n ↔ mayerDegree X = n := by
  rw [mayerMultiIndicesOfDegree, Finset.mem_map]
  constructor
  · rintro ⟨f, hf, hfeq⟩
    subst X
    exact (Finset.mem_piAntidiag.mp hf).1
  · intro hX
    refine ⟨X, ?_, by simp⟩
    exact Finset.mem_piAntidiag.mpr ⟨hX, fun _ _ => Finset.mem_univ _⟩

omit [DecidableEq P] in
@[simp]
theorem card_toMultiset_eq_mayerDegree (X : MayerMultiIndex P) :
    X.toMultiset.card = mayerDegree X := by
  rw [Finsupp.card_toMultiset, mayerDegree]
  exact Finsupp.sum_fintype X (fun _ n => n) (fun _ => rfl)

/-- The number of labelled orderings times the multi-index symmetry factor is
the factorial of the total degree. -/
theorem mayerSymmetryFactor_mul_countPerms
    (X : MayerMultiIndex P) :
    mayerSymmetryFactor X * X.toMultiset.countPerms =
      (mayerDegree X).factorial := by
  rw [mayerSymmetryFactor, Multiset.countPerms,
    Finsupp.toMultiset_toFinsupp,
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ X.support)]
  exact Nat.multinomial_spec Finset.univ X

/-- Residual symmetry factor after one occurrence of `root` has been
distinguished. -/
def pinnedMayerSymmetryFactor (X : MayerMultiIndex P) (root : P) : ℕ :=
  (X root - 1).factorial *
    ∏ γ ∈ (Finset.univ : Finset P).erase root, (X γ).factorial

/-- Multi-index obtained by deleting one distinguished root occurrence. -/
def eraseRootOccurrence (X : MayerMultiIndex P) (root : P) :
    MayerMultiIndex P :=
  X.update root (X root - 1)

/-- The residual pinned factor is the ordinary symmetry factor after deleting
one occurrence of the distinguished label. -/
theorem mayerSymmetryFactor_eraseRootOccurrence_eq_pinnedMayerSymmetryFactor
    (X : MayerMultiIndex P) (root : P) :
    mayerSymmetryFactor (eraseRootOccurrence X root) =
      pinnedMayerSymmetryFactor X root := by
  classical
  unfold mayerSymmetryFactor pinnedMayerSymmetryFactor eraseRootOccurrence
  rw [← Finset.mul_prod_erase (Finset.univ : Finset P)
    (fun γ => ((X.update root (X root - 1)) γ).factorial)
    (Finset.mem_univ root)]
  apply congrArg₂ (fun a b : ℕ => a * b)
  · simp
  · apply Finset.prod_congr rfl
    intro γ hγ
    have hne : γ ≠ root := Finset.ne_of_mem_erase hγ
    simp [hne]

/-- Distinguishing one of the `X root` occurrences removes exactly that
factor from the full Mayer symmetry factor. -/
theorem mayerSymmetryFactor_eq_mul_pinnedMayerSymmetryFactor
    (X : MayerMultiIndex P) (root : P) (hroot : X root ≠ 0) :
    mayerSymmetryFactor X =
      X root * pinnedMayerSymmetryFactor X root := by
  classical
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hroot
  unfold mayerSymmetryFactor pinnedMayerSymmetryFactor
  rw [← Finset.mul_prod_erase (Finset.univ : Finset P)
    (fun γ => (X γ).factorial) (Finset.mem_univ root)]
  rw [hn, Nat.factorial_succ]
  simp only [Nat.succ_sub_one]
  simp [Nat.succ_eq_add_one, mul_comm, mul_left_comm, mul_assoc]

/-- Real-valued pinned orbit normalization. -/
theorem natCast_div_mayerSymmetryFactor_eq_inv_pinned
    (X : MayerMultiIndex P) (root : P) (hroot : X root ≠ 0) :
    (X root : ℝ) / (mayerSymmetryFactor X : ℝ) =
      1 / (pinnedMayerSymmetryFactor X root : ℝ) := by
  rw [mayerSymmetryFactor_eq_mul_pinnedMayerSymmetryFactor X root hroot]
  push_cast
  have hx : (X root : ℝ) ≠ 0 := by exact_mod_cast hroot
  have hp : (pinnedMayerSymmetryFactor X root : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_ne_zero (by
      exact mul_ne_zero (Nat.factorial_ne_zero _) (Finset.prod_ne_zero_iff.mpr
        (fun γ _ => Nat.factorial_ne_zero (X γ)))))
  field_simp

/-- Exact labelled-to-symmetric normalization over `ℂ`. -/
theorem countPerms_div_factorial_eq_inv_mayerSymmetryFactor
    (X : MayerMultiIndex P) :
    (X.toMultiset.countPerms : ℂ) / ((mayerDegree X).factorial : ℂ) =
      1 / (mayerSymmetryFactor X : ℂ) := by
  have hfac : ((mayerDegree X).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (mayerDegree X)
  have hsym : (mayerSymmetryFactor X : ℂ) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr
      (fun γ _ => Nat.factorial_ne_zero (X γ))
  apply (div_eq_div_iff hfac hsym).mpr
  norm_cast
  simpa [mul_comm] using mayerSymmetryFactor_mul_countPerms X

/-- Multiplying any unlabelled cluster weight by the normalized number of its
labelled orderings produces its usual Mayer symmetry factor. -/
theorem countPerms_normalizes_clusterWeight
    (X : MayerMultiIndex P) (z : ℂ) :
    ((X.toMultiset.countPerms : ℂ) / ((mayerDegree X).factorial : ℂ)) * z =
      z / (mayerSymmetryFactor X : ℂ) := by
  rw [countPerms_div_factorial_eq_inv_mayerSymmetryFactor]
  ring

/-- Degree-by-degree exponential-generating-function normalization.  This is
the exact finite sum that converts labelled multiplicities into the symmetric
multi-index convention. -/
theorem sum_countPerms_div_factorial_eq_sum_div_mayerSymmetryFactor
    (n : ℕ) (weight : MayerMultiIndex P → ℂ) :
    ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        ((X.toMultiset.countPerms : ℂ) / (n.factorial : ℂ)) * weight X =
      ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        weight X / (mayerSymmetryFactor X : ℂ) := by
  apply Finset.sum_congr rfl
  intro X hX
  have hdegree : mayerDegree X = n :=
    (mem_mayerMultiIndicesOfDegree n X).mp hX
  rw [← hdegree, countPerms_normalizes_clusterWeight]

/-- Symmetric Mayer normalization for the actual Ursell/activity weight. -/
theorem labelledMayerDegreeSum_eq_symmetricClusterSum
    (M : FinitePolymerModel P) (n : ℕ) :
    ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        ((X.toMultiset.countPerms : ℂ) / (n.factorial : ℂ)) *
          ((M.mayerUrsell X : ℂ) * M.mayerActivityMonomial X) =
      ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        M.mayerClusterTerm X := by
  rw [sum_countPerms_div_factorial_eq_sum_div_mayerSymmetryFactor]
  apply Finset.sum_congr rfl
  intro X _
  unfold mayerClusterTerm
  ring

/-- The degree-`n` coefficient in the symmetric Mayer convention. -/
def symmetricMayerDegreeSum (M : FinitePolymerModel P) (n : ℕ) : ℂ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n, M.mayerClusterTerm X

/-- There is no connected Mayer contribution of total degree zero. -/
@[simp]
theorem symmetricMayerDegreeSum_zero (M : FinitePolymerModel P) :
    M.symmetricMayerDegreeSum 0 = 0 := by
  unfold symmetricMayerDegreeSum
  simp only [mayerMultiIndicesOfDegree, Finset.piAntidiag_zero]
  rw [Finset.sum_map, Finset.sum_singleton]
  apply M.mayerClusterTerm_eq_zero_of_not_connected
  intro hconnected
  rcases hconnected.nonempty with ⟨⟨γ, i⟩⟩
  simpa using i.isLt


/-- Degree-`n` symmetric Mayer coefficient with one occurrence of `root`
distinguished. -/
def pinnedSymmetricMayerDegreeSum
    (M : FinitePolymerModel P) (root : P) (n : ℕ) : ℂ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
    (X root : ℂ) * M.mayerClusterTerm X

/-- Summing over the distinguished root label counts every degree-`n`
cluster exactly `n` times.  This is the finite normalization identity used to
recover the unpinned series from pinned KP estimates. -/
theorem sum_pinnedSymmetricMayerDegreeSum
    (M : FinitePolymerModel P) (n : ℕ) :
    ∑ root : P, M.pinnedSymmetricMayerDegreeSum root n =
      (n : ℂ) * M.symmetricMayerDegreeSum n := by
  classical
  unfold pinnedSymmetricMayerDegreeSum symmetricMayerDegreeSum
  calc
    (∑ root : P, ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        (X root : ℂ) * M.mayerClusterTerm X) =
        ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
          ∑ root : P, (X root : ℂ) * M.mayerClusterTerm X := by
      rw [Finset.sum_comm]
    _ = ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        (n : ℂ) * M.mayerClusterTerm X := by
      apply Finset.sum_congr rfl
      intro X hX
      rw [← Finset.sum_mul]
      congr 1
      norm_cast
      exact (mem_mayerMultiIndicesOfDegree n X).mp hX
    _ = (n : ℂ) * ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        M.mayerClusterTerm X := by
      rw [Finset.mul_sum]

/-- The full symmetric multi-index Mayer series, organized by total
multiplicity.  Convergence is deliberately kept separate from this
normalization definition. -/
def symmetricMayerSum (M : FinitePolymerModel P) : ℂ :=
  ∑' n : ℕ, M.symmetricMayerDegreeSum n

/-- The labelled orbit sum is exactly the symmetric degree coefficient. -/
theorem labelledMayerDegreeSum_eq_symmetricMayerDegreeSum
    (M : FinitePolymerModel P) (n : ℕ) :
    ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        ((X.toMultiset.countPerms : ℂ) / (n.factorial : ℂ)) *
          ((M.mayerUrsell X : ℂ) * M.mayerActivityMonomial X) =
      M.symmetricMayerDegreeSum n := by
  exact M.labelledMayerDegreeSum_eq_symmetricClusterSum n

end FinitePolymerModel

end

end YangMills.Polymer
