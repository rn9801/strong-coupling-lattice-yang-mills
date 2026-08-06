/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import MarkovSemigroups.DobrushinZegarlinski.AbstractInfluence

/-!
# Marked influence bounds for finite polymer systems

This module is independent of the Yang--Mills model.  It packages the last,
purely linear step of a polymer comparison argument: once a marked response is
bounded by the Neumann series of a nonnegative influence matrix, finite-range
support turns graph separation into an exponential estimate.

The Neumann-series backend is the Apache-2.0-licensed
`AbstractInfluenceMatrix` of Michael R. Douglas' pinned
`markov-semigroups` repository.  The declarations below add the marked-root
and defect-set interface needed by the polymer expansion.
-/

namespace YangMills.Polymer

open MarkovSemigroups.DobrushinZegarlinski

noncomputable section

variable {P : Type*} [DecidableEq P]

/-- Entrywise Neumann influence from `root` to `defect`. -/
def neumannInfluence (M : AbstractInfluenceMatrix P) (root defect : P) : ℝ :=
  ∑' n : ℕ, M.iterate n root defect

theorem neumannInfluence_nonneg (M : AbstractInfluenceMatrix P)
    (root defect : P) :
    0 ≤ neumannInfluence M root defect := by
  exact tsum_nonneg fun n => M.iterate_nonneg n root defect

/-- Total Neumann influence from one root into a finite defect set.  The
defects are summed *inside* the path-length series; consequently the uniform
row bound controls the whole set without a factor proportional to its size. -/
def neumannInfluenceToSet (M : AbstractInfluenceMatrix P) (root : P)
    (defects : Finset P) : ℝ :=
  ∑' n : ℕ, ∑ defect ∈ defects, M.iterate n root defect

theorem neumannInfluenceToSet_nonneg (M : AbstractInfluenceMatrix P)
    (root : P) (defects : Finset P) :
    0 ≤ neumannInfluenceToSet M root defects := by
  exact tsum_nonneg fun n => Finset.sum_nonneg fun defect _ =>
    M.iterate_nonneg n root defect

/-- A finite defect set at distance at least `r` receives at most the
geometric Neumann tail `α^r / (1-α)`. -/
theorem neumannInfluenceToSet_le_exponential
    (M : AbstractInfluenceMatrix P) (dist : P → P → ℕ)
    (h_refl : ∀ x, dist x x = 0)
    (h_triangle : ∀ x y z, dist x y ≤ dist x z + dist z y)
    (h_support : ∀ x y, dist x y > 1 → M.entry x y = 0)
    (root : P) (defects : Finset P) (r : ℕ)
    (hseparated : ∀ defect ∈ defects, r ≤ dist root defect) :
    neumannInfluenceToSet M root defects ≤
      M.α ^ r / (1 - M.α) := by
  let f : ℕ → ℝ := fun n => ∑ defect ∈ defects, M.iterate n root defect
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n =>
    Finset.sum_nonneg fun defect _ => M.iterate_nonneg n root defect
  have hf_bound : ∀ n, f n ≤ M.α ^ n := by
    intro n
    exact ((M.iterate_row_summable n root).sum_le_tsum defects
      (fun defect _ => M.iterate_nonneg n root defect)).trans
        (M.iterate_row_sum_bound n root)
  have hf_summable : Summable f :=
    Summable.of_nonneg_of_le hf_nonneg hf_bound
      (summable_geometric_of_lt_one M.α_nonneg M.α_lt_one)
  have hf_zero : ∀ n, n < r → f n = 0 := by
    intro n hn
    apply Finset.sum_eq_zero
    intro defect hdefect
    apply M.iterate_dist_zero dist 1 Nat.one_pos h_refl h_triangle h_support
    simpa only [mul_one] using hn.trans_le (hseparated defect hdefect)
  let b : ℕ → ℝ := fun n => if n < r then 0 else M.α ^ n
  have hb_nonneg : ∀ n, 0 ≤ b n := fun n => by
    by_cases hn : n < r
    · simp [b, hn]
    · simp [b, hn, pow_nonneg M.α_nonneg]
  have hb_le : ∀ n, b n ≤ M.α ^ n := fun n => by
    by_cases hn : n < r
    · simp [b, hn, pow_nonneg M.α_nonneg]
    · simp [b, hn]
  have hb_summable : Summable b :=
    Summable.of_nonneg_of_le hb_nonneg hb_le
      (summable_geometric_of_lt_one M.α_nonneg M.α_lt_one)
  have hfb : ∀ n, f n ≤ b n := by
    intro n
    by_cases hn : n < r
    · simp [b, hn, hf_zero n hn]
    · simpa [b, hn] using hf_bound n
  have hb_sum : ∑' n, b n = M.α ^ r * (1 - M.α)⁻¹ := by
    have hinj : Function.Injective (fun m : ℕ => m + r) := by
      intro a a' h
      exact Nat.add_right_cancel h
    have hsupp : Function.support b ⊆ Set.range (fun m : ℕ => m + r) := by
      intro n hn
      have hnr : r ≤ n := by
        apply Nat.not_lt.mp
        intro hlt
        exact hn (by simp [b, hlt])
      exact ⟨n - r, Nat.sub_add_cancel hnr⟩
    have hreindex : ∑' m, b (m + r) = ∑' n, b n :=
      hinj.tsum_eq (f := b) hsupp
    calc
      ∑' n, b n = ∑' m, b (m + r) := hreindex.symm
      _ = ∑' m, M.α ^ r * M.α ^ m := by
        apply tsum_congr
        intro m
        have hnot : ¬m + r < r := by omega
        simp [b, hnot, pow_add, mul_comm]
      _ = M.α ^ r * ∑' m, M.α ^ m := tsum_mul_left
      _ = M.α ^ r * (1 - M.α)⁻¹ := by
        rw [tsum_geometric_of_lt_one M.α_nonneg M.α_lt_one]
  calc
    neumannInfluenceToSet M root defects = ∑' n, f n := rfl
    _ ≤ ∑' n, b n :=
      Summable.tsum_le_tsum hfb hf_summable hb_summable
    _ = M.α ^ r * (1 - M.α)⁻¹ := hb_sum
    _ = M.α ^ r / (1 - M.α) := by rw [div_eq_mul_inv]

/-- A marked comparison certificate records the genuinely model-dependent
cancellation statement: the response is controlled by influence paths from a
finite root set to the finite set on which the two activities differ. -/
structure MarkedInfluenceCertificate (M : AbstractInfluenceMatrix P) where
  roots : Finset P
  defects : Finset P
  amplitude : ℝ
  response : ℝ
  amplitude_nonneg : 0 ≤ amplitude
  response_nonneg : 0 ≤ response
  response_le : response ≤ amplitude *
    ∑ root ∈ roots, neumannInfluenceToSet M root defects

namespace MarkedInfluenceCertificate

/-- Distance conversion for a marked comparison.  If every root--defect pair
is at distance at least `r`, and the influence matrix has range one for that
distance, the response decays as `α^r`. -/
theorem response_le_exponential
    (M : AbstractInfluenceMatrix P) (C : MarkedInfluenceCertificate M)
    (dist : P → P → ℕ)
    (h_refl : ∀ x, dist x x = 0)
    (h_triangle : ∀ x y z, dist x y ≤ dist x z + dist z y)
    (h_support : ∀ x y, dist x y > 1 → M.entry x y = 0)
    (r : ℕ)
    (hseparated : ∀ root ∈ C.roots, ∀ defect ∈ C.defects,
      r ≤ dist root defect) :
    C.response ≤ C.amplitude * (C.roots.card : ℝ) *
      (M.α ^ r / (1 - M.α)) := by
  have hrootBound : ∀ root ∈ C.roots,
      neumannInfluenceToSet M root C.defects ≤
        M.α ^ r / (1 - M.α) := by
    intro root hroot
    exact neumannInfluenceToSet_le_exponential M dist h_refl h_triangle
      h_support root C.defects r (fun defect hdefect =>
        hseparated root hroot defect hdefect)
  calc
    C.response ≤ C.amplitude *
        ∑ root ∈ C.roots, neumannInfluenceToSet M root C.defects :=
      C.response_le
    _ ≤ C.amplitude *
        ∑ _root ∈ C.roots, (M.α ^ r / (1 - M.α)) := by
      apply mul_le_mul_of_nonneg_left _ C.amplitude_nonneg
      apply Finset.sum_le_sum
      intro root hroot
      exact hrootBound root hroot
    _ = C.amplitude * (C.roots.card : ℝ) *
        (M.α ^ r / (1 - M.α)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

end MarkedInfluenceCertificate

end

end YangMills.Polymer
