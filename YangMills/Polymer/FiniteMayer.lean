/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.Dobrushin
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Data.Finset.Dedup

/-!
# The finite-volume Mayer logarithm

For a finite hard-core gas, successively insert the polymers in a duplicate-
free list.  The deletion identity writes every insertion ratio as `1 + u`,
where `u` is the pinned compatible-partition ratio.  The explicit
Dobrushin--KP certificate gives `‖u‖ < 1`, so the ordinary Mayer series for
`log (1 + u)` converges absolutely.  Summing these local series gives a
normalized logarithm whose exponential is exactly the finite partition
function.  The argument is stated for an arbitrary finite hard-core gas.

The value is a logarithm branch normalized at zero activity; it is not
silently identified with the global principal `Complex.log`, in accordance
with the roadmap's convention.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

namespace FinitePolymerModel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The pinned perturbation appearing when `γ` is inserted after the
polymers in `T`. -/
def mayerInsertion (M : FinitePolymerModel P) (γ : P) (T : Finset P) : ℂ :=
  M.activity γ *
    (M.partitionOn (M.compatibleWith T γ) / M.partitionOn T)

/-- The `n`th term of the local Mayer series `log (1 + u)`.  Its zeroth term
is zero because division by the natural number zero is zero in `ℂ`. -/
def mayerInsertionTerm (M : FinitePolymerModel P)
    (γ : P) (T : Finset P) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ (n + 1) * (M.mayerInsertion γ T) ^ n / n

/-- Local, pinned Mayer logarithm for one polymer insertion. -/
def mayerInsertionLog (M : FinitePolymerModel P) (γ : P) (T : Finset P) : ℂ :=
  ∑' n : ℕ, M.mayerInsertionTerm γ T n

/-- Deletion-ordered finite-volume Mayer sum.  Although the polymer list is
finite, every insertion logarithm contains the usual repeated-polymer Mayer
series. -/
def deletionMayerSum (M : FinitePolymerModel P) : List P → ℂ
  | [] => 0
  | γ :: l => M.mayerInsertionLog γ l.toFinset + M.deletionMayerSum l

/-- Canonical finite-volume Mayer sum, using `Finset.toList` only to choose a
deletion order. -/
def finiteMayerSum (M : FinitePolymerModel P) (S : Finset P) : ℂ :=
  M.deletionMayerSum S.toList

@[simp]
theorem deletionMayerSum_nil (M : FinitePolymerModel P) :
    M.deletionMayerSum [] = 0 := rfl

@[simp]
theorem deletionMayerSum_cons (M : FinitePolymerModel P) (γ : P) (l : List P) :
    M.deletionMayerSum (γ :: l) =
      M.mayerInsertionLog γ l.toFinset + M.deletionMayerSum l := rfl

/-- The explicit certificate bounds a pinned Mayer variable by its local
Dobrushin budget. -/
theorem norm_mayerInsertion_le_one_sub_exp_of_dobrushin
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hD : M.DobrushinCertificate S a) (T : Finset P) (hTS : T ⊆ S)
    {γ : P} (hγT : γ ∉ T) (hγS : γ ∈ S) :
    ‖M.mayerInsertion γ T‖ ≤ 1 - Real.exp (-a γ) := by
  have hsub : insert γ T ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hγS
    · exact hTS hx
  have hpinned := M.norm_pinnedPartitionRatio_le_of_dobrushin
    S a hD (insert γ T) hsub (Finset.mem_insert_self γ T)
  have herase : (insert γ T).erase γ = T := Finset.erase_insert hγT
  rw [herase] at hpinned
  change ‖M.mayerInsertion γ T‖ ≤ 1 - Real.exp (-a γ)
  exact hpinned

/-- The explicit certificate places every pinned Mayer variable strictly
inside the unit disk. -/
theorem norm_mayerInsertion_lt_one_of_dobrushin
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hD : M.DobrushinCertificate S a) (T : Finset P) (hTS : T ⊆ S)
    {γ : P} (hγT : γ ∉ T) (hγS : γ ∈ S) :
    ‖M.mayerInsertion γ T‖ < 1 := by
  exact (M.norm_mayerInsertion_le_one_sub_exp_of_dobrushin
    S a hD T hTS hγT hγS).trans_lt
      (by linarith [Real.exp_pos (-a γ)])

/-- The norm series of one pinned Mayer logarithm converges to the scalar
majorant `-log (1 - ‖u‖)`.  This records absolute convergence, not merely
convergence of the alternating complex logarithm. -/
theorem hasSum_norm_mayerInsertionTerm_of_dobrushin
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hD : M.DobrushinCertificate S a) (T : Finset P) (hTS : T ⊆ S)
    {γ : P} (hγT : γ ∉ T) (hγS : γ ∈ S) :
    HasSum (fun n : ℕ => ‖M.mayerInsertionTerm γ T n‖)
      (-Real.log (1 - ‖M.mayerInsertion γ T‖)) := by
  let q : ℝ := ‖M.mayerInsertion γ T‖
  have hq : q < 1 :=
    M.norm_mayerInsertion_lt_one_of_dobrushin S a hD T hTS hγT hγS
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one
    (show |q| < 1 by simpa [q, abs_of_nonneg (norm_nonneg _)] using hq)
  rw [← hasSum_nat_add_iff' 1]
  have htail : HasSum
      (fun n : ℕ => ‖M.mayerInsertionTerm γ T (n + 1)‖)
      (-Real.log (1 - q)) := by
    convert hs using 1
    funext n
    simp only [mayerInsertionTerm, norm_div, norm_mul, norm_pow, norm_neg,
      norm_one, one_pow, one_mul, Complex.norm_natCast]
    norm_num
    rfl
  simpa [mayerInsertionTerm, q] using htail

/-- Absolute summability of every pinned Mayer logarithm under the explicit
Dobrushin--KP certificate. -/
theorem summable_norm_mayerInsertionTerm_of_dobrushin
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hD : M.DobrushinCertificate S a) (T : Finset P) (hTS : T ⊆ S)
    {γ : P} (hγT : γ ∉ T) (hγS : γ ∈ S) :
    Summable (fun n : ℕ => ‖M.mayerInsertionTerm γ T n‖) :=
  (M.hasSum_norm_mayerInsertionTerm_of_dobrushin
    S a hD T hTS hγT hγS).summable

/-- The full absolute pinned Mayer series fits in the local weight `a γ`.
This is the quantitative rooted estimate furnished by the existing explicit
certificate. -/
theorem tsum_norm_mayerInsertionTerm_le_of_dobrushin
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hD : M.DobrushinCertificate S a) (T : Finset P) (hTS : T ⊆ S)
    {γ : P} (hγT : γ ∉ T) (hγS : γ ∈ S) :
    ∑' n : ℕ, ‖M.mayerInsertionTerm γ T n‖ ≤ a γ := by
  have hsum := M.hasSum_norm_mayerInsertionTerm_of_dobrushin
    S a hD T hTS hγT hγS
  rw [hsum.tsum_eq]
  have hbudget := M.norm_mayerInsertion_le_one_sub_exp_of_dobrushin
    S a hD T hTS hγT hγS
  have hq := M.norm_mayerInsertion_lt_one_of_dobrushin
    S a hD T hTS hγT hγS
  have hpositive : 0 < 1 - ‖M.mayerInsertion γ T‖ := sub_pos.mpr hq
  have hexp : Real.exp (-a γ) ≤ 1 - ‖M.mayerInsertion γ T‖ := by
    linarith
  have hlog := Real.strictMonoOn_log.monotoneOn
    (Real.exp_pos (-a γ)) hpositive hexp
  rw [Real.log_exp] at hlog
  linarith

/-- The local Mayer series is exactly the analytic logarithm of its insertion
ratio. -/
theorem mayerInsertionLog_eq_log_of_dobrushin
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hD : M.DobrushinCertificate S a) (T : Finset P) (hTS : T ⊆ S)
    {γ : P} (hγT : γ ∉ T) (hγS : γ ∈ S) :
    M.mayerInsertionLog γ T = Complex.log (1 + M.mayerInsertion γ T) := by
  unfold mayerInsertionLog mayerInsertionTerm
  exact (Complex.hasSum_taylorSeries_log
    (M.norm_mayerInsertion_lt_one_of_dobrushin S a hD T hTS hγT hγS)).tsum_eq

/-- Exact insertion ratio furnished by the polymer deletion identity. -/
theorem one_add_mayerInsertion_eq_partition_ratio
    (M : FinitePolymerModel P) (T : Finset P) {γ : P} (hγT : γ ∉ T)
    (hTzero : M.partitionOn T ≠ 0) :
    1 + M.mayerInsertion γ T =
      M.partitionOn (insert γ T) / M.partitionOn T := by
  rw [mayerInsertion, M.partitionOn_delete (insert γ T)
    (Finset.mem_insert_self γ T), Finset.erase_insert hγT]
  field_simp

/-- The deletion-ordered Mayer sum exponentiates to the exact restricted
partition function.  This is the finite Mayer/log-partition identity for the
normalized logarithm branch. -/
theorem exp_deletionMayerSum_eq_partitionOn_of_dobrushin
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hD : M.DobrushinCertificate S a) (l : List P)
    (hl : l.Nodup) (hlS : l.toFinset ⊆ S) :
    Complex.exp (M.deletionMayerSum l) = M.partitionOn l.toFinset := by
  induction l with
  | nil => simp
  | cons γ l ih =>
      have hγl : γ ∉ l := (List.nodup_cons.mp hl).1
      have hlnodup : l.Nodup := (List.nodup_cons.mp hl).2
      have hγT : γ ∉ l.toFinset := by simpa using hγl
      have hlsub : l.toFinset ⊆ S := by
        exact (Finset.subset_insert γ l.toFinset).trans (by simpa using hlS)
      have hγS : γ ∈ S := hlS (by simp)
      have hTzero := M.partitionOn_ne_zero_of_dobrushin S a hD l.toFinset hlsub
      have hlocal := M.mayerInsertionLog_eq_log_of_dobrushin
        S a hD l.toFinset hlsub hγT hγS
      have hratio := M.one_add_mayerInsertion_eq_partition_ratio
        l.toFinset hγT hTzero
      have hratiozero : 1 + M.mayerInsertion γ l.toFinset ≠ 0 := by
        rw [hratio]
        exact div_ne_zero
          (M.partitionOn_ne_zero_of_dobrushin S a hD (insert γ l.toFinset)
            (by simpa using hlS)) hTzero
      rw [deletionMayerSum_cons, Complex.exp_add, hlocal,
        Complex.exp_log hratiozero, ih hlnodup hlsub, hratio]
      rw [div_mul_cancel₀ _ hTzero]
      simp

/-- Canonical finite-volume specialization. -/
theorem exp_finiteMayerSum_eq_partitionOn_of_dobrushin
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hD : M.DobrushinCertificate S a) :
    Complex.exp (M.finiteMayerSum S) = M.partitionOn S := by
  unfold finiteMayerSum
  simpa [Finset.toList_toFinset] using
    M.exp_deletionMayerSum_eq_partitionOn_of_dobrushin S a hD S.toList
      (Finset.nodup_toList S) (by simp)

/-- Full-partition finite Mayer/log identity. -/
theorem exp_finiteMayerSum_eq_partitionFunction_of_dobrushin
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hD : M.DobrushinCertificate Finset.univ a) :
    Complex.exp (M.finiteMayerSum Finset.univ) = M.partitionFunction := by
  simpa [partitionFunction] using
    M.exp_finiteMayerSum_eq_partitionOn_of_dobrushin Finset.univ a hD

end FinitePolymerModel

end

end YangMills.Polymer
