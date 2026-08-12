/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.OrderedFinpartitionEquiv

/-!
# The partition-lattice Möbius cancellation on labelled finite sets

For a block of size `s > 0`, the partition-lattice Möbius weight is
`(-1)^(s-1) (s-1)!`.  The product of these weights over all blocks sums to
zero on a labelled set of size at least two.  We prove the identity directly
from Mathlib's `OrderedFinpartition.extendEquiv`: adding the new label either
creates a singleton or enlarges one old block, and the two contributions
cancel after summing the old block sizes.

This is precisely the finite cancellation needed to pass between graph
moments and connected graph cumulants.  It is independent of polymers and
Yang--Mills.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

/-- Möbius weight of one nonempty partition block. -/
def partitionMobiusBlockWeight (s : ℕ) : ℤ :=
  (-1 : ℤ) ^ (s - 1) * (s - 1).factorial

@[simp]
theorem partitionMobiusBlockWeight_one :
    partitionMobiusBlockWeight 1 = 1 := by
  simp [partitionMobiusBlockWeight]

theorem partitionMobiusBlockWeight_succ {s : ℕ} (hs : 0 < s) :
    partitionMobiusBlockWeight (s + 1) =
      -(s : ℤ) * partitionMobiusBlockWeight s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  simp only [partitionMobiusBlockWeight, Nat.succ_sub_one,
    Nat.factorial_succ]
  push_cast
  rw [pow_succ]
  ring

/-- Product Möbius weight of an ordered finite partition. -/
def orderedFinpartitionMobiusWeight {n : ℕ}
    (c : OrderedFinpartition n) : ℤ :=
  ∏ i : Fin c.length, partitionMobiusBlockWeight (c.partSize i)

theorem sum_orderedFinpartition_partSize {n : ℕ}
    (c : OrderedFinpartition n) :
    ∑ i : Fin c.length, c.partSize i = n := by
  have hcard := Fintype.card_congr c.equivSigma
  simpa using hcard

@[simp]
theorem orderedFinpartitionMobiusWeight_extendLeft {n : ℕ}
    (c : OrderedFinpartition n) :
    orderedFinpartitionMobiusWeight c.extendLeft =
      orderedFinpartitionMobiusWeight c := by
  unfold orderedFinpartitionMobiusWeight
  change (∏ i : Fin (c.length + 1),
      partitionMobiusBlockWeight
        (Fin.cons (α := fun _ ↦ ℕ) 1 c.partSize i)) = _
  rw [show (fun i : Fin (c.length + 1) ↦
        partitionMobiusBlockWeight
          (Fin.cons (α := fun _ ↦ ℕ) 1 c.partSize i)) =
      Fin.cons (partitionMobiusBlockWeight 1)
        (fun i ↦ partitionMobiusBlockWeight (c.partSize i)) by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp]
  rw [Fin.prod_cons, partitionMobiusBlockWeight_one, one_mul]

theorem orderedFinpartitionMobiusWeight_extendMiddle {n : ℕ}
    (c : OrderedFinpartition n) (i : Fin c.length) :
    orderedFinpartitionMobiusWeight (c.extendMiddle i) =
      -(c.partSize i : ℤ) * orderedFinpartitionMobiusWeight c := by
  classical
  unfold orderedFinpartitionMobiusWeight
  change (∏ j : Fin c.length,
      partitionMobiusBlockWeight
        (Function.update c.partSize i (c.partSize i + 1) j)) = _
  have hfun : (fun j : Fin c.length ↦
        partitionMobiusBlockWeight
          (Function.update c.partSize i (c.partSize i + 1) j)) =
      Function.update (fun j ↦ partitionMobiusBlockWeight (c.partSize j)) i
        (partitionMobiusBlockWeight (c.partSize i + 1)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hfun]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [partitionMobiusBlockWeight_succ (c.partSize_pos i)]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin c.length))
    (fun j ↦ partitionMobiusBlockWeight (c.partSize j))
    (Finset.mem_univ i)]
  ring

/-- Adding one labelled point multiplies the total partition Möbius weight
by `1 - n`. -/
theorem sum_orderedFinpartitionMobiusWeight_succ (n : ℕ) :
    (∑ c : OrderedFinpartition (n + 1),
        orderedFinpartitionMobiusWeight c) =
      (1 - (n : ℤ)) *
        ∑ c : OrderedFinpartition n, orderedFinpartitionMobiusWeight c := by
  rw [← (OrderedFinpartition.extendEquiv n).sum_comp]
  rw [Fintype.sum_sigma]
  simp only [OrderedFinpartition.extendEquiv_apply, Fintype.sum_option,
    OrderedFinpartition.extend_none, OrderedFinpartition.extend_some,
    orderedFinpartitionMobiusWeight_extendLeft,
    orderedFinpartitionMobiusWeight_extendMiddle]
  calc
    (∑ c : OrderedFinpartition n,
        (orderedFinpartitionMobiusWeight c +
          ∑ i : Fin c.length,
            -(c.partSize i : ℤ) * orderedFinpartitionMobiusWeight c)) =
        ∑ c : OrderedFinpartition n,
          (1 - (n : ℤ)) * orderedFinpartitionMobiusWeight c := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.sum_mul]
      have hsize := sum_orderedFinpartition_partSize c
      have hsizeZ : ∑ i : Fin c.length, (c.partSize i : ℤ) = (n : ℤ) := by
        exact_mod_cast hsize
      rw [Finset.sum_neg_distrib, hsizeZ]
      ring
    _ = (1 - (n : ℤ)) *
        ∑ c : OrderedFinpartition n,
          orderedFinpartitionMobiusWeight c := by
      rw [Finset.mul_sum]

/-- Exact partition-lattice Möbius cancellation. -/
theorem sum_orderedFinpartitionMobiusWeight (n : ℕ) :
    (∑ c : OrderedFinpartition n, orderedFinpartitionMobiusWeight c) =
      if n = 0 ∨ n = 1 then 1 else 0 := by
  cases n with
  | zero => simp [orderedFinpartitionMobiusWeight]
  | succ n =>
      cases n with
      | zero => simp [orderedFinpartitionMobiusWeight]
      | succ n =>
          have hz : ∀ m : ℕ,
              (∑ c : OrderedFinpartition (m + 2),
                orderedFinpartitionMobiusWeight c) = 0 := by
            intro m
            induction m with
            | zero =>
                rw [show 0 + 2 = 1 + 1 by omega,
                  sum_orderedFinpartitionMobiusWeight_succ 1]
                norm_num
            | succ m ih =>
                rw [show (m + 1) + 2 = (m + 2) + 1 by omega,
                  sum_orderedFinpartitionMobiusWeight_succ (m + 2), ih,
                  mul_zero]
          rw [if_neg (by omega)]
          simpa [Nat.succ_eq_add_one] using hz n

/-- Möbius coefficient of the interval from an ordered partition to the
indiscrete partition.  It depends only on the number of blocks. -/
def orderedFinpartitionTopMobiusWeight {n : ℕ}
    (c : OrderedFinpartition n) : ℤ :=
  partitionMobiusBlockWeight c.length

theorem orderedFinpartitionTopMobiusWeight_extendLeft {n : ℕ}
    (c : OrderedFinpartition n) (hc : 0 < c.length) :
    orderedFinpartitionTopMobiusWeight c.extendLeft =
      -(c.length : ℤ) * orderedFinpartitionTopMobiusWeight c := by
  simpa [orderedFinpartitionTopMobiusWeight] using
    partitionMobiusBlockWeight_succ hc

@[simp]
theorem orderedFinpartitionTopMobiusWeight_extendMiddle {n : ℕ}
    (c : OrderedFinpartition n) (i : Fin c.length) :
    orderedFinpartitionTopMobiusWeight (c.extendMiddle i) =
      orderedFinpartitionTopMobiusWeight c := by
  simp [orderedFinpartitionTopMobiusWeight]

/-- Once the labelled set is nonempty, adding one new label makes the total
top-interval Möbius coefficient vanish: the new singleton contribution
cancels the choices of an existing block. -/
theorem sum_orderedFinpartitionTopMobiusWeight_succ_eq_zero
    (n : ℕ) (hn : 0 < n) :
    (∑ c : OrderedFinpartition (n + 1),
      orderedFinpartitionTopMobiusWeight c) = 0 := by
  rw [← (OrderedFinpartition.extendEquiv n).sum_comp]
  rw [Fintype.sum_sigma]
  simp only [OrderedFinpartition.extendEquiv_apply, Fintype.sum_option,
    OrderedFinpartition.extend_none, OrderedFinpartition.extend_some]
  apply Finset.sum_eq_zero
  intro c _hc
  rw [orderedFinpartitionTopMobiusWeight_extendLeft c (c.length_pos hn)]
  simp only [orderedFinpartitionTopMobiusWeight_extendMiddle]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

/-- Exact cancellation of the Möbius coefficients from all partitions of a
labelled set to the indiscrete partition. -/
theorem sum_orderedFinpartitionTopMobiusWeight (n : ℕ) :
    (∑ c : OrderedFinpartition n,
      orderedFinpartitionTopMobiusWeight c) =
      if n = 0 ∨ n = 1 then 1 else 0 := by
  cases n with
  | zero => simp [orderedFinpartitionTopMobiusWeight,
      partitionMobiusBlockWeight]
  | succ n =>
      cases n with
      | zero => simp [orderedFinpartitionTopMobiusWeight,
          partitionMobiusBlockWeight]
      | succ n =>
          rw [if_neg (by omega)]
          simpa [Nat.succ_eq_add_one] using
            sum_orderedFinpartitionTopMobiusWeight_succ_eq_zero
              (n + 1) (by omega)

end

end YangMills.Polymer
