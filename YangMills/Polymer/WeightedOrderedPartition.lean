/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Weighted exponential formula for ordered finite partitions

Mathlib's `OrderedFinpartition` is the labelled-set partition occurring in
the Faà di Bruno formula, but Mathlib does not currently expose its weighted
exponential-generating-function identity.  This file supplies the real,
nonnegative form needed for rooted polymer trees.

The proof is analytic but completely finite on the combinatorial side.  The
weight of an ordered partition is recognized by Faà di Bruno as a Taylor
coefficient of

`exp (sum_s b_s z^s / s!)`.

Complex Taylor convergence then sums those nonnegative real coefficients at
`z = 1`.  No polymer or Yang--Mills definitions occur in this file.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

/-- Product weight of all blocks of an ordered finite partition. -/
def orderedFinpartitionWeight (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition n, ∏ i : Fin c.length, b (c.partSize i)

/-- Block weights truncated above degree `N`. -/
def truncatedBlockWeight (b : ℕ → ℝ) (N s : ℕ) : ℝ :=
  if s ≤ N then b s else 0

theorem orderedFinpartitionWeight_truncatedBlockWeight_of_le
    (b : ℕ → ℝ) {N n : ℕ} (hn : n ≤ N) :
    orderedFinpartitionWeight (truncatedBlockWeight b N) n =
      orderedFinpartitionWeight b n := by
  classical
  unfold orderedFinpartitionWeight
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.prod_congr rfl
  intro i _
  simp [truncatedBlockWeight, (c.partSize_le i).trans hn]

/-- Truncated exponential generating polynomial associated to block weights.
The constant term is included; applications set it to zero. -/
def complexTruncatedExponentialPolynomial
    (b : ℕ → ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ s ∈ Finset.range (N + 1),
    ((b s / (s.factorial : ℝ) : ℝ) : ℂ) * z ^ s

theorem complexTruncatedExponentialPolynomial_zero
    (b : ℕ → ℝ) (N : ℕ) (hb0 : b 0 = 0) :
    complexTruncatedExponentialPolynomial b N 0 = 0 := by
  unfold complexTruncatedExponentialPolynomial
  rw [Finset.sum_eq_single 0]
  · simp [hb0]
  · intro s hs hs0
    simp [hs0]
  · simp

theorem complexTruncatedExponentialPolynomial_one
    (b : ℕ → ℝ) (N : ℕ) :
    complexTruncatedExponentialPolynomial b N 1 =
      ((∑ s ∈ Finset.range (N + 1),
        b s / (s.factorial : ℝ) : ℝ) : ℂ) := by
  simp [complexTruncatedExponentialPolynomial, Complex.ofReal_sum]

/-- Up to the truncation degree, the iterated derivatives at zero are the
prescribed block weights. -/
theorem iteratedDeriv_complexTruncatedExponentialPolynomial_zero
    (b : ℕ → ℝ) (N n : ℕ) (hn : n ≤ N) :
    iteratedDeriv n (complexTruncatedExponentialPolynomial b N) 0 =
      (b n : ℂ) := by
  classical
  unfold complexTruncatedExponentialPolynomial
  rw [iteratedDeriv_fun_sum]
  · rw [Finset.sum_eq_single n]
    · simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow,
        Nat.sub_self, pow_zero, mul_one]
      rw [Nat.descFactorial_self]
      have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
      norm_cast
      exact div_mul_cancel₀ (b n) hfac
    · intro s hs hsn
      simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
      by_cases hns : n < s
      · have hsub : s - n ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hns
        simp [hsub]
      · have hsnlt : s < n := lt_of_le_of_ne (Nat.le_of_not_gt hns) hsn
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr hsnlt]
        simp
    · simp [hn]
  · intro s hs
    fun_prop

/-- At every degree, the iterated derivative of the truncated polynomial is
the correspondingly truncated block weight. -/
theorem iteratedDeriv_complexTruncatedExponentialPolynomial_zero_eq_truncated
    (b : ℕ → ℝ) (N n : ℕ) :
    iteratedDeriv n (complexTruncatedExponentialPolynomial b N) 0 =
      (truncatedBlockWeight b N n : ℂ) := by
  classical
  by_cases hn : n ≤ N
  · rw [iteratedDeriv_complexTruncatedExponentialPolynomial_zero b N n hn]
    simp [truncatedBlockWeight, hn]
  · have hNn : N < n := Nat.lt_of_not_ge hn
    unfold complexTruncatedExponentialPolynomial
    rw [iteratedDeriv_fun_sum]
    · rw [show (truncatedBlockWeight b N n : ℂ) = 0 by
        simp [truncatedBlockWeight, hn]]
      apply Finset.sum_eq_zero
      intro s hs
      have hsN : s ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
      have hsn : s < n := hsN.trans_lt hNn
      simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hsn]
      simp
    · intro s hs
      fun_prop

theorem contDiff_complexTruncatedExponentialPolynomial
    (b : ℕ → ℝ) (N : ℕ) :
    ContDiff ℂ ⊤ (complexTruncatedExponentialPolynomial b N) := by
  unfold complexTruncatedExponentialPolynomial
  fun_prop

@[simp]
theorem iteratedDeriv_complex_exp (n : ℕ) (z : ℂ) :
    iteratedDeriv n Complex.exp z = Complex.exp z := by
  have h := congrFun (iteratedDeriv_cexp_const_mul n 1) z
  simpa using h

/-- Faà di Bruno identifies the Taylor derivative of the exponential of the
truncated EGF with the weighted ordered-partition sum. -/
theorem iteratedDeriv_exp_complexTruncatedExponentialPolynomial_zero
    (b : ℕ → ℝ) (N n : ℕ) (hb0 : b 0 = 0) :
    iteratedDeriv n
        (fun z : ℂ ↦ Complex.exp
          (complexTruncatedExponentialPolynomial b N z)) 0 =
      (orderedFinpartitionWeight (truncatedBlockWeight b N) n : ℂ) := by
  classical
  have hexp : ContDiffAt ℂ ⊤ Complex.exp
      (complexTruncatedExponentialPolynomial b N 0) :=
    Complex.contDiff_exp.contDiffAt
  have hpoly : ContDiffAt ℂ ⊤
      (complexTruncatedExponentialPolynomial b N) 0 :=
    (contDiff_complexTruncatedExponentialPolynomial b N).contDiffAt
  rw [show (fun z : ℂ ↦ Complex.exp
      (complexTruncatedExponentialPolynomial b N z)) =
        Complex.exp ∘ complexTruncatedExponentialPolynomial b N by rfl]
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hexp hpoly (by simp)]
  rw [complexTruncatedExponentialPolynomial_zero b N hb0]
  simp only [iteratedDeriv_complex_exp, Complex.exp_zero, one_mul]
  unfold orderedFinpartitionWeight
  push_cast
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.prod_congr rfl
  intro i _
  exact iteratedDeriv_complexTruncatedExponentialPolynomial_zero_eq_truncated
    b N (c.partSize i)

/-- The truncated exponential polynomial is entire. -/
theorem differentiable_complexTruncatedExponentialPolynomial
    (b : ℕ → ℝ) (N : ℕ) :
    Differentiable ℂ (complexTruncatedExponentialPolynomial b N) := by
  unfold complexTruncatedExponentialPolynomial
  fun_prop

/-- The complete weighted ordered-partition EGF for the truncated block
weights sums to the exponential of the truncated block EGF. -/
theorem hasSum_factorialNormalized_orderedFinpartitionWeight_truncated
    (b : ℕ → ℝ) (N : ℕ) (hb0 : b 0 = 0) :
    HasSum
      (fun n : ℕ ↦
        orderedFinpartitionWeight (truncatedBlockWeight b N) n /
          (n.factorial : ℝ))
      (Real.exp (∑ s ∈ Finset.range (N + 1),
        b s / (s.factorial : ℝ))) := by
  have hentire : Differentiable ℂ
      (fun z : ℂ ↦ Complex.exp
        (complexTruncatedExponentialPolynomial b N z)) := by
    exact Complex.differentiable_exp.comp
      (differentiable_complexTruncatedExponentialPolynomial b N)
  have htaylor := Complex.hasSum_taylorSeries_of_entire hentire 0 1
  have htaylor' :
      HasSum
        (fun n : ℕ ↦
          ((orderedFinpartitionWeight (truncatedBlockWeight b N) n /
            (n.factorial : ℝ) : ℝ) : ℂ))
        (Complex.exp
          (complexTruncatedExponentialPolynomial b N 1)) := by
    refine HasSum.congr_fun htaylor (fun n ↦ ?_)
    rw [iteratedDeriv_exp_complexTruncatedExponentialPolynomial_zero
      b N n hb0]
    norm_cast
    simp [div_eq_mul_inv]
    ring
  rw [complexTruncatedExponentialPolynomial_one,
    ← Complex.ofReal_exp] at htaylor'
  exact_mod_cast htaylor'

theorem orderedFinpartitionWeight_nonneg
    (b : ℕ → ℝ) (hb : ∀ s, 0 ≤ b s) (n : ℕ) :
    0 ≤ orderedFinpartitionWeight b n := by
  classical
  unfold orderedFinpartitionWeight
  exact Finset.sum_nonneg fun c _ ↦
    Finset.prod_nonneg fun i _ ↦ hb (c.partSize i)

/-- Finite weighted labelled-set exponential formula.  Only block sizes at
most `N` can occur on the left, so truncating the block weights does not
change it. -/
theorem sum_factorialNormalized_orderedFinpartitionWeight_le_exp
    (b : ℕ → ℝ) (N : ℕ) (hb0 : b 0 = 0)
    (hb : ∀ s, 0 ≤ b s) :
    (∑ n ∈ Finset.range (N + 1),
      orderedFinpartitionWeight b n / (n.factorial : ℝ)) ≤
      Real.exp (∑ s ∈ Finset.range (N + 1),
        b s / (s.factorial : ℝ)) := by
  let bt := truncatedBlockWeight b N
  have hbt : ∀ s, 0 ≤ bt s := by
    intro s
    simp only [bt, truncatedBlockWeight]
    split_ifs
    · exact hb s
    · exact le_rfl
  have hsum :=
    hasSum_factorialNormalized_orderedFinpartitionWeight_truncated
      b N hb0
  calc
    (∑ n ∈ Finset.range (N + 1),
        orderedFinpartitionWeight b n / (n.factorial : ℝ)) =
      ∑ n ∈ Finset.range (N + 1),
        orderedFinpartitionWeight bt n / (n.factorial : ℝ) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [orderedFinpartitionWeight_truncatedBlockWeight_of_le b
            (Nat.le_of_lt_succ (Finset.mem_range.mp hn))]
    _ ≤ ∑' n : ℕ,
        orderedFinpartitionWeight bt n / (n.factorial : ℝ) :=
      hsum.summable.sum_le_tsum _ (fun n _ ↦
        div_nonneg (orderedFinpartitionWeight_nonneg bt hbt n)
          (Nat.cast_nonneg _))
    _ = Real.exp (∑ s ∈ Finset.range (N + 1),
        b s / (s.factorial : ℝ)) := hsum.tsum_eq

end

end YangMills.Polymer
