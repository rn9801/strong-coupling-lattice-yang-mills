/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.FiniteMayer
import YangMills.Polymer.LabelledMayerExponential
import YangMills.Polymer.LabelledRootedForestSpecies
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Analytic evaluation of the finite Mayer logarithm

The labelled exponential formula is formal, whereas the KP theorem produces
an honestly absolutely convergent symmetric Mayer series.  This file bridges
the two statements without evaluating a formal power series at the boundary
point `1`.  We evaluate the connected coefficients at `|z| < 1`, use their
formal logarithmic differential equation, and pass to `z = 1` by absolute
convergence.
-/

namespace YangMills.Polymer

open Filter
open scoped BigOperators

noncomputable section

namespace FinitePolymerModel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- On the full finite species the restricted coefficient is the ordinary
symmetric Mayer degree sum. -/
theorem restrictedSymmetricMayerCoefficient_univ
    (M : FinitePolymerModel P) (n : ℕ) :
    M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1) =
      M.symmetricMayerDegreeSum (n + 1) := by
  simp [restrictedSymmetricMayerCoefficient, symmetricMayerDegreeSum]

/-- KP summability of the symmetric connected coefficients. -/
theorem summable_norm_restrictedSymmetricMayerCoefficient_univ_of_koteckyPreiss
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    Summable (fun n : ℕ ↦
      ‖M.restrictedSymmetricMayerCoefficient Finset.univ n‖) := by
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (M.summable_normMayerDegreeSum_succ_of_koteckyPreiss_certified a hKP)
  simpa [M.restrictedSymmetricMayerCoefficient_univ] using
    M.norm_symmetricMayerDegreeSum_le (n + 1)

/-- KP summability of the differentiated symmetric connected series. -/
theorem summable_norm_derivative_restrictedSymmetricMayerCoefficient_univ_of_koteckyPreiss
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    Summable (fun n : ℕ ↦
      ‖((n + 1 : ℕ) : ℂ) *
        M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1)‖) := by
  have h :=
    M.summable_succ_mul_normMayerDegreeSum_succ_of_koteckyPreiss_certified
      a hKP
  apply Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_) h
  rw [norm_mul, Complex.norm_natCast,
    M.restrictedSymmetricMayerCoefficient_univ]
  exact mul_le_mul_of_nonneg_left
    (M.norm_symmetricMayerDegreeSum_le (n + 1)) (Nat.cast_nonneg _)

/-- Honest analytic function represented by the convergent connected Mayer
coefficients on the closed unit disk. -/
def connectedGeneratingFunction (M : FinitePolymerModel P) (z : ℂ) : ℂ :=
  ∑' n : ℕ,
    M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1) * z ^ (n + 1)

/-- The connected series is normalized to vanish at zero activity. -/
@[simp]
theorem connectedGeneratingFunction_zero (M : FinitePolymerModel P) :
    M.connectedGeneratingFunction 0 = 0 := by
  unfold connectedGeneratingFunction
  simp

/-- Absolute convergence of the connected function on the closed unit disk. -/
theorem summable_connectedGeneratingFunction
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun n : ℕ ↦
      M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1) *
        z ^ (n + 1)) := by
  have hshift : Summable (fun n : ℕ ↦
      ‖M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1)‖) :=
    (M.summable_norm_restrictedSymmetricMayerCoefficient_univ_of_koteckyPreiss
      a hKP).comp_injective (i := fun n : ℕ ↦ n + 1)
        (by intro n m h; exact Nat.add_right_cancel h)
  apply Summable.of_norm_bounded hshift
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) hz)

/-- The connected function is continuous up to `|z| = 1`; this is the Abel
boundary input used to evaluate at unit activity. -/
theorem continuousOn_connectedGeneratingFunction_closedBall
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    ContinuousOn M.connectedGeneratingFunction (Metric.closedBall 0 1) := by
  unfold connectedGeneratingFunction
  apply continuousOn_tsum
  · intro n
    fun_prop
  · exact
      (M.summable_norm_restrictedSymmetricMayerCoefficient_univ_of_koteckyPreiss
        a hKP).comp_injective (i := fun n : ℕ ↦ n + 1)
          (by intro n m h; exact Nat.add_right_cancel h)
  · intro n z hz
    rw [norm_mul, norm_pow]
    have hz1 : ‖z‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact mul_le_of_le_one_right
      (norm_nonneg
        (M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1)))
      (pow_le_one₀ (norm_nonneg z) hz1)

/-- Termwise differentiated connected Mayer series on the open unit disk. -/
theorem hasDerivAt_connectedGeneratingFunction
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    HasDerivAt M.connectedGeneratingFunction
      (∑' n : ℕ, M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1) *
        ((n + 1 : ℕ) : ℂ) * z ^ n) z := by
  unfold connectedGeneratingFunction
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun n y ↦
      M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1) *
        y ^ (n + 1))
    (g' := fun n y ↦
      M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1) *
        ((n + 1 : ℕ) : ℂ) * y ^ n)
    (u := fun n : ℕ ↦
      ‖((n + 1 : ℕ) : ℂ) *
        M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1)‖)
    (t := Metric.ball (0 : ℂ) 1) (y₀ := 0)
  · exact M.summable_norm_derivative_restrictedSymmetricMayerCoefficient_univ_of_koteckyPreiss
      a hKP
  · exact Metric.isOpen_ball
  · exact (convex_ball (0 : ℂ) 1).isPreconnected
  · intro n y _
    simpa [Nat.add_sub_cancel, mul_assoc] using
      ((hasDerivAt_pow (n + 1) y).const_mul
        (M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1)))
  · intro n y hy
    rw [norm_mul, norm_mul, norm_pow]
    have hy1 : ‖y‖ ≤ 1 := by
      exact (by simpa only [Metric.mem_ball, dist_zero_right] using hy : ‖y‖ < 1).le
    calc
      ‖M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1)‖ *
          ‖((n + 1 : ℕ) : ℂ)‖ * ‖y‖ ^ n =
          (‖((n + 1 : ℕ) : ℂ)‖ *
            ‖M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1)‖) *
              ‖y‖ ^ n := by ring
      _ ≤ ‖((n + 1 : ℕ) : ℂ)‖ *
          ‖M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1)‖ :=
        mul_le_of_le_one_right
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (pow_le_one₀ (norm_nonneg _) hy1)
      _ = ‖((n + 1 : ℕ) : ℂ) *
          M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1)‖ := by
        rw [norm_mul]
  · simp
  · simp
  · exact hz

/-- The finite partition polynomial is the evaluation of its formal
coefficient sequence. -/
theorem partitionGeneratingPolynomial_eq_sum_range
    (M : FinitePolymerModel P) (z : ℂ) :
    M.partitionGeneratingPolynomial Finset.univ z =
      ∑ n ∈ Finset.range ((Finset.univ : Finset P).card + 1),
        M.partitionDegreeCoefficient Finset.univ n * z ^ n := rfl

/-- Outside the finite partition-polynomial degree range its coefficient
sequence vanishes. -/
theorem partitionDegreeCoefficient_univ_eq_zero_outside
    (M : FinitePolymerModel P) {n : ℕ}
    (hn : n ∉ Finset.range ((Finset.univ : Finset P).card + 1)) :
    M.partitionDegreeCoefficient Finset.univ n = 0 := by
  apply M.partitionDegreeCoefficient_eq_zero_of_card_lt Finset.univ
  simpa [Finset.mem_range, not_lt] using hn

/-- The partition generating polynomial is the total sum of its coefficient
sequence at every scalar argument. -/
theorem partitionGeneratingPolynomial_eq_tsum
    (M : FinitePolymerModel P) (z : ℂ) :
    M.partitionGeneratingPolynomial Finset.univ z =
      ∑' n : ℕ, M.partitionDegreeCoefficient Finset.univ n * z ^ n := by
  rw [M.partitionGeneratingPolynomial_eq_sum_range]
  symm
  apply tsum_eq_sum
  intro n hn
  rw [M.partitionDegreeCoefficient_univ_eq_zero_outside hn, zero_mul]

/-- The formal logarithmic differential equation evaluates on the open unit
disk.  The finite first factor makes this a direct Cauchy-product
calculation, while KP provides absolute convergence of the differentiated
connected factor. -/
theorem partitionGeneratingPolynomial_mul_connectedDerivative
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    M.partitionGeneratingPolynomial Finset.univ z *
        (∑' n : ℕ,
          M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1) *
            ((n + 1 : ℕ) : ℂ) * z ^ n) =
      ∑' n : ℕ,
        M.partitionDegreeCoefficient Finset.univ (n + 1) *
          ((n + 1 : ℕ) : ℂ) * z ^ n := by
  let b : ℕ → ℂ := fun n ↦ M.partitionDegreeCoefficient Finset.univ n
  let c : ℕ → ℂ := fun n ↦
    M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1) *
      ((n + 1 : ℕ) : ℂ)
  have hb : Summable (fun n : ℕ ↦ ‖b n * z ^ n‖) := by
    apply summable_of_hasFiniteSupport
    refine (Finset.finite_toSet
      (Finset.range ((Finset.univ : Finset P).card + 1))).subset ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    by_contra hnr
    have hbzero : b n = 0 := by
      unfold b
      exact M.partitionDegreeCoefficient_univ_eq_zero_outside hnr
    simp [hbzero] at hn
  have hc : Summable (fun n : ℕ ↦ ‖c n * z ^ n‖) := by
    have hc0 :=
      M.summable_norm_derivative_restrictedSymmetricMayerCoefficient_univ_of_koteckyPreiss
        a hKP
    apply Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hc0
    rw [norm_mul, norm_pow]
    have hz1 : ‖z‖ ≤ 1 :=
      (by simpa only [Metric.mem_ball, dist_zero_right] using hz : ‖z‖ < 1).le
    unfold c
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    push_cast
    calc
      ‖M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1)‖ *
          ((n : ℝ) + 1) * ‖z‖ ^ n ≤
          ‖M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1)‖ *
            ((n : ℝ) + 1) :=
        mul_le_of_le_one_right
          (mul_nonneg (norm_nonneg _) (by positivity))
          (pow_le_one₀ (norm_nonneg _) hz1)
      _ = ((n : ℝ) + 1) *
          ‖M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1)‖ := by ring
  rw [M.partitionGeneratingPolynomial_eq_tsum]
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hb hc]
  apply tsum_congr
  intro n
  have hformal := congrArg (PowerSeries.coeff n)
    (M.partitionPowerSeries_mul_derivative_restrictedSymmetricMayerPowerSeries
      Finset.univ)
  rw [PowerSeries.coeff_mul] at hformal
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ PowerSeries.coeff i (M.partitionPowerSeries Finset.univ) *
      PowerSeries.coeff j
        (PowerSeries.derivative ℂ
          (M.restrictedSymmetricMayerPowerSeries Finset.univ))) n] at hformal
  rw [PowerSeries.coeff_derivative] at hformal
  have hcoeff : ∑ k ∈ Finset.range (n + 1), b k * c (n - k) =
      M.partitionDegreeCoefficient Finset.univ (n + 1) *
        ((n + 1 : ℕ) : ℂ) := by
    simpa [b, c, PowerSeries.coeff_derivative,
      M.coeff_partitionPowerSeries,
      restrictedSymmetricMayerPowerSeries, PowerSeries.coeff_mk,
      M.labelledConnectedDegreeSum_div_factorial, mul_assoc,
      mul_left_comm, mul_comm] using hformal
  calc
    ∑ k ∈ Finset.range (n + 1),
        b k * z ^ k * (c (n - k) * z ^ (n - k)) =
        (∑ k ∈ Finset.range (n + 1), b k * c (n - k)) * z ^ n := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      calc
        b k * z ^ k * (c (n - k) * z ^ (n - k)) =
            b k * c (n - k) * (z ^ k * z ^ (n - k)) := by ring
        _ = b k * c (n - k) * z ^ (k + (n - k)) := by rw [pow_add]
        _ = b k * c (n - k) * z ^ n := by rw [Nat.add_sub_of_le hkn]
    _ = M.partitionDegreeCoefficient Finset.univ (n + 1) *
        ((n + 1 : ℕ) : ℂ) * z ^ n := by rw [hcoeff]

/-- The differentiated finite partition polynomial in coefficient form. -/
theorem hasDerivAt_partitionGeneratingPolynomial
    (M : FinitePolymerModel P) (z : ℂ) :
    HasDerivAt (M.partitionGeneratingPolynomial Finset.univ)
      (∑' n : ℕ, M.partitionDegreeCoefficient Finset.univ (n + 1) *
        ((n + 1 : ℕ) : ℂ) * z ^ n) z := by
  unfold partitionGeneratingPolynomial
  have hfinite := HasDerivAt.fun_sum (u := Finset.range
      ((Finset.univ : Finset P).card + 1)) (fun n _ ↦
    (hasDerivAt_pow n z).const_mul
      (M.partitionDegreeCoefficient Finset.univ n))
  convert hfinite using 1
  have htsum : (∑' n : ℕ,
      M.partitionDegreeCoefficient Finset.univ (n + 1) *
        ((n + 1 : ℕ) : ℂ) * z ^ n) =
      ∑ n ∈ Finset.range (Finset.univ : Finset P).card,
        M.partitionDegreeCoefficient Finset.univ (n + 1) *
          ((n + 1 : ℕ) : ℂ) * z ^ n := by
    apply tsum_eq_sum
    intro n hn
    rw [M.partitionDegreeCoefficient_eq_zero_of_card_lt Finset.univ]
    · simp
    · exact Nat.lt_succ_iff.mpr (not_lt.mp (fun h ↦ hn (Finset.mem_range.mpr h)))
  rw [htsum, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Nat.add_sub_cancel]
  ring

/-- On the open unit disk the finite partition polynomial is the exponential
of the convergent symmetric connected series. -/
theorem exp_connectedGeneratingFunction_eq_partitionGeneratingPolynomial
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    Set.EqOn (fun z ↦ Complex.exp (M.connectedGeneratingFunction z))
      (M.partitionGeneratingPolynomial Finset.univ)
      (Metric.ball (0 : ℂ) 1) := by
  let U : Set ℂ := Metric.ball 0 1
  let Pfun : ℂ → ℂ := M.partitionGeneratingPolynomial Finset.univ
  let H : ℂ → ℂ := fun z ↦
    Complex.exp (-M.connectedGeneratingFunction z) * Pfun z
  have hH : ∀ z ∈ U, HasDerivAt H 0 z := by
    intro z hz
    let D : ℂ := ∑' n : ℕ,
      M.restrictedSymmetricMayerCoefficient Finset.univ (n + 1) *
        ((n + 1 : ℕ) : ℂ) * z ^ n
    have hC : HasDerivAt M.connectedGeneratingFunction D z :=
      M.hasDerivAt_connectedGeneratingFunction a hKP hz
    have hP : HasDerivAt Pfun (Pfun z * D) z := by
      have hp0 := M.hasDerivAt_partitionGeneratingPolynomial z
      rw [M.partitionGeneratingPolynomial_mul_connectedDerivative a hKP hz]
      exact hp0
    have hexp : HasDerivAt
        (fun w ↦ Complex.exp (-M.connectedGeneratingFunction w))
        (Complex.exp (-M.connectedGeneratingFunction z) * (-D)) z := by
      simpa using hC.neg.cexp
    have hprod := hexp.mul hP
    convert hprod using 1
    ring
  have hdiff : DifferentiableOn ℂ H U := fun z hz ↦
    (hH z hz).differentiableAt.differentiableWithinAt
  have hzero : U.EqOn (deriv H) 0 := fun z hz ↦ by
    rw [(hH z hz).deriv]
    rfl
  intro z hz
  have hconst := Metric.isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball (0 : ℂ) 1).isPreconnected hdiff hzero
    (show z ∈ U from hz) (show (0 : ℂ) ∈ U by simp [U])
  have hHz : H z = 1 := by
    simpa [H, Pfun] using hconst
  change Complex.exp (M.connectedGeneratingFunction z) = Pfun z
  calc
    Complex.exp (M.connectedGeneratingFunction z) =
        Complex.exp (M.connectedGeneratingFunction z) * 1 := by ring
    _ = Complex.exp (M.connectedGeneratingFunction z) *
        (Complex.exp (-M.connectedGeneratingFunction z) * Pfun z) := by
      change Complex.exp (M.connectedGeneratingFunction z) * 1 =
        Complex.exp (M.connectedGeneratingFunction z) * H z
      rw [hHz]
    _ = (Complex.exp (M.connectedGeneratingFunction z) *
        Complex.exp (-M.connectedGeneratingFunction z)) * Pfun z := by ring
    _ = Pfun z := by rw [← Complex.exp_add]; simp

/-- Abel evaluation at unit activity: the absolutely convergent symmetric
Mayer series exponentiates to the finite partition function. -/
theorem exp_connectedGeneratingFunction_one_eq_partitionFunction
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    Complex.exp (M.connectedGeneratingFunction 1) = M.partitionFunction := by
  let z : ℕ → ℂ := fun n ↦
    ((1 - 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hz : ∀ n, z n ∈ Metric.ball (0 : ℂ) 1 := by
    intro n
    simp only [Metric.mem_ball, dist_zero_right, z]
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hone : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn]
      exact_mod_cast Nat.le_add_left 1 n
    rw [abs_of_nonneg (sub_nonneg.mpr hone)]
    linarith [one_div_pos.mpr hn]
  have hpoint : ∀ n,
      Complex.exp (M.connectedGeneratingFunction (z n)) =
        M.partitionGeneratingPolynomial Finset.univ (z n) := fun n ↦
    M.exp_connectedGeneratingFunction_eq_partitionGeneratingPolynomial a hKP (hz n)
  have hzone : Tendsto z atTop (nhds (1 : ℂ)) := by
    have hreal : Tendsto (fun n : ℕ ↦
        (1 - 1 / ((n : ℝ) + 1) : ℝ)) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hzoneWithin : Tendsto z atTop
      (nhdsWithin (1 : ℂ) (Metric.closedBall 0 1)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hzone, Filter.Eventually.of_forall fun n ↦ ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (by simpa only [Metric.mem_ball, dist_zero_right] using hz n :
      ‖z n‖ < 1).le
  have hleft : Tendsto
      (fun n ↦ Complex.exp (M.connectedGeneratingFunction (z n))) atTop
      (nhds (Complex.exp (M.connectedGeneratingFunction 1))) := by
    have hcont : ContinuousWithinAt M.connectedGeneratingFunction
        (Metric.closedBall 0 1) 1 :=
      (M.continuousOn_connectedGeneratingFunction_closedBall a hKP)
        (1 : ℂ)
        (show (1 : ℂ) ∈ Metric.closedBall 0 1 by
          rw [Metric.mem_closedBall, dist_zero_right]
          norm_num)
    exact Complex.continuous_exp.continuousAt.tendsto.comp
      (hcont.tendsto.comp hzoneWithin)
  have hright : Tendsto
      (fun n ↦ M.partitionGeneratingPolynomial Finset.univ (z n)) atTop
      (nhds (M.partitionGeneratingPolynomial Finset.univ 1)) :=
    (M.contDiff_partitionGeneratingPolynomial Finset.univ).continuous.continuousAt.tendsto.comp
      hzone
  have heq := tendsto_nhds_unique hleft (hright.congr' <|
    Filter.Eventually.of_forall fun n ↦ (hpoint n).symm)
  calc
    Complex.exp (M.connectedGeneratingFunction 1) =
        M.partitionGeneratingPolynomial Finset.univ 1 := heq
    _ = M.partitionOn Finset.univ := by
      unfold partitionGeneratingPolynomial
      simpa using M.sum_partitionDegreeCoefficient_range Finset.univ
    _ = M.partitionFunction := rfl

set_option maxHeartbeats 400000 in
-- Elaborating the abstract `tsum` shift through the KP certificate is just
-- above the project default in object-code builds.
/-- The unit-activity connected generating function is the existing
symmetric Mayer sum. -/
theorem connectedGeneratingFunction_one_eq_symmetricMayerSum
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    M.connectedGeneratingFunction 1 = M.symmetricMayerSum := by
  unfold connectedGeneratingFunction symmetricMayerSum
  simp only [one_pow, mul_one, M.restrictedSymmetricMayerCoefficient_univ]
  have hshift :=
    M.summable_symmetricMayerDegreeSum_succ_of_koteckyPreiss_certified a hKP
  rw [tsum_eq_zero_add' hshift]
  simp

/-- The absolutely convergent symmetric finite Mayer sum exponentiates
exactly to the finite partition function. -/
theorem exp_symmetricMayerSum_eq_partitionFunction_of_koteckyPreiss
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    Complex.exp M.symmetricMayerSum = M.partitionFunction := by
  rw [← M.connectedGeneratingFunction_one_eq_symmetricMayerSum a hKP]
  exact M.exp_connectedGeneratingFunction_one_eq_partitionFunction a hKP

set_option maxHeartbeats 400000 in
-- Regrouping the absolutely convergent multi-index series by total degree
-- creates dependent finite fibers and is just above the default elaboration
-- budget in object-code builds.
/-- Under a genuine KP certificate, the degree-organized symmetric Mayer sum
is exactly the absolutely convergent sum over all finite multi-indices. -/
theorem symmetricMayerSum_eq_tsum_mayerClusterTerm_of_koteckyPreiss
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    M.symmetricMayerSum = ∑' X : MayerMultiIndex P, M.mayerClusterTerm X := by
  let b : ℕ → ℝ := fun n ↦ M.normMayerDegreeSum n
  have hbzero : b 0 = 0 := by
    unfold b normMayerDegreeSum
    apply Finset.sum_eq_zero
    intro X hX
    rw [norm_eq_zero]
    apply M.mayerClusterTerm_eq_zero_of_not_connected
    intro hconnected
    rcases hconnected.nonempty with ⟨⟨γ, i⟩⟩
    have hdegree := (mem_mayerMultiIndicesOfDegree 0 X).mp hX
    unfold mayerDegree at hdegree
    have hγ : X γ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Nat.zero_le _)).mp
        hdegree γ (Finset.mem_univ γ)
    simpa [hγ] using i.isLt
  have hbshift : Summable (fun n : ℕ ↦ b (n + 1)) := by
    simpa [b] using
      M.summable_normMayerDegreeSum_succ_of_koteckyPreiss_certified a hKP
  have hb : Summable b := (summable_nat_add_iff 1).mp (by
    simpa [Nat.add_comm] using hbshift)
  have hfiber (n : ℕ) :
      (∑' X : {X : MayerMultiIndex P // mayerDegree X = n},
        ‖M.mayerClusterTerm X.1‖) = b n := by
    letI : Fintype {X : MayerMultiIndex P // mayerDegree X = n} :=
      Fintype.ofFinset (mayerMultiIndicesOfDegree (P := P) n)
        (fun X ↦ mem_mayerMultiIndicesOfDegree n X)
    rw [tsum_fintype]
    unfold b normMayerDegreeSum
    exact (Finset.sum_subtype (mayerMultiIndicesOfDegree (P := P) n)
      (fun X ↦ mem_mayerMultiIndicesOfDegree n X)
      (fun X ↦ ‖M.mayerClusterTerm X‖)).symm
  let e := Equiv.sigmaFiberEquiv
    (mayerDegree : MayerMultiIndex P → ℕ)
  have hsigmaNorm : Summable
      (fun z : Σ n, {X : MayerMultiIndex P // mayerDegree X = n} ↦
        ‖M.mayerClusterTerm z.2.1‖) := by
    rw [summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)]
    refine ⟨?_, ?_⟩
    · intro n
      letI : Fintype {X : MayerMultiIndex P // mayerDegree X = n} :=
        Fintype.ofFinset (mayerMultiIndicesOfDegree (P := P) n)
          (fun X ↦ mem_mayerMultiIndicesOfDegree n X)
      exact Summable.of_finite
    · exact hb.congr fun n ↦ (hfiber n).symm
  have hsigma : Summable
      (fun z : Σ n, {X : MayerMultiIndex P // mayerDegree X = n} ↦
        M.mayerClusterTerm z.2.1) :=
    summable_norm_iff.mp hsigmaNorm
  have hfiberSummable (n : ℕ) : Summable
      (fun X : {X : MayerMultiIndex P // mayerDegree X = n} ↦
        M.mayerClusterTerm X.1) := by
    letI : Fintype {X : MayerMultiIndex P // mayerDegree X = n} :=
      Fintype.ofFinset (mayerMultiIndicesOfDegree (P := P) n)
        (fun X ↦ mem_mayerMultiIndicesOfDegree n X)
    exact Summable.of_finite
  have hinner (n : ℕ) :
      M.symmetricMayerDegreeSum n =
        ∑' X : {X : MayerMultiIndex P // mayerDegree X = n},
          M.mayerClusterTerm X.1 := by
    letI : Fintype {X : MayerMultiIndex P // mayerDegree X = n} :=
      Fintype.ofFinset (mayerMultiIndicesOfDegree (P := P) n)
        (fun X ↦ mem_mayerMultiIndicesOfDegree n X)
    rw [tsum_fintype]
    unfold symmetricMayerDegreeSum
    exact Finset.sum_subtype (mayerMultiIndicesOfDegree (P := P) n)
      (fun X ↦ mem_mayerMultiIndicesOfDegree n X)
      (fun X ↦ M.mayerClusterTerm X)
  calc
    M.symmetricMayerSum = ∑' n : ℕ,
        ∑' X : {X : MayerMultiIndex P // mayerDegree X = n},
          M.mayerClusterTerm X.1 := by
      unfold symmetricMayerSum
      exact tsum_congr hinner
    _ = ∑' z : Σ n, {X : MayerMultiIndex P // mayerDegree X = n},
        M.mayerClusterTerm z.2.1 := by
      symm
      exact hsigma.tsum_sigma' hfiberSummable
    _ = ∑' X : MayerMultiIndex P, M.mayerClusterTerm X := e.tsum_eq _

end FinitePolymerModel

end

end YangMills.Polymer
