/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Complex.Basic

/-!
# A missing formal power-series logarithm identity

Mathlib currently defines `PowerSeries.logOf` but does not yet expose the
inverse identity saying that exponentiating it recovers a series with constant
coefficient one.  This file develops the derivative identities needed by the
Mayer exponential formula.  It is independent of every polymer model.
-/

namespace YangMills.Polymer

noncomputable section

namespace PowerSeriesBridge

/-- Exponential of a power series with zero constant term, defined by formal
substitution into Mathlib's exponential series. -/
def expOf (g : PowerSeries ℂ) : PowerSeries ℂ :=
  (PowerSeries.exp ℂ).subst g

theorem derivative_expOf {g : PowerSeries ℂ}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.derivative ℂ (expOf g) =
      expOf g * PowerSeries.derivative ℂ g := by
  rw [expOf, PowerSeries.derivative_subst
    ℂ (PowerSeries.HasSubst.of_constantCoeff_zero hg),
    PowerSeries.derivative_exp]

theorem constantCoeff_expOf {g : PowerSeries ℂ}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.constantCoeff (expOf g) = 1 := by
  change MvPowerSeries.constantCoeff (PowerSeries.subst g (PowerSeries.exp ℂ)) = 1
  rw [PowerSeries.constantCoeff_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero hg)]
  have hgc : MvPowerSeries.constantCoeff g = 0 := hg
  simp only [map_pow, hgc]
  simp only [PowerSeries.coeff_exp, one_div]
  rw [finsum_eq_single _ 0 (fun n hn => by simp [hn])]
  simp

/-- The derivative of the formal logarithm is the inverse of `1 + X`. -/
theorem derivative_log_mul_one_add_X :
    PowerSeries.derivative ℂ (PowerSeries.log ℂ) *
        (1 + PowerSeries.X) = 1 := by
  rw [PowerSeries.deriv_log]
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_mul]
  | succ n =>
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ']
      simp only [PowerSeries.coeff_one, PowerSeries.coeff_mk, map_pow, map_neg,
        map_one]
      rw [Finset.sum_eq_single (n, 0)]
      · simp [pow_succ]
      · rintro ⟨i, j⟩ hij hne
        cases j with
        | zero =>
            exfalso
            apply hne
            have hsum : i + 0 = n := Finset.mem_antidiagonal.mp hij
            ext <;> omega
        | succ j =>
            simp [PowerSeries.coeff_X]
      · simp

/-- Substituting the logarithmic derivative at `f - 1` gives the formal
inverse of `f`. -/
theorem derivative_log_subst_eq_inv {f : PowerSeries ℂ}
    (hf : PowerSeries.constantCoeff f = 1) :
    (PowerSeries.derivative ℂ (PowerSeries.log ℂ)).subst (f - 1) = f⁻¹ := by
  let hsub : PowerSeries.HasSubst (f - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      change PowerSeries.constantCoeff f - 1 = 0
      rw [hf, sub_self])
  have hmul := congrArg (PowerSeries.substAlgHom hsub)
    derivative_log_mul_one_add_X
  simp only [map_mul, map_add, map_one, PowerSeries.substAlgHom_X] at hmul
  calc
    (PowerSeries.derivative ℂ (PowerSeries.log ℂ)).subst (f - 1) =
        (PowerSeries.derivative ℂ (PowerSeries.log ℂ)).subst (f - 1) *
          (f * f⁻¹) := by
            rw [PowerSeries.mul_inv_cancel f]
            · simp
            · simp [hf]
    _ = f⁻¹ := by
      rw [← mul_assoc]
      change _ * f * f⁻¹ = f⁻¹
      rw [show (PowerSeries.derivative ℂ (PowerSeries.log ℂ)).subst (f - 1) * f = 1 by
        simpa [PowerSeries.coe_substAlgHom, add_sub_cancel] using hmul]
      simp

/-- Formal logarithmic derivative. -/
theorem derivative_logOf {f : PowerSeries ℂ}
    (hf : PowerSeries.constantCoeff f = 1) :
    PowerSeries.derivative ℂ (PowerSeries.logOf f) =
      f⁻¹ * PowerSeries.derivative ℂ f := by
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst
    ℂ (PowerSeries.HasSubst.of_constantCoeff_zero (by
      change PowerSeries.constantCoeff f - 1 = 0
      rw [hf, sub_self])),
    derivative_log_subst_eq_inv hf]
  simp

/-- Exponentiating Mathlib's formal `logOf` recovers every complex power
series with constant coefficient one. -/
theorem expOf_logOf {f : PowerSeries ℂ}
    (hf : PowerSeries.constantCoeff f = 1) :
    expOf (PowerSeries.logOf f) = f := by
  let g := PowerSeries.logOf f
  have hg : PowerSeries.constantCoeff g = 0 :=
    PowerSeries.constantCoeff_logOf hf
  let E := expOf g
  have hEder : PowerSeries.derivative ℂ E =
      E * PowerSeries.derivative ℂ g := derivative_expOf hg
  have hgder : PowerSeries.derivative ℂ g =
      f⁻¹ * PowerSeries.derivative ℂ f := derivative_logOf hf
  have hfne : PowerSeries.constantCoeff f ≠ 0 := by simp [hf]
  have hprodder : PowerSeries.derivative ℂ (E * f⁻¹) = 0 := by
    change PowerSeries.derivativeFun (E * f⁻¹) = 0
    rw [PowerSeries.derivativeFun_mul]
    simp only [smul_eq_mul]
    rw [show PowerSeries.derivativeFun E =
        E * PowerSeries.derivative ℂ g from hEder,
      show PowerSeries.derivativeFun f⁻¹ =
        -f⁻¹ ^ 2 * PowerSeries.derivative ℂ f by
          exact PowerSeries.derivative_inv' f,
      hgder]
    ring
  have hprodconst : PowerSeries.constantCoeff (E * f⁻¹) = 1 := by
    rw [map_mul]
    have hEc : PowerSeries.constantCoeff E = 1 := constantCoeff_expOf hg
    rw [hEc]
    simp [hf]
  have hprod : E * f⁻¹ = 1 := by
    apply PowerSeries.derivative.ext
    · simpa using hprodder
    · simpa using hprodconst
  change E = f
  calc
    E = (E * f⁻¹) * f := by
      rw [mul_assoc, PowerSeries.inv_mul_cancel f hfne, mul_one]
    _ = f := by rw [hprod, one_mul]

/-- Conversely, taking `logOf` after formal exponentiation recovers a series
with zero constant coefficient. -/
theorem logOf_expOf {g : PowerSeries ℂ}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.logOf (expOf g) = g := by
  let E := expOf g
  have hEc : PowerSeries.constantCoeff E = 1 := constantCoeff_expOf hg
  apply PowerSeries.derivative.ext
  · rw [derivative_logOf hEc, derivative_expOf hg]
    rw [← mul_assoc, PowerSeries.inv_mul_cancel E (by simp [hEc]), one_mul]
  · rw [PowerSeries.constantCoeff_logOf hEc, hg]

/-- Formal exponentiation is injective on the augmentation ideal. -/
theorem expOf_injective_on_constantCoeff_zero
    {g h : PowerSeries ℂ}
    (hg : PowerSeries.constantCoeff g = 0)
    (hh : PowerSeries.constantCoeff h = 0)
    (heq : expOf g = expOf h) :
    g = h := by
  rw [← logOf_expOf hg, heq, logOf_expOf hh]

/-- A zero-constant-term series whose formal exponential is `f` is exactly
Mathlib's `logOf f`. -/
theorem eq_logOf_of_expOf_eq
    {g f : PowerSeries ℂ}
    (hg : PowerSeries.constantCoeff g = 0)
    (heq : expOf g = f) :
    g = PowerSeries.logOf f := by
  rw [← heq, logOf_expOf hg]

end PowerSeriesBridge

end

end YangMills.Polymer
