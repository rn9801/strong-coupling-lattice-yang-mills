/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.PowerSeriesLog
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Two formal polynomial sources in a power series

The power-series variable records total polymer activity.  The two variables
of `MvPolynomial (Fin 2) ℂ` are independent observable sources.  The mixed
source coefficient of a formal exponential is the sum of a genuinely
two-root connected coefficient and the product of its two one-root
coefficients.  This is the algebraic cancellation behind truncated
correlations.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

namespace BivariateSourcePowerSeries

abbrev Coeff := MvPolynomial (Fin 2) ℂ

/-- Formal exponential for a series with two polynomial source variables. -/
def expOf (g : PowerSeries Coeff) : PowerSeries Coeff :=
  (PowerSeries.exp Coeff).subst g

/-- Partial differentiation in source `i`, coefficient by coefficient. -/
def sourceDerivative (i : Fin 2) (f : PowerSeries Coeff) : PowerSeries Coeff :=
  PowerSeries.mk fun n => MvPolynomial.pderiv i (PowerSeries.coeff n f)

@[simp]
theorem coeff_sourceDerivative (i : Fin 2) (f : PowerSeries Coeff) (n : ℕ) :
    PowerSeries.coeff n (sourceDerivative i f) =
      MvPolynomial.pderiv i (PowerSeries.coeff n f) := by
  simp [sourceDerivative]

@[simp]
theorem constantCoeff_sourceDerivative (i : Fin 2) (f : PowerSeries Coeff) :
    PowerSeries.constantCoeff (sourceDerivative i f) =
      MvPolynomial.pderiv i (PowerSeries.constantCoeff f) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [coeff_sourceDerivative]

theorem sourceDerivative_add (i : Fin 2) (f g : PowerSeries Coeff) :
    sourceDerivative i (f + g) =
      sourceDerivative i f + sourceDerivative i g := by
  apply PowerSeries.ext
  intro n
  simp

theorem sourceDerivative_sub (i : Fin 2) (f g : PowerSeries Coeff) :
    sourceDerivative i (f - g) =
      sourceDerivative i f - sourceDerivative i g := by
  apply PowerSeries.ext
  intro n
  simp

theorem sourceDerivative_mul (i : Fin 2) (f g : PowerSeries Coeff) :
    sourceDerivative i (f * g) =
      sourceDerivative i f * g + f * sourceDerivative i g := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_sourceDerivative, PowerSeries.coeff_mul,
    map_sum, MvPolynomial.pderiv_mul, map_add]
  rw [Finset.sum_add_distrib]

theorem sourceDerivative_derivative (i : Fin 2) (f : PowerSeries Coeff) :
    sourceDerivative i (PowerSeries.derivative Coeff f) =
      PowerSeries.derivative Coeff (sourceDerivative i f) := by
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.coeff_derivative, mul_comm]

theorem derivative_expOf {g : PowerSeries Coeff}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.derivative Coeff (expOf g) =
      expOf g * PowerSeries.derivative Coeff g := by
  rw [expOf, PowerSeries.derivative_subst
    Coeff (PowerSeries.HasSubst.of_constantCoeff_zero hg),
    PowerSeries.derivative_exp]

theorem constantCoeff_expOf {g : PowerSeries Coeff}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.constantCoeff (expOf g) = 1 := by
  change MvPowerSeries.constantCoeff
      (PowerSeries.subst g (PowerSeries.exp Coeff)) = 1
  rw [PowerSeries.constantCoeff_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero hg)]
  have hgc : MvPowerSeries.constantCoeff g = 0 := hg
  simp only [map_pow, hgc, PowerSeries.coeff_exp, one_div]
  rw [finsum_eq_single _ 0 (fun n hn => by simp [hn])]
  simp

/-- A homogeneous formal ODE with zero initial value has only the zero
solution. -/
theorem eq_zero_of_derivative_eq_mul
    (h k : PowerSeries Coeff)
    (hder : PowerSeries.derivative Coeff h = h * k)
    (hzero : PowerSeries.constantCoeff h = 0) :
    h = 0 := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simpa [PowerSeries.constantCoeff] using hzero
      | succ n =>
          have hcoeff := congrArg (PowerSeries.coeff n) hder
          rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at hcoeff
          have hsum :
              (∑ x ∈ Finset.antidiagonal n,
                PowerSeries.coeff x.1 h * PowerSeries.coeff x.2 k) = 0 := by
            apply Finset.sum_eq_zero
            rintro ⟨a, b⟩ hab
            have ha : a < n + 1 := by
              have hab' := Finset.mem_antidiagonal.mp hab
              omega
            rw [ih a ha]
            simp
          rw [hsum] at hcoeff
          have hcast : ((n : Coeff) + 1) ≠ 0 := by
            intro hzero
            have hc := congrArg
              (MvPolynomial.constantCoeff : Coeff →+* ℂ) hzero
            have hc' : (n : ℂ) + 1 = 0 := by
              simpa using hc
            have hnat : n + 1 = 0 := by
              exact_mod_cast hc'
            omega
          exact (mul_eq_zero.mp hcoeff).resolve_right hcast

/-- Formal chain rule for either polynomial source. -/
theorem sourceDerivative_expOf {g : PowerSeries Coeff}
    (hg : PowerSeries.constantCoeff g = 0) (i : Fin 2) :
    sourceDerivative i (expOf g) =
      expOf g * sourceDerivative i g := by
  let e := expOf g
  let h := sourceDerivative i e - e * sourceDerivative i g
  have he : PowerSeries.derivative Coeff e =
      e * PowerSeries.derivative Coeff g := derivative_expOf hg
  have hhder : PowerSeries.derivative Coeff h =
      h * PowerSeries.derivative Coeff g := by
    have hprod : PowerSeries.derivative Coeff
        (e * sourceDerivative i g) =
        e * PowerSeries.derivative Coeff (sourceDerivative i g) +
          sourceDerivative i g * PowerSeries.derivative Coeff e := by
      simpa only [smul_eq_mul] using
        PowerSeries.derivativeFun_mul e (sourceDerivative i g)
    dsimp [h]
    rw [map_sub, ← sourceDerivative_derivative, he,
      sourceDerivative_mul, sourceDerivative_derivative, hprod, he]
    ring
  have hhzero : PowerSeries.constantCoeff h = 0 := by
    dsimp [h, e]
    rw [map_sub, map_mul, constantCoeff_sourceDerivative,
      constantCoeff_expOf hg, constantCoeff_sourceDerivative, hg]
    simp
  have hh := eq_zero_of_derivative_eq_mul h
    (PowerSeries.derivative Coeff g) hhder hhzero
  dsimp [h] at hh
  exact sub_eq_zero.mp hh

/-- Evaluating both polynomial sources commutes with the formal
exponential. -/
theorem map_expOf_eval (g : PowerSeries Coeff)
    (hg : PowerSeries.constantCoeff g = 0) (alpha : Fin 2 → ℂ) :
    (expOf g).map (MvPolynomial.eval alpha) =
      PowerSeriesBridge.expOf
        (g.map (MvPolynomial.eval alpha)) := by
  unfold expOf PowerSeriesBridge.expOf
  calc
    (PowerSeries.subst g (PowerSeries.exp Coeff)).map
        (MvPolynomial.eval alpha) =
      ((PowerSeries.exp Coeff).map (MvPolynomial.eval alpha)).subst
        (g.map (MvPolynomial.eval alpha)) :=
      PowerSeries.map_subst
        (PowerSeries.HasSubst.of_constantCoeff_zero hg)
        (PowerSeries.exp Coeff)
    _ = (PowerSeries.exp ℂ).subst
        (g.map (MvPolynomial.eval alpha)) := by
      rw [PowerSeries.map_exp]

/-- Evaluation at zero in both source variables. -/
def constantSource (f : PowerSeries Coeff) : PowerSeries ℂ :=
  f.map MvPolynomial.constantCoeff

/-- Coefficient linear in source `i` and constant in the other source. -/
def linearCoefficient (i : Fin 2) (f : PowerSeries Coeff) : PowerSeries ℂ :=
  constantSource (sourceDerivative i f)

/-- Coefficient bilinear in the two distinct sources. -/
def mixedCoefficient (f : PowerSeries Coeff) : PowerSeries ℂ :=
  constantSource
    (sourceDerivative (0 : Fin 2) (sourceDerivative (1 : Fin 2) f))

/-- Linear extraction in the first variable on a two-variable monomial. -/
theorem constantCoeff_pderiv_first_twoVariableMonomial
    (a b : ℕ) (z : ℂ) :
    MvPolynomial.constantCoeff
        (MvPolynomial.pderiv (0 : Fin 2)
          ((MvPolynomial.X (0 : Fin 2)) ^ a *
            (MvPolynomial.X (1 : Fin 2)) ^ b * MvPolynomial.C z)) =
      if a = 1 ∧ b = 0 then z else 0 := by
  rcases a with _ | a
  · simp
  rcases b with _ | b
  · rcases a with _ | a <;> simp
  · simp

/-- Linear extraction in the second variable on a two-variable monomial. -/
theorem constantCoeff_pderiv_second_twoVariableMonomial
    (a b : ℕ) (z : ℂ) :
    MvPolynomial.constantCoeff
        (MvPolynomial.pderiv (1 : Fin 2)
          ((MvPolynomial.X (0 : Fin 2)) ^ a *
            (MvPolynomial.X (1 : Fin 2)) ^ b * MvPolynomial.C z)) =
      if a = 0 ∧ b = 1 then z else 0 := by
  rcases a with _ | a
  · rcases b with _ | b
    · simp
    · rcases b with _ | b <;> simp
  · simp

/-- Mixed extraction on a two-variable monomial. -/
theorem constantCoeff_pderiv_pderiv_twoVariableMonomial
    (a b : ℕ) (z : ℂ) :
    MvPolynomial.constantCoeff
        (MvPolynomial.pderiv (0 : Fin 2)
          (MvPolynomial.pderiv (1 : Fin 2)
            ((MvPolynomial.X (0 : Fin 2)) ^ a *
              (MvPolynomial.X (1 : Fin 2)) ^ b *
                MvPolynomial.C z))) =
      if a = 1 ∧ b = 1 then z else 0 := by
  rcases a with _ | a
  · simp
  rcases b with _ | b
  · simp
  rcases a with _ | a
  · rcases b with _ | b
    · simp
    · simp
  · simp

/-- Mixed pointed exponential formula.  The second summand is precisely the
product removed when passing from a two-source moment to its cumulant. -/
theorem mixedCoefficient_expOf {g : PowerSeries Coeff}
    (hg : PowerSeries.constantCoeff g = 0) :
    mixedCoefficient (expOf g) =
      constantSource (expOf g) *
        (mixedCoefficient g +
          linearCoefficient 0 g * linearCoefficient 1 g) := by
  unfold mixedCoefficient linearCoefficient constantSource
  rw [sourceDerivative_expOf hg 1,
    sourceDerivative_mul, sourceDerivative_expOf hg 0]
  simp only [map_add, map_mul]
  ring

end BivariateSourcePowerSeries

end

end YangMills.Polymer
