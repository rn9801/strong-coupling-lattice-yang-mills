/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.PowerSeriesLog
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Formal differentiation of a polynomial source

The total-activity variable of a Mayer series is the power-series variable.
Observable sources are independent polynomial variables in the coefficient
ring.  This file supplies the algebraic chain rule needed to extract the
coefficient linear in one source from a formal exponential.  It is entirely
polymer-independent.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

namespace SourcePowerSeries

abbrev Coeff := Polynomial ℂ

/-- Formal exponential for a series with polynomial coefficients. -/
def expOf (g : PowerSeries Coeff) : PowerSeries Coeff :=
  (PowerSeries.exp Coeff).subst g

/-- Differentiation in the polynomial source, coefficient by coefficient. -/
def sourceDerivative (f : PowerSeries Coeff) : PowerSeries Coeff :=
  PowerSeries.mk fun n => (PowerSeries.coeff n f).derivative

@[simp]
theorem coeff_sourceDerivative (f : PowerSeries Coeff) (n : ℕ) :
    PowerSeries.coeff n (sourceDerivative f) =
      (PowerSeries.coeff n f).derivative := by
  simp [sourceDerivative]

@[simp]
theorem constantCoeff_sourceDerivative (f : PowerSeries Coeff) :
    PowerSeries.constantCoeff (sourceDerivative f) =
      (PowerSeries.constantCoeff f).derivative := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [coeff_sourceDerivative]

theorem sourceDerivative_add (f g : PowerSeries Coeff) :
    sourceDerivative (f + g) = sourceDerivative f + sourceDerivative g := by
  apply PowerSeries.ext
  intro n
  simp

theorem sourceDerivative_sub (f g : PowerSeries Coeff) :
    sourceDerivative (f - g) = sourceDerivative f - sourceDerivative g := by
  apply PowerSeries.ext
  intro n
  simp

theorem sourceDerivative_mul (f g : PowerSeries Coeff) :
    sourceDerivative (f * g) =
      sourceDerivative f * g + f * sourceDerivative g := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_sourceDerivative, PowerSeries.coeff_mul,
    Polynomial.derivative_sum, Polynomial.derivative_mul,
    map_add]
  rw [Finset.sum_add_distrib]

theorem sourceDerivative_derivative (f : PowerSeries Coeff) :
    sourceDerivative (PowerSeries.derivative Coeff f) =
      PowerSeries.derivative Coeff (sourceDerivative f) := by
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.coeff_derivative]

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
solution.  This coefficient induction is the uniqueness input for the source
chain rule. -/
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
            rintro ⟨i, j⟩ hij
            have hi : i < n + 1 := by
              have hij' := Finset.mem_antidiagonal.mp hij
              omega
            rw [ih i hi]
            simp
          rw [hsum] at hcoeff
          have hcast : ((n : Coeff) + 1) ≠ 0 := by
            exact_mod_cast Nat.succ_ne_zero n
          exact (mul_eq_zero.mp hcoeff).resolve_right hcast

/-- Formal chain rule for differentiation in the coefficient source. -/
theorem sourceDerivative_expOf {g : PowerSeries Coeff}
    (hg : PowerSeries.constantCoeff g = 0) :
    sourceDerivative (expOf g) = expOf g * sourceDerivative g := by
  let e := expOf g
  let h := sourceDerivative e - e * sourceDerivative g
  have he : PowerSeries.derivative Coeff e =
      e * PowerSeries.derivative Coeff g := derivative_expOf hg
  have hhder : PowerSeries.derivative Coeff h =
      h * PowerSeries.derivative Coeff g := by
    have hprod : PowerSeries.derivative Coeff
        (e * sourceDerivative g) =
        e * PowerSeries.derivative Coeff (sourceDerivative g) +
          sourceDerivative g * PowerSeries.derivative Coeff e := by
      simpa only [smul_eq_mul] using
        PowerSeries.derivativeFun_mul e (sourceDerivative g)
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

/-- Evaluation of the coefficient-source exponential agrees with the usual
complex formal exponential. -/
theorem map_expOf_eval (g : PowerSeries Coeff)
    (hg : PowerSeries.constantCoeff g = 0) (alpha : ℂ) :
    (expOf g).map (Polynomial.evalRingHom alpha) =
      PowerSeriesBridge.expOf
        (g.map (Polynomial.evalRingHom alpha)) := by
  unfold expOf PowerSeriesBridge.expOf
  calc
    (PowerSeries.subst g (PowerSeries.exp Coeff)).map
        (Polynomial.evalRingHom alpha) =
      ((PowerSeries.exp Coeff).map (Polynomial.evalRingHom alpha)).subst
        (g.map (Polynomial.evalRingHom alpha)) :=
      PowerSeries.map_subst
        (PowerSeries.HasSubst.of_constantCoeff_zero hg)
        (PowerSeries.exp Coeff)
    _ = (PowerSeries.exp ℂ).subst
        (g.map (Polynomial.evalRingHom alpha)) := by
      rw [PowerSeries.map_exp]

/-- Evaluating a polynomial derivative at zero selects its linear
coefficient. -/
theorem eval_zero_derivative (p : Coeff) :
    Polynomial.eval 0 p.derivative = p.coeff 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_derivative]
  simp

/-- Power series obtained by selecting the coefficient linear in the
polynomial source. -/
def linearCoefficient (f : PowerSeries Coeff) : PowerSeries ℂ :=
  (sourceDerivative f).map (Polynomial.evalRingHom 0)

@[simp]
theorem coeff_linearCoefficient (f : PowerSeries Coeff) (n : ℕ) :
    PowerSeries.coeff n (linearCoefficient f) =
      (PowerSeries.coeff n f).coeff 1 := by
  rw [linearCoefficient, PowerSeries.coeff_map,
    coeff_sourceDerivative]
  exact eval_zero_derivative _

/-- Evaluation at zero in the source coefficient ring. -/
def constantSource (f : PowerSeries Coeff) : PowerSeries ℂ :=
  f.map (Polynomial.evalRingHom 0)

theorem linearCoefficient_expOf {g : PowerSeries Coeff}
    (hg : PowerSeries.constantCoeff g = 0) :
    linearCoefficient (expOf g) =
      constantSource (expOf g) * linearCoefficient g := by
  unfold linearCoefficient constantSource
  rw [sourceDerivative_expOf hg, map_mul]

end SourcePowerSeries

end

end YangMills.Polymer
