/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Measure-preserving eigenfunction selection

The lemma in this file is the abstract change-of-variables argument behind
center selection.  It is deliberately independent of lattice gauge theory:
an integrable eigenfunction of a measure-preserving automorphism has zero
integral whenever its eigenvalue is not one.
-/

open MeasureTheory

namespace YangMills.Probability

variable {X : Type*} [MeasurableSpace X]

/-- A nontrivial eigenfunction of a measure-preserving measurable
automorphism has zero integral. -/
theorem integral_eq_zero_of_measurePreserving_eigen
    (mu : Measure X) (T : X ≃ᵐ X) (hT : MeasurePreserving T mu mu)
    (f : X → ℂ) (c : ℂ) (hc : c ≠ 1)
    (heigen : ∀ x, f (T x) = c * f x) :
    ∫ x, f x ∂mu = 0 := by
  have hchange := hT.integral_comp' f
  have hscale : (∫ x, f (T x) ∂mu) = c * ∫ x, f x ∂mu := by
    simp_rw [heigen]
    exact integral_const_mul c f
  rw [hscale] at hchange
  exact eq_zero_of_mul_eq_self_left hc hchange

end YangMills.Probability
