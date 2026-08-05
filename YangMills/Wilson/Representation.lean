/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.FiniteVolume
import YangMills.Gauge.Observable
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Exponential

/-!
# Continuous finite-dimensional unitary representations

This module gives the narrow representation-theoretic interface needed by
Wilson lattice gauge theory. It packages a positive-dimensional continuous
homomorphism into a matrix unitary group, then derives its character,
normalized character, and bounded real Wilson plaquette potential.
-/

namespace YangMills.Wilson

open YangMills.Gauge

noncomputable section

/-- A positive-dimensional continuous unitary representation in fixed matrix
coordinates. The explicit dimension positivity makes normalized characters
canonical without a separate typeclass assumption. -/
structure ContinuousUnitaryRepData (G : Type*) (n : ℕ)
    [Group G] [TopologicalSpace G] where
  ρ : G →* Matrix.unitaryGroup (Fin n) ℂ
  continuous_ρ : Continuous ρ
  dimension_pos : 0 < n

namespace ContinuousUnitaryRepData

variable {G : Type*} {n : ℕ} [Group G] [TopologicalSpace G]

/-- Matrix character of a continuous unitary representation. -/
def character (ρ : ContinuousUnitaryRepData G n) (g : G) : ℂ :=
  Matrix.trace (ρ.ρ g : Matrix (Fin n) (Fin n) ℂ)

/-- The matrix character is continuous. -/
theorem continuous_character (ρ : ContinuousUnitaryRepData G n) :
    Continuous ρ.character := by
  apply Continuous.matrix_trace
  exact continuous_subtype_val.comp ρ.continuous_ρ

/-- Characters are invariant under conjugation. -/
theorem character_conj (ρ : ContinuousUnitaryRepData G n) (a g : G) :
    ρ.character (a * g * a⁻¹) = ρ.character g := by
  simpa only [character, map_mul, map_inv, Matrix.UnitaryGroup.mul_val,
    Matrix.UnitaryGroup.inv_val, Unitary.val_toUnits_apply,
    Unitary.val_inv_toUnits_apply] using
    Matrix.trace_units_conj (Unitary.toUnits (ρ.ρ a))
      (ρ.ρ g : Matrix (Fin n) (Fin n) ℂ)

/-- The character of the inverse is the complex conjugate character. -/
theorem character_inv (ρ : ContinuousUnitaryRepData G n) (g : G) :
    ρ.character g⁻¹ = star (ρ.character g) := by
  simp only [character, map_inv, Matrix.UnitaryGroup.inv_val,
    Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]

/-- A unitary character has norm at most the representation dimension. -/
theorem norm_character_le (ρ : ContinuousUnitaryRepData G n) (g : G) :
    ‖ρ.character g‖ ≤ n := by
  unfold character Matrix.trace Matrix.diag
  calc
    ‖∑ i : Fin n, (ρ.ρ g : Matrix (Fin n) (Fin n) ℂ) i i‖ ≤
        ∑ i : Fin n, ‖(ρ.ρ g : Matrix (Fin n) (Fin n) ℂ) i i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
      exact Finset.sum_le_sum fun i _ =>
        entry_norm_bound_of_unitary (ρ.ρ g).property i i
    _ = n := by simp

/-- The character at the identity is the representation dimension. -/
@[simp]
theorem character_one (ρ : ContinuousUnitaryRepData G n) :
    ρ.character 1 = n := by
  simp [character]

/-- Character divided by the positive representation dimension. -/
def normalizedCharacter (ρ : ContinuousUnitaryRepData G n) (g : G) : ℂ :=
  (n : ℂ)⁻¹ * ρ.character g

/-- The normalized character is continuous. -/
theorem continuous_normalizedCharacter (ρ : ContinuousUnitaryRepData G n) :
    Continuous ρ.normalizedCharacter :=
  continuous_const.mul ρ.continuous_character

/-- The normalized character is a class function. -/
theorem normalizedCharacter_conj (ρ : ContinuousUnitaryRepData G n) (a g : G) :
    ρ.normalizedCharacter (a * g * a⁻¹) = ρ.normalizedCharacter g := by
  simp only [normalizedCharacter, ρ.character_conj]

/-- The normalized character sends inversion to complex conjugation. -/
theorem normalizedCharacter_inv (ρ : ContinuousUnitaryRepData G n) (g : G) :
    ρ.normalizedCharacter g⁻¹ = star (ρ.normalizedCharacter g) := by
  unfold normalizedCharacter
  rw [ρ.character_inv]
  simp

/-- The normalized character equals one at the identity. -/
@[simp]
theorem normalizedCharacter_one (ρ : ContinuousUnitaryRepData G n) :
    ρ.normalizedCharacter 1 = 1 := by
  rw [normalizedCharacter, character_one]
  exact inv_mul_cancel₀ (mod_cast ρ.dimension_pos.ne')

/-- The normalized character has norm at most one. -/
theorem norm_normalizedCharacter_le (ρ : ContinuousUnitaryRepData G n) (g : G) :
    ‖ρ.normalizedCharacter g‖ ≤ 1 := by
  rw [normalizedCharacter, norm_mul, norm_inv]
  have hn : (0 : ℝ) < n := by exact_mod_cast ρ.dimension_pos
  have hcast : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  rw [hcast]
  calc
    (n : ℝ)⁻¹ * ‖ρ.character g‖ ≤ (n : ℝ)⁻¹ * n := by
      exact mul_le_mul_of_nonneg_left (ρ.norm_character_le g) (inv_nonneg.mpr hn.le)
    _ = 1 := inv_mul_cancel₀ hn.ne'

/-- The normalized character as the continuous class-function label expected
by the local-observable layer. -/
def normalizedCharacterClassFunction (ρ : ContinuousUnitaryRepData G n) :
    ContinuousClassFunction G where
  toContinuousMap := ⟨ρ.normalizedCharacter, ρ.continuous_normalizedCharacter⟩
  map_conj := ρ.normalizedCharacter_conj

/-- The real part of the normalized character is the bounded real Wilson
plaquette potential. -/
def wilsonPotential (ρ : ContinuousUnitaryRepData G n) :
    RealPlaquettePotential G where
  toContinuousMap :=
    ⟨fun g => (ρ.normalizedCharacter g).re,
      Complex.continuous_re.comp ρ.continuous_normalizedCharacter⟩
  conj_invariant := fun a g => by
    change (ρ.normalizedCharacter (a * g * a⁻¹)).re = (ρ.normalizedCharacter g).re
    rw [ρ.normalizedCharacter_conj]
  inv_invariant := fun g => by
    change (ρ.normalizedCharacter g⁻¹).re = (ρ.normalizedCharacter g).re
    rw [ρ.normalizedCharacter_inv]
    simp
  bound := 1
  bound_nonneg := zero_le_one
  norm_le_bound := fun g => by
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (ρ.norm_normalizedCharacter_le g)

@[simp]
theorem wilsonPotential_apply (ρ : ContinuousUnitaryRepData G n) (g : G) :
    ρ.wilsonPotential g = (ρ.normalizedCharacter g).re :=
  rfl

/-- Real exponential perturbation bound in the form used by the Wilson
strong-coupling expansion. -/
theorem abs_exp_sub_one_le_exp_abs_sub_one (x : ℝ) :
    |Real.exp x - 1| ≤ Real.exp |x| - 1 := by
  calc
    |Real.exp x - 1| = ‖((Real.exp x - 1 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖Complex.exp (x : ℂ) - 1‖ := by
      rw [← Complex.ofReal_exp]
      norm_cast
    _ ≤ Real.exp |x| - 1 := by
      simpa [Real.norm_eq_abs] using
        (Complex.norm_exp_sub_sum_le_exp_norm_sub_sum (x : ℂ) 1)

/-- Uniform single-plaquette perturbation estimate for the normalized Wilson
potential. -/
theorem abs_exp_mul_wilsonPotential_sub_one_le
    (ρ : ContinuousUnitaryRepData G n) (β : ℝ) (g : G) :
    |Real.exp (β * ρ.wilsonPotential g) - 1| ≤ Real.exp |β| - 1 := by
  apply (abs_exp_sub_one_le_exp_abs_sub_one _).trans
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  calc
    |β * ρ.wilsonPotential g| = |β| * |ρ.wilsonPotential g| := abs_mul _ _
    _ ≤ |β| * 1 := by
      gcongr
      simpa only [Real.norm_eq_abs] using ρ.wilsonPotential.norm_le_bound g
    _ = |β| := mul_one _

end ContinuousUnitaryRepData

end

end YangMills.Wilson
