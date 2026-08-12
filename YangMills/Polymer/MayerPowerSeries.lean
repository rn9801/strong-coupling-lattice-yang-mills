/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.FiniteGas
import YangMills.Polymer.MayerNormalization
import YangMills.Polymer.PowerSeriesLog

/-!
# The scalar activity-counting partition power series

Scaling every activity by one formal variable turns the finite hard-core
partition function into a polynomial power series, graded by family
cardinality.  Its formal logarithm is the canonical branch to which the
symmetric Mayer degree coefficients must be compared.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

namespace FinitePolymerModel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Coefficient of degree `n` in the uniformly activity-scaled finite
partition function. -/
def partitionDegreeCoefficient (M : FinitePolymerModel P)
    (S : Finset P) (n : ℕ) : ℂ :=
  ∑ Γ ∈ (M.compatibleFamilies S).filter (fun Γ => Γ.card = n),
    M.familyWeight Γ

/-- Finite partition polynomial, viewed as a formal power series. -/
def partitionPowerSeries (M : FinitePolymerModel P)
    (S : Finset P) : PowerSeries ℂ :=
  PowerSeries.mk (M.partitionDegreeCoefficient S)

omit [DecidableEq P] in
@[simp]
theorem coeff_partitionPowerSeries (M : FinitePolymerModel P)
    (S : Finset P) (n : ℕ) :
    PowerSeries.coeff n (M.partitionPowerSeries S) =
      M.partitionDegreeCoefficient S n := by
  simp [partitionPowerSeries]

omit [DecidableEq P] in
/-- The activity-graded coefficients regroup exactly to the original finite
restricted partition function. -/
theorem sum_partitionDegreeCoefficient_range
    (M : FinitePolymerModel P) (S : Finset P) :
    ∑ n ∈ Finset.range (S.card + 1),
        M.partitionDegreeCoefficient S n = M.partitionOn S := by
  classical
  unfold partitionDegreeCoefficient partitionOn
  apply Finset.sum_fiberwise_of_maps_to
  intro Γ hΓ
  have hsub : Γ ⊆ S := by
    exact Finset.mem_powerset.mp
      (Finset.mem_filter.mp hΓ).1
  exact Finset.mem_range.mpr
    (Nat.lt_succ_of_le (Finset.card_le_card hsub))

omit [DecidableEq P] in
/-- The finite partition power series is supported in degrees at most
`S.card`. -/
theorem partitionDegreeCoefficient_eq_zero_of_card_lt
    (M : FinitePolymerModel P) (S : Finset P) {n : ℕ}
    (hcard : S.card < n) :
    M.partitionDegreeCoefficient S n = 0 := by
  classical
  unfold partitionDegreeCoefficient
  apply Finset.sum_eq_zero
  intro Γ hΓ
  have hmem := Finset.mem_filter.mp hΓ
  have hsub : Γ ⊆ S := Finset.mem_powerset.mp
    (Finset.mem_filter.mp hmem.1).1
  have hle := Finset.card_le_card hsub
  omega

omit [DecidableEq P] in
@[simp]
theorem partitionDegreeCoefficient_zero
    (M : FinitePolymerModel P) (S : Finset P) :
    M.partitionDegreeCoefficient S 0 = 1 := by
  classical
  unfold partitionDegreeCoefficient
  have hfilter :
      (M.compatibleFamilies S).filter (fun Γ => Γ.card = 0) = {∅} := by
    ext Γ
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      exact Finset.card_eq_zero.mp h.2
    · rintro rfl
      simp [compatibleFamilies, Compatible]
  rw [hfilter]
  simp

omit [DecidableEq P] in
@[simp]
theorem constantCoeff_partitionPowerSeries
    (M : FinitePolymerModel P) (S : Finset P) :
    PowerSeries.constantCoeff (M.partitionPowerSeries S) = 1 := by
  rw [partitionPowerSeries, PowerSeries.constantCoeff_mk]
  exact M.partitionDegreeCoefficient_zero S

/-- The canonical formal Mayer logarithm of a finite restricted gas. -/
def formalMayerLog (M : FinitePolymerModel P)
    (S : Finset P) : PowerSeries ℂ :=
  PowerSeries.logOf (M.partitionPowerSeries S)

omit [DecidableEq P] in
@[simp]
theorem constantCoeff_formalMayerLog
    (M : FinitePolymerModel P) (S : Finset P) :
    PowerSeries.constantCoeff (M.formalMayerLog S) = 0 :=
  PowerSeries.constantCoeff_logOf (M.constantCoeff_partitionPowerSeries S)

omit [DecidableEq P] in
/-- Exact formal finite Mayer/log-partition identity. -/
theorem expOf_formalMayerLog_eq_partitionPowerSeries
    (M : FinitePolymerModel P) (S : Finset P) :
    PowerSeriesBridge.expOf (M.formalMayerLog S) =
      M.partitionPowerSeries S :=
  PowerSeriesBridge.expOf_logOf (M.constantCoeff_partitionPowerSeries S)

/-- Candidate connected coefficient of positive degree, restricted to
multi-indices supported in `S`.  Degree zero is fixed separately to be zero,
as required of a logarithm. -/
def restrictedSymmetricMayerCoefficient
    (M : FinitePolymerModel P) (S : Finset P) : ℕ → ℂ
  | 0 => 0
  | n + 1 =>
      ∑ X ∈ (mayerMultiIndicesOfDegree (P := P) (n + 1)).filter
          (fun X => X.support ⊆ S),
        M.mayerClusterTerm X

/-- Formal power series of restricted symmetric connected Mayer
coefficients. -/
def restrictedSymmetricMayerPowerSeries
    (M : FinitePolymerModel P) (S : Finset P) : PowerSeries ℂ :=
  PowerSeries.mk (M.restrictedSymmetricMayerCoefficient S)

@[simp]
theorem constantCoeff_restrictedSymmetricMayerPowerSeries
    (M : FinitePolymerModel P) (S : Finset P) :
    PowerSeries.constantCoeff
      (M.restrictedSymmetricMayerPowerSeries S) = 0 := by
  simp [restrictedSymmetricMayerPowerSeries,
    restrictedSymmetricMayerCoefficient]

/-- Once the connected exponential formula is proved coefficientwise, no
further branch argument remains: formal exponential injectivity identifies
the symmetric Mayer series with the canonical finite partition logarithm. -/
theorem restrictedSymmetricMayerPowerSeries_eq_formalMayerLog_of_expOf_eq
    (M : FinitePolymerModel P) (S : Finset P)
    (hExp : PowerSeriesBridge.expOf
        (M.restrictedSymmetricMayerPowerSeries S) =
      M.partitionPowerSeries S) :
    M.restrictedSymmetricMayerPowerSeries S = M.formalMayerLog S := by
  exact PowerSeriesBridge.eq_logOf_of_expOf_eq
    (M.constantCoeff_restrictedSymmetricMayerPowerSeries S) hExp

end FinitePolymerModel

end

end YangMills.Polymer
