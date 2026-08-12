/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.BivariateSourcePowerSeries
import YangMills.Polymer.LabelledMayerExponential
import YangMills.Polymer.MayerPowerSeries

/-!
# Bigraded finite-polymer source expansions

A grading `Q → Fin 2 → ℕ` assigns two formal source degrees to every
polymer type.  Bulk, left-root, right-root, and bridge-root polymers can thus
carry degrees `(0,0)`, `(1,0)`, `(0,1)`, and `(1,1)`.  This file proves the
exact fixed-labelled Mayer exponential formula with those two sources kept
as polynomial coefficients.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

namespace FinitePolymerModel

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Total source degree of a Mayer multi-index in source coordinate `i`. -/
def bigradedMultiplicity (grading : Q → Fin 2 → ℕ)
    (X : MayerMultiIndex Q) (i : Fin 2) : ℕ :=
  ∑ q : Q, grading q i * X q

/-- Scale every activity by the monomial prescribed by a two-source
grading. -/
def scaleByBigradedSource (M : FinitePolymerModel Q)
    (grading : Q → Fin 2 → ℕ) (alpha : Fin 2 → ℂ) :
    FinitePolymerModel Q where
  incompatible := M.incompatible
  decidableIncompatible := M.decidableIncompatible
  symmetric_incompatible := M.symmetric_incompatible
  self_incompatible := M.self_incompatible
  activity q := (∏ i : Fin 2, alpha i ^ grading q i) * M.activity q

/-- Additive weight carried by a Mayer multi-index. -/
def weightedMultiplicity (weight : Q → ℕ)
    (X : MayerMultiIndex Q) : ℕ :=
  ∑ q : Q, weight q * X q

/-- Scale every polymer activity by a common parameter to its prescribed
natural weight. -/
def scaleByNatWeight (M : FinitePolymerModel Q)
    (weight : Q → ℕ) (t : ℂ) : FinitePolymerModel Q where
  incompatible := M.incompatible
  decidableIncompatible := M.decidableIncompatible
  symmetric_incompatible := M.symmetric_incompatible
  self_incompatible := M.self_incompatible
  activity q := t ^ weight q * M.activity q

theorem mayerActivityMonomial_scaleByNatWeight
    (M : FinitePolymerModel Q) (weight : Q → ℕ) (t : ℂ)
    (X : MayerMultiIndex Q) :
    (M.scaleByNatWeight weight t).mayerActivityMonomial X =
      t ^ weightedMultiplicity weight X * M.mayerActivityMonomial X := by
  classical
  unfold mayerActivityMonomial scaleByNatWeight weightedMultiplicity
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]
  apply congrArg₂ (fun a b : ℂ => a * b) ?_ rfl
  apply Finset.prod_congr rfl
  intro q _
  rw [pow_mul]

theorem mayerClusterTerm_scaleByNatWeight
    (M : FinitePolymerModel Q) (weight : Q → ℕ) (t : ℂ)
    (X : MayerMultiIndex Q) :
    (M.scaleByNatWeight weight t).mayerClusterTerm X =
      t ^ weightedMultiplicity weight X * M.mayerClusterTerm X := by
  unfold mayerClusterTerm
  rw [mayerActivityMonomial_scaleByNatWeight]
  change (M.mayerUrsell X : ℂ) / (mayerSymmetryFactor X : ℂ) *
      (t ^ weightedMultiplicity weight X * M.mayerActivityMonomial X) = _
  ring

theorem mayerActivityMonomial_scaleByBigradedSource
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (alpha : Fin 2 → ℂ) (X : MayerMultiIndex Q) :
    (M.scaleByBigradedSource grading alpha).mayerActivityMonomial X =
      (∏ i : Fin 2, alpha i ^ bigradedMultiplicity grading X i) *
        M.mayerActivityMonomial X := by
  classical
  unfold mayerActivityMonomial scaleByBigradedSource bigradedMultiplicity
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp_rw [← Finset.prod_pow]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro q _
  rw [pow_mul]

/-- Bigraded source scaling of normalized connected Mayer terms. -/
theorem mayerClusterTerm_scaleByBigradedSource
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (alpha : Fin 2 → ℂ) (X : MayerMultiIndex Q) :
    (M.scaleByBigradedSource grading alpha).mayerClusterTerm X =
      (∏ i : Fin 2, alpha i ^ bigradedMultiplicity grading X i) *
        M.mayerClusterTerm X := by
  unfold mayerClusterTerm
  rw [mayerActivityMonomial_scaleByBigradedSource]
  change (M.mayerUrsell X : ℂ) / (mayerSymmetryFactor X : ℂ) *
      ((∏ i : Fin 2, alpha i ^ bigradedMultiplicity grading X i) *
        M.mayerActivityMonomial X) = _
  ring

/-- Polynomial family weight retaining both formal sources. -/
def bigradedSourceFamilyWeight
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (Gamma : Finset Q) : BivariateSourcePowerSeries.Coeff :=
  ∏ q ∈ Gamma,
    (∏ i : Fin 2, MvPolynomial.X i ^ grading q i) *
      MvPolynomial.C (M.activity q)

theorem eval_bigradedSourceFamilyWeight
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (alpha : Fin 2 → ℂ) (Gamma : Finset Q) :
    MvPolynomial.eval alpha (M.bigradedSourceFamilyWeight grading Gamma) =
      (M.scaleByBigradedSource grading alpha).familyWeight Gamma := by
  classical
  unfold bigradedSourceFamilyWeight familyWeight scaleByBigradedSource
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro q _
  simp only [map_mul, map_prod, map_pow, MvPolynomial.eval_X,
    MvPolynomial.eval_C]

/-- Total-activity partition series with the bigraded sources retained. -/
def bigradedSourcePartitionPowerSeries
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ) :
    PowerSeries BivariateSourcePowerSeries.Coeff :=
  PowerSeries.mk fun n =>
    ∑ Gamma ∈ (M.compatibleFamilies Finset.univ).filter
        (fun Gamma => Gamma.card = n),
      M.bigradedSourceFamilyWeight grading Gamma

/-- Connected total-activity Mayer series with the bigraded sources
retained. -/
def bigradedSourceMayerPowerSeries
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ) :
    PowerSeries BivariateSourcePowerSeries.Coeff :=
  PowerSeries.mk fun
    | 0 => 0
    | n + 1 =>
        ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) (n + 1),
          (∏ i : Fin 2,
            MvPolynomial.X i ^ bigradedMultiplicity grading X i) *
            MvPolynomial.C (M.mayerClusterTerm X)

/-- Finite sum of all total-activity coefficients of the bigraded partition
series. -/
def bigradedTotalPartitionPolynomial
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ) :
    BivariateSourcePowerSeries.Coeff :=
  ∑ n ∈ Finset.range ((Finset.univ : Finset Q).card + 1),
    PowerSeries.coeff n (M.bigradedSourcePartitionPowerSeries grading)

/-- The four source coefficients of the finite total partition polynomial. -/
def bigradedVacuumPartitionCoefficient
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ) : ℂ :=
  MvPolynomial.constantCoeff (M.bigradedTotalPartitionPolynomial grading)

def bigradedFirstPartitionCoefficient
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ) : ℂ :=
  MvPolynomial.constantCoeff
    (MvPolynomial.pderiv 0 (M.bigradedTotalPartitionPolynomial grading))

def bigradedSecondPartitionCoefficient
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ) : ℂ :=
  MvPolynomial.constantCoeff
    (MvPolynomial.pderiv 1 (M.bigradedTotalPartitionPolynomial grading))

def bigradedMixedPartitionCoefficient
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ) : ℂ :=
  MvPolynomial.constantCoeff
    (MvPolynomial.pderiv 0
      (MvPolynomial.pderiv 1 (M.bigradedTotalPartitionPolynomial grading)))

@[simp]
theorem constantCoeff_bigradedSourceMayerPowerSeries
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ) :
    PowerSeries.constantCoeff (M.bigradedSourceMayerPowerSeries grading) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [bigradedSourceMayerPowerSeries]

/-- Mixed connected Mayer coefficient at fixed total degree. -/
def bigradedMixedMayerDegreeSum
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (n : ℕ) : ℂ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
    if bigradedMultiplicity grading X 0 = 1 ∧
        bigradedMultiplicity grading X 1 = 1 then
      M.mayerClusterTerm X else 0

/-- Connected coefficient linear in the first source and constant in the
second. -/
def bigradedFirstLinearMayerDegreeSum
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (n : ℕ) : ℂ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
    if bigradedMultiplicity grading X 0 = 1 ∧
        bigradedMultiplicity grading X 1 = 0 then
      M.mayerClusterTerm X else 0

/-- Connected coefficient constant in the first source and linear in the
second. -/
def bigradedSecondLinearMayerDegreeSum
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (n : ℕ) : ℂ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
    if bigradedMultiplicity grading X 0 = 0 ∧
        bigradedMultiplicity grading X 1 = 1 then
      M.mayerClusterTerm X else 0

/-- Absolute mixed-sector sum before cancellation at fixed total degree. -/
def bigradedMixedNormDegreeSum
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (n : ℕ) : ℝ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
    if bigradedMultiplicity grading X 0 = 1 ∧
        bigradedMultiplicity grading X 1 = 1 then
      ‖M.mayerClusterTerm X‖ else 0

/-- Absolute mixed-sector sum with an exponential natural-weight tilt. -/
def bigradedMixedWeightedNormDegreeSum
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (weight : Q → ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
    if bigradedMultiplicity grading X 0 = 1 ∧
        bigradedMultiplicity grading X 1 = 1 then
      t ^ weightedMultiplicity weight X * ‖M.mayerClusterTerm X‖ else 0

/-- The absolute mixed-sector sum dominates the norm of the connected mixed
coefficient at each fixed total degree. -/
theorem norm_bigradedMixedMayerDegreeSum_le_bigradedMixedNormDegreeSum
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ) (n : ℕ) :
    ‖M.bigradedMixedMayerDegreeSum grading n‖ ≤
      M.bigradedMixedNormDegreeSum grading n := by
  classical
  unfold bigradedMixedMayerDegreeSum bigradedMixedNormDegreeSum
  calc
    ‖∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
        if bigradedMultiplicity grading X 0 = 1 ∧
            bigradedMultiplicity grading X 1 = 1 then
          M.mayerClusterTerm X else 0‖ ≤
      ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
        ‖if bigradedMultiplicity grading X 0 = 1 ∧
            bigradedMultiplicity grading X 1 = 1 then
          M.mayerClusterTerm X else 0‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro X _
      split_ifs <;> simp

/-- A mixed absolute sector can be pinned at its first source coordinate.
The grading multiplicity is retained explicitly, so the estimate applies to
ordinary left/right roots and to polymers carrying both source degrees. -/
theorem bigradedMixedNormDegreeSum_le_sum_firstGrading_pinnedMayerTreeDegreeSum
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ) (n : ℕ) :
    M.bigradedMixedNormDegreeSum grading n ≤
      ∑ q : Q, (grading q 0 : ℝ) * M.pinnedMayerTreeDegreeSum q n := by
  classical
  unfold bigradedMixedNormDegreeSum
  calc
    (∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
        if bigradedMultiplicity grading X 0 = 1 ∧
            bigradedMultiplicity grading X 1 = 1 then
          ‖M.mayerClusterTerm X‖ else 0) ≤
      ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
        if bigradedMultiplicity grading X 0 = 1 ∧
            bigradedMultiplicity grading X 1 = 1 then
          M.mayerTreeMajorant X else 0 := by
      apply Finset.sum_le_sum
      intro X _
      split_ifs
      · exact M.norm_mayerClusterTerm_le_mayerTreeMajorant X
      · exact le_rfl
    _ ≤ ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
        (∑ q : Q, (grading q 0 : ℝ) * (X q : ℝ)) *
          M.mayerTreeMajorant X := by
      apply Finset.sum_le_sum
      intro X _
      by_cases hdegree : bigradedMultiplicity grading X 0 = 1 ∧
          bigradedMultiplicity grading X 1 = 1
      · rw [if_pos hdegree]
        have hcast :
            (∑ q : Q, (grading q 0 : ℝ) * (X q : ℝ)) = 1 := by
          exact_mod_cast hdegree.1
        rw [hcast, one_mul]
      · rw [if_neg hdegree]
        exact mul_nonneg
          (Finset.sum_nonneg fun q _ ↦
            mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (by
            unfold mayerTreeMajorant
            positivity)
    _ = ∑ q : Q, (grading q 0 : ℝ) *
        M.pinnedMayerTreeDegreeSum q n := by
      simp only [pinnedMayerTreeDegreeSum, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro X _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _
      ring

theorem bigradedMixedNormDegreeSum_le_scaled
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (alpha : Fin 2 → ℂ) (halpha0 : alpha 0 ≠ 0)
    (halpha1 : alpha 1 ≠ 0) (n : ℕ) :
    M.bigradedMixedNormDegreeSum grading n ≤
      (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
        (M.scaleByBigradedSource grading alpha).normMayerDegreeSum n := by
  classical
  unfold bigradedMixedNormDegreeSum normMayerDegreeSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro X _
  by_cases hdegree : bigradedMultiplicity grading X 0 = 1 ∧
      bigradedMultiplicity grading X 1 = 1
  · rw [if_pos hdegree]
    have hscale := M.mayerClusterTerm_scaleByBigradedSource grading alpha X
    have hscale' :
        (M.scaleByBigradedSource grading alpha).mayerClusterTerm X =
          (alpha 0 * alpha 1) * M.mayerClusterTerm X := by
      simpa [Fin.prod_univ_two, hdegree] using hscale
    rw [hscale', norm_mul, norm_mul]
    have hnorm0 : ‖alpha 0‖ ≠ 0 := norm_ne_zero_iff.mpr halpha0
    have hnorm1 : ‖alpha 1‖ ≠ 0 := norm_ne_zero_iff.mpr halpha1
    exact le_of_eq (by field_simp)
  · rw [if_neg hdegree]
    positivity

/-- Source rescaling can be restricted to the mixed sector itself.  This
sharper form is what permits the mixed coefficient to be pinned only at
source polymers, avoiding the volume-sized bulk Mayer majorant. -/
theorem bigradedMixedNormDegreeSum_le_scaled_mixed
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (alpha : Fin 2 → ℂ) (halpha0 : alpha 0 ≠ 0)
    (halpha1 : alpha 1 ≠ 0) (n : ℕ) :
    M.bigradedMixedNormDegreeSum grading n ≤
      (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
        (M.scaleByBigradedSource grading alpha).bigradedMixedNormDegreeSum
          grading n := by
  classical
  unfold bigradedMixedNormDegreeSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro X _
  by_cases hdegree : bigradedMultiplicity grading X 0 = 1 ∧
      bigradedMultiplicity grading X 1 = 1
  · rw [if_pos hdegree, if_pos hdegree]
    have hscale := M.mayerClusterTerm_scaleByBigradedSource grading alpha X
    have hscale' :
        (M.scaleByBigradedSource grading alpha).mayerClusterTerm X =
          (alpha 0 * alpha 1) * M.mayerClusterTerm X := by
      simpa [Fin.prod_univ_two, hdegree] using hscale
    rw [hscale', norm_mul, norm_mul]
    have hnorm0 : ‖alpha 0‖ ≠ 0 := norm_ne_zero_iff.mpr halpha0
    have hnorm1 : ‖alpha 1‖ ≠ 0 := norm_ne_zero_iff.mpr halpha1
    exact le_of_eq (by field_simp)
  · simp [hdegree]

theorem bigradedMixedWeightedNormDegreeSum_eq_scaleByNatWeight
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (weight : Q → ℕ) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    M.bigradedMixedWeightedNormDegreeSum grading weight t n =
      (M.scaleByNatWeight weight (t : ℂ)).bigradedMixedNormDegreeSum
        grading n := by
  classical
  unfold bigradedMixedWeightedNormDegreeSum bigradedMixedNormDegreeSum
  apply Finset.sum_congr rfl
  intro X _
  by_cases hdegree : bigradedMultiplicity grading X 0 = 1 ∧
      bigradedMultiplicity grading X 1 = 1
  · rw [if_pos hdegree, if_pos hdegree,
      mayerClusterTerm_scaleByNatWeight, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  · simp [hdegree]

theorem norm_bigradedFirstLinearMayerDegreeSum_le_scaled
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (alpha : Fin 2 → ℂ) (halpha0 : alpha 0 ≠ 0) (n : ℕ) :
    ‖M.bigradedFirstLinearMayerDegreeSum grading n‖ ≤
      ‖alpha 0‖⁻¹ *
        (M.scaleByBigradedSource grading alpha).normMayerDegreeSum n := by
  classical
  let Malpha := M.scaleByBigradedSource grading alpha
  unfold bigradedFirstLinearMayerDegreeSum normMayerDegreeSum
  calc
    ‖∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
        if bigradedMultiplicity grading X 0 = 1 ∧
            bigradedMultiplicity grading X 1 = 0 then
          M.mayerClusterTerm X else 0‖ ≤
      ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
        ‖if bigradedMultiplicity grading X 0 = 1 ∧
            bigradedMultiplicity grading X 1 = 0 then
          M.mayerClusterTerm X else 0‖ := norm_sum_le _ _
    _ ≤ ‖alpha 0‖⁻¹ *
        ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
          ‖Malpha.mayerClusterTerm X‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro X _
      by_cases hdegree : bigradedMultiplicity grading X 0 = 1 ∧
          bigradedMultiplicity grading X 1 = 0
      · rw [if_pos hdegree]
        have hscale := M.mayerClusterTerm_scaleByBigradedSource grading alpha X
        have hscale' : Malpha.mayerClusterTerm X =
            alpha 0 * M.mayerClusterTerm X := by
          simpa [Malpha, Fin.prod_univ_two, hdegree] using hscale
        rw [hscale', norm_mul]
        have hnorm : ‖alpha 0‖ ≠ 0 := norm_ne_zero_iff.mpr halpha0
        exact le_of_eq (by field_simp)
      · rw [if_neg hdegree, norm_zero]
        positivity

theorem norm_bigradedSecondLinearMayerDegreeSum_le_scaled
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (alpha : Fin 2 → ℂ) (halpha1 : alpha 1 ≠ 0) (n : ℕ) :
    ‖M.bigradedSecondLinearMayerDegreeSum grading n‖ ≤
      ‖alpha 1‖⁻¹ *
        (M.scaleByBigradedSource grading alpha).normMayerDegreeSum n := by
  classical
  let Malpha := M.scaleByBigradedSource grading alpha
  unfold bigradedSecondLinearMayerDegreeSum normMayerDegreeSum
  calc
    ‖∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
        if bigradedMultiplicity grading X 0 = 0 ∧
            bigradedMultiplicity grading X 1 = 1 then
          M.mayerClusterTerm X else 0‖ ≤
      ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
        ‖if bigradedMultiplicity grading X 0 = 0 ∧
            bigradedMultiplicity grading X 1 = 1 then
          M.mayerClusterTerm X else 0‖ := norm_sum_le _ _
    _ ≤ ‖alpha 1‖⁻¹ *
        ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
          ‖Malpha.mayerClusterTerm X‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro X _
      by_cases hdegree : bigradedMultiplicity grading X 0 = 0 ∧
          bigradedMultiplicity grading X 1 = 1
      · rw [if_pos hdegree]
        have hscale := M.mayerClusterTerm_scaleByBigradedSource grading alpha X
        have hscale' : Malpha.mayerClusterTerm X =
            alpha 1 * M.mayerClusterTerm X := by
          simpa [Malpha, Fin.prod_univ_two, hdegree] using hscale
        rw [hscale', norm_mul]
        have hnorm : ‖alpha 1‖ ≠ 0 := norm_ne_zero_iff.mpr halpha1
        exact le_of_eq (by field_simp)
      · rw [if_neg hdegree, norm_zero]
        positivity

/-- A mixed bidegree-one sector at unit source is dominated by the full Mayer
majorant after any nonzero rescaling of both sources. -/
theorem norm_bigradedMixedMayerDegreeSum_le_scaled
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (alpha : Fin 2 → ℂ) (halpha0 : alpha 0 ≠ 0)
    (halpha1 : alpha 1 ≠ 0) (n : ℕ) :
    ‖M.bigradedMixedMayerDegreeSum grading n‖ ≤
      (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
        (M.scaleByBigradedSource grading alpha).normMayerDegreeSum n := by
  classical
  let Malpha := M.scaleByBigradedSource grading alpha
  unfold bigradedMixedMayerDegreeSum normMayerDegreeSum
  calc
    ‖∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
        if bigradedMultiplicity grading X 0 = 1 ∧
            bigradedMultiplicity grading X 1 = 1 then
          M.mayerClusterTerm X else 0‖ ≤
      ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
        ‖if bigradedMultiplicity grading X 0 = 1 ∧
            bigradedMultiplicity grading X 1 = 1 then
          M.mayerClusterTerm X else 0‖ := norm_sum_le _ _
    _ ≤ (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
        ∑ X ∈ mayerMultiIndicesOfDegree (P := Q) n,
          ‖Malpha.mayerClusterTerm X‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro X _
      by_cases hdegree : bigradedMultiplicity grading X 0 = 1 ∧
          bigradedMultiplicity grading X 1 = 1
      · rw [if_pos hdegree]
        have hscale := M.mayerClusterTerm_scaleByBigradedSource
          grading alpha X
        have hscale' : Malpha.mayerClusterTerm X =
            (alpha 0 * alpha 1) * M.mayerClusterTerm X := by
          simpa [Malpha, Fin.prod_univ_two, hdegree] using hscale
        rw [hscale', norm_mul, norm_mul]
        have hnorm0 : ‖alpha 0‖ ≠ 0 := norm_ne_zero_iff.mpr halpha0
        have hnorm1 : ‖alpha 1‖ ≠ 0 := norm_ne_zero_iff.mpr halpha1
        exact le_of_eq (by field_simp)
      · rw [if_neg hdegree, norm_zero]
        positivity

/-- Absolute summability of the mixed unit-source sector transfers from a
nonzero source scaling whose full Mayer majorant is summable. -/
theorem summable_norm_bigradedMixedMayerDegreeSum_succ_of_scaled
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (alpha : Fin 2 → ℂ) (halpha0 : alpha 0 ≠ 0)
    (halpha1 : alpha 1 ≠ 0)
    (hscaled : Summable (fun n : ℕ ↦
      (M.scaleByBigradedSource grading alpha).normMayerDegreeSum (n + 1))) :
    Summable (fun n : ℕ ↦
      ‖M.bigradedMixedMayerDegreeSum grading (n + 1)‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => M.norm_bigradedMixedMayerDegreeSum_le_scaled
      grading alpha halpha0 halpha1 (n + 1))
    (hscaled.mul_left (‖alpha 0‖ * ‖alpha 1‖)⁻¹)

theorem summable_norm_bigradedFirstLinearMayerDegreeSum_succ_of_scaled
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (alpha : Fin 2 → ℂ) (halpha0 : alpha 0 ≠ 0)
    (hscaled : Summable (fun n : ℕ ↦
      (M.scaleByBigradedSource grading alpha).normMayerDegreeSum (n + 1))) :
    Summable (fun n : ℕ ↦
      ‖M.bigradedFirstLinearMayerDegreeSum grading (n + 1)‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => M.norm_bigradedFirstLinearMayerDegreeSum_le_scaled
      grading alpha halpha0 (n + 1))
    (hscaled.mul_left ‖alpha 0‖⁻¹)

theorem summable_norm_bigradedSecondLinearMayerDegreeSum_succ_of_scaled
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (alpha : Fin 2 → ℂ) (halpha1 : alpha 1 ≠ 0)
    (hscaled : Summable (fun n : ℕ ↦
      (M.scaleByBigradedSource grading alpha).normMayerDegreeSum (n + 1))) :
    Summable (fun n : ℕ ↦
      ‖M.bigradedSecondLinearMayerDegreeSum grading (n + 1)‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => M.norm_bigradedSecondLinearMayerDegreeSum_le_scaled
      grading alpha halpha1 (n + 1))
    (hscaled.mul_left ‖alpha 1‖⁻¹)

/-- Evaluating the partition sources gives the scaled ordinary partition
series. -/
theorem map_bigradedSourcePartitionPowerSeries_eval
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (alpha : Fin 2 → ℂ) :
    (M.bigradedSourcePartitionPowerSeries grading).map
        (MvPolynomial.eval alpha) =
      (M.scaleByBigradedSource grading alpha).partitionPowerSeries
        Finset.univ := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map, coeff_partitionPowerSeries]
  simp only [bigradedSourcePartitionPowerSeries, PowerSeries.coeff_mk]
  unfold partitionDegreeCoefficient
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro Gamma _
  exact M.eval_bigradedSourceFamilyWeight grading alpha Gamma

/-- Evaluation of the finite total partition polynomial is the partition
function of the source-scaled gas. -/
theorem eval_bigradedTotalPartitionPolynomial
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (alpha : Fin 2 → ℂ) :
    MvPolynomial.eval alpha (M.bigradedTotalPartitionPolynomial grading) =
      (M.scaleByBigradedSource grading alpha).partitionFunction := by
  unfold bigradedTotalPartitionPolynomial
  rw [map_sum]
  have hcoeff (n : ℕ) :
      MvPolynomial.eval alpha
          (PowerSeries.coeff n (M.bigradedSourcePartitionPowerSeries grading)) =
        (M.scaleByBigradedSource grading alpha).partitionDegreeCoefficient
          Finset.univ n := by
    have hmapped := congrArg (PowerSeries.coeff n)
      (M.map_bigradedSourcePartitionPowerSeries_eval grading alpha)
    simpa only [PowerSeries.coeff_map, coeff_partitionPowerSeries] using hmapped
  calc
    _ = ∑ n ∈ Finset.range ((Finset.univ : Finset Q).card + 1),
        (M.scaleByBigradedSource grading alpha).partitionDegreeCoefficient
          Finset.univ n := by
      apply Finset.sum_congr rfl
      intro n _
      exact hcoeff n
    _ = (M.scaleByBigradedSource grading alpha).partitionOn Finset.univ :=
      sum_partitionDegreeCoefficient_range
        (M.scaleByBigradedSource grading alpha) Finset.univ
    _ = _ := rfl

/-- The bigraded partition series is supported in the finite hard-core
range. -/
theorem coeff_bigradedSourcePartitionPowerSeries_eq_zero_of_card_lt
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ) {n : ℕ}
    (hcard : (Finset.univ : Finset Q).card < n) :
    PowerSeries.coeff n (M.bigradedSourcePartitionPowerSeries grading) = 0 := by
  apply MvPolynomial.funext
  intro alpha
  have hmapped := congrArg (PowerSeries.coeff n)
    (M.map_bigradedSourcePartitionPowerSeries_eval grading alpha)
  calc
    MvPolynomial.eval alpha
        (PowerSeries.coeff n (M.bigradedSourcePartitionPowerSeries grading)) =
      PowerSeries.coeff n
        ((M.scaleByBigradedSource grading alpha).partitionPowerSeries
          Finset.univ) := by
      simpa only [PowerSeries.coeff_map] using hmapped
    _ = 0 := by
      rw [coeff_partitionPowerSeries]
      exact partitionDegreeCoefficient_eq_zero_of_card_lt
        (M.scaleByBigradedSource grading alpha) Finset.univ hcard
    _ = MvPolynomial.eval alpha 0 := by simp

/-- Evaluating the connected sources gives the scaled symmetric Mayer
series. -/
theorem map_bigradedSourceMayerPowerSeries_eval
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (alpha : Fin 2 → ℂ) :
    (M.bigradedSourceMayerPowerSeries grading).map
        (MvPolynomial.eval alpha) =
      (M.scaleByBigradedSource grading alpha).restrictedSymmetricMayerPowerSeries
        Finset.univ := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [bigradedSourceMayerPowerSeries,
        restrictedSymmetricMayerPowerSeries,
        restrictedSymmetricMayerCoefficient]
  | succ n =>
      rw [PowerSeries.coeff_map]
      simp only [bigradedSourceMayerPowerSeries, PowerSeries.coeff_mk,
        restrictedSymmetricMayerPowerSeries,
        restrictedSymmetricMayerCoefficient, map_sum, map_mul, map_prod,
        map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C]
      rw [Finset.filter_eq_self.2]
      · apply Finset.sum_congr rfl
        intro X _
        exact (M.mayerClusterTerm_scaleByBigradedSource grading alpha X).symm
      · intro X _
        exact Finset.subset_univ _

/-- Exact bigraded fixed-labelled exponential formula. -/
theorem expOf_bigradedSourceMayerPowerSeries
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ) :
    BivariateSourcePowerSeries.expOf
        (M.bigradedSourceMayerPowerSeries grading) =
      M.bigradedSourcePartitionPowerSeries grading := by
  apply PowerSeries.ext
  intro n
  apply MvPolynomial.funext
  intro alpha
  have hcomplex :
      PowerSeriesBridge.expOf
          ((M.scaleByBigradedSource grading alpha).restrictedSymmetricMayerPowerSeries
            Finset.univ) =
        (M.scaleByBigradedSource grading alpha).partitionPowerSeries
          Finset.univ := by
    rw [restrictedSymmetricMayerPowerSeries_eq_formalMayerLog
      (M.scaleByBigradedSource grading alpha) Finset.univ]
    exact expOf_formalMayerLog_eq_partitionPowerSeries
      (M.scaleByBigradedSource grading alpha) Finset.univ
  have hmapped :
      (BivariateSourcePowerSeries.expOf
          (M.bigradedSourceMayerPowerSeries grading)).map
            (MvPolynomial.eval alpha) =
        (M.bigradedSourcePartitionPowerSeries grading).map
          (MvPolynomial.eval alpha) := by
    rw [BivariateSourcePowerSeries.map_expOf_eval _
      (M.constantCoeff_bigradedSourceMayerPowerSeries grading) alpha,
      M.map_bigradedSourceMayerPowerSeries_eval grading alpha,
      M.map_bigradedSourcePartitionPowerSeries_eval grading alpha]
    exact hcomplex
  exact congrArg (PowerSeries.coeff n) hmapped

/-- First-source extraction selects total bidegree `(1,0)`. -/
theorem coeff_linearCoefficient_first_bigradedSourceMayerPowerSeries
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (n : ℕ) :
    PowerSeries.coeff n
        (BivariateSourcePowerSeries.linearCoefficient 0
          (M.bigradedSourceMayerPowerSeries grading)) =
      M.bigradedFirstLinearMayerDegreeSum grading n := by
  unfold BivariateSourcePowerSeries.linearCoefficient
    BivariateSourcePowerSeries.constantSource
  rw [PowerSeries.coeff_map,
    BivariateSourcePowerSeries.coeff_sourceDerivative]
  cases n with
  | zero =>
      unfold bigradedFirstLinearMayerDegreeSum
      simp only [bigradedSourceMayerPowerSeries, PowerSeries.coeff_mk,
        map_zero]
      symm
      apply Finset.sum_eq_zero
      intro X hX
      have hdegree : mayerDegree X = 0 :=
        (mem_mayerMultiIndicesOfDegree 0 X).mp hX
      have hx : ∀ q : Q, X q = 0 := by
        intro q
        unfold mayerDegree at hdegree
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => Nat.zero_le _)).mp hdegree q (Finset.mem_univ q)
      simp [bigradedMultiplicity, hx]
  | succ n =>
      simp only [bigradedSourceMayerPowerSeries, PowerSeries.coeff_mk,
        map_sum, Fin.prod_univ_two]
      unfold bigradedFirstLinearMayerDegreeSum
      apply Finset.sum_congr rfl
      intro X _
      exact BivariateSourcePowerSeries.constantCoeff_pderiv_first_twoVariableMonomial
        (bigradedMultiplicity grading X 0)
        (bigradedMultiplicity grading X 1) (M.mayerClusterTerm X)

/-- Second-source extraction selects total bidegree `(0,1)`. -/
theorem coeff_linearCoefficient_second_bigradedSourceMayerPowerSeries
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (n : ℕ) :
    PowerSeries.coeff n
        (BivariateSourcePowerSeries.linearCoefficient 1
          (M.bigradedSourceMayerPowerSeries grading)) =
      M.bigradedSecondLinearMayerDegreeSum grading n := by
  unfold BivariateSourcePowerSeries.linearCoefficient
    BivariateSourcePowerSeries.constantSource
  rw [PowerSeries.coeff_map,
    BivariateSourcePowerSeries.coeff_sourceDerivative]
  cases n with
  | zero =>
      unfold bigradedSecondLinearMayerDegreeSum
      simp only [bigradedSourceMayerPowerSeries, PowerSeries.coeff_mk,
        map_zero]
      symm
      apply Finset.sum_eq_zero
      intro X hX
      have hdegree : mayerDegree X = 0 :=
        (mem_mayerMultiIndicesOfDegree 0 X).mp hX
      have hx : ∀ q : Q, X q = 0 := by
        intro q
        unfold mayerDegree at hdegree
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => Nat.zero_le _)).mp hdegree q (Finset.mem_univ q)
      simp [bigradedMultiplicity, hx]
  | succ n =>
      simp only [bigradedSourceMayerPowerSeries, PowerSeries.coeff_mk,
        map_sum, Fin.prod_univ_two]
      unfold bigradedSecondLinearMayerDegreeSum
      apply Finset.sum_congr rfl
      intro X _
      exact BivariateSourcePowerSeries.constantCoeff_pderiv_second_twoVariableMonomial
        (bigradedMultiplicity grading X 0)
        (bigradedMultiplicity grading X 1) (M.mayerClusterTerm X)

/-- Mixed source extraction selects total bidegree `(1,1)`. -/
theorem coeff_mixedCoefficient_bigradedSourceMayerPowerSeries
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (n : ℕ) :
    PowerSeries.coeff n
        (BivariateSourcePowerSeries.mixedCoefficient
          (M.bigradedSourceMayerPowerSeries grading)) =
      M.bigradedMixedMayerDegreeSum grading n := by
  unfold BivariateSourcePowerSeries.mixedCoefficient
    BivariateSourcePowerSeries.constantSource
  rw [PowerSeries.coeff_map,
    BivariateSourcePowerSeries.coeff_sourceDerivative,
    BivariateSourcePowerSeries.coeff_sourceDerivative]
  cases n with
  | zero =>
      unfold bigradedMixedMayerDegreeSum
      simp only [bigradedSourceMayerPowerSeries, PowerSeries.coeff_mk,
        map_zero]
      symm
      apply Finset.sum_eq_zero
      intro X hX
      have hdegree : mayerDegree X = 0 :=
        (mem_mayerMultiIndicesOfDegree 0 X).mp hX
      have hx : ∀ q : Q, X q = 0 := by
        intro q
        unfold mayerDegree at hdegree
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => Nat.zero_le _)).mp hdegree q (Finset.mem_univ q)
      simp [bigradedMultiplicity, hx]
  | succ n =>
      simp only [bigradedSourceMayerPowerSeries, PowerSeries.coeff_mk,
        map_sum, Fin.prod_univ_two]
      unfold bigradedMixedMayerDegreeSum
      apply Finset.sum_congr rfl
      intro X _
      exact BivariateSourcePowerSeries.constantCoeff_pderiv_pderiv_twoVariableMonomial
        (bigradedMultiplicity grading X 0)
        (bigradedMultiplicity grading X 1) (M.mayerClusterTerm X)

/-- The mixed bigraded partition coefficient satisfies the pointed
exponential identity. -/
theorem mixedCoefficient_bigradedSourcePartitionPowerSeries
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ) :
    BivariateSourcePowerSeries.mixedCoefficient
        (M.bigradedSourcePartitionPowerSeries grading) =
      BivariateSourcePowerSeries.constantSource
          (M.bigradedSourcePartitionPowerSeries grading) *
        (BivariateSourcePowerSeries.mixedCoefficient
            (M.bigradedSourceMayerPowerSeries grading) +
          BivariateSourcePowerSeries.linearCoefficient 0
              (M.bigradedSourceMayerPowerSeries grading) *
            BivariateSourcePowerSeries.linearCoefficient 1
              (M.bigradedSourceMayerPowerSeries grading)) := by
  rw [← M.expOf_bigradedSourceMayerPowerSeries grading]
  exact BivariateSourcePowerSeries.mixedCoefficient_expOf
    (M.constantCoeff_bigradedSourceMayerPowerSeries grading)

/-- The coefficient linear in either source satisfies the one-pointed
exponential identity. -/
theorem linearCoefficient_bigradedSourcePartitionPowerSeries
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (i : Fin 2) :
    BivariateSourcePowerSeries.linearCoefficient i
        (M.bigradedSourcePartitionPowerSeries grading) =
      BivariateSourcePowerSeries.constantSource
          (M.bigradedSourcePartitionPowerSeries grading) *
        BivariateSourcePowerSeries.linearCoefficient i
          (M.bigradedSourceMayerPowerSeries grading) := by
  rw [← M.expOf_bigradedSourceMayerPowerSeries grading]
  unfold BivariateSourcePowerSeries.linearCoefficient
  rw [BivariateSourcePowerSeries.sourceDerivative_expOf
    (M.constantCoeff_bigradedSourceMayerPowerSeries grading) i]
  unfold BivariateSourcePowerSeries.constantSource
  rw [map_mul]

/-! ## Evaluation at unit total activity -/

/-- Absolute convergence of the three connected source sectors evaluates the
formal pointed identities at unit total activity. -/
theorem bigradedPartitionCoefficients_eq_connected
    (M : FinitePolymerModel Q) (grading : Q → Fin 2 → ℕ)
    (hfirst : Summable (fun n : ℕ ↦
      ‖M.bigradedFirstLinearMayerDegreeSum grading (n + 1)‖))
    (hsecond : Summable (fun n : ℕ ↦
      ‖M.bigradedSecondLinearMayerDegreeSum grading (n + 1)‖))
    (hmixed : Summable (fun n : ℕ ↦
      ‖M.bigradedMixedMayerDegreeSum grading (n + 1)‖)) :
    M.bigradedFirstPartitionCoefficient grading =
        M.bigradedVacuumPartitionCoefficient grading *
          ∑' n : ℕ, M.bigradedFirstLinearMayerDegreeSum grading n ∧
      M.bigradedSecondPartitionCoefficient grading =
        M.bigradedVacuumPartitionCoefficient grading *
          ∑' n : ℕ, M.bigradedSecondLinearMayerDegreeSum grading n ∧
      M.bigradedMixedPartitionCoefficient grading =
        M.bigradedVacuumPartitionCoefficient grading *
          ((∑' n : ℕ, M.bigradedMixedMayerDegreeSum grading n) +
            (∑' n : ℕ, M.bigradedFirstLinearMayerDegreeSum grading n) *
              ∑' n : ℕ,
                M.bigradedSecondLinearMayerDegreeSum grading n) := by
  let sourcePartition := M.bigradedSourcePartitionPowerSeries grading
  let sourceConnected := M.bigradedSourceMayerPowerSeries grading
  let B : ℕ → ℂ := fun n => PowerSeries.coeff n
    (BivariateSourcePowerSeries.constantSource sourcePartition)
  let C0 : ℕ → ℂ := fun n => PowerSeries.coeff n
    (BivariateSourcePowerSeries.linearCoefficient 0 sourceConnected)
  let C1 : ℕ → ℂ := fun n => PowerSeries.coeff n
    (BivariateSourcePowerSeries.linearCoefficient 1 sourceConnected)
  let C01 : ℕ → ℂ := fun n => PowerSeries.coeff n
    (BivariateSourcePowerSeries.mixedCoefficient sourceConnected)
  let Conv : ℕ → ℂ := fun n =>
    ∑ pair ∈ Finset.antidiagonal n, C0 pair.1 * C1 pair.2
  let D : ℕ → ℂ := fun n => C01 n + Conv n
  let R0 : ℕ → ℂ := fun n => PowerSeries.coeff n
    (BivariateSourcePowerSeries.linearCoefficient 0 sourcePartition)
  let R1 : ℕ → ℂ := fun n => PowerSeries.coeff n
    (BivariateSourcePowerSeries.linearCoefficient 1 sourcePartition)
  let Rmix : ℕ → ℂ := fun n => PowerSeries.coeff n
    (BivariateSourcePowerSeries.mixedCoefficient sourcePartition)
  let cutoff := (Finset.univ : Finset Q).card + 1
  have hsourceZero {n : ℕ} (hn : n ∉ Finset.range cutoff) :
      PowerSeries.coeff n sourcePartition = 0 := by
    apply M.coeff_bigradedSourcePartitionPowerSeries_eq_zero_of_card_lt grading
    exact Nat.lt_of_not_ge fun hle =>
      hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
  have hBzero {n : ℕ} (hn : n ∉ Finset.range cutoff) : B n = 0 := by
    unfold B BivariateSourcePowerSeries.constantSource
    rw [PowerSeries.coeff_map, hsourceZero hn, map_zero]
  have hR0zero {n : ℕ} (hn : n ∉ Finset.range cutoff) : R0 n = 0 := by
    unfold R0 BivariateSourcePowerSeries.linearCoefficient
      BivariateSourcePowerSeries.constantSource
    rw [PowerSeries.coeff_map,
      BivariateSourcePowerSeries.coeff_sourceDerivative, hsourceZero hn]
    simp
  have hR1zero {n : ℕ} (hn : n ∉ Finset.range cutoff) : R1 n = 0 := by
    unfold R1 BivariateSourcePowerSeries.linearCoefficient
      BivariateSourcePowerSeries.constantSource
    rw [PowerSeries.coeff_map,
      BivariateSourcePowerSeries.coeff_sourceDerivative, hsourceZero hn]
    simp
  have hRmixzero {n : ℕ} (hn : n ∉ Finset.range cutoff) : Rmix n = 0 := by
    unfold Rmix BivariateSourcePowerSeries.mixedCoefficient
      BivariateSourcePowerSeries.constantSource
    rw [PowerSeries.coeff_map,
      BivariateSourcePowerSeries.coeff_sourceDerivative,
      BivariateSourcePowerSeries.coeff_sourceDerivative, hsourceZero hn]
    simp
  have hBnorm : Summable (fun n => ‖B n‖) :=
    summable_of_ne_finset_zero (s := Finset.range cutoff) fun n hn => by
      rw [hBzero hn, norm_zero]
  have hC0norm : Summable (fun n => ‖C0 n‖) := by
    have htail : Summable (fun n => ‖C0 (n + 1)‖) := by
      apply hfirst.congr
      intro n
      unfold C0 sourceConnected
      rw [M.coeff_linearCoefficient_first_bigradedSourceMayerPowerSeries grading]
    exact (summable_nat_add_iff (f := fun n => ‖C0 n‖) 1).mp htail
  have hC1norm : Summable (fun n => ‖C1 n‖) := by
    have htail : Summable (fun n => ‖C1 (n + 1)‖) := by
      apply hsecond.congr
      intro n
      unfold C1 sourceConnected
      rw [M.coeff_linearCoefficient_second_bigradedSourceMayerPowerSeries grading]
    exact (summable_nat_add_iff (f := fun n => ‖C1 n‖) 1).mp htail
  have hC01norm : Summable (fun n => ‖C01 n‖) := by
    have htail : Summable (fun n => ‖C01 (n + 1)‖) := by
      apply hmixed.congr
      intro n
      unfold C01 sourceConnected
      rw [M.coeff_mixedCoefficient_bigradedSourceMayerPowerSeries grading]
    exact (summable_nat_add_iff (f := fun n => ‖C01 n‖) 1).mp htail
  have hConvNorm : Summable (fun n => ‖Conv n‖) :=
    summable_norm_sum_mul_antidiagonal_of_summable_norm hC0norm hC1norm
  have hDnorm : Summable (fun n => ‖D n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_add_le (C01 n) (Conv n)) (hC01norm.add hConvNorm)
  have hBsum : HasSum B (M.bigradedVacuumPartitionCoefficient grading) := by
    have hfinite : HasSum B (∑ n ∈ Finset.range cutoff, B n) :=
      hasSum_sum_of_ne_finset_zero
        (s := Finset.range cutoff) (fun n hn => hBzero hn)
    simpa [bigradedVacuumPartitionCoefficient,
      bigradedTotalPartitionPolynomial, B, sourcePartition, cutoff,
      BivariateSourcePowerSeries.constantSource, map_sum] using hfinite
  have hR0sum : HasSum R0 (M.bigradedFirstPartitionCoefficient grading) := by
    have hfinite : HasSum R0 (∑ n ∈ Finset.range cutoff, R0 n) :=
      hasSum_sum_of_ne_finset_zero
        (s := Finset.range cutoff) (fun n hn => hR0zero hn)
    simpa [bigradedFirstPartitionCoefficient,
      bigradedTotalPartitionPolynomial, R0, sourcePartition, cutoff,
      BivariateSourcePowerSeries.linearCoefficient,
      BivariateSourcePowerSeries.constantSource, map_sum] using hfinite
  have hR1sum : HasSum R1 (M.bigradedSecondPartitionCoefficient grading) := by
    have hfinite : HasSum R1 (∑ n ∈ Finset.range cutoff, R1 n) :=
      hasSum_sum_of_ne_finset_zero
        (s := Finset.range cutoff) (fun n hn => hR1zero hn)
    simpa [bigradedSecondPartitionCoefficient,
      bigradedTotalPartitionPolynomial, R1, sourcePartition, cutoff,
      BivariateSourcePowerSeries.linearCoefficient,
      BivariateSourcePowerSeries.constantSource, map_sum] using hfinite
  have hRmixsum : HasSum Rmix (M.bigradedMixedPartitionCoefficient grading) := by
    have hfinite : HasSum Rmix (∑ n ∈ Finset.range cutoff, Rmix n) :=
      hasSum_sum_of_ne_finset_zero
        (s := Finset.range cutoff) (fun n hn => hRmixzero hn)
    simpa [bigradedMixedPartitionCoefficient,
      bigradedTotalPartitionPolynomial, Rmix, sourcePartition, cutoff,
      BivariateSourcePowerSeries.mixedCoefficient,
      BivariateSourcePowerSeries.constantSource, map_sum] using hfinite
  have hpoint0 :
      BivariateSourcePowerSeries.linearCoefficient 0 sourcePartition =
        BivariateSourcePowerSeries.constantSource sourcePartition *
          BivariateSourcePowerSeries.linearCoefficient 0 sourceConnected :=
    M.linearCoefficient_bigradedSourcePartitionPowerSeries grading 0
  have hpoint1 :
      BivariateSourcePowerSeries.linearCoefficient 1 sourcePartition =
        BivariateSourcePowerSeries.constantSource sourcePartition *
          BivariateSourcePowerSeries.linearCoefficient 1 sourceConnected :=
    M.linearCoefficient_bigradedSourcePartitionPowerSeries grading 1
  have hpointMix :
      BivariateSourcePowerSeries.mixedCoefficient sourcePartition =
        BivariateSourcePowerSeries.constantSource sourcePartition *
          (BivariateSourcePowerSeries.mixedCoefficient sourceConnected +
            BivariateSourcePowerSeries.linearCoefficient 0 sourceConnected *
              BivariateSourcePowerSeries.linearCoefficient 1 sourceConnected) :=
    M.mixedCoefficient_bigradedSourcePartitionPowerSeries grading
  have hproduct0 : (∑' n, B n) * (∑' n, C0 n) = ∑' n, R0 n := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hBnorm hC0norm]
    apply tsum_congr
    intro n
    have hcoeff := congrArg (PowerSeries.coeff n) hpoint0
    simpa only [B, C0, R0, PowerSeries.coeff_mul] using hcoeff.symm
  have hproduct1 : (∑' n, B n) * (∑' n, C1 n) = ∑' n, R1 n := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hBnorm hC1norm]
    apply tsum_congr
    intro n
    have hcoeff := congrArg (PowerSeries.coeff n) hpoint1
    simpa only [B, C1, R1, PowerSeries.coeff_mul] using hcoeff.symm
  have hDcoeff (n : ℕ) : PowerSeries.coeff n
      (BivariateSourcePowerSeries.mixedCoefficient sourceConnected +
        BivariateSourcePowerSeries.linearCoefficient 0 sourceConnected *
          BivariateSourcePowerSeries.linearCoefficient 1 sourceConnected) = D n := by
    simp only [map_add, PowerSeries.coeff_mul]
    rfl
  have hproductMix : (∑' n, B n) * (∑' n, D n) = ∑' n, Rmix n := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hBnorm hDnorm]
    apply tsum_congr
    intro n
    have hcoeff := congrArg (PowerSeries.coeff n) hpointMix
    rw [PowerSeries.coeff_mul] at hcoeff
    simpa only [B, Rmix, hDcoeff] using hcoeff.symm
  have hConvSum : (∑' n, C0 n) * (∑' n, C1 n) = ∑' n, Conv n :=
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hC0norm hC1norm
  have hDsum : ∑' n, D n = (∑' n, C01 n) +
      (∑' n, C0 n) * (∑' n, C1 n) := by
    rw [show (∑' n, D n) = (∑' n, C01 n) + ∑' n, Conv n by
      exact Summable.tsum_add hC01norm.of_norm hConvNorm.of_norm]
    rw [← hConvSum]
  have hfirstResult : M.bigradedFirstPartitionCoefficient grading =
      M.bigradedVacuumPartitionCoefficient grading *
        ∑' n, M.bigradedFirstLinearMayerDegreeSum grading n := by
    calc
      _ = ∑' n, R0 n := hR0sum.tsum_eq.symm
      _ = (∑' n, B n) * (∑' n, C0 n) := hproduct0.symm
      _ = _ := by
        rw [hBsum.tsum_eq]
        congr 1
        apply tsum_congr
        intro n
        exact M.coeff_linearCoefficient_first_bigradedSourceMayerPowerSeries
          grading n
  have hsecondResult : M.bigradedSecondPartitionCoefficient grading =
      M.bigradedVacuumPartitionCoefficient grading *
        ∑' n, M.bigradedSecondLinearMayerDegreeSum grading n := by
    calc
      _ = ∑' n, R1 n := hR1sum.tsum_eq.symm
      _ = (∑' n, B n) * (∑' n, C1 n) := hproduct1.symm
      _ = _ := by
        rw [hBsum.tsum_eq]
        congr 1
        apply tsum_congr
        intro n
        exact M.coeff_linearCoefficient_second_bigradedSourceMayerPowerSeries
          grading n
  refine ⟨hfirstResult, hsecondResult, ?_⟩
  calc
    _ = ∑' n, Rmix n := hRmixsum.tsum_eq.symm
    _ = (∑' n, B n) * (∑' n, D n) := hproductMix.symm
    _ = M.bigradedVacuumPartitionCoefficient grading *
        ((∑' n, C01 n) + (∑' n, C0 n) * (∑' n, C1 n)) := by
      rw [hBsum.tsum_eq, hDsum]
    _ = _ := by
      congr 1
      congr 1
      · apply tsum_congr
        intro n
        exact M.coeff_mixedCoefficient_bigradedSourceMayerPowerSeries grading n
      · congr 1
        · apply tsum_congr
          intro n
          exact M.coeff_linearCoefficient_first_bigradedSourceMayerPowerSeries
            grading n
        · apply tsum_congr
          intro n
          exact M.coeff_linearCoefficient_second_bigradedSourceMayerPowerSeries
            grading n

end FinitePolymerModel

end

end YangMills.Polymer
