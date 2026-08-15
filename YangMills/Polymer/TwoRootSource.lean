/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.Augmented
import YangMills.Polymer.BivariateSourcePowerSeries

/-!
# Fixed-labelled two-root source expansion

This file equips the compatible two-root augmentation with two honest
polynomial source variables.  It proves the exact fixed-labelled
exponential formula before source extraction and then extracts the mixed
pointed identity.  The two distinct roots are compatible, so a connected
mixed Mayer term must be linked through bulk polymers.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

namespace FinitePolymerModel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Multiplicity of labelled root `r` in a two-root Mayer multi-index. -/
def twoRootMultiplicity
    (X : MayerMultiIndex (AugmentedPolymer P (Fin 2))) (r : Fin 2) : ℕ :=
  X (Sum.inr r)

/-- Scaling the two root activities independently records their two
multiplicities in the activity monomial. -/
theorem mayerActivityMonomial_augmentRoots_twoSource
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ)
    (alpha : Fin 2 → ℂ)
    (X : MayerMultiIndex (AugmentedPolymer P (Fin 2))) :
    (M.augmentRoots touches
        (fun r => alpha r * rootActivity r)).mayerActivityMonomial X =
      (∏ r : Fin 2, alpha r ^ twoRootMultiplicity X r) *
        (M.augmentRoots touches rootActivity).mayerActivityMonomial X := by
  classical
  unfold mayerActivityMonomial twoRootMultiplicity
  simp only [Fintype.prod_sum_type, augmentRoots, mul_pow]
  rw [Finset.prod_mul_distrib]
  ring

/-- The independently scaled source law for normalized connected Mayer
terms. -/
theorem mayerClusterTerm_augmentRoots_twoSource
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ)
    (alpha : Fin 2 → ℂ)
    (X : MayerMultiIndex (AugmentedPolymer P (Fin 2))) :
    (M.augmentRoots touches
        (fun r => alpha r * rootActivity r)).mayerClusterTerm X =
      (∏ r : Fin 2, alpha r ^ twoRootMultiplicity X r) *
        (M.augmentRoots touches rootActivity).mayerClusterTerm X := by
  unfold mayerClusterTerm
  rw [M.mayerActivityMonomial_augmentRoots_twoSource
    touches rootActivity alpha X]
  change ((M.augmentRoots touches rootActivity).mayerUrsell X : ℂ) /
      (mayerSymmetryFactor X : ℂ) *
        ((∏ r : Fin 2, alpha r ^ twoRootMultiplicity X r) *
          (M.augmentRoots touches rootActivity).mayerActivityMonomial X) = _
  ring

/-- Polynomial activity product of a compatible family with one variable
for each of the two labelled roots. -/
def twoRootSourceFamilyWeight
    (M : FinitePolymerModel P) (rootActivity : Fin 2 → ℂ)
    (Gamma : Finset (AugmentedPolymer P (Fin 2))) :
    BivariateSourcePowerSeries.Coeff :=
  ∏ x ∈ Gamma, match x with
    | Sum.inl gamma => MvPolynomial.C (M.activity gamma)
    | Sum.inr r => MvPolynomial.X r * MvPolynomial.C (rootActivity r)

/-- Evaluation of both sources recovers the independently scaled family
weight. -/
theorem eval_twoRootSourceFamilyWeight
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ)
    (alpha : Fin 2 → ℂ)
    (Gamma : Finset (AugmentedPolymer P (Fin 2))) :
    MvPolynomial.eval alpha (M.twoRootSourceFamilyWeight rootActivity Gamma) =
      (M.augmentRoots touches
        (fun r => alpha r * rootActivity r)).familyWeight Gamma := by
  classical
  unfold twoRootSourceFamilyWeight familyWeight
  change (MvPolynomial.eval alpha)
      (∏ x ∈ Gamma, match x with
        | Sum.inl gamma => MvPolynomial.C (M.activity gamma)
        | Sum.inr r => MvPolynomial.X r * MvPolynomial.C (rootActivity r)) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  rintro (gamma | r) _
  · simp
  · simp

/-- Total-activity partition series with both root sources retained in the
coefficient ring. -/
def twoRootSourcePartitionPowerSeries
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ) :
    PowerSeries BivariateSourcePowerSeries.Coeff :=
  let A := M.augmentRoots touches rootActivity
  PowerSeries.mk fun n =>
    ∑ Gamma ∈ (A.compatibleFamilies Finset.univ).filter
        (fun Gamma => Gamma.card = n),
      M.twoRootSourceFamilyWeight rootActivity Gamma

/-- Connected total-activity series with both root sources retained. -/
def twoRootSourceMayerPowerSeries
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ) :
    PowerSeries BivariateSourcePowerSeries.Coeff :=
  PowerSeries.mk fun
    | 0 => 0
    | n + 1 =>
        ∑ X ∈ mayerMultiIndicesOfDegree
            (P := AugmentedPolymer P (Fin 2)) (n + 1),
          (∏ r : Fin 2,
              MvPolynomial.X r ^ twoRootMultiplicity X r) *
            MvPolynomial.C
              ((M.augmentRoots touches rootActivity).mayerClusterTerm X)

/-- Connected degree coefficient linear in the first root and constant in
the second. -/
def firstRootLinearMayerDegreeSum
    (A : FinitePolymerModel (AugmentedPolymer P (Fin 2))) (n : ℕ) : ℂ :=
  ∑ X ∈ mayerMultiIndicesOfDegree
      (P := AugmentedPolymer P (Fin 2)) n,
    if twoRootMultiplicity X 0 = 1 ∧ twoRootMultiplicity X 1 = 0 then
      A.mayerClusterTerm X else 0

/-- Connected degree coefficient linear in the second root and constant in
the first. -/
def secondRootLinearMayerDegreeSum
    (A : FinitePolymerModel (AugmentedPolymer P (Fin 2))) (n : ℕ) : ℂ :=
  ∑ X ∈ mayerMultiIndicesOfDegree
      (P := AugmentedPolymer P (Fin 2)) n,
    if twoRootMultiplicity X 0 = 0 ∧ twoRootMultiplicity X 1 = 1 then
      A.mayerClusterTerm X else 0

/-- Genuinely mixed connected coefficient: each labelled root occurs
exactly once. -/
def twoRootMixedMayerDegreeSum
    (A : FinitePolymerModel (AugmentedPolymer P (Fin 2))) (n : ℕ) : ℂ :=
  ∑ X ∈ mayerMultiIndicesOfDegree
      (P := AugmentedPolymer P (Fin 2)) n,
    if twoRootMultiplicity X 0 = 1 ∧ twoRootMultiplicity X 1 = 1 then
      A.mayerClusterTerm X else 0

/-! ## Symmetry-normalized two-pinned tree sector -/

/-- Adjoin one occurrence of each labelled root to a residual Mayer
multi-index.  The order is fixed only to make the inverse reindexing
literal. -/
def addTwoRootOccurrences
    (Y : MayerMultiIndex (AugmentedPolymer P (Fin 2))) :
    MayerMultiIndex (AugmentedPolymer P (Fin 2)) :=
  (Y + Finsupp.single (Sum.inr (1 : Fin 2)) 1) +
    Finsupp.single (Sum.inr (0 : Fin 2)) 1

/-- Delete the distinguished first and second root occurrences. -/
def eraseTwoRootOccurrences
    (X : MayerMultiIndex (AugmentedPolymer P (Fin 2))) :
    MayerMultiIndex (AugmentedPolymer P (Fin 2)) :=
  eraseRootOccurrence
    (eraseRootOccurrence X (Sum.inr (0 : Fin 2)))
    (Sum.inr (1 : Fin 2))

@[simp]
theorem twoRootMultiplicity_addTwoRootOccurrences_zero
    (Y : MayerMultiIndex (AugmentedPolymer P (Fin 2))) :
    twoRootMultiplicity (addTwoRootOccurrences Y) 0 =
      twoRootMultiplicity Y 0 + 1 := by
  simp [addTwoRootOccurrences, twoRootMultiplicity]

@[simp]
theorem twoRootMultiplicity_addTwoRootOccurrences_one
    (Y : MayerMultiIndex (AugmentedPolymer P (Fin 2))) :
    twoRootMultiplicity (addTwoRootOccurrences Y) 1 =
      twoRootMultiplicity Y 1 + 1 := by
  simp [addTwoRootOccurrences, twoRootMultiplicity]

/-- Adding both labelled roots raises total Mayer degree by two. -/
theorem mayerDegree_addTwoRootOccurrences
    (Y : MayerMultiIndex (AugmentedPolymer P (Fin 2))) :
    mayerDegree (addTwoRootOccurrences Y) = mayerDegree Y + 2 := by
  unfold addTwoRootOccurrences
  rw [mayerDegree_add_single, mayerDegree_add_single]

/-- Deleting and then restoring the two unique labelled root occurrences is
the identity. -/
theorem addTwoRootOccurrences_eraseTwoRootOccurrences
    (X : MayerMultiIndex (AugmentedPolymer P (Fin 2)))
    (hzero : twoRootMultiplicity X 0 = 1)
    (hone : twoRootMultiplicity X 1 = 1) :
    addTwoRootOccurrences (eraseTwoRootOccurrences X) = X := by
  let root0 : AugmentedPolymer P (Fin 2) := Sum.inr 0
  let root1 : AugmentedPolymer P (Fin 2) := Sum.inr 1
  have hx0 : X root0 = 1 := by
    simpa [root0, twoRootMultiplicity] using hzero
  have hx1 : X root1 = 1 := by
    simpa [root1, twoRootMultiplicity] using hone
  have hroot0 : X root0 ≠ 0 := by
    omega
  have hroot1 : (eraseRootOccurrence X root0) root1 ≠ 0 := by
    simp [eraseRootOccurrence, Finsupp.update_apply, root0, root1, hx1]
  have hback1 := eraseRootOccurrence_add_single_eq
    (eraseRootOccurrence X root0) root1 hroot1
  have hback0 := eraseRootOccurrence_add_single_eq X root0 hroot0
  calc
    addTwoRootOccurrences (eraseTwoRootOccurrences X) =
        (eraseRootOccurrence (eraseRootOccurrence X root0) root1 +
            Finsupp.single root1 1) + Finsupp.single root0 1 := rfl
    _ = eraseRootOccurrence X root0 + Finsupp.single root0 1 := by
      rw [hback1]
    _ = X := hback0

@[simp]
theorem twoRootMultiplicity_eraseTwoRootOccurrences_zero
    (X : MayerMultiIndex (AugmentedPolymer P (Fin 2))) :
    twoRootMultiplicity (eraseTwoRootOccurrences X) 0 =
      twoRootMultiplicity X 0 - 1 := by
  simp [eraseTwoRootOccurrences, eraseRootOccurrence,
    Finsupp.update_apply, twoRootMultiplicity]

@[simp]
theorem twoRootMultiplicity_eraseTwoRootOccurrences_one
    (X : MayerMultiIndex (AugmentedPolymer P (Fin 2))) :
    twoRootMultiplicity (eraseTwoRootOccurrences X) 1 =
      twoRootMultiplicity X 1 - 1 := by
  simp [eraseTwoRootOccurrences, eraseRootOccurrence,
    Finsupp.update_apply, twoRootMultiplicity]

/-- Tree majorant of the genuinely mixed sector at fixed total degree. -/
def twoRootMixedMayerTreeDegreeSum
    (A : FinitePolymerModel (AugmentedPolymer P (Fin 2))) (n : ℕ) : ℝ :=
  ∑ X ∈ mayerMultiIndicesOfDegree
      (P := AugmentedPolymer P (Fin 2)) n,
    if twoRootMultiplicity X 0 = 1 ∧ twoRootMultiplicity X 1 = 1 then
      A.mayerTreeMajorant X else 0

/-- The residual two-pinned tree orbit: both labelled root activities have
been removed, and only the symmetry factor of the residual bulk orbit
remains. -/
def residualSymmetricTwoPinnedTreeDegreeSum
    (A₀ : FinitePolymerModel (AugmentedPolymer P (Fin 2))) (n : ℕ) : ℝ :=
  ∑ Y ∈ mayerMultiIndicesOfDegree
      (P := AugmentedPolymer P (Fin 2)) n,
    if twoRootMultiplicity Y 0 = 0 ∧ twoRootMultiplicity Y 1 = 0 then
      (((graphSpanningTrees (A₀.mayerIncompatibilityGraph
          (addTwoRootOccurrences Y))).card : ℝ) *
        ∏ child : AugmentedPolymer P (Fin 2),
          ‖A₀.activity child‖ ^ Y child) /
        (mayerSymmetryFactor Y : ℝ)
    else 0

/-- After both root occurrences are distinguished, their activities factor
from the tree majorant and the remaining denominator is precisely the
symmetry factor of the root-free residual orbit. -/
theorem mayerTreeMajorant_addTwoRootOccurrences
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ)
    (Y : MayerMultiIndex (AugmentedPolymer P (Fin 2)))
    (hzero : twoRootMultiplicity Y 0 = 0)
    (hone : twoRootMultiplicity Y 1 = 0) :
    (M.augmentRoots touches rootActivity).mayerTreeMajorant
        (addTwoRootOccurrences Y) =
      ‖rootActivity 0‖ * ‖rootActivity 1‖ *
        ((((graphSpanningTrees
            ((M.augmentRoots touches (fun _ => 0)).mayerIncompatibilityGraph
              (addTwoRootOccurrences Y))).card : ℝ) *
          ∏ child : AugmentedPolymer P (Fin 2),
            ‖(M.augmentRoots touches (fun _ => 0)).activity child‖ ^ Y child) /
          (mayerSymmetryFactor Y : ℝ)) := by
  classical
  let A₁ := M.augmentRoots touches rootActivity
  let A₀ := M.augmentRoots touches (fun _ => 0)
  let root0 : AugmentedPolymer P (Fin 2) := Sum.inr 0
  let root1 : AugmentedPolymer P (Fin 2) := Sum.inr 1
  let Z : MayerMultiIndex (AugmentedPolymer P (Fin 2)) :=
    Y + Finsupp.single root1 1
  have hy0 : Y root0 = 0 := by
    simpa [root0, twoRootMultiplicity] using hzero
  have hy1 : Y root1 = 0 := by
    simpa [root1, twoRootMultiplicity] using hone
  have hrootCount :
      ((Z + Finsupp.single root0 1 :
        MayerMultiIndex (AugmentedPolymer P (Fin 2))) root0) = 1 := by
    simp [Z, root0, root1, hy0]
  have hsymmetry : mayerSymmetryFactor Z = mayerSymmetryFactor Y := by
    have hroot : Z root1 ≠ 0 := by simp [Z]
    have hcount : Z root1 = 1 := by simp [Z, hy1]
    calc
      mayerSymmetryFactor Z =
          Z root1 * pinnedMayerSymmetryFactor Z root1 :=
        mayerSymmetryFactor_eq_mul_pinnedMayerSymmetryFactor Z root1 hroot
      _ = pinnedMayerSymmetryFactor Z root1 := by rw [hcount, one_mul]
      _ = mayerSymmetryFactor Y := by
        simpa [Z] using pinnedMayerSymmetryFactor_add_single Y root1
  have hactivity :
      (∏ child : AugmentedPolymer P (Fin 2), ‖A₁.activity child‖ ^ Y child) =
        ∏ child : AugmentedPolymer P (Fin 2), ‖A₀.activity child‖ ^ Y child := by
    apply Finset.prod_congr rfl
    rintro (child | r) _
    · rfl
    · fin_cases r
      · change ‖A₁.activity root0‖ ^ Y root0 =
          ‖A₀.activity root0‖ ^ Y root0
        rw [hy0]
        simp
      · change ‖A₁.activity root1‖ ^ Y root1 =
          ‖A₀.activity root1‖ ^ Y root1
        rw [hy1]
        simp
  have hrootIdentity :=
    A₁.root_mul_residualTreeTerm_eq_pinned_mayerTreeMajorant Z root0
  rw [hrootCount, Nat.cast_one, one_mul] at hrootIdentity
  rw [prod_norm_activity_add_single, hsymmetry, hactivity] at hrootIdentity
  calc
    A₁.mayerTreeMajorant (addTwoRootOccurrences Y) =
        ‖A₁.activity root0‖ *
          ((((graphSpanningTrees
              (A₁.mayerIncompatibilityGraph
                (addTwoRootOccurrences Y))).card : ℝ) *
            (‖A₁.activity root1‖ *
              ∏ child : AugmentedPolymer P (Fin 2),
                ‖A₀.activity child‖ ^ Y child)) /
            (mayerSymmetryFactor Y : ℝ)) := by
      simpa [Z, addTwoRootOccurrences] using hrootIdentity.symm
    _ = ‖rootActivity 0‖ * ‖rootActivity 1‖ *
        ((((graphSpanningTrees
            (A₀.mayerIncompatibilityGraph
              (addTwoRootOccurrences Y))).card : ℝ) *
          ∏ child : AugmentedPolymer P (Fin 2),
            ‖A₀.activity child‖ ^ Y child) /
          (mayerSymmetryFactor Y : ℝ)) := by
      change ‖rootActivity 0‖ *
          ((((graphSpanningTrees
              (A₀.mayerIncompatibilityGraph
                (addTwoRootOccurrences Y))).card : ℝ) *
            (‖rootActivity 1‖ *
              ∏ child : AugmentedPolymer P (Fin 2),
                ‖A₀.activity child‖ ^ Y child)) /
            (mayerSymmetryFactor Y : ℝ)) = _
      ring

/-- Exact two-root normalization.  The mixed degree-`n+2` tree sector is
the product of the two root activities and the degree-`n` root-free
two-pinned orbit sum; no extra factorial or ordered-label multiplicity is
left over. -/
theorem twoRootMixedMayerTreeDegreeSum_add_two
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ) (n : ℕ) :
    (M.augmentRoots touches rootActivity).twoRootMixedMayerTreeDegreeSum
        (n + 2) =
      ‖rootActivity 0‖ * ‖rootActivity 1‖ *
        (M.augmentRoots touches (fun _ => 0)).residualSymmetricTwoPinnedTreeDegreeSum
          n := by
  classical
  let A₁ := M.augmentRoots touches rootActivity
  let A₀ := M.augmentRoots touches (fun _ => 0)
  let source :=
    (mayerMultiIndicesOfDegree
      (P := AugmentedPolymer P (Fin 2)) n).filter
        (fun Y => twoRootMultiplicity Y 0 = 0 ∧
          twoRootMultiplicity Y 1 = 0)
  let target :=
    (mayerMultiIndicesOfDegree
      (P := AugmentedPolymer P (Fin 2)) (n + 2)).filter
        (fun X => twoRootMultiplicity X 0 = 1 ∧
          twoRootMultiplicity X 1 = 1)
  let residualTerm
      (Y : MayerMultiIndex (AugmentedPolymer P (Fin 2))) : ℝ :=
    (((graphSpanningTrees
        (A₀.mayerIncompatibilityGraph
          (addTwoRootOccurrences Y))).card : ℝ) *
      ∏ child : AugmentedPolymer P (Fin 2),
        ‖A₀.activity child‖ ^ Y child) /
      (mayerSymmetryFactor Y : ℝ)
  have hreindex :
      (∑ Y ∈ source, A₁.mayerTreeMajorant (addTwoRootOccurrences Y)) =
        ∑ X ∈ target, A₁.mayerTreeMajorant X := by
    apply Finset.sum_bij
        (fun Y (_hY : Y ∈ source) => addTwoRootOccurrences Y)
    · intro Y hY
      have hdata := Finset.mem_filter.mp hY
      apply Finset.mem_filter.mpr
      refine ⟨(mem_mayerMultiIndicesOfDegree (n + 2) _).mpr ?_, ?_⟩
      · rw [mayerDegree_addTwoRootOccurrences]
        exact congrArg (fun k => k + 2)
          ((mem_mayerMultiIndicesOfDegree n Y).mp hdata.1)
      · simp [hdata.2]
    · intro Y₁ _ Y₂ _ h
      unfold addTwoRootOccurrences at h
      exact add_right_cancel (add_right_cancel h)
    · intro X hX
      have hdata := Finset.mem_filter.mp hX
      let Y := eraseTwoRootOccurrences X
      have hback : addTwoRootOccurrences Y = X :=
        addTwoRootOccurrences_eraseTwoRootOccurrences X hdata.2.1 hdata.2.2
      have hdegree :=
        (mem_mayerMultiIndicesOfDegree (n + 2) X).mp hdata.1
      have hYdegree : mayerDegree Y = n := by
        have hadd := mayerDegree_addTwoRootOccurrences Y
        rw [hback, hdegree] at hadd
        omega
      have hYroots : twoRootMultiplicity Y 0 = 0 ∧
          twoRootMultiplicity Y 1 = 0 := by
        simp [Y, hdata.2]
      exact ⟨Y, Finset.mem_filter.mpr
        ⟨(mem_mayerMultiIndicesOfDegree n Y).mpr hYdegree, hYroots⟩,
          hback⟩
    · intro Y _
      rfl
  have hrestrict :
      (∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) (n + 2),
          if twoRootMultiplicity X 0 = 1 ∧
              twoRootMultiplicity X 1 = 1 then
            A₁.mayerTreeMajorant X else 0) =
        ∑ X ∈ target, A₁.mayerTreeMajorant X := by
    dsimp [target]
    rw [Finset.sum_filter]
  have hterm (Y : MayerMultiIndex (AugmentedPolymer P (Fin 2)))
      (hY : Y ∈ source) :
      A₁.mayerTreeMajorant (addTwoRootOccurrences Y) =
        ‖rootActivity 0‖ * ‖rootActivity 1‖ * residualTerm Y := by
    have hdata := (Finset.mem_filter.mp hY).2
    simpa [A₁, A₀, residualTerm] using
      M.mayerTreeMajorant_addTwoRootOccurrences
        touches rootActivity Y hdata.1 hdata.2
  unfold twoRootMixedMayerTreeDegreeSum
  rw [hrestrict, ← hreindex]
  calc
    (∑ Y ∈ source, A₁.mayerTreeMajorant (addTwoRootOccurrences Y)) =
        ∑ Y ∈ source,
          (‖rootActivity 0‖ * ‖rootActivity 1‖) * residualTerm Y := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = (‖rootActivity 0‖ * ‖rootActivity 1‖) *
        ∑ Y ∈ source, residualTerm Y := by
      rw [Finset.mul_sum]
    _ = ‖rootActivity 0‖ * ‖rootActivity 1‖ *
        A₀.residualSymmetricTwoPinnedTreeDegreeSum n := by
      congr 1
      unfold residualSymmetricTwoPinnedTreeDegreeSum
      dsimp [source, residualTerm]
      rw [Finset.sum_filter]

theorem residualSymmetricTwoPinnedTreeDegreeSum_nonneg
    (A₀ : FinitePolymerModel (AugmentedPolymer P (Fin 2))) (n : ℕ) :
    0 ≤ A₀.residualSymmetricTwoPinnedTreeDegreeSum n := by
  classical
  unfold residualSymmetricTwoPinnedTreeDegreeSum
  exact Finset.sum_nonneg fun Y _ => by
    split_ifs
    · exact div_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          (Finset.prod_nonneg fun child _ =>
            pow_nonneg (norm_nonneg _) _))
        (Nat.cast_nonneg _)
    · exact le_rfl

/-- Whitney's tree bound, restricted to the genuinely mixed sector. -/
theorem norm_twoRootMixedMayerDegreeSum_le_tree
    (A : FinitePolymerModel (AugmentedPolymer P (Fin 2))) (n : ℕ) :
    ‖A.twoRootMixedMayerDegreeSum n‖ ≤
      A.twoRootMixedMayerTreeDegreeSum n := by
  classical
  unfold twoRootMixedMayerDegreeSum twoRootMixedMayerTreeDegreeSum
  calc
    ‖∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) n,
        if twoRootMultiplicity X 0 = 1 ∧
            twoRootMultiplicity X 1 = 1 then
          A.mayerClusterTerm X else 0‖ ≤
      ∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) n,
        ‖if twoRootMultiplicity X 0 = 1 ∧
            twoRootMultiplicity X 1 = 1 then
          A.mayerClusterTerm X else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) n,
        if twoRootMultiplicity X 0 = 1 ∧
            twoRootMultiplicity X 1 = 1 then
          A.mayerTreeMajorant X else 0 := by
      apply Finset.sum_le_sum
      intro X _
      by_cases hroots : twoRootMultiplicity X 0 = 1 ∧
          twoRootMultiplicity X 1 = 1
      · simp only [hroots]
        exact A.norm_mayerClusterTerm_le_mayerTreeMajorant X
      · simp [hroots]

/-- The mixed tree sector is a sub-sum of the tree series pinned at either
labelled root. -/
theorem twoRootMixedMayerTreeDegreeSum_le_pinned
    (A : FinitePolymerModel (AugmentedPolymer P (Fin 2)))
    (r : Fin 2) (n : ℕ) :
    A.twoRootMixedMayerTreeDegreeSum n ≤
      A.pinnedMayerTreeDegreeSum (Sum.inr r) n := by
  classical
  unfold twoRootMixedMayerTreeDegreeSum pinnedMayerTreeDegreeSum
  apply Finset.sum_le_sum
  intro X _
  by_cases hroots : twoRootMultiplicity X 0 = 1 ∧
      twoRootMultiplicity X 1 = 1
  · rw [if_pos hroots]
    have hr : X (Sum.inr r) = 1 := by
      fin_cases r
      · exact hroots.1
      · exact hroots.2
    rw [hr, Nat.cast_one, one_mul]
  · rw [if_neg hroots]
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold mayerTreeMajorant
    positivity

/-- Degreewise mixed Mayer control by the exact root-free two-pinned tree
orbit.  This is the two-root analogue of the one-root residual normalization
used by the KP theorem. -/
theorem norm_twoRootMixedMayerDegreeSum_add_two_le
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ) (n : ℕ) :
    ‖(M.augmentRoots touches rootActivity).twoRootMixedMayerDegreeSum
        (n + 2)‖ ≤
      ‖rootActivity 0‖ * ‖rootActivity 1‖ *
        (M.augmentRoots touches (fun _ => 0)).residualSymmetricTwoPinnedTreeDegreeSum
          n := by
  calc
    _ ≤ (M.augmentRoots touches rootActivity).twoRootMixedMayerTreeDegreeSum
        (n + 2) :=
      norm_twoRootMixedMayerDegreeSum_le_tree _ _
    _ = _ := M.twoRootMixedMayerTreeDegreeSum_add_two
      touches rootActivity n

/-! ## Source-sector summability from a nonzero KP regularization -/

theorem norm_firstRootLinearMayerDegreeSum_le_scaled
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity alpha : Fin 2 → ℂ)
    (halpha : alpha 0 ≠ 0) (n : ℕ) :
    ‖(M.augmentRoots touches rootActivity).firstRootLinearMayerDegreeSum n‖ ≤
      ‖alpha 0‖⁻¹ *
        (M.augmentRoots touches
          (fun r => alpha r * rootActivity r)).normMayerDegreeSum n := by
  classical
  let A := M.augmentRoots touches rootActivity
  let Aalpha := M.augmentRoots touches
    (fun r => alpha r * rootActivity r)
  unfold firstRootLinearMayerDegreeSum normMayerDegreeSum
  calc
    ‖∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) n,
        if twoRootMultiplicity X 0 = 1 ∧
            twoRootMultiplicity X 1 = 0 then
          A.mayerClusterTerm X else 0‖ ≤
      ∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) n,
        ‖if twoRootMultiplicity X 0 = 1 ∧
            twoRootMultiplicity X 1 = 0 then
          A.mayerClusterTerm X else 0‖ := norm_sum_le _ _
    _ ≤ ‖alpha 0‖⁻¹ *
        ∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) n,
          ‖Aalpha.mayerClusterTerm X‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro X _
      by_cases hroot : twoRootMultiplicity X 0 = 1 ∧
          twoRootMultiplicity X 1 = 0
      · rw [if_pos hroot]
        have hscale := M.mayerClusterTerm_augmentRoots_twoSource
          touches rootActivity alpha X
        have hscale' : Aalpha.mayerClusterTerm X =
            alpha 0 * A.mayerClusterTerm X := by
          simpa [A, Aalpha, Fin.prod_univ_two, hroot] using hscale
        rw [hscale', norm_mul]
        have hnorm : ‖alpha 0‖ ≠ 0 := norm_ne_zero_iff.mpr halpha
        exact le_of_eq (by field_simp)
      · rw [if_neg hroot, norm_zero]
        positivity

theorem norm_secondRootLinearMayerDegreeSum_le_scaled
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity alpha : Fin 2 → ℂ)
    (halpha : alpha 1 ≠ 0) (n : ℕ) :
    ‖(M.augmentRoots touches rootActivity).secondRootLinearMayerDegreeSum n‖ ≤
      ‖alpha 1‖⁻¹ *
        (M.augmentRoots touches
          (fun r => alpha r * rootActivity r)).normMayerDegreeSum n := by
  classical
  let A := M.augmentRoots touches rootActivity
  let Aalpha := M.augmentRoots touches
    (fun r => alpha r * rootActivity r)
  unfold secondRootLinearMayerDegreeSum normMayerDegreeSum
  calc
    ‖∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) n,
        if twoRootMultiplicity X 0 = 0 ∧
            twoRootMultiplicity X 1 = 1 then
          A.mayerClusterTerm X else 0‖ ≤
      ∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) n,
        ‖if twoRootMultiplicity X 0 = 0 ∧
            twoRootMultiplicity X 1 = 1 then
          A.mayerClusterTerm X else 0‖ := norm_sum_le _ _
    _ ≤ ‖alpha 1‖⁻¹ *
        ∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) n,
          ‖Aalpha.mayerClusterTerm X‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro X _
      by_cases hroot : twoRootMultiplicity X 0 = 0 ∧
          twoRootMultiplicity X 1 = 1
      · rw [if_pos hroot]
        have hscale := M.mayerClusterTerm_augmentRoots_twoSource
          touches rootActivity alpha X
        have hscale' : Aalpha.mayerClusterTerm X =
            alpha 1 * A.mayerClusterTerm X := by
          simpa [A, Aalpha, Fin.prod_univ_two, hroot] using hscale
        rw [hscale', norm_mul]
        have hnorm : ‖alpha 1‖ ≠ 0 := norm_ne_zero_iff.mpr halpha
        exact le_of_eq (by field_simp)
      · rw [if_neg hroot, norm_zero]
        positivity

theorem norm_twoRootMixedMayerDegreeSum_le_scaled
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity alpha : Fin 2 → ℂ)
    (halpha0 : alpha 0 ≠ 0) (halpha1 : alpha 1 ≠ 0) (n : ℕ) :
    ‖(M.augmentRoots touches rootActivity).twoRootMixedMayerDegreeSum n‖ ≤
      (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
        (M.augmentRoots touches
          (fun r => alpha r * rootActivity r)).normMayerDegreeSum n := by
  classical
  let A := M.augmentRoots touches rootActivity
  let Aalpha := M.augmentRoots touches
    (fun r => alpha r * rootActivity r)
  unfold twoRootMixedMayerDegreeSum normMayerDegreeSum
  calc
    ‖∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) n,
        if twoRootMultiplicity X 0 = 1 ∧
            twoRootMultiplicity X 1 = 1 then
          A.mayerClusterTerm X else 0‖ ≤
      ∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) n,
        ‖if twoRootMultiplicity X 0 = 1 ∧
            twoRootMultiplicity X 1 = 1 then
          A.mayerClusterTerm X else 0‖ := norm_sum_le _ _
    _ ≤ (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
        ∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) n,
          ‖Aalpha.mayerClusterTerm X‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro X _
      by_cases hroots : twoRootMultiplicity X 0 = 1 ∧
          twoRootMultiplicity X 1 = 1
      · rw [if_pos hroots]
        have hscale := M.mayerClusterTerm_augmentRoots_twoSource
          touches rootActivity alpha X
        have hscale' : Aalpha.mayerClusterTerm X =
            (alpha 0 * alpha 1) * A.mayerClusterTerm X := by
          simpa [A, Aalpha, Fin.prod_univ_two, hroots] using hscale
        rw [hscale', norm_mul, norm_mul]
        have hnorm0 : ‖alpha 0‖ ≠ 0 := norm_ne_zero_iff.mpr halpha0
        have hnorm1 : ‖alpha 1‖ ≠ 0 := norm_ne_zero_iff.mpr halpha1
        exact le_of_eq (by field_simp)
      · rw [if_neg hroots, norm_zero]
        positivity

/-- Absolute summability of the first labelled source sector can be
transferred from any nonzero rescaling for which the full Mayer majorant is
summable. -/
theorem summable_norm_firstRootLinearMayerDegreeSum_succ_of_scaled
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity alpha : Fin 2 → ℂ)
    (halpha : alpha 0 ≠ 0)
    (hscaled : Summable (fun n : ℕ ↦
      (M.augmentRoots touches
        (fun r => alpha r * rootActivity r)).normMayerDegreeSum (n + 1))) :
    Summable (fun n : ℕ ↦
      ‖(M.augmentRoots touches rootActivity).firstRootLinearMayerDegreeSum
        (n + 1)‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => M.norm_firstRootLinearMayerDegreeSum_le_scaled
      touches rootActivity alpha halpha (n + 1))
    (hscaled.mul_left ‖alpha 0‖⁻¹)

/-- Absolute summability of the second labelled source sector can be
transferred from a nonzero rescaled gas. -/
theorem summable_norm_secondRootLinearMayerDegreeSum_succ_of_scaled
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity alpha : Fin 2 → ℂ)
    (halpha : alpha 1 ≠ 0)
    (hscaled : Summable (fun n : ℕ ↦
      (M.augmentRoots touches
        (fun r => alpha r * rootActivity r)).normMayerDegreeSum (n + 1))) :
    Summable (fun n : ℕ ↦
      ‖(M.augmentRoots touches rootActivity).secondRootLinearMayerDegreeSum
        (n + 1)‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => M.norm_secondRootLinearMayerDegreeSum_le_scaled
      touches rootActivity alpha halpha (n + 1))
    (hscaled.mul_left ‖alpha 1‖⁻¹)

/-- Absolute summability of the genuinely mixed source sector can be
transferred from a gas in which both labelled root activities are nonzero. -/
theorem summable_norm_twoRootMixedMayerDegreeSum_succ_of_scaled
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity alpha : Fin 2 → ℂ)
    (halpha0 : alpha 0 ≠ 0) (halpha1 : alpha 1 ≠ 0)
    (hscaled : Summable (fun n : ℕ ↦
      (M.augmentRoots touches
        (fun r => alpha r * rootActivity r)).normMayerDegreeSum (n + 1))) :
    Summable (fun n : ℕ ↦
      ‖(M.augmentRoots touches rootActivity).twoRootMixedMayerDegreeSum
        (n + 1)‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => M.norm_twoRootMixedMayerDegreeSum_le_scaled
      touches rootActivity alpha halpha0 halpha1 (n + 1))
    (hscaled.mul_left (‖alpha 0‖ * ‖alpha 1‖)⁻¹)

/-- Distinguished occurrence of the first labelled root. -/
def twoRootFirstVertex
    (X : MayerMultiIndex (AugmentedPolymer P (Fin 2)))
    (h : 0 < twoRootMultiplicity X 0) : MayerVertex X :=
  ⟨Sum.inr 0, ⟨0, h⟩⟩

/-- Distinguished occurrence of the second labelled root. -/
def twoRootSecondVertex
    (X : MayerMultiIndex (AugmentedPolymer P (Fin 2)))
    (h : 0 < twoRootMultiplicity X 1) : MayerVertex X :=
  ⟨Sum.inr 1, ⟨0, h⟩⟩

/-- A nonzero mixed coefficient is a connected cluster joining the two
distinguished root occurrences.  Those occurrences are not adjacent because
distinct roots in `augmentRoots` are compatible; hence the joining path must
pass through bulk occurrences. -/
theorem twoRootMixed_nonzero_connected_nonadjacent
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ)
    (X : MayerMultiIndex (AugmentedPolymer P (Fin 2)))
    (hzero : twoRootMultiplicity X 0 = 1)
    (hone : twoRootMultiplicity X 1 = 1)
    (hterm : (M.augmentRoots touches rootActivity).mayerClusterTerm X ≠ 0) :
    ((M.augmentRoots touches rootActivity).mayerIncompatibilityGraph X).Connected ∧
      ¬((M.augmentRoots touches rootActivity).mayerIncompatibilityGraph X).Adj
        (twoRootFirstVertex X (by omega))
        (twoRootSecondVertex X (by omega)) := by
  constructor
  · by_contra hconnected
    exact hterm
      ((M.augmentRoots touches rootActivity).mayerClusterTerm_eq_zero_of_not_connected
        X hconnected)
  · simp [mayerIncompatibilityGraph, twoRootFirstVertex,
      twoRootSecondVertex, augmentRoots]

/-- Consequently every nonzero mixed term contains an actual simple path
between the two compatible labelled roots. -/
theorem exists_twoRootPath_of_mixed_nonzero
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ)
    (X : MayerMultiIndex (AugmentedPolymer P (Fin 2)))
    (hzero : twoRootMultiplicity X 0 = 1)
    (hone : twoRootMultiplicity X 1 = 1)
    (hterm : (M.augmentRoots touches rootActivity).mayerClusterTerm X ≠ 0) :
    ∃ path :
        ((M.augmentRoots touches rootActivity).mayerIncompatibilityGraph X).Walk
          (twoRootFirstVertex X (by omega))
          (twoRootSecondVertex X (by omega)),
      path.IsPath := by
  have hconnected :=
    (M.twoRootMixed_nonzero_connected_nonadjacent
      touches rootActivity X hzero hone hterm).1
  exact hconnected.preconnected.exists_isPath
    (twoRootFirstVertex X (by omega))
    (twoRootSecondVertex X (by omega))

@[simp]
theorem constantCoeff_twoRootSourceMayerPowerSeries
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ) :
    PowerSeries.constantCoeff
      (M.twoRootSourceMayerPowerSeries touches rootActivity) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [twoRootSourceMayerPowerSeries]

/-- Source extraction identifies the first-root connected coefficient. -/
theorem coeff_linearCoefficient_first_twoRootSourceMayerPowerSeries
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ) (n : ℕ) :
    PowerSeries.coeff n
        (BivariateSourcePowerSeries.linearCoefficient 0
          (M.twoRootSourceMayerPowerSeries touches rootActivity)) =
      (M.augmentRoots touches rootActivity).firstRootLinearMayerDegreeSum n := by
  unfold BivariateSourcePowerSeries.linearCoefficient
    BivariateSourcePowerSeries.constantSource
  rw [PowerSeries.coeff_map,
    BivariateSourcePowerSeries.coeff_sourceDerivative]
  cases n with
  | zero =>
      unfold firstRootLinearMayerDegreeSum
      simp only [twoRootSourceMayerPowerSeries, PowerSeries.coeff_mk,
        map_zero]
      symm
      apply Finset.sum_eq_zero
      intro X hX
      have hdegree : mayerDegree X = 0 :=
        (mem_mayerMultiIndicesOfDegree 0 X).mp hX
      have hx : ∀ x : AugmentedPolymer P (Fin 2), X x = 0 := by
        intro x
        unfold mayerDegree at hdegree
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => Nat.zero_le _)).mp hdegree x (Finset.mem_univ x)
      simp [twoRootMultiplicity, hx]
  | succ n =>
      simp only [twoRootSourceMayerPowerSeries, PowerSeries.coeff_mk,
        map_sum, Fin.prod_univ_two]
      unfold firstRootLinearMayerDegreeSum
      apply Finset.sum_congr rfl
      intro X _
      exact BivariateSourcePowerSeries.constantCoeff_pderiv_first_twoVariableMonomial
        (twoRootMultiplicity X 0) (twoRootMultiplicity X 1)
        ((M.augmentRoots touches rootActivity).mayerClusterTerm X)

/-- Source extraction identifies the second-root connected coefficient. -/
theorem coeff_linearCoefficient_second_twoRootSourceMayerPowerSeries
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ) (n : ℕ) :
    PowerSeries.coeff n
        (BivariateSourcePowerSeries.linearCoefficient 1
          (M.twoRootSourceMayerPowerSeries touches rootActivity)) =
      (M.augmentRoots touches rootActivity).secondRootLinearMayerDegreeSum n := by
  unfold BivariateSourcePowerSeries.linearCoefficient
    BivariateSourcePowerSeries.constantSource
  rw [PowerSeries.coeff_map,
    BivariateSourcePowerSeries.coeff_sourceDerivative]
  cases n with
  | zero =>
      unfold secondRootLinearMayerDegreeSum
      simp only [twoRootSourceMayerPowerSeries, PowerSeries.coeff_mk,
        map_zero]
      symm
      apply Finset.sum_eq_zero
      intro X hX
      have hdegree : mayerDegree X = 0 :=
        (mem_mayerMultiIndicesOfDegree 0 X).mp hX
      have hx : ∀ x : AugmentedPolymer P (Fin 2), X x = 0 := by
        intro x
        unfold mayerDegree at hdegree
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => Nat.zero_le _)).mp hdegree x (Finset.mem_univ x)
      simp [twoRootMultiplicity, hx]
  | succ n =>
      simp only [twoRootSourceMayerPowerSeries, PowerSeries.coeff_mk,
        map_sum, Fin.prod_univ_two]
      unfold secondRootLinearMayerDegreeSum
      apply Finset.sum_congr rfl
      intro X _
      exact BivariateSourcePowerSeries.constantCoeff_pderiv_second_twoVariableMonomial
        (twoRootMultiplicity X 0) (twoRootMultiplicity X 1)
        ((M.augmentRoots touches rootActivity).mayerClusterTerm X)

/-- Mixed source extraction is exactly the multiplicity-one two-root Mayer
degree sum. -/
theorem coeff_mixedCoefficient_twoRootSourceMayerPowerSeries
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ) (n : ℕ) :
    PowerSeries.coeff n
        (BivariateSourcePowerSeries.mixedCoefficient
          (M.twoRootSourceMayerPowerSeries touches rootActivity)) =
      (M.augmentRoots touches rootActivity).twoRootMixedMayerDegreeSum n := by
  unfold BivariateSourcePowerSeries.mixedCoefficient
    BivariateSourcePowerSeries.constantSource
  rw [PowerSeries.coeff_map,
    BivariateSourcePowerSeries.coeff_sourceDerivative,
    BivariateSourcePowerSeries.coeff_sourceDerivative]
  cases n with
  | zero =>
      unfold twoRootMixedMayerDegreeSum
      simp only [twoRootSourceMayerPowerSeries, PowerSeries.coeff_mk,
        map_zero]
      symm
      apply Finset.sum_eq_zero
      intro X hX
      have hdegree : mayerDegree X = 0 :=
        (mem_mayerMultiIndicesOfDegree 0 X).mp hX
      have hx : ∀ x : AugmentedPolymer P (Fin 2), X x = 0 := by
        intro x
        unfold mayerDegree at hdegree
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => Nat.zero_le _)).mp hdegree x (Finset.mem_univ x)
      simp [twoRootMultiplicity, hx]
  | succ n =>
      simp only [twoRootSourceMayerPowerSeries, PowerSeries.coeff_mk,
        map_sum, Fin.prod_univ_two]
      unfold twoRootMixedMayerDegreeSum
      apply Finset.sum_congr rfl
      intro X _
      exact BivariateSourcePowerSeries.constantCoeff_pderiv_pderiv_twoVariableMonomial
        (twoRootMultiplicity X 0) (twoRootMultiplicity X 1)
        ((M.augmentRoots touches rootActivity).mayerClusterTerm X)

/-- Evaluate the two-source partition series. -/
theorem map_twoRootSourcePartitionPowerSeries_eval
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ)
    (alpha : Fin 2 → ℂ) :
    (M.twoRootSourcePartitionPowerSeries touches rootActivity).map
        (MvPolynomial.eval alpha) =
      (M.augmentRoots touches
        (fun r => alpha r * rootActivity r)).partitionPowerSeries
          Finset.univ := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map, coeff_partitionPowerSeries]
  simp only [twoRootSourcePartitionPowerSeries, PowerSeries.coeff_mk]
  unfold partitionDegreeCoefficient
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro Gamma _
  exact M.eval_twoRootSourceFamilyWeight
    touches rootActivity alpha Gamma

/-- Evaluate the two-source connected Mayer series. -/
theorem map_twoRootSourceMayerPowerSeries_eval
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ)
    (alpha : Fin 2 → ℂ) :
    (M.twoRootSourceMayerPowerSeries touches rootActivity).map
        (MvPolynomial.eval alpha) =
      (M.augmentRoots touches
        (fun r => alpha r * rootActivity r)).restrictedSymmetricMayerPowerSeries
          Finset.univ := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [twoRootSourceMayerPowerSeries,
        restrictedSymmetricMayerPowerSeries,
        restrictedSymmetricMayerCoefficient]
  | succ n =>
      rw [PowerSeries.coeff_map]
      simp only [twoRootSourceMayerPowerSeries, PowerSeries.coeff_mk,
        restrictedSymmetricMayerPowerSeries, map_sum, map_mul, map_prod,
        map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C]
      change (∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) (n + 1),
          (∏ r : Fin 2, alpha r ^ twoRootMultiplicity X r) *
            (M.augmentRoots touches rootActivity).mayerClusterTerm X) =
        ∑ X ∈ (mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P (Fin 2)) (n + 1)).filter
            (fun X => X.support ⊆ Finset.univ),
          (M.augmentRoots touches
            (fun r => alpha r * rootActivity r)).mayerClusterTerm X
      rw [Finset.filter_eq_self.2]
      · apply Finset.sum_congr rfl
        intro X _
        rw [M.mayerClusterTerm_augmentRoots_twoSource
          touches rootActivity alpha X]
      · intro X _
        exact Finset.subset_univ _

/-- Exact two-source fixed-labelled exponential formula. -/
theorem expOf_twoRootSourceMayerPowerSeries
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ) :
    BivariateSourcePowerSeries.expOf
        (M.twoRootSourceMayerPowerSeries touches rootActivity) =
      M.twoRootSourcePartitionPowerSeries touches rootActivity := by
  apply PowerSeries.ext
  intro n
  apply MvPolynomial.funext
  intro alpha
  have hcomplex :
      PowerSeriesBridge.expOf
          ((M.augmentRoots touches
            (fun r => alpha r * rootActivity r)).restrictedSymmetricMayerPowerSeries
              Finset.univ) =
        (M.augmentRoots touches
          (fun r => alpha r * rootActivity r)).partitionPowerSeries
            Finset.univ := by
    rw [(M.augmentRoots touches
      (fun r => alpha r * rootActivity r)).restrictedSymmetricMayerPowerSeries_eq_formalMayerLog]
    exact (M.augmentRoots touches
      (fun r => alpha r * rootActivity r)).expOf_formalMayerLog_eq_partitionPowerSeries
        Finset.univ
  have hmapped :
      (BivariateSourcePowerSeries.expOf
          (M.twoRootSourceMayerPowerSeries touches rootActivity)).map
            (MvPolynomial.eval alpha) =
        (M.twoRootSourcePartitionPowerSeries touches rootActivity).map
          (MvPolynomial.eval alpha) := by
    rw [BivariateSourcePowerSeries.map_expOf_eval _
      (M.constantCoeff_twoRootSourceMayerPowerSeries
        touches rootActivity) alpha,
      M.map_twoRootSourceMayerPowerSeries_eval
        touches rootActivity alpha,
      M.map_twoRootSourcePartitionPowerSeries_eval
        touches rootActivity alpha]
    exact hcomplex
  exact congrArg (PowerSeries.coeff n) hmapped

/-- Mixed pointed exponential formula for the compatible two-root gas. -/
theorem mixedCoefficient_twoRootSourcePartitionPowerSeries
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ) :
    BivariateSourcePowerSeries.mixedCoefficient
        (M.twoRootSourcePartitionPowerSeries touches rootActivity) =
      BivariateSourcePowerSeries.constantSource
          (M.twoRootSourcePartitionPowerSeries touches rootActivity) *
        (BivariateSourcePowerSeries.mixedCoefficient
            (M.twoRootSourceMayerPowerSeries touches rootActivity) +
          BivariateSourcePowerSeries.linearCoefficient 0
              (M.twoRootSourceMayerPowerSeries touches rootActivity) *
            BivariateSourcePowerSeries.linearCoefficient 1
              (M.twoRootSourceMayerPowerSeries touches rootActivity)) := by
  rw [← M.expOf_twoRootSourceMayerPowerSeries touches rootActivity]
  exact BivariateSourcePowerSeries.mixedCoefficient_expOf
    (M.constantCoeff_twoRootSourceMayerPowerSeries touches rootActivity)

/-! ## Evaluation at unit total activity -/

/-- Finite zero-source coefficient of the two-root partition series. -/
def twoRootVacuumPartitionCoefficient
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ) : ℂ :=
  ∑ n ∈ Finset.range
      ((Finset.univ : Finset (AugmentedPolymer P (Fin 2))).card + 1),
    PowerSeries.coeff n
      (BivariateSourcePowerSeries.constantSource
        (M.twoRootSourcePartitionPowerSeries touches rootActivity))

/-- Finite coefficient bilinear in the two partition sources. -/
def twoRootMixedPartitionCoefficient
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ) : ℂ :=
  ∑ n ∈ Finset.range
      ((Finset.univ : Finset (AugmentedPolymer P (Fin 2))).card + 1),
    PowerSeries.coeff n
      (BivariateSourcePowerSeries.mixedCoefficient
        (M.twoRootSourcePartitionPowerSeries touches rootActivity))

/-- The bivariate partition series is supported in the finite range allowed
by the augmented hard-core gas. -/
theorem coeff_twoRootSourcePartitionPowerSeries_eq_zero_of_card_lt
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ) {n : ℕ}
    (hcard :
      (Finset.univ : Finset (AugmentedPolymer P (Fin 2))).card < n) :
    PowerSeries.coeff n
        (M.twoRootSourcePartitionPowerSeries touches rootActivity) = 0 := by
  apply MvPolynomial.funext
  intro alpha
  have hmapped := congrArg (PowerSeries.coeff n)
    (M.map_twoRootSourcePartitionPowerSeries_eval
      touches rootActivity alpha)
  calc
    MvPolynomial.eval alpha
        (PowerSeries.coeff n
          (M.twoRootSourcePartitionPowerSeries touches rootActivity)) =
      PowerSeries.coeff n
        ((M.augmentRoots touches
          (fun r => alpha r * rootActivity r)).partitionPowerSeries
            Finset.univ) := by
      simpa only [PowerSeries.coeff_map] using hmapped
    _ = 0 := by
      rw [coeff_partitionPowerSeries]
      exact (M.augmentRoots touches
        (fun r => alpha r * rootActivity r)).partitionDegreeCoefficient_eq_zero_of_card_lt
          Finset.univ hcard
    _ = MvPolynomial.eval alpha 0 := by simp

/-- Absolute convergence of the three connected source sectors lets the
mixed pointed identity be evaluated at unit total activity.  The exact
bilinear partition coefficient is the vacuum coefficient times the sum of
the genuinely connected two-root series and the product of the two one-root
series. -/
theorem twoRootMixedPartitionCoefficient_eq_vacuum_mul_connected
    (M : FinitePolymerModel P) (touches : Fin 2 → P → Prop)
    [DecidableRel touches] (rootActivity : Fin 2 → ℂ)
    (hfirst : Summable (fun n : ℕ =>
      ‖(M.augmentRoots touches rootActivity).firstRootLinearMayerDegreeSum
        (n + 1)‖))
    (hsecond : Summable (fun n : ℕ =>
      ‖(M.augmentRoots touches rootActivity).secondRootLinearMayerDegreeSum
        (n + 1)‖))
    (hmixed : Summable (fun n : ℕ =>
      ‖(M.augmentRoots touches rootActivity).twoRootMixedMayerDegreeSum
        (n + 1)‖)) :
    M.twoRootMixedPartitionCoefficient touches rootActivity =
      M.twoRootVacuumPartitionCoefficient touches rootActivity *
        ((∑' n : ℕ,
            (M.augmentRoots touches rootActivity).twoRootMixedMayerDegreeSum n) +
          (∑' n : ℕ,
              (M.augmentRoots touches rootActivity).firstRootLinearMayerDegreeSum n) *
            ∑' n : ℕ,
              (M.augmentRoots touches rootActivity).secondRootLinearMayerDegreeSum n) := by
  let sourcePartition :=
    M.twoRootSourcePartitionPowerSeries touches rootActivity
  let sourceConnected :=
    M.twoRootSourceMayerPowerSeries touches rootActivity
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
  let Rmix : ℕ → ℂ := fun n => PowerSeries.coeff n
    (BivariateSourcePowerSeries.mixedCoefficient sourcePartition)
  let cutoff :=
    (Finset.univ : Finset (AugmentedPolymer P (Fin 2))).card + 1
  have hsourceZero {n : ℕ} (hn : n ∉ Finset.range cutoff) :
      PowerSeries.coeff n sourcePartition = 0 := by
    apply M.coeff_twoRootSourcePartitionPowerSeries_eq_zero_of_card_lt
      touches rootActivity
    exact Nat.lt_of_not_ge fun hle =>
      hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
  have hBzero {n : ℕ} (hn : n ∉ Finset.range cutoff) : B n = 0 := by
    unfold B BivariateSourcePowerSeries.constantSource
    rw [PowerSeries.coeff_map, hsourceZero hn, map_zero]
  have hRzero {n : ℕ} (hn : n ∉ Finset.range cutoff) : Rmix n = 0 := by
    unfold Rmix BivariateSourcePowerSeries.mixedCoefficient
      BivariateSourcePowerSeries.constantSource
    rw [PowerSeries.coeff_map,
      BivariateSourcePowerSeries.coeff_sourceDerivative,
      BivariateSourcePowerSeries.coeff_sourceDerivative,
      hsourceZero hn]
    simp
  have hBnorm : Summable (fun n => ‖B n‖) :=
    summable_of_ne_finset_zero (s := Finset.range cutoff) fun n hn => by
      rw [hBzero hn, norm_zero]
  have hC0norm : Summable (fun n => ‖C0 n‖) := by
    have htail : Summable (fun n => ‖C0 (n + 1)‖) := by
      apply hfirst.congr
      intro n
      unfold C0 sourceConnected
      rw [M.coeff_linearCoefficient_first_twoRootSourceMayerPowerSeries
        touches rootActivity]
    exact (summable_nat_add_iff (f := fun n => ‖C0 n‖) 1).mp htail
  have hC1norm : Summable (fun n => ‖C1 n‖) := by
    have htail : Summable (fun n => ‖C1 (n + 1)‖) := by
      apply hsecond.congr
      intro n
      unfold C1 sourceConnected
      rw [M.coeff_linearCoefficient_second_twoRootSourceMayerPowerSeries
        touches rootActivity]
    exact (summable_nat_add_iff (f := fun n => ‖C1 n‖) 1).mp htail
  have hC01norm : Summable (fun n => ‖C01 n‖) := by
    have htail : Summable (fun n => ‖C01 (n + 1)‖) := by
      apply hmixed.congr
      intro n
      unfold C01 sourceConnected
      rw [M.coeff_mixedCoefficient_twoRootSourceMayerPowerSeries
        touches rootActivity]
    exact (summable_nat_add_iff (f := fun n => ‖C01 n‖) 1).mp htail
  have hConvNorm : Summable (fun n => ‖Conv n‖) := by
    exact summable_norm_sum_mul_antidiagonal_of_summable_norm
      hC0norm hC1norm
  have hDnorm : Summable (fun n => ‖D n‖) := by
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_add_le (C01 n) (Conv n))
      (hC01norm.add hConvNorm)
  have hBsum : HasSum B
      (M.twoRootVacuumPartitionCoefficient touches rootActivity) := by
    have hfinite : HasSum B (∑ n ∈ Finset.range cutoff, B n) :=
      hasSum_sum_of_ne_finset_zero
        (s := Finset.range cutoff) (fun n hn => hBzero hn)
    simpa only [twoRootVacuumPartitionCoefficient, B,
      sourcePartition, cutoff] using hfinite
  have hRsum : HasSum Rmix
      (M.twoRootMixedPartitionCoefficient touches rootActivity) := by
    have hfinite : HasSum Rmix (∑ n ∈ Finset.range cutoff, Rmix n) :=
      hasSum_sum_of_ne_finset_zero
        (s := Finset.range cutoff) (fun n hn => hRzero hn)
    simpa only [twoRootMixedPartitionCoefficient, Rmix,
      sourcePartition, cutoff] using hfinite
  have hpoint :
      BivariateSourcePowerSeries.mixedCoefficient sourcePartition =
        BivariateSourcePowerSeries.constantSource sourcePartition *
          (BivariateSourcePowerSeries.mixedCoefficient sourceConnected +
            BivariateSourcePowerSeries.linearCoefficient 0 sourceConnected *
              BivariateSourcePowerSeries.linearCoefficient 1 sourceConnected) := by
    exact M.mixedCoefficient_twoRootSourcePartitionPowerSeries
      touches rootActivity
  have hDcoeff (n : ℕ) : PowerSeries.coeff n
      (BivariateSourcePowerSeries.mixedCoefficient sourceConnected +
        BivariateSourcePowerSeries.linearCoefficient 0 sourceConnected *
          BivariateSourcePowerSeries.linearCoefficient 1 sourceConnected) =
      D n := by
    simp only [map_add, PowerSeries.coeff_mul]
    rfl
  have hproduct :
      (∑' n, B n) * (∑' n, D n) = ∑' n, Rmix n := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      hBnorm hDnorm]
    apply tsum_congr
    intro n
    have hcoeff := congrArg (PowerSeries.coeff n) hpoint
    rw [PowerSeries.coeff_mul] at hcoeff
    simpa only [B, Rmix, hDcoeff] using hcoeff.symm
  have hConvSum :
      (∑' n, C0 n) * (∑' n, C1 n) = ∑' n, Conv n := by
    exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      hC0norm hC1norm
  have hDsum :
      ∑' n, D n = (∑' n, C01 n) +
        (∑' n, C0 n) * (∑' n, C1 n) := by
    rw [show (∑' n, D n) = (∑' n, C01 n) + ∑' n, Conv n by
      exact Summable.tsum_add hC01norm.of_norm hConvNorm.of_norm]
    rw [← hConvSum]
  calc
    M.twoRootMixedPartitionCoefficient touches rootActivity =
        ∑' n, Rmix n := hRsum.tsum_eq.symm
    _ = (∑' n, B n) * (∑' n, D n) := hproduct.symm
    _ = M.twoRootVacuumPartitionCoefficient touches rootActivity *
        ((∑' n, C01 n) + (∑' n, C0 n) * (∑' n, C1 n)) := by
      rw [hBsum.tsum_eq, hDsum]
    _ = M.twoRootVacuumPartitionCoefficient touches rootActivity *
        ((∑' n : ℕ,
            (M.augmentRoots touches rootActivity).twoRootMixedMayerDegreeSum n) +
          (∑' n : ℕ,
              (M.augmentRoots touches rootActivity).firstRootLinearMayerDegreeSum n) *
            ∑' n : ℕ,
              (M.augmentRoots touches rootActivity).secondRootLinearMayerDegreeSum n) := by
      congr 1
      congr 1
      · apply tsum_congr
        intro n
        exact M.coeff_mixedCoefficient_twoRootSourceMayerPowerSeries
          touches rootActivity n
      · congr 1
        · apply tsum_congr
          intro n
          exact M.coeff_linearCoefficient_first_twoRootSourceMayerPowerSeries
            touches rootActivity n
        · apply tsum_congr
          intro n
          exact M.coeff_linearCoefficient_second_twoRootSourceMayerPowerSeries
            touches rootActivity n

end FinitePolymerModel

end

end YangMills.Polymer
