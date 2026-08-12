/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.LabelledTreeSummation
import YangMills.Polymer.MayerPowerSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Fixed-labelled Mayer coefficients

This module removes the dependent occurrence type from the finite Mayer
exponential formula.  All degree-`n` objects live on the literal carrier
`Fin n`.  Histogram-orbit normalization then recovers the symmetric
multi-index coefficients, including the restriction to a finite polymer set.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

namespace FinitePolymerModel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Activity with polymers outside `S` switched off. -/
def restrictedActivity (M : FinitePolymerModel P) (S : Finset P)
    (γ : P) : ℂ :=
  if γ ∈ S then M.activity γ else 0

/-- Multiplicative activity weight of a fixed labelled tuple. -/
def labelledRestrictedActivityWeight (M : FinitePolymerModel P)
    (S : Finset P) {n : ℕ} (label : Fin n → P) : ℂ :=
  ∏ i : Fin n, M.restrictedActivity S (label i)

/-- A restricted histogram weight is the usual activity monomial when its
support lies in `S`, and vanishes otherwise. -/
theorem histogramWeight_restrictedActivity
    (M : FinitePolymerModel P) (S : Finset P) (X : MayerMultiIndex P) :
    histogramWeight (M.restrictedActivity S) X =
      if X.support ⊆ S then M.mayerActivityMonomial X else 0 := by
  classical
  by_cases hsupport : X.support ⊆ S
  · rw [if_pos hsupport, histogramWeight_eq_prod]
    unfold mayerActivityMonomial
    apply Finset.prod_congr rfl
    intro γ _
    by_cases hγ : γ ∈ S
    · simp [restrictedActivity, hγ]
    · have hx : X γ = 0 := by
        rw [← Finsupp.notMem_support_iff]
        exact fun hmem ↦ hγ (hsupport hmem)
      simp [restrictedActivity, hγ, hx]
  · rw [if_neg hsupport, histogramWeight_eq_prod]
    obtain ⟨γ, hγX, hγS⟩ := Finset.not_subset.mp hsupport
    apply Finset.prod_eq_zero (Finset.mem_univ γ)
    have hx : X γ ≠ 0 := Finsupp.mem_support_iff.mp hγX
    simp [restrictedActivity, hγS, hx]

/-- The labelled tuple activity product depends only on its histogram. -/
theorem labelledRestrictedActivityWeight_eq_histogramWeight
    (M : FinitePolymerModel P) (S : Finset P) {n : ℕ}
    (label : Fin n → P) :
    M.labelledRestrictedActivityWeight S label =
      histogramWeight (M.restrictedActivity S) (labelHistogram label) := by
  exact (histogramWeight_labelHistogram
    (M.restrictedActivity S) label).symm

/-- Unnormalized connected coefficient on the fixed carrier `Fin n`. -/
def labelledConnectedDegreeSum (M : FinitePolymerModel P)
    (S : Finset P) (n : ℕ) : ℂ :=
  ∑ label : Fin n → P,
    (connectedSpanningGraphSum
        (labelledIncompatibilityGraph M label) : ℂ) *
      M.labelledRestrictedActivityWeight S label

/-- Unnormalized compatibility moment on the fixed carrier `Fin n`.  The
signed sum over all spanning subgraphs is the inclusion--exclusion indicator
that the labelled incompatibility graph has no edges. -/
def labelledMomentDegreeSum (M : FinitePolymerModel P)
    (S : Finset P) (n : ℕ) : ℂ :=
  ∑ label : Fin n → P,
    (allSpanningGraphSum
        (labelledIncompatibilityGraph M label) : ℂ) *
      M.labelledRestrictedActivityWeight S label

/-- A Mayer occurrence graph is edgeless precisely when no label is repeated
and its support is a compatible polymer family. -/
theorem mayerIncompatibilityGraph_eq_bot_iff
    (M : FinitePolymerModel P) (X : MayerMultiIndex P) :
    M.mayerIncompatibilityGraph X = ⊥ ↔
      (∀ γ, X γ ≤ 1) ∧ M.Compatible X.support := by
  classical
  rw [SimpleGraph.eq_bot_iff_forall_not_adj]
  constructor
  · intro hno
    constructor
    · intro γ
      by_contra hle
      have htwo : 2 ≤ X γ := by omega
      let i : MayerVertex X := ⟨γ, ⟨0, by omega⟩⟩
      let j : MayerVertex X := ⟨γ, ⟨1, by omega⟩⟩
      have hij : i ≠ j := by
        intro h
        have := congrArg (fun v : MayerVertex X ↦ v.2.1) h
        change (0 : ℕ) = 1 at this
        omega
      exact hno i j ⟨hij, M.self_incompatible γ⟩
    · intro γ hγ δ hδ hγδ hinc
      have hγpos : 0 < X γ := by
        exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hγ)
      have hδpos : 0 < X δ := by
        exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hδ)
      let i : MayerVertex X := ⟨γ, ⟨0, hγpos⟩⟩
      let j : MayerVertex X := ⟨δ, ⟨0, hδpos⟩⟩
      have hij : i ≠ j := by
        intro h
        exact hγδ (congrArg Sigma.fst h)
      exact hno i j ⟨hij, hinc⟩
  · rintro ⟨hle, hcompat⟩ i j ⟨hij', hinc⟩
    by_cases hlabel : i.1 = j.1
    · apply hij'
      cases i with
      | mk γ a =>
        cases j with
        | mk δ b =>
          dsimp at hlabel ⊢
          subst δ
          congr
          apply Fin.ext
          have ha := a.2
          have hb := b.2
          have hγ := hle γ
          omega
    · have hiSupport : i.1 ∈ X.support := by
        rw [Finsupp.mem_support_iff]
        exact Nat.ne_of_gt
          (lt_of_le_of_lt (Nat.zero_le i.2.1) (Fin.is_lt i.2))
      have hjSupport : j.1 ∈ X.support := by
        rw [Finsupp.mem_support_iff]
        exact Nat.ne_of_gt
          (lt_of_le_of_lt (Nat.zero_le j.2.1) (Fin.is_lt j.2))
      exact hcompat hiSupport hjSupport hlabel hinc

/-- The multiplicity-one multi-index associated to a finite family. -/
def familyMultiIndex (Γ : Finset P) : MayerMultiIndex P :=
  Γ.1.toFinsupp

@[simp]
theorem familyMultiIndex_apply (Γ : Finset P) (γ : P) :
    familyMultiIndex Γ γ = if γ ∈ Γ then 1 else 0 := by
  change Multiset.count γ Γ.1 = if γ ∈ Γ then 1 else 0
  exact Multiset.count_eq_of_nodup Γ.2

@[simp]
theorem support_familyMultiIndex (Γ : Finset P) :
    (familyMultiIndex Γ).support = Γ := by
  simp [familyMultiIndex]

@[simp]
theorem mayerDegree_familyMultiIndex (Γ : Finset P) :
    mayerDegree (familyMultiIndex Γ) = Γ.card := by
  rw [← card_toMultiset_eq_mayerDegree]
  simp [familyMultiIndex]

@[simp]
theorem mayerSymmetryFactor_familyMultiIndex (Γ : Finset P) :
    mayerSymmetryFactor (familyMultiIndex Γ) = 1 := by
  classical
  unfold mayerSymmetryFactor
  apply Finset.prod_eq_one
  intro γ _
  rw [familyMultiIndex_apply]
  split_ifs <;> simp

@[simp]
theorem mayerActivityMonomial_familyMultiIndex
    (M : FinitePolymerModel P) (Γ : Finset P) :
    M.mayerActivityMonomial (familyMultiIndex Γ) = M.familyWeight Γ := by
  classical
  simp [mayerActivityMonomial, familyWeight, familyMultiIndex_apply]

@[simp]
theorem countPerms_familyMultiIndex (Γ : Finset P) :
    (familyMultiIndex Γ).toMultiset.countPerms = Γ.card.factorial := by
  have h := mayerSymmetryFactor_mul_countPerms (familyMultiIndex Γ)
  simpa using h

/-- Every multiplicity-one multi-index is recovered from its support. -/
theorem familyMultiIndex_support_eq_self
    (X : MayerMultiIndex P) (hle : ∀ γ, X γ ≤ 1) :
    familyMultiIndex X.support = X := by
  ext γ
  by_cases hγ : γ ∈ X.support
  · have hpos : 0 < X γ := Nat.pos_of_ne_zero
      (Finsupp.mem_support_iff.mp hγ)
    have hleγ := hle γ
    rw [familyMultiIndex_apply, if_pos hγ]
    omega
  · have hzero : X γ = 0 := Finsupp.notMem_support_iff.mp hγ
    simp [familyMultiIndex_apply, hγ, hzero]

/-- Degree-`n` multiplicity-one compatible multi-indices supported in `S`. -/
def simpleCompatibleMultiIndices (M : FinitePolymerModel P)
    (S : Finset P) (n : ℕ) : Finset (MayerMultiIndex P) :=
  (mayerMultiIndicesOfDegree (P := P) n).filter fun X ↦
    (∀ γ, X γ ≤ 1) ∧ M.Compatible X.support ∧ X.support ⊆ S

/-- Fixed-labelled compatibility moments regroup by multiplicity-one Mayer
histograms. -/
theorem labelledMomentDegreeSum_eq_simpleHistogramSum
    (M : FinitePolymerModel P) (S : Finset P) (n : ℕ) :
    M.labelledMomentDegreeSum S n =
      ∑ X ∈ M.simpleCompatibleMultiIndices S n,
        (X.toMultiset.countPerms : ℂ) * M.mayerActivityMonomial X := by
  classical
  unfold labelledMomentDegreeSum
  unfold labelledRestrictedActivityWeight
  simp_rw [← histogramWeight_labelHistogram]
  calc
    (∑ label : Fin n → P,
        (allSpanningGraphSum
            (labelledIncompatibilityGraph M label) : ℂ) *
          histogramWeight (M.restrictedActivity S)
            (labelHistogram label)) =
      ∑ label : Fin n → P,
        (allSpanningGraphSum
            (M.mayerIncompatibilityGraph (labelHistogram label)) : ℂ) *
          histogramWeight (M.restrictedActivity S)
            (labelHistogram label) := by
        apply Finset.sum_congr rfl
        intro label _
        rw [allSpanningGraphSum_eq_of_iso
          (labelledIncompatibilityGraphIso M label)]
    _ = ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        (X.toMultiset.countPerms : ℂ) *
          ((allSpanningGraphSum (M.mayerIncompatibilityGraph X) : ℂ) *
            histogramWeight (M.restrictedActivity S) X) := by
        exact sum_labelings_weight_eq_sum_countPerms_histogramWeight_complex
          n (fun X ↦
            (allSpanningGraphSum (M.mayerIncompatibilityGraph X) : ℂ) *
              histogramWeight (M.restrictedActivity S) X)
    _ = ∑ X ∈ M.simpleCompatibleMultiIndices S n,
        (X.toMultiset.countPerms : ℂ) * M.mayerActivityMonomial X := by
      unfold simpleCompatibleMultiIndices
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro X _
      rw [allSpanningGraphSum_eq_if,
        histogramWeight_restrictedActivity]
      by_cases hle : ∀ γ, X γ ≤ 1
      · by_cases hcompat : M.Compatible X.support
        · by_cases hsupport : X.support ⊆ S
          · rw [if_pos ((mayerIncompatibilityGraph_eq_bot_iff M X).mpr
                ⟨hle, hcompat⟩), if_pos hsupport]
            simp [hle, hcompat, hsupport]
          · rw [if_neg hsupport]
            simp [hle, hcompat, hsupport]
        · have hgraph : M.mayerIncompatibilityGraph X ≠ ⊥ := fun h ↦
            hcompat ((mayerIncompatibilityGraph_eq_bot_iff M X).mp h).2
          rw [if_neg hgraph]
          simp [hle, hcompat]
      · have hgraph : M.mayerIncompatibilityGraph X ≠ ⊥ := fun h ↦
          hle ((mayerIncompatibilityGraph_eq_bot_iff M X).mp h).1
        rw [if_neg hgraph]
        simp [hle]

/-- Multiplicity-one histograms are in weight-preserving bijection with
compatible families of the same cardinality. -/
theorem simpleHistogramSum_eq_factorial_mul_partitionDegreeCoefficient
    (M : FinitePolymerModel P) (S : Finset P) (n : ℕ) :
    (∑ X ∈ M.simpleCompatibleMultiIndices S n,
        (X.toMultiset.countPerms : ℂ) * M.mayerActivityMonomial X) =
      (n.factorial : ℂ) * M.partitionDegreeCoefficient S n := by
  classical
  unfold partitionDegreeCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_bij (fun X _ ↦ X.support)
  · intro X hX
    have hdata := Finset.mem_filter.mp hX
    have hdegree := (mem_mayerMultiIndicesOfDegree n X).mp hdata.1
    rcases hdata.2 with ⟨hle, hcompat, hsupport⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr hsupport, hcompat⟩
    · rw [← mayerDegree_familyMultiIndex X.support,
        familyMultiIndex_support_eq_self X hle]
      exact hdegree
  · intro X₁ hX₁ X₂ hX₂ hsupport
    have hle₁ := (Finset.mem_filter.mp hX₁).2.1
    have hle₂ := (Finset.mem_filter.mp hX₂).2.1
    rw [← familyMultiIndex_support_eq_self X₁ hle₁,
      ← familyMultiIndex_support_eq_self X₂ hle₂, hsupport]
  · intro Γ hΓ
    have hdata := Finset.mem_filter.mp hΓ
    have hfamily := Finset.mem_filter.mp hdata.1
    refine ⟨familyMultiIndex Γ, ?_, support_familyMultiIndex Γ⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_mayerMultiIndicesOfDegree n _).mpr
      simpa using hdata.2
    · refine ⟨?_, ?_, ?_⟩
      · intro γ
        rw [familyMultiIndex_apply]
        split_ifs <;> omega
      · simpa using hfamily.2
      · simpa using Finset.mem_powerset.mp hfamily.1
  · intro X hX
    have hdata := (Finset.mem_filter.mp hX).2
    rw [← familyMultiIndex_support_eq_self X hdata.1,
      countPerms_familyMultiIndex,
      mayerActivityMonomial_familyMultiIndex]
    have hdegree := (mem_mayerMultiIndicesOfDegree n X).mp
      (Finset.mem_filter.mp hX).1
    have hcard : X.support.card = n := by
      rw [← mayerDegree_familyMultiIndex X.support,
        familyMultiIndex_support_eq_self X hdata.1]
      exact hdegree
    rw [hcard]
    simp

/-- Exact labelled normalization of the finite partition coefficient. -/
theorem labelledMomentDegreeSum_div_factorial
    (M : FinitePolymerModel P) (S : Finset P) (n : ℕ) :
    M.labelledMomentDegreeSum S n / (n.factorial : ℂ) =
      M.partitionDegreeCoefficient S n := by
  rw [labelledMomentDegreeSum_eq_simpleHistogramSum,
    simpleHistogramSum_eq_factorial_mul_partitionDegreeCoefficient]
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  exact mul_div_cancel_left₀ (M.partitionDegreeCoefficient S n) hfac

/-- Exact unnormalized form of the labelled partition coefficient. -/
theorem labelledMomentDegreeSum_eq_factorial_mul_partitionDegreeCoefficient
    (M : FinitePolymerModel P) (S : Finset P) (n : ℕ) :
    M.labelledMomentDegreeSum S n =
      (n.factorial : ℂ) * M.partitionDegreeCoefficient S n := by
  rw [labelledMomentDegreeSum_eq_simpleHistogramSum,
    simpleHistogramSum_eq_factorial_mul_partitionDegreeCoefficient]

/-! ## Analytic jets of the finite partition polynomial -/

/-- The finite activity-graded partition function as an honest polynomial
function.  Its Taylor coefficients are `partitionDegreeCoefficient`. -/
def partitionGeneratingPolynomial (M : FinitePolymerModel P)
    (S : Finset P) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (S.card + 1),
    M.partitionDegreeCoefficient S k * z ^ k

@[simp]
theorem partitionGeneratingPolynomial_zero
    (M : FinitePolymerModel P) (S : Finset P) :
    M.partitionGeneratingPolynomial S 0 = 1 := by
  classical
  unfold partitionGeneratingPolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    simp [hk0]
  · simp

theorem contDiff_partitionGeneratingPolynomial
    (M : FinitePolymerModel P) (S : Finset P) :
    ContDiff ℂ ⊤ (M.partitionGeneratingPolynomial S) := by
  unfold partitionGeneratingPolynomial
  fun_prop

/-- The degree-`n` labelled moment is the `n`th derivative at zero of the
finite partition polynomial. -/
theorem iteratedDeriv_partitionGeneratingPolynomial_zero
    (M : FinitePolymerModel P) (S : Finset P) (n : ℕ) :
    iteratedDeriv n (M.partitionGeneratingPolynomial S) 0 =
      M.labelledMomentDegreeSum S n := by
  classical
  unfold partitionGeneratingPolynomial
  rw [iteratedDeriv_fun_sum]
  · by_cases hn : n ≤ S.card
    · rw [Finset.sum_eq_single n]
      · simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow,
          Nat.sub_self, pow_zero, mul_one, Nat.descFactorial_self]
        rw [labelledMomentDegreeSum_eq_factorial_mul_partitionDegreeCoefficient]
        ring
      · intro k hk hkn
        simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
        rcases lt_or_gt_of_ne hkn with hkn | hnk
        · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hkn]
          simp
        · have hsub : k - n ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hnk
          simp [hsub]
      · simp [hn]
    · have hcard : S.card < n := Nat.lt_of_not_ge hn
      rw [labelledMomentDegreeSum_eq_factorial_mul_partitionDegreeCoefficient,
        partitionDegreeCoefficient_eq_zero_of_card_lt M S hcard, mul_zero]
      apply Finset.sum_eq_zero
      intro k hk
      have hkcard : k ≤ S.card :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hkn : k < n := hkcard.trans_lt hcard
      simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hkn]
      simp
  · intro k hk
    fun_prop

/-- The positive-order derivatives of the principal complex logarithm at
one are the top-interval Möbius weights of the partition lattice. -/
theorem iteratedDeriv_complex_log_one (k : ℕ) (hk : 0 < k) :
    iteratedDeriv k Complex.log (1 : ℂ) =
      (partitionMobiusBlockWeight k : ℂ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  change iteratedDeriv (n + 1) Complex.log (1 : ℂ) =
    (partitionMobiusBlockWeight (n + 1) : ℂ)
  rw [iteratedDeriv_succ']
  have hderiv : deriv Complex.log =ᶠ[nhds (1 : ℂ)]
      fun z : ℂ ↦ 1 / z := by
    filter_upwards [Complex.isOpen_slitPlane.mem_nhds
      Complex.one_mem_slitPlane] with z hz
    simpa using (Complex.hasDerivAt_log hz).deriv
  rw [hderiv.iteratedDeriv_eq n]
  have h := iteratedDerivWithin_one_div (s := Set.univ) n
    (isOpen_univ : IsOpen (Set.univ : Set ℂ))
    (show (1 : ℂ) ∈ Set.univ by simp)
  simpa [iteratedDerivWithin_univ, partitionMobiusBlockWeight] using h

/-! ## Labelled set-partition cumulants -/

/-- Restricting a global labelling to every block of an ordered partition is
an equivalence with a dependent family of block labellings. -/
noncomputable def orderedFinpartitionLabelEquiv
    {n : ℕ} (c : OrderedFinpartition n) :
    (Fin n → P) ≃ (∀ i : Fin c.length, Fin (c.partSize i) → P) where
  toFun label i j := label (c.emb i j)
  invFun blockLabel v := blockLabel (c.index v) (c.invEmbedding v)
  left_inv label := by
    funext v
    simp
  right_inv blockLabel := by
    funext i j
    have h := c.equivSigma.left_inv ⟨i, j⟩
    exact congrArg (fun p : Σ i, Fin (c.partSize i) ↦
      blockLabel p.1 p.2) h

/-- Restricting a labelled incompatibility graph to a partition block is
the labelled graph of the restricted labelling. -/
theorem labelledIncompatibilityGraph_comap_orderedBlock
    (M : FinitePolymerModel P) {n : ℕ} (c : OrderedFinpartition n)
    (label : Fin n → P) (i : Fin c.length) :
    (labelledIncompatibilityGraph M label).comap (c.emb i) =
      labelledIncompatibilityGraph M (fun j ↦ label (c.emb i j)) := by
  ext v w
  change (c.emb i v ≠ c.emb i w ∧
      M.incompatible (label (c.emb i v)) (label (c.emb i w))) ↔
    (v ≠ w ∧ M.incompatible (label (c.emb i v)) (label (c.emb i w)))
  constructor
  · rintro ⟨hvw, hinc⟩
    exact ⟨fun h ↦ hvw (congrArg (c.emb i) h), hinc⟩
  · rintro ⟨hvw, hinc⟩
    exact ⟨(c.emb_strictMono i).injective.ne hvw, hinc⟩

/-- An ambient graph has no edge internal to a partition block exactly when
every fixed-carrier block restriction is edgeless. -/
theorem partitionEdgeFinset_eq_empty_iff_orderedBlocks_eq_bot
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : OrderedFinpartition n) :
    partitionEdgeFinset G (orderedFinpartitionToFinpartition c) = ∅ ↔
      ∀ i : Fin c.length, G.comap (c.emb i) = ⊥ := by
  classical
  let Q := orderedFinpartitionToFinpartition c
  constructor
  · intro hempty i
    rw [SimpleGraph.eq_bot_iff_forall_not_adj]
    intro v w hvw
    let edge : Sym2 (Fin n) := s(c.emb i v, c.emb i w)
    have hedgeG : edge ∈ G.edgeSet := by
      exact (SimpleGraph.mem_edgeSet G).mpr hvw
    have hblock : orderedFinpartitionBlock c i ∈ Q.parts := by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hvblock : c.emb i v ∈ orderedFinpartitionBlock c i := by
      exact (mem_orderedFinpartitionBlock c i _).mpr ⟨v, rfl⟩
    have hwblock : c.emb i w ∈ orderedFinpartitionBlock c i := by
      exact (mem_orderedFinpartitionBlock c i _).mpr ⟨w, rfl⟩
    have hpart : Q.part (c.emb i v) = Q.part (c.emb i w) := by
      rw [Q.part_eq_of_mem hblock hvblock,
        Q.part_eq_of_mem hblock hwblock]
    have hedge : edge ∈ partitionEdgeFinset G Q := by
      apply (mem_partitionEdgeFinset G Q edge).mpr
      exact ⟨hedgeG, hpart⟩
    rw [hempty] at hedge
    exact Finset.notMem_empty edge hedge
  · intro hblocks
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro edge hedge
    have hdata := (mem_partitionEdgeFinset G
      (orderedFinpartitionToFinpartition c) edge).mp hedge
    induction edge using Sym2.inductionOn with
    | _ v w =>
      have hvw : G.Adj v w := (SimpleGraph.mem_edgeSet G).mp hdata.1
      have hpart :
          (orderedFinpartitionToFinpartition c).part v =
            (orderedFinpartitionToFinpartition c).part w := hdata.2
      obtain ⟨i, a, hia⟩ := c.cover v
      have hblock : orderedFinpartitionBlock c i ∈
          (orderedFinpartitionToFinpartition c).parts := by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      have hvblock : v ∈ orderedFinpartitionBlock c i := by
        exact (mem_orderedFinpartitionBlock c i v).mpr ⟨a, hia⟩
      have hwpart :
          (orderedFinpartitionToFinpartition c).part w =
            orderedFinpartitionBlock c i := by
        rw [← hpart]
        exact (orderedFinpartitionToFinpartition c).part_eq_of_mem
          hblock hvblock
      have hwblock : w ∈ orderedFinpartitionBlock c i := by
        exact ((orderedFinpartitionToFinpartition c).part_eq_iff_mem
          hblock).mp hwpart
      obtain ⟨b, hib⟩ :=
        (mem_orderedFinpartitionBlock c i w).mp hwblock
      have hab : (G.comap (c.emb i)).Adj a b := by
        simpa [hia, hib] using hvw
      rw [hblocks i] at hab
      exact hab

/-- The product of block inclusion--exclusion indicators is the indicator
that no ambient edge lies inside any partition block. -/
theorem prod_allSpanningGraphSum_orderedBlocks
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : OrderedFinpartition n) :
    (∏ i : Fin c.length,
      (allSpanningGraphSum (G.comap (c.emb i)) : ℂ)) =
        if partitionEdgeFinset G (orderedFinpartitionToFinpartition c) = ∅
        then 1 else 0 := by
  classical
  simp_rw [allSpanningGraphSum_eq_if]
  by_cases hblocks : ∀ i : Fin c.length, G.comap (c.emb i) = ⊥
  · have hedge :=
      (partitionEdgeFinset_eq_empty_iff_orderedBlocks_eq_bot G c).mpr hblocks
    simp [hblocks, hedge]
  · have hedge :=
      (partitionEdgeFinset_eq_empty_iff_orderedBlocks_eq_bot G c).not.mpr
        hblocks
    obtain ⟨i, hi⟩ := not_forall.mp hblocks
    rw [if_neg hedge]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- For one ordered partition, summing the factorized block moments over all
global labels is the product of the independent labelled moment sums. -/
theorem sum_labelings_partitionMoment_eq_prod_labelledMomentDegreeSum
    (M : FinitePolymerModel P) (S : Finset P) {n : ℕ}
    (c : OrderedFinpartition n) :
    (∑ label : Fin n → P,
      ((if partitionEdgeFinset (labelledIncompatibilityGraph M label)
          (orderedFinpartitionToFinpartition c) = ∅ then 1 else 0) : ℂ) *
        M.labelledRestrictedActivityWeight S label) =
      ∏ i : Fin c.length,
        M.labelledMomentDegreeSum S (c.partSize i) := by
  classical
  let blockWeight := fun (i : Fin c.length)
      (label : Fin (c.partSize i) → P) ↦
    (allSpanningGraphSum
        (labelledIncompatibilityGraph M label) : ℂ) *
      M.labelledRestrictedActivityWeight S label
  calc
    (∑ label : Fin n → P,
      ((if partitionEdgeFinset (labelledIncompatibilityGraph M label)
          (orderedFinpartitionToFinpartition c) = ∅ then 1 else 0) : ℂ) *
        M.labelledRestrictedActivityWeight S label) =
      ∑ label : Fin n → P,
        ∏ i : Fin c.length,
          blockWeight i (fun j ↦ label (c.emb i j)) := by
        apply Finset.sum_congr rfl
        intro label _
        unfold blockWeight
        rw [Finset.prod_mul_distrib]
        have hgraph :
            (∏ i : Fin c.length,
              (allSpanningGraphSum
                (labelledIncompatibilityGraph M
                  (fun j ↦ label (c.emb i j))) : ℂ)) =
              ∏ i : Fin c.length,
                (allSpanningGraphSum
                  ((labelledIncompatibilityGraph M label).comap
                    (c.emb i)) : ℂ) := by
          apply Finset.prod_congr rfl
          intro i _
          rw [labelledIncompatibilityGraph_comap_orderedBlock]
        rw [hgraph, prod_allSpanningGraphSum_orderedBlocks]
        unfold labelledRestrictedActivityWeight
        rw [← c.prod_sigma_eq_prod]
    _ = ∑ blockLabel : ∀ i : Fin c.length,
          Fin (c.partSize i) → P,
        ∏ i : Fin c.length, blockWeight i (blockLabel i) := by
          exact Fintype.sum_equiv (orderedFinpartitionLabelEquiv c)
            _ _ (fun _ ↦ rfl)
    _ = ∏ i : Fin c.length,
        ∑ label : Fin (c.partSize i) → P, blockWeight i label := by
          rw [Fintype.prod_sum]
    _ = ∏ i : Fin c.length,
        M.labelledMomentDegreeSum S (c.partSize i) := by
          rfl

/-- Möbius cumulant of the fixed-labelled compatibility moments. -/
def labelledMomentCumulant (M : FinitePolymerModel P)
    (S : Finset P) : ℕ → ℂ
  | 0 => 0
  | n + 1 =>
      ∑ c : OrderedFinpartition (n + 1),
        (partitionMobiusBlockWeight c.length : ℂ) *
          ∏ i : Fin c.length,
            M.labelledMomentDegreeSum S (c.partSize i)

/-- Faà di Bruno identifies the labelled moment cumulant with the Taylor
jet of the logarithm of the finite partition polynomial. -/
theorem iteratedDeriv_log_partitionGeneratingPolynomial_zero
    (M : FinitePolymerModel P) (S : Finset P) (n : ℕ) :
    iteratedDeriv n
        (Complex.log ∘ M.partitionGeneratingPolynomial S) 0 =
      M.labelledMomentCumulant S n := by
  classical
  cases n with
  | zero => simp [labelledMomentCumulant]
  | succ n =>
      have hlog : ContDiffAt ℂ ⊤ Complex.log
          (M.partitionGeneratingPolynomial S 0) := by
        rw [M.partitionGeneratingPolynomial_zero S]
        exact Complex.contDiffAt_log Complex.one_mem_slitPlane
      have hpoly : ContDiffAt ℂ ⊤
          (M.partitionGeneratingPolynomial S) 0 :=
        (M.contDiff_partitionGeneratingPolynomial S).contDiffAt
      change iteratedDeriv (n + 1)
          (Complex.log ∘ M.partitionGeneratingPolynomial S) 0 = _
      rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hlog hpoly (by simp)]
      unfold labelledMomentCumulant
      apply Finset.sum_congr rfl
      intro c _
      rw [M.partitionGeneratingPolynomial_zero S,
        iteratedDeriv_complex_log_one c.length (c.length_pos (by omega))]
      apply congrArg ((partitionMobiusBlockWeight c.length : ℂ) * ·)
      apply Finset.prod_congr rfl
      intro i _
      exact M.iteratedDeriv_partitionGeneratingPolynomial_zero S
        (c.partSize i)

/-- The connected signed graph sum is exactly the Möbius cumulant of the
fixed-labelled compatibility moments. -/
theorem labelledConnectedDegreeSum_eq_labelledMomentCumulant
    (M : FinitePolymerModel P) (S : Finset P) (n : ℕ) :
    M.labelledConnectedDegreeSum S n = M.labelledMomentCumulant S n := by
  classical
  cases n with
  | zero =>
      unfold labelledConnectedDegreeSum labelledMomentCumulant
      apply Finset.sum_eq_zero
      intro label _
      have hnot :
          ¬(labelledIncompatibilityGraph M label).Connected := by
        intro h
        exact not_nonempty_iff.mpr inferInstance h.nonempty
      rw [connectedSpanningGraphSum_eq_zero_of_not_connected hnot]
      simp
  | succ n =>
      unfold labelledConnectedDegreeSum labelledMomentCumulant
      simp_rw [connectedSpanningGraphSum_eq_partitionMobius_cancellation]
      push_cast
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      rw [← (orderedFinpartitionEquivFinpartition (n + 1)).sum_comp]
      apply Finset.sum_congr rfl
      intro c _
      change
        (∑ label : Fin (n + 1) → P,
          (partitionMobiusBlockWeight
              (orderedFinpartitionToFinpartition c).parts.card : ℂ) *
            (if partitionEdgeFinset
                (labelledIncompatibilityGraph M label)
                (orderedFinpartitionToFinpartition c) = ∅ then 1 else 0) *
              M.labelledRestrictedActivityWeight S label) =
          (partitionMobiusBlockWeight c.length : ℂ) *
            ∏ i : Fin c.length,
              M.labelledMomentDegreeSum S (c.partSize i)
      rw [card_parts_orderedFinpartitionToFinpartition]
      calc
        (∑ label : Fin (n + 1) → P,
            (partitionMobiusBlockWeight c.length : ℂ) *
              (if partitionEdgeFinset
                  (labelledIncompatibilityGraph M label)
                  (orderedFinpartitionToFinpartition c) = ∅ then 1 else 0) *
                M.labelledRestrictedActivityWeight S label) =
            (partitionMobiusBlockWeight c.length : ℂ) *
              ∑ label : Fin (n + 1) → P,
                ((if partitionEdgeFinset
                    (labelledIncompatibilityGraph M label)
                    (orderedFinpartitionToFinpartition c) = ∅ then 1 else 0) : ℂ) *
                  M.labelledRestrictedActivityWeight S label := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro label _
              ring
        _ = (partitionMobiusBlockWeight c.length : ℂ) *
            ∏ i : Fin c.length,
              M.labelledMomentDegreeSum S (c.partSize i) := by
              rw [sum_labelings_partitionMoment_eq_prod_labelledMomentDegreeSum]

/-- The labelled moments and connected coefficients satisfy the exact
logarithmic-derivative convolution. -/
theorem labelledMoment_connected_convolution
    (M : FinitePolymerModel P) (S : Finset P) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * M.labelledMomentDegreeSum S i *
          M.labelledConnectedDegreeSum S (n - i + 1) =
      M.labelledMomentDegreeSum S (n + 1) := by
  let f := M.partitionGeneratingPolynomial S
  let h := Complex.log ∘ f
  have hf : ContDiffAt ℂ ⊤ f 0 :=
    (M.contDiff_partitionGeneratingPolynomial S).contDiffAt
  have hlog : ContDiffAt ℂ ⊤ Complex.log (f 0) := by
    change ContDiffAt ℂ ⊤ Complex.log
      (M.partitionGeneratingPolynomial S 0)
    rw [M.partitionGeneratingPolynomial_zero S]
    exact Complex.contDiffAt_log Complex.one_mem_slitPlane
  have hh : ContDiffAt ℂ ⊤ h 0 := hlog.comp 0 hf
  have hdh : ContDiffAt ℂ ⊤ (deriv h) 0 :=
    hh.derivWithin (by simp)
  have hslit : ∀ᶠ z in nhds (0 : ℂ), f z ∈ Complex.slitPlane := by
    have hfcont : ContinuousAt f 0 := hf.continuousAt
    apply hfcont.eventually (Complex.isOpen_slitPlane.mem_nhds ?_)
    change M.partitionGeneratingPolynomial S 0 ∈ Complex.slitPlane
    rw [M.partitionGeneratingPolynomial_zero S]
    exact Complex.one_mem_slitPlane
  have hprod : f * deriv h =ᶠ[nhds (0 : ℂ)] deriv f := by
    filter_upwards [hslit] with z hz
    have hfdiff : DifferentiableAt ℂ f z := by
      exact ((M.contDiff_partitionGeneratingPolynomial S).differentiable
        (by simp)) z
    have hderiv := Complex.deriv_log_comp_eq_logDeriv hfdiff hz
    change f z * deriv h z = deriv f z
    rw [hderiv]
    unfold logDeriv
    change f z * (deriv f z / f z) = deriv f z
    have hfne : f z ≠ 0 := Complex.slitPlane_ne_zero hz
    field_simp
  have hjets := hprod.iteratedDeriv_eq n
  rw [iteratedDeriv_mul (hf.of_le (by simp)) (hdh.of_le (by simp))]
    at hjets
  rw [← iteratedDeriv_succ'] at hjets
  have hshift (j : ℕ) :
      iteratedDeriv j (deriv h) 0 = iteratedDeriv (j + 1) h 0 := by
    exact (congrFun (iteratedDeriv_succ' (n := j) (f := h)) 0).symm
  simp_rw [hshift] at hjets
  change (∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℂ) * iteratedDeriv i f 0 *
        iteratedDeriv (n - i + 1) h 0) =
    iteratedDeriv (n + 1) f 0 at hjets
  simpa [f, h, M.iteratedDeriv_partitionGeneratingPolynomial_zero,
    M.iteratedDeriv_log_partitionGeneratingPolynomial_zero,
    M.labelledConnectedDegreeSum_eq_labelledMomentCumulant] using hjets

/-- Fixed-labelled connected sums regroup exactly by Mayer histograms. -/
theorem labelledConnectedDegreeSum_eq_histogramSum
    (M : FinitePolymerModel P) (S : Finset P) (n : ℕ) :
    M.labelledConnectedDegreeSum S n =
      ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        (X.toMultiset.countPerms : ℂ) *
          ((M.mayerUrsell X : ℂ) *
            histogramWeight (M.restrictedActivity S) X) := by
  classical
  unfold labelledConnectedDegreeSum
  simp_rw [connectedSpanningGraphSum_labelledIncompatibilityGraph,
    labelledRestrictedActivityWeight_eq_histogramWeight]
  exact sum_labelings_weight_eq_sum_countPerms_histogramWeight_complex
    n (fun X ↦ (M.mayerUrsell X : ℂ) *
      histogramWeight (M.restrictedActivity S) X)

/-- Dividing the fixed-labelled connected degree sum by `n!` gives exactly
the restricted symmetric Mayer coefficient. -/
theorem labelledConnectedDegreeSum_div_factorial
    (M : FinitePolymerModel P) (S : Finset P) (n : ℕ) :
    M.labelledConnectedDegreeSum S n / (n.factorial : ℂ) =
      M.restrictedSymmetricMayerCoefficient S n := by
  classical
  cases n with
  | zero =>
      unfold labelledConnectedDegreeSum
      rw [show (∑ label : Fin 0 → P,
          (connectedSpanningGraphSum
              (labelledIncompatibilityGraph M label) : ℂ) *
            M.labelledRestrictedActivityWeight S label) = 0 by
        apply Finset.sum_eq_zero
        intro label _
        have hnot :
            ¬(labelledIncompatibilityGraph M label).Connected := by
          intro h
          exact not_nonempty_iff.mpr inferInstance h.nonempty
        rw [connectedSpanningGraphSum_eq_zero_of_not_connected hnot]
        simp]
      simp [restrictedSymmetricMayerCoefficient]
  | succ n =>
      rw [labelledConnectedDegreeSum_eq_histogramSum, Finset.sum_div]
      calc
        (∑ X ∈ mayerMultiIndicesOfDegree (P := P) (n + 1),
            (X.toMultiset.countPerms : ℂ) *
                ((M.mayerUrsell X : ℂ) *
                  histogramWeight (M.restrictedActivity S) X) /
              ((n + 1).factorial : ℂ)) =
            ∑ X ∈ mayerMultiIndicesOfDegree (P := P) (n + 1),
              ((X.toMultiset.countPerms : ℂ) /
                  ((n + 1).factorial : ℂ)) *
                ((M.mayerUrsell X : ℂ) *
                  histogramWeight (M.restrictedActivity S) X) := by
              apply Finset.sum_congr rfl
              intro X _
              ring
        _ = ∑ X ∈ mayerMultiIndicesOfDegree (P := P) (n + 1),
              ((M.mayerUrsell X : ℂ) *
                histogramWeight (M.restrictedActivity S) X) /
                  (mayerSymmetryFactor X : ℂ) :=
            sum_countPerms_div_factorial_eq_sum_div_mayerSymmetryFactor
              (n + 1) (fun X ↦ (M.mayerUrsell X : ℂ) *
                histogramWeight (M.restrictedActivity S) X)
        _ = ∑ X ∈ (mayerMultiIndicesOfDegree (P := P) (n + 1)).filter
                (fun X ↦ X.support ⊆ S),
              M.mayerClusterTerm X := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro X _
            rw [histogramWeight_restrictedActivity]
            by_cases hsupport : X.support ⊆ S
            · rw [if_pos hsupport, if_pos hsupport]
              unfold mayerClusterTerm
              ring
            · rw [if_neg hsupport, if_neg hsupport]
              simp
        _ = M.restrictedSymmetricMayerCoefficient S (n + 1) := rfl

/-- Coefficient form of fixed-labelled/symmetric normalization. -/
theorem coeff_restrictedSymmetricMayerPowerSeries
    (M : FinitePolymerModel P) (S : Finset P) (n : ℕ) :
    PowerSeries.coeff n (M.restrictedSymmetricMayerPowerSeries S) =
      M.labelledConnectedDegreeSum S n / (n.factorial : ℂ) := by
  rw [restrictedSymmetricMayerPowerSeries, PowerSeries.coeff_mk,
    labelledConnectedDegreeSum_div_factorial]

/-- Coefficientwise logarithmic differential equation for the restricted
connected series. -/
theorem partitionPowerSeries_mul_derivative_restrictedSymmetricMayerPowerSeries
    (M : FinitePolymerModel P) (S : Finset P) :
    M.partitionPowerSeries S *
        PowerSeries.derivative ℂ (M.restrictedSymmetricMayerPowerSeries S) =
      PowerSeries.derivative ℂ (M.partitionPowerSeries S) := by
  ext n
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ PowerSeries.coeff i (M.partitionPowerSeries S) *
        PowerSeries.coeff j
          (PowerSeries.derivative ℂ
            (M.restrictedSymmetricMayerPowerSeries S))) n]
  simp_rw [PowerSeries.coeff_derivative,
    coeff_restrictedSymmetricMayerPowerSeries,
    coeff_partitionPowerSeries,
    ← labelledMomentDegreeSum_div_factorial]
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  apply mul_left_cancel₀ hfac
  calc
    (n.factorial : ℂ) *
        ∑ i ∈ Finset.range (n + 1),
          (M.labelledMomentDegreeSum S i / (i.factorial : ℂ)) *
            (M.labelledConnectedDegreeSum S (n - i + 1) /
                ((n - i + 1).factorial : ℂ) *
              (((n - i : ℕ) : ℂ) + 1)) =
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * M.labelledMomentDegreeSum S i *
          M.labelledConnectedDegreeSum S (n - i + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i ≤ n :=
          Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hchooseNat := Nat.choose_mul_factorial_mul_factorial hin
        have hchoose :
            (n.choose i : ℂ) * (i.factorial : ℂ) *
                ((n - i).factorial : ℂ) = (n.factorial : ℂ) := by
          exact_mod_cast hchooseNat
        rw [Nat.factorial_succ]
        push_cast
        have hiFac : (i.factorial : ℂ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero i
        have hniFac : ((n - i).factorial : ℂ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero (n - i)
        have hsucc : (((n - i : ℕ) : ℂ) + 1) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero (n - i)
        have hsucc' : (n : ℂ) - (i : ℂ) + 1 ≠ 0 := by
          rw [← Nat.cast_sub hin]
          exact hsucc
        field_simp [hiFac, hniFac, hsucc, hsucc']
        ring_nf at hchoose ⊢
        rw [hchoose]
    _ = M.labelledMomentDegreeSum S (n + 1) :=
      M.labelledMoment_connected_convolution S n
    _ = (n.factorial : ℂ) *
        (M.labelledMomentDegreeSum S (n + 1) /
            ((n + 1).factorial : ℂ) * ((n : ℂ) + 1)) := by
      rw [Nat.factorial_succ]
      push_cast
      have hsucc : ((n : ℂ) + 1) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      field_simp

/-- The finite symmetric Mayer sum is exactly the canonical formal logarithm
of the finite partition power series.  This is the finite-volume linked
cluster theorem in the symmetric multi-index normalization. -/
theorem restrictedSymmetricMayerPowerSeries_eq_formalMayerLog
    (M : FinitePolymerModel P) (S : Finset P) :
    M.restrictedSymmetricMayerPowerSeries S = M.formalMayerLog S := by
  let A := M.partitionPowerSeries S
  let C := M.restrictedSymmetricMayerPowerSeries S
  have hAc : PowerSeries.constantCoeff A = 1 :=
    M.constantCoeff_partitionPowerSeries S
  have hAne : PowerSeries.constantCoeff A ≠ 0 := by simp [hAc]
  have hrel : A * PowerSeries.derivative ℂ C =
      PowerSeries.derivative ℂ A := by
    exact M.partitionPowerSeries_mul_derivative_restrictedSymmetricMayerPowerSeries S
  apply PowerSeries.derivative.ext
  · change PowerSeries.derivative ℂ C =
        PowerSeries.derivative ℂ (PowerSeries.logOf A)
    rw [PowerSeriesBridge.derivative_logOf hAc]
    calc
      PowerSeries.derivative ℂ C =
          1 * PowerSeries.derivative ℂ C := by rw [one_mul]
      _ = (A⁻¹ * A) * PowerSeries.derivative ℂ C := by
        rw [PowerSeries.inv_mul_cancel A hAne]
      _ = A⁻¹ * (A * PowerSeries.derivative ℂ C) := by
        rw [mul_assoc]
      _ = A⁻¹ * PowerSeries.derivative ℂ A := by rw [hrel]
  · change PowerSeries.constantCoeff C =
        PowerSeries.constantCoeff (PowerSeries.logOf A)
    rw [PowerSeries.constantCoeff_logOf hAc]
    exact M.constantCoeff_restrictedSymmetricMayerPowerSeries S

end FinitePolymerModel

end

end YangMills.Polymer
