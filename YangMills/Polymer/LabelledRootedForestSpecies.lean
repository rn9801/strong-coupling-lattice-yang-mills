/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.LabelledTreeSummation
import YangMills.Polymer.WeightedOrderedPartition

/-!
# Fixed-labelled rooted forests as a weighted set species

This file closes the finite combinatorial bridge in the KP proof.  A rooted
labelled spanning tree is cut at its distinguished root.  Its residual
components are transported to literal carriers `Fin s`, canonically ordered,
and equipped with their unique root attachment.  The encoding is injective
because the block labels, block graphs, and attachments have explicit
reconstruction maps.

The resulting finite-degree sum is a weighted `OrderedFinpartition` sum, so
`WeightedOrderedPartition` supplies its factorially normalized exponential
bound.
-/

namespace YangMills.Polymer

open SimpleGraph
open scoped BigOperators

noncomputable section

namespace FinitePolymerModel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- A residual fixed label tuple together with a rooted spanning tree. -/
def FixedLabelledRootedTree (M : FinitePolymerModel P)
    (root : P) (n : ℕ) :=
  Σ label : Fin n → P,
    {T : SimpleGraph (Option (Fin n)) //
      T ∈ graphSpanningTrees (labelledIncompatibilityGraph M
        (fixedRootedMayerLabel root label))}

/-- A labelled component tree and one allowed attachment to its parent. -/
def LabelledAttachedTreeChoice (M : FinitePolymerModel P)
    (root : P) (s : ℕ) :=
  Σ label : Fin s → P,
    {T : SimpleGraph (Fin s) //
      T ∈ graphSpanningTrees (labelledIncompatibilityGraph M label)} ×
    {j : Fin s // M.incompatible root (label j)}

/-- An unordered rooted forest represented by canonically ordered blocks. -/
def FixedLabelledRootedForestCode (M : FinitePolymerModel P)
    (root : P) (n : ℕ) :=
  Σ c : OrderedFinpartition n,
    ∀ i : Fin c.length,
      M.LabelledAttachedTreeChoice root (c.partSize i)

local instance fixedLabelledRootedTreeFintype
    (M : FinitePolymerModel P) (root : P) (n : ℕ) :
    Fintype (M.FixedLabelledRootedTree root n) := by
  classical
  unfold FixedLabelledRootedTree
  infer_instance

local instance labelledAttachedTreeChoiceFintype
    (M : FinitePolymerModel P) (root : P) (s : ℕ) :
    Fintype (M.LabelledAttachedTreeChoice root s) := by
  classical
  unfold LabelledAttachedTreeChoice
  infer_instance

local instance fixedLabelledRootedForestCodeFintype
    (M : FinitePolymerModel P) (root : P) (n : ℕ) :
    Fintype (M.FixedLabelledRootedForestCode root n) := by
  classical
  unfold FixedLabelledRootedForestCode
  infer_instance

/-- Canonical fixed-carrier forest code of a rooted labelled tree. -/
def fixedLabelledRootedTreeToForestCode
    (M : FinitePolymerModel P) (root : P) {n : ℕ}
    (x : M.FixedLabelledRootedTree root n) :
    M.FixedLabelledRootedForestCode root n := by
  let label := x.1
  let T := x.2.1
  have hdata : T ≤ labelledIncompatibilityGraph M
      (fixedRootedMayerLabel root label) ∧ T.IsTree := by
    have hx := x.2.2
    have hx' : T ∈ spanningTreeGraphs (labelledIncompatibilityGraph M
        (fixedRootedMayerLabel root label)) := by
      simpa only [graphSpanningTrees_eq_spanningTreeGraphs] using hx
    exact (mem_spanningTreeGraphs _ _).mp hx'
  refine ⟨orderedAwayComponentPartition T, fun i ↦ ?_⟩
  refine ⟨orderedAwayComponentLabel label T i,
    ⟨orderedAwayComponentGraph T i, ?_⟩,
    ⟨orderedAwayChildRootIndex hdata.2 i, ?_⟩⟩
  · exact M.orderedAwayComponentGraph_mem_graphSpanningTrees
      root label hdata.2 hdata.1 i
  · exact M.incompatible_orderedAwayChildRootLabel
      root label hdata.2 hdata.1 i

/-- Forget proofs and reconstruct the global label and rooted graph from a
forest code. -/
def fixedLabelledRootedForestCodeDecode
    (M : FinitePolymerModel P) (root : P) {n : ℕ}
    (x : M.FixedLabelledRootedForestCode root n) :
    (Fin n → P) × SimpleGraph (Option (Fin n)) :=
  (assembleOrderedComponentLabels x.1 (fun i ↦ (x.2 i).1),
    graphOfFixedRootData
      (assembleOrderedComponentGraphs x.1 (fun i ↦ (x.2 i).2.1.1))
      (assembleOrderedComponentAttachments x.1
        (fun i ↦ (x.2 i).2.2.1)))

/-- Decoding the canonical code recovers both the label tuple and the rooted
tree exactly. -/
theorem fixedLabelledRootedForestCodeDecode_encode
    (M : FinitePolymerModel P) (root : P) {n : ℕ}
    (x : M.FixedLabelledRootedTree root n) :
    M.fixedLabelledRootedForestCodeDecode root
        (M.fixedLabelledRootedTreeToForestCode root x) =
      (x.1, x.2.1) := by
  classical
  have hdata : x.2.1.IsTree := by
    have hx := x.2.2
    have hx' : x.2.1 ∈ spanningTreeGraphs
        (labelledIncompatibilityGraph M
          (fixedRootedMayerLabel root x.1)) := by
      simpa only [graphSpanningTrees_eq_spanningTreeGraphs] using hx
    exact (mem_spanningTreeGraphs _ _).mp hx' |>.2
  apply Prod.ext
  · exact assemble_orderedComponentLabels
      (orderedAwayComponentPartition x.2.1) x.1
  · simp only [fixedLabelledRootedForestCodeDecode,
      fixedLabelledRootedTreeToForestCode]
    rw [show assembleOrderedComponentGraphs
        (orderedAwayComponentPartition x.2.1)
          (fun i ↦ orderedAwayComponentGraph x.2.1 i) =
        awayGraphOnFin x.2.1 by
          exact assemble_orderedComponentGraphs (awayGraphOnFin x.2.1)]
    rw [assemble_orderedAwayChildRootIndices hdata,
      graphOfFixedRootData_fixedRootData]

/-- The canonical rooted-forest encoding is injective. -/
theorem fixedLabelledRootedTreeToForestCode_injective
    (M : FinitePolymerModel P) (root : P) {n : ℕ} :
    Function.Injective
      (M.fixedLabelledRootedTreeToForestCode root :
        M.FixedLabelledRootedTree root n →
          M.FixedLabelledRootedForestCode root n) := by
  intro x y hxy
  have hdecode := congrArg
    (M.fixedLabelledRootedForestCodeDecode root) hxy
  rw [M.fixedLabelledRootedForestCodeDecode_encode root x,
    M.fixedLabelledRootedForestCodeDecode_encode root y] at hdecode
  cases x with
  | mk labelX treeX =>
      cases y with
      | mk labelY treeY =>
          simp only [Prod.mk.injEq] at hdecode
          cases hdecode.1
          have htree : treeX = treeY := Subtype.ext hdecode.2
          cases htree
          rfl

/-- Activity weight carried by a fixed-labelled rooted spanning tree.  The
tree itself contributes only multiplicity; all analytic weight is on the
residual labels. -/
def fixedLabelledRootedTreeWeight
    (M : FinitePolymerModel P) (root : P) {n : ℕ}
    (x : M.FixedLabelledRootedTree root n) : ℝ :=
  ∏ j : Fin n, ‖M.activity (x.1 j)‖

/-- Activity weight of one labelled component/tree/attachment choice. -/
def labelledAttachedTreeChoiceWeight
    (M : FinitePolymerModel P) (root : P) {s : ℕ}
    (x : M.LabelledAttachedTreeChoice root s) : ℝ :=
  ∏ j : Fin s, ‖M.activity (x.1 j)‖

/-- Product weight of an ordered rooted-forest code. -/
def fixedLabelledRootedForestCodeWeight
    (M : FinitePolymerModel P) (root : P) {n : ℕ}
    (x : M.FixedLabelledRootedForestCode root n) : ℝ :=
  ∏ i : Fin x.1.length,
    M.labelledAttachedTreeChoiceWeight root (x.2 i)

theorem fixedLabelledRootedTreeWeight_nonneg
    (M : FinitePolymerModel P) (root : P) {n : ℕ}
    (x : M.FixedLabelledRootedTree root n) :
    0 ≤ M.fixedLabelledRootedTreeWeight root x := by
  exact Finset.prod_nonneg fun _ _ ↦ norm_nonneg _

theorem labelledAttachedTreeChoiceWeight_nonneg
    (M : FinitePolymerModel P) (root : P) {s : ℕ}
    (x : M.LabelledAttachedTreeChoice root s) :
    0 ≤ M.labelledAttachedTreeChoiceWeight root x := by
  exact Finset.prod_nonneg fun _ _ ↦ norm_nonneg _

theorem fixedLabelledRootedForestCodeWeight_nonneg
    (M : FinitePolymerModel P) (root : P) {n : ℕ}
    (x : M.FixedLabelledRootedForestCode root n) :
    0 ≤ M.fixedLabelledRootedForestCodeWeight root x := by
  exact Finset.prod_nonneg fun i _ ↦
    M.labelledAttachedTreeChoiceWeight_nonneg root (x.2 i)

/-- Cutting at the distinguished root preserves the full activity weight. -/
theorem fixedLabelledRootedTreeToForestCode_weight
    (M : FinitePolymerModel P) (root : P) {n : ℕ}
    (x : M.FixedLabelledRootedTree root n) :
    M.fixedLabelledRootedForestCodeWeight root
        (M.fixedLabelledRootedTreeToForestCode root x) =
      M.fixedLabelledRootedTreeWeight root x := by
  classical
  exact M.prod_orderedAwayComponentLabel_norm_activity x.1 x.2.1

/-- Summing the fixed-tree species merely counts the spanning trees for each
residual label tuple. -/
theorem sum_fixedLabelledRootedTreeWeight
    (M : FinitePolymerModel P) (root : P) (n : ℕ) :
    (∑ x : M.FixedLabelledRootedTree root n,
      M.fixedLabelledRootedTreeWeight root x) =
    ∑ label : Fin n → P, M.labelledPinnedTreeWeight root label := by
  classical
  let e : M.FixedLabelledRootedTree root n ≃
      Σ label : Fin n → P,
        {T : SimpleGraph (Option (Fin n)) //
          T ∈ graphSpanningTrees (labelledIncompatibilityGraph M
            (fixedRootedMayerLabel root label))} := Equiv.refl _
  calc
    (∑ x : M.FixedLabelledRootedTree root n,
        M.fixedLabelledRootedTreeWeight root x) =
      ∑ q : Σ label : Fin n → P,
          {T : SimpleGraph (Option (Fin n)) //
            T ∈ graphSpanningTrees (labelledIncompatibilityGraph M
              (fixedRootedMayerLabel root label))},
        ∏ j : Fin n, ‖M.activity (q.1 j)‖ := by
          exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
    _ = ∑ label : Fin n → P,
        ∑ _T : {T : SimpleGraph (Option (Fin n)) //
            T ∈ graphSpanningTrees (labelledIncompatibilityGraph M
              (fixedRootedMayerLabel root label))},
          ∏ j : Fin n, ‖M.activity (label j)‖ := by
      exact Fintype.sum_sigma' (fun (label : Fin n → P)
          (_T : {T : SimpleGraph (Option (Fin n)) //
            T ∈ graphSpanningTrees (labelledIncompatibilityGraph M
              (fixedRootedMayerLabel root label))}) ↦
        ∏ j : Fin n, ‖M.activity (label j)‖)
    _ = ∑ label : Fin n → P,
        M.labelledPinnedTreeWeight root label := by
      apply Finset.sum_congr rfl
      intro label _
      unfold labelledPinnedTreeWeight
      simp

/-- For one fixed label tuple, summing over its component spanning trees and
allowed parent attachments gives the attached-component weight. -/
theorem sum_labelledAttachedTreeChoiceWeight_fiber
    (M : FinitePolymerModel P) (root : P) (s : ℕ)
    (label : Fin s → P) :
    (∑ _x :
        {T : SimpleGraph (Fin s) //
          T ∈ graphSpanningTrees (labelledIncompatibilityGraph M label)} ×
        {j : Fin s // M.incompatible root (label j)},
      ∏ j : Fin s, ‖M.activity (label j)‖) =
      M.labelledAttachedComponentWeight root label := by
  classical
  unfold labelledAttachedComponentWeight
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_coe, nsmul_eq_mul, Nat.cast_mul]
  rw [Fintype.card_subtype]
  rw [← Finset.sum_filter]
  simp
  ring

/-- The total weight of the explicit component/tree/attachment choices is
exactly the previously defined attached-component mass. -/
theorem sum_labelledAttachedTreeChoiceWeight
    (M : FinitePolymerModel P) (root : P) (s : ℕ) :
    (∑ x : M.LabelledAttachedTreeChoice root s,
      M.labelledAttachedTreeChoiceWeight root x) =
      ∑ label : Fin s → P,
        M.labelledAttachedComponentWeight root label := by
  classical
  let e : M.LabelledAttachedTreeChoice root s ≃
      Σ label : Fin s → P,
        {T : SimpleGraph (Fin s) //
          T ∈ graphSpanningTrees (labelledIncompatibilityGraph M label)} ×
        {j : Fin s // M.incompatible root (label j)} := Equiv.refl _
  calc
    (∑ x : M.LabelledAttachedTreeChoice root s,
        M.labelledAttachedTreeChoiceWeight root x) =
      ∑ q : Σ label : Fin s → P,
          {T : SimpleGraph (Fin s) //
            T ∈ graphSpanningTrees (labelledIncompatibilityGraph M label)} ×
          {j : Fin s // M.incompatible root (label j)},
        ∏ j : Fin s, ‖M.activity (q.1 j)‖ := by
          exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
    _ = ∑ label : Fin s → P,
        ∑ _x :
            {T : SimpleGraph (Fin s) //
              T ∈ graphSpanningTrees (labelledIncompatibilityGraph M label)} ×
            {j : Fin s // M.incompatible root (label j)},
          ∏ j : Fin s, ‖M.activity (label j)‖ := by
      exact Fintype.sum_sigma' (fun (label : Fin s → P) _x ↦
        ∏ j : Fin s, ‖M.activity (label j)‖)
    _ = ∑ label : Fin s → P,
        M.labelledAttachedComponentWeight root label := by
      apply Finset.sum_congr rfl
      intro label _
      exact M.sum_labelledAttachedTreeChoiceWeight_fiber root s label

set_option maxHeartbeats 1200000 in
-- Dependent products over variable-size ordered blocks require extra elaboration.
/-- Summing all explicit forest codes factors independently over their
ordered blocks.  This is the finite weighted set-species identity used by
the global exponential formula. -/
theorem sum_fixedLabelledRootedForestCodeWeight
    (M : FinitePolymerModel P) (root : P) (n : ℕ) :
    (∑ x : M.FixedLabelledRootedForestCode root n,
      M.fixedLabelledRootedForestCodeWeight root x) =
      orderedFinpartitionWeight
        (fun s ↦ ∑ label : Fin s → P,
          M.labelledAttachedComponentWeight root label) n := by
  classical
  let e : M.FixedLabelledRootedForestCode root n ≃
      Σ c : OrderedFinpartition n,
        ∀ i : Fin c.length,
          M.LabelledAttachedTreeChoice root (c.partSize i) := Equiv.refl _
  calc
    (∑ x : M.FixedLabelledRootedForestCode root n,
        M.fixedLabelledRootedForestCodeWeight root x) =
      ∑ q : Σ c : OrderedFinpartition n,
          ∀ i : Fin c.length,
            M.LabelledAttachedTreeChoice root (c.partSize i),
        ∏ i : Fin q.1.length,
          M.labelledAttachedTreeChoiceWeight root (q.2 i) := by
      exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
    _ = ∑ c : OrderedFinpartition n,
        ∑ choices : ∀ i : Fin c.length,
            M.LabelledAttachedTreeChoice root (c.partSize i),
          ∏ i : Fin c.length,
            M.labelledAttachedTreeChoiceWeight root (choices i) := by
      exact Fintype.sum_sigma' (fun (c : OrderedFinpartition n)
          (choices : ∀ i : Fin c.length,
            M.LabelledAttachedTreeChoice root (c.partSize i)) ↦
        ∏ i : Fin c.length,
          M.labelledAttachedTreeChoiceWeight root (choices i))
    _ = ∑ c : OrderedFinpartition n,
        ∏ i : Fin c.length,
          ∑ choice : M.LabelledAttachedTreeChoice root (c.partSize i),
            M.labelledAttachedTreeChoiceWeight root choice := by
      apply Finset.sum_congr rfl
      intro c _
      exact (Fintype.prod_sum (fun i choice ↦
        M.labelledAttachedTreeChoiceWeight root choice)).symm
    _ = ∑ c : OrderedFinpartition n,
        ∏ i : Fin c.length,
          ∑ label : Fin (c.partSize i) → P,
            M.labelledAttachedComponentWeight root label := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.prod_congr rfl
      intro i _
      exact M.sum_labelledAttachedTreeChoiceWeight root (c.partSize i)
    _ = orderedFinpartitionWeight
        (fun s ↦ ∑ label : Fin s → P,
          M.labelledAttachedComponentWeight root label) n := by
      rfl

/-- The injective root-cutting code bounds every fixed-degree labelled
rooted-tree sum by the ordered-partition weight of attached components. -/
theorem sum_fixedLabelledRootedTreeWeight_le_forestCodeWeight
    (M : FinitePolymerModel P) (root : P) (n : ℕ) :
    (∑ x : M.FixedLabelledRootedTree root n,
      M.fixedLabelledRootedTreeWeight root x) ≤
    ∑ y : M.FixedLabelledRootedForestCode root n,
      M.fixedLabelledRootedForestCodeWeight root y := by
  classical
  let enc : M.FixedLabelledRootedTree root n →
      M.FixedLabelledRootedForestCode root n :=
    M.fixedLabelledRootedTreeToForestCode root
  calc
    (∑ x : M.FixedLabelledRootedTree root n,
        M.fixedLabelledRootedTreeWeight root x) =
      ∑ x : M.FixedLabelledRootedTree root n,
        M.fixedLabelledRootedForestCodeWeight root (enc x) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (M.fixedLabelledRootedTreeToForestCode_weight root x).symm
    _ = ∑ y ∈ (Finset.univ :
          Finset (M.FixedLabelledRootedTree root n)).image enc,
        M.fixedLabelledRootedForestCodeWeight root y := by
      rw [Finset.sum_image
        (M.fixedLabelledRootedTreeToForestCode_injective root).injOn]
    _ ≤ ∑ y : M.FixedLabelledRootedForestCode root n,
        M.fixedLabelledRootedForestCodeWeight root y := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _)
        (fun y _ _ ↦ M.fixedLabelledRootedForestCodeWeight_nonneg root y)

/-- Fixed-degree rooted-tree species bound in the exact form consumed by the
weighted ordered-partition exponential formula. -/
theorem sum_labelledPinnedTreeWeight_le_orderedFinpartitionWeight
    (M : FinitePolymerModel P) (root : P) (n : ℕ) :
    (∑ label : Fin n → P, M.labelledPinnedTreeWeight root label) ≤
      orderedFinpartitionWeight
        (fun s ↦ ∑ label : Fin s → P,
          M.labelledAttachedComponentWeight root label) n := by
  rw [← M.sum_fixedLabelledRootedTreeWeight root n,
    ← M.sum_fixedLabelledRootedForestCodeWeight root n]
  exact M.sum_fixedLabelledRootedTreeWeight_le_forestCodeWeight root n

/-- The fixed-labelled root-deletion recurrence.  It is obtained by summing
the fixed-degree forest-code bound, applying the weighted labelled-set
exponential formula, and then using the exact `s/s!` attachment cancellation
from `LabelledTreeSummation`. -/
theorem labelledPinnedTreePartialSum_succ_le_exp
    (M : FinitePolymerModel P) (root : P) (N : ℕ) :
    M.labelledPinnedTreePartialSum root (N + 1) ≤
      Real.exp
        (∑ child ∈ (Finset.univ : Finset P).filter (M.incompatible root),
          ‖M.activity child‖ * M.labelledPinnedTreePartialSum child N) := by
  classical
  let b : ℕ → ℝ := fun s ↦ ∑ label : Fin s → P,
    M.labelledAttachedComponentWeight root label
  have hb0 : b 0 = 0 := by
    simp [b, labelledAttachedComponentWeight]
  have hb : ∀ s, 0 ≤ b s := by
    intro s
    rw [show b s = ∑ choice : M.LabelledAttachedTreeChoice root s,
        M.labelledAttachedTreeChoiceWeight root choice by
      exact (M.sum_labelledAttachedTreeChoiceWeight root s).symm]
    exact Finset.sum_nonneg fun choice _ ↦
      M.labelledAttachedTreeChoiceWeight_nonneg root choice
  calc
    M.labelledPinnedTreePartialSum root (N + 1) =
        ∑ n ∈ Finset.range (N + 1),
          (∑ label : Fin n → P,
            M.labelledPinnedTreeWeight root label) /
              (n.factorial : ℝ) := by
      rfl
    _ ≤ ∑ n ∈ Finset.range (N + 1),
        orderedFinpartitionWeight b n / (n.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      exact div_le_div_of_nonneg_right
        (M.sum_labelledPinnedTreeWeight_le_orderedFinpartitionWeight root n)
        (Nat.cast_nonneg _)
    _ ≤ Real.exp (∑ s ∈ Finset.range (N + 1),
        b s / (s.factorial : ℝ)) :=
      sum_factorialNormalized_orderedFinpartitionWeight_le_exp b N hb0 hb
    _ = Real.exp
        (∑ child ∈ (Finset.univ : Finset P).filter (M.incompatible root),
          ‖M.activity child‖ * M.labelledPinnedTreePartialSum child N) := by
      congr 1
      change (∑ s ∈ Finset.range (N + 1),
          M.factorialNormalizedLabelledAttachedComponentDegreeSum root s) = _
      rw [Finset.sum_range_succ']
      have hzero :
          M.factorialNormalizedLabelledAttachedComponentDegreeSum root 0 = 0 := by
        simp [factorialNormalizedLabelledAttachedComponentDegreeSum,
          labelledAttachedComponentWeight]
      rw [hzero, add_zero]
      simp_rw [M.factorialNormalizedLabelledAttachedComponentDegreeSum_succ root]
      unfold labelledPinnedTreePartialSum
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro child _
      rw [Finset.mul_sum]

/-- The labelled recurrence is no longer an assumption: the explicit
fixed-labelled forest species proves it for every finite polymer model. -/
theorem labelledRootedTreeRecurrence
    (M : FinitePolymerModel P) : M.LabelledRootedTreeRecurrence := by
  intro root N
  exact M.labelledPinnedTreePartialSum_succ_le_exp root N

/-- Symmetric multi-index/orbit form of the proven labelled recurrence. -/
theorem rootedTreeOrbitRecurrence
    (M : FinitePolymerModel P) : M.RootedTreeOrbitRecurrence :=
  M.labelledRootedTreeRecurrence_iff_orbitRecurrence.mp
    M.labelledRootedTreeRecurrence

/-- Genuine KP/tree orbit bound, with no remaining combinatorial premise. -/
theorem rootedTreeOrbitBound
    (M : FinitePolymerModel P) : M.RootedTreeOrbitBound :=
  M.rootedTreeOrbitBound_of_recurrence M.rootedTreeOrbitRecurrence

/-- Summability of the positive pinned spanning-tree majorant with the
fixed-labelled recurrence discharged. -/
theorem summable_pinnedMayerTreeDegreeSum_succ_of_koteckyPreiss_certified
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) (root : P) :
    Summable (fun n : ℕ ↦ M.pinnedMayerTreeDegreeSum root (n + 1)) :=
  M.summable_pinnedMayerTreeDegreeSum_succ_of_koteckyPreiss
    a M.rootedTreeOrbitBound hKP root

/-- Absolute convergence of every pinned positive-degree Mayer series from
the standard KP certificate alone. -/
theorem summable_pinnedNormMayerDegreeSum_succ_of_koteckyPreiss_certified
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) (root : P) :
    Summable (fun n : ℕ ↦ M.pinnedNormMayerDegreeSum root (n + 1)) :=
  M.summable_pinnedNormMayerDegreeSum_succ_of_koteckyPreiss
    a M.rootedTreeOrbitBound hKP root

/-- Genuine absolute summability of the full positive-degree Mayer series,
with the formerly conditional rooted-tree premise discharged. -/
theorem summable_normMayerDegreeSum_succ_of_koteckyPreiss_certified
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    Summable (fun n : ℕ ↦ M.normMayerDegreeSum (n + 1)) :=
  M.summable_normMayerDegreeSum_succ_of_koteckyPreiss
    a M.rootedTreeOrbitBound hKP

/-- Complex symmetric Mayer coefficients are summable after removing the
zero-degree term. -/
theorem summable_symmetricMayerDegreeSum_succ_of_koteckyPreiss_certified
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    Summable (fun n : ℕ ↦ M.symmetricMayerDegreeSum (n + 1)) := by
  apply Summable.of_norm_bounded
    (M.summable_normMayerDegreeSum_succ_of_koteckyPreiss_certified a hKP)
  intro n
  exact M.norm_symmetricMayerDegreeSum_le (n + 1)

/-- The first degree moment of the absolute Mayer series is summable.  The
factor `n + 1` is not an extra estimate: it is exactly the sum over all
possible distinguished polymer labels, so the already-certified pinned KP
series supplies it. -/
theorem summable_succ_mul_normMayerDegreeSum_succ_of_koteckyPreiss_certified
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    Summable (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ) * M.normMayerDegreeSum (n + 1)) := by
  have hsum : Summable (fun n : ℕ ↦
      ∑ root : P, M.pinnedNormMayerDegreeSum root (n + 1)) :=
    summable_sum (s := (Finset.univ : Finset P)) fun root _ ↦
      M.summable_pinnedNormMayerDegreeSum_succ_of_koteckyPreiss_certified
        a hKP root
  exact hsum.congr fun n ↦ M.sum_pinnedNormMayerDegreeSum (n + 1)

/-- Quantitative rooted-orbit total-mass bound from the KP certificate alone. -/
theorem tsum_residualSymmetricPinnedTreeDegreeSum_le_of_koteckyPreiss_certified
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) (root : P) :
    ∑' n : ℕ, M.residualSymmetricPinnedTreeDegreeSum root n ≤
      Real.exp (a root) :=
  M.tsum_residualSymmetricPinnedTreeDegreeSum_le_of_koteckyPreiss
    a M.rootedTreeOrbitBound hKP root

/-- Quantitative positive-degree pinned-tree mass from the certified
fixed-labelled rooted-forest recurrence. -/
theorem tsum_pinnedMayerTreeDegreeSum_succ_le_of_koteckyPreiss_certified
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) (root : P) :
    ∑' n : ℕ, M.pinnedMayerTreeDegreeSum root (n + 1) ≤
      ‖M.activity root‖ * Real.exp (a root) :=
  M.tsum_pinnedMayerTreeDegreeSum_succ_le_of_koteckyPreiss
    a M.rootedTreeOrbitBound hKP root

/-- Quantitative absolute Mayer bound, obtained by combining the sharp
Whitney termwise inequality with the certified rooted-tree budget. -/
theorem tsum_pinnedNormMayerDegreeSum_succ_le_of_koteckyPreiss_certified
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) (root : P) :
    ∑' n : ℕ, M.pinnedNormMayerDegreeSum root (n + 1) ≤
      ‖M.activity root‖ * Real.exp (a root) := by
  have hnorm :=
    M.summable_pinnedNormMayerDegreeSum_succ_of_koteckyPreiss_certified
      a hKP root
  have htree :=
    M.summable_pinnedMayerTreeDegreeSum_succ_of_koteckyPreiss_certified
      a hKP root
  exact (hnorm.tsum_le_tsum (fun n ↦ by
    unfold pinnedNormMayerDegreeSum pinnedMayerTreeDegreeSum
    apply Finset.sum_le_sum
    intro X _
    exact M.pinned_norm_mayerClusterTerm_le_tree root X) htree).trans
      (M.tsum_pinnedMayerTreeDegreeSum_succ_le_of_koteckyPreiss_certified
        a hKP root)

/-- Every finite collection of multiplicity-pinned Mayer terms is bounded by
the same rooted KP budget.  This finite-partial-sum form is the one that
passes directly to countable ambient polymer species. -/
theorem sum_pinnedNormMayerTerm_le_of_koteckyPreiss_certified
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) (root : P)
    (U : Finset (MayerMultiIndex P)) :
    ∑ X ∈ U, (X root : ℝ) * ‖M.mayerClusterTerm X‖ ≤
      ‖M.activity root‖ * Real.exp (a root) := by
  let N := U.sup mayerDegree
  let f : MayerMultiIndex P → ℝ :=
    fun X ↦ (X root : ℝ) * ‖M.mayerClusterTerm X‖
  let b : ℕ → ℝ := fun n ↦ M.pinnedNormMayerDegreeSum root n
  have hmaps : ∀ X ∈ U, mayerDegree X ∈ Finset.range (N + 1) := by
    intro X hX
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hX))
  have hfiber :
      ∑ X ∈ U, f X =
        ∑ n ∈ Finset.range (N + 1),
          ∑ X ∈ U with mayerDegree X = n, f X := by
    exact (Finset.sum_fiberwise_of_maps_to hmaps f).symm
  have hdegree : ∀ n,
      ∑ X ∈ U with mayerDegree X = n, f X ≤ b n := by
    intro n
    unfold b FinitePolymerModel.pinnedNormMayerDegreeSum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro X hX
      exact (mem_mayerMultiIndicesOfDegree n X).mpr
        (Finset.mem_filter.mp hX).2
    · intro X _ _
      exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hbzero : b 0 = 0 := by
    unfold b FinitePolymerModel.pinnedNormMayerDegreeSum
    apply Finset.sum_eq_zero
    intro X hX
    have hdegreeX : mayerDegree X = 0 :=
      (mem_mayerMultiIndicesOfDegree 0 X).mp hX
    have hroot : X root = 0 := by
      unfold mayerDegree at hdegreeX
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ ↦ Nat.zero_le _)).mp hdegreeX root (Finset.mem_univ root)
    simp [hroot]
  have hbshift : Summable (fun n : ℕ ↦ b (n + 1)) := by
    simpa [b] using
      M.summable_pinnedNormMayerDegreeSum_succ_of_koteckyPreiss_certified
        a hKP root
  have hb : Summable b := (summable_nat_add_iff 1).mp (by
    simpa [Nat.add_comm] using hbshift)
  have htsum : ∑' n : ℕ, b n = ∑' n : ℕ, b (n + 1) := by
    have h := hb.sum_add_tsum_nat_add 1
    simpa [hbzero, Nat.add_comm] using h.symm
  calc
    ∑ X ∈ U, (X root : ℝ) * ‖M.mayerClusterTerm X‖ =
        ∑ X ∈ U, f X := rfl
    _ = ∑ n ∈ Finset.range (N + 1),
          ∑ X ∈ U with mayerDegree X = n, f X := hfiber
    _ ≤ ∑ n ∈ Finset.range (N + 1), b n := by
      exact Finset.sum_le_sum fun n _ ↦ hdegree n
    _ ≤ ∑' n : ℕ, b n :=
      hb.sum_le_tsum _ (fun _ _ ↦ by
        unfold b FinitePolymerModel.pinnedNormMayerDegreeSum
        exact Finset.sum_nonneg fun _ _ ↦
          mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    _ = ∑' n : ℕ, M.pinnedNormMayerDegreeSum root (n + 1) := by
      rw [htsum]
    _ ≤ ‖M.activity root‖ * Real.exp (a root) :=
      M.tsum_pinnedNormMayerDegreeSum_succ_le_of_koteckyPreiss_certified
        a hKP root

end FinitePolymerModel

end

end YangMills.Polymer
