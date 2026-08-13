/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.GraphExponential
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Boolean-interval cancellation for Penrose graph partitions

The sharp tree-graph argument partitions connected spanning edge sets into
Boolean intervals `[T, R(T)]` indexed by spanning trees.  Every nontrivial
interval cancels in the signed graph sum; only trees with `R(T) = T` survive.

This file proves that cancellation independently of any particular choice of
Penrose map.  The remaining graph-theoretic task is to construct the interval
partition itself (for example by ordered greedy deletion).  It belongs to the
model-independent polymer/combinatorics layer.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

/-- Finsets lying in the Boolean interval from `T` to `R`. -/
def finsetInterval {E : Type*} [DecidableEq E]
    (T R : Finset E) : Finset (Finset E) :=
  R.powerset.filter fun H => T ⊆ H

@[simp]
theorem mem_finsetInterval {E : Type*} [DecidableEq E]
    {T R H : Finset E} :
    H ∈ finsetInterval T R ↔ T ⊆ H ∧ H ⊆ R := by
  simp [finsetInterval, and_comm]

/-- Translation by the lower endpoint identifies `[T,R]` with the powerset
of `R \ T`. -/
theorem sum_finsetInterval_eq_sum_powerset_sdiff
    {E : Type*} [DecidableEq E] (T R : Finset E) (hTR : T ⊆ R) :
    ∑ H ∈ finsetInterval T R, (-1 : ℤ) ^ H.card =
      ∑ s ∈ (R \ T).powerset, (-1 : ℤ) ^ (T.card + s.card) := by
  classical
  apply Finset.sum_bij (fun H _ => H \ T)
  · intro H hH
    exact Finset.mem_powerset.mpr <| by
      intro e he
      exact Finset.mem_sdiff.mpr
        ⟨(mem_finsetInterval.mp hH).2 (Finset.mem_sdiff.mp he).1,
          (Finset.mem_sdiff.mp he).2⟩
  · intro H₁ hH₁ H₂ hH₂ heq
    have hT₁ : T ⊆ H₁ := (mem_finsetInterval.mp hH₁).1
    have hT₂ : T ⊆ H₂ := (mem_finsetInterval.mp hH₂).1
    rw [← Finset.union_sdiff_of_subset hT₁,
      ← Finset.union_sdiff_of_subset hT₂, heq]
  · intro s hs
    have hsRT : s ⊆ R \ T := Finset.mem_powerset.mp hs
    refine ⟨T ∪ s, ?_, ?_⟩
    · apply mem_finsetInterval.mpr
      refine ⟨Finset.subset_union_left, ?_⟩
      exact Finset.union_subset hTR
        (hsRT.trans Finset.sdiff_subset)
    · ext e
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨heT | hes, hnotT⟩
        · exact (hnotT heT).elim
        · exact hes
      · intro hes
        exact ⟨Or.inr hes, (Finset.mem_sdiff.mp (hsRT hes)).2⟩
  · intro H hH
    have hTH : T ⊆ H := (mem_finsetInterval.mp hH).1
    have hdisj : Disjoint T (H \ T) := Finset.disjoint_sdiff
    rw [← Finset.card_union_of_disjoint hdisj,
      Finset.union_sdiff_of_subset hTH]

/-- Signed cancellation on a Boolean interval.  A non-singleton interval has
sum zero; a singleton tree interval contributes its usual edge sign. -/
theorem sum_finsetInterval_neg_one_pow_card
    {E : Type*} [DecidableEq E] (T R : Finset E) (hTR : T ⊆ R) :
    ∑ H ∈ finsetInterval T R, (-1 : ℤ) ^ H.card =
      (-1 : ℤ) ^ T.card * if R \ T = ∅ then 1 else 0 := by
  rw [sum_finsetInterval_eq_sum_powerset_sdiff T R hTR]
  calc
    ∑ s ∈ (R \ T).powerset, (-1 : ℤ) ^ (T.card + s.card) =
        (-1 : ℤ) ^ T.card *
          ∑ s ∈ (R \ T).powerset, (-1 : ℤ) ^ s.card := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [pow_add]
    _ = (-1 : ℤ) ^ T.card * if R \ T = ∅ then 1 else 0 := by
      rw [Finset.sum_powerset_neg_one_pow_card]

/-- The singleton form used for a closed Penrose tree. -/
theorem sum_finsetInterval_eq_sign_of_eq
    {E : Type*} [DecidableEq E] (T R : Finset E) (hTR : T ⊆ R)
    (hRT : R ⊆ T) :
    ∑ H ∈ finsetInterval T R, (-1 : ℤ) ^ H.card =
      (-1 : ℤ) ^ T.card := by
  rw [sum_finsetInterval_neg_one_pow_card T R hTR]
  rw [if_pos (Finset.sdiff_eq_empty_iff_subset.mpr hRT), mul_one]

/-- The cancellation form used for a nontrivial Penrose interval. -/
theorem sum_finsetInterval_eq_zero_of_ssubset
    {E : Type*} [DecidableEq E] (T R : Finset E) (hTR : T ⊂ R) :
    ∑ H ∈ finsetInterval T R, (-1 : ℤ) ^ H.card = 0 := by
  rw [sum_finsetInterval_neg_one_pow_card T R hTR.1]
  have hne : R \ T ≠ ∅ :=
    (Finset.sdiff_nonempty.mpr (not_subset_of_ssubset hTR)).ne_empty
  rw [if_neg hne, mul_zero]

/-! ## Abstract Penrose interval schemes -/

/-- A finite family partitioned into Boolean intervals indexed by its chosen
trees.  This is the exact interface supplied by any concrete Penrose or
ordered-greedy construction. -/
structure PenroseIntervalScheme (E : Type*) [DecidableEq E] where
  /-- Connected spanning edge sets to be partitioned. -/
  family : Finset (Finset E)
  /-- Lower endpoints, intended to be spanning trees. -/
  trees : Finset (Finset E)
  /-- The tree assigned to an edge set. -/
  owner : Finset E → Finset E
  /-- Upper endpoint of the interval belonging to a tree. -/
  closure : Finset E → Finset E
  owner_mem : ∀ H ∈ family, owner H ∈ trees
  lower_subset_closure : ∀ T ∈ trees, T ⊆ closure T
  fiber_eq_interval : ∀ T ∈ trees,
    family.filter (fun H => owner H = T) = finsetInterval T (closure T)

namespace PenroseIntervalScheme

variable {E : Type*} [DecidableEq E]

/-- Penrose regrouping: the signed family sum is the sum of its Boolean
interval cancellations. -/
theorem signedSum_eq_intervalSum (S : PenroseIntervalScheme E) :
    ∑ H ∈ S.family, (-1 : ℤ) ^ H.card =
      ∑ T ∈ S.trees,
        ((-1 : ℤ) ^ T.card *
          if S.closure T \ T = ∅ then 1 else 0) := by
  classical
  have hfilter :
      S.family.filter (fun H => S.owner H ∈ S.trees) = S.family := by
    ext H
    simp only [Finset.mem_filter]
    exact and_iff_left_of_imp (S.owner_mem H)
  calc
    ∑ H ∈ S.family, (-1 : ℤ) ^ H.card =
        ∑ H ∈ S.family.filter (fun H => S.owner H ∈ S.trees),
          (-1 : ℤ) ^ H.card := by rw [hfilter]
    _ = ∑ T ∈ S.trees,
          ∑ H ∈ S.family.filter (fun H => S.owner H = T),
            (-1 : ℤ) ^ H.card := by
      symm
      exact Finset.sum_fiberwise_eq_sum_filter
        S.family S.trees S.owner (fun H => (-1 : ℤ) ^ H.card)
    _ = ∑ T ∈ S.trees,
        ((-1 : ℤ) ^ T.card *
          if S.closure T \ T = ∅ then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [S.fiber_eq_interval T hT,
        sum_finsetInterval_neg_one_pow_card T (S.closure T)
          (S.lower_subset_closure T hT)]

/-- Sharp abstract tree bound.  Once a connected graph family has a Penrose
interval scheme, its signed sum is bounded by the number of indexing trees,
with no extra all-graphs factor. -/
theorem abs_signedSum_le_card_trees (S : PenroseIntervalScheme E) :
    |∑ H ∈ S.family, (-1 : ℤ) ^ H.card| ≤ S.trees.card := by
  rw [S.signedSum_eq_intervalSum]
  calc
    |∑ T ∈ S.trees,
        ((-1 : ℤ) ^ T.card *
          if S.closure T \ T = ∅ then 1 else 0)| ≤
        ∑ T ∈ S.trees,
          |((-1 : ℤ) ^ T.card *
            if S.closure T \ T = ∅ then 1 else 0)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _T ∈ S.trees, (1 : ℤ) := by
      gcongr with T hT
      split_ifs <;> simp
    _ = S.trees.card := by simp

end PenroseIntervalScheme

/-! ## Graph specialization -/

/-- Spanning trees of an arbitrary finite graph. -/
def graphSpanningTrees {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (SimpleGraph V) := by
  classical
  exact (spanningSubgraphs G).filter fun T => T.IsTree

/-- Edge-finset presentation of the connected spanning subgraphs. -/
def connectedSpanningEdgeFamilies
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (Finset (Sym2 V)) := by
  classical
  exact ((spanningSubgraphs G).filter SimpleGraph.Connected).image finiteEdges

/-- Edge-finset presentation of the spanning trees. -/
def spanningTreeEdgeFamilies
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (Finset (Sym2 V)) := by
  classical
  exact (graphSpanningTrees G).image finiteEdges

/-- A concrete graph Penrose scheme is precisely a Boolean-interval scheme
whose family consists of the connected spanning subgraphs and whose lower
endpoints are the spanning trees of `G`. -/
structure GraphPenroseScheme
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    extends PenroseIntervalScheme (Sym2 V) where
  family_eq : family = connectedSpanningEdgeFamilies G
  trees_eq : trees = spanningTreeEdgeFamilies G

namespace GraphPenroseScheme

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem connectedSpanningGraphSum_eq_edgeFamilySum (G : SimpleGraph V) :
    connectedSpanningGraphSum G =
      ∑ E ∈ connectedSpanningEdgeFamilies G, (-1 : ℤ) ^ E.card := by
  classical
  unfold connectedSpanningGraphSum connectedSpanningEdgeFamilies
  apply Finset.sum_bij (fun H _ => finiteEdges H)
  · intro H hH
    exact Finset.mem_image.mpr ⟨H, hH, rfl⟩
  · intro H₁ _ H₂ _ h
    exact finiteEdges_inj h
  · intro E hE
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hE
    exact ⟨H, hH, rfl⟩
  · intro H _
    rfl

theorem card_spanningTreeEdgeFamilies (G : SimpleGraph V) :
    (spanningTreeEdgeFamilies G).card = (graphSpanningTrees G).card := by
  classical
  unfold spanningTreeEdgeFamilies
  rw [Finset.card_image_iff.mpr]
  intro H₁ _ H₂ _ h
  exact finiteEdges_inj h

/-- The sharp Penrose tree-graph inequality obtained from a concrete interval
scheme.  There is no conservative all-graphs multiplier. -/
theorem abs_connectedSpanningGraphSum_le_card_trees
    {G : SimpleGraph V} (S : GraphPenroseScheme G) :
    |connectedSpanningGraphSum G| ≤ (graphSpanningTrees G).card := by
  rw [connectedSpanningGraphSum_eq_edgeFamilySum, ← S.family_eq,
    ← card_spanningTreeEdgeFamilies G, ← S.trees_eq]
  exact S.toPenroseIntervalScheme.abs_signedSum_le_card_trees

end GraphPenroseScheme

end

end YangMills.Polymer
