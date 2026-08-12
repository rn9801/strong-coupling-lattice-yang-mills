/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Partition.Finpartition
import YangMills.Polymer.FinpartitionCoarsening

/-!
# Signed finite-graph sums for the Mayer exponential formula

This file isolates the graph combinatorics used to regroup the normalized
Mayer logarithm into symmetric Ursell coefficients.  It is independent of
Yang--Mills and of all polymer activities.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

local instance {V : Type*} : DecidableEq (SimpleGraph V) :=
  Classical.decEq _

local instance {V : Type*} : DecidableLE (SimpleGraph V) :=
  Classical.decRel _

local instance {V : Type*} : DecidablePred
    (fun G : SimpleGraph V => G.Connected) := fun _ => Classical.propDecidable _

local instance {V : Type*} [Fintype V] [DecidableEq V] :
    DecidableLE (Finpartition (Finset.univ : Finset V)) := Classical.decRel _

local instance {V : Type*} [Fintype V] [DecidableEq V] :
    DecidableLT (Finpartition (Finset.univ : Finset V)) := Classical.decRel _

local instance {V : Type*} [Fintype V] [DecidableEq V] :
    LocallyFiniteOrder (Finpartition (Finset.univ : Finset V)) :=
  Fintype.toLocallyFiniteOrder

/-- All spanning subgraphs of a finite graph. -/
def spanningSubgraphs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (SimpleGraph V) := by
  classical
  exact Finset.univ.filter fun H => H ≤ G

/-- The edge set of a finite graph, represented without choosing a
`DecidableRel` instance for adjacency.  This canonical representation avoids
typeclass-dependent `edgeFinset` terms in the graph-sum bijections below. -/
def finiteEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun e => e ∈ G.edgeSet

@[simp]
theorem mem_finiteEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (e : Sym2 V) :
    e ∈ finiteEdges G ↔ e ∈ G.edgeSet := by
  classical
  simp [finiteEdges]

theorem finiteEdges_inj {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} (h : finiteEdges G = finiteEdges H) : G = H := by
  apply SimpleGraph.edgeSet_inj.mp
  ext e
  simpa only [mem_finiteEdges] using Finset.ext_iff.mp h e

theorem finiteEdges_subset_finiteEdges {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} : finiteEdges G ⊆ finiteEdges H ↔ G ≤ H := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet]
  constructor
  · intro h e he
    exact (mem_finiteEdges H e).mp (h ((mem_finiteEdges G e).mpr he))
  · intro h e he
    exact (mem_finiteEdges H e).mpr (h ((mem_finiteEdges G e).mp he))

/-- Signed sum over all spanning subgraphs. -/
def allSpanningGraphSum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℤ :=
  ∑ H ∈ spanningSubgraphs G, (-1 : ℤ) ^ (finiteEdges H).card

private lemma finiteEdges_fromEdgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : Finset (Sym2 V)) (hs : s ⊆ finiteEdges G) :
    finiteEdges (SimpleGraph.fromEdgeSet (s : Set (Sym2 V))) = s := by
  classical
  ext e
  rw [mem_finiteEdges, SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_diff, Finset.mem_coe]
  constructor
  · exact fun h => h.1
  · intro he
    refine ⟨he, ?_⟩
    exact G.not_isDiag_of_mem_edgeSet
      ((mem_finiteEdges G _).mp (hs he))

/-- Spanning subgraphs are in weight-preserving bijection with subsets of the
ambient edge finset. -/
theorem allSpanningGraphSum_eq_powerset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    allSpanningGraphSum G =
      ∑ s ∈ (finiteEdges G).powerset, (-1 : ℤ) ^ s.card := by
  classical
  unfold allSpanningGraphSum
  apply Finset.sum_bij (fun H _ => finiteEdges H)
  · intro H hH
    exact Finset.mem_powerset.mpr <|
      finiteEdges_subset_finiteEdges.mpr
        (Finset.mem_filter.mp hH).2
  · intro H₁ _ H₂ _ h
    exact finiteEdges_inj h
  · intro s hs
    have hsG : s ⊆ finiteEdges G := Finset.mem_powerset.mp hs
    let H := SimpleGraph.fromEdgeSet (s : Set (Sym2 V))
    have hHE : finiteEdges H = s := finiteEdges_fromEdgeFinset G s hsG
    refine ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hHE⟩
    exact finiteEdges_subset_finiteEdges.mp (hHE.trans_le hsG)
  · intro H hH
    rfl

/-- Inclusion--exclusion cancellation for all spanning subgraphs. -/
theorem allSpanningGraphSum_eq_if {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    allSpanningGraphSum G = if G = ⊥ then 1 else 0 := by
  classical
  rw [allSpanningGraphSum_eq_powerset,
    Finset.sum_powerset_neg_one_pow_card]
  congr 1
  apply propext
  constructor
  · intro h
    rw [← SimpleGraph.edgeSet_eq_empty]
    ext e
    constructor
    · intro he
      have : e ∈ finiteEdges G := (mem_finiteEdges G e).mpr he
      rw [h] at this
      exact (Finset.notMem_empty e this).elim
    · simp
  · rintro rfl
    ext e
    simp [finiteEdges]

@[simp]
theorem allSpanningGraphSum_bot {V : Type*} [Fintype V] [DecidableEq V] :
    allSpanningGraphSum (⊥ : SimpleGraph V) = 1 := by
  rw [allSpanningGraphSum_eq_if]
  simp

theorem allSpanningGraphSum_eq_zero_of_ne_bot
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G ≠ ⊥) :
    allSpanningGraphSum G = 0 := by
  rw [allSpanningGraphSum_eq_if, if_neg hG]

/-- The inclusion--exclusion sum over all spanning subgraphs is invariant
under graph isomorphism. -/
theorem allSpanningGraphSum_eq_of_iso
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {K : SimpleGraph W} (e : G ≃g K) :
    allSpanningGraphSum G = allSpanningGraphSum K := by
  rw [allSpanningGraphSum_eq_if, allSpanningGraphSum_eq_if]
  congr 1
  apply propext
  constructor
  · intro hG
    rw [SimpleGraph.eq_bot_iff_forall_not_adj]
    intro v w hvw
    have hback : G.Adj (e.symm v) (e.symm w) :=
      e.map_rel_iff.mp (by simpa using hvw)
    have hbot : (⊥ : SimpleGraph V).Adj (e.symm v) (e.symm w) :=
      hG ▸ hback
    exact hbot
  · intro hK
    rw [SimpleGraph.eq_bot_iff_forall_not_adj]
    intro v w hvw
    have hmap : K.Adj (e v) (e w) := e.map_rel_iff.mpr hvw
    have hbot : (⊥ : SimpleGraph W).Adj (e v) (e w) := hK ▸ hmap
    exact hbot

/-! ## Component partitions -/

/-- Partition of a finite vertex type into the connected components of a
graph. -/
def componentPartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finpartition (Finset.univ : Finset V) := by
  classical
  exact Finpartition.ofSetoid G.reachableSetoid

@[simp]
theorem mem_componentPartition_part_iff_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v w : V) :
    w ∈ (componentPartition G).part v ↔ G.Reachable v w := by
  classical
  exact Finpartition.mem_part_ofSetoid_iff_rel

/-- Two vertices lie in the same component part exactly when they are
reachable. -/
theorem componentPartition_part_eq_iff_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v w : V) :
    (componentPartition G).part v = (componentPartition G).part w ↔
      G.Reachable v w := by
  classical
  constructor
  · intro h
    apply (mem_componentPartition_part_iff_reachable G v w).mp
    apply ((componentPartition G).mem_part_iff_part_eq_part
      (Finset.mem_univ w) (Finset.mem_univ v)).mpr
    exact h.symm
  · intro h
    have hw : w ∈ (componentPartition G).part v :=
      (mem_componentPartition_part_iff_reachable G v w).mpr h
    exact (((componentPartition G).mem_part_iff_part_eq_part
      (Finset.mem_univ w) (Finset.mem_univ v)).mp hw).symm

private theorem reachable_part_eq_of_adj_part_eq
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (Q : Finpartition (Finset.univ : Finset V))
    (h : ∀ ⦃v w⦄, H.Adj v w → Q.part v = Q.part w)
    {v w : V} (hvw : H.Reachable v w) : Q.part v = Q.part w := by
  rw [SimpleGraph.reachable_eq_reflTransGen] at hvw
  induction hvw using Relation.ReflTransGen.trans_induction_on with
  | refl => rfl
  | single hab => exact h hab
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Refinement of the component partition is equivalent to saying that every
selected edge has both endpoints in one part of the coarser partition. -/
theorem componentPartition_le_iff_adj_part_eq
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (Q : Finpartition (Finset.univ : Finset V)) :
    componentPartition H ≤ Q ↔
      ∀ ⦃v w : V⦄, H.Adj v w → Q.part v = Q.part w := by
  classical
  constructor
  · intro hle v w hvw
    let b := (componentPartition H).part v
    have hb : b ∈ (componentPartition H).parts := by
      exact (componentPartition H).part_mem.mpr (Finset.mem_univ v)
    obtain ⟨c, hc, hbc⟩ := hle hb
    have hvb : v ∈ b := (componentPartition H).mem_part (Finset.mem_univ v)
    have hwb : w ∈ b := by
      exact (mem_componentPartition_part_iff_reachable H v w).mpr hvw.reachable
    rw [Q.part_eq_of_mem hc (hbc hvb), Q.part_eq_of_mem hc (hbc hwb)]
  · intro hedge b hb
    obtain ⟨v, hvb⟩ := (componentPartition H).nonempty_of_mem_parts hb
    have hvuniv : v ∈ (Finset.univ : Finset V) := Finset.mem_univ v
    refine ⟨Q.part v, Q.part_mem.mpr hvuniv, ?_⟩
    intro w hwb
    have hvreach : H.Reachable v w := by
      have hvpart : (componentPartition H).part v = b :=
        (componentPartition H).part_eq_of_mem hb hvb
      rw [← hvpart] at hwb
      exact (mem_componentPartition_part_iff_reachable H v w).mp hwb
    have heq := reachable_part_eq_of_adj_part_eq H Q hedge hvreach
    exact heq.symm ▸ Q.mem_part (Finset.mem_univ w)

/-- On a nonempty vertex type, the component partition is indiscrete exactly
when the graph is connected. -/
theorem componentPartition_eq_top_iff_connected
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) :
    componentPartition G = ⊤ ↔ G.Connected := by
  classical
  constructor
  · intro htop
    refine SimpleGraph.Connected.mk ?_
    intro v w
    apply (componentPartition_part_eq_iff_reachable G v w).mp
    rw [htop]
    apply (Finpartition.parts_top_subsingleton
      (Finset.univ : Finset V))
    · exact (⊤ : Finpartition (Finset.univ : Finset V)).part_mem.mpr
        (Finset.mem_univ v)
    · exact (⊤ : Finpartition (Finset.univ : Finset V)).part_mem.mpr
        (Finset.mem_univ w)
  · intro hconn
    apply le_antisymm le_top
    change ∀ ⦃b⦄, b ∈ (⊤ : Finpartition (Finset.univ : Finset V)).parts →
      ∃ c ∈ (componentPartition G).parts, b ⊆ c
    intro b hb
    have hbtop : b = (Finset.univ : Finset V) :=
      Finset.mem_singleton.mp
        (Finpartition.parts_top_subset (Finset.univ : Finset V) hb)
    subst b
    let v : V := Classical.choice ‹Nonempty V›
    refine ⟨(componentPartition G).part v,
      (componentPartition G).part_mem.mpr (Finset.mem_univ v), ?_⟩
    intro w _
    exact (mem_componentPartition_part_iff_reachable G v w).mpr
      (hconn.preconnected v w)

/-- On a nonempty labelled carrier, a finite partition is indiscrete exactly
when it has one part. -/
theorem finpartition_eq_top_iff_card_parts_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (Q : Finpartition (Finset.univ : Finset V)) :
    Q = ⊤ ↔ Q.parts.card = 1 := by
  classical
  have huniv : (Finset.univ : Finset V) ≠ ∅ :=
    (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty).ne_empty
  constructor
  · rintro rfl
    have hnonzero :
        (⊤ : Finpartition (Finset.univ : Finset V)).parts.card ≠ 0 :=
      Finset.card_ne_zero.mpr
        ((⊤ : Finpartition (Finset.univ : Finset V)).parts_nonempty huniv)
    have hle :
        (⊤ : Finpartition (Finset.univ : Finset V)).parts.card ≤ 1 := by
      simpa using Finset.card_le_card
        (Finpartition.parts_top_subset (Finset.univ : Finset V))
    omega
  · intro hcard
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard
    have hbuniv : b = (Finset.univ : Finset V) := by
      have hcover := Q.biUnion_parts
      rw [hb] at hcover
      simpa using hcover
    apply le_antisymm le_top
    intro t ht
    have htuniv : t = (Finset.univ : Finset V) :=
      Finset.mem_singleton.mp
        (Finpartition.parts_top_subset (Finset.univ : Finset V) ht)
    subst t
    refine ⟨b, ?_, ?_⟩
    · rw [hb]
      simp
    · rw [hbuniv]

/-- Explicit top-interval Möbius coefficient for the finite partition
lattice.  This is derived from the labelled coarsening cancellation rather
than assumed as an incidence-algebra formula. -/
theorem finpartition_mu_top_eq_partitionMobiusBlockWeight
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (Q : Finpartition (Finset.univ : Finset V)) :
    IncidenceAlgebra.mu ℤ Q ⊤ =
      partitionMobiusBlockWeight Q.parts.card := by
  classical
  let f : Finpartition (Finset.univ : Finset V) → ℤ :=
    fun R ↦ partitionMobiusBlockWeight R.parts.card
  let g : Finpartition (Finset.univ : Finset V) → ℤ :=
    fun R ↦ if R = ⊤ then 1 else 0
  have hsum : ∀ R, g R = ∑ T ∈ Finset.Ici R, f T := by
    intro R
    rw [Finset.sum_subtype (Finset.Ici R)
      (fun T ↦ Finset.mem_Ici)]
    rw [sum_finpartitionCoarsening_topMobiusWeight]
    have hparts : R.parts.card ≠ 0 := by
      exact Finset.card_ne_zero.mpr
        (R.parts_nonempty
          (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty).ne_empty)
    change (if R = ⊤ then 1 else 0) =
      if R.parts.card = 0 ∨ R.parts.card = 1 then 1 else 0
    by_cases htop : R = ⊤
    · have hcardone :=
        (finpartition_eq_top_iff_card_parts_eq_one R).mp htop
      rw [if_pos htop, if_pos (Or.inr hcardone)]
    · have hcardone : R.parts.card ≠ 1 := fun hcard ↦ htop
        ((finpartition_eq_top_iff_card_parts_eq_one R).mpr hcard)
      rw [if_neg htop, if_neg]
      exact fun h ↦ h.elim hparts hcardone
  have hinv := IncidenceAlgebra.moebius_inversion_top f g hsum Q
  dsimp only [f] at hinv
  have hcollapse :
      (∑ R ∈ Finset.Ici Q, IncidenceAlgebra.mu ℤ Q R * g R) =
        IncidenceAlgebra.mu ℤ Q ⊤ := by
    rw [Finset.sum_eq_single ⊤]
    · simp [g]
    · intro R hR hne
      simp [g, hne]
    · simp
  rw [hcollapse] at hinv
  exact hinv.symm

/-! ## Möbius regrouping by components -/

/-- Signed spanning-subgraph sum with an exactly prescribed component
partition. -/
def componentFiberSum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (R : Finpartition (Finset.univ : Finset V)) : ℤ :=
  ∑ H ∈ (spanningSubgraphs G).filter (fun H => componentPartition H = R),
    (-1 : ℤ) ^ (finiteEdges H).card

/-- Signed spanning-subgraph sum whose component partition refines `Q`. -/
def partitionRestrictedGraphSum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (Q : Finpartition (Finset.univ : Finset V)) : ℤ :=
  ∑ H ∈ (spanningSubgraphs G).filter (fun H => componentPartition H ≤ Q),
    (-1 : ℤ) ^ (finiteEdges H).card

/-- Grouping by the exact component partition. -/
theorem partitionRestrictedGraphSum_eq_sum_componentFiberSum
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (Q : Finpartition (Finset.univ : Finset V)) :
    partitionRestrictedGraphSum G Q =
      ∑ R ∈ Finset.Iic Q, componentFiberSum G R := by
  classical
  rw [partitionRestrictedGraphSum]
  symm
  simpa only [componentFiberSum, Finset.mem_Iic] using
    (Finset.sum_fiberwise_eq_sum_filter
      (spanningSubgraphs G) (Finset.Iic Q) componentPartition
      (fun H : SimpleGraph V => (-1 : ℤ) ^ (finiteEdges H).card))

/-- Signed sum over connected spanning subgraphs, expressed using the same
canonical finite edge representation as `allSpanningGraphSum`. -/
def connectedSpanningGraphSum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℤ :=
  ∑ H ∈ (spanningSubgraphs G).filter SimpleGraph.Connected,
    (-1 : ℤ) ^ (finiteEdges H).card

/-- Relabelling the vertices of a finite graph preserves the cardinality of
its canonical finite edge set. -/
theorem card_finiteEdges_map_equiv
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (e : V ≃ W) (G : SimpleGraph V) :
    (finiteEdges (G.map e.toEmbedding)).card = (finiteEdges G).card := by
  classical
  have hleft : finiteEdges (G.map e.toEmbedding) =
      (G.map e.toEmbedding).edgeFinset := by
    ext edge
    simp only [mem_finiteEdges, SimpleGraph.mem_edgeFinset]
  have hright : finiteEdges G = G.edgeFinset := by
    ext edge
    simp only [mem_finiteEdges, SimpleGraph.mem_edgeFinset]
  rw [hleft, hright, SimpleGraph.card_edgeFinset_map]

/-- The signed connected-spanning-subgraph sum is invariant under graph
isomorphism.  This is the relabelling fact needed to pass from a fixed
labelled carrier to Mayer histogram occurrence types. -/
theorem connectedSpanningGraphSum_eq_of_iso
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {K : SimpleGraph W} (e : G ≃g K) :
    connectedSpanningGraphSum G = connectedSpanningGraphSum K := by
  classical
  have hmapG : G.map e.toEquiv.toEmbedding = K := by
    ext v w
    constructor
    · rintro h
      obtain ⟨a, b, hab, rfl, rfl⟩ :=
        (SimpleGraph.map_adj e.toEquiv.toEmbedding G v w).mp h
      exact e.map_rel_iff.mpr hab
    · intro hvw
      apply (SimpleGraph.map_adj e.toEquiv.toEmbedding G v w).mpr
      exact ⟨e.symm v, e.symm w,
        e.map_rel_iff.mp (by simpa using hvw), by simp, by simp⟩
  unfold connectedSpanningGraphSum
  apply Finset.sum_bij
      (fun H (_hH : H ∈
        (spanningSubgraphs G).filter SimpleGraph.Connected) =>
          H.map e.toEquiv.toEmbedding)
  · intro H hH
    have hdata := Finset.mem_filter.mp hH
    have hHG := (Finset.mem_filter.mp hdata.1).2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (SimpleGraph.map_monotone e.toEquiv hHG).trans_eq hmapG
    · exact (SimpleGraph.Iso.map e.toEquiv H).connected_iff.mp hdata.2
  · intro H₁ _ H₂ _ heq
    exact SimpleGraph.map_injective e.toEquiv.toEmbedding heq
  · intro L hL
    let H := L.map e.symm.toEquiv.toEmbedding
    have hback : H.map e.toEquiv.toEmbedding = L := by
      ext v w
      simp [H, SimpleGraph.map_adj']
    refine ⟨H, ?_, hback⟩
    have hdata := Finset.mem_filter.mp hL
    have hLK := (Finset.mem_filter.mp hdata.1).2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro v w hvw
      have hL : L.Adj (e v) (e w) := by
        rw [← hback]
        exact (SimpleGraph.map_adj_apply).mpr hvw
      have hmap : K.Adj (e v) (e w) := hLK hL
      exact e.map_rel_iff.mp hmap
    · exact (SimpleGraph.Iso.map e.symm.toEquiv L).connected_iff.mp hdata.2
  · intro H hH
    rw [card_finiteEdges_map_equiv]

theorem connectedSpanningSubgraphs_eq_empty_of_not_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : ¬G.Connected) :
    (spanningSubgraphs G).filter SimpleGraph.Connected = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro H hH
  have hdata := (Finset.mem_filter.mp hH).2
  have hHG := (Finset.mem_filter.mp (Finset.mem_filter.mp hH).1).2
  exact hG (hdata.mono hHG)

theorem connectedSpanningGraphSum_eq_zero_of_not_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : ¬G.Connected) :
    connectedSpanningGraphSum G = 0 := by
  rw [connectedSpanningGraphSum,
    connectedSpanningSubgraphs_eq_empty_of_not_connected hG]
  simp

/-- On a nonempty vertex type, the top component fiber is precisely the
connected spanning-subgraph sum. -/
theorem componentFiberSum_top_eq_connectedSpanningGraphSum
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) :
    componentFiberSum G ⊤ = connectedSpanningGraphSum G := by
  classical
  apply Finset.sum_congr
  · ext H
    simp only [Finset.mem_filter, componentPartition_eq_top_iff_connected]
  · intro H hH
    rfl

/-- Finite-poset Möbius inversion isolates the connected component fiber.
This is the algebraic core of the labelled exponential formula. -/
theorem connectedSpanningGraphSum_eq_moebius
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) :
    connectedSpanningGraphSum G =
      ∑ Q : Finpartition (Finset.univ : Finset V),
        IncidenceAlgebra.mu ℤ Q ⊤ * partitionRestrictedGraphSum G Q := by
  classical
  let f : Finpartition (Finset.univ : Finset V) → ℤ := componentFiberSum G
  let g : Finpartition (Finset.univ : Finset V) → ℤ :=
    partitionRestrictedGraphSum G
  have hfg : ∀ Q, g Q = ∑ R ∈ Finset.Iic Q, f R := by
    intro Q
    exact partitionRestrictedGraphSum_eq_sum_componentFiberSum G Q
  have hinv := IncidenceAlgebra.moebius_inversion_bot f g hfg
    (⊤ : Finpartition (Finset.univ : Finset V))
  dsimp [f, g] at hinv
  rw [componentFiberSum_top_eq_connectedSpanningGraphSum] at hinv
  simpa [f, g] using hinv

/-! ## Cancellation inside a prescribed partition -/

/-- Whether an unordered vertex pair lies in one part of a partition. -/
def edgeWithinPartition {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V)) : Sym2 V → Prop :=
  Sym2.lift ⟨fun v w => Q.part v = Q.part w,
    fun _ _ => propext eq_comm⟩

@[simp]
theorem edgeWithinPartition_mk {V : Type*} [Fintype V]
    [DecidableEq V] (Q : Finpartition (Finset.univ : Finset V)) (v w : V) :
    edgeWithinPartition Q s(v, w) ↔ Q.part v = Q.part w := by
  rfl

/-- Ambient edges whose endpoints belong to one part of `Q`. -/
def partitionEdgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (Q : Finpartition (Finset.univ : Finset V)) : Finset (Sym2 V) := by
  classical
  exact (finiteEdges G).filter (edgeWithinPartition Q)

@[simp]
theorem mem_partitionEdgeFinset {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V)
    (Q : Finpartition (Finset.univ : Finset V))
    (e : Sym2 V) :
    e ∈ partitionEdgeFinset G Q ↔
      e ∈ G.edgeSet ∧ edgeWithinPartition Q e := by
  classical
  simp [partitionEdgeFinset]

/-- For a spanning subgraph, component refinement is exactly containment of
its selected edges in the ambient within-part edge set. -/
theorem componentPartition_le_iff_finiteEdges_subset_partitionEdgeFinset
    {V : Type*} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}
    (hHG : H ≤ G) (Q : Finpartition (Finset.univ : Finset V)) :
    componentPartition H ≤ Q ↔
      finiteEdges H ⊆ partitionEdgeFinset G Q := by
  classical
  rw [componentPartition_le_iff_adj_part_eq]
  constructor
  · intro h e he
    have heH : e ∈ H.edgeSet := (mem_finiteEdges H e).mp he
    apply (mem_partitionEdgeFinset G Q e).mpr
    refine ⟨SimpleGraph.edgeSet_mono hHG heH, ?_⟩
    induction e using Sym2.inductionOn with
    | _ v w =>
        exact (edgeWithinPartition_mk Q v w).mpr
          (h ((SimpleGraph.mem_edgeSet H).mp heH))
  · intro h v w hvw
    have heH : s(v, w) ∈ finiteEdges H :=
      (mem_finiteEdges H _).mpr ((SimpleGraph.mem_edgeSet H).mpr hvw)
    have he := (mem_partitionEdgeFinset G Q _).mp (h heH)
    exact (edgeWithinPartition_mk Q v w).mp he.2

/-- The restricted graph sum is a signed powerset sum over precisely the
ambient edges lying inside parts of `Q`. -/
theorem partitionRestrictedGraphSum_eq_powerset
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (Q : Finpartition (Finset.univ : Finset V)) :
    partitionRestrictedGraphSum G Q =
      ∑ s ∈ (partitionEdgeFinset G Q).powerset,
        (-1 : ℤ) ^ s.card := by
  unfold partitionRestrictedGraphSum
  apply Finset.sum_bij (fun H _ => finiteEdges H)
  · intro H hH
    have hdata := (Finset.mem_filter.mp hH).2
    have hHG := (Finset.mem_filter.mp (Finset.mem_filter.mp hH).1).2
    exact Finset.mem_powerset.mpr
      ((componentPartition_le_iff_finiteEdges_subset_partitionEdgeFinset
        hHG Q).mp hdata)
  · intro H₁ _ H₂ _ h
    exact finiteEdges_inj h
  · intro s hs
    have hsQ : s ⊆ partitionEdgeFinset G Q := Finset.mem_powerset.mp hs
    have hsG : s ⊆ finiteEdges G := by
      intro e he
      exact (mem_finiteEdges G e).mpr
        ((mem_partitionEdgeFinset G Q e).mp (hsQ he)).1
    let H := SimpleGraph.fromEdgeSet (s : Set (Sym2 V))
    have hHE : finiteEdges H = s := finiteEdges_fromEdgeFinset G s hsG
    have hHG : H ≤ G :=
      finiteEdges_subset_finiteEdges.mp (hHE.trans_le hsG)
    have hHQ : componentPartition H ≤ Q :=
      (componentPartition_le_iff_finiteEdges_subset_partitionEdgeFinset
        hHG Q).mpr (hHE.trans_le hsQ)
    refine ⟨H, Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHG⟩, hHQ⟩, hHE⟩
  · intro H hH
    rfl

/-- Inclusion--exclusion inside the parts of `Q`. -/
theorem partitionRestrictedGraphSum_eq_if
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (Q : Finpartition (Finset.univ : Finset V)) :
    partitionRestrictedGraphSum G Q =
      if partitionEdgeFinset G Q = ∅ then 1 else 0 := by
  rw [partitionRestrictedGraphSum_eq_powerset,
    Finset.sum_powerset_neg_one_pow_card]

/-- Cumulant form of the connected-graph sum.  The only surviving partition
moments are those whose parts contain no ambient edge. -/
theorem connectedSpanningGraphSum_eq_moebius_cancellation
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) :
    connectedSpanningGraphSum G =
      ∑ Q : Finpartition (Finset.univ : Finset V),
        IncidenceAlgebra.mu ℤ Q ⊤ *
          (if partitionEdgeFinset G Q = ∅ then 1 else 0) := by
  rw [connectedSpanningGraphSum_eq_moebius]
  apply Finset.sum_congr rfl
  intro Q _
  rw [partitionRestrictedGraphSum_eq_if]

/-- Connected graph cumulants with the explicit labelled-partition Möbius
coefficient.  This is the factorial coefficient used by the ordinary Mayer
multi-index normalization. -/
theorem connectedSpanningGraphSum_eq_partitionMobius_cancellation
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) :
    connectedSpanningGraphSum G =
      ∑ Q : Finpartition (Finset.univ : Finset V),
        partitionMobiusBlockWeight Q.parts.card *
          (if partitionEdgeFinset G Q = ∅ then 1 else 0) := by
  rw [connectedSpanningGraphSum_eq_moebius_cancellation]
  apply Finset.sum_congr rfl
  intro Q _
  rw [finpartition_mu_top_eq_partitionMobiusBlockWeight]

end

end YangMills.Polymer
