/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.Penrose
import Mathlib.Data.Fintype.EquivFin

/-!
# Whitney broken-circuit cancellation

This file implements the ordered sign-reversing involution behind the sharp
tree-graph inequality.  For an ordered edge set `A`, an ambient edge `e` is
active when its endpoints are already joined by edges of `A` strictly below
`e`.  Toggling the least active edge preserves connectedness and reverses the
edge-cardinality sign.  The fixed connected edge sets are forests, hence
spanning trees.

The construction is entirely graph/combinatorics based and supplies the
model-independent tree-graph estimate used by the polymer expansion.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

namespace Whitney

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A simple graph represented by a finite set of undirected edges. -/
def edgeGraph (A : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (A : Set (Sym2 V))

theorem edgeGraph_mono {A B : Finset (Sym2 V)} (hAB : A ⊆ B) :
    edgeGraph A ≤ edgeGraph B := by
  apply SimpleGraph.fromEdgeSet_mono
  simpa using hAB

@[simp]
theorem edgeGraph_empty : edgeGraph (∅ : Finset (Sym2 V)) = ⊥ := by
  simp [edgeGraph]

/-- The graph consisting of the edges of `A` whose ranks are strictly below
the rank of `e`. -/
def lowerEdgeGraph (rank : Sym2 V → ℕ)
    (A : Finset (Sym2 V)) (e : Sym2 V) : SimpleGraph V := by
  classical
  exact SimpleGraph.fromEdgeSet (A.filter (fun f => rank f < rank e) : Set (Sym2 V))

/-- The endpoints of `e` are joined by edges of `A` strictly below `e`. -/
def LowerReachable (rank : Sym2 V → ℕ)
    (A : Finset (Sym2 V)) (e : Sym2 V) : Prop :=
  Sym2.lift
    ⟨fun v w => (lowerEdgeGraph rank A e).Reachable v w,
      fun _ _ => propext SimpleGraph.reachable_comm⟩ e

@[simp]
theorem lowerReachable_mk (rank : Sym2 V → ℕ)
    (A : Finset (Sym2 V)) (v w : V) :
    LowerReachable rank A s(v, w) ↔
      (lowerEdgeGraph rank A s(v, w)).Reachable v w := by
  rfl

/-- Ambient edges whose endpoints are already connected below that edge. -/
def activeEdges (rank : Sym2 V → ℕ) (G : SimpleGraph V)
    (A : Finset (Sym2 V)) : Finset (Sym2 V) := by
  classical
  exact (finiteEdges G).filter (LowerReachable rank A)

@[simp]
theorem mem_activeEdges (rank : Sym2 V → ℕ) {G : SimpleGraph V}
    {A : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ activeEdges rank G A ↔
      e ∈ finiteEdges G ∧ LowerReachable rank A e := by
  simp [activeEdges]

/-- Toggle one edge in a finite edge set. -/
def toggle (A : Finset (Sym2 V)) (e : Sym2 V) : Finset (Sym2 V) :=
  if e ∈ A then A.erase e else insert e A

@[simp]
theorem mem_toggle_self (A : Finset (Sym2 V)) (e : Sym2 V) :
    e ∈ toggle A e ↔ e ∉ A := by
  by_cases he : e ∈ A <;> simp [toggle, he]

@[simp]
theorem mem_toggle_of_ne (A : Finset (Sym2 V)) {e f : Sym2 V}
    (hfe : f ≠ e) : f ∈ toggle A e ↔ f ∈ A := by
  by_cases he : e ∈ A <;> simp [toggle, he, hfe]

@[simp]
theorem toggle_toggle (A : Finset (Sym2 V)) (e : Sym2 V) :
    toggle (toggle A e) e = A := by
  ext f
  by_cases hfe : f = e
  · subst f
    simp
  · simp [mem_toggle_of_ne, hfe]

theorem lowerEdgeGraph_toggle_of_rank_le (rank : Sym2 V → ℕ)
    (A : Finset (Sym2 V)) {e f : Sym2 V} (hfe : rank f ≤ rank e) :
    lowerEdgeGraph rank (toggle A e) f = lowerEdgeGraph rank A f := by
  ext u v
  simp only [lowerEdgeGraph, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
    Finset.mem_filter]
  constructor
  · rintro ⟨⟨huv, hlt⟩, hne⟩
    refine ⟨⟨?_, hlt⟩, hne⟩
    exact (mem_toggle_of_ne A (fun h => by rw [h] at hlt; omega)).mp huv
  · rintro ⟨⟨huv, hlt⟩, hne⟩
    refine ⟨⟨?_, hlt⟩, hne⟩
    exact (mem_toggle_of_ne A (fun h => by rw [h] at hlt; omega)).mpr huv

theorem lowerReachable_toggle_of_rank_le (rank : Sym2 V → ℕ)
    (A : Finset (Sym2 V)) {e f : Sym2 V} (hfe : rank f ≤ rank e) :
    LowerReachable rank (toggle A e) f ↔ LowerReachable rank A f := by
  induction f using Sym2.ind with
  | _ u v =>
      simp only [lowerReachable_mk,
        lowerEdgeGraph_toggle_of_rank_le rank A hfe]

theorem lowerEdgeGraph_eq_edgeGraph_filter (rank : Sym2 V → ℕ)
    (A : Finset (Sym2 V)) (e : Sym2 V) :
    lowerEdgeGraph rank A e = edgeGraph (A.filter (fun f => rank f < rank e)) := by
  rfl

theorem lowerEdgeGraph_insert_max (rank : Sym2 V → ℕ)
    (a : Sym2 V) (A : Finset (Sym2 V))
    (ha : ∀ e ∈ A, rank e < rank a) :
    lowerEdgeGraph rank (insert a A) a = edgeGraph A := by
  rw [lowerEdgeGraph_eq_edgeGraph_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | heA, hea⟩
    · exact (lt_irrefl _ hea).elim
    · exact heA
  · intro heA
    exact ⟨Or.inr heA, ha e heA⟩

theorem edgeGraph_insert_mk (A : Finset (Sym2 V)) (u v : V) :
    edgeGraph (insert s(u, v) A) = edgeGraph A ⊔ SimpleGraph.edge u v := by
  ext x y
  simp only [edgeGraph, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
    Finset.mem_insert, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  grind [Sym2.eq_iff]

theorem lowerEdgeGraph_insert_of_rank_lt (rank : Sym2 V → ℕ)
    (A : Finset (Sym2 V)) {a e : Sym2 V} (hea : rank e < rank a) :
    lowerEdgeGraph rank (insert a A) e = lowerEdgeGraph rank A e := by
  ext u v
  simp only [lowerEdgeGraph, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
    Finset.mem_filter, Finset.mem_insert]
  constructor <;> rintro ⟨⟨hmem, hlt⟩, hne⟩
  · refine ⟨⟨?_, hlt⟩, hne⟩
    rcases hmem with hEq | hA
    · subst a
      exact (lt_asymm hea hlt).elim
    · exact hA
  · exact ⟨⟨Or.inr hmem, hlt⟩, hne⟩

/-- Inserting edges in increasing order shows that a finite edge set with no
lower-reachable edge is acyclic. -/
theorem edgeGraph_isAcyclic_of_forall_not_lowerReachable
    (rank : Sym2 V → ℕ) (hrank : Function.Injective rank)
    {A : Finset (Sym2 V)}
    (hdiag : ∀ e ∈ A, e ∉ Sym2.diagSet)
    (hactive : ∀ e ∈ A, ¬ LowerReachable rank A e) :
    (edgeGraph A).IsAcyclic := by
  induction A using Finset.induction_on_max_value rank with
  | empty => simp
  | @insert a A haA ha hA =>
      have ha_strict : ∀ e ∈ A, rank e < rank a := by
        intro e heA
        have hea : e ≠ a := fun h => haA (h ▸ heA)
        exact (ha e heA).lt_of_ne (fun h => hea (hrank h))
      have hactiveA : ∀ e ∈ A, ¬ LowerReachable rank A e := by
        intro e heA hre
        apply hactive e (Finset.mem_insert_of_mem heA)
        induction e using Sym2.ind with
        | _ u v =>
            rw [lowerReachable_mk] at hre ⊢
            rwa [lowerEdgeGraph_insert_of_rank_lt rank A (ha_strict s(u, v) heA)]
      have hacycA : (edgeGraph A).IsAcyclic :=
        hA (fun e heA => hdiag e (Finset.mem_insert_of_mem heA)) hactiveA
      induction a using Sym2.ind with
      | _ u v =>
          have huv : u ≠ v := by
            simpa [Sym2.mem_diagSet, Sym2.mk_isDiag_iff] using
              hdiag s(u, v) (Finset.mem_insert_self _ _)
          rw [edgeGraph_insert_mk]
          apply hacycA.sup_edge_of_not_reachable
          intro hre
          apply hactive s(u, v) (Finset.mem_insert_self _ _)
          rw [lowerReachable_mk,
            lowerEdgeGraph_insert_max rank s(u, v) A ha_strict]
          exact hre

/-! ## The least-active-edge pivot -/

/-- The least rank occurring among the active edges. -/
def firstActiveRank (rank : Sym2 V → ℕ) (G : SimpleGraph V)
    (A : Finset (Sym2 V)) (h : (activeEdges rank G A).Nonempty) : ℕ :=
  ((activeEdges rank G A).image rank).min' (h.image rank)

private theorem exists_active_of_rank_eq_firstActiveRank
    (rank : Sym2 V → ℕ) (G : SimpleGraph V) (A : Finset (Sym2 V))
    (h : (activeEdges rank G A).Nonempty) :
    ∃ e ∈ activeEdges rank G A, rank e = firstActiveRank rank G A h := by
  have hmin := Finset.min'_mem ((activeEdges rank G A).image rank) (h.image rank)
  simpa [firstActiveRank] using Finset.mem_image.mp hmin

/-- The active edge of least rank. -/
def firstActive (rank : Sym2 V → ℕ) (G : SimpleGraph V)
    (A : Finset (Sym2 V)) (h : (activeEdges rank G A).Nonempty) : Sym2 V :=
  Classical.choose (exists_active_of_rank_eq_firstActiveRank rank G A h)

theorem firstActive_mem (rank : Sym2 V → ℕ) (G : SimpleGraph V)
    (A : Finset (Sym2 V)) (h : (activeEdges rank G A).Nonempty) :
    firstActive rank G A h ∈ activeEdges rank G A :=
  (Classical.choose_spec
    (exists_active_of_rank_eq_firstActiveRank rank G A h)).1

theorem rank_firstActive_eq (rank : Sym2 V → ℕ) (G : SimpleGraph V)
    (A : Finset (Sym2 V)) (h : (activeEdges rank G A).Nonempty) :
    rank (firstActive rank G A h) = firstActiveRank rank G A h :=
  (Classical.choose_spec
    (exists_active_of_rank_eq_firstActiveRank rank G A h)).2

theorem rank_firstActive_le (rank : Sym2 V → ℕ) (G : SimpleGraph V)
    (A : Finset (Sym2 V)) (h : (activeEdges rank G A).Nonempty)
    {e : Sym2 V} (he : e ∈ activeEdges rank G A) :
    rank (firstActive rank G A h) ≤ rank e := by
  calc
    rank (firstActive rank G A h) = firstActiveRank rank G A h :=
      rank_firstActive_eq rank G A h
    _ ≤ rank e := Finset.min'_le ((activeEdges rank G A).image rank) _
      (Finset.mem_image.mpr ⟨e, he, rfl⟩)

theorem firstActive_mem_activeEdges_toggle
    (rank : Sym2 V → ℕ) (G : SimpleGraph V) (A : Finset (Sym2 V))
    (h : (activeEdges rank G A).Nonempty) :
    firstActive rank G A h ∈
      activeEdges rank G (toggle A (firstActive rank G A h)) := by
  rw [mem_activeEdges] at ⊢
  refine ⟨(mem_activeEdges rank).mp (firstActive_mem rank G A h) |>.1, ?_⟩
  rw [lowerReachable_toggle_of_rank_le rank A (le_refl _)]
  exact (mem_activeEdges rank).mp (firstActive_mem rank G A h) |>.2

theorem firstActive_toggle
    (rank : Sym2 V → ℕ) (hrank : Function.Injective rank)
    (G : SimpleGraph V) (A : Finset (Sym2 V))
    (h : (activeEdges rank G A).Nonempty) :
    firstActive rank G (toggle A (firstActive rank G A h))
        ⟨firstActive rank G A h,
          firstActive_mem_activeEdges_toggle rank G A h⟩ =
      firstActive rank G A h := by
  let e := firstActive rank G A h
  let htoggle : (activeEdges rank G (toggle A e)).Nonempty :=
    ⟨e, firstActive_mem_activeEdges_toggle rank G A h⟩
  apply hrank
  apply le_antisymm
  · exact rank_firstActive_le rank G (toggle A e) htoggle
      (firstActive_mem_activeEdges_toggle rank G A h)
  · let f := firstActive rank G (toggle A e) htoggle
    have hfe : rank f ≤ rank e :=
      rank_firstActive_le rank G (toggle A e) htoggle
        (firstActive_mem_activeEdges_toggle rank G A h)
    apply rank_firstActive_le rank G A h
    rw [mem_activeEdges] at ⊢
    have hf := (mem_activeEdges rank).mp
      (firstActive_mem rank G (toggle A e) htoggle)
    refine ⟨hf.1, ?_⟩
    rw [← lowerReachable_toggle_of_rank_le rank A hfe]
    exact hf.2

/-! ## Preservation of the connected spanning family -/

theorem lowerEdgeGraph_le_edgeGraph_toggle (rank : Sym2 V → ℕ)
    (A : Finset (Sym2 V)) (e : Sym2 V) :
    lowerEdgeGraph rank A e ≤ edgeGraph (toggle A e) := by
  apply SimpleGraph.fromEdgeSet_mono
  intro f hf
  simp only [Finset.mem_coe, Finset.mem_filter] at hf ⊢
  exact (mem_toggle_of_ne A (fun h => by subst f; omega)).mpr hf.1

theorem edgeGraph_toggle_eq_deleteEdges_of_mem
    (A : Finset (Sym2 V)) {e : Sym2 V} (heA : e ∈ A) :
    edgeGraph (toggle A e) = (edgeGraph A).deleteEdges {e} := by
  rw [toggle, if_pos heA]
  ext u v
  simp only [edgeGraph, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
    Finset.mem_erase, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  tauto

theorem edgeGraph_toggle_connected
    (rank : Sym2 V → ℕ) (G : SimpleGraph V) (A : Finset (Sym2 V))
    (hconn : (edgeGraph A).Connected)
    {e : Sym2 V} (he : e ∈ activeEdges rank G A) :
    (edgeGraph (toggle A e)).Connected := by
  by_cases heA : e ∈ A
  · rw [edgeGraph_toggle_eq_deleteEdges_of_mem A heA]
    induction e using Sym2.ind with
    | _ u v =>
        apply hconn.connected_delete_edge_of_not_isBridge
        rw [SimpleGraph.isBridge_iff]
        push Not
        intro _hadj
        have hre := (mem_activeEdges rank).mp he |>.2
        rw [lowerReachable_mk] at hre
        exact hre.mono (by
          rw [← edgeGraph_toggle_eq_deleteEdges_of_mem A heA]
          exact lowerEdgeGraph_le_edgeGraph_toggle rank A s(u, v))
  · apply hconn.mono (edgeGraph_mono ?_)
    intro f hf
    exact (mem_toggle_of_ne A (fun h => by subst f; exact heA hf)).mpr hf

theorem toggle_subset_finiteEdges
    (rank : Sym2 V → ℕ) (G : SimpleGraph V) (A : Finset (Sym2 V))
    (hAG : A ⊆ finiteEdges G) {e : Sym2 V}
    (he : e ∈ activeEdges rank G A) :
    toggle A e ⊆ finiteEdges G := by
  intro f hf
  by_cases hfe : f = e
  · subst f
    exact (mem_activeEdges rank).mp he |>.1
  · exact hAG ((mem_toggle_of_ne A hfe).mp hf)

theorem finiteEdges_edgeGraph_of_subset
    (G : SimpleGraph V) {A : Finset (Sym2 V)}
    (hAG : A ⊆ finiteEdges G) :
    finiteEdges (edgeGraph A) = A := by
  ext e
  rw [mem_finiteEdges, edgeGraph, SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_diff, Finset.mem_coe]
  constructor
  · exact fun h => h.1
  · intro heA
    refine ⟨heA, ?_⟩
    exact G.not_isDiag_of_mem_edgeSet ((mem_finiteEdges G e).mp (hAG heA))

theorem mem_connectedSpanningEdgeFamilies_iff
    (G : SimpleGraph V) {A : Finset (Sym2 V)} :
    A ∈ connectedSpanningEdgeFamilies G ↔
      A ⊆ finiteEdges G ∧ (edgeGraph A).Connected := by
  classical
  unfold connectedSpanningEdgeFamilies
  constructor
  · intro hA
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hA
    have hHG : H ≤ G := (Finset.mem_filter.mp (Finset.mem_filter.mp hH).1).2
    refine ⟨finiteEdges_subset_finiteEdges.mpr hHG, ?_⟩
    have hedge : edgeGraph (finiteEdges H) = H :=
      finiteEdges_inj (finiteEdges_edgeGraph_of_subset H Finset.Subset.rfl)
    rw [hedge]
    exact (Finset.mem_filter.mp hH).2
  · rintro ⟨hAG, hconn⟩
    let H := edgeGraph A
    have hHE : finiteEdges H = A := finiteEdges_edgeGraph_of_subset G hAG
    apply Finset.mem_image.mpr
    refine ⟨H, ?_, hHE⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hconn⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, finiteEdges_subset_finiteEdges.mp (hHE.trans_le hAG)⟩

theorem mem_spanningTreeEdgeFamilies_iff
    (G : SimpleGraph V) {A : Finset (Sym2 V)} :
    A ∈ spanningTreeEdgeFamilies G ↔
      A ⊆ finiteEdges G ∧ (edgeGraph A).IsTree := by
  classical
  unfold spanningTreeEdgeFamilies graphSpanningTrees
  constructor
  · intro hA
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hA
    have hTG : T ≤ G := (Finset.mem_filter.mp (Finset.mem_filter.mp hT).1).2
    refine ⟨finiteEdges_subset_finiteEdges.mpr hTG, ?_⟩
    have hedge : edgeGraph (finiteEdges T) = T :=
      finiteEdges_inj (finiteEdges_edgeGraph_of_subset T Finset.Subset.rfl)
    rw [hedge]
    exact (Finset.mem_filter.mp hT).2
  · rintro ⟨hAG, htree⟩
    let T := edgeGraph A
    have hTE : finiteEdges T = A := finiteEdges_edgeGraph_of_subset G hAG
    apply Finset.mem_image.mpr
    refine ⟨T, ?_, hTE⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, htree⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, finiteEdges_subset_finiteEdges.mp (hTE.trans_le hAG)⟩

/-- Connected spanning edge sets possessing an active edge. -/
def activeConnectedEdgeFamilies (rank : Sym2 V → ℕ) (G : SimpleGraph V) :
    Finset (Finset (Sym2 V)) :=
  (connectedSpanningEdgeFamilies G).filter fun A =>
    (activeEdges rank G A).Nonempty

@[simp]
theorem mem_activeConnectedEdgeFamilies (rank : Sym2 V → ℕ)
    (G : SimpleGraph V) {A : Finset (Sym2 V)} :
    A ∈ activeConnectedEdgeFamilies rank G ↔
      A ∈ connectedSpanningEdgeFamilies G ∧
        (activeEdges rank G A).Nonempty := by
  simp [activeConnectedEdgeFamilies]

theorem toggle_mem_activeConnectedEdgeFamilies
    (rank : Sym2 V → ℕ) (G : SimpleGraph V) (A : Finset (Sym2 V))
    (hA : A ∈ activeConnectedEdgeFamilies rank G) :
    toggle A (firstActive rank G A
      ((mem_activeConnectedEdgeFamilies rank G).mp hA).2) ∈
      activeConnectedEdgeFamilies rank G := by
  let hactive := ((mem_activeConnectedEdgeFamilies rank G).mp hA).2
  let e := firstActive rank G A hactive
  have he : e ∈ activeEdges rank G A := firstActive_mem rank G A hactive
  have hfamily := (mem_activeConnectedEdgeFamilies rank G).mp hA |>.1
  have hchar := (mem_connectedSpanningEdgeFamilies_iff G).mp hfamily
  apply (mem_activeConnectedEdgeFamilies rank G).mpr
  refine ⟨(mem_connectedSpanningEdgeFamilies_iff G).mpr ⟨?_, ?_⟩, ?_⟩
  · exact toggle_subset_finiteEdges rank G A hchar.1 he
  · exact edgeGraph_toggle_connected rank G A hchar.2 he
  · exact ⟨e, firstActive_mem_activeEdges_toggle rank G A hactive⟩

theorem negOnePow_card_add_toggle
    (A : Finset (Sym2 V)) (e : Sym2 V) :
    (-1 : ℤ) ^ A.card + (-1 : ℤ) ^ (toggle A e).card = 0 := by
  by_cases he : e ∈ A
  · have hcard : A.card = (A.erase e).card + 1 :=
      (Finset.card_erase_add_one he).symm
    rw [toggle, if_pos he, hcard, pow_succ]
    ring
  · rw [toggle, if_neg he, Finset.card_insert_of_notMem he, pow_succ]
    ring

theorem toggle_firstActive_ne
    (rank : Sym2 V → ℕ) (G : SimpleGraph V) (A : Finset (Sym2 V))
    (h : (activeEdges rank G A).Nonempty) :
    toggle A (firstActive rank G A h) ≠ A := by
  intro hEq
  have := Finset.ext_iff.mp hEq (firstActive rank G A h)
  simp at this

theorem toggle_firstActive_involutive
    (rank : Sym2 V → ℕ) (hrank : Function.Injective rank)
    (G : SimpleGraph V) (A : Finset (Sym2 V))
    (hA : A ∈ activeConnectedEdgeFamilies rank G) :
    let B := toggle A (firstActive rank G A
      ((mem_activeConnectedEdgeFamilies rank G).mp hA).2)
    let hB := toggle_mem_activeConnectedEdgeFamilies rank G A hA
    toggle B (firstActive rank G B
      ((mem_activeConnectedEdgeFamilies rank G).mp hB).2) = A := by
  dsimp only
  rw [firstActive_toggle rank hrank G A
    ((mem_activeConnectedEdgeFamilies rank G).mp hA).2]
  exact toggle_toggle A _

/-- Whitney's sign-reversing involution cancels every connected spanning edge
set with an active edge. -/
theorem sum_activeConnectedEdgeFamilies_eq_zero
    (rank : Sym2 V → ℕ) (hrank : Function.Injective rank)
    (G : SimpleGraph V) :
    ∑ A ∈ activeConnectedEdgeFamilies rank G, (-1 : ℤ) ^ A.card = 0 := by
  classical
  apply Finset.sum_involution
    (fun A hA => toggle A (firstActive rank G A
      ((mem_activeConnectedEdgeFamilies rank G).mp hA).2))
  · intro A hA
    exact negOnePow_card_add_toggle A _
  · intro A hA _
    exact toggle_firstActive_ne rank G A
      ((mem_activeConnectedEdgeFamilies rank G).mp hA).2
  · intro A hA
    exact toggle_firstActive_involutive rank hrank G A hA
  · intro A hA
    exact toggle_mem_activeConnectedEdgeFamilies rank G A hA

/-- Connected spanning edge sets fixed by the Whitney involution. -/
def inactiveConnectedEdgeFamilies (rank : Sym2 V → ℕ) (G : SimpleGraph V) :
    Finset (Finset (Sym2 V)) :=
  (connectedSpanningEdgeFamilies G).filter fun A =>
    ¬(activeEdges rank G A).Nonempty

@[simp]
theorem mem_inactiveConnectedEdgeFamilies (rank : Sym2 V → ℕ)
    (G : SimpleGraph V) {A : Finset (Sym2 V)} :
    A ∈ inactiveConnectedEdgeFamilies rank G ↔
      A ∈ connectedSpanningEdgeFamilies G ∧
        ¬(activeEdges rank G A).Nonempty := by
  simp [inactiveConnectedEdgeFamilies]

theorem inactiveConnectedEdgeFamilies_subset_spanningTreeEdgeFamilies
    (rank : Sym2 V → ℕ) (hrank : Function.Injective rank)
    (G : SimpleGraph V) :
    inactiveConnectedEdgeFamilies rank G ⊆ spanningTreeEdgeFamilies G := by
  intro A hA
  have hmem := (mem_inactiveConnectedEdgeFamilies rank G).mp hA
  have hchar := (mem_connectedSpanningEdgeFamilies_iff G).mp hmem.1
  apply (mem_spanningTreeEdgeFamilies_iff G).mpr
  refine ⟨hchar.1, ⟨hchar.2, ?_⟩⟩
  apply edgeGraph_isAcyclic_of_forall_not_lowerReachable rank hrank
  · intro e heA
    exact G.not_isDiag_of_mem_edgeSet
      ((mem_finiteEdges G e).mp (hchar.1 heA))
  · intro e heA hre
    apply hmem.2
    refine ⟨e, (mem_activeEdges rank).mpr ⟨hchar.1 heA, hre⟩⟩

theorem connectedEdgeFamilySum_eq_inactive
    (rank : Sym2 V → ℕ) (hrank : Function.Injective rank)
    (G : SimpleGraph V) :
    ∑ A ∈ connectedSpanningEdgeFamilies G, (-1 : ℤ) ^ A.card =
      ∑ A ∈ inactiveConnectedEdgeFamilies rank G, (-1 : ℤ) ^ A.card := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (connectedSpanningEdgeFamilies G)
    (fun A => (activeEdges rank G A).Nonempty)
    (fun A => (-1 : ℤ) ^ A.card)
  have hzero := sum_activeConnectedEdgeFamilies_eq_zero rank hrank G
  rw [show (connectedSpanningEdgeFamilies G).filter
      (fun A => (activeEdges rank G A).Nonempty) =
        activeConnectedEdgeFamilies rank G from rfl, hzero, zero_add] at hsplit
  rw [show (connectedSpanningEdgeFamilies G).filter
      (fun A => ¬(activeEdges rank G A).Nonempty) =
        inactiveConnectedEdgeFamilies rank G from rfl] at hsplit
  exact hsplit.symm

theorem abs_connectedEdgeFamilySum_le_card_trees
    (rank : Sym2 V → ℕ) (hrank : Function.Injective rank)
    (G : SimpleGraph V) :
    |∑ A ∈ connectedSpanningEdgeFamilies G, (-1 : ℤ) ^ A.card| ≤
      (spanningTreeEdgeFamilies G).card := by
  rw [connectedEdgeFamilySum_eq_inactive rank hrank G]
  calc
    |∑ A ∈ inactiveConnectedEdgeFamilies rank G, (-1 : ℤ) ^ A.card| ≤
        ∑ A ∈ inactiveConnectedEdgeFamilies rank G,
          |(-1 : ℤ) ^ A.card| := Finset.abs_sum_le_sum_abs _ _
    _ = (inactiveConnectedEdgeFamilies rank G).card := by simp
    _ ≤ (spanningTreeEdgeFamilies G).card := by
      exact_mod_cast Finset.card_le_card
        (inactiveConnectedEdgeFamilies_subset_spanningTreeEdgeFamilies rank hrank G)

/-- A canonical injective numeric rank on the finite undirected edge type. -/
def canonicalEdgeRank (e : Sym2 V) : ℕ :=
  (Fintype.equivFin (Sym2 V) e).val

theorem canonicalEdgeRank_injective :
    Function.Injective (canonicalEdgeRank (V := V)) := by
  intro e f hef
  apply (Fintype.equivFin (Sym2 V)).injective
  apply Fin.ext
  exact hef

/-- The unconditional sharp Whitney tree-graph inequality in edge-finset
form. -/
theorem abs_connectedEdgeFamilySum_le_card_trees_canonical
    (G : SimpleGraph V) :
    |∑ A ∈ connectedSpanningEdgeFamilies G, (-1 : ℤ) ^ A.card| ≤
      (spanningTreeEdgeFamilies G).card :=
  abs_connectedEdgeFamilySum_le_card_trees canonicalEdgeRank
    (canonicalEdgeRank_injective (V := V)) G

/-- The sharp tree-graph inequality for every finite simple graph, proved by
the concrete Whitney broken-circuit involution.  Unlike the abstract Penrose
interface, this theorem requires no interval-scheme hypothesis. -/
theorem abs_connectedSpanningGraphSum_le_card_trees
    (G : SimpleGraph V) :
    |connectedSpanningGraphSum G| ≤ (graphSpanningTrees G).card := by
  rw [GraphPenroseScheme.connectedSpanningGraphSum_eq_edgeFamilySum,
    ← GraphPenroseScheme.card_spanningTreeEdgeFamilies]
  exact abs_connectedEdgeFamilySum_le_card_trees_canonical G

end Whitney

end

end YangMills.Polymer
