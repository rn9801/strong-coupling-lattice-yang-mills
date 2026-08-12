/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.PlaquettePolymer
import YangMills.Polymer.Dobrushin
import YangMills.Polymer.KoteckyPreiss
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Counting certificates and an explicit strong-coupling radius

This module separates lattice combinatorics from the numerical part of the KP
argument.  `AnimalCountingCertificate` records a proved degree and rooted
connected-animal estimate for a finite graph.  The geometric tail and the
conversion from a small-coupling disk to the scalar KP inequality are proved
once and for all.
-/

namespace YangMills.StrongCoupling

open Polymer

noncomputable section

open Lattice.Cubic

local instance {d : ℕ} : DecidableEq (Plaquette d) := Classical.decEq _

/-! ## Uniform plaquette incidence and adjacency bounds -/

/-- The four stored positive edges around a coordinate plaquette. -/
theorem plaquette_boundary_edgeSupport {d : ℕ} (p : Plaquette d) :
    p.boundary.edgeSupport =
      { ⟨p.base, p.first⟩,
        ⟨step p.base (.forward p.first), p.second⟩,
        ⟨step p.base (.forward p.second), p.first⟩,
        ⟨p.base, p.second⟩ } := by
  have h₃ : p.base + unitVector p.first + unitVector p.second +
      -unitVector p.first = p.base + unitVector p.second := by abel
  simp only [Plaquette.boundary, Path.rectangleBoundary, SignedDirection.forward,
    Path.advance, step, SignedDirection.delta, SignedDirection.backward,
    Path.rectangleRaw, Path.straight, Nat.reduceAdd, edgeFrom, SignedEdge.toArrow,
    SignedEdge.target, h₃, Quiver.Path.comp_cons, Quiver.Path.comp_nil,
    Path.edgeSupport_castTarget, Path.edgeSupport_cons, SignedEdge.positive,
    add_neg_cancel_right, Path.edgeSupport_nil, insert_empty_eq]
  apply Finset.ext
  intro e
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- Translation carries the four stored positive boundary edges of a
plaquette to the boundary edges of the translated plaquette. -/
theorem plaquette_boundary_edgeSupport_translate {d : ℕ}
    (v : Site d) (p : Plaquette d) :
    (p.translate v).boundary.edgeSupport =
      p.boundary.edgeSupport.map
        (PositiveEdge.translationEquiv v).toEmbedding := by
  rw [plaquette_boundary_edgeSupport, plaquette_boundary_edgeSupport]
  simp [PositiveEdge.translationEquiv, PositiveEdge.translate,
    Plaquette.translate, translate_step]

/-- Every plaquette containing `e` is one of four placements for a choice of
the other coordinate direction. -/
def incidentPlaquettes {d : ℕ} (e : PositiveEdge d) : Finset (Plaquette d) := by
  classical
  exact (Finset.univ : Finset {j : Fin d // j ≠ e.direction}).biUnion fun j =>
    { ⟨e.source, e.direction, j, j.2.symm⟩,
      ⟨e.source - unitVector j, e.direction, j, j.2.symm⟩,
      ⟨e.source, j, e.direction, j.2⟩,
      ⟨e.source - unitVector j, j, e.direction, j.2⟩ }

theorem mem_incidentPlaquettes_of_mem_boundary {d : ℕ}
    (e : PositiveEdge d) (p : Plaquette d)
    (he : e ∈ p.boundary.edgeSupport) : p ∈ incidentPlaquettes e := by
  classical
  rw [plaquette_boundary_edgeSupport] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with h₁ | h₂ | h₃ | h₄
  · have hd : e.direction = p.first := congrArg PositiveEdge.direction h₁
    have hb : e.source = p.base := congrArg PositiveEdge.source h₁
    let j : {j : Fin d // j ≠ e.direction} :=
      ⟨p.second, fun h => p.distinct (hd.symm.trans h.symm)⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    apply Finset.mem_insert.mpr
    left
    cases p
    simp_all [j]
  · have hd : e.direction = p.second := congrArg PositiveEdge.direction h₂
    have hb : e.source = step p.base (.forward p.first) :=
      congrArg PositiveEdge.source h₂
    let j : {j : Fin d // j ≠ e.direction} :=
      ⟨p.first, fun h => p.distinct (h.trans hd)⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    apply Finset.mem_insert.mpr; right
    apply Finset.mem_insert.mpr; right
    apply Finset.mem_insert.mpr; right
    apply Finset.mem_singleton.mpr
    cases p
    simp_all [j, step]
  · have hd : e.direction = p.first := congrArg PositiveEdge.direction h₃
    have hb : e.source = step p.base (.forward p.second) :=
      congrArg PositiveEdge.source h₃
    let j : {j : Fin d // j ≠ e.direction} :=
      ⟨p.second, fun h => p.distinct (hd.symm.trans h.symm)⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    apply Finset.mem_insert.mpr; right
    apply Finset.mem_insert.mpr; left
    cases p
    simp_all [j, step]
  · have hd : e.direction = p.second := congrArg PositiveEdge.direction h₄
    have hb : e.source = p.base := congrArg PositiveEdge.source h₄
    let j : {j : Fin d // j ≠ e.direction} :=
      ⟨p.first, fun h => p.distinct (h.trans hd)⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    apply Finset.mem_insert.mpr; right
    apply Finset.mem_insert.mpr; right
    apply Finset.mem_insert.mpr; left
    cases p
    simp_all [j]

/-- The explicit incidence list contains only plaquettes whose boundary
contains the specified positive edge. -/
theorem mem_boundary_of_mem_incidentPlaquettes {d : ℕ}
    (e : PositiveEdge d) (p : Plaquette d)
    (hp : p ∈ incidentPlaquettes e) : e ∈ p.boundary.edgeSupport := by
  classical
  rw [incidentPlaquettes, Finset.mem_biUnion] at hp
  obtain ⟨j, _, hp⟩ := hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    rw [plaquette_boundary_edgeSupport] <;> simp [step]

/-- Incidence is exactly boundary membership. -/
theorem mem_incidentPlaquettes_iff_mem_boundary {d : ℕ}
    (e : PositiveEdge d) (p : Plaquette d) :
    p ∈ incidentPlaquettes e ↔ e ∈ p.boundary.edgeSupport :=
  ⟨mem_boundary_of_mem_incidentPlaquettes e p,
    mem_incidentPlaquettes_of_mem_boundary e p⟩

/-- Translation commutes with the finite list of plaquettes incident to a
positive edge. -/
theorem incidentPlaquettes_translate {d : ℕ} (v : Site d)
    (e : PositiveEdge d) :
    incidentPlaquettes (e.translate v) =
      (incidentPlaquettes e).map
        (Plaquette.translationEquiv v).toEmbedding := by
  classical
  ext p
  rw [Finset.mem_map_equiv]
  rw [mem_incidentPlaquettes_iff_mem_boundary,
    mem_incidentPlaquettes_iff_mem_boundary]
  change e.translate v ∈ p.boundary.edgeSupport ↔
    e ∈ (p.translate (-v)).boundary.edgeSupport
  rw [plaquette_boundary_edgeSupport_translate, Finset.mem_map_equiv]
  change e.translate v ∈ p.boundary.edgeSupport ↔
    e.translate (-(-v)) ∈ p.boundary.edgeSupport
  rw [neg_neg]

/-- A positive edge belongs to at most `4d` oriented coordinate plaquettes. -/
theorem card_incidentPlaquettes_le {d : ℕ} (e : PositiveEdge d) :
    (incidentPlaquettes e).card ≤ 4 * d := by
  classical
  calc
    (incidentPlaquettes e).card ≤
        ∑ j : {j : Fin d // j ≠ e.direction},
          ({ ⟨e.source, e.direction, j, j.2.symm⟩,
             ⟨e.source - unitVector j, e.direction, j, j.2.symm⟩,
             ⟨e.source, j, e.direction, j.2⟩,
             ⟨e.source - unitVector j, j, e.direction, j.2⟩ } :
            Finset (Plaquette d)).card := by
      simpa [incidentPlaquettes] using
        (Finset.card_biUnion_le :
          (Finset.univ.biUnion fun j : {j : Fin d // j ≠ e.direction} =>
            ({ ⟨e.source, e.direction, j, j.2.symm⟩,
               ⟨e.source - unitVector j, e.direction, j, j.2.symm⟩,
               ⟨e.source, j, e.direction, j.2⟩,
               ⟨e.source - unitVector j, j, e.direction, j.2⟩ } :
              Finset (Plaquette d))).card ≤ _)
    _ ≤ ∑ _j : {j : Fin d // j ≠ e.direction}, 4 := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.card_le_four
    _ = 4 * Fintype.card {j : Fin d // j ≠ e.direction} := by
      simp [Nat.mul_comm]
    _ ≤ 4 * d := Nat.mul_le_mul_left 4 (by
      simpa only [Fintype.card_fin] using
        Fintype.card_subtype_le (fun j : Fin d => j ≠ e.direction))

/-- Candidate plaquette neighbors obtained by choosing an edge of `p` and an
incident plaquette at that edge. -/
def plaquetteNeighborCandidates {d : ℕ} (p : Plaquette d) :
    Finset (Plaquette d) :=
  p.boundary.edgeSupport.biUnion incidentPlaquettes

theorem card_plaquetteNeighborCandidates_le {d : ℕ} (p : Plaquette d) :
    (plaquetteNeighborCandidates p).card ≤ 16 * d := by
  classical
  calc
    (plaquetteNeighborCandidates p).card ≤
        ∑ e ∈ p.boundary.edgeSupport, (incidentPlaquettes e).card :=
      by simpa [plaquetteNeighborCandidates] using
        (Finset.card_biUnion_le (s := p.boundary.edgeSupport)
          (t := incidentPlaquettes))
    _ ≤ ∑ _e ∈ p.boundary.edgeSupport, 4 * d := by
      apply Finset.sum_le_sum
      intro e _
      exact card_incidentPlaquettes_le e
    _ = p.boundary.edgeSupport.card * (4 * d) := by simp
    _ ≤ 4 * (4 * d) := by
      gcongr
      rw [plaquette_boundary_edgeSupport]
      exact Finset.card_le_four
    _ = 16 * d := by omega

/-- Connected finite vertex sets containing a specified root and having a
specified cardinality. -/
def rootedAnimals {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) (n : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun X => root ∈ X ∧ X.card = n ∧
    (G.induce (X : Set V)).Connected

/-- A reusable graph-animal counting certificate.  Constants need not be
optimal; `animalConstant` is the exponential base used in KP tails. -/
structure AnimalCountingCertificate (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  degreeBound : ℕ
  animalConstant : ℕ
  degree_le : ∀ v, G.degree v ≤ degreeBound
  rooted_count_le : ∀ root n,
    (rootedAnimals G root n).card ≤ animalConstant ^ (n - 1)

/-! ### A uniform bounded-degree animal certificate -/

/-- State of the deterministic breadth-first exploration used to encode a
connected vertex set. -/
structure AnimalExplorationState (V : Type*) where
  seen : Finset V
  processed : Finset V
  deriving DecidableEq, Fintype

/-- Vertices which have been discovered but not yet processed. -/
def AnimalExplorationState.frontier {V : Type*} [DecidableEq V]
    (s : AnimalExplorationState V) : Finset V :=
  s.seen \ s.processed

/-- One deterministic exploration step inside a target set. -/
def animalExplorationStep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    (s : AnimalExplorationState V) : AnimalExplorationState V := by
  classical
  exact if h : s.frontier.Nonempty then
    let v := h.choose
    ⟨s.seen ∪ (G.neighborFinset v ∩ X), insert v s.processed⟩
  else s

/-- Target-set exploration after `k` steps. -/
def animalExploration {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : V) (X : Finset V) (k : ℕ) : AnimalExplorationState V :=
  (animalExplorationStep G X)^[k] ⟨{root}, ∅⟩

@[simp]
theorem animalExploration_succ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : V) (X : Finset V) (k : ℕ) :
    animalExploration G root X (k + 1) =
      animalExplorationStep G X (animalExploration G root X k) := by
  simp [animalExploration, Function.iterate_succ_apply']

/-- All one-step states obtained by choosing an arbitrary subset of the next
vertex's neighbors. -/
def animalExplorationOptions {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : AnimalExplorationState V) : Finset (AnimalExplorationState V) := by
  classical
  exact if h : s.frontier.Nonempty then
    let v := h.choose
    (G.neighborFinset v).powerset.image fun A =>
      ⟨s.seen ∪ A, insert v s.processed⟩
  else {s}

/-- Exploration states reachable after `k` arbitrary bounded-degree choices. -/
def animalExplorationStates {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : V) : ℕ → Finset (AnimalExplorationState V)
  | 0 => {⟨{root}, ∅⟩}
  | k + 1 => (animalExplorationStates G root k).biUnion
      (animalExplorationOptions G)

theorem animalExploration_mem_states
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : V) (X : Finset V) (k : ℕ) :
    animalExploration G root X k ∈ animalExplorationStates G root k := by
  classical
  induction k with
  | zero => simp [animalExploration, animalExplorationStates]
  | succ k ih =>
      rw [animalExploration_succ]
      apply Finset.mem_biUnion.mpr
      refine ⟨animalExploration G root X k, ih, ?_⟩
      unfold animalExplorationOptions animalExplorationStep
      by_cases h : (animalExploration G root X k).frontier.Nonempty
      · simp only [h, dite_true]
        apply Finset.mem_image.mpr
        refine ⟨G.neighborFinset
            h.choose ∩ X, ?_, rfl⟩
        exact Finset.mem_powerset.mpr (Finset.inter_subset_left)
      · simp [h]

theorem card_animalExplorationOptions_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {D : ℕ}
    (hdegree : ∀ v, G.degree v ≤ D) (s : AnimalExplorationState V) :
    (animalExplorationOptions G s).card ≤ 2 ^ D := by
  classical
  unfold animalExplorationOptions
  by_cases h : s.frontier.Nonempty
  · simp only [h, dite_true]
    calc
      ((G.neighborFinset h.choose).powerset.image fun A =>
          AnimalExplorationState.mk (s.seen ∪ A)
            (insert h.choose s.processed)).card ≤
          (G.neighborFinset h.choose).powerset.card :=
        Finset.card_image_le
      _ = 2 ^ G.degree h.choose := by
        rw [Finset.card_powerset, SimpleGraph.card_neighborFinset_eq_degree]
      _ ≤ 2 ^ D := pow_le_pow_right' (by omega) (hdegree _)
  · simp [h, Nat.one_le_two_pow]

theorem card_animalExplorationStates_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {D : ℕ}
    (hdegree : ∀ v, G.degree v ≤ D) (root : V) (k : ℕ) :
    (animalExplorationStates G root k).card ≤ (2 ^ D) ^ k := by
  classical
  induction k with
  | zero => simp [animalExplorationStates]
  | succ k ih =>
      rw [animalExplorationStates]
      calc
        ((animalExplorationStates G root k).biUnion
            (animalExplorationOptions G)).card ≤
            ∑ s ∈ animalExplorationStates G root k,
              (animalExplorationOptions G s).card := Finset.card_biUnion_le
        _ ≤ ∑ _s ∈ animalExplorationStates G root k, 2 ^ D := by
          apply Finset.sum_le_sum
          intro s _
          exact card_animalExplorationOptions_le G hdegree s
        _ = (animalExplorationStates G root k).card * 2 ^ D := by simp
        _ ≤ (2 ^ D) ^ k * 2 ^ D := Nat.mul_le_mul_right _ ih
        _ = (2 ^ D) ^ (k + 1) := by rw [pow_succ]

/-- The exploration invariant: discovered vertices lie in the target,
processed vertices were discovered, and every processed vertex has had all of
its target-neighbors discovered. -/
def AnimalExplorationInvariant {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : V) (X : Finset V) (s : AnimalExplorationState V) : Prop :=
  root ∈ s.seen ∧ s.seen ⊆ X ∧ s.processed ⊆ s.seen ∧
    ∀ v ∈ s.processed, ∀ w ∈ X, G.Adj v w → w ∈ s.seen

theorem animalExplorationInvariant_step
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : V) (X : Finset V) (s : AnimalExplorationState V)
    (hinv : AnimalExplorationInvariant G root X s) :
    AnimalExplorationInvariant G root X (animalExplorationStep G X s) := by
  classical
  unfold animalExplorationStep
  by_cases h : s.frontier.Nonempty
  · simp only [h, dite_true]
    let v := h.choose
    have hvfront : v ∈ s.frontier := h.choose_spec
    have hvseen : v ∈ s.seen := (Finset.mem_sdiff.mp hvfront).1
    have hvnot : v ∉ s.processed := (Finset.mem_sdiff.mp hvfront).2
    refine ⟨Finset.mem_union_left _ hinv.1, ?_, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_union.mp hw with hw | hw
      · exact hinv.2.1 hw
      · exact (Finset.mem_inter.mp hw).2
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Finset.mem_union_left _ hvseen
      · exact Finset.mem_union_left _ (hinv.2.2.1 hw)
    · intro u hu w hwX hadj
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Finset.mem_union_right _ <| Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset v w).mpr hadj, hwX⟩
      · exact Finset.mem_union_left _ (hinv.2.2.2 u hu w hwX hadj)
  · simpa [h] using hinv

theorem animalExploration_invariant
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {root : V} {X : Finset V} (hroot : root ∈ X) (k : ℕ) :
    AnimalExplorationInvariant G root X (animalExploration G root X k) := by
  induction k with
  | zero => simp [animalExploration, AnimalExplorationInvariant, hroot]
  | succ k ih =>
      rw [animalExploration_succ]
      exact animalExplorationInvariant_step G root X _ ih

theorem animalExploration_seen_step_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (s : AnimalExplorationState V) :
    s.seen ⊆ (animalExplorationStep G X s).seen := by
  classical
  unfold animalExplorationStep
  by_cases h : s.frontier.Nonempty
  · simp only [h, dite_true]
    exact Finset.subset_union_left
  · simp [h]

theorem animalExploration_seen_monotone
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : V) (X : Finset V) :
    Monotone fun k => (animalExploration G root X k).seen := by
  apply monotone_nat_of_le_succ
  intro k
  rw [animalExploration_succ]
  exact animalExploration_seen_step_subset G X _

/-- A closed nonempty subset of a connected induced graph is the whole
vertex set. -/
theorem eq_of_connected_of_neighbor_closed
    {V : Type*} (G : SimpleGraph V)
    {root : V} {X S : Finset V} (hroot : root ∈ S) (hSX : S ⊆ X)
    (hconnected : (G.induce (X : Set V)).Connected)
    (hclosed : ∀ v ∈ S, ∀ w ∈ X, G.Adj v w → w ∈ S) :
    S = X := by
  classical
  apply Finset.Subset.antisymm hSX
  intro w hwX
  let rootX : X := ⟨root, hSX hroot⟩
  let wX : X := ⟨w, hwX⟩
  obtain ⟨p⟩ := hconnected.preconnected rootX wX
  let rec follow {u v : X} (p : (G.induce (X : Set V)).Walk u v)
      (hu : u.1 ∈ S) : v.1 ∈ S := by
    cases p with
    | nil => exact hu
    | @cons _ next _ hadj tail =>
        apply follow tail
        exact hclosed u.1 hu next.1 next.2 hadj
  exact follow p hroot

theorem animalExploration_seen_eq_of_frontier_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {root : V} {X : Finset V} {k : ℕ}
    (hroot : root ∈ X) (hconnected : (G.induce (X : Set V)).Connected)
    (hempty : ¬(animalExploration G root X k).frontier.Nonempty) :
    (animalExploration G root X k).seen = X := by
  have hinv := animalExploration_invariant G hroot k
  apply eq_of_connected_of_neighbor_closed G hinv.1 hinv.2.1 hconnected
  intro v hv w hw hadj
  apply hinv.2.2.2 v ?_ w hw hadj
  have hsubset : (animalExploration G root X k).seen ⊆
      (animalExploration G root X k).processed := by
    exact Finset.sdiff_eq_empty_iff_subset.mp
      (Finset.not_nonempty_iff_eq_empty.mp hempty)
  exact hsubset hv

theorem animalExploration_processed_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : V) (X : Finset V) (k : ℕ)
    (hfront : ∀ j < k, (animalExploration G root X j).frontier.Nonempty) :
    (animalExploration G root X k).processed.card = k := by
  induction k with
  | zero => simp [animalExploration]
  | succ k ih =>
      rw [animalExploration_succ]
      have hk := hfront k (Nat.lt_succ_self k)
      unfold animalExplorationStep
      simp only [hk, dite_true]
      rw [Finset.card_insert_of_notMem]
      · rw [ih (fun j hj => hfront j (hj.trans (Nat.lt_succ_self k)))]
      · exact (Finset.mem_sdiff.mp hk.choose_spec).2

/-- A connected target of size `n` is completely discovered after at most
`n-1` breadth-first processing steps. -/
theorem animalExploration_seen_eq_target
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {root : V} {X : Finset V} {n : ℕ}
    (hroot : root ∈ X) (hcard : X.card = n)
    (hconnected : (G.induce (X : Set V)).Connected) :
    (animalExploration G root X (n - 1)).seen = X := by
  have hn : 0 < n := by
    rw [← hcard]
    exact Finset.card_pos.mpr ⟨root, hroot⟩
  by_contra hne
  have hfinalInv := animalExploration_invariant G hroot (n - 1)
  have hfront : ∀ j < n,
      (animalExploration G root X j).frontier.Nonempty := by
    intro j hj
    by_contra hempty
    have hseenj := animalExploration_seen_eq_of_frontier_empty G hroot hconnected hempty
    have hjle : j ≤ n - 1 := by omega
    have hmono := animalExploration_seen_monotone G root X hjle
    have hXsub : X ⊆ (animalExploration G root X (n - 1)).seen := by
      intro x hx
      exact hmono (hseenj.symm.subset hx)
    exact hne (Finset.Subset.antisymm hfinalInv.2.1 hXsub)
  have hprocessed := animalExploration_processed_card_eq G root X (n - 1)
    (fun j hj => hfront j (by omega))
  have hfrontFinal := hfront (n - 1) (by omega)
  have hproper : (animalExploration G root X (n - 1)).processed ⊂
      (animalExploration G root X (n - 1)).seen := by
    refine ⟨hfinalInv.2.2.1, ?_⟩
    intro hreverse
    obtain ⟨v, hv⟩ := hfrontFinal
    exact (Finset.mem_sdiff.mp hv).2 (hreverse (Finset.mem_sdiff.mp hv).1)
  have hcardSeen : n ≤ (animalExploration G root X (n - 1)).seen.card := by
    have := Finset.card_lt_card hproper
    omega
  have hcardLe : (animalExploration G root X (n - 1)).seen.card ≤ n := by
    exact (Finset.card_le_card hfinalInv.2.1).trans_eq hcard
  have hXcardLe : X.card ≤ (animalExploration G root X (n - 1)).seen.card := by
    rw [hcard]
    exact hcardSeen
  exact hne (Finset.eq_of_subset_of_card_le hfinalInv.2.1 hXcardLe)

set_option maxHeartbeats 2000000 in
-- The injectivity proof normalizes two finite breadth-first explorations.
/-- A graph of maximum degree `D` has at most `(2^D)^(n-1)` connected
`n`-vertex sets containing a fixed root.  The proof encodes an animal by the
state of a deterministic breadth-first exploration; each processed vertex
has at most `2^D` possible neighbor subsets. -/
theorem card_rootedAnimals_le_pow_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {D : ℕ}
    (hdegree : ∀ v, G.degree v ≤ D) (root : V) (n : ℕ) :
    (rootedAnimals G root n).card ≤ (2 ^ D) ^ (n - 1) := by
  classical
  let f : Finset V → AnimalExplorationState V := fun X =>
    animalExploration G root X (n - 1)
  apply (Finset.card_le_card_of_injOn f ?_ ?_).trans
    (card_animalExplorationStates_le G hdegree root (n - 1))
  · intro X hX
    exact animalExploration_mem_states G root X (n - 1)
  · intro X hX Y hY hXY
    have hx : root ∈ X ∧ X.card = n ∧ (G.induce (X : Set V)).Connected := by
      simpa [rootedAnimals] using hX
    have hy : root ∈ Y ∧ Y.card = n ∧ (G.induce (Y : Set V)).Connected := by
      simpa [rootedAnimals] using hY
    have hxcover := animalExploration_seen_eq_target G hx.1 hx.2.1 hx.2.2
    have hycover := animalExploration_seen_eq_target G hy.1 hy.2.1 hy.2.2
    have hseen := congrArg AnimalExplorationState.seen hXY
    exact hxcover.symm.trans (hseen.trans hycover)

/-- Canonical graph-animal certificate obtained from a maximum-degree bound. -/
def boundedDegreeAnimalCountingCertificate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) : AnimalCountingCertificate V G where
  degreeBound := D
  animalConstant := 2 ^ D
  degree_le := hdegree
  rooted_count_le := card_rootedAnimals_le_pow_degree G hdegree

/-- Rooted animal generating functions are bounded by the geometric series
implied by an animal-counting certificate. -/
theorem rootedAnimalGeneratingFunction_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (cert : AnimalCountingCertificate V G) (root : V) {q : ℝ}
    (hq : 0 ≤ q) (hsmall : (cert.animalConstant : ℝ) * q < 1) :
    (∑' n : ℕ, ((rootedAnimals G root (n + 1)).card : ℝ) * q ^ (n + 1)) ≤
      q / (1 - (cert.animalConstant : ℝ) * q) := by
  let C : ℝ := cert.animalConstant
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hgeom : Summable fun n : ℕ => q * (C * q) ^ n := by
    exact (hasSum_geometric_of_lt_one (mul_nonneg hC hq) hsmall).summable.mul_left q
  have hterm : ∀ n : ℕ,
      ((rootedAnimals G root (n + 1)).card : ℝ) * q ^ (n + 1) ≤
        q * (C * q) ^ n := by
    intro n
    have hcountNat := cert.rooted_count_le root (n + 1)
    have hcount : ((rootedAnimals G root (n + 1)).card : ℝ) ≤ C ^ n := by
      change ((rootedAnimals G root (n + 1)).card : ℝ) ≤
        (cert.animalConstant : ℝ) ^ n
      exact_mod_cast (by simpa using hcountNat)
    calc
      ((rootedAnimals G root (n + 1)).card : ℝ) * q ^ (n + 1) ≤
          C ^ n * q ^ (n + 1) :=
        mul_le_mul_of_nonneg_right hcount (pow_nonneg hq _)
      _ = q * (C * q) ^ n := by
        rw [pow_succ]
        ring
  have hsource : Summable fun n : ℕ =>
      ((rootedAnimals G root (n + 1)).card : ℝ) * q ^ (n + 1) :=
    hgeom.of_nonneg_of_le
      (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _)) hterm
  calc
    _ ≤ ∑' n : ℕ, q * (C * q) ^ n := hsource.tsum_le_tsum hterm hgeom
    _ = q * (1 - C * q)⁻¹ :=
      ((hasSum_geometric_of_lt_one (mul_nonneg hC hq) hsmall).mul_left q).tsum_eq
    _ = q / (1 - C * q) := by rw [div_eq_mul_inv]

section PlaquettePolymers

open Gauge Lattice.Cubic

variable {d : ℕ} {G₀ : Type*} [Group G₀] [TopologicalSpace G₀]
  [IsTopologicalGroup G₀] [MeasurableSpace G₀] [BorelSpace G₀]
  [SecondCountableTopology G₀] [GaugeHaarProbability G₀]

omit [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀]
  [MeasurableSpace G₀] [BorelSpace G₀] [SecondCountableTopology G₀]
  [GaugeHaarProbability G₀] in
/-- The active-plaquette adjacency degree is bounded solely by the lattice
dimension, independently of the finite volume and exterior field. -/
theorem plaquetteAdjacency_degree_le (Λ : FiniteSpecification d G₀)
    (p : ActivePlaquette Λ) :
    (plaquetteAdjacencyGraph Λ).degree p ≤ 16 * d := by
  classical
  let valEmbedding : ActivePlaquette Λ ↪ Plaquette d :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hsub : ((plaquetteAdjacencyGraph Λ).neighborFinset p).map valEmbedding ⊆
      plaquetteNeighborCandidates p.1 := by
    intro q hq
    rcases Finset.mem_map.mp hq with ⟨q', hq', rfl⟩
    have hadj : (plaquetteAdjacencyGraph Λ).Adj p q' := by
      exact ((plaquetteAdjacencyGraph Λ).mem_neighborFinset p q').mp hq'
    rcases Finset.not_disjoint_iff.mp hadj.2 with ⟨e, hep, heq⟩
    have hep' : e ∈ p.1.boundary.edgeSupport :=
      (Finset.mem_filter.mp hep).2
    have heq' : e ∈ q'.1.boundary.edgeSupport :=
      (Finset.mem_filter.mp heq).2
    exact Finset.mem_biUnion.mpr
      ⟨e, hep', mem_incidentPlaquettes_of_mem_boundary e q'.1 heq'⟩
  calc
    (plaquetteAdjacencyGraph Λ).degree p =
        ((plaquetteAdjacencyGraph Λ).neighborFinset p).card := rfl
    _ = (((plaquetteAdjacencyGraph Λ).neighborFinset p).map valEmbedding).card :=
      (Finset.card_map valEmbedding).symm
    _ ≤ (plaquetteNeighborCandidates p.1).card := Finset.card_le_card hsub
    _ ≤ 16 * d := card_plaquetteNeighborCandidates_le p.1

/-- Uniform graph-animal certificate for active plaquettes in dimension `d`.
Neither constant depends on the finite specification or its exterior field. -/
def cubicPlaquetteAnimalCertificate (Λ : FiniteSpecification d G₀) :
    AnimalCountingCertificate (ActivePlaquette Λ) (plaquetteAdjacencyGraph Λ) :=
  boundedDegreeAnimalCountingCertificate (plaquetteAdjacencyGraph Λ) (16 * d)
    (plaquetteAdjacency_degree_le Λ)

omit [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀]
  [MeasurableSpace G₀] [BorelSpace G₀] [SecondCountableTopology G₀]
  [GaugeHaarProbability G₀] in
@[simp]
theorem cubicPlaquetteAnimalCertificate_degreeBound
    (Λ : FiniteSpecification d G₀) :
    (cubicPlaquetteAnimalCertificate Λ).degreeBound = 16 * d := rfl

omit [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀]
  [MeasurableSpace G₀] [BorelSpace G₀] [SecondCountableTopology G₀]
  [GaugeHaarProbability G₀] in
@[simp]
theorem cubicPlaquetteAnimalCertificate_animalConstant
    (Λ : FiniteSpecification d G₀) :
    (cubicPlaquetteAnimalCertificate Λ).animalConstant = 2 ^ (16 * d) := rfl

/-- Plaquette polymers of a fixed size containing a specified root. -/
def rootedPlaquettePolymers (Λ : FiniteSpecification d G₀)
    (root : ActivePlaquette Λ) (n : ℕ) : Finset (PlaquettePolymer Λ) :=
  Finset.univ.filter fun γ => root ∈ γ.1 ∧ γ.1.card = n

omit [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀]
  [MeasurableSpace G₀] [BorelSpace G₀] [SecondCountableTopology G₀]
  [GaugeHaarProbability G₀] in
/-- Rooted plaquette polymers are exactly the rooted animals of the
plaquette-adjacency graph. -/
theorem card_rootedPlaquettePolymers_eq_rootedAnimals
    (Λ : FiniteSpecification d G₀) (root : ActivePlaquette Λ) (n : ℕ) :
    (rootedPlaquettePolymers Λ root n).card =
      (rootedAnimals (plaquetteAdjacencyGraph Λ) root n).card := by
  classical
  apply Finset.card_bij (fun γ _ => γ.1)
  · intro γ hγ
    have h := (Finset.mem_filter.mp hγ).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1, h.2, γ.2.2⟩
  · intro γ₁ hγ₁ γ₂ hγ₂ heq
    exact Subtype.ext heq
  · intro X hX
    have h := (Finset.mem_filter.mp hX).2
    let γ : PlaquettePolymer Λ := ⟨X, ⟨root, h.1⟩, h.2.2⟩
    refine ⟨γ, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1, h.2.1⟩

omit [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀]
  [MeasurableSpace G₀] [BorelSpace G₀] [SecondCountableTopology G₀]
  [GaugeHaarProbability G₀] in
/-- The total weight of polymers containing a fixed root is controlled by
the rooted-animal generating function. -/
theorem sum_rootedPlaquettePolymerWeights_le
    (Λ : FiniteSpecification d G₀)
    (cert : AnimalCountingCertificate (ActivePlaquette Λ)
      (plaquetteAdjacencyGraph Λ))
    (root : ActivePlaquette Λ) {q : ℝ}
    (hq : 0 ≤ q) (hsmall : (cert.animalConstant : ℝ) * q < 1) :
    ∑ γ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
        (fun γ => root ∈ γ.1), q ^ γ.1.card ≤
      q / (1 - (cert.animalConstant : ℝ) * q) := by
  classical
  let s := (Finset.univ : Finset (PlaquettePolymer Λ)).filter
    (fun γ => root ∈ γ.1)
  let N := Fintype.card (ActivePlaquette Λ)
  have hmaps : ∀ γ ∈ s, γ.1.card ∈ Finset.range (N + 1) := by
    intro γ _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ γ.1))
  calc
    ∑ γ ∈ s, q ^ γ.1.card =
        ∑ n ∈ Finset.range (N + 1),
          ∑ γ ∈ s with γ.1.card = n, q ^ γ.1.card := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hmaps _
    _ = ∑ n ∈ Finset.range (N + 1),
          ((rootedAnimals (plaquetteAdjacencyGraph Λ) root n).card : ℝ) * q ^ n := by
      apply Finset.sum_congr rfl
      intro n _
      calc
        (∑ γ ∈ s with γ.1.card = n, q ^ γ.1.card) =
            ((rootedPlaquettePolymers Λ root n).card : ℝ) * q ^ n := by
          have hs : s.filter (fun γ => γ.1.card = n) =
              rootedPlaquettePolymers Λ root n := by
            ext γ
            simp [s, rootedPlaquettePolymers]
          rw [hs]
          calc
            (∑ γ ∈ rootedPlaquettePolymers Λ root n, q ^ γ.1.card) =
                ∑ _γ ∈ rootedPlaquettePolymers Λ root n, q ^ n := by
              apply Finset.sum_congr rfl
              intro γ hγ
              rw [(Finset.mem_filter.mp hγ).2.2]
            _ = ((rootedPlaquettePolymers Λ root n).card : ℝ) * q ^ n := by
              simp
        _ = ((rootedAnimals (plaquetteAdjacencyGraph Λ) root n).card : ℝ) * q ^ n := by
          rw [card_rootedPlaquettePolymers_eq_rootedAnimals]
    _ ≤ ∑' n : ℕ, ((rootedAnimals (plaquetteAdjacencyGraph Λ) root (n + 1)).card : ℝ) *
          q ^ (n + 1) := by
      let f : ℕ → ℝ := fun n =>
        ((rootedAnimals (plaquetteAdjacencyGraph Λ) root n).card : ℝ) * q ^ n
      let g : ℕ → ℝ := fun n => f (n + 1)
      have hf0 : f 0 = 0 := by
        have hempty : rootedAnimals (plaquetteAdjacencyGraph Λ) root 0 = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro X hX
          have h := (Finset.mem_filter.mp hX).2
          exact (Finset.card_ne_zero.mpr ⟨root, h.1⟩) h.2.1
        simp [f, hempty]
      let C : ℝ := cert.animalConstant
      have hC : 0 ≤ C := Nat.cast_nonneg _
      have hgeom : Summable fun n : ℕ => q * (C * q) ^ n := by
        exact (hasSum_geometric_of_lt_one (mul_nonneg hC hq) hsmall).summable.mul_left q
      have hg_le : ∀ n : ℕ, g n ≤ q * (C * q) ^ n := by
        intro n
        have hcountNat := cert.rooted_count_le root (n + 1)
        have hcount : ((rootedAnimals (plaquetteAdjacencyGraph Λ) root (n + 1)).card : ℝ) ≤
            C ^ n := by
          change ((rootedAnimals (plaquetteAdjacencyGraph Λ) root (n + 1)).card : ℝ) ≤
            (cert.animalConstant : ℝ) ^ n
          exact_mod_cast (by simpa using hcountNat)
        dsimp [g, f]
        calc
          ((rootedAnimals (plaquetteAdjacencyGraph Λ) root (n + 1)).card : ℝ) *
              q ^ (n + 1) ≤ C ^ n * q ^ (n + 1) :=
            mul_le_mul_of_nonneg_right hcount (pow_nonneg hq _)
          _ = q * (C * q) ^ n := by rw [pow_succ]; ring
      have hg_nonneg : ∀ n, 0 ≤ g n := by
        intro n
        exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _)
      have hg : Summable g := hgeom.of_nonneg_of_le hg_nonneg hg_le
      change (Finset.range (N + 1)).sum f ≤ tsum g
      rw [Finset.sum_range_succ']
      change (Finset.range N).sum g + f 0 ≤ tsum g
      rw [hf0, add_zero]
      exact hg.sum_le_tsum (Finset.range N) (fun n _ => hg_nonneg n)
    _ ≤ q / (1 - (cert.animalConstant : ℝ) * q) :=
      rootedAnimalGeneratingFunction_le cert root hq hsmall

/-- Active plaquettes at graph distance at most one from a polymer. -/
def polymerClosedNeighborhood (Λ : FiniteSpecification d G₀)
    (γ : PlaquettePolymer Λ) : Finset (ActivePlaquette Λ) :=
  γ.1.biUnion fun p => insert p ((plaquetteAdjacencyGraph Λ).neighborFinset p)

omit [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀]
  [MeasurableSpace G₀] [BorelSpace G₀] [SecondCountableTopology G₀]
  [GaugeHaarProbability G₀] in
theorem card_polymerClosedNeighborhood_le
    (Λ : FiniteSpecification d G₀)
    (cert : AnimalCountingCertificate (ActivePlaquette Λ)
      (plaquetteAdjacencyGraph Λ)) (γ : PlaquettePolymer Λ) :
    (polymerClosedNeighborhood Λ γ).card ≤
      γ.1.card * (cert.degreeBound + 1) := by
  classical
  calc
    (polymerClosedNeighborhood Λ γ).card ≤
        ∑ p ∈ γ.1,
          (insert p ((plaquetteAdjacencyGraph Λ).neighborFinset p)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ γ.1, (cert.degreeBound + 1) := by
      apply Finset.sum_le_sum
      intro p _
      calc
        (insert p ((plaquetteAdjacencyGraph Λ).neighborFinset p)).card ≤
            (plaquetteAdjacencyGraph Λ).degree p + 1 := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          exact Finset.card_insert_le _ _
        _ ≤ cert.degreeBound + 1 := Nat.add_le_add_right (cert.degree_le p) 1
    _ = γ.1.card * (cert.degreeBound + 1) := by simp

omit [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀]
  [MeasurableSpace G₀] [BorelSpace G₀] [SecondCountableTopology G₀]
  [GaugeHaarProbability G₀] in
theorem mem_polymerClosedNeighborhood_of_incompatible
    (Λ : FiniteSpecification d G₀) {γ δ : PlaquettePolymer Λ}
    (h : plaquettePolymerIncompatible Λ γ δ) :
    ∃ q ∈ δ.1, q ∈ polymerClosedNeighborhood Λ γ := by
  classical
  rcases h with ⟨p, hp, q, hq, hpq⟩
  refine ⟨q, hq, Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩⟩
  rcases hpq with rfl | hpq
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert.mpr <| Or.inr <|
      ((plaquetteAdjacencyGraph Λ).mem_neighborFinset p q).mpr hpq

omit [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀]
  [MeasurableSpace G₀] [BorelSpace G₀] [SecondCountableTopology G₀]
  [GaugeHaarProbability G₀] in
/-- Sum of the cardinality weights of all polymers incompatible with `γ`.
The estimate is uniform once the graph-animal certificate is uniform. -/
theorem sum_incompatiblePlaquettePolymerWeights_le
    (Λ : FiniteSpecification d G₀)
    (cert : AnimalCountingCertificate (ActivePlaquette Λ)
      (plaquetteAdjacencyGraph Λ)) (γ : PlaquettePolymer Λ) {q : ℝ}
    (hq : 0 ≤ q) (hsmall : (cert.animalConstant : ℝ) * q < 1) :
    ∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
        (plaquettePolymerIncompatible Λ γ), q ^ δ.1.card ≤
      (γ.1.card : ℝ) * (cert.degreeBound + 1) *
        (q / (1 - (cert.animalConstant : ℝ) * q)) := by
  classical
  let R := polymerClosedNeighborhood Λ γ
  let w : PlaquettePolymer Λ → ℝ := fun δ => q ^ δ.1.card
  have hpoint : ∀ δ : PlaquettePolymer Λ,
      (if plaquettePolymerIncompatible Λ γ δ then w δ else 0) ≤
        ∑ r ∈ R, if r ∈ δ.1 then w δ else 0 := by
    intro δ
    by_cases hinc : plaquettePolymerIncompatible Λ γ δ
    · simp only [hinc, if_true]
      obtain ⟨r, hrδ, hrR⟩ :=
        mem_polymerClosedNeighborhood_of_incompatible Λ hinc
      calc
        w δ = (if r ∈ δ.1 then w δ else 0) := by simp [hrδ]
        _ ≤ ∑ x ∈ R, if x ∈ δ.1 then w δ else 0 := by
          apply Finset.single_le_sum
              (s := R) (f := fun x => if x ∈ δ.1 then w δ else 0)
          · intro x _
            by_cases hx : x ∈ δ.1
            · simp [hx, w, pow_nonneg hq]
            · simp [hx]
          · exact hrR
    · rw [if_neg hinc]
      exact Finset.sum_nonneg fun x _ => by
        by_cases hx : x ∈ δ.1
        · simp [hx, w, pow_nonneg hq]
        · simp [hx]
  calc
    ∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
        (plaquettePolymerIncompatible Λ γ), q ^ δ.1.card =
        ∑ δ : PlaquettePolymer Λ,
          if plaquettePolymerIncompatible Λ γ δ then w δ else 0 := by
      rw [Finset.sum_filter]
    _ ≤ ∑ δ : PlaquettePolymer Λ,
        ∑ r ∈ R, if r ∈ δ.1 then w δ else 0 :=
      Finset.sum_le_sum fun δ _ => hpoint δ
    _ = ∑ r ∈ R, ∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
          (fun δ => r ∈ δ.1), q ^ δ.1.card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_filter]
    _ ≤ ∑ _r ∈ R,
          q / (1 - (cert.animalConstant : ℝ) * q) := by
      apply Finset.sum_le_sum
      intro r _
      exact sum_rootedPlaquettePolymerWeights_le Λ cert r hq hsmall
    _ = (R.card : ℝ) *
          (q / (1 - (cert.animalConstant : ℝ) * q)) := by simp
    _ ≤ ((γ.1.card * (cert.degreeBound + 1) : ℕ) : ℝ) *
          (q / (1 - (cert.animalConstant : ℝ) * q)) := by
      gcongr
      exact_mod_cast card_polymerClosedNeighborhood_le Λ cert γ
    _ = (γ.1.card : ℝ) * (cert.degreeBound + 1) *
          (q / (1 - (cert.animalConstant : ℝ) * q)) := by
      push_cast
      ring

end PlaquettePolymers

/-! ## Explicit Dobrushin smallness threshold -/

/-- A positive scalar threshold which simultaneously controls animal tails,
incompatibility neighborhoods, and the elementary Dobrushin remainder. -/
def dobrushinThreshold (degreeBound animalConstant : ℕ) : ℝ :=
  min (1 / 8) <| min
    (1 / (16 * (animalConstant + 1 : ℝ)))
    (Real.log 2 / (16 * (degreeBound + 1 : ℝ)))

theorem dobrushinThreshold_pos (degreeBound animalConstant : ℕ) :
    0 < dobrushinThreshold degreeBound animalConstant := by
  unfold dobrushinThreshold
  apply lt_min (by norm_num)
  apply lt_min <;> positivity

/-- Elementary exponential remainder used by the Dobrushin criterion. -/
theorem half_mul_le_one_sub_exp_neg {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have hone : 0 < 1 + x := by linarith
  have hexp : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hinv : (Real.exp x)⁻¹ ≤ (1 + x)⁻¹ := by
    exact (inv_le_inv₀ (Real.exp_pos x) hone).mpr hexp
  have halg : (1 + x)⁻¹ ≤ 1 - x / 2 := by
    apply (inv_le_iff_one_le_mul₀ hone).mpr
    nlinarith
  rw [Real.exp_neg]
  linarith

section QuantitativeDobrushin

open Gauge Lattice.Cubic

variable {d : ℕ} {G₀ : Type*} [Group G₀] [TopologicalSpace G₀]
  [IsTopologicalGroup G₀] [MeasurableSpace G₀] [BorelSpace G₀]
  [SecondCountableTopology G₀] [GaugeHaarProbability G₀]

/-- The cardinality-exponential Dobrushin weight used at strong coupling. -/
def plaquetteDobrushinWeight (q : ℝ) {Λ : FiniteSpecification d G₀}
    (γ : PlaquettePolymer Λ) : ℝ :=
  (8 * q) ^ γ.1.card

/-- Linear size weight used by the standard Kotecký--Preiss tree
criterion. -/
def plaquetteKPWeight {Λ : FiniteSpecification d G₀}
    (γ : PlaquettePolymer Λ) : ℝ :=
  (γ.1.card : ℝ) * Real.log 2

omit [IsTopologicalGroup G₀] [BorelSpace G₀] [SecondCountableTopology G₀] in
/-- The same explicit scalar threshold also discharges the genuine
Kotecký--Preiss activity-sum condition used by the rooted-tree expansion. -/
theorem plaquettePolymerModel_koteckyPreiss
    (Λ : FiniteSpecification d G₀) (Φ : RealPlaquettePotential G₀) (β : ℂ)
    (cert : AnimalCountingCertificate (ActivePlaquette Λ)
      (plaquetteAdjacencyGraph Λ))
    (hsmall : perturbationMajorant Φ β <
      dobrushinThreshold cert.degreeBound cert.animalConstant) :
    (plaquettePolymerModel Λ Φ β).KoteckyPreissCertificate Finset.univ
      plaquetteKPWeight := by
  classical
  let q := perturbationMajorant Φ β
  have hq₀ : 0 ≤ q := perturbationMajorant_nonneg Φ β
  have hthreshold := hsmall
  rw [dobrushinThreshold, lt_min_iff, lt_min_iff] at hthreshold
  rcases hthreshold with ⟨hqEight, hqAnimal, hqDegree⟩
  have htwoq₀ : 0 ≤ 2 * q := mul_nonneg (by norm_num) hq₀
  have hCtwoq : (cert.animalConstant : ℝ) * (2 * q) < 1 := by
    have hCnonneg : 0 ≤ (cert.animalConstant : ℝ) := by positivity
    have hdenpos : 0 < (16 : ℝ) * (cert.animalConstant + 1) := by positivity
    have hmul := (lt_div_iff₀ hdenpos).mp hqAnimal
    nlinarith
  refine ⟨?_, ?_⟩
  · intro γ
    exact mul_nonneg (Nat.cast_nonneg γ.1.card) (Real.log_pos (by norm_num)).le
  · intro γ _
    let n := γ.1.card
    have hsum := sum_incompatiblePlaquettePolymerWeights_le
      Λ cert γ htwoq₀ hCtwoq
    have hpoint : ∀ δ : PlaquettePolymer Λ,
        ‖(plaquettePolymerModel Λ Φ β).activity δ‖ *
            Real.exp (plaquetteKPWeight δ) ≤
          (2 * q) ^ δ.1.card := by
      intro δ
      have hactivity := norm_plaquettePolymer_activity_le Λ Φ β δ
      have hexp : Real.exp (plaquetteKPWeight δ) =
          (2 : ℝ) ^ δ.1.card := by
        rw [plaquetteKPWeight, Real.exp_nat_mul,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [hexp]
      calc
        _ ≤ q ^ δ.1.card * (2 : ℝ) ^ δ.1.card := by
          exact mul_le_mul_of_nonneg_right
            (by simpa [q, PlaquettePolymer.support] using hactivity)
            (pow_nonneg (by norm_num) _)
        _ = (2 * q) ^ δ.1.card := by rw [mul_pow]; ring
    have hweighted :
        ∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
            ((plaquettePolymerModel Λ Φ β).incompatible γ),
            ‖(plaquettePolymerModel Λ Φ β).activity δ‖ *
              Real.exp (plaquetteKPWeight δ) ≤
          (n : ℝ) * (cert.degreeBound + 1) *
            ((2 * q) /
              (1 - (cert.animalConstant : ℝ) * (2 * q))) := by
      calc
        _ ≤ ∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
              (plaquettePolymerIncompatible Λ γ),
              (2 * q) ^ δ.1.card := by
          apply Finset.sum_le_sum
          intro δ _
          exact hpoint δ
        _ ≤ _ := hsum
    have hfrac :
        (2 * q) / (1 - (cert.animalConstant : ℝ) * (2 * q)) ≤ 4 * q := by
      have hCnonneg : 0 ≤ (cert.animalConstant : ℝ) := by positivity
      have hdenpos : 0 < (16 : ℝ) * (cert.animalConstant + 1) := by positivity
      have hmul := (lt_div_iff₀ hdenpos).mp hqAnimal
      have hhalf : (cert.animalConstant : ℝ) * (2 * q) ≤ 1 / 2 := by
        nlinarith
      have hden : 0 < 1 - (cert.animalConstant : ℝ) * (2 * q) := by
        linarith
      apply (div_le_iff₀ hden).mpr
      nlinarith
    have hlocal : (cert.degreeBound + 1 : ℝ) * (4 * q) ≤ Real.log 2 := by
      have hdenpos : 0 < (16 : ℝ) * (cert.degreeBound + 1) := by positivity
      have hmul := (lt_div_iff₀ hdenpos).mp hqDegree
      have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith
    calc
      _ ≤ (n : ℝ) * (cert.degreeBound + 1) *
          ((2 * q) / (1 - (cert.animalConstant : ℝ) * (2 * q))) := hweighted
      _ ≤ (n : ℝ) * (cert.degreeBound + 1) * (4 * q) := by
        gcongr
      _ ≤ (n : ℝ) * Real.log 2 := by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      _ = plaquetteKPWeight γ := rfl

omit [IsTopologicalGroup G₀] [BorelSpace G₀] [SecondCountableTopology G₀] in
/-- The explicit strong-coupling threshold leaves a quantitative three-
quarter reserve in the bulk KP inequality.  This reserve is used to switch
on finitely many small labelled source activities without changing the bulk
weight. -/
theorem plaquettePolymerModel_kp_incompatible_sum_le_quarter
    (Λ : FiniteSpecification d G₀) (Φ : RealPlaquettePotential G₀) (β : ℂ)
    (cert : AnimalCountingCertificate (ActivePlaquette Λ)
      (plaquetteAdjacencyGraph Λ))
    (hsmall : perturbationMajorant Φ β <
      dobrushinThreshold cert.degreeBound cert.animalConstant)
    (γ : PlaquettePolymer Λ) :
    ∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
        ((plaquettePolymerModel Λ Φ β).incompatible γ),
        ‖(plaquettePolymerModel Λ Φ β).activity δ‖ *
          Real.exp (plaquetteKPWeight δ) ≤
      (γ.1.card : ℝ) * (Real.log 2 / 4) := by
  classical
  let q := perturbationMajorant Φ β
  have hq₀ : 0 ≤ q := perturbationMajorant_nonneg Φ β
  have hthreshold := hsmall
  rw [dobrushinThreshold, lt_min_iff, lt_min_iff] at hthreshold
  rcases hthreshold with ⟨_hqEight, hqAnimal, hqDegree⟩
  have htwoq₀ : 0 ≤ 2 * q := mul_nonneg (by norm_num) hq₀
  have hCtwoq : (cert.animalConstant : ℝ) * (2 * q) < 1 := by
    have hCnonneg : 0 ≤ (cert.animalConstant : ℝ) := by positivity
    have hdenpos : 0 < (16 : ℝ) * (cert.animalConstant + 1) := by
      positivity
    have hmul := (lt_div_iff₀ hdenpos).mp hqAnimal
    nlinarith
  have hsum := sum_incompatiblePlaquettePolymerWeights_le
    Λ cert γ htwoq₀ hCtwoq
  have hpoint : ∀ δ : PlaquettePolymer Λ,
      ‖(plaquettePolymerModel Λ Φ β).activity δ‖ *
          Real.exp (plaquetteKPWeight δ) ≤
        (2 * q) ^ δ.1.card := by
    intro δ
    have hactivity := norm_plaquettePolymer_activity_le Λ Φ β δ
    have hexp : Real.exp (plaquetteKPWeight δ) =
        (2 : ℝ) ^ δ.1.card := by
      rw [plaquetteKPWeight, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [hexp]
    calc
      _ ≤ q ^ δ.1.card * (2 : ℝ) ^ δ.1.card := by
        exact mul_le_mul_of_nonneg_right
          (by simpa [q, PlaquettePolymer.support] using hactivity)
          (pow_nonneg (by norm_num) _)
      _ = (2 * q) ^ δ.1.card := by rw [mul_pow]; ring
  have hweighted :
      ∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
          ((plaquettePolymerModel Λ Φ β).incompatible γ),
          ‖(plaquettePolymerModel Λ Φ β).activity δ‖ *
            Real.exp (plaquetteKPWeight δ) ≤
        (γ.1.card : ℝ) * (cert.degreeBound + 1) *
          ((2 * q) /
            (1 - (cert.animalConstant : ℝ) * (2 * q))) := by
    calc
      _ ≤ ∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
            (plaquettePolymerIncompatible Λ γ),
            (2 * q) ^ δ.1.card := by
        apply Finset.sum_le_sum
        intro δ _
        exact hpoint δ
      _ ≤ _ := hsum
  have hfrac :
      (2 * q) / (1 - (cert.animalConstant : ℝ) * (2 * q)) ≤ 4 * q := by
    have hCnonneg : 0 ≤ (cert.animalConstant : ℝ) := by positivity
    have hdenpos : 0 < (16 : ℝ) * (cert.animalConstant + 1) := by
      positivity
    have hmul := (lt_div_iff₀ hdenpos).mp hqAnimal
    have hhalf : (cert.animalConstant : ℝ) * (2 * q) ≤ 1 / 2 := by
      nlinarith
    have hden : 0 < 1 - (cert.animalConstant : ℝ) * (2 * q) := by
      linarith
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hlocal :
      (cert.degreeBound + 1 : ℝ) * (4 * q) ≤ Real.log 2 / 4 := by
    have hdenpos : 0 < (16 : ℝ) * (cert.degreeBound + 1) := by
      positivity
    have hmul := (lt_div_iff₀ hdenpos).mp hqDegree
    have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  calc
    _ ≤ (γ.1.card : ℝ) * (cert.degreeBound + 1) *
        ((2 * q) /
          (1 - (cert.animalConstant : ℝ) * (2 * q))) := hweighted
    _ ≤ (γ.1.card : ℝ) * (cert.degreeBound + 1) * (4 * q) := by
      gcongr
    _ = (γ.1.card : ℝ) *
        ((cert.degreeBound + 1 : ℝ) * (4 * q)) := by ring
    _ ≤ (γ.1.card : ℝ) * (Real.log 2 / 4) :=
      mul_le_mul_of_nonneg_left hlocal (Nat.cast_nonneg _)

omit [IsTopologicalGroup G₀] [BorelSpace G₀] [SecondCountableTopology G₀] in
/-- The animal-counting bounds discharge the local Dobrushin criterion at the
explicit scalar threshold. -/
theorem plaquettePolymerModel_dobrushin
    (Λ : FiniteSpecification d G₀) (Φ : RealPlaquettePotential G₀) (β : ℂ)
    (cert : AnimalCountingCertificate (ActivePlaquette Λ)
      (plaquetteAdjacencyGraph Λ))
    (hsmall : perturbationMajorant Φ β <
      dobrushinThreshold cert.degreeBound cert.animalConstant) :
    (plaquettePolymerModel Λ Φ β).DobrushinCertificate Finset.univ
      (plaquetteDobrushinWeight (perturbationMajorant Φ β)) := by
  classical
  let q := perturbationMajorant Φ β
  let r := 8 * q
  have hq₀ : 0 ≤ q := perturbationMajorant_nonneg Φ β
  have hthreshold := hsmall
  rw [dobrushinThreshold, lt_min_iff, lt_min_iff] at hthreshold
  rcases hthreshold with ⟨hqEight, hqAnimal, hqDegree⟩
  have hr₀ : 0 ≤ r := mul_nonneg (by norm_num) hq₀
  have hr₁ : r ≤ 1 := by
    dsimp [r]
    linarith
  have hCr : (cert.animalConstant : ℝ) * r < 1 := by
    dsimp [r]
    have hCnonneg : 0 ≤ (cert.animalConstant : ℝ) := by positivity
    have hdenpos : 0 < (16 : ℝ) * (cert.animalConstant + 1) := by positivity
    have hmul := (lt_div_iff₀ hdenpos).mp hqAnimal
    nlinarith
  refine ⟨?_, ?_⟩
  · intro γ
    exact pow_nonneg hr₀ _
  · intro γ _
    let n := γ.1.card
    have hn : 0 < n := γ.2.1.card_pos
    have hsum := sum_incompatiblePlaquettePolymerWeights_le Λ cert γ hr₀ hCr
    have hfrac : r / (1 - (cert.animalConstant : ℝ) * r) ≤ 2 * r := by
      have hCnonneg : 0 ≤ (cert.animalConstant : ℝ) := by positivity
      have hhalf : (cert.animalConstant : ℝ) * r ≤ 1 / 2 := by
        have hdenpos : 0 < (16 : ℝ) * (cert.animalConstant + 1) := by positivity
        have hmul := (lt_div_iff₀ hdenpos).mp hqAnimal
        dsimp [r]
        nlinarith
      have hden : 0 < 1 - (cert.animalConstant : ℝ) * r := by linarith
      apply (div_le_iff₀ hden).mpr
      nlinarith
    have hlog : ((n : ℝ) * (cert.degreeBound + 1)) *
        (r / (1 - (cert.animalConstant : ℝ) * r)) ≤
        (n : ℝ) * Real.log 2 := by
      have hdegreeNonneg : 0 ≤ (cert.degreeBound + 1 : ℝ) := by positivity
      have hdenpos : 0 < (16 : ℝ) * (cert.degreeBound + 1) := by positivity
      have hmul := (lt_div_iff₀ hdenpos).mp hqDegree
      have hnnonneg : 0 ≤ (n : ℝ) := by positivity
      calc
        ((n : ℝ) * (cert.degreeBound + 1)) *
            (r / (1 - (cert.animalConstant : ℝ) * r)) ≤
            ((n : ℝ) * (cert.degreeBound + 1)) * (2 * r) := by
          gcongr
        _ ≤ (n : ℝ) * Real.log 2 := by
          dsimp [r]
          nlinarith
    have hsumLog :
        (∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
          (plaquettePolymerIncompatible Λ γ),
            plaquetteDobrushinWeight q δ) ≤ (n : ℝ) * Real.log 2 := by
      exact hsum.trans hlog
    have hexp : Real.exp
        (∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
          (plaquettePolymerIncompatible Λ γ),
            plaquetteDobrushinWeight q δ) ≤ (2 : ℝ) ^ n := by
      calc
        _ ≤ Real.exp ((n : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hsumLog
        _ = (2 : ℝ) ^ n := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    have hactivity := norm_plaquettePolymer_activity_le Λ Φ β γ
    have hactivity' : ‖(plaquettePolymerModel Λ Φ β).activity γ‖ ≤ q ^ n := by
      simpa [q, n, PlaquettePolymer.support] using hactivity
    have hlhs : ‖(plaquettePolymerModel Λ Φ β).activity γ‖ * Real.exp
        (∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
          ((plaquettePolymerModel Λ Φ β).incompatible γ),
            plaquetteDobrushinWeight q δ) ≤ (2 * q) ^ n := by
      calc
        _ ≤ q ^ n * (2 : ℝ) ^ n :=
          mul_le_mul hactivity' hexp (Real.exp_pos _).le (pow_nonneg hq₀ _)
        _ = (2 * q) ^ n := by rw [mul_pow]; ring
    have haHalf : (2 * q) ^ n ≤ r ^ n / 2 := by
      have htwoPow : (2 : ℝ) ≤ 4 ^ n := by
        exact_mod_cast (show (2 : ℕ) ≤ 4 ^ n by
          calc
            (2 : ℕ) ≤ 4 ^ 1 := by norm_num
            _ ≤ 4 ^ n := pow_le_pow_right' (by omega) hn)
      have hbase : 0 ≤ (2 * q) ^ n := pow_nonneg (mul_nonneg (by norm_num) hq₀) _
      have hrpow : r ^ n = 4 ^ n * (2 * q) ^ n := by
        dsimp [r]
        rw [show (8 : ℝ) * q = 4 * (2 * q) by ring, mul_pow]
      rw [hrpow]
      nlinarith
    have hrpow₁ : r ^ n ≤ 1 := by
      exact pow_le_one₀ hr₀ hr₁
    exact hlhs.trans <| haHalf.trans <|
      half_mul_le_one_sub_exp_neg (pow_nonneg hr₀ _) hrpow₁

end QuantitativeDobrushin

section StrongCouplingDisk

open Gauge Lattice.Cubic Gauge.FiniteVolume

variable {d : ℕ} {G₀ : Type*} [Group G₀] [TopologicalSpace G₀]
  [IsTopologicalGroup G₀] [MeasurableSpace G₀] [BorelSpace G₀]
  [SecondCountableTopology G₀] [GaugeHaarProbability G₀]

/-- A concrete positive complex-coupling radius obtained from a graph-animal
certificate.  The harmless `+1` in the denominator also covers zero
potentials without a case split. -/
def certifiedStrongCouplingRadius (degreeBound animalConstant : ℕ)
    (potentialBound : ℝ) : ℝ :=
  Real.log (1 + dobrushinThreshold degreeBound animalConstant) /
    (potentialBound + 1)

theorem certifiedStrongCouplingRadius_pos
    (degreeBound animalConstant : ℕ) {potentialBound : ℝ}
    (hbound : 0 ≤ potentialBound) :
    0 < certifiedStrongCouplingRadius degreeBound animalConstant potentialBound := by
  unfold certifiedStrongCouplingRadius
  apply div_pos
  · apply Real.log_pos
    linarith [dobrushinThreshold_pos degreeBound animalConstant]
  · linarith

omit [IsTopologicalGroup G₀] [MeasurableSpace G₀] [BorelSpace G₀]
  [SecondCountableTopology G₀] [GaugeHaarProbability G₀] in
theorem perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius
    (Φ : RealPlaquettePotential G₀) (degreeBound animalConstant : ℕ)
    {β : ℂ}
    (hβ : ‖β‖ < certifiedStrongCouplingRadius degreeBound animalConstant Φ.bound) :
    perturbationMajorant Φ β < dobrushinThreshold degreeBound animalConstant := by
  let t := dobrushinThreshold degreeBound animalConstant
  have ht : 0 < t := dobrushinThreshold_pos _ _
  have hden : 0 < Φ.bound + 1 := by linarith [Φ.bound_nonneg]
  have hmul : ‖β‖ * (Φ.bound + 1) < Real.log (1 + t) := by
    exact (lt_div_iff₀ hden).mp hβ
  have hboundMul : ‖β‖ * Φ.bound ≤ ‖β‖ * (Φ.bound + 1) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg β)
  have hexp : Real.exp (‖β‖ * Φ.bound) < 1 + t := by
    rw [← Real.exp_log (by linarith : 0 < 1 + t)]
    exact Real.exp_lt_exp.mpr (hboundMul.trans_lt hmul)
  change Real.exp (‖β‖ * Φ.bound) - 1 < t
  linarith

/-- Explicit finite-volume zero-free theorem for the Yang--Mills partition
function.  Its radius depends only on the potential bound and the two uniform
counting constants, not on the volume or exterior configuration. -/
theorem complexPartitionFunction_ne_zero_of_norm_lt_certifiedRadius
    (Λ : FiniteSpecification d G₀) (Φ : RealPlaquettePotential G₀)
    (cert : AnimalCountingCertificate (ActivePlaquette Λ)
      (plaquetteAdjacencyGraph Λ)) {β : ℂ}
    (hβ : ‖β‖ < certifiedStrongCouplingRadius cert.degreeBound
      cert.animalConstant Φ.bound) :
    complexPartitionFunction Λ Φ β ≠ 0 := by
  rw [complexPartitionFunction_eq_polymerPartition]
  apply (plaquettePolymerModel Λ Φ β).partitionFunction_ne_zero_of_dobrushin
    (plaquetteDobrushinWeight (perturbationMajorant Φ β))
  apply plaquettePolymerModel_dobrushin Λ Φ β cert
  exact perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
    cert.degreeBound cert.animalConstant hβ

/-- Dimension-only strong-coupling radius for the cubic plaquette gas. -/
def latticeStrongCouplingRadius (d : ℕ) (potentialBound : ℝ) : ℝ :=
  certifiedStrongCouplingRadius (16 * d) (2 ^ (16 * d)) potentialBound

theorem latticeStrongCouplingRadius_pos (d : ℕ) {potentialBound : ℝ}
    (hbound : 0 ≤ potentialBound) :
    0 < latticeStrongCouplingRadius d potentialBound :=
  certifiedStrongCouplingRadius_pos _ _ hbound

omit [IsTopologicalGroup G₀] [MeasurableSpace G₀] [BorelSpace G₀]
  [SecondCountableTopology G₀] [GaugeHaarProbability G₀] in
/-- On the explicit lattice disk, the twice-tilted plaquette activity
majorant remains inside the geometric animal radius.  This is the scalar
estimate used when an additional factor `exp (plaquetteKPWeight γ) = 2^|γ|`
is attached to every polymer. -/
theorem animalConstant_mul_two_mul_perturbationMajorant_lt_one
    (Φ : RealPlaquettePotential G₀) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    (2 ^ (16 * d) : ℝ) * (2 * perturbationMajorant Φ β) < 1 := by
  let C : ℕ := 2 ^ (16 * d)
  have hsmall :=
    perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
      (16 * d) (2 ^ (16 * d)) hβ
  rw [dobrushinThreshold, lt_min_iff, lt_min_iff] at hsmall
  have hqAnimal := hsmall.2.1
  have hqAnimal' : perturbationMajorant Φ β <
      1 / ((16 : ℝ) * ((C : ℝ) + 1)) := by
    simpa [C] using hqAnimal
  have hCnonneg : 0 ≤ (C : ℝ) := by positivity
  have hdenpos : 0 < (16 : ℝ) * ((C : ℝ) + 1) := by positivity
  have hmul := (lt_div_iff₀ hdenpos).mp hqAnimal'
  have htarget : (C : ℝ) * (2 * perturbationMajorant Φ β) < 1 := by
    nlinarith
  simpa [C] using htarget

/-- Milestone 9 exit theorem: the exact finite-volume Yang--Mills partition
function is zero-free on one explicit nonzero disk, uniformly over every
finite specification and every exterior configuration in dimension `d`. -/
theorem complexPartitionFunction_ne_zero_of_norm_lt_latticeRadius
    (Λ : FiniteSpecification d G₀) (Φ : RealPlaquettePotential G₀)
    {β : ℂ} (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    complexPartitionFunction Λ Φ β ≠ 0 := by
  exact complexPartitionFunction_ne_zero_of_norm_lt_certifiedRadius Λ Φ
    (cubicPlaquetteAnimalCertificate Λ) hβ

end StrongCouplingDisk

/-- Infinite geometric majorant for animals of size at least `r + 1`. -/
def geometricAnimalTail (q C : ℝ) (r : ℕ) : ℝ :=
  ∑' k : ℕ, q * (C * q) ^ (k + r)

theorem geometricAnimalTail_eq (q C : ℝ) (r : ℕ)
    (hq : 0 ≤ q) (hC : 0 ≤ C) (hsmall : C * q < 1) :
    geometricAnimalTail q C r = q * (C * q) ^ r / (1 - C * q) := by
  have hnonneg : 0 ≤ C * q := mul_nonneg hC hq
  unfold geometricAnimalTail
  calc
    (∑' k : ℕ, q * (C * q) ^ (k + r)) =
        ∑' k : ℕ, (q * (C * q) ^ r) * (C * q) ^ k := by
      congr 1
      funext k
      rw [pow_add]
      ring
    _ = (q * (C * q) ^ r) * (1 - C * q)⁻¹ :=
      ((hasSum_geometric_of_lt_one hnonneg hsmall).mul_left
        (q * (C * q) ^ r)).tsum_eq
    _ = q * (C * q) ^ r / (1 - C * q) := by rw [div_eq_mul_inv]

theorem geometricAnimalTail_nonneg (q C : ℝ) (r : ℕ)
    (hq : 0 ≤ q) (hC : 0 ≤ C) :
    0 ≤ geometricAnimalTail q C r := by
  unfold geometricAnimalTail
  exact tsum_nonneg fun _ => mul_nonneg hq (pow_nonneg (mul_nonneg hC hq) _)

/-- Explicit radius solving `K (exp(|β| M)-1) < 1`. -/
def betaStrong (K M : ℝ) : ℝ :=
  Real.log (1 + K⁻¹) / M

theorem betaStrong_pos {K M : ℝ} (hK : 0 < K) (hM : 0 < M) :
    0 < betaStrong K M := by
  unfold betaStrong
  apply div_pos
  · apply Real.log_pos
    nlinarith [inv_pos.mpr hK]
  · exact hM

/-- The explicit disk implies the scalar geometric KP smallness inequality. -/
theorem geometricKP_of_norm_lt_betaStrong {K M : ℝ} (hK : 0 < K) (hM : 0 < M)
    {β : ℂ} (hβ : ‖β‖ < betaStrong K M) :
    K * (Real.exp (‖β‖ * M) - 1) < 1 := by
  have hlog : ‖β‖ * M < Real.log (1 + K⁻¹) := by
    rw [betaStrong] at hβ
    exact (lt_div_iff₀ hM).mp hβ
  have hone : 0 < 1 + K⁻¹ := by positivity
  have hexp : Real.exp (‖β‖ * M) < 1 + K⁻¹ := by
    rw [← Real.exp_log hone]
    exact Real.exp_lt_exp.mpr hlog
  have hKnonneg : 0 ≤ K := hK.le
  calc
    K * (Real.exp (‖β‖ * M) - 1) < K * ((1 + K⁻¹) - 1) := by
      gcongr
    _ = 1 := by field_simp; ring

/-- A geometric counting argument can be exposed through this narrow bridge:
once the scalar smallness inequality holds, it supplies the finite KP deletion
certificate required by the abstract gas. -/
def GeometricKPBridge {P : Type*} [Fintype P] [DecidableEq P]
    (M : ℂ → FinitePolymerModel P) (K scale : ℝ) : Prop :=
  ∀ β, K * (Real.exp (‖β‖ * scale) - 1) < 1 →
    (M β).FiniteKPCertificate Finset.univ

/-- Concrete nonzero-radius theorem discharging the abstract KP certificate. -/
theorem partition_nonzero_of_norm_lt_betaStrong
    {P : Type*} [Fintype P] [DecidableEq P]
    (M : ℂ → FinitePolymerModel P) {K scale : ℝ}
    (hK : 0 < K) (hscale : 0 < scale)
    (hbridge : GeometricKPBridge M K scale)
    {β : ℂ} (hβ : ‖β‖ < betaStrong K scale) :
    (M β).partitionFunction ≠ 0 := by
  apply (M β).partitionFunction_ne_zero_of_finiteKP
  exact hbridge β (geometricKP_of_norm_lt_betaStrong hK hscale hβ)

end

end YangMills.StrongCoupling
