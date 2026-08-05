/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.Dobrushin
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Connected clusters in a finite polymer gas

This module defines the incompatibility graph of an ordered polymer tuple and
its Ursell coefficient as the signed sum over connected spanning subgraphs.
It also supplies a deliberately safe finite-graph majorant and an analytic
finite-volume KP interface.  The majorant counts every graph rather than using
an optimized Penrose partition; this loses constants but keeps every estimate
explicit and auditable.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

namespace FinitePolymerModel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Incompatibility graph carried by an ordered tuple of polymers. -/
def incompatibilityGraph (M : FinitePolymerModel P) {n : ℕ} (γ : Fin n → P) :
    SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ M.incompatible (γ i) (γ j)
  symm _ _ h := ⟨h.1.symm, M.symmetric_incompatible h.2⟩
  loopless := ⟨fun i (h : i ≠ i ∧ M.incompatible (γ i) (γ i)) => h.1 rfl⟩

/-- Connected spanning subgraphs of a finite incompatibility graph. -/
def connectedSpanningSubgraphs {n : ℕ} (G : SimpleGraph (Fin n)) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact Finset.univ.filter fun H => H ≤ G ∧ H.Connected

/-- Signed connected-graph sum.  This is the usual Ursell coefficient. -/
def ursellGraph {n : ℕ} (G : SimpleGraph (Fin n)) : ℤ := by
  classical
  exact ∑ H ∈ connectedSpanningSubgraphs G, (-1 : ℤ) ^ H.edgeFinset.card

/-- Ursell coefficient of an ordered polymer tuple. -/
def ursell (M : FinitePolymerModel P) {n : ℕ} (γ : Fin n → P) : ℤ :=
  ursellGraph (M.incompatibilityGraph γ)

theorem connectedSpanningSubgraphs_eq_empty_of_not_connected {n : ℕ}
    {G : SimpleGraph (Fin n)} (hG : ¬G.Connected) :
    connectedSpanningSubgraphs G = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro H hH
  have hH' : H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin n) => H ≤ G ∧ H.Connected) := by
    simpa only [connectedSpanningSubgraphs] using hH
  rcases Finset.mem_filter.mp hH' with ⟨_, hHG, hHconn⟩
  exact hG (hHconn.mono hHG)

/-- The connected graph sum vanishes when its ambient graph is disconnected. -/
theorem ursellGraph_eq_zero_of_not_connected {n : ℕ}
    {G : SimpleGraph (Fin n)} (hG : ¬G.Connected) :
    ursellGraph G = 0 := by
  rw [ursellGraph, connectedSpanningSubgraphs_eq_empty_of_not_connected hG]
  simp

omit [DecidableEq P] in
/-- Polymer Ursell coefficients vanish on disconnected incompatibility graphs. -/
theorem ursell_eq_zero_of_not_connected (M : FinitePolymerModel P) {n : ℕ}
    {γ : Fin n → P} (hγ : ¬(M.incompatibilityGraph γ).Connected) :
    M.ursell γ = 0 :=
  ursellGraph_eq_zero_of_not_connected hγ

/-- Safe all-graph majorant. Each signed summand has norm one. -/
theorem norm_ursellGraph_le_card_graphs {n : ℕ} (G : SimpleGraph (Fin n)) :
    ‖ursellGraph G‖ ≤ (Fintype.card (SimpleGraph (Fin n)) : ℤ) := by
  classical
  calc
    ‖ursellGraph G‖ ≤
        ∑ H ∈ connectedSpanningSubgraphs G, ‖(-1 : ℤ) ^ H.edgeFinset.card‖ := by
      rw [ursellGraph]
      exact norm_sum_le _ _
    _ = ((connectedSpanningSubgraphs G).card : ℤ) := by simp
    _ ≤ (Fintype.card (SimpleGraph (Fin n)) : ℤ) := by
      exact_mod_cast Finset.card_le_univ (connectedSpanningSubgraphs G)

/-- Spanning trees contained in a finite graph. -/
def spanningTrees {n : ℕ} (G : SimpleGraph (Fin n)) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact Finset.univ.filter fun T => T ≤ G ∧ T.IsTree

/-- A canonical spanning tree of a connected finite graph. -/
noncomputable def chosenSpanningTree {n : ℕ} (G : SimpleGraph (Fin n)) :
    SimpleGraph (Fin n) := by
  classical
  exact if h : G.Connected then Classical.choose h.exists_isTree_le else ⊥

theorem chosenSpanningTree_le_of_connected {n : ℕ}
    {G : SimpleGraph (Fin n)} (hG : G.Connected) :
    chosenSpanningTree G ≤ G := by
  rw [chosenSpanningTree, dif_pos hG]
  exact (Classical.choose_spec hG.exists_isTree_le).1

theorem chosenSpanningTree_isTree_of_connected {n : ℕ}
    {G : SimpleGraph (Fin n)} (hG : G.Connected) :
    (chosenSpanningTree G).IsTree := by
  rw [chosenSpanningTree, dif_pos hG]
  exact (Classical.choose_spec hG.exists_isTree_le).2

/-- Conservative tree-indexed graph bound.  A connected spanning subgraph is
encoded by one of its spanning trees together with the subgraph itself.  This
is weaker than the Penrose cancellation bound but makes the spanning-tree
control explicit without additional assumptions. -/
theorem card_connectedSpanningSubgraphs_le_tree_graphs {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    (connectedSpanningSubgraphs G).card ≤
      (spanningTrees G).card * Fintype.card (SimpleGraph (Fin n)) := by
  classical
  let f : SimpleGraph (Fin n) → SimpleGraph (Fin n) × SimpleGraph (Fin n) :=
    fun H => (chosenSpanningTree H, H)
  have hmap : Set.MapsTo f (connectedSpanningSubgraphs G : Set _)
      ((spanningTrees G).product (Finset.univ : Finset (SimpleGraph (Fin n))) : Set _) := by
    intro H hH
    have hdata := (Finset.mem_filter.mp hH).2
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩,
      Finset.mem_univ _⟩
    · exact (chosenSpanningTree_le_of_connected hdata.2).trans hdata.1
    · exact chosenSpanningTree_isTree_of_connected hdata.2
  calc
    (connectedSpanningSubgraphs G).card ≤
        ((spanningTrees G).product
          (Finset.univ : Finset (SimpleGraph (Fin n)))).card :=
      Finset.card_le_card_of_injOn f hmap (fun _ _ _ _ h => congrArg Prod.snd h)
    _ = (spanningTrees G).card * Fintype.card (SimpleGraph (Fin n)) := by simp

/-- Ursell tree-graph majorant obtained from the conservative tree-indexed
encoding above. -/
theorem norm_ursellGraph_le_tree_graphs {n : ℕ} (G : SimpleGraph (Fin n)) :
    ‖ursellGraph G‖ ≤
      ((spanningTrees G).card * Fintype.card (SimpleGraph (Fin n)) : ℕ) := by
  classical
  calc
    ‖ursellGraph G‖ ≤
        ∑ H ∈ connectedSpanningSubgraphs G,
          ‖(-1 : ℤ) ^ H.edgeFinset.card‖ := by
      rw [ursellGraph]
      exact norm_sum_le _ _
    _ = ((connectedSpanningSubgraphs G).card : ℤ) := by simp
    _ ≤ ((spanningTrees G).card * Fintype.card (SimpleGraph (Fin n)) : ℕ) := by
      exact_mod_cast card_connectedSpanningSubgraphs_le_tree_graphs G

/-! ## Analytic finite-volume families -/

/-- A complex-analytic activity family with fixed incompatibility relation. -/
structure AnalyticFamily (P : Type*) [Fintype P] where
  incompatible : P → P → Prop
  decidableIncompatible : DecidableRel incompatible
  symmetric_incompatible : Symmetric incompatible
  self_incompatible : ∀ γ, incompatible γ γ
  activity : ℂ → P → ℂ
  analytic_activity : ∀ γ, AnalyticOnNhd ℂ (fun β => activity β γ) Set.univ

attribute [instance] AnalyticFamily.decidableIncompatible

namespace AnalyticFamily

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The finite polymer model at a fixed coupling. -/
def model (A : AnalyticFamily P) (β : ℂ) : FinitePolymerModel P where
  incompatible := A.incompatible
  decidableIncompatible := A.decidableIncompatible
  symmetric_incompatible := A.symmetric_incompatible
  self_incompatible := A.self_incompatible
  activity := A.activity β

/-- Restricted partition function of an analytic activity family. -/
def partitionOn (A : AnalyticFamily P) (S : Finset P) (β : ℂ) : ℂ := by
  classical
  exact ∑ Γ ∈ S.powerset.filter (fun (Γ : Finset P) =>
      (Γ : Set P).Pairwise fun γ δ => ¬A.incompatible γ δ),
      ∏ γ ∈ Γ, A.activity β γ

/-- Full partition function of an analytic activity family. -/
def partitionFunction (A : AnalyticFamily P) (β : ℂ) : ℂ :=
  A.partitionOn Finset.univ β

/-- Weight of a family as a function of the coupling. -/
def familyWeight (A : AnalyticFamily P) (Γ : Finset P) (β : ℂ) : ℂ :=
  ∏ γ ∈ Γ, A.activity β γ

omit [DecidableEq P] in
theorem analyticOnNhd_familyWeight (A : AnalyticFamily P) (Γ : Finset P) :
    AnalyticOnNhd ℂ (A.familyWeight Γ) Set.univ := by
  classical
  apply Finset.analyticOnNhd_fun_prod Γ
  intro γ _
  exact A.analytic_activity γ

/-- Finite-volume partition functions are analytic because they are finite
sums of finite products of analytic activities. -/
theorem analyticOnNhd_partitionOn (A : AnalyticFamily P) (S : Finset P) :
    AnalyticOnNhd ℂ (A.partitionOn S) Set.univ := by
  classical
  unfold partitionOn
  apply Finset.analyticOnNhd_fun_sum
  intro Γ _
  exact A.analyticOnNhd_familyWeight Γ

theorem analyticOnNhd_partitionFunction (A : AnalyticFamily P) :
    AnalyticOnNhd ℂ A.partitionFunction Set.univ := by
  simpa only [partitionFunction] using A.analyticOnNhd_partitionOn Finset.univ

/-- A family whose induced incompatibility graph is connected.  Empty and
singleton families follow Mathlib's graph-connectedness convention. -/
def ConnectedFamily (A : AnalyticFamily P) (Γ : Finset P) : Prop :=
  (SimpleGraph.fromRel fun γ δ : Γ =>
    γ ≠ δ ∧ A.incompatible γ.1 δ.1).Connected

/-- Finite marked connected-family sum.  It is the finite-volume building
block used for defect insertions; the mark must occur in the family. -/
def markedClusterSum (A : AnalyticFamily P) (S : Finset P) (mark : P)
    (β : ℂ) : ℂ := by
  classical
  exact ∑ Γ ∈ S.powerset.filter (fun Γ => mark ∈ Γ ∧ A.ConnectedFamily Γ),
      A.familyWeight Γ β

/-- Extend the finite marked sum by zero to all finite polymer families. -/
def markedClusterTerm (A : AnalyticFamily P) (S : Finset P) (mark : P)
    (β : ℂ) (Γ : Finset P) : ℂ := by
  classical
  exact if Γ ∈ S.powerset.filter (fun Γ => mark ∈ Γ ∧ A.ConnectedFamily Γ)
    then A.familyWeight Γ β else 0

/-- Absolute convergence of the marked finite-volume cluster sum. -/
theorem summable_norm_markedClusterTerm (A : AnalyticFamily P)
    (S : Finset P) (mark : P) (β : ℂ) :
    Summable fun Γ : Finset P => ‖A.markedClusterTerm S mark β Γ‖ := by
  apply summable_of_hasFiniteSupport
  exact Set.toFinite _

theorem analyticOnNhd_markedClusterSum (A : AnalyticFamily P)
    (S : Finset P) (mark : P) :
    AnalyticOnNhd ℂ (A.markedClusterSum S mark) Set.univ := by
  classical
  unfold markedClusterSum
  apply Finset.analyticOnNhd_fun_sum
  intro Γ _
  exact A.analyticOnNhd_familyWeight Γ

/-- The normalized finite-volume logarithm.  It is used only on domains where
the KP certificate proves the partition function is nonzero. -/
def clusterLog (A : AnalyticFamily P) (S : Finset P) (β : ℂ) : ℂ :=
  Complex.log (A.partitionOn S β)

/-- Finite exponential formula on the KP zero-free domain. -/
theorem exp_clusterLog_eq_partitionOn (A : AnalyticFamily P) (S : Finset P)
    (β : ℂ) (hβ : A.partitionOn S β ≠ 0) :
    Complex.exp (A.clusterLog S β) = A.partitionOn S β := by
  exact Complex.exp_log hβ

/-- Explicit finite analytic KP hypothesis on a coupling domain. -/
def AnalyticKPCertificate (A : AnalyticFamily P) (S : Finset P)
    (D : Set ℂ) : Prop :=
  ∀ β ∈ D, (A.model β).FiniteKPCertificate S

/-- Explicit local analytic Dobrushin--KP hypothesis on a coupling domain. -/
def AnalyticDobrushinCertificate (A : AnalyticFamily P) (S : Finset P)
    (D : Set ℂ) (a : P → ℝ) : Prop :=
  ∀ β ∈ D, (A.model β).DobrushinCertificate S a

/-- Milestone 7 analytic KP theorem.  The cluster sums here are finite-volume
marked connected sums, hence absolutely summable without a limiting argument;
the uniform KP certificate supplies nonvanishing throughout the domain. -/
theorem analyticKP (A : AnalyticFamily P) (S : Finset P) (D : Set ℂ)
    (hKP : A.AnalyticKPCertificate S D) :
    (∀ β ∈ D, A.partitionOn S β ≠ 0) ∧
      AnalyticOnNhd ℂ (A.partitionOn S) Set.univ ∧
      (∀ mark, AnalyticOnNhd ℂ (A.markedClusterSum S mark) Set.univ) ∧
      (∀ β ∈ D, ∀ mark, Summable fun Γ : Finset P =>
        ‖A.markedClusterTerm S mark β Γ‖) ∧
      (∀ β ∈ D, Complex.exp (A.clusterLog S β) = A.partitionOn S β) := by
  have hne : ∀ β ∈ D, A.partitionOn S β ≠ 0 := by
    intro β hβ
    simpa [partitionOn, model, FinitePolymerModel.partitionOn,
      FinitePolymerModel.compatibleFamilies, FinitePolymerModel.Compatible,
      FinitePolymerModel.familyWeight] using
      (A.model β).partitionOn_ne_zero_of_finiteKP S (hKP β hβ)
  refine ⟨hne, A.analyticOnNhd_partitionOn S, ?_, ?_, ?_⟩
  · exact fun mark => A.analyticOnNhd_markedClusterSum S mark
  · exact fun β _ mark => A.summable_norm_markedClusterTerm S mark β
  · intro β hβ
    exact A.exp_clusterLog_eq_partitionOn S β (hne β hβ)

/-- Analytic finite-volume cluster package under the explicit local
Dobrushin--KP inequality.  It supplies zero-freeness on the whole domain;
analyticity and absolute summability of the marked finite cluster sums are
global because their supports are finite. -/
theorem analyticDobrushinKP (A : AnalyticFamily P) (S : Finset P) (D : Set ℂ)
    (a : P → ℝ) (hD : A.AnalyticDobrushinCertificate S D a) :
    (∀ β ∈ D, A.partitionOn S β ≠ 0) ∧
      AnalyticOnNhd ℂ (A.partitionOn S) Set.univ ∧
      (∀ mark, AnalyticOnNhd ℂ (A.markedClusterSum S mark) Set.univ) ∧
      (∀ β ∈ D, ∀ mark, Summable fun Γ : Finset P =>
        ‖A.markedClusterTerm S mark β Γ‖) ∧
      (∀ β ∈ D, Complex.exp (A.clusterLog S β) = A.partitionOn S β) := by
  have hne : ∀ β ∈ D, A.partitionOn S β ≠ 0 := by
    intro β hβ
    simpa [partitionOn, model, FinitePolymerModel.partitionOn,
      FinitePolymerModel.compatibleFamilies, FinitePolymerModel.Compatible,
      FinitePolymerModel.familyWeight] using
      (A.model β).partitionOn_ne_zero_of_dobrushin S a (hD β hβ) S
        (Finset.Subset.rfl)
  refine ⟨hne, A.analyticOnNhd_partitionOn S, ?_, ?_, ?_⟩
  · exact fun mark => A.analyticOnNhd_markedClusterSum S mark
  · exact fun β _ mark => A.summable_norm_markedClusterTerm S mark β
  · intro β hβ
    exact A.exp_clusterLog_eq_partitionOn S β (hne β hβ)

end AnalyticFamily

end FinitePolymerModel

end

end YangMills.Polymer
