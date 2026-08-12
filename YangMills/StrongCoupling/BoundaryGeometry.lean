/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.Counting
import YangMills.StrongCoupling.MarkedExpansion
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Geometry of observable roots and boundary defects

This file identifies the two finite plaquette sets that enter boundary
mixing.  Observable roots meet the recorded edge support of the insertion;
boundary defects read a frozen edge on which the two exterior configurations
differ.  It also proves the two uniform geometric facts used by the decay
estimate: at most `4d` roots per observable edge, and a connected plaquette
set joining points at graph distance `r` has more than `r` plaquettes.
-/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

local instance boundaryGeometryDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*}

/-- Active plaquettes whose boundary meets the recorded support of `F`. -/
def observableRootPlaquettes [TopologicalSpace G]
    (Λ : FiniteSpecification d G) (F : LocalObservable d G) :
    Finset (ActivePlaquette Λ) :=
  Finset.univ.filter fun p =>
    ¬Disjoint p.1.boundary.edgeSupport F.support

/-- Active plaquettes that read a frozen edge on which two exterior
configurations differ. -/
def boundaryDisagreementPlaquettes
    (Λ : FiniteSpecification d G) (η η' : Gauge.Configuration d G) :
    Finset (ActivePlaquette Λ) := by
  classical
  exact Finset.univ.filter fun p =>
    ∃ e ∈ p.1.boundary.edgeSupport,
      e ∉ Λ.dynamicEdges ∧ η e ≠ η' e

@[simp]
theorem mem_observableRootPlaquettes [TopologicalSpace G]
    (Λ : FiniteSpecification d G) (F : LocalObservable d G)
    (p : ActivePlaquette Λ) :
    p ∈ observableRootPlaquettes Λ F ↔
      ¬Disjoint p.1.boundary.edgeSupport F.support := by
  simp [observableRootPlaquettes]

@[simp]
theorem mem_boundaryDisagreementPlaquettes
    (Λ : FiniteSpecification d G) (η η' : Gauge.Configuration d G)
    (p : ActivePlaquette Λ) :
    p ∈ boundaryDisagreementPlaquettes Λ η η' ↔
      ∃ e ∈ p.1.boundary.edgeSupport,
        e ∉ Λ.dynamicEdges ∧ η e ≠ η' e := by
  simp [boundaryDisagreementPlaquettes]

/-- Candidate roots obtained by taking every plaquette incident to an
observable-support edge. -/
def observableRootCandidates [TopologicalSpace G]
    (F : LocalObservable d G) : Finset (Plaquette d) :=
  F.support.biUnion incidentPlaquettes

theorem observableRootPlaquettes_card_le_candidates [TopologicalSpace G]
    (Λ : FiniteSpecification d G) (F : LocalObservable d G) :
    (observableRootPlaquettes Λ F).card ≤
      (observableRootCandidates F).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : ActivePlaquette Λ => p.1)
  · intro p hp
    have hroot := (mem_observableRootPlaquettes Λ F p).mp hp
    rw [Finset.not_disjoint_iff] at hroot
    obtain ⟨e, hep, heF⟩ := hroot
    exact Finset.mem_biUnion.mpr
      ⟨e, heF, mem_incidentPlaquettes_of_mem_boundary e p.1 hep⟩
  · intro p _ q _ hpq
    exact Subtype.ext hpq

/-- Each recorded observable edge creates at most `4d` plaquette roots. -/
theorem card_observableRootPlaquettes_le [TopologicalSpace G]
    (Λ : FiniteSpecification d G) (F : LocalObservable d G) :
    (observableRootPlaquettes Λ F).card ≤ 4 * d * F.support.card := by
  classical
  calc
    (observableRootPlaquettes Λ F).card ≤
        (observableRootCandidates F).card :=
      observableRootPlaquettes_card_le_candidates Λ F
    _ ≤ ∑ e ∈ F.support, (incidentPlaquettes e).card := by
      simpa [observableRootCandidates] using
        (Finset.card_biUnion_le (s := F.support) (t := incidentPlaquettes))
    _ ≤ ∑ _e ∈ F.support, 4 * d := by
      apply Finset.sum_le_sum
      intro e _
      exact card_incidentPlaquettes_le e
    _ = 4 * d * F.support.card := by
      simp [Nat.mul_comm]

/-- If a selected active plaquette set avoids the disagreement plaquettes,
its marked weight is exactly the same for both exterior configurations. -/
theorem markedSubsetWeight_withExterior_eq_of_disjoint_defects
    [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [GaugeHaarProbability G]
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (X : Finset (Plaquette d))
    (η η' : Gauge.Configuration d G) (hF : F.support ⊆ Λ.dynamicEdges)
    (hX : X ⊆ Λ.activePlaquettes)
    (hdisjoint : Disjoint (activeSubset Λ X)
      (boundaryDisagreementPlaquettes Λ η η')) :
    markedSubsetWeight F (withExterior Λ η) Φ β X =
      markedSubsetWeight F (withExterior Λ η') Φ β X := by
  apply markedSubsetWeight_withExterior_eq_of_eqOn F Λ Φ β X η η' hF
  intro p hp e he hedyn
  by_contra hne
  let pA : ActivePlaquette Λ := ⟨p, hX hp⟩
  have hpX : pA ∈ activeSubset Λ X := by
    simp [activeSubset, pA, hp]
  have hpD : pA ∈ boundaryDisagreementPlaquettes Λ η η' := by
    rw [mem_boundaryDisagreementPlaquettes]
    exact ⟨e, he, hedyn, hne⟩
  exact (Finset.disjoint_left.mp hdisjoint hpX hpD)

/-- If a selected active plaquette set avoids the disagreement plaquettes,
its unmarked polymer activity is also exactly independent of the two exterior
fields. -/
theorem subsetWeight_withExterior_eq_of_disjoint_defects
    [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [GaugeHaarProbability G]
    (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (X : Finset (Plaquette d))
    (η η' : Gauge.Configuration d G)
    (hX : X ⊆ Λ.activePlaquettes)
    (hdisjoint : Disjoint (activeSubset Λ X)
      (boundaryDisagreementPlaquettes Λ η η')) :
    subsetWeight (withExterior Λ η) Φ β X =
      subsetWeight (withExterior Λ η') Φ β X := by
  apply subsetWeight_withExterior_eq_of_eqOn Λ Φ β X η η'
  intro p hp e he hedyn
  by_contra hne
  let pA : ActivePlaquette Λ := ⟨p, hX hp⟩
  have hpX : pA ∈ activeSubset Λ X := by
    simp [activeSubset, pA, hp]
  have hpD : pA ∈ boundaryDisagreementPlaquettes Λ η η' := by
    rw [mem_boundaryDisagreementPlaquettes]
    exact ⟨e, he, hedyn, hne⟩
  exact (Finset.disjoint_left.mp hdisjoint hpX hpD)

/-- Distance conversion inside a connected active plaquette set.  The graph
distance between any two of its plaquettes is strictly smaller than its
cardinality. -/
theorem plaquette_dist_lt_card_of_connected_subset
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d))
    (hX : X ⊆ Λ.activePlaquettes)
    (hconnected : ((plaquetteAdjacencyGraph Λ).induce
      (activeSubset Λ X : Set (ActivePlaquette Λ))).Connected)
    (p q : ActivePlaquette Λ) (hp : p.1 ∈ X) (hq : q.1 ∈ X) :
    (plaquetteAdjacencyGraph Λ).dist p q < X.card := by
  classical
  let pX : activeSubset Λ X := ⟨p, by simp [activeSubset, hp]⟩
  let qX : activeSubset Λ X := ⟨q, by simp [activeSubset, hq]⟩
  obtain ⟨w, hw⟩ := (hconnected pX qX).exists_isPath
  let w' := w.map (SimpleGraph.Embedding.induce
    (activeSubset Λ X : Set (ActivePlaquette Λ))).toHom
  have hdist : (plaquetteAdjacencyGraph Λ).dist p q ≤ w'.length := by
    simpa [w', pX, qX] using SimpleGraph.dist_le w'
  have hlength : w.length < (activeSubset Λ X).card := by
    simpa using hw.length_lt
  have hcard : (activeSubset Λ X).card = X.card := by
    have hmap := activeSubset_map_val_eq Λ X hX
    calc
      (activeSubset Λ X).card =
          ((activeSubset Λ X).map ⟨Subtype.val, Subtype.val_injective⟩).card :=
        (Finset.card_map _).symm
      _ = X.card := congrArg Finset.card hmap
  simp only [w', SimpleGraph.Walk.length_map] at hdist
  rw [hcard] at hlength
  exact hdist.trans_lt hlength

end

end YangMills.StrongCoupling
