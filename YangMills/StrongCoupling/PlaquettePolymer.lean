/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.PlaquetteExpansion
import YangMills.Polymer.GraphComponents

/-!
# Connected plaquette polymers

Plaquettes are adjacent when their factors share a dynamic edge.  Polymers are
nonempty connected finite sets in this graph, and two polymers are incompatible
when they overlap or have adjacent members.  Their activity is the integrated
subset weight from the exact plaquette expansion.
-/

namespace YangMills.StrongCoupling

open MeasureTheory
open Gauge Lattice.Cubic Polymer
open Gauge.FiniteVolume
open scoped BigOperators

noncomputable section

local instance {d : ℕ} : DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- The finite type of active plaquettes. -/
abbrev ActivePlaquette (Λ : FiniteSpecification d G) :=
  {p : Plaquette d // p ∈ Λ.activePlaquettes}

instance (Λ : FiniteSpecification d G) : Fintype (ActivePlaquette Λ) :=
  Fintype.ofFinset Λ.activePlaquettes fun _ => Iff.rfl

instance (Λ : FiniteSpecification d G) : DecidableEq (ActivePlaquette Λ) :=
  Classical.decEq _

/-- Adjacency graph obtained by sharing at least one dynamic edge. -/
def plaquetteAdjacencyGraph (Λ : FiniteSpecification d G) :
    SimpleGraph (ActivePlaquette Λ) where
  Adj p q := p ≠ q ∧ ¬Disjoint (plaquetteDynamicSupport Λ p) (plaquetteDynamicSupport Λ q)
  symm _ _ h := ⟨h.1.symm, fun hd => h.2 hd.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (Λ : FiniteSpecification d G) :
    DecidableRel (plaquetteAdjacencyGraph Λ).Adj :=
  Classical.decRel _

/-- A nonempty connected set of active plaquettes. -/
def PlaquettePolymer (Λ : FiniteSpecification d G) :=
  {γ : Finset (ActivePlaquette Λ) //
    γ.Nonempty ∧ ((plaquetteAdjacencyGraph Λ).induce
      (γ : Set (ActivePlaquette Λ))).Connected}

instance (Λ : FiniteSpecification d G) : Fintype (PlaquettePolymer Λ) := by
  classical
  let candidates := (Finset.univ : Finset (Finset (ActivePlaquette Λ))).filter
    fun (γ : Finset (ActivePlaquette Λ)) =>
    Finset.Nonempty γ ∧ ((plaquetteAdjacencyGraph Λ).induce
      (γ : Set (ActivePlaquette Λ))).Connected
  refine Fintype.ofFinset candidates ?_
  intro γ
  simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro h <;> exact h

instance (Λ : FiniteSpecification d G) : DecidableEq (PlaquettePolymer Λ) :=
  Classical.decEq _

/-- The one-plaquette polymer rooted at an active plaquette. -/
def singletonPlaquettePolymer (Λ : FiniteSpecification d G)
    (p : ActivePlaquette Λ) : PlaquettePolymer Λ :=
  ⟨{p}, Finset.singleton_nonempty p, by
    letI : Nonempty {q // q ∈ ({p} : Finset (ActivePlaquette Λ))} :=
      ⟨⟨p, Finset.mem_singleton_self p⟩⟩
    letI : Subsingleton {q // q ∈ ({p} : Finset (ActivePlaquette Λ))} :=
      ⟨fun q r => Subtype.ext <|
        (Finset.mem_singleton.mp q.2).trans (Finset.mem_singleton.mp r.2).symm⟩
    exact SimpleGraph.Connected.of_subsingleton⟩

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
@[simp]
theorem mem_singletonPlaquettePolymer (Λ : FiniteSpecification d G)
    (p q : ActivePlaquette Λ) :
    q ∈ (singletonPlaquettePolymer Λ p).1 ↔ q = p := by
  simp [singletonPlaquettePolymer]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
@[simp]
theorem card_singletonPlaquettePolymer (Λ : FiniteSpecification d G)
    (p : ActivePlaquette Λ) :
    (singletonPlaquettePolymer Λ p).1.card = 1 := by
  simp [singletonPlaquettePolymer]

/-- Underlying untyped plaquette set of a connected polymer. -/
def PlaquettePolymer.support {Λ : FiniteSpecification d G} (γ : PlaquettePolymer Λ) :
    Finset (Plaquette d) :=
  γ.1.map ⟨Subtype.val, Subtype.val_injective⟩

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
@[simp]
theorem PlaquettePolymer.support_nonempty {Λ : FiniteSpecification d G}
    (γ : PlaquettePolymer Λ) : γ.support.Nonempty := by
  simpa [PlaquettePolymer.support] using γ.2.1

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
theorem PlaquettePolymer.support_subset_active {Λ : FiniteSpecification d G}
    (γ : PlaquettePolymer Λ) : γ.support ⊆ Λ.activePlaquettes := by
  intro p hp
  rcases Finset.mem_map.mp hp with ⟨q, _, rfl⟩
  exact q.2

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Forgetting the active-plaquette subtype is injective on plaquette
polymers. -/
theorem PlaquettePolymer.support_injective {Λ : FiniteSpecification d G} :
    Function.Injective (PlaquettePolymer.support (Λ := Λ)) := by
  intro γ δ h
  apply Subtype.ext
  exact Finset.map_injective ⟨Subtype.val, Subtype.val_injective⟩ h

/-- Polymer incompatibility: some members coincide or are adjacent. -/
def plaquettePolymerIncompatible (Λ : FiniteSpecification d G)
    (γ δ : PlaquettePolymer Λ) : Prop :=
  ∃ p ∈ γ.1, ∃ q ∈ δ.1, p = q ∨ (plaquetteAdjacencyGraph Λ).Adj p q

instance (Λ : FiniteSpecification d G) :
    DecidableRel (plaquettePolymerIncompatible Λ) :=
  Classical.decRel _

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
theorem plaquettePolymerIncompatible_symmetric (Λ : FiniteSpecification d G) :
    Symmetric (plaquettePolymerIncompatible Λ) := by
  rintro γ δ ⟨p, hp, q, hq, hpq⟩
  exact ⟨q, hq, p, hp, hpq.elim (fun h => Or.inl h.symm)
    (fun h => Or.inr ((plaquetteAdjacencyGraph Λ).symm h))⟩

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
theorem plaquettePolymerIncompatible_self (Λ : FiniteSpecification d G)
    (γ : PlaquettePolymer Λ) : plaquettePolymerIncompatible Λ γ γ := by
  obtain ⟨p, hp⟩ := γ.2.1
  exact ⟨p, hp, p, hp, Or.inl rfl⟩

/-- The abstract hard-core model associated with connected plaquette
activities. -/
def plaquettePolymerModel (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    FinitePolymerModel (PlaquettePolymer Λ) where
  incompatible := plaquettePolymerIncompatible Λ
  decidableIncompatible := inferInstance
  symmetric_incompatible := plaquettePolymerIncompatible_symmetric Λ
  self_incompatible := plaquettePolymerIncompatible_self Λ
  activity γ := subsetWeight Λ Φ β γ.support

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] in
/-- A polymer containing `p` is incompatible with the singleton polymer at
`p`. -/
theorem singletonPlaquettePolymer_incompatible_of_mem
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (p : ActivePlaquette Λ) (γ : PlaquettePolymer Λ) (hp : p ∈ γ.1) :
    (plaquettePolymerModel Λ Φ β).incompatible
      (singletonPlaquettePolymer Λ p) γ := by
  exact ⟨p, by simp [singletonPlaquettePolymer], p, hp, Or.inl rfl⟩

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] in
/-- Connected plaquette activities inherit the subset cardinality bound. -/
theorem norm_plaquettePolymer_activity_le (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (γ : PlaquettePolymer Λ) :
    ‖(plaquettePolymerModel Λ Φ β).activity γ‖ ≤
      perturbationMajorant Φ β ^ γ.support.card :=
  norm_subsetWeight_le Λ Φ β γ.support

/-- Exterior replacement without changing the dynamic or active finite sets. -/
def withExterior (Λ : FiniteSpecification d G)
    (η : Gauge.Configuration d G) : FiniteSpecification d G where
  dynamicEdges := Λ.dynamicEdges
  activePlaquettes := Λ.activePlaquettes
  exterior := η

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
@[simp]
theorem withExterior_dynamicEdges
    (Λ : FiniteSpecification d G) (η : Gauge.Configuration d G) :
    (withExterior Λ η).dynamicEdges = Λ.dynamicEdges := rfl

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
@[simp]
theorem withExterior_activePlaquettes
    (Λ : FiniteSpecification d G) (η : Gauge.Configuration d G) :
    (withExterior Λ η).activePlaquettes = Λ.activePlaquettes := rfl

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] in
/-- A subset weight sees exterior data only on boundary edges of its
plaquettes. -/
theorem subsetWeight_withExterior_eq_of_eqOn
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) (η η' : Gauge.Configuration d G)
    (hη : ∀ p ∈ X, ∀ e ∈ p.boundary.edgeSupport, e ∉ Λ.dynamicEdges → η e = η' e) :
    subsetWeight (withExterior Λ η) Φ β X =
      subsetWeight (withExterior Λ η') Φ β X := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun U => by
    unfold subsetIntegrand
    apply Finset.prod_congr rfl
    intro p hp
    unfold plaquettePerturbation plaquetteHolonomy
    have hhol : Gauge.holonomy ((withExterior Λ η).evaluate U) p.boundary =
        Gauge.holonomy ((withExterior Λ η').evaluate U) p.boundary := by
      apply Gauge.holonomy_eq_of_eqOn_edgeSupport
      intro e he
      by_cases hedyn : e ∈ Λ.dynamicEdges
      · simp [FiniteSpecification.evaluate, withExterior, hedyn]
      · simp [FiniteSpecification.evaluate, withExterior, hedyn,
          hη p hp e he hedyn]
    rw [hhol]

/-! ## Canonical connected components -/

/-- Union of the underlying plaquette supports in a polymer family. -/
def polymerFamilySupport (Λ : FiniteSpecification d G)
    (Γ : Finset (PlaquettePolymer Λ)) : Finset (Plaquette d) := by
  classical
  exact Γ.biUnion PlaquettePolymer.support

/-- Active plaquettes belonging to an arbitrary untyped subset. -/
def activeSubset (Λ : FiniteSpecification d G) (X : Finset (Plaquette d)) :
    Finset (ActivePlaquette Λ) :=
  Finset.univ.filter fun p => p.1 ∈ X

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Forgetting the active-plaque subtype recovers a subset that was already
contained in the active plaquettes. -/
theorem activeSubset_map_val_eq
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d))
    (hX : X ⊆ Λ.activePlaquettes) :
    (activeSubset Λ X).map ⟨Subtype.val, Subtype.val_injective⟩ = X := by
  classical
  ext p
  simp only [activeSubset, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hp
    exact ⟨⟨p, hX hp⟩, hp, rfl⟩

/-- Polymer associated with one connected component of the graph induced on
an active plaquette subset. -/
def componentPolymer (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d))
    (c : ((plaquetteAdjacencyGraph Λ).induce
      (activeSubset Λ X : Set (ActivePlaquette Λ))).ConnectedComponent) :
    PlaquettePolymer Λ :=
  ⟨Polymer.GraphComponents.componentFinset
      (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) c,
    Polymer.GraphComponents.componentFinset_nonempty
      (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) c,
    Polymer.GraphComponents.connected_induce_componentFinset
      (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) c⟩

/-- The canonical family of connected components of a plaquette subset. -/
def componentFamily (Λ : FiniteSpecification d G) (X : Finset (Plaquette d)) :
    Finset (PlaquettePolymer Λ) := by
  classical
  exact Finset.univ.image (componentPolymer Λ X)

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Distinct graph components produce distinct polymers. -/
theorem componentPolymer_injective (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) : Function.Injective (componentPolymer Λ X) := by
  intro a b hab
  obtain ⟨v, hv⟩ := Polymer.GraphComponents.componentFinset_nonempty
    (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) a
  have hvb : v ∈ Polymer.GraphComponents.componentFinset
      (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) b := by
    have hsupport : (componentPolymer Λ X a).1 = (componentPolymer Λ X b).1 :=
      congrArg Subtype.val hab
    change Polymer.GraphComponents.componentFinset
      (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) a =
        Polymer.GraphComponents.componentFinset
          (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) b at hsupport
    rw [← hsupport]
    exact hv
  rcases Finset.mem_map.mp hv with ⟨va, hva, hvaVal⟩
  rcases Finset.mem_map.mp hvb with ⟨vb, hvb, hvbVal⟩
  have hvab : va = vb := Subtype.ext (hvaVal.trans hvbVal.symm)
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (Finset.mem_filter.mp hva).2 (hvab ▸ (Finset.mem_filter.mp hvb).2)

/-- Untyped plaquette supports of the canonical components. -/
def componentSupports (Λ : FiniteSpecification d G) (X : Finset (Plaquette d)) :
    Finset (Finset (Plaquette d)) := by
  classical
  exact Finset.univ.image fun c => (componentPolymer Λ X c).support

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Canonical component supports cover the original active subset. -/
theorem biUnion_componentSupports_eq (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) (hX : X ⊆ Λ.activePlaquettes) :
    (componentSupports Λ X).biUnion id = X := by
  classical
  ext p
  constructor
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨Y, hY, hpY⟩
    rcases Finset.mem_image.mp hY with ⟨c, _, rfl⟩
    rcases Finset.mem_map.mp hpY with ⟨q, hq, hqp⟩
    have hqActive := Polymer.GraphComponents.componentFinset_subset
      (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) c hq
    have hqX : q.1 ∈ X := (Finset.mem_filter.mp hqActive).2
    have hqp' : q.1 = p := hqp
    rw [hqp'] at hqX
    exact hqX
  · intro hp
    let q : ActivePlaquette Λ := ⟨p, hX hp⟩
    have hqActive : q ∈ activeSubset Λ X := by
      simp [activeSubset, q, hp]
    have hqUnion : q ∈ (Polymer.GraphComponents.componentFinsets
        (plaquetteAdjacencyGraph Λ) (activeSubset Λ X)).biUnion id := by
      rw [Polymer.GraphComponents.biUnion_componentFinsets]
      exact hqActive
    rcases Finset.mem_biUnion.mp hqUnion with ⟨Y, hY, hqY⟩
    rcases (Polymer.GraphComponents.mem_componentFinsets
      (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) Y).mp hY with ⟨c, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(componentPolymer Λ X c).support, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩
    · apply Finset.mem_map.mpr
      exact ⟨q, hqY, rfl⟩

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Canonical component supports are pairwise disjoint. -/
theorem pairwise_disjoint_componentSupports (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) :
    (componentSupports Λ X : Set (Finset (Plaquette d))).Pairwise Disjoint := by
  classical
  intro A hA B hB hAB
  rcases Finset.mem_image.mp hA with ⟨a, _, rfl⟩
  rcases Finset.mem_image.mp hB with ⟨b, _, rfl⟩
  have hab : a ≠ b := fun h => hAB (by subst b; rfl)
  apply Finset.disjoint_left.mpr
  intro p hpA hpB
  rcases Finset.mem_map.mp hpA with ⟨pa, hpa, hpaVal⟩
  rcases Finset.mem_map.mp hpB with ⟨pb, hpb, hpbVal⟩
  have hpab : pa = pb := Subtype.ext (hpaVal.trans hpbVal.symm)
  have hpair := Polymer.GraphComponents.pairwise_disjoint_componentFinsets
    (plaquetteAdjacencyGraph Λ) (activeSubset Λ X)
  have ha := (Polymer.GraphComponents.mem_componentFinsets
    (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) _).2 ⟨a, rfl⟩
  have hb := (Polymer.GraphComponents.mem_componentFinsets
    (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) _).2 ⟨b, rfl⟩
  exact (Finset.disjoint_left.mp (hpair ha hb (fun h => hab <|
    componentPolymer_injective Λ X <| Subtype.ext h))) hpa (hpab ▸ hpb)

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] in
/-- The canonical connected-component family is compatible. -/
theorem componentFamily_compatible (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (X : Finset (Plaquette d)) :
    (plaquettePolymerModel Λ Φ β).Compatible (componentFamily Λ X) := by
  classical
  intro γ hγ δ hδ hγδ
  rcases Finset.mem_image.mp hγ with ⟨a, _, rfl⟩
  rcases Finset.mem_image.mp hδ with ⟨b, _, rfl⟩
  have hab : a ≠ b := fun h => hγδ (by subst b; rfl)
  rintro ⟨p, hp, q, hq, hpq⟩
  rcases hpq with hpq | hpq
  · subst q
    exact hab (Polymer.GraphComponents.component_eq_of_mem
      (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) hp hq)
  · exact Polymer.GraphComponents.not_adj_of_mem_componentFinset_of_ne
      (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) hab hp hq hpq

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- The untyped support of the canonical family is the original active
plaquette subset. -/
theorem polymerFamilySupport_componentFamily_eq
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d))
    (hX : X ⊆ Λ.activePlaquettes) :
    polymerFamilySupport Λ (componentFamily Λ X) = X := by
  classical
  calc
    polymerFamilySupport Λ (componentFamily Λ X) =
        (componentSupports Λ X).biUnion id := by
      ext p
      simp [polymerFamilySupport, componentFamily, componentSupports]
    _ = X := biUnion_componentSupports_eq Λ X hX

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Distinct canonical components read disjoint dynamic coordinates. -/
theorem pairwise_disjoint_componentCoordinateSupports
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d)) :
    (componentSupports Λ X : Set (Finset (Plaquette d))).Pairwise
      fun A B => Disjoint
        (subsetCoordinateSupport Λ A : Set Λ.dynamicEdges)
        (subsetCoordinateSupport Λ B : Set Λ.dynamicEdges) := by
  classical
  intro A hA B hB hAB
  rcases Finset.mem_image.mp hA with ⟨a, _, rfl⟩
  rcases Finset.mem_image.mp hB with ⟨b, _, rfl⟩
  have hab : a ≠ b := fun h => hAB (by subst b; rfl)
  apply Set.disjoint_left.mpr
  intro e heA heB
  rcases Finset.mem_biUnion.mp heA with ⟨p, hpA, hep⟩
  rcases Finset.mem_biUnion.mp heB with ⟨q, hqB, heq⟩
  rcases Finset.mem_map.mp hpA with ⟨pa, hpa, hpaVal⟩
  rcases Finset.mem_map.mp hqB with ⟨qb, hqb, hqbVal⟩
  have hpaVal' : pa.1 = p := hpaVal
  have hqbVal' : qb.1 = q := hqbVal
  have hpane : pa ≠ qb := by
    intro hpq
    apply hab
    exact Polymer.GraphComponents.component_eq_of_mem
      (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) hpa (hpq ▸ hqb)
  have hePa : e.1 ∈ plaquetteDynamicSupport Λ pa.1 := by
    simp only [plaquetteDynamicSupport, Finset.mem_filter]
    exact ⟨e.2, hpaVal' ▸ (Finset.mem_filter.mp hep).2⟩
  have heQb : e.1 ∈ plaquetteDynamicSupport Λ qb.1 := by
    simp only [plaquetteDynamicSupport, Finset.mem_filter]
    exact ⟨e.2, hqbVal' ▸ (Finset.mem_filter.mp heq).2⟩
  have hadj : (plaquetteAdjacencyGraph Λ).Adj pa qb :=
    ⟨hpane, Finset.not_disjoint_iff.mpr ⟨e.1, hePa, heQb⟩⟩
  exact Polymer.GraphComponents.not_adj_of_mem_componentFinset_of_ne
    (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) hab hpa hqb hadj

/-- A plaquette-subset weight is the product of the activities of its
canonical connected components. -/
theorem subsetWeight_eq_componentFamilyWeight
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) (hX : X ⊆ Λ.activePlaquettes) :
    subsetWeight Λ Φ β X =
      (plaquettePolymerModel Λ Φ β).familyWeight (componentFamily Λ X) := by
  classical
  have hsupportInj : Function.Injective
      (fun c => (componentPolymer Λ X c).support) := by
    intro a b h
    apply componentPolymer_injective Λ X
    apply Subtype.ext
    apply Finset.map_injective ⟨Subtype.val, Subtype.val_injective⟩
    exact h
  calc
    subsetWeight Λ Φ β X = subsetWeight Λ Φ β
        ((componentSupports Λ X).biUnion id) := by
      rw [biUnion_componentSupports_eq Λ X hX]
    _ = ∏ A ∈ componentSupports Λ X, subsetWeight Λ Φ β A :=
      subsetWeight_biUnion Λ Φ β (componentSupports Λ X)
        (pairwise_disjoint_componentSupports Λ X)
        (pairwise_disjoint_componentCoordinateSupports Λ X)
    _ = (plaquettePolymerModel Λ Φ β).familyWeight
        (componentFamily Λ X) := by
      unfold componentSupports componentFamily FinitePolymerModel.familyWeight
      rw [Finset.prod_image hsupportInj.injOn]
      rw [Finset.prod_image (componentPolymer_injective Λ X).injOn]
      rfl

/-! ## Uniqueness of compatible component decompositions -/

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
private theorem familyOwner_exists (Λ : FiniteSpecification d G)
    (Γ : Finset (PlaquettePolymer Λ)) (X : Finset (Plaquette d))
    (hcover : polymerFamilySupport Λ Γ = X) (q : activeSubset Λ X) :
    ∃ γ ∈ Γ, q.1 ∈ γ.1 := by
  classical
  have hqX : q.1.1 ∈ X := (Finset.mem_filter.mp q.2).2
  have hqUnion : q.1.1 ∈ polymerFamilySupport Λ Γ := by
    rw [hcover]
    exact hqX
  rcases Finset.mem_biUnion.mp hqUnion with ⟨γ, hγ, hqγ⟩
  rcases Finset.mem_map.mp hqγ with ⟨r, hr, hrq⟩
  have hrq' : r = q.1 := Subtype.ext hrq
  exact ⟨γ, hγ, hrq' ▸ hr⟩

/-- The unique member of a compatible covering family that contains a given
active plaquette. -/
private noncomputable def familyOwner (Λ : FiniteSpecification d G)
    (Γ : Finset (PlaquettePolymer Λ)) (X : Finset (Plaquette d))
    (hcover : polymerFamilySupport Λ Γ = X) (q : activeSubset Λ X) :
    PlaquettePolymer Λ :=
  Classical.choose (familyOwner_exists Λ Γ X hcover q)

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
private theorem familyOwner_mem_family (Λ : FiniteSpecification d G)
    (Γ : Finset (PlaquettePolymer Λ)) (X : Finset (Plaquette d))
    (hcover : polymerFamilySupport Λ Γ = X) (q : activeSubset Λ X) :
    familyOwner Λ Γ X hcover q ∈ Γ :=
  (Classical.choose_spec (familyOwner_exists Λ Γ X hcover q)).1

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
private theorem familyOwner_contains (Λ : FiniteSpecification d G)
    (Γ : Finset (PlaquettePolymer Λ)) (X : Finset (Plaquette d))
    (hcover : polymerFamilySupport Λ Γ = X) (q : activeSubset Λ X) :
    q.1 ∈ (familyOwner Λ Γ X hcover q).1 :=
  (Classical.choose_spec (familyOwner_exists Λ Γ X hcover q)).2

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] in
/-- Along an induced adjacency edge, a compatible covering family has the
same owner on both endpoints. -/
private theorem familyOwner_eq_of_adj
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (Γ : Finset (PlaquettePolymer Λ)) (X : Finset (Plaquette d))
    (hΓ : (plaquettePolymerModel Λ Φ β).Compatible Γ)
    (hcover : polymerFamilySupport Λ Γ = X)
    {p q : activeSubset Λ X}
    (hpq : ((plaquetteAdjacencyGraph Λ).induce
      (activeSubset Λ X : Set (ActivePlaquette Λ))).Adj p q) :
    familyOwner Λ Γ X hcover p = familyOwner Λ Γ X hcover q := by
  by_contra hne
  apply hΓ (familyOwner_mem_family Λ Γ X hcover p)
    (familyOwner_mem_family Λ Γ X hcover q) hne
  exact ⟨p.1, familyOwner_contains Λ Γ X hcover p,
    q.1, familyOwner_contains Λ Γ X hcover q, Or.inr hpq⟩

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] in
private theorem familyOwner_eq_of_reachable
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (Γ : Finset (PlaquettePolymer Λ)) (X : Finset (Plaquette d))
    (hΓ : (plaquettePolymerModel Λ Φ β).Compatible Γ)
    (hcover : polymerFamilySupport Λ Γ = X)
    {p q : activeSubset Λ X}
    (hpq : ((plaquetteAdjacencyGraph Λ).induce
      (activeSubset Λ X : Set (ActivePlaquette Λ))).Reachable p q) :
    familyOwner Λ Γ X hcover p = familyOwner Λ Γ X hcover q :=
  Polymer.GraphComponents.label_eq_of_reachable _
    (familyOwner Λ Γ X hcover)
    (familyOwner_eq_of_adj Λ Φ β Γ X hΓ hcover) hpq

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
private theorem mem_activeSubset_of_mem_family
    (Λ : FiniteSpecification d G) (Γ : Finset (PlaquettePolymer Λ))
    (X : Finset (Plaquette d)) (hcover : polymerFamilySupport Λ Γ = X)
    {γ : PlaquettePolymer Λ} (hγ : γ ∈ Γ) {p : ActivePlaquette Λ}
    (hp : p ∈ γ.1) : p ∈ activeSubset Λ X := by
  classical
  have hpSupport : p.1 ∈ γ.support :=
    Finset.mem_map.mpr ⟨p, hp, rfl⟩
  have hpUnion : p.1 ∈ polymerFamilySupport Λ Γ :=
    Finset.mem_biUnion.mpr ⟨γ, hγ, hpSupport⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ p, hcover ▸ hpUnion⟩

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] in
private theorem familyOwner_eq_of_contains
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (Γ : Finset (PlaquettePolymer Λ)) (X : Finset (Plaquette d))
    (hΓ : (plaquettePolymerModel Λ Φ β).Compatible Γ)
    (hcover : polymerFamilySupport Λ Γ = X)
    {γ : PlaquettePolymer Λ} (hγ : γ ∈ Γ) (q : activeSubset Λ X)
    (hq : q.1 ∈ γ.1) : familyOwner Λ Γ X hcover q = γ := by
  by_contra hne
  apply hΓ (familyOwner_mem_family Λ Γ X hcover q) hγ hne
  exact ⟨q.1, familyOwner_contains Λ Γ X hcover q,
    q.1, hq, Or.inl rfl⟩

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] in
/-- Every induced graph component is exactly the owner polymer selected by a
compatible family that covers the subset. -/
private theorem componentPolymer_eq_familyOwner
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (Γ : Finset (PlaquettePolymer Λ)) (X : Finset (Plaquette d))
    (hΓ : (plaquettePolymerModel Λ Φ β).Compatible Γ)
    (hcover : polymerFamilySupport Λ Γ = X)
    (c : ((plaquetteAdjacencyGraph Λ).induce
      (activeSubset Λ X : Set (ActivePlaquette Λ))).ConnectedComponent) :
    componentPolymer Λ X c = familyOwner Λ Γ X hcover c.out := by
  apply Subtype.ext
  ext p
  constructor
  · intro hp
    have hpActive := Polymer.GraphComponents.componentFinset_subset
      (plaquetteAdjacencyGraph Λ) (activeSubset Λ X) c hp
    let q : activeSubset Λ X := ⟨p, hpActive⟩
    have hpComp : q ∈ c.supp := by
      rcases Finset.mem_map.mp hp with ⟨r, hr, hrp⟩
      have hrp' : r = q := by
        apply Subtype.ext
        exact hrp
      exact hrp' ▸ (Finset.mem_filter.mp hr).2
    have hreach : ((plaquetteAdjacencyGraph Λ).induce
        (activeSubset Λ X : Set (ActivePlaquette Λ))).Reachable c.out q :=
      c.reachable_of_mem_supp c.out_eq hpComp
    have howners := familyOwner_eq_of_reachable Λ Φ β Γ X hΓ hcover hreach
    have hcontains := familyOwner_contains Λ Γ X hcover q
    rw [howners]
    exact hcontains
  · intro hp
    let γ := familyOwner Λ Γ X hcover c.out
    have hγ : γ ∈ Γ := familyOwner_mem_family Λ Γ X hcover c.out
    have hpActive : p ∈ activeSubset Λ X :=
      mem_activeSubset_of_mem_family Λ Γ X hcover hγ hp
    let q : activeSubset Λ X := ⟨p, hpActive⟩
    let f : ((plaquetteAdjacencyGraph Λ).induce
        (γ.1 : Set (ActivePlaquette Λ))) →g
        ((plaquetteAdjacencyGraph Λ).induce
          (activeSubset Λ X : Set (ActivePlaquette Λ))) := {
      toFun r := ⟨r.1, mem_activeSubset_of_mem_family
        Λ Γ X hcover hγ r.2⟩
      map_rel' := fun h => h }
    have hrootγ : c.out.1 ∈ γ.1 :=
      familyOwner_contains Λ Γ X hcover c.out
    have hreachγ := γ.2.2.preconnected
      (⟨c.out.1, hrootγ⟩ : {r // r ∈ γ.1})
      (⟨p, hp⟩ : {r // r ∈ γ.1})
    have hreach := hreachγ.map f
    have hcomponent : ((plaquetteAdjacencyGraph Λ).induce
        (activeSubset Λ X : Set (ActivePlaquette Λ))).connectedComponentMk q = c :=
      (SimpleGraph.ConnectedComponent.sound hreach).symm.trans c.out_eq
    apply Finset.mem_map.mpr
    refine ⟨q, Finset.mem_filter.mpr ⟨by simp, hcomponent⟩, rfl⟩

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G] in
/-- A compatible family covering `X` is the canonical connected-component
family of `X`. -/
theorem compatibleFamily_eq_componentFamily
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (Γ : Finset (PlaquettePolymer Λ)) (X : Finset (Plaquette d))
    (hΓ : (plaquettePolymerModel Λ Φ β).Compatible Γ)
    (hcover : polymerFamilySupport Λ Γ = X) :
    Γ = componentFamily Λ X := by
  classical
  apply Finset.Subset.antisymm
  · intro γ hγ
    obtain ⟨p, hp⟩ := γ.2.1
    have hpActive : p ∈ activeSubset Λ X :=
      mem_activeSubset_of_mem_family Λ Γ X hcover hγ hp
    let q : activeSubset Λ X := ⟨p, hpActive⟩
    let c := ((plaquetteAdjacencyGraph Λ).induce
      (activeSubset Λ X : Set (ActivePlaquette Λ))).connectedComponentMk q
    have hqComp : q ∈ c.supp :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    have hreach := c.reachable_of_mem_supp c.out_eq hqComp
    have howners := familyOwner_eq_of_reachable Λ Φ β Γ X hΓ hcover hreach
    have hownerγ := familyOwner_eq_of_contains Λ Φ β Γ X hΓ hcover hγ q hp
    have hcomponent : componentPolymer Λ X c = γ :=
      (componentPolymer_eq_familyOwner Λ Φ β Γ X hΓ hcover c).trans
        (howners.trans hownerγ)
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, hcomponent⟩
  · intro γ hγ
    rcases Finset.mem_image.mp hγ with ⟨c, _, rfl⟩
    rw [componentPolymer_eq_familyOwner Λ Φ β Γ X hΓ hcover c]
    exact familyOwner_mem_family Λ Γ X hcover c.out

/-! ## Exact connected resummation interface -/

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
theorem polymerFamilySupport_subset_active (Λ : FiniteSpecification d G)
    (Γ : Finset (PlaquettePolymer Λ)) :
    polymerFamilySupport Λ Γ ⊆ Λ.activePlaquettes := by
  classical
  intro p hp
  simp only [polymerFamilySupport] at hp
  rcases Finset.mem_biUnion.mp hp with ⟨γ, _, hpγ⟩
  exact γ.support_subset_active hpγ

/-- Exact component-factorization statement.  It says that a subset weight is
the sum over compatible connected-component decompositions with that union.
For the plaquette adjacency graph the decomposition is unique; the sum form is
convenient for the finite resummation proof. -/
def HasExactComponentFactorization (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) : Prop := by
  classical
  exact ∀ X ∈ Λ.activePlaquettes.powerset,
      subsetWeight Λ Φ β X =
        ∑ Γ ∈ (plaquettePolymerModel Λ Φ β).compatibleFamilies Finset.univ with
          polymerFamilySupport Λ Γ = X,
          (plaquettePolymerModel Λ Φ β).familyWeight Γ

/-- The plaquette activities satisfy exact connected-component
factorization. -/
theorem hasExactComponentFactorization
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ) :
    HasExactComponentFactorization Λ Φ β := by
  classical
  intro X hX
  have hXsub := Finset.mem_powerset.mp hX
  rw [subsetWeight_eq_componentFamilyWeight Λ Φ β X hXsub]
  symm
  apply Finset.sum_eq_single (componentFamily Λ X)
  · intro Γ hΓ hne
    rcases Finset.mem_filter.mp hΓ with ⟨hΓcompatible, hcover⟩
    have hcompatible := (Finset.mem_filter.mp hΓcompatible).2
    exact (hne (compatibleFamily_eq_componentFamily
      Λ Φ β Γ X hcompatible hcover)).elim
  · intro hnot
    exact (hnot <| Finset.mem_filter.mpr ⟨
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
        componentFamily_compatible Λ Φ β X⟩,
      polymerFamilySupport_componentFamily_eq Λ X hXsub⟩).elim

/-- The exact plaquette subset expansion resums unconditionally to the
abstract hard-core polymer partition. -/
theorem complexPartitionFunction_eq_polymerPartition
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ) :
    complexPartitionFunction Λ Φ β =
      (plaquettePolymerModel Λ Φ β).partitionFunction := by
  classical
  have hfactor := hasExactComponentFactorization Λ Φ β
  rw [complexPartitionFunction_eq_sum_subsetWeight]
  unfold FinitePolymerModel.partitionFunction FinitePolymerModel.partitionOn
  let C := (plaquettePolymerModel Λ Φ β).compatibleFamilies Finset.univ
  let w := (plaquettePolymerModel Λ Φ β).familyWeight
  change (∑ X ∈ Λ.activePlaquettes.powerset, subsetWeight Λ Φ β X) =
    ∑ Γ ∈ C, w Γ
  calc
    _ = ∑ X ∈ Λ.activePlaquettes.powerset,
        ∑ Γ ∈ C with polymerFamilySupport Λ Γ = X, w Γ := by
      apply Finset.sum_congr rfl
      intro X hX
      exact hfactor X hX
    _ = ∑ Γ ∈ C, w Γ := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro Γ _
      rw [Finset.sum_eq_single (polymerFamilySupport Λ Γ)]
      · simp
      · intro X _ hne
        simp [hne.symm]
      · intro hnot
        exfalso
        exact hnot (Finset.mem_powerset.mpr (polymerFamilySupport_subset_active Λ Γ))

end

end YangMills.StrongCoupling
