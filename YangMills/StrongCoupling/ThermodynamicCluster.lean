/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.Counting
import YangMills.Polymer.CountableMayer
import YangMills.Polymer.MayerEvaluation
import YangMills.Polymer.Relabel
import Mathlib.Order.PiLex
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Translation-stable plaquette polymers

Finite-volume plaquette-polymer types depend on a specification.  Pressure
instead needs one stable countable index on the full cubic lattice.  This file
defines that index, its canonical finite Haar activity, and its translation
action.  These are the geometric objects used by the anchored cluster series.
-/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Polymer
open MeasureTheory

noncomputable section

local instance {d : ℕ} : DecidableEq (Plaquette d) := Classical.decEq _

/-- Full-lattice plaquette adjacency: two distinct plaquettes share a stored
positive boundary edge. -/
def fullPlaquetteAdjacencyGraph (d : ℕ) : SimpleGraph (Plaquette d) where
  Adj p q := p ≠ q ∧ ¬Disjoint p.boundary.edgeSupport q.boundary.edgeSupport
  symm _ _ h := ⟨h.1.symm, fun hd ↦ h.2 hd.symm⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

instance (d : ℕ) : DecidableRel (fullPlaquetteAdjacencyGraph d).Adj :=
  Classical.decRel _

/-- A finite nonempty connected plaquette set in the full cubic lattice. -/
def InfinitePlaquettePolymer (d : ℕ) :=
  {γ : Finset (Plaquette d) //
    γ.Nonempty ∧ ((fullPlaquetteAdjacencyGraph d).induce
      (γ : Set (Plaquette d))).Connected}

instance (d : ℕ) : DecidableEq (InfinitePlaquettePolymer d) := Classical.decEq _
instance (d : ℕ) : Countable (InfinitePlaquettePolymer d) :=
  Subtype.val_injective.countable

namespace InfinitePlaquettePolymer

variable {d : ℕ}

/-- The underlying finite plaquette support. -/
def support (γ : InfinitePlaquettePolymer d) : Finset (Plaquette d) := γ.1

/-- The global one-plaquette polymer. -/
def singleton (p : Plaquette d) : InfinitePlaquettePolymer d :=
  ⟨{p}, Finset.singleton_nonempty p, by
    letI : Nonempty {q // q ∈ ({p} : Finset (Plaquette d))} :=
      ⟨⟨p, Finset.mem_singleton_self p⟩⟩
    letI : Subsingleton {q // q ∈ ({p} : Finset (Plaquette d))} :=
      ⟨fun q r ↦ Subtype.ext <|
        (Finset.mem_singleton.mp q.2).trans (Finset.mem_singleton.mp r.2).symm⟩
    exact SimpleGraph.Connected.of_subsingleton⟩

@[simp]
theorem support_singleton (p : Plaquette d) : (singleton p).support = {p} := rfl

@[simp]
theorem card_support_singleton (p : Plaquette d) : (singleton p).support.card = 1 := by
  simp

@[simp]
theorem support_nonempty (γ : InfinitePlaquettePolymer d) : γ.support.Nonempty := γ.2.1

@[simp]
theorem fullPlaquetteAdjacency_translate_iff
    (v : Site d) (p q : Plaquette d) :
    (fullPlaquetteAdjacencyGraph d).Adj (p.translate v) (q.translate v) ↔
      (fullPlaquetteAdjacencyGraph d).Adj p q := by
  change (p.translate v ≠ q.translate v ∧
      ¬Disjoint (p.translate v).boundary.edgeSupport
        (q.translate v).boundary.edgeSupport) ↔
    (p ≠ q ∧ ¬Disjoint p.boundary.edgeSupport q.boundary.edgeSupport)
  have hne : p.translate v ≠ q.translate v ↔ p ≠ q :=
    (Plaquette.translationEquiv v).injective.ne_iff
  rw [hne, plaquette_boundary_edgeSupport_translate,
    plaquette_boundary_edgeSupport_translate, Finset.disjoint_map]

/-- Translate a full-lattice polymer. -/
def translate (v : Site d) (γ : InfinitePlaquettePolymer d) :
    InfinitePlaquettePolymer d := by
  let e := Plaquette.translationEquiv v
  let support' := γ.support.map e.toEmbedding
  refine ⟨support', γ.support_nonempty.map, ?_⟩
  let se : {p // p ∈ γ.support} ≃ {p // p ∈ support'} :=
    Equiv.subtypeEquiv e (fun p ↦ by
      change p ∈ γ.support ↔ e p ∈ γ.support.map e.toEmbedding
      rw [Finset.mem_map_equiv]
      rw [e.symm_apply_apply])
  let graphIso :
      (fullPlaquetteAdjacencyGraph d).induce (γ.support : Set (Plaquette d)) ≃g
        (fullPlaquetteAdjacencyGraph d).induce (support' : Set (Plaquette d)) :=
    ⟨se, fun {p q} ↦ by
      change (fullPlaquetteAdjacencyGraph d).Adj
          (p.1.translate v) (q.1.translate v) ↔
        (fullPlaquetteAdjacencyGraph d).Adj p.1 q.1
      exact fullPlaquetteAdjacency_translate_iff v p.1 q.1⟩
  exact graphIso.connected_iff.mp γ.2.2

@[simp]
theorem support_translate (v : Site d) (γ : InfinitePlaquettePolymer d) :
    (γ.translate v).support =
      γ.support.map (Plaquette.translationEquiv v).toEmbedding := rfl

@[simp]
theorem translate_zero (γ : InfinitePlaquettePolymer d) : γ.translate 0 = γ := by
  apply Subtype.ext
  ext p
  change p ∈ γ.support.map (Plaquette.translationEquiv 0).toEmbedding ↔
    p ∈ γ.support
  rw [Finset.mem_map_equiv]
  change p.translate (-0) ∈ γ.support ↔ p ∈ γ.support
  simp

@[simp]
theorem translate_translate (v w : Site d) (γ : InfinitePlaquettePolymer d) :
    (γ.translate v).translate w = γ.translate (v + w) := by
  apply Subtype.ext
  ext p
  change p ∈
      (γ.support.map (Plaquette.translationEquiv v).toEmbedding).map
        (Plaquette.translationEquiv w).toEmbedding ↔
    p ∈ γ.support.map (Plaquette.translationEquiv (v + w)).toEmbedding
  rw [Finset.mem_map_equiv, Finset.mem_map_equiv, Finset.mem_map_equiv]
  change (p.translate (-w)).translate (-v) ∈ γ.support ↔
    p.translate (-(v + w)) ∈ γ.support
  rw [Plaquette.translate_translate]
  abel

/-- Translation is a bijection of full-lattice plaquette polymers. -/
def translationEquiv (v : Site d) :
    InfinitePlaquettePolymer d ≃ InfinitePlaquettePolymer d where
  toFun := translate v
  invFun := translate (-v)
  left_inv γ := by simp
  right_inv γ := by simp

/-- All positive edges read by the polymer. -/
def edgeSupport (γ : InfinitePlaquettePolymer d) : Finset (PositiveEdge d) :=
  γ.support.biUnion fun p ↦ p.boundary.edgeSupport

@[simp]
theorem edgeSupport_translate (v : Site d) (γ : InfinitePlaquettePolymer d) :
    (γ.translate v).edgeSupport =
      γ.edgeSupport.map (PositiveEdge.translationEquiv v).toEmbedding := by
  ext e
  rw [Finset.mem_map_equiv]
  simp only [edgeSupport, support_translate, Finset.mem_biUnion]
  constructor
  · rintro ⟨q, hq, he⟩
    rw [Finset.mem_map_equiv] at hq
    refine ⟨q.translate (-v), hq, ?_⟩
    rw [plaquette_boundary_edgeSupport_translate (-v) q,
      Finset.mem_map_equiv]
    simpa [PositiveEdge.translationEquiv] using he
  · rintro ⟨p, hp, he⟩
    refine ⟨p.translate v, ?_, ?_⟩
    · rw [Finset.mem_map_equiv]
      change (p.translate v).translate (-v) ∈ γ.support
      simpa using hp
    · rw [plaquette_boundary_edgeSupport_translate, Finset.mem_map_equiv]
      simpa using he

theorem boundary_subset_edgeSupport (γ : InfinitePlaquettePolymer d)
    {p : Plaquette d} (hp : p ∈ γ.support) :
    p.boundary.edgeSupport ⊆ γ.edgeSupport := by
  intro e he
  exact Finset.mem_biUnion.mpr ⟨p, hp, he⟩

/-- Canonical free-boundary finite specification carrying exactly one global
polymer.  Every edge read by its plaquettes is dynamic, so its activity has no
frozen-boundary dependence. -/
def supportSpecification {G : Type*} [Group G]
    (γ : InfinitePlaquettePolymer d) : FiniteSpecification d G where
  dynamicEdges := γ.edgeSupport
  activePlaquettes := γ.support
  exterior := fun _ ↦ 1

@[simp]
theorem supportSpecification_dynamicEdges {G : Type*} [Group G]
    (γ : InfinitePlaquettePolymer d) :
    (γ.supportSpecification (G := G)).dynamicEdges = γ.edgeSupport := rfl

@[simp]
theorem supportSpecification_activePlaquettes {G : Type*} [Group G]
    (γ : InfinitePlaquettePolymer d) :
    (γ.supportSpecification (G := G)).activePlaquettes = γ.support := rfl

@[simp]
theorem supportSpecification_translate {G : Type*} [Group G]
    (v : Site d) (γ : InfinitePlaquettePolymer d) :
    (γ.supportSpecification (G := G)).translate v =
      (γ.translate v).supportSpecification := by
  cases γ with
  | mk support hsupport =>
      simp only [supportSpecification, FiniteSpecification.translate,
        edgeSupport_translate]
      congr 1

/-- One finite specification carrying an arbitrary finite family of global
polymers.  All boundary edges of all active plaquettes are dynamic. -/
def finiteFamilySpecification {G : Type*} [Group G]
    (S : Finset (InfinitePlaquettePolymer d)) : FiniteSpecification d G where
  activePlaquettes := S.biUnion support
  dynamicEdges := (S.biUnion support).biUnion fun p ↦ p.boundary.edgeSupport
  exterior := fun _ ↦ 1

@[simp]
theorem finiteFamilySpecification_activePlaquettes {G : Type*} [Group G]
    (S : Finset (InfinitePlaquettePolymer d)) :
    (finiteFamilySpecification (G := G) S).activePlaquettes =
      S.biUnion support := rfl

@[simp]
theorem finiteFamilySpecification_dynamicEdges {G : Type*} [Group G]
    (S : Finset (InfinitePlaquettePolymer d)) :
    (finiteFamilySpecification (G := G) S).dynamicEdges =
      (S.biUnion support).biUnion fun p ↦ p.boundary.edgeSupport := rfl

theorem support_subset_finiteFamilySpecification {G : Type*} [Group G]
    (S : Finset (InfinitePlaquettePolymer d)) (gamma : S) :
    gamma.1.support ⊆
      (finiteFamilySpecification (G := G) S).activePlaquettes := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨gamma.1, gamma.2, hp⟩

theorem plaquetteDynamicSupport_finiteFamilySpecification
    {G : Type*} [Group G] (S : Finset (InfinitePlaquettePolymer d))
    (p : ActivePlaquette (finiteFamilySpecification (G := G) S)) :
    plaquetteDynamicSupport (finiteFamilySpecification (G := G) S) p.1 =
      p.1.boundary.edgeSupport := by
  unfold plaquetteDynamicSupport
  ext e
  constructor
  · exact fun he ↦ (Finset.mem_filter.mp he).2
  · intro he
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨p.1, p.2, he⟩, he⟩

@[simp]
theorem plaquetteAdjacency_finiteFamilySpecification_iff
    {G : Type*} [Group G] (S : Finset (InfinitePlaquettePolymer d))
    (p q : ActivePlaquette (finiteFamilySpecification (G := G) S)) :
    (plaquetteAdjacencyGraph (finiteFamilySpecification (G := G) S)).Adj p q ↔
      (fullPlaquetteAdjacencyGraph d).Adj p.1 q.1 := by
  change (p ≠ q ∧
      ¬Disjoint
        (plaquetteDynamicSupport (finiteFamilySpecification (G := G) S) p.1)
        (plaquetteDynamicSupport (finiteFamilySpecification (G := G) S) q.1)) ↔
    (p.1 ≠ q.1 ∧
      ¬Disjoint p.1.boundary.edgeSupport q.1.boundary.edgeSupport)
  rw [plaquetteDynamicSupport_finiteFamilySpecification,
    plaquetteDynamicSupport_finiteFamilySpecification,
    Subtype.val_injective.ne_iff]

/-- Realize a member of a finite global-polymer family as a polymer in the
finite specification carrying the whole family. -/
def toFiniteFamilyPolymer {G : Type*} [Group G]
    (S : Finset (InfinitePlaquettePolymer d)) (gamma : S) :
    PlaquettePolymer (finiteFamilySpecification (G := G) S) := by
  let Lambda := finiteFamilySpecification (G := G) S
  let A := activeSubset Lambda gamma.1.support
  refine ⟨A, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := gamma.1.support_nonempty
    let q : ActivePlaquette Lambda :=
      ⟨p, support_subset_finiteFamilySpecification S gamma hp⟩
    exact ⟨q, by simp [A, activeSubset, q, hp]⟩
  · let f :
        ((fullPlaquetteAdjacencyGraph d).induce
          (gamma.1.support : Set (Plaquette d))) →g
        ((plaquetteAdjacencyGraph Lambda).induce
          (A : Set (ActivePlaquette Lambda))) := {
      toFun := fun p ↦
        ⟨⟨p.1, support_subset_finiteFamilySpecification S gamma p.2⟩,
          by simp [A, activeSubset]⟩
      map_rel' := by
        intro p q hpq
        exact (plaquetteAdjacency_finiteFamilySpecification_iff S _ _).mpr hpq
      }
    apply gamma.1.2.2.map f
    rintro ⟨q, hq⟩
    have hqsupport : q.1 ∈ gamma.1.support := by
      simpa [A, activeSubset] using hq
    exact ⟨⟨q.1, hqsupport⟩, rfl⟩

@[simp]
theorem support_toFiniteFamilyPolymer {G : Type*} [Group G]
    (S : Finset (InfinitePlaquettePolymer d)) (gamma : S) :
    (toFiniteFamilyPolymer (G := G) S gamma).support = gamma.1.support := by
  exact activeSubset_map_val_eq _ _
    (support_subset_finiteFamilySpecification S gamma)

theorem toFiniteFamilyPolymer_injective {G : Type*} [Group G]
    (S : Finset (InfinitePlaquettePolymer d)) :
    Function.Injective (toFiniteFamilyPolymer (G := G) S) := by
  intro gamma delta h
  apply Subtype.ext
  apply Subtype.ext
  simpa using congrArg PlaquettePolymer.support h

/-! ## Exact free finite regions -/

/-- Free-boundary specification whose active plaquettes are exactly `A` and
whose dynamic variables contain every stored edge read by `A`. -/
def freeRegionSpecification {G : Type*} [Group G]
    (A : Finset (Plaquette d)) : FiniteSpecification d G where
  activePlaquettes := A
  dynamicEdges := A.biUnion fun p ↦ p.boundary.edgeSupport
  exterior := fun _ ↦ 1

@[simp]
theorem freeRegionSpecification_activePlaquettes {G : Type*} [Group G]
    (A : Finset (Plaquette d)) :
    (freeRegionSpecification (G := G) A).activePlaquettes = A := rfl

@[simp]
theorem freeRegionSpecification_dynamicEdges {G : Type*} [Group G]
    (A : Finset (Plaquette d)) :
    (freeRegionSpecification (G := G) A).dynamicEdges =
      A.biUnion fun p ↦ p.boundary.edgeSupport := rfl

theorem plaquetteDynamicSupport_freeRegionSpecification
    {G : Type*} [Group G] (A : Finset (Plaquette d))
    (p : ActivePlaquette (freeRegionSpecification (G := G) A)) :
    plaquetteDynamicSupport (freeRegionSpecification (G := G) A) p.1 =
      p.1.boundary.edgeSupport := by
  unfold plaquetteDynamicSupport
  ext e
  constructor
  · exact fun he ↦ (Finset.mem_filter.mp he).2
  · intro he
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨p.1, p.2, he⟩, he⟩

@[simp]
theorem plaquetteAdjacency_freeRegionSpecification_iff
    {G : Type*} [Group G] (A : Finset (Plaquette d))
    (p q : ActivePlaquette (freeRegionSpecification (G := G) A)) :
    (plaquetteAdjacencyGraph (freeRegionSpecification (G := G) A)).Adj p q ↔
      (fullPlaquetteAdjacencyGraph d).Adj p.1 q.1 := by
  change (p ≠ q ∧
      ¬Disjoint
        (plaquetteDynamicSupport (freeRegionSpecification (G := G) A) p.1)
        (plaquetteDynamicSupport (freeRegionSpecification (G := G) A) q.1)) ↔
    (p.1 ≠ q.1 ∧
      ¬Disjoint p.1.boundary.edgeSupport q.1.boundary.edgeSupport)
  rw [plaquetteDynamicSupport_freeRegionSpecification,
    plaquetteDynamicSupport_freeRegionSpecification,
    Subtype.val_injective.ne_iff]

/-- Forget the active-plaquette subtype of a free-region polymer. -/
def ofFreeRegionPolymer {G : Type*} [Group G]
    (A : Finset (Plaquette d))
    (γ : PlaquettePolymer (freeRegionSpecification (G := G) A)) :
    InfinitePlaquettePolymer d := by
  refine ⟨γ.support, γ.support_nonempty, ?_⟩
  let f :
      ((plaquetteAdjacencyGraph (freeRegionSpecification (G := G) A)).induce
        (γ.1 : Set (ActivePlaquette (freeRegionSpecification (G := G) A)))) →g
      ((fullPlaquetteAdjacencyGraph d).induce
        (γ.support : Set (Plaquette d))) := {
    toFun := fun p ↦ ⟨p.1.1, by
      exact Finset.mem_map.mpr ⟨p.1, p.2, rfl⟩⟩
    map_rel' := by
      intro p q hpq
      exact (plaquetteAdjacency_freeRegionSpecification_iff A p.1 q.1).mp hpq
    }
  apply γ.2.2.map f
  rintro ⟨p, hp⟩
  rcases Finset.mem_map.mp hp with ⟨q, hq, rfl⟩
  exact ⟨⟨q, hq⟩, rfl⟩

@[simp]
theorem support_ofFreeRegionPolymer {G : Type*} [Group G]
    (A : Finset (Plaquette d))
    (γ : PlaquettePolymer (freeRegionSpecification (G := G) A)) :
    (ofFreeRegionPolymer A γ).support = γ.support := rfl

theorem ofFreeRegionPolymer_injective {G : Type*} [Group G]
    (A : Finset (Plaquette d)) :
    Function.Injective (ofFreeRegionPolymer (G := G) A) := by
  intro γ δ h
  apply PlaquettePolymer.support_injective
  exact congrArg support h

/-- Regard a global polymer whose support lies in `A` as a polymer of the
free-region specification on `A`. -/
def toFreeRegionPolymer {G : Type*} [Group G]
    (A : Finset (Plaquette d)) (γ : InfinitePlaquettePolymer d)
    (hγ : γ.support ⊆ A) :
    PlaquettePolymer (freeRegionSpecification (G := G) A) := by
  let Λ := freeRegionSpecification (G := G) A
  let B := activeSubset Λ γ.support
  refine ⟨B, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := γ.support_nonempty
    let q : ActivePlaquette Λ := ⟨p, hγ hp⟩
    exact ⟨q, by simp [B, activeSubset, q, hp]⟩
  · let f :
        ((fullPlaquetteAdjacencyGraph d).induce
          (γ.support : Set (Plaquette d))) →g
        ((plaquetteAdjacencyGraph Λ).induce
      (B : Set (ActivePlaquette Λ))) := {
      toFun := fun p ↦ ⟨⟨p.1, hγ p.2⟩,
        by simp [B, activeSubset]⟩
      map_rel' := by
        intro p q hpq
        exact (plaquetteAdjacency_freeRegionSpecification_iff A _ _).mpr hpq
      }
    apply γ.2.2.map f
    rintro ⟨q, hq⟩
    have hqsupport : q.1 ∈ γ.support := by
      simpa [B, activeSubset] using hq
    exact ⟨⟨q.1, hqsupport⟩, rfl⟩

@[simp]
theorem support_toFreeRegionPolymer {G : Type*} [Group G]
    (A : Finset (Plaquette d)) (γ : InfinitePlaquettePolymer d)
    (hγ : γ.support ⊆ A) :
    (toFreeRegionPolymer (G := G) A γ hγ).support = γ.support := by
  exact activeSubset_map_val_eq _ _ hγ

/-- The finite set of all global polymers carried by `A`. -/
def freeRegionGlobalPolymers {G : Type*} [Group G]
    (A : Finset (Plaquette d)) : Finset (InfinitePlaquettePolymer d) :=
  (Finset.univ : Finset
    (PlaquettePolymer (freeRegionSpecification (G := G) A))).image
      (ofFreeRegionPolymer A)

theorem support_subset_of_mem_freeRegionGlobalPolymers
    {G : Type*} [Group G] (A : Finset (Plaquette d))
    {γ : InfinitePlaquettePolymer d}
    (hγ : γ ∈ freeRegionGlobalPolymers (G := G) A) :
    γ.support ⊆ A := by
  rcases Finset.mem_image.mp hγ with ⟨δ, _, rfl⟩
  rw [support_ofFreeRegionPolymer]
  exact δ.support_subset_active

@[simp]
theorem mem_freeRegionGlobalPolymers_iff_support_subset
    {G : Type*} [Group G] (A : Finset (Plaquette d))
    (γ : InfinitePlaquettePolymer d) :
    γ ∈ freeRegionGlobalPolymers (G := G) A ↔ γ.support ⊆ A := by
  constructor
  · exact support_subset_of_mem_freeRegionGlobalPolymers A
  · intro hγ
    apply Finset.mem_image.mpr
    refine ⟨toFreeRegionPolymer A γ hγ, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact support_toFreeRegionPolymer (G := G) A γ hγ

/-- Exact equivalence between finite-region polymers and the corresponding
finite subtype of the stable global polymer species. -/
def freeRegionPolymerEquiv {G : Type*} [Group G]
    (A : Finset (Plaquette d)) :
    PlaquettePolymer (freeRegionSpecification (G := G) A) ≃
      freeRegionGlobalPolymers (G := G) A :=
  Equiv.ofBijective
    (fun γ ↦ ⟨ofFreeRegionPolymer A γ,
      Finset.mem_image.mpr ⟨γ, Finset.mem_univ γ, rfl⟩⟩)
    ⟨fun _ _ h ↦ ofFreeRegionPolymer_injective A (congrArg Subtype.val h),
      fun δ ↦ by
        rcases Finset.mem_image.mp δ.2 with ⟨γ, _, hγ⟩
        exact ⟨γ, Subtype.ext hγ⟩⟩

end InfinitePlaquettePolymer

variable {d : ℕ}

/-- Two full-lattice polymers are incompatible when some plaquettes overlap
or share a stored positive boundary edge. -/
def infinitePlaquettePolymerIncompatible
    (γ δ : InfinitePlaquettePolymer d) : Prop :=
  ∃ p ∈ γ.support, ∃ q ∈ δ.support,
    p = q ∨ (fullPlaquetteAdjacencyGraph d).Adj p q

@[simp]
theorem InfinitePlaquettePolymer.incompatible_toFiniteFamilyPolymer_iff
    {G : Type*} [Group G] (S : Finset (InfinitePlaquettePolymer d))
    (gamma delta : S) :
    plaquettePolymerIncompatible
        (InfinitePlaquettePolymer.finiteFamilySpecification (G := G) S)
        (InfinitePlaquettePolymer.toFiniteFamilyPolymer S gamma)
        (InfinitePlaquettePolymer.toFiniteFamilyPolymer S delta) ↔
      infinitePlaquettePolymerIncompatible gamma.1 delta.1 := by
  constructor
  · rintro ⟨p, hp, q, hq, hpq⟩
    have hp' : p.1 ∈ gamma.1.support := by
      simpa [InfinitePlaquettePolymer.toFiniteFamilyPolymer, activeSubset]
        using hp
    have hq' : q.1 ∈ delta.1.support := by
      simpa [InfinitePlaquettePolymer.toFiniteFamilyPolymer, activeSubset]
        using hq
    refine ⟨p.1, hp', q.1, hq', ?_⟩
    exact hpq.imp (fun h ↦ congrArg Subtype.val h) (fun h ↦
      (InfinitePlaquettePolymer.plaquetteAdjacency_finiteFamilySpecification_iff
        S p q).mp h)
  · rintro ⟨p, hp, q, hq, hpq⟩
    let p' : ActivePlaquette
        (InfinitePlaquettePolymer.finiteFamilySpecification (G := G) S) :=
      ⟨p, InfinitePlaquettePolymer.support_subset_finiteFamilySpecification
        S gamma hp⟩
    let q' : ActivePlaquette
        (InfinitePlaquettePolymer.finiteFamilySpecification (G := G) S) :=
      ⟨q, InfinitePlaquettePolymer.support_subset_finiteFamilySpecification
        S delta hq⟩
    refine ⟨p', ?_, q', ?_, ?_⟩
    · simpa [InfinitePlaquettePolymer.toFiniteFamilyPolymer,
        activeSubset, p'] using hp
    · simpa [InfinitePlaquettePolymer.toFiniteFamilyPolymer,
        activeSubset, q'] using hq
    · exact hpq.imp (fun h ↦ Subtype.ext h)
        (fun h ↦
          (InfinitePlaquettePolymer.plaquetteAdjacency_finiteFamilySpecification_iff
            S p' q').mpr h)

@[simp]
theorem InfinitePlaquettePolymer.incompatible_ofFreeRegionPolymer_iff
    {G : Type*} [Group G] (A : Finset (Plaquette d))
    (γ δ : PlaquettePolymer
      (InfinitePlaquettePolymer.freeRegionSpecification (G := G) A)) :
    infinitePlaquettePolymerIncompatible
        (InfinitePlaquettePolymer.ofFreeRegionPolymer A γ)
        (InfinitePlaquettePolymer.ofFreeRegionPolymer A δ) ↔
      plaquettePolymerIncompatible
        (InfinitePlaquettePolymer.freeRegionSpecification (G := G) A) γ δ := by
  constructor
  · rintro ⟨p, hp, q, hq, hpq⟩
    rcases Finset.mem_map.mp hp with ⟨p', hp', rfl⟩
    rcases Finset.mem_map.mp hq with ⟨q', hq', rfl⟩
    refine ⟨p', hp', q', hq', ?_⟩
    exact hpq.imp (fun h ↦ Subtype.ext h)
      (fun h ↦
        (InfinitePlaquettePolymer.plaquetteAdjacency_freeRegionSpecification_iff
          A p' q').mpr h)
  · rintro ⟨p, hp, q, hq, hpq⟩
    refine ⟨p.1, ?_, q.1, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨p, hp, rfl⟩
    · exact Finset.mem_map.mpr ⟨q, hq, rfl⟩
    · exact hpq.imp (congrArg Subtype.val)
        (fun h ↦
          (InfinitePlaquettePolymer.plaquetteAdjacency_freeRegionSpecification_iff
            A p q).mp h)

instance : DecidableRel
    (infinitePlaquettePolymerIncompatible (d := d)) := Classical.decRel _

theorem infinitePlaquettePolymerIncompatible_symmetric :
    Symmetric (infinitePlaquettePolymerIncompatible (d := d)) := by
  rintro γ δ ⟨p, hp, q, hq, hpq⟩
  exact ⟨q, hq, p, hp, hpq.elim (fun h ↦ Or.inl h.symm)
    (fun h ↦ Or.inr ((fullPlaquetteAdjacencyGraph d).symm h))⟩

theorem infinitePlaquettePolymerIncompatible_self
    (γ : InfinitePlaquettePolymer d) :
    infinitePlaquettePolymerIncompatible γ γ := by
  obtain ⟨p, hp⟩ := γ.support_nonempty
  exact ⟨p, hp, p, hp, Or.inl rfl⟩

theorem singleton_incompatible_of_mem (p : Plaquette d)
    (γ : InfinitePlaquettePolymer d) (hp : p ∈ γ.support) :
    infinitePlaquettePolymerIncompatible (InfinitePlaquettePolymer.singleton p) γ :=
  ⟨p, by simp, p, hp, Or.inl rfl⟩

@[simp]
theorem infinitePlaquettePolymerIncompatible_translate_iff
    (v : Site d) (γ δ : InfinitePlaquettePolymer d) :
    infinitePlaquettePolymerIncompatible (γ.translate v) (δ.translate v) ↔
      infinitePlaquettePolymerIncompatible γ δ := by
  constructor
  · rintro ⟨p, hp, q, hq, hpq⟩
    rw [InfinitePlaquettePolymer.support_translate,
      Finset.mem_map_equiv] at hp hq
    refine ⟨p.translate (-v), hp, q.translate (-v), hq, ?_⟩
    rcases hpq with hpq | hpq
    · exact Or.inl (congrArg (Plaquette.translate (-v)) hpq)
    · exact Or.inr ((InfinitePlaquettePolymer.fullPlaquetteAdjacency_translate_iff
        v (p.translate (-v)) (q.translate (-v))).mp (by simpa using hpq))
  · rintro ⟨p, hp, q, hq, hpq⟩
    refine ⟨p.translate v, ?_, q.translate v, ?_, ?_⟩
    · rw [InfinitePlaquettePolymer.support_translate, Finset.mem_map_equiv]
      change (p.translate v).translate (-v) ∈ γ.support
      simpa using hp
    · rw [InfinitePlaquettePolymer.support_translate, Finset.mem_map_equiv]
      change (q.translate v).translate (-v) ∈ δ.support
      simpa using hq
    · exact hpq.imp (congrArg (Plaquette.translate v))
        ((InfinitePlaquettePolymer.fullPlaquetteAdjacency_translate_iff
          v p q).mpr)

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- Translation-stable infinite-lattice polymer activity, computed by a
finite product-Haar integral on the polymer's exact edge support. -/
def infinitePlaquetteActivity (Φ : RealPlaquettePotential G) (β : ℂ)
    (γ : InfinitePlaquettePolymer d) : ℂ :=
  subsetWeight (γ.supportSpecification (G := G)) Φ β γ.support

theorem InfinitePlaquettePolymer.supportSpecification_dynamic_subset_family
    (S : Finset (InfinitePlaquettePolymer d)) (γ : S) :
    (γ.1.supportSpecification (G := G)).dynamicEdges ⊆
      (finiteFamilySpecification (G := G) S).dynamicEdges := by
  intro e he
  rcases Finset.mem_biUnion.mp he with ⟨p, hp, he⟩
  exact Finset.mem_biUnion.mpr
    ⟨p, Finset.mem_biUnion.mpr ⟨γ.1, γ.2, hp⟩, he⟩

/-- A global polymer activity is unchanged when its exact support
specification is enlarged to the common finite specification carrying a
finite family. -/
theorem subsetWeight_finiteFamilySpecification_eq_infinitePlaquetteActivity
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (S : Finset (InfinitePlaquettePolymer d)) (γ : S) :
    subsetWeight (InfinitePlaquettePolymer.finiteFamilySpecification
        (G := G) S) Φ β γ.1.support =
      infinitePlaquetteActivity Φ β γ.1 := by
  let small := γ.1.supportSpecification (G := G)
  let large := InfinitePlaquettePolymer.finiteFamilySpecification (G := G) S
  have hsub : small.dynamicEdges ⊆ large.dynamicEdges :=
    InfinitePlaquettePolymer.supportSpecification_dynamic_subset_family S γ
  let R : DynamicConfiguration large → DynamicConfiguration small :=
    Gauge.ProductHaar.restrictOfFinsetSubset (G := G) hsub
  have hintegrand : ∀ U : DynamicConfiguration large,
      subsetIntegrand large Φ β γ.1.support U =
        subsetIntegrand small Φ β γ.1.support (R U) := by
    intro U
    unfold subsetIntegrand
    apply Finset.prod_congr rfl
    intro p hp
    unfold plaquettePerturbation plaquetteHolonomy
    have hhol : Gauge.holonomy (large.evaluate U) p.boundary =
        Gauge.holonomy (small.evaluate (R U)) p.boundary := by
      apply Gauge.holonomy_eq_of_eqOn_edgeSupport
      intro e he
      have hesmall : e ∈ small.dynamicEdges :=
        Finset.mem_biUnion.mpr ⟨p, hp, he⟩
      have helarge : e ∈ large.dynamicEdges := hsub hesmall
      rw [small.evaluate_of_mem (R U) e hesmall,
        large.evaluate_of_mem U e helarge]
      rfl
    rw [hhol]
  unfold subsetWeight infinitePlaquetteActivity
  rw [show γ.1.supportSpecification (G := G) = small from rfl,
    show InfinitePlaquettePolymer.finiteFamilySpecification (G := G) S =
      large from rfl]
  calc
    (∫ U, subsetIntegrand large Φ β γ.1.support U ∂large.haarMeasure) =
        ∫ U, subsetIntegrand small Φ β γ.1.support (R U)
          ∂large.haarMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hintegrand
    _ = ∫ V, subsetIntegrand small Φ β γ.1.support V
          ∂small.haarMeasure := by
      exact Gauge.ProductHaar.integral_restrictOfFinsetSubset
        (G := G) hsub (subsetIntegrand small Φ β γ.1.support)
        (continuous_subsetIntegrand small Φ β γ.1.support).measurable

/-- The activity of a free-region polymer is its stable global activity.
Every edge read by the polymer is dynamic in the free-region specification,
so extra variables integrate out by normalized product Haar. -/
theorem subsetWeight_freeRegionSpecification_eq_infinitePlaquetteActivity
    (Φ : RealPlaquettePotential G) (β : ℂ) (A : Finset (Plaquette d))
    (γ : PlaquettePolymer
      (InfinitePlaquettePolymer.freeRegionSpecification (G := G) A)) :
    subsetWeight (InfinitePlaquettePolymer.freeRegionSpecification
        (G := G) A) Φ β γ.support =
      infinitePlaquetteActivity Φ β
        (InfinitePlaquettePolymer.ofFreeRegionPolymer A γ) := by
  let global := InfinitePlaquettePolymer.ofFreeRegionPolymer A γ
  let small := global.supportSpecification (G := G)
  let large := InfinitePlaquettePolymer.freeRegionSpecification (G := G) A
  have hsub : small.dynamicEdges ⊆ large.dynamicEdges := by
    intro e he
    rcases Finset.mem_biUnion.mp he with ⟨p, hp, he⟩
    exact Finset.mem_biUnion.mpr
      ⟨p, γ.support_subset_active (by simpa [global] using hp), he⟩
  let R : DynamicConfiguration large → DynamicConfiguration small :=
    Gauge.ProductHaar.restrictOfFinsetSubset (G := G) hsub
  have hintegrand : ∀ U : DynamicConfiguration large,
      subsetIntegrand large Φ β γ.support U =
        subsetIntegrand small Φ β γ.support (R U) := by
    intro U
    unfold subsetIntegrand
    apply Finset.prod_congr rfl
    intro p hp
    unfold plaquettePerturbation plaquetteHolonomy
    have hhol : Gauge.holonomy (large.evaluate U) p.boundary =
        Gauge.holonomy (small.evaluate (R U)) p.boundary := by
      apply Gauge.holonomy_eq_of_eqOn_edgeSupport
      intro e he
      have hesmall : e ∈ small.dynamicEdges :=
        Finset.mem_biUnion.mpr ⟨p, by simpa [small, global] using hp, he⟩
      have helarge : e ∈ large.dynamicEdges := hsub hesmall
      rw [small.evaluate_of_mem (R U) e hesmall,
        large.evaluate_of_mem U e helarge]
      rfl
    rw [hhol]
  change (∫ U, subsetIntegrand large Φ β γ.support U ∂large.haarMeasure) =
    ∫ V, subsetIntegrand small Φ β γ.support V ∂small.haarMeasure
  calc
    (∫ U, subsetIntegrand large Φ β γ.support U ∂large.haarMeasure) =
        ∫ U, subsetIntegrand small Φ β γ.support (R U)
          ∂large.haarMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hintegrand
    _ = ∫ V, subsetIntegrand small Φ β γ.support V
          ∂small.haarMeasure := by
      exact Gauge.ProductHaar.integral_restrictOfFinsetSubset
        (G := G) hsub (subsetIntegrand small Φ β γ.support)
        (continuous_subsetIntegrand small Φ β γ.support).measurable

/-- Stable countable hard-core model for the thermodynamic Mayer series. -/
def infinitePlaquettePolymerModel
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    CountablePolymerModel (InfinitePlaquettePolymer d) where
  incompatible := infinitePlaquettePolymerIncompatible
  decidableIncompatible := inferInstance
  symmetric_incompatible := infinitePlaquettePolymerIncompatible_symmetric
  self_incompatible := infinitePlaquettePolymerIncompatible_self
  activity := infinitePlaquetteActivity Φ β

/-- Positive cardinality majorant model at radius `r`. -/
def infinitePlaquetteMajorantModel
    (Φ : RealPlaquettePotential G) (r : ℝ) :
    CountablePolymerModel (InfinitePlaquettePolymer d) where
  incompatible := infinitePlaquettePolymerIncompatible
  decidableIncompatible := inferInstance
  symmetric_incompatible := infinitePlaquettePolymerIncompatible_symmetric
  self_incompatible := infinitePlaquettePolymerIncompatible_self
  activity γ := (perturbationMajorant Φ (r : ℂ) ^ γ.support.card : ℝ)

/-- Finite plaquette gas with the positive cardinality activity `q^|gamma|`. -/
def plaquetteCardinalityMajorantModel
    (Λ : FiniteSpecification d G) (q : ℝ) :
    FinitePolymerModel (PlaquettePolymer Λ) where
  incompatible := plaquettePolymerIncompatible Λ
  decidableIncompatible := inferInstance
  symmetric_incompatible := plaquettePolymerIncompatible_symmetric Λ
  self_incompatible := plaquettePolymerIncompatible_self Λ
  activity γ := (q ^ γ.1.card : ℝ)

/-- The lattice-animal proof of KP applies verbatim to the positive
cardinality majorant model. -/
theorem plaquetteCardinalityMajorantModel_koteckyPreiss
    (Λ : FiniteSpecification d G) (q : ℝ)
    (cert : AnimalCountingCertificate (ActivePlaquette Λ)
      (plaquetteAdjacencyGraph Λ))
    (hq : 0 ≤ q)
    (hsmall : q < dobrushinThreshold cert.degreeBound cert.animalConstant) :
    (plaquetteCardinalityMajorantModel Λ q).KoteckyPreissCertificate
      Finset.univ plaquetteKPWeight := by
  have hthreshold := hsmall
  rw [dobrushinThreshold, lt_min_iff, lt_min_iff] at hthreshold
  rcases hthreshold with ⟨_hqEight, hqAnimal, hqDegree⟩
  have htwoq : 0 ≤ 2 * q := mul_nonneg (by norm_num) hq
  have hCtwoq : (cert.animalConstant : ℝ) * (2 * q) < 1 := by
    have hCnonneg : 0 ≤ (cert.animalConstant : ℝ) := by positivity
    have hdenpos : 0 < (16 : ℝ) * (cert.animalConstant + 1) := by positivity
    have hmul := (lt_div_iff₀ hdenpos).mp hqAnimal
    nlinarith
  refine ⟨fun γ ↦ mul_nonneg (Nat.cast_nonneg γ.1.card)
    (Real.log_pos (by norm_num)).le, ?_⟩
  intro γ _
  let n := γ.1.card
  have hsum := sum_incompatiblePlaquettePolymerWeights_le
    Λ cert γ htwoq hCtwoq
  have hweighted :
      ∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
          ((plaquetteCardinalityMajorantModel Λ q).incompatible γ),
          ‖(plaquetteCardinalityMajorantModel Λ q).activity δ‖ *
            Real.exp (plaquetteKPWeight δ) ≤
        (n : ℝ) * (cert.degreeBound + 1) *
          ((2 * q) / (1 - (cert.animalConstant : ℝ) * (2 * q))) := by
    calc
      _ = ∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
            (plaquettePolymerIncompatible Λ γ), (2 * q) ^ δ.1.card := by
        apply Finset.sum_congr rfl
        intro δ _
        rw [plaquetteKPWeight, Real.exp_nat_mul,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        change ‖((q ^ δ.1.card : ℝ) : ℂ)‖ * 2 ^ δ.1.card = _
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg hq _), mul_pow]
        ring
      _ ≤ _ := hsum
  have hfrac :
      (2 * q) / (1 - (cert.animalConstant : ℝ) * (2 * q)) ≤ 4 * q := by
    have hdenpos : 0 < (16 : ℝ) * (cert.animalConstant + 1) := by positivity
    have hmul := (lt_div_iff₀ hdenpos).mp hqAnimal
    have hhalf : (cert.animalConstant : ℝ) * (2 * q) ≤ 1 / 2 := by
      nlinarith
    have hden : 0 < 1 - (cert.animalConstant : ℝ) * (2 * q) := by linarith
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hlocal : (cert.degreeBound + 1 : ℝ) * (4 * q) ≤ Real.log 2 := by
    have hdenpos : 0 < (16 : ℝ) * (cert.degreeBound + 1) := by positivity
    have hmul := (lt_div_iff₀ hdenpos).mp hqDegree
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  calc
    _ ≤ (n : ℝ) * (cert.degreeBound + 1) *
        ((2 * q) / (1 - (cert.animalConstant : ℝ) * (2 * q))) := hweighted
    _ ≤ (n : ℝ) * (cert.degreeBound + 1) * (4 * q) := by gcongr
    _ ≤ (n : ℝ) * Real.log 2 := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hlocal (Nat.cast_nonneg n)
    _ = plaquetteKPWeight γ := rfl

theorem perturbationMajorant_le_of_norm_le_real
    (Φ : RealPlaquettePotential G) (z : ℂ) (r : ℝ)
    (hz : ‖z‖ ≤ r) :
    perturbationMajorant Φ z ≤ perturbationMajorant Φ (r : ℂ) := by
  unfold perturbationMajorant
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  have hr : 0 ≤ r := (norm_nonneg z).trans hz
  simpa [abs_of_nonneg hr] using
    mul_le_mul_of_nonneg_right hz Φ.bound_nonneg

theorem norm_infinitePlaquetteActivity_le_majorant
    (Φ : RealPlaquettePotential G) (z : ℂ) (r : ℝ)
    (hz : ‖z‖ ≤ r) (γ : InfinitePlaquettePolymer d) :
    ‖infinitePlaquetteActivity Φ z γ‖ ≤
      ‖(infinitePlaquetteMajorantModel (d := d) Φ r).activity γ‖ := by
  rw [show ‖(infinitePlaquetteMajorantModel (d := d) Φ r).activity γ‖ =
      perturbationMajorant Φ (r : ℂ) ^ γ.support.card by
    change ‖((perturbationMajorant Φ (r : ℂ) ^ γ.support.card : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (pow_nonneg (perturbationMajorant_nonneg Φ (r : ℂ)) _)]]
  exact (norm_subsetWeight_le (γ.supportSpecification (G := G)) Φ z
      γ.support).trans
    (pow_le_pow_left₀ (perturbationMajorant_nonneg Φ z)
      (perturbationMajorant_le_of_norm_le_real Φ z r hz) _)

theorem norm_mayerActivityMonomial_le_majorant
    (Φ : RealPlaquettePotential G) (z : ℂ) (r : ℝ)
    (hz : ‖z‖ ≤ r)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) :
    ‖(infinitePlaquettePolymerModel Φ z).mayerActivityMonomial X‖ ≤
      ‖CountablePolymerModel.mayerActivityMonomial
        (infinitePlaquetteMajorantModel (d := d) Φ r) X‖ := by
  rw [CountablePolymerModel.mayerActivityMonomial,
    CountablePolymerModel.mayerActivityMonomial]
  change ‖∏ γ ∈ X.support,
      (infinitePlaquettePolymerModel Φ z).activity γ ^ X γ‖ ≤
    ‖∏ γ ∈ X.support,
      (infinitePlaquetteMajorantModel (d := d) Φ r).activity γ ^ X γ‖
  rw [norm_prod, norm_prod]
  apply Finset.prod_le_prod
  · intro γ _
    exact norm_nonneg _
  · intro γ _
    rw [norm_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_infinitePlaquetteActivity_le_majorant Φ z r hz γ) _

theorem norm_infinitePlaquetteMayerClusterTerm_le_majorant
    (Φ : RealPlaquettePotential G) (z : ℂ) (r : ℝ)
    (hz : ‖z‖ ≤ r)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) :
    ‖(infinitePlaquettePolymerModel Φ z).mayerClusterTerm X‖ ≤
      ‖CountablePolymerModel.mayerClusterTerm
        (infinitePlaquetteMajorantModel (d := d) Φ r) X‖ := by
  unfold CountablePolymerModel.mayerClusterTerm
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_mayerActivityMonomial_le_majorant Φ z r hz X) (norm_nonneg _)

theorem infinitePlaquetteActivity_entire
    (Φ : RealPlaquettePotential G) (γ : InfinitePlaquettePolymer d) :
    AnalyticOnNhd ℂ (fun β ↦ infinitePlaquetteActivity Φ β γ) Set.univ :=
  YangMills.StrongCoupling.subsetWeight_entire
    γ.supportSpecification Φ γ.support

/-- Entire countable activity family underlying the thermodynamic cluster
series. -/
def infinitePlaquetteAnalyticFamily
    (Φ : RealPlaquettePotential G) :
    CountablePolymerModel.AnalyticFamily (InfinitePlaquettePolymer d) where
  incompatible := infinitePlaquettePolymerIncompatible
  decidableIncompatible := inferInstance
  symmetric_incompatible := infinitePlaquettePolymerIncompatible_symmetric
  self_incompatible := infinitePlaquettePolymerIncompatible_self
  activity := infinitePlaquetteActivity Φ
  analytic_activity := infinitePlaquetteActivity_entire Φ

theorem infinitePlaquetteAnalyticFamily_model
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    (infinitePlaquetteAnalyticFamily (d := d) Φ).model β =
      infinitePlaquettePolymerModel (d := d) Φ β := rfl

/-- Every fixed global Mayer cluster coefficient is entire. -/
theorem analyticOnNhd_infinitePlaquetteMayerClusterTerm
    (Φ : RealPlaquettePotential G)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) :
    AnalyticOnNhd ℂ
      (fun β ↦ (infinitePlaquettePolymerModel Φ β).mayerClusterTerm X)
      Set.univ := by
  simpa only [infinitePlaquetteAnalyticFamily_model] using
    (infinitePlaquetteAnalyticFamily (d := d) Φ).analyticOnNhd_mayerClusterTerm X

@[simp]
theorem infinitePlaquetteActivity_translate
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (v : Site d) (γ : InfinitePlaquettePolymer d) :
    infinitePlaquetteActivity Φ β (γ.translate v) =
      infinitePlaquetteActivity Φ β γ := by
  rw [infinitePlaquetteActivity, ← InfinitePlaquettePolymer.supportSpecification_translate]
  exact subsetWeight_translate γ.supportSpecification Φ β γ.support v

theorem norm_infinitePlaquetteActivity_le
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (γ : InfinitePlaquettePolymer d) :
    ‖infinitePlaquetteActivity Φ β γ‖ ≤
      perturbationMajorant Φ β ^ γ.support.card :=
  norm_subsetWeight_le (γ.supportSpecification (G := G)) Φ β γ.support

/-- The explicit finite-volume plaquette KP certificate is uniform over all
finite restrictions of the full-lattice polymer species.  The proof embeds
an arbitrary finite family into its common finite support specification and
then restricts the already-certified finite KP sum. -/
theorem infinitePlaquettePolymerModel_finiteRestrictionKP
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    CountablePolymerModel.FiniteRestrictionKPCertificate
      (infinitePlaquettePolymerModel (d := d) Φ β)
      (fun γ ↦ (γ.support.card : ℝ) * Real.log 2) := by
  intro S
  let Λ := InfinitePlaquettePolymer.finiteFamilySpecification (G := G) S
  let e : S → PlaquettePolymer Λ :=
    InfinitePlaquettePolymer.toFiniteFamilyPolymer S
  have heinj : Function.Injective e :=
    InfinitePlaquettePolymer.toFiniteFamilyPolymer_injective S
  have hsmall : perturbationMajorant Φ β <
      dobrushinThreshold (16 * d) (2 ^ (16 * d)) :=
    perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
      (16 * d) (2 ^ (16 * d)) hβ
  have hfinite : (plaquettePolymerModel Λ Φ β).KoteckyPreissCertificate
      Finset.univ plaquetteKPWeight := by
    exact plaquettePolymerModel_koteckyPreiss Λ Φ β
      (cubicPlaquetteAnimalCertificate Λ) hsmall
  refine ⟨?_, ?_⟩
  · intro γ
    exact mul_nonneg (Nat.cast_nonneg _)
      (Real.log_pos (by norm_num)).le
  · intro γ _
    let f : PlaquettePolymer Λ → ℝ := fun δ ↦
      ‖(plaquettePolymerModel Λ Φ β).activity δ‖ *
        Real.exp (plaquetteKPWeight δ)
    have hterm : ∀ δ : S,
        ‖((infinitePlaquettePolymerModel (d := d) Φ β).restrict S).activity δ‖ *
            Real.exp ((δ.1.support.card : ℝ) * Real.log 2) = f (e δ) := by
      intro δ
      have hactivity :=
        subsetWeight_finiteFamilySpecification_eq_infinitePlaquetteActivity
          Φ β S δ
      change ‖infinitePlaquetteActivity Φ β δ.1‖ *
          Real.exp ((δ.1.support.card : ℝ) * Real.log 2) = _
      rw [← hactivity]
      change ‖subsetWeight Λ Φ β δ.1.support‖ *
          Real.exp ((δ.1.support.card : ℝ) * Real.log 2) = _
      unfold f plaquetteKPWeight plaquettePolymerModel
      have hsupp : (e δ).support = δ.1.support :=
        InfinitePlaquettePolymer.support_toFiniteFamilyPolymer S δ
      have hcard : (e δ).1.card = δ.1.support.card := by
        rw [← PlaquettePolymer.card_support, hsupp]
      simp only
      rw [hsupp, hcard]
    have hinc : ∀ δ : S,
        (infinitePlaquettePolymerModel (d := d) Φ β).incompatible γ.1 δ.1 ↔
          (plaquettePolymerModel Λ Φ β).incompatible (e γ) (e δ) := by
      intro δ
      exact (InfinitePlaquettePolymer.incompatible_toFiniteFamilyPolymer_iff
        (G := G) S γ δ).symm
    calc
      ∑ δ ∈ (Finset.univ : Finset S).filter
            (fun δ ↦ (CountablePolymerModel.restrict
              (infinitePlaquettePolymerModel (d := d) Φ β) S).incompatible γ δ),
          ‖((infinitePlaquettePolymerModel (d := d) Φ β).restrict S).activity δ‖ *
            Real.exp ((δ.1.support.card : ℝ) * Real.log 2) =
          ∑ δ : S, if (plaquettePolymerModel Λ Φ β).incompatible
              (e γ) (e δ) then f (e δ) else 0 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro δ _
        by_cases hi : (plaquettePolymerModel Λ Φ β).incompatible
            (e γ) (e δ)
        · rw [if_pos hi]
          have hi' : (CountablePolymerModel.restrict
              (infinitePlaquettePolymerModel (d := d) Φ β) S).incompatible
                γ δ := (hinc δ).mpr hi
          rw [if_pos hi']
          exact hterm δ
        · rw [if_neg hi]
          have hi' : ¬(CountablePolymerModel.restrict
              (infinitePlaquettePolymerModel (d := d) Φ β) S).incompatible
                γ δ := fun h ↦ hi ((hinc δ).mp h)
          rw [if_neg hi']
      _ = ∑ η ∈ (Finset.univ : Finset S).image e,
          if (plaquettePolymerModel Λ Φ β).incompatible (e γ) η
          then f η else 0 := by
        exact (Finset.sum_image (s := (Finset.univ : Finset S))
          (f := fun η : PlaquettePolymer Λ ↦
            if (plaquettePolymerModel Λ Φ β).incompatible (e γ) η
            then f η else 0) (Set.injOn_of_injective heinj)).symm
      _ ≤ ∑ η : PlaquettePolymer Λ,
          if (plaquettePolymerModel Λ Φ β).incompatible (e γ) η
          then f η else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
        intro η _ _
        split_ifs
        · exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
        · exact le_rfl
      _ = ∑ η ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
            ((plaquettePolymerModel Λ Φ β).incompatible (e γ)),
          ‖(plaquettePolymerModel Λ Φ β).activity η‖ *
            Real.exp (plaquetteKPWeight η) := by
        rw [Finset.sum_filter]
      _ ≤ plaquetteKPWeight (e γ) :=
        hfinite.2 (e γ) (Finset.mem_univ _)
      _ = (γ.1.support.card : ℝ) * Real.log 2 := by
        unfold plaquetteKPWeight
        rw [← PlaquettePolymer.card_support,
          InfinitePlaquettePolymer.support_toFiniteFamilyPolymer]

/-! ## Exact finite free-region pressure -/

/-- Union of all plaquettes carried by a finite global Mayer cluster. -/
def infinitePlaquetteMayerCarrier
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) : Finset (Plaquette d) :=
  CountablePolymerModel.mayerCarrier InfinitePlaquettePolymer.support X

/-- Translate every polymer species occurring in a global Mayer
multi-index. -/
def translateInfinitePlaquetteMayerMultiIndex (v : Site d) :
    CountablePolymerModel.MayerMultiIndex (InfinitePlaquettePolymer d) ≃
      CountablePolymerModel.MayerMultiIndex (InfinitePlaquettePolymer d) :=
  Finsupp.equivCongrLeft (InfinitePlaquettePolymer.translationEquiv v)

@[simp]
theorem translateInfinitePlaquetteMayerMultiIndex_apply
    (v : Site d)
    (X : CountablePolymerModel.MayerMultiIndex (InfinitePlaquettePolymer d))
    (γ : InfinitePlaquettePolymer d) :
    translateInfinitePlaquetteMayerMultiIndex v X (γ.translate v) = X γ := by
  simp [translateInfinitePlaquetteMayerMultiIndex,
    InfinitePlaquettePolymer.translationEquiv]

@[simp]
theorem support_translateInfinitePlaquetteMayerMultiIndex
    (v : Site d)
    (X : CountablePolymerModel.MayerMultiIndex (InfinitePlaquettePolymer d)) :
    (translateInfinitePlaquetteMayerMultiIndex v X).support = X.support.map
      (InfinitePlaquettePolymer.translationEquiv v).toEmbedding := by
  ext γ
  rw [Finset.mem_map_equiv]
  simp only [Finsupp.mem_support_iff]
  rw [show translateInfinitePlaquetteMayerMultiIndex v X γ =
      X ((InfinitePlaquettePolymer.translationEquiv v).symm γ) by rfl]

@[simp]
theorem infinitePlaquetteMayerCarrier_translate
    (v : Site d)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) :
    infinitePlaquetteMayerCarrier
        (translateInfinitePlaquetteMayerMultiIndex v X) =
      (infinitePlaquetteMayerCarrier X).map
        (Plaquette.translationEquiv v).toEmbedding := by
  ext p
  simp only [infinitePlaquetteMayerCarrier,
    CountablePolymerModel.mayerCarrier,
    support_translateInfinitePlaquetteMayerMultiIndex,
    Finset.mem_biUnion, Finset.mem_map_equiv,
    InfinitePlaquettePolymer.translationEquiv,
    Plaquette.translationEquiv]
  constructor
  · rintro ⟨γ, hγX, hpγ⟩
    refine ⟨γ.translate (-v), hγX, ?_⟩
    rw [InfinitePlaquettePolymer.support_translate, Finset.mem_map_equiv]
    change (p.translate (-v)).translate (-(-v)) ∈ γ.support
    simpa using hpγ
  · rintro ⟨γ, hγX, hpγ⟩
    refine ⟨γ.translate v, ?_, ?_⟩
    · simpa using hγX
    · rw [InfinitePlaquettePolymer.support_translate, Finset.mem_map_equiv]
      change p.translate (-v) ∈ γ.support
      simpa using hpγ

@[simp]
theorem infinitePlaquetteMayerClusterTerm_translate
    (Φ : RealPlaquettePotential G) (β : ℂ) (v : Site d)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) :
    (infinitePlaquettePolymerModel Φ β).mayerClusterTerm
        (translateInfinitePlaquetteMayerMultiIndex v X) =
      (infinitePlaquettePolymerModel Φ β).mayerClusterTerm X := by
  exact CountablePolymerModel.mayerClusterTerm_relabelMultiIndex
    (infinitePlaquettePolymerModel Φ β)
    (infinitePlaquettePolymerModel Φ β)
    (InfinitePlaquettePolymer.translationEquiv v)
    (fun γ δ ↦ infinitePlaquettePolymerIncompatible_translate_iff v γ δ)
    (fun γ ↦ infinitePlaquetteActivity_translate Φ β v γ) X

/-- The global polymer gas restricted to polymers carried by `A` is exactly
the ordinary free-region plaquette gas, up to the canonical species
equivalence. -/
theorem partitionFunction_restrict_freeRegionGlobalPolymers
    (Φ : RealPlaquettePotential G) (β : ℂ) (A : Finset (Plaquette d)) :
    ((infinitePlaquettePolymerModel (d := d) Φ β).restrict
      (InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G) A)).partitionFunction =
      (plaquettePolymerModel
        (InfinitePlaquettePolymer.freeRegionSpecification (G := G) A) Φ β).partitionFunction := by
  let M := plaquettePolymerModel
    (InfinitePlaquettePolymer.freeRegionSpecification (G := G) A) Φ β
  let N := (infinitePlaquettePolymerModel (d := d) Φ β).restrict
    (InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G) A)
  let e := InfinitePlaquettePolymer.freeRegionPolymerEquiv (G := G) A
  have hinc : ∀ γ δ, N.incompatible (e γ) (e δ) ↔ M.incompatible γ δ := by
    intro γ δ
    exact InfinitePlaquettePolymer.incompatible_ofFreeRegionPolymer_iff
      (G := G) A γ δ
  have hact : ∀ γ, N.activity (e γ) = M.activity γ := by
    intro γ
    change infinitePlaquetteActivity Φ β
        (InfinitePlaquettePolymer.ofFreeRegionPolymer A γ) =
      subsetWeight (InfinitePlaquettePolymer.freeRegionSpecification
        (G := G) A) Φ β γ.support
    exact (subsetWeight_freeRegionSpecification_eq_infinitePlaquetteActivity
      Φ β A γ).symm
  exact M.partitionFunction_eq_of_equiv N e hinc hact

/-- Exact finite free-region pressure identity, expressed on the stable
global polymer species.  This is the finite-volume logarithm branch used by
the boundary/volume limit. -/
theorem exp_symmetricMayerSum_restrict_freeRegion_eq_complexPartitionFunction
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (A : Finset (Plaquette d)) :
    Complex.exp
        (((infinitePlaquettePolymerModel (d := d) Φ β).restrict
          (InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G) A)).symmetricMayerSum) =
      complexPartitionFunction
        (InfinitePlaquettePolymer.freeRegionSpecification (G := G) A) Φ β := by
  let S := InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G) A
  let M := infinitePlaquettePolymerModel (d := d) Φ β
  calc
    Complex.exp ((M.restrict S).symmetricMayerSum) =
        (M.restrict S).partitionFunction := by
      exact FinitePolymerModel.exp_symmetricMayerSum_eq_partitionFunction_of_koteckyPreiss
          (M.restrict S)
          (fun γ : S ↦ (γ.1.support.card : ℝ) * Real.log 2)
          (infinitePlaquettePolymerModel_finiteRestrictionKP Φ hβ S)
    _ = (plaquettePolymerModel
        (InfinitePlaquettePolymer.freeRegionSpecification (G := G) A) Φ β).partitionFunction :=
      partitionFunction_restrict_freeRegionGlobalPolymers Φ β A
    _ = complexPartitionFunction
        (InfinitePlaquettePolymer.freeRegionSpecification (G := G) A) Φ β := by
      symm
      exact complexPartitionFunction_eq_polymerPartition _ _ _

/-- The finite symmetric Mayer logarithm is the stable global cluster series
cut off exactly by geometric carrier containment. -/
theorem symmetricMayerSum_restrict_freeRegion_eq_tsum_carrier
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (A : Finset (Plaquette d)) :
    ((infinitePlaquettePolymerModel (d := d) Φ β).restrict
      (InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G) A)).symmetricMayerSum =
      ∑' X : CountablePolymerModel.MayerMultiIndex
          (InfinitePlaquettePolymer d),
        if infinitePlaquetteMayerCarrier X ⊆ A then
          (infinitePlaquettePolymerModel Φ β).mayerClusterTerm X else 0 := by
  let M := infinitePlaquettePolymerModel (d := d) Φ β
  let S := InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G) A
  rw [M.symmetricMayerSum_restrict_eq_tsum S
    (fun γ ↦ (γ.support.card : ℝ) * Real.log 2)
    (infinitePlaquettePolymerModel_finiteRestrictionKP Φ hβ)]
  apply tsum_congr
  intro X
  congr 1
  apply propext
  constructor
  · intro hX p hp
    rcases (CountablePolymerModel.mem_mayerCarrier
      InfinitePlaquettePolymer.support X p).mp hp with ⟨γ, hγX, hpγ⟩
    exact InfinitePlaquettePolymer.support_subset_of_mem_freeRegionGlobalPolymers
      A (hX hγX) hpγ
  · intro hcarrier γ hγX
    apply (InfinitePlaquettePolymer.mem_freeRegionGlobalPolymers_iff_support_subset
      (G := G) A γ).mpr
    intro p hp
    apply hcarrier
    exact (CountablePolymerModel.mem_mayerCarrier
      InfinitePlaquettePolymer.support X p).mpr ⟨γ, hγX, hp⟩

/-- The positive cardinality majorant at a radius inside the explicit disk
has the same uniform finite-restriction KP certificate. -/
theorem infinitePlaquetteMajorantModel_finiteRestrictionKP
    (Φ : RealPlaquettePotential G) {r : ℝ}
    (hr0 : 0 ≤ r)
    (hr : r < latticeStrongCouplingRadius d Φ.bound) :
    CountablePolymerModel.FiniteRestrictionKPCertificate
      (infinitePlaquetteMajorantModel (d := d) Φ r)
      (fun γ ↦ (γ.support.card : ℝ) * Real.log 2) := by
  intro S
  let Λ := InfinitePlaquettePolymer.finiteFamilySpecification (G := G) S
  let e : S → PlaquettePolymer Λ :=
    InfinitePlaquettePolymer.toFiniteFamilyPolymer S
  have heinj : Function.Injective e :=
    InfinitePlaquettePolymer.toFiniteFamilyPolymer_injective S
  let q := perturbationMajorant Φ (r : ℂ)
  have hqsmall : q <
      dobrushinThreshold (cubicPlaquetteAnimalCertificate Λ).degreeBound
        (cubicPlaquetteAnimalCertificate Λ).animalConstant :=
    perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
      (16 * d) (2 ^ (16 * d)) (by simpa [abs_of_nonneg hr0] using hr)
  have hfinite : (plaquetteCardinalityMajorantModel Λ q).KoteckyPreissCertificate
      Finset.univ plaquetteKPWeight := by
    exact plaquetteCardinalityMajorantModel_koteckyPreiss Λ q
      (cubicPlaquetteAnimalCertificate Λ)
      (perturbationMajorant_nonneg Φ (r : ℂ)) hqsmall
  refine ⟨?_, ?_⟩
  · intro γ
    exact mul_nonneg (Nat.cast_nonneg _)
      (Real.log_pos (by norm_num)).le
  · intro γ _
    let f : PlaquettePolymer Λ → ℝ := fun δ ↦
      ‖(plaquetteCardinalityMajorantModel Λ q).activity δ‖ *
        Real.exp (plaquetteKPWeight δ)
    have hterm : ∀ δ : S,
        ‖((infinitePlaquetteMajorantModel (d := d) Φ r).restrict S).activity δ‖ *
            Real.exp ((δ.1.support.card : ℝ) * Real.log 2) ≤ f (e δ) := by
      intro δ
      have hsupp : (e δ).support = δ.1.support :=
        InfinitePlaquettePolymer.support_toFiniteFamilyPolymer S δ
      have hcard : (e δ).1.card = δ.1.support.card := by
        rw [← PlaquettePolymer.card_support, hsupp]
      change ‖((q ^ δ.1.support.card : ℝ) : ℂ)‖ *
          Real.exp ((δ.1.support.card : ℝ) * Real.log 2) ≤ _
      unfold f plaquetteKPWeight plaquetteCardinalityMajorantModel
      rw [show ‖((q ^ δ.1.support.card : ℝ) : ℂ)‖ =
          q ^ δ.1.support.card by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg (perturbationMajorant_nonneg Φ _) _)],
        hcard]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (perturbationMajorant_nonneg Φ _) _)]
      rw [hcard]
    have hinc : ∀ δ : S,
        (infinitePlaquetteMajorantModel (d := d) Φ r).incompatible γ.1 δ.1 ↔
          (plaquetteCardinalityMajorantModel Λ q).incompatible (e γ) (e δ) := by
      intro δ
      exact (InfinitePlaquettePolymer.incompatible_toFiniteFamilyPolymer_iff
        (G := G) S γ δ).symm
    calc
      ∑ δ ∈ (Finset.univ : Finset S).filter
            (fun δ ↦ (CountablePolymerModel.restrict
              (infinitePlaquetteMajorantModel (d := d) Φ r) S).incompatible
                γ δ),
          ‖((infinitePlaquetteMajorantModel (d := d) Φ r).restrict S).activity δ‖ *
            Real.exp ((δ.1.support.card : ℝ) * Real.log 2) ≤
          ∑ δ : S, if (plaquetteCardinalityMajorantModel Λ q).incompatible
              (e γ) (e δ) then f (e δ) else 0 := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro δ _
        by_cases hi : (plaquetteCardinalityMajorantModel Λ q).incompatible
            (e γ) (e δ)
        · rw [if_pos hi]
          have hi' : (CountablePolymerModel.restrict
              (infinitePlaquetteMajorantModel (d := d) Φ r) S).incompatible
                γ δ := (hinc δ).mpr hi
          rw [if_pos hi']
          exact hterm δ
        · rw [if_neg hi]
          have hi' : ¬(CountablePolymerModel.restrict
              (infinitePlaquetteMajorantModel (d := d) Φ r) S).incompatible
                γ δ := fun h ↦ hi ((hinc δ).mp h)
          rw [if_neg hi']
      _ = ∑ η ∈ (Finset.univ : Finset S).image e,
          if (plaquetteCardinalityMajorantModel Λ q).incompatible (e γ) η
          then f η else 0 := by
        exact (Finset.sum_image (s := (Finset.univ : Finset S))
          (f := fun η : PlaquettePolymer Λ ↦
            if (plaquetteCardinalityMajorantModel Λ q).incompatible (e γ) η
            then f η else 0) (Set.injOn_of_injective heinj)).symm
      _ ≤ ∑ η : PlaquettePolymer Λ,
          if (plaquetteCardinalityMajorantModel Λ q).incompatible (e γ) η
          then f η else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
        intro η _ _
        split_ifs
        · exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
        · exact le_rfl
      _ = ∑ η ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
            ((plaquetteCardinalityMajorantModel Λ q).incompatible (e γ)),
          ‖(plaquetteCardinalityMajorantModel Λ q).activity η‖ *
            Real.exp (plaquetteKPWeight η) := by rw [Finset.sum_filter]
      _ ≤ plaquetteKPWeight (e γ) :=
        hfinite.2 (e γ) (Finset.mem_univ _)
      _ = (γ.1.support.card : ℝ) * Real.log 2 := by
        unfold plaquetteKPWeight
        rw [← PlaquettePolymer.card_support,
          InfinitePlaquettePolymer.support_toFiniteFamilyPolymer]

/-! ## Plaquette-rooted pressure coefficients -/

/-- Ordered plaquette directions at one lattice site.  The project uses
ordered coordinate plaquettes, so this is the exact translation-orbit type. -/
structure PlaquetteOrientation (d : ℕ) where
  first : Fin d
  second : Fin d
  distinct : first ≠ second
  deriving Fintype, DecidableEq

/-- Representative at the origin of an ordered plaquette translation orbit. -/
def PlaquetteOrientation.atOrigin (o : PlaquetteOrientation d) : Plaquette d :=
  ⟨0, o.first, o.second, o.distinct⟩

/-- Decompose a plaquette into its base site and ordered orientation. -/
def plaquetteDecompositionEquiv (d : ℕ) :
    Site d × PlaquetteOrientation d ≃ Plaquette d where
  toFun xo := xo.2.atOrigin.translate xo.1
  invFun p := (p.base, ⟨p.first, p.second, p.distinct⟩)
  left_inv xo := by
    rcases xo with ⟨x, o⟩
    rcases o with ⟨i, j, hij⟩
    simp [PlaquetteOrientation.atOrigin, Plaquette.translate,
      Lattice.Cubic.translate]
  right_inv p := by
    rcases p with ⟨x, i, j, hij⟩
    simp [PlaquetteOrientation.atOrigin, Plaquette.translate,
      Lattice.Cubic.translate]

/-- A cluster coefficient rooted at one plaquette.  Division by the carrier
cardinality distributes every unrooted cluster exactly once over the
plaquettes in its geometric carrier; this is the canonical pressure
normalization without choosing an arbitrary logarithm branch. -/
def plaquetteRootedMayerTerm
    (Φ : RealPlaquettePotential G) (β : ℂ) (p : Plaquette d)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) : ℂ :=
  if p ∈ infinitePlaquetteMayerCarrier X then
    (infinitePlaquettePolymerModel Φ β).mayerClusterTerm X /
      (infinitePlaquetteMayerCarrier X).card
  else 0

@[simp]
theorem plaquetteRootedMayerTerm_translate
    (Φ : RealPlaquettePotential G) (β : ℂ) (v : Site d)
    (p : Plaquette d)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) :
    plaquetteRootedMayerTerm Φ β (p.translate v)
        (translateInfinitePlaquetteMayerMultiIndex v X) =
      plaquetteRootedMayerTerm Φ β p X := by
  rw [plaquetteRootedMayerTerm, plaquetteRootedMayerTerm,
    infinitePlaquetteMayerCarrier_translate,
    infinitePlaquetteMayerClusterTerm_translate, Finset.card_map]
  simp [Plaquette.translationEquiv]

/-- The full rooted cluster series is constant on every plaquette
translation orbit. -/
theorem tsum_plaquetteRootedMayerTerm_translate
    (Φ : RealPlaquettePotential G) (β : ℂ) (v : Site d)
    (p : Plaquette d) :
    (∑' X, plaquetteRootedMayerTerm Φ β (p.translate v) X) =
      ∑' X, plaquetteRootedMayerTerm Φ β p X := by
  calc
    (∑' X, plaquetteRootedMayerTerm Φ β (p.translate v) X) =
        ∑' X, plaquetteRootedMayerTerm Φ β (p.translate v)
          (translateInfinitePlaquetteMayerMultiIndex v X) :=
      (Equiv.tsum_eq (translateInfinitePlaquetteMayerMultiIndex v)
        (fun X ↦ plaquetteRootedMayerTerm Φ β (p.translate v) X)).symm
    _ = ∑' X, plaquetteRootedMayerTerm Φ β p X := by
      apply tsum_congr
      intro X
      exact plaquetteRootedMayerTerm_translate Φ β v p X

/-- Every fixed plaquette-rooted pressure summand is entire. -/
theorem analyticOnNhd_plaquetteRootedMayerTerm
    (Φ : RealPlaquettePotential G) (p : Plaquette d)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) :
    AnalyticOnNhd ℂ (fun β ↦ plaquetteRootedMayerTerm Φ β p X)
      Set.univ := by
  by_cases hp : p ∈ infinitePlaquetteMayerCarrier X
  · simp only [plaquetteRootedMayerTerm, hp, if_true, div_eq_mul_inv]
    exact (analyticOnNhd_infinitePlaquetteMayerClusterTerm Φ X).mul
      (analyticOnNhd_const : AnalyticOnNhd ℂ
        (fun _ : ℂ ↦ ((infinitePlaquetteMayerCarrier X).card : ℂ)⁻¹)
        Set.univ)
  · simp only [plaquetteRootedMayerTerm, hp, if_false]
    exact analyticOnNhd_const

/-- A rooted pressure term is dominated by the sum of multiplicity-pinned
Mayer norms over the polymers in the cluster that contain the anchor. -/
theorem norm_plaquetteRootedMayerTerm_le_pinned_sum
    (Φ : RealPlaquettePotential G) (β : ℂ) (p : Plaquette d)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d))
    (S : Finset (InfinitePlaquettePolymer d)) (hX : X.support ⊆ S) :
    ‖plaquetteRootedMayerTerm Φ β p X‖ ≤
      ∑ γ ∈ S, if p ∈ γ.support then
        (infinitePlaquettePolymerModel Φ β).pinnedNormMayerTerm γ X
      else 0 := by
  let M := infinitePlaquettePolymerModel (d := d) Φ β
  by_cases hp : p ∈ infinitePlaquetteMayerCarrier X
  · rcases (CountablePolymerModel.mem_mayerCarrier
      InfinitePlaquettePolymer.support X p).mp hp with ⟨γ, hγX, hpγ⟩
    have hγS : γ ∈ S := hX hγX
    have hXγ : 1 ≤ X γ := Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp hγX)
    have hcarrier : 1 ≤ (infinitePlaquetteMayerCarrier X).card :=
      Finset.one_le_card.mpr ⟨p, hp⟩
    have hdiv : ‖M.mayerClusterTerm X /
        (infinitePlaquetteMayerCarrier X).card‖ ≤
        ‖M.mayerClusterTerm X‖ := by
      rw [norm_div, Complex.norm_natCast]
      exact div_le_self (norm_nonneg _)
        (by exact_mod_cast hcarrier)
    have hpinned : ‖M.mayerClusterTerm X‖ ≤
        M.pinnedNormMayerTerm γ X := by
      unfold CountablePolymerModel.pinnedNormMayerTerm
      calc
        ‖M.mayerClusterTerm X‖ = 1 * ‖M.mayerClusterTerm X‖ := by ring
        _ ≤ (X γ : ℝ) * ‖M.mayerClusterTerm X‖ := by
          gcongr
          exact_mod_cast hXγ
    rw [plaquetteRootedMayerTerm, if_pos hp]
    refine (hdiv.trans hpinned).trans ?_
    have hsingle := Finset.single_le_sum
      (f := fun δ ↦ if p ∈ δ.support then
        M.pinnedNormMayerTerm δ X else 0)
      (fun δ _ ↦ by
        change 0 ≤ if p ∈ δ.support then M.pinnedNormMayerTerm δ X else 0
        split_ifs
        · exact CountablePolymerModel.pinnedNormMayerTerm_nonneg M δ X
        · exact le_rfl) hγS
    simpa [hpγ] using hsingle
  · rw [plaquetteRootedMayerTerm, if_neg hp, norm_zero]
    exact Finset.sum_nonneg fun γ _ ↦ by
      split_ifs
      · exact CountablePolymerModel.pinnedNormMayerTerm_nonneg M γ X
      · exact le_rfl

/-- Model-generic version of the rooted-carrier domination. -/
theorem norm_rootedMayerTerm_le_pinned_sum_model
    (M : CountablePolymerModel (InfinitePlaquettePolymer d))
    (p : Plaquette d)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d))
    (S : Finset (InfinitePlaquettePolymer d)) (hX : X.support ⊆ S) :
    ‖if p ∈ infinitePlaquetteMayerCarrier X then
        M.mayerClusterTerm X / (infinitePlaquetteMayerCarrier X).card
      else 0‖ ≤
      ∑ γ ∈ S, if p ∈ γ.support then M.pinnedNormMayerTerm γ X
      else 0 := by
  by_cases hp : p ∈ infinitePlaquetteMayerCarrier X
  · rcases (CountablePolymerModel.mem_mayerCarrier
      InfinitePlaquettePolymer.support X p).mp hp with ⟨γ, hγX, hpγ⟩
    have hγS : γ ∈ S := hX hγX
    have hXγ : 1 ≤ X γ := Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp hγX)
    have hcarrier : 1 ≤ (infinitePlaquetteMayerCarrier X).card :=
      Finset.one_le_card.mpr ⟨p, hp⟩
    rw [if_pos hp, norm_div, Complex.norm_natCast]
    have hdiv : ‖M.mayerClusterTerm X‖ /
        (infinitePlaquetteMayerCarrier X).card ≤ ‖M.mayerClusterTerm X‖ :=
      div_le_self (norm_nonneg _) (by exact_mod_cast hcarrier)
    have hpinned : ‖M.mayerClusterTerm X‖ ≤ M.pinnedNormMayerTerm γ X := by
      unfold CountablePolymerModel.pinnedNormMayerTerm
      calc
        ‖M.mayerClusterTerm X‖ = 1 * ‖M.mayerClusterTerm X‖ := by ring
        _ ≤ (X γ : ℝ) * ‖M.mayerClusterTerm X‖ := by
          gcongr
          exact_mod_cast hXγ
    refine (hdiv.trans hpinned).trans ?_
    have hsingle := Finset.single_le_sum
      (f := fun δ ↦ if p ∈ δ.support then
        M.pinnedNormMayerTerm δ X else 0)
      (fun δ _ ↦ by
        change 0 ≤ if p ∈ δ.support then M.pinnedNormMayerTerm δ X else 0
        split_ifs
        · exact M.pinnedNormMayerTerm_nonneg δ X
        · exact le_rfl) hγS
    simpa [hpγ] using hsingle
  · rw [if_neg hp, norm_zero]
    exact Finset.sum_nonneg fun γ _ ↦ by
      split_ifs
      · exact M.pinnedNormMayerTerm_nonneg γ X
      · exact le_rfl

/-- Carrier-rooting is an exact normalization: summing the rooted term over
any finite region containing the carrier recovers the unrooted cluster
coefficient once. -/
theorem sum_plaquetteRootedMayerTerm_eq_mayerClusterTerm
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (A : Finset (Plaquette d))
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d))
    (hcarrier : infinitePlaquetteMayerCarrier X ⊆ A) :
    ∑ p ∈ A, plaquetteRootedMayerTerm Φ β p X =
      (infinitePlaquettePolymerModel Φ β).mayerClusterTerm X := by
  let C := infinitePlaquetteMayerCarrier X
  by_cases hC : C.Nonempty
  · rw [show ∑ p ∈ A, plaquetteRootedMayerTerm Φ β p X =
        ∑ p ∈ C, plaquetteRootedMayerTerm Φ β p X by
      symm
      apply Finset.sum_subset hcarrier
      intro p _ hp
      simp [plaquetteRootedMayerTerm, hp]]
    simp only [plaquetteRootedMayerTerm]
    have hcard : (C.card : ℂ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hC
    calc
      ∑ p ∈ C, (if p ∈ C then
          (infinitePlaquettePolymerModel Φ β).mayerClusterTerm X / C.card
        else 0) = ∑ _p ∈ C,
          (infinitePlaquettePolymerModel Φ β).mayerClusterTerm X / C.card := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [if_pos hp]
      _ = (C.card : ℂ) *
          ((infinitePlaquettePolymerModel Φ β).mayerClusterTerm X / C.card) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = (infinitePlaquettePolymerModel Φ β).mayerClusterTerm X := by
        field_simp
  · have hCempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    have hXempty : X.support = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hsupport
      rcases hsupport with ⟨γ, hγ⟩
      obtain ⟨p, hp⟩ := γ.support_nonempty
      have hpC : p ∈ C := (CountablePolymerModel.mem_mayerCarrier
        InfinitePlaquettePolymer.support X p).mpr ⟨γ, hγ, hp⟩
      rw [hCempty] at hpC
      simp at hpC
    let M := infinitePlaquettePolymerModel (d := d) Φ β
    have hnotconnected : ¬(M.mayerIncompatibilityGraph X).Connected := by
      intro h
      rcases h.nonempty with ⟨⟨⟨γ, hγ⟩, i⟩⟩
      rw [hXempty] at hγ
      simp at hγ
    rw [CountablePolymerModel.mayerClusterTerm_eq_zero_of_not_connected
      M X hnotconnected]
    apply Finset.sum_eq_zero
    intro p _
    simp [plaquetteRootedMayerTerm, C, hCempty]

/-- Every finite partial sum of plaquette-rooted Mayer norms is at most the
singleton anchor's KP weight, namely `log 2`. -/
theorem sum_norm_plaquetteRootedMayerTerm_le_log_two
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (p : Plaquette d)
    (U : Finset (CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d))) :
    ∑ X ∈ U, ‖plaquetteRootedMayerTerm Φ β p X‖ ≤ Real.log 2 := by
  let M := infinitePlaquettePolymerModel (d := d) Φ β
  let a : InfinitePlaquettePolymer d → ℝ :=
    fun γ ↦ (γ.support.card : ℝ) * Real.log 2
  let root := InfinitePlaquettePolymer.singleton p
  let S : Finset (InfinitePlaquettePolymer d) :=
    insert root (U.biUnion fun X ↦ X.support)
  have hKP : M.FiniteRestrictionKPCertificate a :=
    infinitePlaquettePolymerModel_finiteRestrictionKP Φ hβ
  have hsupport : ∀ X ∈ U, X.support ⊆ S := by
    intro X hX γ hγ
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨X, hX, hγ⟩)
  calc
    ∑ X ∈ U, ‖plaquetteRootedMayerTerm Φ β p X‖ ≤
        ∑ X ∈ U, ∑ γ ∈ S, if p ∈ γ.support then
          M.pinnedNormMayerTerm γ X else 0 := by
      exact Finset.sum_le_sum fun X hX ↦
        norm_plaquetteRootedMayerTerm_le_pinned_sum Φ β p X S
          (hsupport X hX)
    _ = ∑ γ ∈ S, ∑ X ∈ U, if p ∈ γ.support then
          M.pinnedNormMayerTerm γ X else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ γ ∈ S, if p ∈ γ.support then
          ‖M.activity γ‖ * Real.exp (a γ) else 0 := by
      apply Finset.sum_le_sum
      intro γ _
      by_cases hpγ : p ∈ γ.support
      · simp only [hpγ, if_true]
        exact M.sum_pinnedNormMayerTerm_le_of_finiteRestrictionKP a hKP γ U
      · simp [hpγ]
    _ ≤ ∑ γ ∈ S, M.incompatibleTiltedActivity a root γ := by
      apply Finset.sum_le_sum
      intro γ _
      by_cases hpγ : p ∈ γ.support
      · rw [if_pos hpγ]
        unfold CountablePolymerModel.incompatibleTiltedActivity
        rw [if_pos]
        exact singleton_incompatible_of_mem p γ hpγ
      · rw [if_neg hpγ]
        exact M.incompatibleTiltedActivity_nonneg a root γ
    _ ≤ a root :=
      M.sum_incompatibleTiltedActivity_le_of_finiteRestrictionKP a hKP root S
    _ = Real.log 2 := by simp [a, root]

/-- Genuine absolute convergence of the plaquette-rooted pressure series on
the explicit complex strong-coupling disk. -/
theorem summable_norm_plaquetteRootedMayerTerm
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (p : Plaquette d) :
    Summable (fun X ↦ ‖plaquetteRootedMayerTerm Φ β p X‖) := by
  refine summable_of_sum_le (c := Real.log 2) (fun _ ↦ norm_nonneg _) ?_
  intro U
  exact sum_norm_plaquetteRootedMayerTerm_le_log_two Φ hβ p U

theorem tsum_norm_plaquetteRootedMayerTerm_le_log_two
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (p : Plaquette d) :
    ∑' X, ‖plaquetteRootedMayerTerm Φ β p X‖ ≤ Real.log 2 := by
  apply Real.tsum_le_of_sum_le (fun _ ↦ norm_nonneg _)
  intro U
  exact sum_norm_plaquetteRootedMayerTerm_le_log_two Φ hβ p U

/-- Exact rooted form of the finite free-region Mayer logarithm.  This makes
the thermodynamic error a rooted boundary-reaching tail, in precisely the
same form as the one-root estimates used for infinite volume and
clustering. -/
theorem symmetricMayerSum_restrict_freeRegion_eq_sum_tsum_rooted
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (A : Finset (Plaquette d)) :
    ((infinitePlaquettePolymerModel (d := d) Φ β).restrict
      (InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G) A)).symmetricMayerSum =
      ∑ p ∈ A, ∑' X : CountablePolymerModel.MayerMultiIndex
          (InfinitePlaquettePolymer d),
        if infinitePlaquetteMayerCarrier X ⊆ A then
          plaquetteRootedMayerTerm Φ β p X else 0 := by
  rw [symmetricMayerSum_restrict_freeRegion_eq_tsum_carrier Φ hβ A]
  symm
  have hsummable (p : Plaquette d) : Summable
      (fun X : CountablePolymerModel.MayerMultiIndex
          (InfinitePlaquettePolymer d) ↦
        if infinitePlaquetteMayerCarrier X ⊆ A then
          plaquetteRootedMayerTerm Φ β p X else 0) := by
    apply Summable.of_norm_bounded
      (summable_norm_plaquetteRootedMayerTerm Φ hβ p)
    intro X
    by_cases hX : infinitePlaquetteMayerCarrier X ⊆ A <;> simp [hX]
  rw [← Summable.tsum_finsetSum (s := A) (fun p _ ↦ hsummable p)]
  apply tsum_congr
  intro X
  by_cases hX : infinitePlaquetteMayerCarrier X ⊆ A
  · simp only [hX, if_true]
    exact sum_plaquetteRootedMayerTerm_eq_mayerClusterTerm Φ β A X hX
  · simp [hX]

/-- Uniform termwise majorization of rooted pressure coefficients on a
closed subdisk by the positive cardinality-majorant gas. -/
theorem norm_plaquetteRootedMayerTerm_le_majorant
    (Φ : RealPlaquettePotential G) (p : Plaquette d)
    (z : ℂ) (r : ℝ) (hz : ‖z‖ ≤ r)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) :
    ‖plaquetteRootedMayerTerm Φ z p X‖ ≤
      ‖if p ∈ infinitePlaquetteMayerCarrier X then
          CountablePolymerModel.mayerClusterTerm
            (infinitePlaquetteMajorantModel (d := d) Φ r) X /
              (infinitePlaquetteMayerCarrier X).card
        else 0‖ := by
  by_cases hp : p ∈ infinitePlaquetteMayerCarrier X
  · simp only [plaquetteRootedMayerTerm, hp, if_true, norm_div,
      Complex.norm_natCast]
    exact div_le_div_of_nonneg_right
      (norm_infinitePlaquetteMayerClusterTerm_le_majorant Φ z r hz X)
      (Nat.cast_nonneg _)
  · simp [plaquetteRootedMayerTerm, hp]

/-- The positive rooted majorant used on the closed radius-`r` disk. -/
def plaquetteRootedMajorantTerm
    (Φ : RealPlaquettePotential G) (r : ℝ) (p : Plaquette d)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) : ℂ :=
  if p ∈ infinitePlaquetteMayerCarrier X then
    CountablePolymerModel.mayerClusterTerm
      (infinitePlaquetteMajorantModel (d := d) Φ r) X /
        (infinitePlaquetteMayerCarrier X).card
  else 0

theorem summable_norm_plaquetteRootedMajorantTerm
    (Φ : RealPlaquettePotential G) (p : Plaquette d)
    {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < latticeStrongCouplingRadius d Φ.bound) :
    Summable (fun X ↦ ‖plaquetteRootedMajorantTerm Φ r p X‖) := by
  let M := infinitePlaquetteMajorantModel (d := d) Φ r
  let a : InfinitePlaquettePolymer d → ℝ :=
    fun γ ↦ (γ.support.card : ℝ) * Real.log 2
  let root := InfinitePlaquettePolymer.singleton p
  have hKP : M.FiniteRestrictionKPCertificate a :=
    infinitePlaquetteMajorantModel_finiteRestrictionKP Φ hr0 hr
  refine summable_of_sum_le (c := Real.log 2) (fun X ↦ norm_nonneg _) ?_
  intro U
  let S : Finset (InfinitePlaquettePolymer d) :=
    insert root (U.biUnion fun X ↦ X.support)
  have hsupport : ∀ X ∈ U, X.support ⊆ S := by
    intro X hX γ hγ
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨X, hX, hγ⟩)
  calc
    ∑ X ∈ U, ‖plaquetteRootedMajorantTerm Φ r p X‖ ≤
        ∑ X ∈ U, ∑ γ ∈ S, if p ∈ γ.support then
          M.pinnedNormMayerTerm γ X else 0 := by
      apply Finset.sum_le_sum
      intro X hX
      exact norm_rootedMayerTerm_le_pinned_sum_model M p X S (hsupport X hX)
    _ = ∑ γ ∈ S, ∑ X ∈ U, if p ∈ γ.support then
          M.pinnedNormMayerTerm γ X else 0 := by rw [Finset.sum_comm]
    _ ≤ ∑ γ ∈ S, if p ∈ γ.support then
          ‖M.activity γ‖ * Real.exp (a γ) else 0 := by
      apply Finset.sum_le_sum
      intro γ _
      by_cases hpγ : p ∈ γ.support
      · simp only [hpγ, if_true]
        exact M.sum_pinnedNormMayerTerm_le_of_finiteRestrictionKP a hKP γ U
      · simp [hpγ]
    _ ≤ ∑ γ ∈ S, M.incompatibleTiltedActivity a root γ := by
      apply Finset.sum_le_sum
      intro γ _
      by_cases hpγ : p ∈ γ.support
      · rw [if_pos hpγ]
        unfold CountablePolymerModel.incompatibleTiltedActivity
        rw [if_pos]
        exact singleton_incompatible_of_mem p γ hpγ
      · rw [if_neg hpγ]
        exact M.incompatibleTiltedActivity_nonneg a root γ
    _ ≤ a root :=
      M.sum_incompatibleTiltedActivity_le_of_finiteRestrictionKP a hKP root S
    _ = Real.log 2 := by simp [a, root]

/-- The anchored pressure series at a fixed plaquette is analytic throughout
the explicit strong-coupling disk by locally uniform KP majorization. -/
theorem analyticOnNhd_tsum_plaquetteRootedMayerTerm
    (Φ : RealPlaquettePotential G) (p : Plaquette d) :
    AnalyticOnNhd ℂ (fun z ↦ ∑' X, plaquetteRootedMayerTerm Φ z p X)
      (Metric.ball 0 (latticeStrongCouplingRadius d Φ.bound)) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro z hz
  have hz' : ‖z‖ < latticeStrongCouplingRadius d Φ.bound := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  obtain ⟨r, hzr, hr⟩ := exists_between hz'
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hzr.le
  let U : Set ℂ := Metric.ball 0 r
  have hU : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := by
    simpa only [U, Metric.mem_ball, dist_zero_right] using hzr
  have hsum := summable_norm_plaquetteRootedMajorantTerm Φ p hr0 hr
  have hdiff : DifferentiableOn ℂ
      (fun w ↦ ∑' X, plaquetteRootedMayerTerm Φ w p X) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
    · intro X
      exact (analyticOnNhd_plaquetteRootedMayerTerm Φ p X).differentiableOn.mono
        (Set.subset_univ U)
    · exact hU
    · intro X w hw
      apply norm_plaquetteRootedMayerTerm_le_majorant
      have hwr : ‖w‖ < r := by
        simpa only [U, Metric.mem_ball, dist_zero_right] using hw
      exact hwr.le
  exact (hdiff.differentiableAt (hU.mem_nhds hzU)).differentiableWithinAt

/-- Anchored infinite pressure series.  The sum over direction orbits at the
origin is per lattice site; dividing by the finite orbit count below gives
the pressure per ordered plaquette used by finite-volume normalization. -/
def anchoredPressurePerSite
    (Φ : RealPlaquettePotential G) (β : ℂ) : ℂ :=
  ∑ o : PlaquetteOrientation d, ∑' X, plaquetteRootedMayerTerm Φ β o.atOrigin X

/-- Thermodynamic pressure normalized per active ordered plaquette. -/
def anchoredPressure
    (Φ : RealPlaquettePotential G) (β : ℂ) : ℂ :=
  ((Fintype.card (PlaquetteOrientation d) : ℂ)⁻¹) *
    anchoredPressurePerSite (d := d) Φ β

/-- The per-site anchored pressure is analytic on the explicit
strong-coupling disk. -/
theorem analyticOnNhd_anchoredPressurePerSite
    (Φ : RealPlaquettePotential G) :
    AnalyticOnNhd ℂ (anchoredPressurePerSite (d := d) Φ)
      (Metric.ball 0 (latticeStrongCouplingRadius d Φ.bound)) := by
  unfold anchoredPressurePerSite
  exact Finset.analyticOnNhd_fun_sum Finset.univ fun o _ ↦
    analyticOnNhd_tsum_plaquetteRootedMayerTerm Φ o.atOrigin

/-- The thermodynamic pressure defined by the anchored cluster expansion is
analytic throughout the same explicit complex disk. -/
theorem analyticOnNhd_anchoredPressure
    (Φ : RealPlaquettePotential G) :
    AnalyticOnNhd ℂ (anchoredPressure (d := d) Φ)
      (Metric.ball 0 (latticeStrongCouplingRadius d Φ.bound)) := by
  unfold anchoredPressure
  exact analyticOnNhd_const.mul (analyticOnNhd_anchoredPressurePerSite Φ)

end

end YangMills.StrongCoupling
