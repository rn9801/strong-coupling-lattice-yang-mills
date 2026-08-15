/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.SpatialClusterExpansion

/-!
# Spatial support of decorated Mayer clusters

This file supplies the geometric half of the spatial cluster expansion.  It
uses an incidence graph obtained by adjoining the two observable roots to the
active-plaquette adjacency graph.  Every decorated polymer has a connected
carrier in this graph, and Mayer incompatibility joins the corresponding
carriers.  Thus a mixed connected Mayer term must span the two roots.

No influence-matrix or Dobrushin comparison argument is used here.
-/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Polymer

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-! ## The two-root plaquette incidence graph -/

/-- Active plaquettes together with the two abstract observable roots. -/
abbrev BivariateObservableSpatialVertex
    (Λ : FiniteSpecification d G) := ActivePlaquette Λ ⊕ Fin 2

/-- The active plaquettes incident to observable root `i`. -/
def bivariateObservableRootPlaquettes
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (i : Fin 2) : Finset (ActivePlaquette Λ) :=
  if i = 0 then observableRootPlaquettes Λ F else
    observableRootPlaquettes Λ H

/-- Plaquette adjacency with two additional root vertices.  A root is
adjacent exactly to the active plaquettes incident to its observable. -/
def bivariateObservableSpatialGraph
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G) :
    SimpleGraph (BivariateObservableSpatialVertex Λ) where
  Adj x y := match x, y with
    | Sum.inl p, Sum.inl q => (plaquetteAdjacencyGraph Λ).Adj p q
    | Sum.inl p, Sum.inr i => p ∈ bivariateObservableRootPlaquettes F H Λ i
    | Sum.inr i, Sum.inl p => p ∈ bivariateObservableRootPlaquettes F H Λ i
    | Sum.inr _, Sum.inr _ => False
  symm := by
    rintro (p | i) (q | j) h
    · exact h.symm
    · exact h
    · exact h
    · exact h
  loopless := by
    constructor
    rintro (p | i) h
    · exact (plaquetteAdjacencyGraph Λ).loopless.irrefl p h
    · exact h

instance (F H : LocalObservable d G) (Λ : FiniteSpecification d G) :
    DecidableRel (bivariateObservableSpatialGraph F H Λ).Adj :=
  Classical.decRel _

/-- Embed a finite untyped active-plaquette support into the spatial graph. -/
def liftPlaquetteSupport
    (Λ : FiniteSpecification d G) (S : Finset (Plaquette d)) :
    Finset (BivariateObservableSpatialVertex Λ) :=
  (activeSubset Λ S).map
    ⟨Sum.inl, fun _ _ h => Sum.inl_injective h⟩

theorem card_liftPlaquetteSupport
    (Λ : FiniteSpecification d G) (S : Finset (Plaquette d))
    (hS : S ⊆ Λ.activePlaquettes) :
    (liftPlaquetteSupport Λ S).card = S.card := by
  classical
  unfold liftPlaquetteSupport
  rw [Finset.card_map]
  have hmap := activeSubset_map_val_eq Λ S hS
  calc
    (activeSubset Λ S).card =
        ((activeSubset Λ S).map
          ⟨Subtype.val, Subtype.val_injective⟩).card :=
      (Finset.card_map _).symm
    _ = S.card := congrArg Finset.card hmap

/-- Untyped plaquette support represented by any one of the four decorated
polymer types. -/
def bivariateDecoratedObservablePlaquetteSupport
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G) :
    (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) → Finset (Plaquette d)
  | Sum.inl (Sum.inl (Sum.inl γ)) => γ.support
  | Sum.inl (Sum.inl (Sum.inr D)) => D.support
  | Sum.inl (Sum.inr E) => E.support
  | Sum.inr B => B.support

theorem bivariateDecoratedObservablePlaquetteSupport_subset_active
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (q : ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) :
    bivariateDecoratedObservablePlaquetteSupport F H Λ q ⊆
      Λ.activePlaquettes := by
  rcases q with ((γ | D) | E) | B
  · exact γ.support_subset_active
  · exact polymerFamilySupport_subset_active Λ D.1
  · exact polymerFamilySupport_subset_active Λ E.1
  · exact polymerFamilySupport_subset_active Λ B.1.1

/-- Spatial carrier of a decorated polymer.  One-sided decorations include
their root; bridge decorations include both roots. -/
def bivariateDecoratedObservableSpatialCarrier
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G) :
    (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) →
      Finset (BivariateObservableSpatialVertex Λ)
  | Sum.inl (Sum.inl (Sum.inl γ)) => liftPlaquetteSupport Λ γ.support
  | Sum.inl (Sum.inl (Sum.inr D)) =>
      insert (Sum.inr 0) (liftPlaquetteSupport Λ D.support)
  | Sum.inl (Sum.inr E) =>
      insert (Sum.inr 1) (liftPlaquetteSupport Λ E.support)
  | Sum.inr B =>
      insert (Sum.inr 0) (insert (Sum.inr 1)
        (liftPlaquetteSupport Λ B.support))

@[simp]
theorem bivariateDecoratedObservableSpatialCarrier_card
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (q : ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) :
    (bivariateDecoratedObservableSpatialCarrier F H Λ q).card =
      bivariateDecoratedObservablePlaquetteCardinality F H Λ q +
        bivariateDecoratedObservableRootGrading F H Λ q 0 +
        bivariateDecoratedObservableRootGrading F H Λ q 1 := by
  classical
  rcases q with ((γ | D) | E) | B
  · have hcard := card_liftPlaquetteSupport Λ γ.support
      γ.support_subset_active
    simpa [bivariateDecoratedObservableSpatialCarrier,
      bivariateDecoratedObservablePlaquetteCardinality,
      bivariateDecoratedObservableRootGrading, PlaquettePolymer.support] using hcard
  · have hcard := card_liftPlaquetteSupport Λ D.support
      (polymerFamilySupport_subset_active Λ D.1)
    have hroot : Sum.inr (0 : Fin 2) ∉ liftPlaquetteSupport Λ D.support := by
      simp [liftPlaquetteSupport]
    rw [bivariateDecoratedObservableSpatialCarrier,
      Finset.card_insert_of_notMem hroot, hcard]
    simp [bivariateDecoratedObservablePlaquetteCardinality,
      bivariateDecoratedObservableRootGrading]
  · have hcard := card_liftPlaquetteSupport Λ E.support
      (polymerFamilySupport_subset_active Λ E.1)
    have hroot : Sum.inr (1 : Fin 2) ∉ liftPlaquetteSupport Λ E.support := by
      simp [liftPlaquetteSupport]
    rw [bivariateDecoratedObservableSpatialCarrier,
      Finset.card_insert_of_notMem hroot, hcard]
    simp [bivariateDecoratedObservablePlaquetteCardinality,
      bivariateDecoratedObservableRootGrading]
  · have hcard := card_liftPlaquetteSupport Λ B.support
      (polymerFamilySupport_subset_active Λ B.1.1)
    have hroot0 : Sum.inr (0 : Fin 2) ∉
        insert (Sum.inr (1 : Fin 2)) (liftPlaquetteSupport Λ B.support) := by
      simp [liftPlaquetteSupport]
    have hroot1 : Sum.inr (1 : Fin 2) ∉ liftPlaquetteSupport Λ B.support := by
      simp [liftPlaquetteSupport]
    rw [bivariateDecoratedObservableSpatialCarrier,
      Finset.card_insert_of_notMem hroot0,
      Finset.card_insert_of_notMem hroot1, hcard]
    simp [bivariateDecoratedObservablePlaquetteCardinality,
      bivariateDecoratedObservableRootGrading]

/-- Union of the spatial carriers of every polymer type charged by a Mayer
multi-index. -/
def bivariateDecoratedMayerSpatialSupport
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration H Λ) ⊕
          TwoObservableBridgeDecoration F H Λ)) :
    Finset (BivariateObservableSpatialVertex Λ) :=
  X.support.biUnion (bivariateDecoratedObservableSpatialCarrier F H Λ)

/-- The spatial carrier contains at most the total charged plaquette
cardinality plus the two source degrees. -/
theorem card_bivariateDecoratedMayerSpatialSupport_le
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration H Λ) ⊕
          TwoObservableBridgeDecoration F H Λ)) :
    (bivariateDecoratedMayerSpatialSupport F H Λ X).card ≤
      FinitePolymerModel.weightedMultiplicity
          (bivariateDecoratedObservablePlaquetteCardinality F H Λ) X +
        FinitePolymerModel.bigradedMultiplicity
          (bivariateDecoratedObservableRootGrading F H Λ) X 0 +
        FinitePolymerModel.bigradedMultiplicity
          (bivariateDecoratedObservableRootGrading F H Λ) X 1 := by
  classical
  let weight := bivariateDecoratedObservablePlaquetteCardinality F H Λ
  let grading := bivariateDecoratedObservableRootGrading F H Λ
  calc
    (bivariateDecoratedMayerSpatialSupport F H Λ X).card ≤
        ∑ q ∈ X.support,
          (bivariateDecoratedObservableSpatialCarrier F H Λ q).card := by
      exact Finset.card_biUnion_le
    _ = ∑ q ∈ X.support, (weight q + grading q 0 + grading q 1) := by
      apply Finset.sum_congr rfl
      intro q _
      exact bivariateDecoratedObservableSpatialCarrier_card F H Λ q
    _ ≤ ∑ q : (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
          ObservableRootDecoration H Λ) ⊕
            TwoObservableBridgeDecoration F H Λ),
          (weight q + grading q 0 + grading q 1) * X q := by
      calc
        _ ≤ ∑ q ∈ X.support,
            (weight q + grading q 0 + grading q 1) * X q := by
          apply Finset.sum_le_sum
          intro q hq
          apply le_mul_of_one_le_right
          · exact Nat.zero_le _
          · exact Nat.one_le_iff_ne_zero.mpr
              ((Finsupp.mem_support_iff.mp hq))
        _ ≤ ∑ q ∈ (Finset.univ : Finset
              (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
                ObservableRootDecoration H Λ) ⊕
                  TwoObservableBridgeDecoration F H Λ)),
              (weight q + grading q 0 + grading q 1) * X q := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (by simp)
            (fun _ _ _ => Nat.zero_le _)
        _ = _ := by simp
    _ = _ := by
      simp only [add_mul, Finset.sum_add_distrib]
      rfl

/-! ## Connected carriers -/

/-- The lifted support of one plaquette polymer remains connected in the
two-root spatial graph. -/
theorem connected_induce_liftPlaquettePolymer
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (γ : PlaquettePolymer Λ) :
    ((bivariateObservableSpatialGraph F H Λ).induce
      (liftPlaquetteSupport Λ γ.support :
        Set (BivariateObservableSpatialVertex Λ))).Connected := by
  classical
  let f :
      ((plaquetteAdjacencyGraph Λ).induce
        (γ.1 : Set (ActivePlaquette Λ))) →g
      ((bivariateObservableSpatialGraph F H Λ).induce
        (liftPlaquetteSupport Λ γ.support :
          Set (BivariateObservableSpatialVertex Λ))) := {
    toFun p := ⟨Sum.inl p.1, by
      simp [liftPlaquetteSupport, activeSubset, PlaquettePolymer.support]⟩
    map_rel' := by
      intro p q hpq
      exact hpq
    }
  apply γ.2.2.map f
  rintro ⟨x, hx⟩
  rcases x with p | i
  · have hp : p.1 ∈ γ.support := by
      simpa [liftPlaquetteSupport, activeSubset] using hx
    have hpγ : p ∈ γ.1 := by
      simpa [PlaquettePolymer.support] using hp
    exact ⟨⟨p, hpγ⟩, rfl⟩
  · simp [liftPlaquetteSupport] at hx

theorem liftPlaquetteSupport_polymerFamilySupport
    (Λ : FiniteSpecification d G) (Γ : Finset (PlaquettePolymer Λ)) :
    liftPlaquetteSupport Λ (polymerFamilySupport Λ Γ) =
      Γ.biUnion (fun γ => liftPlaquetteSupport Λ γ.support) := by
  classical
  ext x
  rcases x with p | i
  · simp [liftPlaquetteSupport, activeSubset, polymerFamilySupport]
  · simp [liftPlaquetteSupport]

/-- A polymer touching the left observable supplies an edge from the left
root to its lifted plaquette support. -/
theorem exists_spatialRoot_zero_adj_of_observableRootTouches
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (γ : PlaquettePolymer Λ) (hγ : observableRootTouches F Λ γ) :
    ∃ x ∈ liftPlaquetteSupport Λ γ.support,
      (bivariateObservableSpatialGraph F H Λ).Adj (Sum.inr 0) x := by
  rcases (observableRootTouches_iff F Λ γ).mp hγ with ⟨p, hpγ, hpF⟩
  refine ⟨Sum.inl p, ?_, ?_⟩
  · simp [liftPlaquetteSupport, activeSubset, PlaquettePolymer.support, hpγ]
  · simpa [bivariateObservableSpatialGraph,
      bivariateObservableRootPlaquettes] using hpF

/-- A polymer touching the right observable supplies an edge from the right
root to its lifted plaquette support. -/
theorem exists_spatialRoot_one_adj_of_observableRootTouches
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (γ : PlaquettePolymer Λ) (hγ : observableRootTouches H Λ γ) :
    ∃ x ∈ liftPlaquetteSupport Λ γ.support,
      (bivariateObservableSpatialGraph F H Λ).Adj (Sum.inr 1) x := by
  rcases (observableRootTouches_iff H Λ γ).mp hγ with ⟨p, hpγ, hpH⟩
  refine ⟨Sum.inl p, ?_, ?_⟩
  · simp [liftPlaquetteSupport, activeSubset, PlaquettePolymer.support, hpγ]
  · simpa [bivariateObservableSpatialGraph,
      bivariateObservableRootPlaquettes] using hpH

/-- A finite carrier is linked to another when the carriers overlap or an
edge of the ambient graph joins them. -/
def SpatialCarriersLinked {V : Type*} [DecidableEq V]
    (K : SimpleGraph V) (S T : Finset V) : Prop :=
  (S ∩ T).Nonempty ∨ ∃ s ∈ S, ∃ t ∈ T, K.Adj s t

/-- The union of two connected linked carriers is connected. -/
theorem connected_induce_union_of_spatialCarriersLinked
    {V : Type*} [DecidableEq V] (K : SimpleGraph V)
    (S T : Finset V)
    (hS : (K.induce (S : Set V)).Connected)
    (hT : (K.induce (T : Set V)).Connected)
    (hlink : SpatialCarriersLinked K S T) :
    (K.induce ((S ∪ T : Finset V) : Set V)).Connected := by
  rcases hlink with hinter | ⟨s, hs, t, ht, hadj⟩
  · rw [Finset.coe_union]
    apply SimpleGraph.induce_union_connected hS.preconnected hT.preconnected
    rcases hinter with ⟨x, hx⟩
    exact ⟨x, by simpa using hx⟩
  · rw [Finset.coe_union]
    exact SimpleGraph.connected_induce_union hS.preconnected hT.preconnected
      hs ht hadj

/-- A finite family of connected patches, each adjacent to one hub vertex,
has connected union after the hub is inserted. -/
theorem connected_induce_insert_biUnion_of_root_adj
    {V Q : Type*} [DecidableEq V] [DecidableEq Q]
    (K : SimpleGraph V) (root : V) (Γ : Finset Q)
    (carrier : Q → Finset V)
    (hconnected : ∀ q ∈ Γ,
      (K.induce (carrier q : Set V)).Connected)
    (hadj : ∀ q ∈ Γ, ∃ x ∈ carrier q, K.Adj root x) :
    (K.induce ((insert root (Γ.biUnion carrier) : Finset V) : Set V)).Connected := by
  classical
  induction Γ using Finset.induction_on with
  | empty =>
      constructor
      · intro u v
        have huv : u = v := by
          apply Subtype.ext
          have hu : u.1 = root := by simpa using u.2
          have hv : v.1 = root := by simpa using v.2
          exact hu.trans hv.symm
        subst v
        exact SimpleGraph.Reachable.rfl
  | @insert q Γ hq ih =>
      have hΓconnected : ∀ r ∈ Γ,
          (K.induce (carrier r : Set V)).Connected := by
        intro r hr
        exact hconnected r (Finset.mem_insert_of_mem hr)
      have hΓadj : ∀ r ∈ Γ, ∃ x ∈ carrier r, K.Adj root x := by
        intro r hr
        exact hadj r (Finset.mem_insert_of_mem hr)
      have hbase := ih hΓconnected hΓadj
      have hqconnected := hconnected q (Finset.mem_insert_self q Γ)
      rcases hadj q (Finset.mem_insert_self q Γ) with ⟨x, hx, hrootx⟩
      have hlink : SpatialCarriersLinked K
          (insert root (Γ.biUnion carrier)) (carrier q) :=
        Or.inr ⟨root, by simp, x, hx, hrootx⟩
      have hunion := connected_induce_union_of_spatialCarriersLinked
        K (insert root (Γ.biUnion carrier)) (carrier q)
        hbase hqconnected hlink
      have heq : insert root ((insert q Γ).biUnion carrier) =
          insert root (Γ.biUnion carrier) ∪ carrier q := by
        ext x
        simp only [Finset.biUnion_insert, Finset.mem_insert, Finset.mem_union,
          Finset.mem_biUnion]
        aesop
      rw [heq]
      exact hunion

theorem connected_induce_singleton_finset
    {V : Type*} [DecidableEq V] (K : SimpleGraph V) (v : V) :
    (K.induce (({v} : Finset V) : Set V)).Connected := by
  letI : Nonempty {x // x ∈ ({v} : Finset V)} := ⟨⟨v, by simp⟩⟩
  constructor
  intro x y
  have hxy : x = y := by
    apply Subtype.ext
    have hx : x.1 = v := by simpa using x.2
    have hy : y.1 = v := by simpa using y.2
    exact hx.trans hy.symm
  subst y
  exact SimpleGraph.Reachable.rfl

/-- Connected patches linked to one fixed connected base have connected
total union. -/
theorem connected_induce_union_biUnion_of_linked_base
    {V Q : Type*} [DecidableEq V] [DecidableEq Q]
    (K : SimpleGraph V) (base : Finset V) (Γ : Finset Q)
    (carrier : Q → Finset V)
    (hbase : (K.induce (base : Set V)).Connected)
    (hconnected : ∀ q ∈ Γ,
      (K.induce (carrier q : Set V)).Connected)
    (hlink : ∀ q ∈ Γ, SpatialCarriersLinked K base (carrier q)) :
    (K.induce ((base ∪ Γ.biUnion carrier : Finset V) : Set V)).Connected := by
  classical
  induction Γ using Finset.induction_on with
  | empty =>
      have hempty : (∅ : Finset Q).biUnion carrier = ∅ := by
        ext x
        simp
      rw [hempty, Finset.union_empty]
      exact hbase
  | @insert q Γ hq ih =>
      have hrest := ih
        (fun r hr => hconnected r (Finset.mem_insert_of_mem hr))
        (fun r hr => hlink r (Finset.mem_insert_of_mem hr))
      have hqconnected := hconnected q (Finset.mem_insert_self q Γ)
      have hbaseSubset : base ⊆ base ∪ Γ.biUnion carrier :=
        Finset.subset_union_left
      have hqLinkBase := hlink q (Finset.mem_insert_self q Γ)
      have hqLinkRest : SpatialCarriersLinked K
          (base ∪ Γ.biUnion carrier) (carrier q) := by
        rcases hqLinkBase with hinter | ⟨s, hs, t, ht, hadj⟩
        · left
          rcases hinter with ⟨x, hx⟩
          exact ⟨x, by
            rw [Finset.mem_inter] at hx ⊢
            exact ⟨hbaseSubset hx.1, hx.2⟩⟩
        · exact Or.inr ⟨s, hbaseSubset hs, t, ht, hadj⟩
      have hunion := connected_induce_union_of_spatialCarriersLinked K
        (base ∪ Γ.biUnion carrier) (carrier q)
        hrest hqconnected hqLinkRest
      have heq : base ∪ (insert q Γ).biUnion carrier =
          (base ∪ Γ.biUnion carrier) ∪ carrier q := by
        ext x
        simp only [Finset.biUnion_insert, Finset.mem_union]
        tauto
      rw [heq]
      exact hunion

/-- The carrier of every complete left decoration is connected. -/
theorem connected_induce_leftDecorationSpatialCarrier
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (D : ObservableRootDecoration F Λ) :
    ((bivariateObservableSpatialGraph F H Λ).induce
      (bivariateDecoratedObservableSpatialCarrier F H Λ
        (Sum.inl (Sum.inl (Sum.inr D))) :
          Set (BivariateObservableSpatialVertex Λ))).Connected := by
  classical
  rw [bivariateDecoratedObservableSpatialCarrier]
  rw [ObservableRootDecoration.support]
  rw [liftPlaquetteSupport_polymerFamilySupport]
  apply connected_induce_insert_biUnion_of_root_adj
  · intro γ hγ
    exact connected_induce_liftPlaquettePolymer F H Λ γ
  · intro γ hγ
    exact exists_spatialRoot_zero_adj_of_observableRootTouches F H Λ γ
      (D.2.2 γ hγ)

/-- The carrier of every complete right decoration is connected. -/
theorem connected_induce_rightDecorationSpatialCarrier
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (E : ObservableRootDecoration H Λ) :
    ((bivariateObservableSpatialGraph F H Λ).induce
      (bivariateDecoratedObservableSpatialCarrier F H Λ
        (Sum.inl (Sum.inr E)) :
          Set (BivariateObservableSpatialVertex Λ))).Connected := by
  classical
  rw [bivariateDecoratedObservableSpatialCarrier]
  rw [ObservableRootDecoration.support]
  rw [liftPlaquetteSupport_polymerFamilySupport]
  apply connected_induce_insert_biUnion_of_root_adj
  · intro γ hγ
    exact connected_induce_liftPlaquettePolymer F H Λ γ
  · intro γ hγ
    exact exists_spatialRoot_one_adj_of_observableRootTouches F H Λ γ
      (E.2.2 γ hγ)

/-- The carrier of an intrinsic two-observable bridge decoration is
connected and contains both abstract roots. -/
theorem connected_induce_bridgeDecorationSpatialCarrier
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (B : TwoObservableBridgeDecoration F H Λ) :
    ((bivariateObservableSpatialGraph F H Λ).induce
      (bivariateDecoratedObservableSpatialCarrier F H Λ (Sum.inr B) :
        Set (BivariateObservableSpatialVertex Λ))).Connected := by
  classical
  rcases B.2 with ⟨γ, hγB, hγF, hγH⟩
  let K := bivariateObservableSpatialGraph F H Λ
  let root0 : BivariateObservableSpatialVertex Λ := Sum.inr 0
  let root1 : BivariateObservableSpatialVertex Λ := Sum.inr 1
  let γcarrier := liftPlaquetteSupport Λ γ.support
  have hγconnected : (K.induce (γcarrier : Set _)).Connected := by
    exact connected_induce_liftPlaquettePolymer F H Λ γ
  rcases exists_spatialRoot_zero_adj_of_observableRootTouches
      F H Λ γ hγF with ⟨x0, hx0, hroot0⟩
  have hroot0connected := connected_induce_singleton_finset K root0
  have hlink0 : SpatialCarriersLinked K ({root0} : Finset _) γcarrier :=
    Or.inr ⟨root0, by simp, x0, hx0, hroot0⟩
  have hbase0 := connected_induce_union_of_spatialCarriersLinked K
    ({root0} : Finset _) γcarrier hroot0connected hγconnected hlink0
  rcases exists_spatialRoot_one_adj_of_observableRootTouches
      F H Λ γ hγH with ⟨x1, hx1, hroot1⟩
  have hroot1connected := connected_induce_singleton_finset K root1
  have hlink1 : SpatialCarriersLinked K ({root1} : Finset _)
      ({root0} ∪ γcarrier) :=
    Or.inr ⟨root1, by simp, x1, by
      exact Finset.mem_union_right _ hx1, hroot1⟩
  have hbase := connected_induce_union_of_spatialCarriersLinked K
    ({root1} : Finset _) ({root0} ∪ γcarrier)
    hroot1connected hbase0 hlink1
  let base : Finset (BivariateObservableSpatialVertex Λ) :=
    {root1} ∪ ({root0} ∪ γcarrier)
  have hpatchConnected : ∀ δ ∈ B.1.1,
      (K.induce (liftPlaquetteSupport Λ δ.support : Set _)).Connected := by
    intro δ _
    exact connected_induce_liftPlaquettePolymer F H Λ δ
  have hpatchLinked : ∀ δ ∈ B.1.1,
      SpatialCarriersLinked K base (liftPlaquetteSupport Λ δ.support) := by
    intro δ hδ
    have htouch := (observableRootTouches_mul_iff F H Λ δ).mp
      (B.1.2.2 δ hδ)
    rcases htouch with hδF | hδH
    · rcases exists_spatialRoot_zero_adj_of_observableRootTouches
        F H Λ δ hδF with ⟨x, hx, hadj⟩
      exact Or.inr ⟨root0, by simp [base], x, hx, hadj⟩
    · rcases exists_spatialRoot_one_adj_of_observableRootTouches
        F H Λ δ hδH with ⟨x, hx, hadj⟩
      exact Or.inr ⟨root1, by simp [base], x, hx, hadj⟩
  have hall := connected_induce_union_biUnion_of_linked_base K base B.1.1
    (fun δ => liftPlaquetteSupport Λ δ.support) hbase
    hpatchConnected hpatchLinked
  let patches := B.1.1.biUnion fun δ => liftPlaquetteSupport Λ δ.support
  have hγsubset : γcarrier ⊆ patches := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨γ, hγB, hx⟩
  rw [bivariateDecoratedObservableSpatialCarrier,
    TwoObservableBridgeDecoration.support,
    ObservableRootDecoration.support,
    liftPlaquetteSupport_polymerFamilySupport]
  have heq : insert root0 (insert root1 patches) = base ∪ patches := by
    ext x
    simp only [base, Finset.mem_insert, Finset.mem_union,
      Finset.mem_singleton]
    constructor
    · tauto
    · intro hx
      rcases hx with (hx1 | hx0 | hxγ) | hxpatch
      · exact Or.inr (Or.inl hx1)
      · exact Or.inl hx0
      · exact Or.inr (Or.inr (hγsubset hxγ))
      · exact Or.inr (Or.inr hxpatch)
  have hresult := heq.symm ▸ hall
  dsimp only [K, root0, root1, patches] at hresult
  exact hresult

/-- Every one of the four decorated polymer types has a connected spatial
carrier. -/
theorem connected_induce_bivariateDecoratedObservableSpatialCarrier
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (q : ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) :
    ((bivariateObservableSpatialGraph F H Λ).induce
      (bivariateDecoratedObservableSpatialCarrier F H Λ q : Set _)).Connected := by
  rcases q with ((γ | D) | E) | B
  · exact connected_induce_liftPlaquettePolymer F H Λ γ
  · exact connected_induce_leftDecorationSpatialCarrier F H Λ D
  · exact connected_induce_rightDecorationSpatialCarrier F H Λ E
  · exact connected_induce_bridgeDecorationSpatialCarrier F H Λ B

/-! ## Mayer incompatibility links spatial carriers -/

theorem SpatialCarriersLinked.symm
    {V : Type*} [DecidableEq V] {K : SimpleGraph V} {S T : Finset V}
    (h : SpatialCarriersLinked K S T) : SpatialCarriersLinked K T S := by
  rcases h with hinter | ⟨s, hs, t, ht, hadj⟩
  · left
    simpa [Finset.inter_comm] using hinter
  · exact Or.inr ⟨t, ht, s, hs, hadj.symm⟩

theorem liftPlaquetteSupport_mono
    (Λ : FiniteSpecification d G) {S T : Finset (Plaquette d)}
    (hST : S ⊆ T) : liftPlaquetteSupport Λ S ⊆ liftPlaquetteSupport Λ T := by
  classical
  intro x hx
  rcases x with p | i
  · have hp : p.1 ∈ S := by
      simpa [liftPlaquetteSupport, activeSubset] using hx
    have hp' : p.1 ∈ T := hST hp
    simpa [liftPlaquetteSupport, activeSubset] using hp'
  · simp [liftPlaquetteSupport] at hx

theorem liftPlaquetteSupport_subset_leftDecorationCarrier
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (D : ObservableRootDecoration F Λ) {γ : PlaquettePolymer Λ}
    (hγ : γ ∈ D.1) :
    liftPlaquetteSupport Λ γ.support ⊆
      bivariateDecoratedObservableSpatialCarrier F H Λ
        (Sum.inl (Sum.inl (Sum.inr D))) := by
  intro x hx
  apply Finset.mem_insert_of_mem
  apply liftPlaquetteSupport_mono Λ
  · intro p hp
    exact (mem_polymerFamilySupport_iff Λ D.1 p).mpr ⟨γ, hγ, hp⟩
  · exact hx

theorem liftPlaquetteSupport_subset_rightDecorationCarrier
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (E : ObservableRootDecoration H Λ) {γ : PlaquettePolymer Λ}
    (hγ : γ ∈ E.1) :
    liftPlaquetteSupport Λ γ.support ⊆
      bivariateDecoratedObservableSpatialCarrier F H Λ
        (Sum.inl (Sum.inr E)) := by
  intro x hx
  apply Finset.mem_insert_of_mem
  apply liftPlaquetteSupport_mono Λ
  · intro p hp
    exact (mem_polymerFamilySupport_iff Λ E.1 p).mpr ⟨γ, hγ, hp⟩
  · exact hx

theorem liftPlaquetteSupport_subset_bridgeDecorationCarrier
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (B : TwoObservableBridgeDecoration F H Λ) {γ : PlaquettePolymer Λ}
    (hγ : γ ∈ B.1.1) :
    liftPlaquetteSupport Λ γ.support ⊆
      bivariateDecoratedObservableSpatialCarrier F H Λ (Sum.inr B) := by
  intro x hx
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  apply liftPlaquetteSupport_mono Λ
  · intro p hp
    exact (mem_polymerFamilySupport_iff Λ B.1.1 p).mpr ⟨γ, hγ, hp⟩
  · exact hx

/-- Incompatible bulk polymers overlap or have a plaquette-adjacency edge
between their lifted supports. -/
theorem spatialCarriersLinked_of_plaquettePolymerIncompatible
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    {γ δ : PlaquettePolymer Λ}
    (h : plaquettePolymerIncompatible Λ γ δ) :
    SpatialCarriersLinked (bivariateObservableSpatialGraph F H Λ)
      (liftPlaquetteSupport Λ γ.support)
      (liftPlaquetteSupport Λ δ.support) := by
  rcases h with ⟨p, hpγ, q, hqδ, hpq | hpq⟩
  · subst q
    left
    refine ⟨Sum.inl p, ?_⟩
    rw [Finset.mem_inter]
    constructor <;>
      simp [liftPlaquetteSupport, activeSubset, PlaquettePolymer.support, *]
  · right
    refine ⟨Sum.inl p, ?_, Sum.inl q, ?_, ?_⟩
    · simp [liftPlaquetteSupport, activeSubset, PlaquettePolymer.support, hpγ]
    · simp [liftPlaquetteSupport, activeSubset, PlaquettePolymer.support, hqδ]
    · exact hpq

theorem spatialCarriersLinked_leftDecoration_bulk
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (D : ObservableRootDecoration F Λ) (γ : PlaquettePolymer Λ)
    (h : observableRootDecorationTouches F Λ D γ) :
    SpatialCarriersLinked (bivariateObservableSpatialGraph F H Λ)
      (bivariateDecoratedObservableSpatialCarrier F H Λ
        (Sum.inl (Sum.inl (Sum.inr D))))
      (liftPlaquetteSupport Λ γ.support) := by
  rcases h with htouch | ⟨δ, hδD, hδγ⟩
  · rcases exists_spatialRoot_zero_adj_of_observableRootTouches
      F H Λ γ htouch with ⟨x, hx, hadj⟩
    exact Or.inr ⟨Sum.inr 0, by
      simp [bivariateDecoratedObservableSpatialCarrier], x, hx, hadj⟩
  · rcases spatialCarriersLinked_of_plaquettePolymerIncompatible
      F H Λ hδγ with hinter | ⟨s, hs, t, ht, hadj⟩
    · left
      rcases hinter with ⟨x, hx⟩
      have hx' := Finset.mem_inter.mp hx
      exact ⟨x, Finset.mem_inter.mpr
        ⟨liftPlaquetteSupport_subset_leftDecorationCarrier
          F H Λ D hδD hx'.1, hx'.2⟩⟩
    · exact Or.inr ⟨s,
        liftPlaquetteSupport_subset_leftDecorationCarrier
          F H Λ D hδD hs, t, ht, hadj⟩

theorem spatialCarriersLinked_rightDecoration_bulk
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (E : ObservableRootDecoration H Λ) (γ : PlaquettePolymer Λ)
    (h : observableRootDecorationTouches H Λ E γ) :
    SpatialCarriersLinked (bivariateObservableSpatialGraph F H Λ)
      (bivariateDecoratedObservableSpatialCarrier F H Λ
        (Sum.inl (Sum.inr E)))
      (liftPlaquetteSupport Λ γ.support) := by
  rcases h with htouch | ⟨δ, hδE, hδγ⟩
  · rcases exists_spatialRoot_one_adj_of_observableRootTouches
      F H Λ γ htouch with ⟨x, hx, hadj⟩
    exact Or.inr ⟨Sum.inr 1, by
      simp [bivariateDecoratedObservableSpatialCarrier], x, hx, hadj⟩
  · rcases spatialCarriersLinked_of_plaquettePolymerIncompatible
      F H Λ hδγ with hinter | ⟨s, hs, t, ht, hadj⟩
    · left
      rcases hinter with ⟨x, hx⟩
      have hx' := Finset.mem_inter.mp hx
      exact ⟨x, Finset.mem_inter.mpr
        ⟨liftPlaquetteSupport_subset_rightDecorationCarrier
          F H Λ E hδE hx'.1, hx'.2⟩⟩
    · exact Or.inr ⟨s,
        liftPlaquetteSupport_subset_rightDecorationCarrier
          F H Λ E hδE hs, t, ht, hadj⟩

theorem spatialCarriersLinked_leftDecoration_rightDecoration
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (D : ObservableRootDecoration F Λ)
    (E : ObservableRootDecoration H Λ)
    (h : observableRootDecorationsCrossIncompatible F H Λ D E) :
    SpatialCarriersLinked (bivariateObservableSpatialGraph F H Λ)
      (bivariateDecoratedObservableSpatialCarrier F H Λ
        (Sum.inl (Sum.inl (Sum.inr D))))
      (bivariateDecoratedObservableSpatialCarrier F H Λ
        (Sum.inl (Sum.inr E))) := by
  rcases h with ⟨γ, hγD, hγH⟩ |
      ⟨δ, hδE, hδF⟩ | ⟨γ, hγD, δ, hδE, hγδ⟩
  · rcases exists_spatialRoot_one_adj_of_observableRootTouches
      F H Λ γ hγH with ⟨x, hx, hadj⟩
    exact Or.inr ⟨x,
      liftPlaquetteSupport_subset_leftDecorationCarrier F H Λ D hγD hx,
      Sum.inr 1, by simp [bivariateDecoratedObservableSpatialCarrier],
      hadj.symm⟩
  · rcases exists_spatialRoot_zero_adj_of_observableRootTouches
      F H Λ δ hδF with ⟨x, hx, hadj⟩
    exact Or.inr ⟨Sum.inr 0,
      by simp [bivariateDecoratedObservableSpatialCarrier], x,
      liftPlaquetteSupport_subset_rightDecorationCarrier F H Λ E hδE hx,
      hadj⟩
  · rcases spatialCarriersLinked_of_plaquettePolymerIncompatible
      F H Λ hγδ with hinter | ⟨s, hs, t, ht, hadj⟩
    · left
      rcases hinter with ⟨x, hx⟩
      have hx' := Finset.mem_inter.mp hx
      exact ⟨x, Finset.mem_inter.mpr
        ⟨liftPlaquetteSupport_subset_leftDecorationCarrier
            F H Λ D hγD hx'.1,
          liftPlaquetteSupport_subset_rightDecorationCarrier
            F H Λ E hδE hx'.2⟩⟩
    · exact Or.inr ⟨s,
        liftPlaquetteSupport_subset_leftDecorationCarrier F H Λ D hγD hs,
        t, liftPlaquetteSupport_subset_rightDecorationCarrier
          F H Λ E hδE ht, hadj⟩

theorem spatialCarriersLinked_bridgeDecoration_bulk
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (B : TwoObservableBridgeDecoration F H Λ) (γ : PlaquettePolymer Λ)
    (h : observableRootDecorationTouches (F.mul H) Λ B.1 γ) :
    SpatialCarriersLinked (bivariateObservableSpatialGraph F H Λ)
      (bivariateDecoratedObservableSpatialCarrier F H Λ (Sum.inr B))
      (liftPlaquetteSupport Λ γ.support) := by
  rcases h with htouch | ⟨δ, hδB, hδγ⟩
  · rcases (observableRootTouches_mul_iff F H Λ γ).mp htouch with hγF | hγH
    · rcases exists_spatialRoot_zero_adj_of_observableRootTouches
        F H Λ γ hγF with ⟨x, hx, hadj⟩
      exact Or.inr ⟨Sum.inr 0, by
        simp [bivariateDecoratedObservableSpatialCarrier], x, hx, hadj⟩
    · rcases exists_spatialRoot_one_adj_of_observableRootTouches
        F H Λ γ hγH with ⟨x, hx, hadj⟩
      exact Or.inr ⟨Sum.inr 1, by
        simp [bivariateDecoratedObservableSpatialCarrier], x, hx, hadj⟩
  · rcases spatialCarriersLinked_of_plaquettePolymerIncompatible
      F H Λ hδγ with hinter | ⟨s, hs, t, ht, hadj⟩
    · left
      rcases hinter with ⟨x, hx⟩
      have hx' := Finset.mem_inter.mp hx
      exact ⟨x, Finset.mem_inter.mpr
        ⟨liftPlaquetteSupport_subset_bridgeDecorationCarrier
          F H Λ B hδB hx'.1, hx'.2⟩⟩
    · exact Or.inr ⟨s,
        liftPlaquetteSupport_subset_bridgeDecorationCarrier
          F H Λ B hδB hs, t, ht, hadj⟩

/-- Every incompatibility edge of the exact decorated gas links the two
spatial carriers. -/
theorem bivariateDecoratedObservableSpatialCarriers_linked_of_incompatible
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (q r : ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ)
    (h : (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).incompatible q r) :
    SpatialCarriersLinked (bivariateObservableSpatialGraph F H Λ)
      (bivariateDecoratedObservableSpatialCarrier F H Λ q)
      (bivariateDecoratedObservableSpatialCarrier F H Λ r) := by
  rcases q with ((γ | D) | E) | B <;>
    rcases r with ((δ | D') | E') | B'
  · exact spatialCarriersLinked_of_plaquettePolymerIncompatible F H Λ h
  · exact (spatialCarriersLinked_leftDecoration_bulk F H Λ D' γ h).symm
  · exact (spatialCarriersLinked_rightDecoration_bulk F H Λ E' γ h).symm
  · exact (spatialCarriersLinked_bridgeDecoration_bulk F H Λ B' γ h).symm
  · exact spatialCarriersLinked_leftDecoration_bulk F H Λ D δ h
  · left
    exact ⟨Sum.inr 0, by
      simp [bivariateDecoratedObservableSpatialCarrier]⟩
  · exact spatialCarriersLinked_leftDecoration_rightDecoration F H Λ D E' h
  · left
    exact ⟨Sum.inr 0, by
      simp [bivariateDecoratedObservableSpatialCarrier]⟩
  · exact spatialCarriersLinked_rightDecoration_bulk F H Λ E δ h
  · exact (spatialCarriersLinked_leftDecoration_rightDecoration
      F H Λ D' E h).symm
  · left
    exact ⟨Sum.inr 1, by
      simp [bivariateDecoratedObservableSpatialCarrier]⟩
  · left
    exact ⟨Sum.inr 1, by
      simp [bivariateDecoratedObservableSpatialCarrier]⟩
  · exact spatialCarriersLinked_bridgeDecoration_bulk F H Λ B δ h
  · left
    exact ⟨Sum.inr 0, by
      simp [bivariateDecoratedObservableSpatialCarrier]⟩
  · left
    exact ⟨Sum.inr 1, by
      simp [bivariateDecoratedObservableSpatialCarrier]⟩
  · left
    exact ⟨Sum.inr 0, by
      simp [bivariateDecoratedObservableSpatialCarrier]⟩

/-! ## Connected carrier of a Mayer walk -/

theorem SpatialCarriersLinked.mono_right
    {V : Type*} [DecidableEq V] {K : SimpleGraph V}
    {S T U : Finset V} (h : SpatialCarriersLinked K S T) (hTU : T ⊆ U) :
    SpatialCarriersLinked K S U := by
  rcases h with hinter | ⟨s, hs, t, ht, hadj⟩
  · left
    rcases hinter with ⟨x, hx⟩
    have hx' := Finset.mem_inter.mp hx
    exact ⟨x, Finset.mem_inter.mpr ⟨hx'.1, hTU hx'.2⟩⟩
  · exact Or.inr ⟨s, hs, t, hTU ht, hadj⟩

/-- Spatial support swept out by the labelled occurrences along a Mayer
walk. -/
def bivariateDecoratedMayerWalkSpatialSupport
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    {X : FinitePolymerModel.MayerMultiIndex
      (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration H Λ) ⊕
          TwoObservableBridgeDecoration F H Λ)}
    {u v : FinitePolymerModel.MayerVertex X}
    (path : ((bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).mayerIncompatibilityGraph
      X).Walk u v) :
    Finset (BivariateObservableSpatialVertex Λ) :=
  path.support.toFinset.biUnion fun w =>
    bivariateDecoratedObservableSpatialCarrier F H Λ w.1

theorem bivariateDecoratedMayerWalkSpatialSupport_connected
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    {X : FinitePolymerModel.MayerMultiIndex
      (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration H Λ) ⊕
          TwoObservableBridgeDecoration F H Λ)}
    {u v : FinitePolymerModel.MayerVertex X}
    (path : ((bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).mayerIncompatibilityGraph
      X).Walk u v) :
    ((bivariateObservableSpatialGraph F H Λ).induce
      (bivariateDecoratedMayerWalkSpatialSupport F H Λ Φ β path :
        Set (BivariateObservableSpatialVertex Λ))).Connected := by
  classical
  induction path with
  | @nil u0 =>
      rw [bivariateDecoratedMayerWalkSpatialSupport]
      rw [SimpleGraph.Walk.support_nil]
      have heq : [u0].toFinset.biUnion (fun w =>
          bivariateDecoratedObservableSpatialCarrier F H Λ w.1) =
          bivariateDecoratedObservableSpatialCarrier F H Λ u0.1 := by
        ext x
        simp
      rw [heq]
      exact connected_induce_bivariateDecoratedObservableSpatialCarrier
        F H Λ u0.1
  | @cons u w v hadj path ih =>
      let carrier := bivariateDecoratedObservableSpatialCarrier F H Λ
      let tailSupport :=
        bivariateDecoratedMayerWalkSpatialSupport F H Λ Φ β path
      have hw : w ∈ path.support.toFinset := by
        simp
      have hwSubset : carrier w.1 ⊆ tailSupport := by
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨w, hw, hx⟩
      have hlink0 :=
        bivariateDecoratedObservableSpatialCarriers_linked_of_incompatible
          F H Λ Φ β u.1 w.1 hadj.2
      have hlink : SpatialCarriersLinked
          (bivariateObservableSpatialGraph F H Λ)
          (carrier u.1) tailSupport := hlink0.mono_right hwSubset
      have hhead :=
        connected_induce_bivariateDecoratedObservableSpatialCarrier
          F H Λ u.1
      have hunion := connected_induce_union_of_spatialCarriersLinked
        (bivariateObservableSpatialGraph F H Λ)
        (carrier u.1) tailSupport hhead ih hlink
      rw [bivariateDecoratedMayerWalkSpatialSupport]
      rw [SimpleGraph.Walk.support_cons]
      have heq : (u :: path.support).toFinset.biUnion (fun z =>
          bivariateDecoratedObservableSpatialCarrier F H Λ z.1) =
          carrier u.1 ∪ tailSupport := by
        ext x
        simp [carrier, tailSupport,
          bivariateDecoratedMayerWalkSpatialSupport]
      rw [heq]
      exact hunion

theorem bivariateDecoratedMayerWalkSpatialSupport_subset
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    {X : FinitePolymerModel.MayerMultiIndex
      (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration H Λ) ⊕
          TwoObservableBridgeDecoration F H Λ)}
    {u v : FinitePolymerModel.MayerVertex X}
    (path : ((bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).mayerIncompatibilityGraph
      X).Walk u v) :
    bivariateDecoratedMayerWalkSpatialSupport F H Λ Φ β path ⊆
      bivariateDecoratedMayerSpatialSupport F H Λ X := by
  classical
  intro x hx
  rw [bivariateDecoratedMayerWalkSpatialSupport] at hx
  rcases Finset.mem_biUnion.mp hx with ⟨w, hw, hxcarrier⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨w.1, ?_, hxcarrier⟩
  exact FinitePolymerModel.mayerVertex_fst_mem_support w

/-! ## Spatial support bound for a nonzero mixed Mayer term -/

/-- Distance inside a connected finite vertex carrier is strictly smaller
than the carrier cardinality. -/
theorem graph_dist_lt_card_of_connected_finset
    {V : Type*} [DecidableEq V] (K : SimpleGraph V) (S : Finset V)
    (hconnected : (K.induce (S : Set V)).Connected)
    (u v : V) (hu : u ∈ S) (hv : v ∈ S) :
    K.dist u v < S.card := by
  classical
  let uS : (S : Set V) := ⟨u, hu⟩
  let vS : (S : Set V) := ⟨v, hv⟩
  obtain ⟨path, hpath⟩ := hconnected.exists_isPath uS vS
  let path' := path.map (SimpleGraph.Embedding.induce (S : Set V)).toHom
  have hdist : K.dist u v ≤ path'.length := by
    simpa [path', uS, vS] using SimpleGraph.dist_le path'
  have hlength : path.length < S.card := by
    simpa using hpath.length_lt
  have hdist' : K.dist u v ≤ path.length := by
    simpa only [path', SimpleGraph.Walk.length_map] using hdist
  exact hdist'.trans_lt hlength

/-- Plaquette-incidence separation of two observable roots.  The subtraction
removes the two root-to-plaquette edges, so this is the ordinary plaquette
chain length between the two incident root sets whenever such a chain
exists. -/
def bivariateObservablePlaquetteSeparation
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G) : ℕ :=
  (bivariateObservableSpatialGraph F H Λ).dist
    (Sum.inr 0) (Sum.inr 1) - 2

/-- The geometric support property needed for exponential clustering: every
nonzero mixed `(1,1)` Mayer term has total charged plaquette cardinality at
least the plaquette-incidence separation of the two observable roots. -/
theorem bivariateDecorated_mixed_nonzero_spatialSeparation_le_weightedMultiplicity
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : FinitePolymerModel.MayerMultiIndex
      (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration H Λ) ⊕
          TwoObservableBridgeDecoration F H Λ))
    (hzero : FinitePolymerModel.bigradedMultiplicity
      (bivariateDecoratedObservableRootGrading F H Λ) X 0 = 1)
    (hone : FinitePolymerModel.bigradedMultiplicity
      (bivariateDecoratedObservableRootGrading F H Λ) X 1 = 1)
    (hterm : (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).mayerClusterTerm
      X ≠ 0) :
    bivariateObservablePlaquetteSeparation F H Λ ≤
      FinitePolymerModel.weightedMultiplicity
        (bivariateDecoratedObservablePlaquetteCardinality F H Λ) X := by
  classical
  let K := bivariateObservableSpatialGraph F H Λ
  let root0 : BivariateObservableSpatialVertex Λ := Sum.inr 0
  let root1 : BivariateObservableSpatialVertex Λ := Sum.inr 1
  let global := bivariateDecoratedMayerSpatialSupport F H Λ X
  let total := FinitePolymerModel.weightedMultiplicity
    (bivariateDecoratedObservablePlaquetteCardinality F H Λ) X
  have hglobalCard : global.card ≤ total + 2 := by
    have hcard := card_bivariateDecoratedMayerSpatialSupport_le F H Λ X
    rw [hzero, hone] at hcard
    simpa [global, total, Nat.add_assoc] using hcard
  have finish {S : Finset (BivariateObservableSpatialVertex Λ)}
      (hSconnected : (K.induce (S : Set _)).Connected)
      (hroot0 : root0 ∈ S) (hroot1 : root1 ∈ S)
      (hSglobal : S ⊆ global) :
      bivariateObservablePlaquetteSeparation F H Λ ≤ total := by
    have hdistS := graph_dist_lt_card_of_connected_finset K S
      hSconnected root0 root1 hroot0 hroot1
    have hcardS : S.card ≤ global.card := Finset.card_le_card hSglobal
    have hdist : K.dist root0 root1 < total + 2 :=
      hdistS.trans_le (hcardS.trans hglobalCard)
    dsimp only [K, root0, root1] at hdist
    dsimp only [bivariateObservablePlaquetteSeparation, K, root0, root1]
    omega
  rcases bivariateDecorated_mixed_nonzero_spanning_witness
      F H Λ Φ β X hzero hone hterm with
    ⟨B, hB⟩ | ⟨D, E, hD, hE, path, _hpath⟩
  · let S := bivariateDecoratedObservableSpatialCarrier F H Λ (Sum.inr B)
    have hBsupport : Sum.inr B ∈ X.support := by
      rw [Finsupp.mem_support_iff]
      omega
    have hSglobal : S ⊆ global := by
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨Sum.inr B, hBsupport, hx⟩
    apply finish
        (connected_induce_bridgeDecorationSpatialCarrier F H Λ B)
        (by
          dsimp only [root0, S,
            bivariateDecoratedObservableSpatialCarrier]
          exact Finset.mem_insert_self _ _)
        (by
          dsimp only [root1, S,
            bivariateDecoratedObservableSpatialCarrier]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        hSglobal
  · let S := bivariateDecoratedMayerWalkSpatialSupport F H Λ Φ β path
    have hstart : bivariateDecoratedLeftRootVertex F H Λ X D hD ∈
        path.support.toFinset := by
      simp
    have hend : bivariateDecoratedRightRootVertex F H Λ X E hE ∈
        path.support.toFinset := by
      simp
    have hroot0S : root0 ∈ S := by
      apply Finset.mem_biUnion.mpr
      refine ⟨bivariateDecoratedLeftRootVertex F H Λ X D hD,
        hstart, ?_⟩
      simp [root0, bivariateDecoratedLeftRootVertex,
        bivariateDecoratedObservableSpatialCarrier]
    have hroot1S : root1 ∈ S := by
      apply Finset.mem_biUnion.mpr
      refine ⟨bivariateDecoratedRightRootVertex F H Λ X E hE,
        hend, ?_⟩
      simp [root1, bivariateDecoratedRightRootVertex,
        bivariateDecoratedObservableSpatialCarrier]
    exact finish
      (bivariateDecoratedMayerWalkSpatialSupport_connected
        F H Λ Φ β path)
      hroot0S hroot1S
      (bivariateDecoratedMayerWalkSpatialSupport_subset
        F H Λ Φ β path)

/-- The geometric support theorem, summed over one total Mayer degree.  A
mixed cluster pays one factor of `t` for every unit of observable
separation, while the right-hand side retains the full plaquette-cardinality
tilt needed by the explicit KP certificate. -/
theorem pow_spatialSeparation_mul_bivariateDecoratedMixedNormDegreeSum_le
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) {t : ℝ} (ht : 1 ≤ t)
    (n : ℕ) :
    t ^ bivariateObservablePlaquetteSeparation F H Λ *
        (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).bigradedMixedNormDegreeSum
          (bivariateDecoratedObservableRootGrading F H Λ) n ≤
      (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).bigradedMixedWeightedNormDegreeSum
        (bivariateDecoratedObservableRootGrading F H Λ)
        (bivariateDecoratedObservablePlaquetteCardinality F H Λ) t n := by
  classical
  unfold FinitePolymerModel.bigradedMixedNormDegreeSum
    FinitePolymerModel.bigradedMixedWeightedNormDegreeSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro X _hX
  by_cases hdegree :
      FinitePolymerModel.bigradedMultiplicity
          (bivariateDecoratedObservableRootGrading F H Λ) X 0 = 1 ∧
        FinitePolymerModel.bigradedMultiplicity
          (bivariateDecoratedObservableRootGrading F H Λ) X 1 = 1
  · rw [if_pos hdegree, if_pos hdegree]
    by_cases hterm :
        (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).mayerClusterTerm
          X = 0
    · simp [hterm]
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ ht
          (bivariateDecorated_mixed_nonzero_spatialSeparation_le_weightedMultiplicity
            F H Λ Φ β X hdegree.1 hdegree.2 hterm))
        (norm_nonneg _)
  · simp [hdegree]

/-- Absolute summability of the full weighted mixed series, including its
degree-zero term. -/
theorem summable_bivariateDecoratedObservableMixedCardinalityWeightedNormDegreeSum
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let M := bivariateDecoratedObservableRootModel F H Λ Φ β 1 1
    let grading := bivariateDecoratedObservableRootGrading F H Λ
    let weight := bivariateDecoratedObservablePlaquetteCardinality F H Λ
    let t := plaquetteCardinalityTilt (d := d) Φ β
    Summable (fun n : ℕ ↦
      M.bigradedMixedWeightedNormDegreeSum grading weight t n) := by
  dsimp only
  exact (summable_nat_add_iff
    (f := fun n : ℕ ↦
      (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).bigradedMixedWeightedNormDegreeSum
        (bivariateDecoratedObservableRootGrading F H Λ)
        (bivariateDecoratedObservablePlaquetteCardinality F H Λ)
        (plaquetteCardinalityTilt (d := d) Φ β) n) 1).mp
      (summable_bivariateDecoratedObservableMixedCardinalityWeightedNormDegreeSum_succ
        F H Λ Φ hβ)

/-- Summed spatial estimate: the entire mixed absolute Mayer series pays the
explicit exponential plaquette-separation factor. -/
theorem pow_spatialSeparation_mul_tsum_bivariateDecoratedMixedNormDegreeSum_le
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let M := bivariateDecoratedObservableRootModel F H Λ Φ β 1 1
    let grading := bivariateDecoratedObservableRootGrading F H Λ
    let weight := bivariateDecoratedObservablePlaquetteCardinality F H Λ
    let t := plaquetteCardinalityTilt (d := d) Φ β
    t ^ bivariateObservablePlaquetteSeparation F H Λ *
        (∑' n : ℕ, M.bigradedMixedNormDegreeSum grading n) ≤
      ∑' n : ℕ,
        M.bigradedMixedWeightedNormDegreeSum grading weight t n := by
  dsimp only
  let M := bivariateDecoratedObservableRootModel F H Λ Φ β 1 1
  let grading := bivariateDecoratedObservableRootGrading F H Λ
  let weight := bivariateDecoratedObservablePlaquetteCardinality F H Λ
  let t := plaquetteCardinalityTilt (d := d) Φ β
  have ht : 1 ≤ t := (one_lt_plaquetteCardinalityTilt Φ hβ).le
  have hweighted : Summable (fun n : ℕ ↦
      M.bigradedMixedWeightedNormDegreeSum grading weight t n) := by
    simpa [M, grading, weight, t] using
      (summable_bivariateDecoratedObservableMixedCardinalityWeightedNormDegreeSum
        F H Λ Φ hβ)
  have hleft : Summable (fun n : ℕ ↦
      t ^ bivariateObservablePlaquetteSeparation F H Λ *
        M.bigradedMixedNormDegreeSum grading n) :=
    Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg (pow_nonneg (zero_le_one.trans ht) _)
        (by
          unfold FinitePolymerModel.bigradedMixedNormDegreeSum
          exact Finset.sum_nonneg fun X _ ↦ by
            split_ifs
            · exact norm_nonneg _
            · exact le_rfl))
      (fun n ↦ by
        simpa [M, grading, weight, t] using
          (pow_spatialSeparation_mul_bivariateDecoratedMixedNormDegreeSum_le
            F H Λ Φ β ht n))
      hweighted
  rw [← tsum_mul_left]
  exact hleft.tsum_le_tsum
    (fun n ↦ by
      simpa [M, grading, weight, t] using
        (pow_spatialSeparation_mul_bivariateDecoratedMixedNormDegreeSum_le
          F H Λ Φ β ht n))
    hweighted

/-- Finite-volume exponential clustering with the still-explicit weighted
mixed KP majorant on the right.  The next analytic step is to bound that
majorant uniformly in the specification by pinned/tree summation. -/
theorem pow_spatialSeparation_mul_norm_complexGibbsTruncatedCorrelation_le_weightedMajorant
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hFH : Disjoint F.support H.support)
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let M := bivariateDecoratedObservableRootModel F H Λ Φ β 1 1
    let grading := bivariateDecoratedObservableRootGrading F H Λ
    let weight := bivariateDecoratedObservablePlaquetteCardinality F H Λ
    let t := plaquetteCardinalityTilt (d := d) Φ β
    t ^ bivariateObservablePlaquetteSeparation F H Λ *
        ‖complexGibbsExpectation (F.mul H) Λ Φ β -
          complexGibbsExpectation F Λ Φ β *
            complexGibbsExpectation H Λ Φ β‖ ≤
      ∑' n : ℕ,
        M.bigradedMixedWeightedNormDegreeSum grading weight t n := by
  dsimp only
  let M := bivariateDecoratedObservableRootModel F H Λ Φ β 1 1
  let grading := bivariateDecoratedObservableRootGrading F H Λ
  let t := plaquetteCardinalityTilt (d := d) Φ β
  have ht : 1 ≤ t := (one_lt_plaquetteCardinalityTilt Φ hβ).le
  have hweighted :=
    summable_bivariateDecoratedObservableMixedCardinalityWeightedNormDegreeSum
      F H Λ Φ hβ
  have hmixedPoint (n : ℕ) :
      M.bigradedMixedNormDegreeSum grading n ≤
        M.bigradedMixedWeightedNormDegreeSum grading
          (bivariateDecoratedObservablePlaquetteCardinality F H Λ) t n := by
    calc
      M.bigradedMixedNormDegreeSum grading n =
          1 * M.bigradedMixedNormDegreeSum grading n := by rw [one_mul]
      _ ≤ t ^ bivariateObservablePlaquetteSeparation F H Λ *
          M.bigradedMixedNormDegreeSum grading n := by
        apply mul_le_mul_of_nonneg_right
        · simpa using
            (pow_le_pow_right₀ ht
              (Nat.zero_le (bivariateObservablePlaquetteSeparation F H Λ)))
        · unfold FinitePolymerModel.bigradedMixedNormDegreeSum
          exact Finset.sum_nonneg fun X _ ↦ by
            split_ifs
            · exact norm_nonneg _
            · exact le_rfl
      _ ≤ _ := by
        simpa [M, grading, t] using
          (pow_spatialSeparation_mul_bivariateDecoratedMixedNormDegreeSum_le
            F H Λ Φ β ht n)
  have hmixed : Summable (fun n : ℕ ↦
      M.bigradedMixedNormDegreeSum grading n) :=
    Summable.of_nonneg_of_le
      (fun n ↦ by
        unfold FinitePolymerModel.bigradedMixedNormDegreeSum
        exact Finset.sum_nonneg fun X _ ↦ by
          split_ifs
          · exact norm_nonneg _
          · exact le_rfl)
      hmixedPoint (by simpa [M, grading, t] using hweighted)
  have hcoeffNorm : Summable (fun n : ℕ ↦
      ‖M.bigradedMixedMayerDegreeSum grading n‖) :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _)
      (fun n ↦ M.norm_bigradedMixedMayerDegreeSum_le_bigradedMixedNormDegreeSum
        grading n) hmixed
  have hcorr :
      ‖complexGibbsExpectation (F.mul H) Λ Φ β -
          complexGibbsExpectation F Λ Φ β *
            complexGibbsExpectation H Λ Φ β‖ ≤
        ∑' n : ℕ, M.bigradedMixedNormDegreeSum grading n := by
    rw [complexGibbsTruncatedCorrelation_eq_tsum_bivariateDecoratedMixed
      F H Λ Φ hFH hβ]
    calc
      ‖∑' n : ℕ, bivariateDecoratedObservableMixedMayerDegreeSum
          F H Λ Φ β n‖ ≤
          ∑' n : ℕ, ‖M.bigradedMixedMayerDegreeSum grading n‖ := by
        simpa [M, grading, bivariateDecoratedObservableMixedMayerDegreeSum] using
          norm_tsum_le_tsum_norm hcoeffNorm
      _ ≤ ∑' n : ℕ, M.bigradedMixedNormDegreeSum grading n :=
        hcoeffNorm.tsum_le_tsum
          (fun n ↦ M.norm_bigradedMixedMayerDegreeSum_le_bigradedMixedNormDegreeSum
            grading n) hmixed
  calc
    t ^ bivariateObservablePlaquetteSeparation F H Λ *
        ‖complexGibbsExpectation (F.mul H) Λ Φ β -
          complexGibbsExpectation F Λ Φ β *
            complexGibbsExpectation H Λ Φ β‖ ≤
      t ^ bivariateObservablePlaquetteSeparation F H Λ *
        (∑' n : ℕ, M.bigradedMixedNormDegreeSum grading n) :=
          mul_le_mul_of_nonneg_left hcorr
            (pow_nonneg (zero_le_one.trans ht) _)
    _ ≤ _ := by
      simpa [M, grading, t] using
        (pow_spatialSeparation_mul_tsum_bivariateDecoratedMixedNormDegreeSum_le
          F H Λ Φ hβ)

/-- End-to-end finite-volume cluster bound obtained by evaluating the
weighted majorant with the quantitative source-pinned KP/tree estimate. -/
theorem
pow_spatialSeparation_mul_norm_complexGibbsTruncatedCorrelation_le_regularizedPinnedTreeBudget
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hFH : Disjoint F.support H.support)
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let t := plaquetteCardinalityTilt (d := d) Φ β
    let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
      F H Λ Φ β
    t ^ bivariateObservablePlaquetteSeparation F H Λ *
        ‖complexGibbsExpectation (F.mul H) Λ Φ β -
          complexGibbsExpectation F Λ Φ β *
            complexGibbsExpectation H Λ Φ β‖ ≤
      (ρ * ρ)⁻¹ * twoRootSourceReserve := by
  dsimp only
  let M := bivariateDecoratedObservableRootModel F H Λ Φ β 1 1
  let grading := bivariateDecoratedObservableRootGrading F H Λ
  let weight := bivariateDecoratedObservablePlaquetteCardinality F H Λ
  let t := plaquetteCardinalityTilt (d := d) Φ β
  let f : ℕ → ℝ := fun n ↦
    M.bigradedMixedWeightedNormDegreeSum grading weight t n
  have hf : Summable f := by
    simpa [f, M, grading, weight, t] using
      (summable_bivariateDecoratedObservableMixedCardinalityWeightedNormDegreeSum
        F H Λ Φ hβ)
  have hfzero : f 0 = 0 := by
    classical
    unfold f FinitePolymerModel.bigradedMixedWeightedNormDegreeSum
    simp [FinitePolymerModel.mayerMultiIndicesOfDegree,
      FinitePolymerModel.bigradedMultiplicity]
  have hfull : (∑' n : ℕ, f n) = ∑' n : ℕ, f (n + 1) := by
    have hsplit := hf.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one, hfzero, zero_add] at hsplit
    exact hsplit.symm
  calc
    t ^ bivariateObservablePlaquetteSeparation F H Λ *
        ‖complexGibbsExpectation (F.mul H) Λ Φ β -
          complexGibbsExpectation F Λ Φ β *
            complexGibbsExpectation H Λ Φ β‖ ≤
      ∑' n : ℕ, f n := by
        simpa [f, M, grading, weight, t] using
          (pow_spatialSeparation_mul_norm_complexGibbsTruncatedCorrelation_le_weightedMajorant
            F H Λ Φ hFH hβ)
    _ = ∑' n : ℕ, f (n + 1) := hfull
    _ ≤ _ := by
      simpa [f, M, grading, weight, t] using
        (tsum_bivariateDecoratedObservableMixedCardinalityWeightedNormDegreeSum_succ_le
          F H Λ Φ hβ)

/-- Volume- and boundary-independent form of the finite-volume cluster
estimate.  The prefactor is explicit in the two fixed observables and the
strong-coupling data, but contains no finite-specification parameter. -/
theorem pow_spatialSeparation_mul_norm_complexGibbsTruncatedCorrelation_le_uniformPinnedTreeBudget
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hFH : Disjoint F.support H.support)
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let t := plaquetteCardinalityTilt (d := d) Φ β
    let ρ₀ :=
      bivariateDecoratedObservableCardinalityTiltUniformRegularization
        (d := d) F H Φ β
    t ^ bivariateObservablePlaquetteSeparation F H Λ *
        ‖complexGibbsExpectation (F.mul H) Λ Φ β -
          complexGibbsExpectation F Λ Φ β *
            complexGibbsExpectation H Λ Φ β‖ ≤
      (ρ₀ * ρ₀)⁻¹ * twoRootSourceReserve := by
  dsimp only
  let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
    F H Λ Φ β
  let ρ₀ := bivariateDecoratedObservableCardinalityTiltUniformRegularization
    (d := d) F H Φ β
  have hρ : 0 < ρ :=
    bivariateDecoratedObservableCardinalityTiltRegularization_pos
      F H Λ Φ β
  have hρ₀ : 0 < ρ₀ :=
    bivariateDecoratedObservableCardinalityTiltUniformRegularization_pos
      (d := d) F H Φ β
  have hρ₀ρ : ρ₀ ≤ ρ := by
    simpa [ρ₀, ρ] using
      bivariateDecoratedObservableCardinalityTiltUniformRegularization_le
        F H Λ Φ hβ
  have hprod : ρ₀ * ρ₀ ≤ ρ * ρ :=
    mul_le_mul hρ₀ρ hρ₀ρ hρ₀.le hρ.le
  have hinv : (ρ * ρ)⁻¹ ≤ (ρ₀ * ρ₀)⁻¹ :=
    inv_anti₀ (mul_pos hρ₀ hρ₀) hprod
  have hregularized :=
    pow_spatialSeparation_mul_norm_complexGibbsTruncatedCorrelation_le_regularizedPinnedTreeBudget
      F H Λ Φ hFH hβ
  calc
    _ ≤ (ρ * ρ)⁻¹ * twoRootSourceReserve := by
      simpa [ρ] using hregularized
    _ ≤ (ρ₀ * ρ₀)⁻¹ * twoRootSourceReserve :=
      mul_le_mul_of_nonneg_right hinv twoRootSourceReserve_pos.le

/-! ## Volume-independent support distance -/

/-- Ambient plaquettes together with two abstract observable roots. -/
abbrev GlobalBivariateObservableSpatialVertex (d : ℕ) :=
  Plaquette d ⊕ Fin 2

/-- The ambient plaquette-incidence graph determined only by two finite edge
supports.  In particular, it is independent of a finite specification and
of its exterior field. -/
def globalBivariateObservableSpatialGraph
    (S T : Finset (PositiveEdge d)) :
    SimpleGraph (GlobalBivariateObservableSpatialVertex d) where
  Adj x y := match x, y with
    | Sum.inl p, Sum.inl q =>
        p ≠ q ∧ ¬Disjoint p.boundary.edgeSupport q.boundary.edgeSupport
    | Sum.inl p, Sum.inr i =>
        ¬Disjoint p.boundary.edgeSupport (if i = 0 then S else T)
    | Sum.inr i, Sum.inl p =>
        ¬Disjoint p.boundary.edgeSupport (if i = 0 then S else T)
    | Sum.inr _, Sum.inr _ => False
  symm := by
    rintro (p | i) (q | j) h
    · exact ⟨h.1.symm, fun hd => h.2 hd.symm⟩
    · exact h
    · exact h
    · exact h
  loopless := by
    constructor
    rintro (p | i) h
    · exact h.1 rfl
    · exact h

instance (S T : Finset (PositiveEdge d)) :
    DecidableRel (globalBivariateObservableSpatialGraph S T).Adj :=
  Classical.decRel _

/-- Forget the active-plaquette subtype while retaining the two roots. -/
def bivariateObservableSpatialVertexToGlobal
    (Λ : FiniteSpecification d G) :
    BivariateObservableSpatialVertex Λ →
      GlobalBivariateObservableSpatialVertex d
  | Sum.inl p => Sum.inl p.1
  | Sum.inr i => Sum.inr i

/-- Every finite-volume spatial edge is an ambient spatial edge.  Dynamic
plaquette adjacency can only remove incidences from the full boundary. -/
def bivariateObservableSpatialGraphToGlobalHom
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G) :
    bivariateObservableSpatialGraph F H Λ →g
      globalBivariateObservableSpatialGraph F.support H.support := by
  refine ⟨bivariateObservableSpatialVertexToGlobal Λ, ?_⟩
  rintro (p | i) (q | j) h
  · change p ≠ q ∧
        ¬Disjoint (plaquetteDynamicSupport Λ p.1)
          (plaquetteDynamicSupport Λ q.1) at h
    refine ⟨fun hpq => h.1 (Subtype.ext hpq), ?_⟩
    rw [Finset.not_disjoint_iff] at h ⊢
    obtain ⟨e, hep, heq⟩ := h.2
    exact ⟨e, (Finset.mem_filter.mp hep).2,
      (Finset.mem_filter.mp heq).2⟩
  · fin_cases j <;> simpa [bivariateObservableSpatialVertexToGlobal,
      globalBivariateObservableSpatialGraph,
      bivariateObservableSpatialGraph,
      bivariateObservableRootPlaquettes,
      mem_observableRootPlaquettes] using h
  · fin_cases i <;> simpa [bivariateObservableSpatialVertexToGlobal,
      globalBivariateObservableSpatialGraph,
      bivariateObservableSpatialGraph,
      bivariateObservableRootPlaquettes,
      mem_observableRootPlaquettes] using h
  · exact h

/-- Plaquette-incidence distance between two finite edge supports in the
ambient lattice.  The two root edges are removed from the count. -/
def globalObservablePlaquetteSeparation
    (S T : Finset (PositiveEdge d)) : ℕ :=
  (globalBivariateObservableSpatialGraph S T).dist
    (Sum.inr 0) (Sum.inr 1) - 2

/-- Whenever the two finite-volume roots are connected, ambient separation
is no larger than finite-volume separation. -/
theorem globalObservablePlaquetteSeparation_le_finite
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (hreach : (bivariateObservableSpatialGraph F H Λ).Reachable
      (Sum.inr 0) (Sum.inr 1)) :
    globalObservablePlaquetteSeparation F.support H.support ≤
      bivariateObservablePlaquetteSeparation F H Λ := by
  obtain ⟨path, hpath⟩ := hreach.exists_walk_length_eq_dist
  let path' := path.map
    (bivariateObservableSpatialGraphToGlobalHom F H Λ)
  have hdist :
      (globalBivariateObservableSpatialGraph F.support H.support).dist
          (Sum.inr 0) (Sum.inr 1) ≤
        (bivariateObservableSpatialGraph F H Λ).dist
          (Sum.inr 0) (Sum.inr 1) := by
    calc
      _ ≤ path'.length := by
        simpa [path', bivariateObservableSpatialVertexToGlobal] using
          SimpleGraph.dist_le path'
      _ = path.length := by simp [path']
      _ = _ := hpath
  unfold globalObservablePlaquetteSeparation
  unfold bivariateObservablePlaquetteSeparation
  omega

/-- Explicit observable-dependent, but volume- and boundary-independent,
amplitude supplied by the complete-decoration KP estimate. -/
def bivariateDecoratedObservableUniformClusteringAmplitude
    (F H : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℂ) : ℝ :=
  let ρ₀ :=
    bivariateDecoratedObservableCardinalityTiltUniformRegularization
      (d := d) F H Φ β
  (ρ₀ * ρ₀)⁻¹ * twoRootSourceReserve

theorem bivariateDecoratedObservableUniformClusteringAmplitude_nonneg
    (F H : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℂ) :
    0 ≤ bivariateDecoratedObservableUniformClusteringAmplitude
      (d := d) F H Φ β := by
  let ρ₀ :=
    bivariateDecoratedObservableCardinalityTiltUniformRegularization
      (d := d) F H Φ β
  have hρ₀ : 0 < ρ₀ :=
    bivariateDecoratedObservableCardinalityTiltUniformRegularization_pos
      (d := d) F H Φ β
  change 0 ≤ (ρ₀ * ρ₀)⁻¹ * twoRootSourceReserve
  exact mul_nonneg (inv_nonneg.mpr (mul_nonneg hρ₀.le hρ₀.le))
    twoRootSourceReserve_pos.le

/-- Uniform cluster decay rate, the inverse of the explicit
plaquette-cardinality tilt. -/
def plaquetteClusterDecayRate
    (Φ : RealPlaquettePotential G) (β : ℂ) : ℝ :=
  (plaquetteCardinalityTilt (d := d) Φ β)⁻¹

theorem plaquetteClusterDecayRate_pos
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    0 < plaquetteClusterDecayRate (d := d) Φ β := by
  exact inv_pos.mpr (zero_lt_one.trans
    (one_lt_plaquetteCardinalityTilt Φ hβ))

theorem plaquetteClusterDecayRate_lt_one
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    plaquetteClusterDecayRate (d := d) Φ β < 1 := by
  simpa [plaquetteClusterDecayRate] using
    (inv_lt_one_of_one_lt₀ (one_lt_plaquetteCardinalityTilt Φ hβ))

/-- Ordinary exponential-decay form of the uniform finite-volume cluster
estimate. -/
theorem norm_complexGibbsTruncatedCorrelation_le_uniformAmplitude_mul_rate_pow
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hFH : Disjoint F.support H.support)
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ‖complexGibbsExpectation (F.mul H) Λ Φ β -
        complexGibbsExpectation F Λ Φ β *
          complexGibbsExpectation H Λ Φ β‖ ≤
      bivariateDecoratedObservableUniformClusteringAmplitude
          (d := d) F H Φ β *
        plaquetteClusterDecayRate (d := d) Φ β ^
          bivariateObservablePlaquetteSeparation F H Λ := by
  let t := plaquetteCardinalityTilt (d := d) Φ β
  let s := bivariateObservablePlaquetteSeparation F H Λ
  let x := ‖complexGibbsExpectation (F.mul H) Λ Φ β -
    complexGibbsExpectation F Λ Φ β *
      complexGibbsExpectation H Λ Φ β‖
  let A := bivariateDecoratedObservableUniformClusteringAmplitude
    (d := d) F H Φ β
  have ht : 0 < t := (one_lt_plaquetteCardinalityTilt Φ hβ).trans' zero_lt_one
  have hmain : t ^ s * x ≤ A := by
    simpa [t, s, x, A,
      bivariateDecoratedObservableUniformClusteringAmplitude] using
      (pow_spatialSeparation_mul_norm_complexGibbsTruncatedCorrelation_le_uniformPinnedTreeBudget
        F H Λ Φ hFH hβ)
  calc
    x = (t ^ s)⁻¹ * (t ^ s * x) := by
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ht.ne'), one_mul]
    _ ≤ (t ^ s)⁻¹ * A :=
      mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr (pow_nonneg ht.le _))
    _ = A * t⁻¹ ^ s := by
      rw [inv_pow]
      ring
    _ = _ := by
      rfl

end

end YangMills.StrongCoupling
