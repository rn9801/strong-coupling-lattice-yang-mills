/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.SpatialClusterGeometry

/-!
# Boundary cancellation for the observable-root cluster expansion

This file gives the exact local cancellation underlying the infinite-volume
construction.  A decorated Mayer cluster only reads the exterior field along
the plaquette support carried by its bulk and observable-root polymers.  Thus
two exterior fields give identical terms whenever that finite support avoids
their boundary-disagreement plaquettes.

This is a cluster-expansion argument; no influence-matrix or Dobrushin
comparison theorem is used.
-/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Polymer

noncomputable section

local instance clusterBoundaryDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-! ## Plaquette support of a decorated one-root cluster -/

/-- Untyped plaquette support of a bulk polymer or a complete observable-root
decoration. -/
def decoratedObservablePlaquetteSupport
    (F : LocalObservable d G) (Λ : FiniteSpecification d G) :
    PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ → Finset (Plaquette d)
  | Sum.inl γ => γ.support
  | Sum.inr D => D.support

theorem decoratedObservablePlaquetteSupport_subset_active
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (q : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) :
    decoratedObservablePlaquetteSupport F Λ q ⊆ Λ.activePlaquettes := by
  rcases q with γ | D
  · exact γ.support_subset_active
  · exact polymerFamilySupport_subset_active Λ D.1

/-- Union of the plaquette supports of all polymer types occurring in a
decorated Mayer multi-index. -/
def decoratedObservableMayerPlaquetteSupport
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)) :
    Finset (Plaquette d) := by
  classical
  exact X.support.biUnion (decoratedObservablePlaquetteSupport F Λ)

theorem decoratedObservablePlaquetteSupport_subset_mayerSupport
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ))
    (q : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)
    (hq : 0 < X q) :
    decoratedObservablePlaquetteSupport F Λ q ⊆
      decoratedObservableMayerPlaquetteSupport F Λ X := by
  intro p hp
  rw [decoratedObservableMayerPlaquetteSupport]
  apply Finset.mem_biUnion.mpr
  refine ⟨q, ?_, hp⟩
  exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hq)

theorem decoratedObservableMayerPlaquetteSupport_subset_active
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)) :
    decoratedObservableMayerPlaquetteSupport F Λ X ⊆ Λ.activePlaquettes := by
  intro p hp
  rw [decoratedObservableMayerPlaquetteSupport] at hp
  rcases Finset.mem_biUnion.mp hp with ⟨q, _hq, hpq⟩
  exact decoratedObservablePlaquetteSupport_subset_active F Λ q hpq

@[simp]
theorem decoratedObservableMayerPlaquetteSupport_withExterior
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (η : Gauge.Configuration d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)) :
    decoratedObservableMayerPlaquetteSupport F (withExterior Λ η) X =
      decoratedObservableMayerPlaquetteSupport F Λ X := by
  classical
  ext p
  simp [decoratedObservableMayerPlaquetteSupport,
    decoratedObservablePlaquetteSupport]
  constructor
  · rintro (⟨a, ha, hp⟩ | ⟨b, hb, hp⟩)
    · exact Or.inl ⟨a, ha, hp⟩
    · exact Or.inr ⟨b, hb, hp⟩
  · rintro (⟨a, ha, hp⟩ | ⟨b, hb, hp⟩)
    · exact Or.inl ⟨a, ha, hp⟩
    · exact Or.inr ⟨b, hb, hp⟩

@[simp]
theorem activeSubset_withExterior
    (Λ : FiniteSpecification d G) (η : Gauge.Configuration d G)
    (S : Finset (Plaquette d)) :
    activeSubset (withExterior Λ η) S = activeSubset Λ S := by
  classical
  ext p
  simp only [activeSubset, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, h⟩
  · intro h
    exact (Finset.mem_filter.mp h).2

@[simp]
theorem bivariateObservableSpatialGraph_withExterior
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (η : Gauge.Configuration d G) :
    bivariateObservableSpatialGraph F H (withExterior Λ η) =
      bivariateObservableSpatialGraph F H Λ := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  rcases x with p | i <;> rcases y with q | j
  · rfl
  · by_cases hj : j = 0 <;>
      simp [bivariateObservableSpatialGraph,
        bivariateObservableRootPlaquettes, observableRootPlaquettes, hj]
  · by_cases hi : i = 0 <;>
      simp [bivariateObservableSpatialGraph,
        bivariateObservableRootPlaquettes, observableRootPlaquettes, hi]
  · change False ↔ False
    exact Iff.rfl

/-- The total Mayer degree does not depend on which extensionally equal
`Fintype` instance enumerates a fixed polymer type. -/
theorem mayerDegree_withExterior
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (η : Gauge.Configuration d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)) :
    @FinitePolymerModel.mayerDegree
        (PlaquettePolymer (withExterior Λ η) ⊕
          ObservableRootDecoration F (withExterior Λ η))
        (inferInstance) X =
      @FinitePolymerModel.mayerDegree
        (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)
        (inferInstance) X := by
  unfold FinitePolymerModel.mayerDegree
  calc
    (∑ q : PlaquettePolymer (withExterior Λ η) ⊕
        ObservableRootDecoration F (withExterior Λ η), X q) =
        X.sum (fun _ m => m) := by
          symm
          exact Finsupp.sum_fintype X (fun _ m => m) (fun _ => rfl)
    _ = ∑ q : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ, X q := by
      exact Finsupp.sum_fintype X (fun _ m => m) (fun _ => rfl)

set_option maxHeartbeats 800000 in
-- Comparing the two subtype enumerations makes typeclass normalization expensive.
@[simp] theorem mayerMultiIndicesOfDegree_withExterior
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (η : Gauge.Configuration d G) (n : ℕ) :
    FinitePolymerModel.mayerMultiIndicesOfDegree
        (P := PlaquettePolymer (withExterior Λ η) ⊕
          ObservableRootDecoration F (withExterior Λ η)) n =
      FinitePolymerModel.mayerMultiIndicesOfDegree
        (P := PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) n := by
  classical
  apply Finset.ext
  intro X
  constructor
  · intro h
    have hWith :
        @FinitePolymerModel.mayerDegree
            (PlaquettePolymer (withExterior Λ η) ⊕
              ObservableRootDecoration F (withExterior Λ η))
            (inferInstance) X = n :=
      (FinitePolymerModel.mem_mayerMultiIndicesOfDegree
        (P := PlaquettePolymer (withExterior Λ η) ⊕
          ObservableRootDecoration F (withExterior Λ η)) n X).mp h
    apply (FinitePolymerModel.mem_mayerMultiIndicesOfDegree
      (P := PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) n X).mpr
    rw [← mayerDegree_withExterior F Λ η X]
    exact hWith
  · intro h
    have hBase :
        @FinitePolymerModel.mayerDegree
            (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)
            (inferInstance) X = n :=
      (FinitePolymerModel.mem_mayerMultiIndicesOfDegree
        (P := PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) n X).mp h
    apply (FinitePolymerModel.mem_mayerMultiIndicesOfDegree
      (P := PlaquettePolymer (withExterior Λ η) ⊕
        ObservableRootDecoration F (withExterior Λ η)) n X).mpr
    rw [mayerDegree_withExterior F Λ η X]
    exact hBase

/-- The union support has cardinality at most the plaquette-cardinality
weight charged with multiplicity by the Mayer multi-index. -/
theorem card_decoratedObservableMayerPlaquetteSupport_le_weightedMultiplicity
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)) :
    (decoratedObservableMayerPlaquetteSupport F Λ X).card ≤
      FinitePolymerModel.weightedMultiplicity
        (decoratedObservablePlaquetteCardinality F Λ) X := by
  classical
  calc
    (decoratedObservableMayerPlaquetteSupport F Λ X).card ≤
        ∑ q ∈ X.support,
          (decoratedObservablePlaquetteSupport F Λ q).card :=
      by
        rw [decoratedObservableMayerPlaquetteSupport]
        exact Finset.card_biUnion_le
    _ = ∑ q ∈ X.support,
          decoratedObservablePlaquetteCardinality F Λ q := by
      apply Finset.sum_congr rfl
      rintro (γ | D) _ <;>
        simp [decoratedObservablePlaquetteSupport,
          decoratedObservablePlaquetteCardinality, PlaquettePolymer.support]
    _ ≤ ∑ q ∈ X.support,
          decoratedObservablePlaquetteCardinality F Λ q * X q := by
      apply Finset.sum_le_sum
      intro q hq
      apply le_mul_of_one_le_right
      · exact Nat.zero_le _
      · exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hq)
    _ ≤ ∑ q : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ,
          decoratedObservablePlaquetteCardinality F Λ q * X q := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (by simp)
        (fun _ _ _ => Nat.zero_le _)
    _ = _ := rfl

/-! ## Exact exterior cancellation -/

/-- A decorated Mayer term is exactly unchanged by an exterior replacement
when the cluster's complete plaquette support avoids every active plaquette
which reads a changed frozen edge. -/
theorem decoratedObservableRootModel_mayerClusterTerm_withExterior_eq_of_disjoint
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ)
    (η η' : Gauge.Configuration d G)
    (hF : F.support ⊆ Λ.dynamicEdges)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ))
    (hdisjoint : Disjoint
      (activeSubset Λ (decoratedObservableMayerPlaquetteSupport F Λ X))
      (boundaryDisagreementPlaquettes Λ η η')) :
    (decoratedObservableRootModel F (withExterior Λ η) Φ β α).mayerClusterTerm X =
      (decoratedObservableRootModel F (withExterior Λ η') Φ β α).mayerClusterTerm X := by
  let A := decoratedObservableRootModel F (withExterior Λ η) Φ β α
  let B := decoratedObservableRootModel F (withExterior Λ η') Φ β α
  have hsupportDisjoint
      (q : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)
      (hq : 0 < X q) :
      Disjoint
        (activeSubset Λ (decoratedObservablePlaquetteSupport F Λ q))
        (boundaryDisagreementPlaquettes Λ η η') := by
    apply Finset.disjoint_left.mpr
    intro p hpq hpD
    exact Finset.disjoint_left.mp hdisjoint (by
      have hp : p.1 ∈ decoratedObservablePlaquetteSupport F Λ q := by
        simpa [activeSubset] using hpq
      have hp' := decoratedObservablePlaquetteSupport_subset_mayerSupport
        F Λ X q hq hp
      simpa [activeSubset] using hp') hpD
  have hactivity
      (q : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)
      (hq : 0 < X q) : A.activity q = B.activity q := by
    rcases q with γ | D
    · exact subsetWeight_withExterior_eq_of_disjoint_defects
        Λ Φ β γ.support η η' γ.support_subset_active
        (hsupportDisjoint (Sum.inl γ) hq)
    · change α * markedSubsetWeight F (withExterior Λ η) Φ β D.support =
        α * markedSubsetWeight F (withExterior Λ η') Φ β D.support
      rw [markedSubsetWeight_withExterior_eq_of_disjoint_defects
        F Λ Φ β D.support η η' hF
        (polymerFamilySupport_subset_active Λ D.1)
        (hsupportDisjoint (Sum.inr D) hq)]
  have hmonomial : A.mayerActivityMonomial X = B.mayerActivityMonomial X := by
    unfold FinitePolymerModel.mayerActivityMonomial
    change (∏ q : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ,
        A.activity q ^ X q) =
      ∏ q : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ,
        B.activity q ^ X q
    apply Finset.prod_congr rfl
    intro q _
    by_cases hq : 0 < X q
    · exact congrArg (fun z : ℂ => z ^ X q) (hactivity q hq)
    · have hq0 : X q = 0 := Nat.eq_zero_of_not_pos hq
      rw [hq0]
      change (1 : ℂ) = 1
      rfl
  change A.mayerClusterTerm X = B.mayerClusterTerm X
  unfold FinitePolymerModel.mayerClusterTerm
  rw [hmonomial]
  rfl

/-! ## One-root spatial carriers -/

/-- Embed the decorated one-root gas as the left sector of the already
constructed two-root spatial geometry.  The unused right root never occurs
in any carrier below. -/
def decoratedObservableLeftEmbedding
    (F : LocalObservable d G) (Λ : FiniteSpecification d G) :
    (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) →
      (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration F Λ) ⊕
          TwoObservableBridgeDecoration F F Λ)
  | Sum.inl γ => Sum.inl (Sum.inl (Sum.inl γ))
  | Sum.inr D => Sum.inl (Sum.inl (Sum.inr D))

/-- Spatial carrier of a decorated one-root polymer, obtained from the left
sector of the two-root incidence graph. -/
def decoratedObservableSpatialCarrier
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (q : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) :
    Finset (BivariateObservableSpatialVertex Λ) :=
  bivariateDecoratedObservableSpatialCarrier F F Λ
    (decoratedObservableLeftEmbedding F Λ q)

/-- Indicator for an observable-root decoration. -/
def decoratedObservableRootIndicator
    (F : LocalObservable d G) (Λ : FiniteSpecification d G) :
    PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ → ℕ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

@[simp]
theorem card_decoratedObservableSpatialCarrier
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (q : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) :
    (decoratedObservableSpatialCarrier F Λ q).card =
      decoratedObservablePlaquetteCardinality F Λ q +
      decoratedObservableRootIndicator F Λ q := by
  rcases q with γ | D
  · unfold decoratedObservableSpatialCarrier
    rw [bivariateDecoratedObservableSpatialCarrier_card]
    simp [decoratedObservableLeftEmbedding, decoratedObservableRootIndicator,
      decoratedObservablePlaquetteCardinality,
      bivariateDecoratedObservablePlaquetteCardinality,
      bivariateDecoratedObservableRootGrading]
  · unfold decoratedObservableSpatialCarrier
    rw [bivariateDecoratedObservableSpatialCarrier_card]
    simp [decoratedObservableLeftEmbedding, decoratedObservableRootIndicator,
      decoratedObservablePlaquetteCardinality,
      bivariateDecoratedObservablePlaquetteCardinality,
      bivariateDecoratedObservableRootGrading]

/-- Union of the spatial carriers of all types charged by a one-root Mayer
multi-index. -/
def decoratedObservableMayerSpatialSupport
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)) :
    Finset (BivariateObservableSpatialVertex Λ) := by
  classical
  exact X.support.biUnion (decoratedObservableSpatialCarrier F Λ)

theorem weightedMultiplicity_rootIndicator_eq_exclusiveRootMultiplicity
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)) :
    FinitePolymerModel.weightedMultiplicity
        (decoratedObservableRootIndicator F Λ) X =
      FinitePolymerModel.exclusiveRootMultiplicity X := by
  classical
  unfold FinitePolymerModel.weightedMultiplicity
    FinitePolymerModel.exclusiveRootMultiplicity
  simp [decoratedObservableRootIndicator]

/-- The one-root spatial carrier has at most the charged plaquette weight
plus the number of observable-root occurrences. -/
theorem card_decoratedObservableMayerSpatialSupport_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)) :
    (decoratedObservableMayerSpatialSupport F Λ X).card ≤
      FinitePolymerModel.weightedMultiplicity
          (decoratedObservablePlaquetteCardinality F Λ) X +
        FinitePolymerModel.exclusiveRootMultiplicity X := by
  classical
  let weight := decoratedObservablePlaquetteCardinality F Λ
  let root := decoratedObservableRootIndicator F Λ
  calc
    (decoratedObservableMayerSpatialSupport F Λ X).card ≤
        ∑ q ∈ X.support,
          (decoratedObservableSpatialCarrier F Λ q).card := by
      rw [decoratedObservableMayerSpatialSupport]
      exact Finset.card_biUnion_le
    _ = ∑ q ∈ X.support, (weight q + root q) := by
      apply Finset.sum_congr rfl
      intro q _
      exact card_decoratedObservableSpatialCarrier F Λ q
    _ ≤ ∑ q : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ,
          (weight q + root q) * X q := by
      calc
        _ ≤ ∑ q ∈ X.support, (weight q + root q) * X q := by
          apply Finset.sum_le_sum
          intro q hq
          apply le_mul_of_one_le_right
          · exact Nat.zero_le _
          · exact Nat.one_le_iff_ne_zero.mpr
              (Finsupp.mem_support_iff.mp hq)
        _ ≤ ∑ q : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ,
            (weight q + root q) * X q := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (by simp)
            (fun _ _ _ => Nat.zero_le _)
    _ = FinitePolymerModel.weightedMultiplicity weight X +
          FinitePolymerModel.weightedMultiplicity root X := by
      simp only [add_mul, Finset.sum_add_distrib]
      rfl
    _ = _ := by
      rw [weightedMultiplicity_rootIndicator_eq_exclusiveRootMultiplicity]

theorem connected_induce_decoratedObservableSpatialCarrier
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (q : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) :
    ((bivariateObservableSpatialGraph F F Λ).induce
      (decoratedObservableSpatialCarrier F Λ q : Set _)).Connected := by
  exact connected_induce_bivariateDecoratedObservableSpatialCarrier
    F F Λ (decoratedObservableLeftEmbedding F Λ q)

/-- Incompatibility in the exact one-root gas links the corresponding
spatial carriers. -/
theorem decoratedObservableSpatialCarriers_linked_of_incompatible
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (q r : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)
    (h : (decoratedObservableRootModel F Λ Φ β 1).incompatible q r) :
    SpatialCarriersLinked (bivariateObservableSpatialGraph F F Λ)
      (decoratedObservableSpatialCarrier F Λ q)
      (decoratedObservableSpatialCarrier F Λ r) := by
  apply bivariateDecoratedObservableSpatialCarriers_linked_of_incompatible
    F F Λ Φ β (decoratedObservableLeftEmbedding F Λ q)
      (decoratedObservableLeftEmbedding F Λ r)
  rcases q with γ | D <;> rcases r with δ | E <;> exact h

/-- Spatial support swept out by a path in the exact one-root Mayer graph. -/
def decoratedObservableMayerWalkSpatialSupport
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    {X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)}
    {u v : FinitePolymerModel.MayerVertex X}
    (path : ((decoratedObservableRootModel F Λ Φ β 1).mayerIncompatibilityGraph
      X).Walk u v) :
    Finset (BivariateObservableSpatialVertex Λ) := by
  classical
  exact path.support.toFinset.biUnion fun w =>
    decoratedObservableSpatialCarrier F Λ w.1

theorem decoratedObservableMayerWalkSpatialSupport_connected
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    {X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)}
    {u v : FinitePolymerModel.MayerVertex X}
    (path : ((decoratedObservableRootModel F Λ Φ β 1).mayerIncompatibilityGraph
      X).Walk u v) :
    ((bivariateObservableSpatialGraph F F Λ).induce
      (decoratedObservableMayerWalkSpatialSupport F Λ Φ β path :
        Set _)).Connected := by
  classical
  induction path with
  | @nil u0 =>
      rw [decoratedObservableMayerWalkSpatialSupport]
      rw [SimpleGraph.Walk.support_nil]
      have heq : [u0].toFinset.biUnion (fun w =>
          decoratedObservableSpatialCarrier F Λ w.1) =
          decoratedObservableSpatialCarrier F Λ u0.1 := by
        ext x
        simp
      rw [heq]
      exact connected_induce_decoratedObservableSpatialCarrier F Λ u0.1
  | @cons u w v hadj path ih =>
      let carrier := decoratedObservableSpatialCarrier F Λ
      let tailSupport :=
        decoratedObservableMayerWalkSpatialSupport F Λ Φ β path
      have hw : w ∈ path.support.toFinset := by
        simpa using path.start_mem_support
      have hwSubset : carrier w.1 ⊆ tailSupport := by
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨w, hw, hx⟩
      have hlink0 :=
        decoratedObservableSpatialCarriers_linked_of_incompatible
          F Λ Φ β u.1 w.1 hadj.2
      have hlink : SpatialCarriersLinked
          (bivariateObservableSpatialGraph F F Λ)
          (carrier u.1) tailSupport := hlink0.mono_right hwSubset
      have hhead := connected_induce_decoratedObservableSpatialCarrier
        F Λ u.1
      have hunion := connected_induce_union_of_spatialCarriersLinked
        (bivariateObservableSpatialGraph F F Λ)
        (carrier u.1) tailSupport hhead ih hlink
      rw [decoratedObservableMayerWalkSpatialSupport]
      rw [SimpleGraph.Walk.support_cons]
      have heq : (u :: path.support).toFinset.biUnion (fun z =>
          decoratedObservableSpatialCarrier F Λ z.1) =
          carrier u.1 ∪ tailSupport := by
        ext x
        simp [carrier, tailSupport,
          decoratedObservableMayerWalkSpatialSupport]
      rw [heq]
      exact hunion

theorem decoratedObservableMayerWalkSpatialSupport_subset
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    {X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)}
    {u v : FinitePolymerModel.MayerVertex X}
    (path : ((decoratedObservableRootModel F Λ Φ β 1).mayerIncompatibilityGraph
      X).Walk u v) :
    decoratedObservableMayerWalkSpatialSupport F Λ Φ β path ⊆
      decoratedObservableMayerSpatialSupport F Λ X := by
  classical
  intro x hx
  rw [decoratedObservableMayerWalkSpatialSupport] at hx
  rcases Finset.mem_biUnion.mp hx with ⟨w, hw, hxcarrier⟩
  rw [decoratedObservableMayerSpatialSupport]
  exact Finset.mem_biUnion.mpr
    ⟨w.1, FinitePolymerModel.mayerVertex_fst_mem_support w, hxcarrier⟩

theorem sum_inl_mem_decoratedObservableSpatialCarrier
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (q : PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)
    (p : ActivePlaquette Λ)
    (hp : p.1 ∈ decoratedObservablePlaquetteSupport F Λ q) :
    Sum.inl p ∈ decoratedObservableSpatialCarrier F Λ q := by
  rcases q with γ | D
  · change p.1 ∈ γ.support at hp
    simp [decoratedObservableSpatialCarrier,
      decoratedObservableLeftEmbedding,
      bivariateDecoratedObservableSpatialCarrier, liftPlaquetteSupport,
      activeSubset, hp]
  · change p.1 ∈ D.support at hp
    simp [decoratedObservableSpatialCarrier,
      decoratedObservableLeftEmbedding,
      bivariateDecoratedObservableSpatialCarrier, liftPlaquetteSupport,
      activeSubset, hp]

/-! ## Boundary-reaching clusters pay their distance -/

/-- If every disagreement plaquette is at root-incidence distance at least
`r + 1`, then every nonzero multiplicity-one decorated cluster which reaches
a disagreement plaquette has charged plaquette cardinality at least `r`.

The statement is deliberately pointwise in the disagreement set; this form
is what the subsequent tail estimate and centered-box exhaustion need. -/
theorem decoratedObservable_boundaryReaching_nonzero_weightedMultiplicity_ge
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (defects : Finset (ActivePlaquette Λ)) (r : ℕ)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ))
    (hroot : FinitePolymerModel.exclusiveRootMultiplicity X = 1)
    (hterm : (decoratedObservableRootModel F Λ Φ β 1).mayerClusterTerm X ≠ 0)
    (hreaches : ¬Disjoint
      (activeSubset Λ (decoratedObservableMayerPlaquetteSupport F Λ X))
      defects)
    (hdistance : ∀ p ∈ defects,
      (bivariateObservableSpatialGraph F F Λ).Reachable
        (Sum.inr 0) (Sum.inl p) →
      r + 1 ≤ (bivariateObservableSpatialGraph F F Λ).dist
        (Sum.inr 0) (Sum.inl p)) :
    r ≤ FinitePolymerModel.weightedMultiplicity
      (decoratedObservablePlaquetteCardinality F Λ) X := by
  classical
  let K := bivariateObservableSpatialGraph F F Λ
  let root0 : BivariateObservableSpatialVertex Λ := Sum.inr 0
  let global := decoratedObservableMayerSpatialSupport F Λ X
  let total := FinitePolymerModel.weightedMultiplicity
    (decoratedObservablePlaquetteCardinality F Λ) X
  have hglobalCard : global.card ≤ total + 1 := by
    have hcard := card_decoratedObservableMayerSpatialSupport_le F Λ X
    rw [hroot] at hcard
    simpa [global, total] using hcard
  have hconnected :
      ((decoratedObservableRootModel F Λ Φ β 1).mayerIncompatibilityGraph
        X).Connected := by
    by_contra hnot
    exact hterm
      ((decoratedObservableRootModel F Λ Φ β 1).mayerClusterTerm_eq_zero_of_not_connected
        X hnot)
  have hexistsRoot : ∃ D : ObservableRootDecoration F Λ,
      0 < X (Sum.inr D) := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ D : ObservableRootDecoration F Λ,
        X (Sum.inr D) = 0 := fun D => Nat.eq_zero_of_le_zero (hnone D)
    simp [FinitePolymerModel.exclusiveRootMultiplicity, hzero] at hroot
  obtain ⟨D, hD⟩ := hexistsRoot
  rw [Finset.not_disjoint_iff] at hreaches
  obtain ⟨p, hpcluster, hpdefect⟩ := hreaches
  have hpPlaquette : p.1 ∈ decoratedObservableMayerPlaquetteSupport F Λ X := by
    simpa [activeSubset] using hpcluster
  rw [decoratedObservableMayerPlaquetteSupport] at hpPlaquette
  obtain ⟨q, hqSupport, hpq⟩ := Finset.mem_biUnion.mp hpPlaquette
  have hq : 0 < X q := Nat.pos_of_ne_zero
    (Finsupp.mem_support_iff.mp hqSupport)
  let u : FinitePolymerModel.MayerVertex X :=
    ⟨Sum.inr D, ⟨0, hD⟩⟩
  let v : FinitePolymerModel.MayerVertex X :=
    ⟨q, ⟨0, hq⟩⟩
  obtain ⟨path, _hpath⟩ := hconnected.preconnected.exists_isPath u v
  let S := decoratedObservableMayerWalkSpatialSupport F Λ Φ β path
  have hu : u ∈ path.support.toFinset := by
    simpa using path.start_mem_support
  have hv : v ∈ path.support.toFinset := by
    simpa using path.end_mem_support
  have hrootS : root0 ∈ S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨u, hu, ?_⟩
    simp [u, root0, decoratedObservableSpatialCarrier,
      decoratedObservableLeftEmbedding,
      bivariateDecoratedObservableSpatialCarrier]
  have hpS : Sum.inl p ∈ S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨v, hv, ?_⟩
    exact sum_inl_mem_decoratedObservableSpatialCarrier F Λ q p hpq
  have hdistS := graph_dist_lt_card_of_connected_finset K S
    (decoratedObservableMayerWalkSpatialSupport_connected F Λ Φ β path)
    root0 (Sum.inl p) hrootS hpS
  have hreachp : K.Reachable root0 (Sum.inl p) := by
    let rootS : S := ⟨root0, hrootS⟩
    let pS : S := ⟨Sum.inl p, hpS⟩
    have hreachS :=
      (decoratedObservableMayerWalkSpatialSupport_connected F Λ Φ β path).preconnected
        rootS pS
    exact hreachS.map
      (SimpleGraph.Embedding.induce (S : Set (BivariateObservableSpatialVertex Λ))).toHom
  have hSglobal : S ⊆ global :=
    decoratedObservableMayerWalkSpatialSupport_subset F Λ Φ β path
  have hcardS : S.card ≤ global.card := Finset.card_le_card hSglobal
  have hdist : K.dist root0 (Sum.inl p) < total + 1 :=
    hdistS.trans_le (hcardS.trans hglobalCard)
  have hlower : r + 1 ≤ K.dist root0 (Sum.inl p) := by
    exact hdistance p hpdefect hreachp
  omega

/-! ## Absolute boundary tails -/

/-- Pointwise tilted domination for the difference of one connected
decorated cluster under two exterior fields.  Clusters which do not reach a
disagreement plaquette cancel exactly; clusters which do reach it pay the
full spatial tilt. -/
theorem pow_mul_norm_decoratedMayerTerm_withExterior_sub_le_tilted
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (η η' : Gauge.Configuration d G)
    (hF : F.support ⊆ Λ.dynamicEdges) (r : ℕ)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ))
    (hroot : FinitePolymerModel.exclusiveRootMultiplicity X = 1)
    (hdistance : ∀ p ∈ boundaryDisagreementPlaquettes Λ η η',
      (bivariateObservableSpatialGraph F F Λ).Reachable
        (Sum.inr 0) (Sum.inl p) →
      r + 1 ≤ (bivariateObservableSpatialGraph F F Λ).dist
        (Sum.inr 0) (Sum.inl p)) :
    plaquetteCardinalityTilt (d := d) Φ β ^ r *
        ‖(decoratedObservableRootModel F (withExterior Λ η) Φ β 1).mayerClusterTerm X -
          (decoratedObservableRootModel F (withExterior Λ η') Φ β 1).mayerClusterTerm X‖ ≤
      ‖(decoratedObservableCardinalityTiltedModel
          F (withExterior Λ η) Φ β 1).mayerClusterTerm X‖ +
        ‖(decoratedObservableCardinalityTiltedModel
          F (withExterior Λ η') Φ β 1).mayerClusterTerm X‖ := by
  let t := plaquetteCardinalityTilt (d := d) Φ β
  let a := (decoratedObservableRootModel
    F (withExterior Λ η) Φ β 1).mayerClusterTerm X
  let b := (decoratedObservableRootModel
    F (withExterior Λ η') Φ β 1).mayerClusterTerm X
  let aTilt := (decoratedObservableCardinalityTiltedModel
    F (withExterior Λ η) Φ β 1).mayerClusterTerm X
  let bTilt := (decoratedObservableCardinalityTiltedModel
    F (withExterior Λ η') Φ β 1).mayerClusterTerm X
  have ht : 1 < t := one_lt_plaquetteCardinalityTilt Φ hβ
  by_cases hreaches : ¬Disjoint
      (activeSubset Λ (decoratedObservableMayerPlaquetteSupport F Λ X))
      (boundaryDisagreementPlaquettes Λ η η')
  · have ha : t ^ r * ‖a‖ ≤ ‖aTilt‖ := by
      by_cases hzero : a = 0
      · simp [hzero]
      · let weightη := FinitePolymerModel.weightedMultiplicity
          (decoratedObservablePlaquetteCardinality F (withExterior Λ η)) X
        have hreachesη : ¬Disjoint
            (activeSubset (withExterior Λ η)
              (decoratedObservableMayerPlaquetteSupport
                F (withExterior Λ η) X))
            (boundaryDisagreementPlaquettes Λ η η') := by
          simpa only [decoratedObservableMayerPlaquetteSupport_withExterior,
            activeSubset_withExterior] using hreaches
        have hdistanceη : ∀ p ∈ boundaryDisagreementPlaquettes Λ η η',
            (bivariateObservableSpatialGraph F F (withExterior Λ η)).Reachable
              (Sum.inr 0) (Sum.inl p) →
            r + 1 ≤
              (bivariateObservableSpatialGraph F F (withExterior Λ η)).dist
                (Sum.inr 0) (Sum.inl p) := by
          simpa only [bivariateObservableSpatialGraph_withExterior] using hdistance
        have hr : r ≤ weightη := by
          exact decoratedObservable_boundaryReaching_nonzero_weightedMultiplicity_ge
            F (withExterior Λ η) Φ β
            (boundaryDisagreementPlaquettes Λ η η') r X hroot hzero
            hreachesη hdistanceη
        have hpow : t ^ r ≤ t ^ weightη :=
          pow_le_pow_right₀ ht.le hr
        have haTilt : aTilt = (t : ℂ) ^ weightη * a := by
          exact decoratedObservableCardinalityTiltedModel_mayerClusterTerm
            F (withExterior Λ η) Φ β 1 X
        calc
          t ^ r * ‖a‖ ≤ t ^ weightη * ‖a‖ :=
            mul_le_mul_of_nonneg_right hpow (norm_nonneg a)
          _ = ‖aTilt‖ := by
            rw [haTilt, norm_mul, norm_pow]
            simp [t, norm_mul, norm_pow,
              abs_of_pos (zero_lt_one.trans ht)]
    have hb : t ^ r * ‖b‖ ≤ ‖bTilt‖ := by
      by_cases hzero : b = 0
      · simp [hzero]
      · let weightη' := FinitePolymerModel.weightedMultiplicity
          (decoratedObservablePlaquetteCardinality F (withExterior Λ η')) X
        have hreachesη' : ¬Disjoint
            (activeSubset (withExterior Λ η')
              (decoratedObservableMayerPlaquetteSupport
                F (withExterior Λ η') X))
            (boundaryDisagreementPlaquettes Λ η η') := by
          simpa only [decoratedObservableMayerPlaquetteSupport_withExterior,
            activeSubset_withExterior] using hreaches
        have hdistanceη' : ∀ p ∈ boundaryDisagreementPlaquettes Λ η η',
            (bivariateObservableSpatialGraph F F (withExterior Λ η')).Reachable
              (Sum.inr 0) (Sum.inl p) →
            r + 1 ≤
              (bivariateObservableSpatialGraph F F (withExterior Λ η')).dist
                (Sum.inr 0) (Sum.inl p) := by
          simpa only [bivariateObservableSpatialGraph_withExterior] using hdistance
        have hr : r ≤ weightη' := by
          exact decoratedObservable_boundaryReaching_nonzero_weightedMultiplicity_ge
            F (withExterior Λ η') Φ β
            (boundaryDisagreementPlaquettes Λ η η') r X hroot hzero
            hreachesη' hdistanceη'
        have hpow : t ^ r ≤ t ^ weightη' :=
          pow_le_pow_right₀ ht.le hr
        have hbTilt : bTilt = (t : ℂ) ^ weightη' * b := by
          exact decoratedObservableCardinalityTiltedModel_mayerClusterTerm
            F (withExterior Λ η') Φ β 1 X
        calc
          t ^ r * ‖b‖ ≤ t ^ weightη' * ‖b‖ :=
            mul_le_mul_of_nonneg_right hpow (norm_nonneg b)
          _ = ‖bTilt‖ := by
            rw [hbTilt, norm_mul, norm_pow]
            simp [t, norm_mul, norm_pow,
              abs_of_pos (zero_lt_one.trans ht)]
    have htri : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
    have hpowNonneg : 0 ≤ t ^ r := by positivity
    change t ^ r * ‖a - b‖ ≤ ‖aTilt‖ + ‖bTilt‖
    nlinarith
  · have hdisjoint : Disjoint
        (activeSubset Λ (decoratedObservableMayerPlaquetteSupport F Λ X))
        (boundaryDisagreementPlaquettes Λ η η') := not_not.mp hreaches
    have hab : a = b := by
      exact decoratedObservableRootModel_mayerClusterTerm_withExterior_eq_of_disjoint
        F Λ Φ β 1 η η' hF X hdisjoint
    change t ^ r * ‖a - b‖ ≤ ‖aTilt‖ + ‖bTilt‖
    rw [hab, sub_self, norm_zero, mul_zero]
    positivity

/-- Absolute sum of termwise exterior differences in one total Mayer
degree, restricted to the multiplicity-one observable-root sector. -/
def decoratedObservableBoundaryDifferenceNormDegreeSum
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (η η' : Gauge.Configuration d G) (n : ℕ) : ℝ :=
  ∑ X ∈ FinitePolymerModel.mayerMultiIndicesOfDegree
      (P := PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) n,
    if FinitePolymerModel.exclusiveRootMultiplicity X = 1 then
      ‖(decoratedObservableRootModel
          F (withExterior Λ η) Φ β 1).mayerClusterTerm X -
        (decoratedObservableRootModel
          F (withExterior Λ η') Φ β 1).mayerClusterTerm X‖
    else 0

/-- Degreewise boundary tail obtained by summing the pointwise cluster
cancellation estimate. -/
theorem pow_mul_decoratedObservableBoundaryDifferenceNormDegreeSum_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (η η' : Gauge.Configuration d G)
    (hF : F.support ⊆ Λ.dynamicEdges) (r n : ℕ)
    (hdistance : ∀ p ∈ boundaryDisagreementPlaquettes Λ η η',
      (bivariateObservableSpatialGraph F F Λ).Reachable
        (Sum.inr 0) (Sum.inl p) →
      r + 1 ≤ (bivariateObservableSpatialGraph F F Λ).dist
        (Sum.inr 0) (Sum.inl p)) :
    plaquetteCardinalityTilt (d := d) Φ β ^ r *
        decoratedObservableBoundaryDifferenceNormDegreeSum
          F Λ Φ β η η' n ≤
      (decoratedObservableCardinalityTiltedModel
          F (withExterior Λ η) Φ β 1).exclusiveRootLinearNormMayerDegreeSum n +
        (decoratedObservableCardinalityTiltedModel
          F (withExterior Λ η') Φ β 1).exclusiveRootLinearNormMayerDegreeSum n := by
  classical
  unfold decoratedObservableBoundaryDifferenceNormDegreeSum
    FinitePolymerModel.exclusiveRootLinearNormMayerDegreeSum
  simp only [mayerMultiIndicesOfDegree_withExterior]
  rw [Finset.mul_sum]
  calc
    (∑ X ∈ FinitePolymerModel.mayerMultiIndicesOfDegree
          (P := PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) n,
        plaquetteCardinalityTilt (d := d) Φ β ^ r *
          (if FinitePolymerModel.exclusiveRootMultiplicity X = 1 then
            ‖(decoratedObservableRootModel
                F (withExterior Λ η) Φ β 1).mayerClusterTerm X -
              (decoratedObservableRootModel
                F (withExterior Λ η') Φ β 1).mayerClusterTerm X‖
           else 0)) ≤
        ∑ X ∈ FinitePolymerModel.mayerMultiIndicesOfDegree
          (P := PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) n,
          ((if FinitePolymerModel.exclusiveRootMultiplicity X = 1 then
              ‖(decoratedObservableCardinalityTiltedModel
                F (withExterior Λ η) Φ β 1).mayerClusterTerm X‖ else 0) +
            (if FinitePolymerModel.exclusiveRootMultiplicity X = 1 then
              ‖(decoratedObservableCardinalityTiltedModel
                F (withExterior Λ η') Φ β 1).mayerClusterTerm X‖ else 0)) := by
      apply Finset.sum_le_sum
      intro X _hX
      by_cases hroot : FinitePolymerModel.exclusiveRootMultiplicity X = 1
      · simp only [hroot, if_true]
        exact pow_mul_norm_decoratedMayerTerm_withExterior_sub_le_tilted
          F Λ Φ hβ η η' hF r X hroot hdistance
      · simp [hroot]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      rfl

/-- The norm of the difference of the two connected coefficients is bounded
by the termwise absolute difference sum. -/
private theorem norm_finset_ite_sum_sub_sum_ite_le
    {P : Type*} (s : Finset P) (p : P → Prop) [DecidablePred p]
    (a b : P → ℂ) :
    ‖(∑ x ∈ s, if p x then a x else 0) -
        ∑ x ∈ s, if p x then b x else 0‖ ≤
      ∑ x ∈ s, if p x then ‖a x - b x‖ else 0 := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ x ∈ s,
        ((if p x then a x else 0) - (if p x then b x else 0))‖ ≤
        ∑ x ∈ s,
          ‖(if p x then a x else 0) - (if p x then b x else 0)‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : p x <;> simp [hx]

theorem norm_decoratedObservableRootLinearMayerDegreeSum_withExterior_sub_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (η η' : Gauge.Configuration d G) (n : ℕ) :
    ‖decoratedObservableRootLinearMayerDegreeSum
        F (withExterior Λ η) Φ β n -
      decoratedObservableRootLinearMayerDegreeSum
        F (withExterior Λ η') Φ β n‖ ≤
      decoratedObservableBoundaryDifferenceNormDegreeSum
        F Λ Φ β η η' n := by
  classical
  unfold decoratedObservableRootLinearMayerDegreeSum
    FinitePolymerModel.exclusiveRootLinearMayerDegreeSum
    decoratedObservableBoundaryDifferenceNormDegreeSum
  simpa only [mayerMultiIndicesOfDegree_withExterior] using
    (norm_finset_ite_sum_sub_sum_ite_le
      (s := FinitePolymerModel.mayerMultiIndicesOfDegree
        (P := PlaquettePolymer (withExterior Λ η) ⊕
          ObservableRootDecoration F (withExterior Λ η)) n)
      (p := fun X => FinitePolymerModel.exclusiveRootMultiplicity X = 1)
      (a := fun X => (decoratedObservableRootModel
        F (withExterior Λ η) Φ β 1).mayerClusterTerm X)
      (b := fun X => (decoratedObservableRootModel
        F (withExterior Λ η') Φ β 1).mayerClusterTerm X))

theorem decoratedObservableBoundaryDifferenceNormDegreeSum_nonneg
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (η η' : Gauge.Configuration d G) (n : ℕ) :
    0 ≤ decoratedObservableBoundaryDifferenceNormDegreeSum
      F Λ Φ β η η' n := by
  classical
  unfold decoratedObservableBoundaryDifferenceNormDegreeSum
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

@[simp]
theorem decoratedObservableRootLinearMayerDegreeSum_zero
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    decoratedObservableRootLinearMayerDegreeSum F Λ Φ β 0 = 0 := by
  classical
  unfold decoratedObservableRootLinearMayerDegreeSum
    FinitePolymerModel.exclusiveRootLinearMayerDegreeSum
  simp [FinitePolymerModel.mayerMultiIndicesOfDegree,
    FinitePolymerModel.exclusiveRootMultiplicity]

/-- The cardinality-weighted absolute boundary-difference series is genuinely
summable.  This is the analytic form of the cluster boundary tail before its
explicit KP budget is applied. -/
theorem summable_pow_mul_decoratedObservableBoundaryDifferenceNormDegreeSum_succ
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (η η' : Gauge.Configuration d G)
    (hF : F.support ⊆ Λ.dynamicEdges) (r : ℕ)
    (hdistance : ∀ p ∈ boundaryDisagreementPlaquettes Λ η η',
      (bivariateObservableSpatialGraph F F Λ).Reachable
        (Sum.inr 0) (Sum.inl p) →
      r + 1 ≤ (bivariateObservableSpatialGraph F F Λ).dist
        (Sum.inr 0) (Sum.inl p)) :
    Summable (fun n : ℕ =>
      plaquetteCardinalityTilt (d := d) Φ β ^ r *
        decoratedObservableBoundaryDifferenceNormDegreeSum
          F Λ Φ β η η' (n + 1)) := by
  let Aη := decoratedObservableCardinalityTiltedModel
    F (withExterior Λ η) Φ β 1
  let Aη' := decoratedObservableCardinalityTiltedModel
    F (withExterior Λ η') Φ β 1
  have hright : Summable (fun n : ℕ =>
      Aη.exclusiveRootLinearNormMayerDegreeSum (n + 1) +
        Aη'.exclusiveRootLinearNormMayerDegreeSum (n + 1)) :=
    (summable_decoratedObservableCardinalityTiltedLinearNormMayerDegreeSum_succ
      F (withExterior Λ η) Φ hβ).add
      (summable_decoratedObservableCardinalityTiltedLinearNormMayerDegreeSum_succ
        F (withExterior Λ η') Φ hβ)
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg
      (pow_nonneg (plaquetteCardinalityTilt_nonneg Φ hβ) r)
      (decoratedObservableBoundaryDifferenceNormDegreeSum_nonneg
        F Λ Φ β η η' (n + 1)))
    (fun n => by
      simpa [Aη, Aη'] using
        (pow_mul_decoratedObservableBoundaryDifferenceNormDegreeSum_le
          F Λ Φ hβ η η' hF r (n + 1) hdistance))
    hright

/-- Explicit volume-free KP/tree estimate for the complete boundary-reaching
one-root cluster tail. -/
theorem pow_mul_tsum_decoratedObservableBoundaryDifferenceNormDegreeSum_succ_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (η η' : Gauge.Configuration d G)
    (hF : F.support ⊆ Λ.dynamicEdges) (r : ℕ)
    (hdistance : ∀ p ∈ boundaryDisagreementPlaquettes Λ η η',
      (bivariateObservableSpatialGraph F F Λ).Reachable
        (Sum.inr 0) (Sum.inl p) →
      r + 1 ≤ (bivariateObservableSpatialGraph F F Λ).dist
        (Sum.inr 0) (Sum.inl p)) :
    plaquetteCardinalityTilt (d := d) Φ β ^ r *
        (∑' n : ℕ, decoratedObservableBoundaryDifferenceNormDegreeSum
          F Λ Φ β η η' (n + 1)) ≤
      2 * observableCardinalityTiltDecorationBudget (d := d) F Φ β := by
  let Aη := decoratedObservableCardinalityTiltedModel
    F (withExterior Λ η) Φ β 1
  let Aη' := decoratedObservableCardinalityTiltedModel
    F (withExterior Λ η') Φ β 1
  have hleft :=
    summable_pow_mul_decoratedObservableBoundaryDifferenceNormDegreeSum_succ
      F Λ Φ hβ η η' hF r hdistance
  have hη :=
    summable_decoratedObservableCardinalityTiltedLinearNormMayerDegreeSum_succ
      F (withExterior Λ η) Φ hβ
  have hη' :=
    summable_decoratedObservableCardinalityTiltedLinearNormMayerDegreeSum_succ
      F (withExterior Λ η') Φ hβ
  rw [← tsum_mul_left]
  calc
    ∑' n : ℕ,
        plaquetteCardinalityTilt (d := d) Φ β ^ r *
          decoratedObservableBoundaryDifferenceNormDegreeSum
            F Λ Φ β η η' (n + 1) ≤
        ∑' n : ℕ,
          (Aη.exclusiveRootLinearNormMayerDegreeSum (n + 1) +
            Aη'.exclusiveRootLinearNormMayerDegreeSum (n + 1)) := by
      exact hleft.tsum_le_tsum
        (fun n => by
          simpa [Aη, Aη'] using
            (pow_mul_decoratedObservableBoundaryDifferenceNormDegreeSum_le
              F Λ Φ hβ η η' hF r (n + 1) hdistance))
        (hη.add hη')
    _ = (∑' n : ℕ, Aη.exclusiveRootLinearNormMayerDegreeSum (n + 1)) +
        ∑' n : ℕ, Aη'.exclusiveRootLinearNormMayerDegreeSum (n + 1) :=
      Summable.tsum_add hη hη'
    _ ≤ observableCardinalityTiltDecorationBudget (d := d) F Φ β +
        observableCardinalityTiltDecorationBudget (d := d) F Φ β := by
      exact add_le_add
        (tsum_decoratedObservableCardinalityTiltedLinearNormMayerDegreeSum_succ_le
          F (withExterior Λ η) Φ hβ)
        (tsum_decoratedObservableCardinalityTiltedLinearNormMayerDegreeSum_succ_le
          F (withExterior Λ η') Φ hβ)
    _ = 2 * observableCardinalityTiltDecorationBudget (d := d) F Φ β := by
      ring

/-- Cluster-expansion boundary mixing for an arbitrary local observable.  The
exponential factor is the explicit cardinality tilt left by the strict slack
in the finite-volume KP certificate. -/
theorem pow_mul_norm_complexGibbsExpectation_withExterior_sub_le_boundaryBudget
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (η η' : Gauge.Configuration d G)
    (hF : F.support ⊆ Λ.dynamicEdges) (r : ℕ)
    (hdistance : ∀ p ∈ boundaryDisagreementPlaquettes Λ η η',
      (bivariateObservableSpatialGraph F F Λ).Reachable
        (Sum.inr 0) (Sum.inl p) →
      r + 1 ≤ (bivariateObservableSpatialGraph F F Λ).dist
        (Sum.inr 0) (Sum.inl p)) :
    plaquetteCardinalityTilt (d := d) Φ β ^ r *
        ‖complexGibbsExpectation F (withExterior Λ η) Φ β -
          complexGibbsExpectation F (withExterior Λ η') Φ β‖ ≤
      2 * observableCardinalityTiltDecorationBudget (d := d) F Φ β := by
  let cη : ℕ → ℂ := fun n =>
    decoratedObservableRootLinearMayerDegreeSum
      F (withExterior Λ η) Φ β n
  let cη' : ℕ → ℂ := fun n =>
    decoratedObservableRootLinearMayerDegreeSum
      F (withExterior Λ η') Φ β n
  have hηNormAll : Summable (fun n : ℕ => ‖cη n‖) := by
    simpa [cη] using
      (summable_norm_decoratedObservableRootLinearMayerDegreeSum
        F (withExterior Λ η) Φ hβ)
  have hη'NormAll : Summable (fun n : ℕ => ‖cη' n‖) := by
    simpa [cη'] using
      (summable_norm_decoratedObservableRootLinearMayerDegreeSum
        F (withExterior Λ η') Φ hβ)
  have hηAll : Summable cη := hηNormAll.of_norm
  have hη'All : Summable cη' := hη'NormAll.of_norm
  have hη : Summable (fun n : ℕ => cη (n + 1)) :=
    (summable_nat_add_iff (f := cη) 1).mpr hηAll
  have hη' : Summable (fun n : ℕ => cη' (n + 1)) :=
    (summable_nat_add_iff (f := cη') 1).mpr hη'All
  have hseriesη : complexGibbsExpectation F (withExterior Λ η) Φ β =
      ∑' n : ℕ, cη (n + 1) := by
    rw [complexGibbsExpectation_eq_tsum_connectedDecoratedRoot
      F (withExterior Λ η) Φ hβ
        (complexPartitionFunction_ne_zero_of_norm_lt_latticeRadius
          (withExterior Λ η) Φ hβ)]
    have hsplit := hηAll.sum_add_tsum_nat_add 1
    have hzero : cη 0 = 0 := by simp [cη]
    simp only [Finset.sum_range_one, hzero, zero_add] at hsplit
    exact hsplit.symm
  have hseriesη' : complexGibbsExpectation F (withExterior Λ η') Φ β =
      ∑' n : ℕ, cη' (n + 1) := by
    rw [complexGibbsExpectation_eq_tsum_connectedDecoratedRoot
      F (withExterior Λ η') Φ hβ
        (complexPartitionFunction_ne_zero_of_norm_lt_latticeRadius
          (withExterior Λ η') Φ hβ)]
    have hsplit := hη'All.sum_add_tsum_nat_add 1
    have hzero : cη' 0 = 0 := by simp [cη']
    simp only [Finset.sum_range_one, hzero, zero_add] at hsplit
    exact hsplit.symm
  have hweighted :=
    summable_pow_mul_decoratedObservableBoundaryDifferenceNormDegreeSum_succ
      F Λ Φ hβ η η' hF r hdistance
  have htOne : 1 ≤ plaquetteCardinalityTilt (d := d) Φ β ^ r :=
    one_le_pow₀ (one_lt_plaquetteCardinalityTilt Φ hβ).le
  have hboundary : Summable (fun n : ℕ =>
      decoratedObservableBoundaryDifferenceNormDegreeSum
        F Λ Φ β η η' (n + 1)) := by
    exact Summable.of_nonneg_of_le
      (fun n => decoratedObservableBoundaryDifferenceNormDegreeSum_nonneg
        F Λ Φ β η η' (n + 1))
      (fun n => by
        have h := mul_le_mul_of_nonneg_right htOne
          (decoratedObservableBoundaryDifferenceNormDegreeSum_nonneg
            F Λ Φ β η η' (n + 1))
        simpa only [one_mul] using h)
      hweighted
  have hdiffNorm : Summable (fun n : ℕ =>
      ‖cη (n + 1) - cη' (n + 1)‖) := (hη.sub hη').norm
  rw [hseriesη, hseriesη', ← Summable.tsum_sub hη hη']
  calc
    plaquetteCardinalityTilt (d := d) Φ β ^ r *
        ‖∑' n : ℕ, (cη (n + 1) - cη' (n + 1))‖ ≤
      plaquetteCardinalityTilt (d := d) Φ β ^ r *
        (∑' n : ℕ, ‖cη (n + 1) - cη' (n + 1)‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_tsum_le_tsum_norm hdiffNorm)
        (pow_nonneg (plaquetteCardinalityTilt_nonneg Φ hβ) r)
    _ ≤ plaquetteCardinalityTilt (d := d) Φ β ^ r *
        (∑' n : ℕ, decoratedObservableBoundaryDifferenceNormDegreeSum
          F Λ Φ β η η' (n + 1)) := by
      apply mul_le_mul_of_nonneg_left
      · exact hdiffNorm.tsum_le_tsum
          (fun n => by
            simpa [cη, cη'] using
              (norm_decoratedObservableRootLinearMayerDegreeSum_withExterior_sub_le
                F Λ Φ β η η' (n + 1)))
          hboundary
      · exact pow_nonneg (plaquetteCardinalityTilt_nonneg Φ hβ) r
    _ ≤ _ :=
      pow_mul_tsum_decoratedObservableBoundaryDifferenceNormDegreeSum_succ_le
        F Λ Φ hβ η η' hF r hdistance

end

end YangMills.StrongCoupling
