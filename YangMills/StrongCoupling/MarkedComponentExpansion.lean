/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.BigradedSource
import YangMills.StrongCoupling.ObservableRootPolymer

/-!
# Observable-root decomposition of the marked plaquette expansion

This file splits the canonical connected components of a marked plaquette
subset into those touching the local observable and those disjoint from it.
The latter components factor exactly out of the marked Haar integral.  This is
the model-specific resummation bridge between the exact marked numerator and
the augmented-root Mayer majorants.
-/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Polymer

noncomputable section

local instance markedComponentDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- Canonical connected components of `X` that touch the observable root. -/
def observableComponentFamily (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d)) :
    Finset (PlaquettePolymer Λ) :=
  (componentFamily Λ X).filter (observableRootTouches F Λ)

/-- Canonical connected components of `X` that avoid the observable root. -/
def awayComponentFamily (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d)) :
    Finset (PlaquettePolymer Λ) :=
  (componentFamily Λ X).filter fun γ => ¬observableRootTouches F Λ γ

@[simp]
theorem mem_observableComponentFamily (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d))
    (γ : PlaquettePolymer Λ) :
    γ ∈ observableComponentFamily F Λ X ↔
      γ ∈ componentFamily Λ X ∧ observableRootTouches F Λ γ := by
  simp [observableComponentFamily]

@[simp]
theorem mem_awayComponentFamily (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d))
    (γ : PlaquettePolymer Λ) :
    γ ∈ awayComponentFamily F Λ X ↔
      γ ∈ componentFamily Λ X ∧ ¬observableRootTouches F Λ γ := by
  simp [awayComponentFamily]

/-- Root-touching and away components partition the canonical component
family. -/
theorem observableComponentFamily_union_awayComponentFamily
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) :
    observableComponentFamily F Λ X ∪ awayComponentFamily F Λ X =
      componentFamily Λ X := by
  classical
  ext γ
  simp only [Finset.mem_union, mem_observableComponentFamily,
    mem_awayComponentFamily]
  constructor
  · rintro (⟨hγ, _⟩ | ⟨hγ, _⟩) <;> exact hγ
  · intro hγ
    by_cases htouch : observableRootTouches F Λ γ
    · exact Or.inl ⟨hγ, htouch⟩
    · exact Or.inr ⟨hγ, htouch⟩

/-- The two component subfamilies are disjoint. -/
theorem disjoint_observableComponentFamily_awayComponentFamily
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) :
    Disjoint (observableComponentFamily F Λ X) (awayComponentFamily F Λ X) := by
  classical
  exact Finset.disjoint_left.mpr fun γ hroot haway =>
    (mem_awayComponentFamily F Λ X γ).mp haway |>.2
      ((mem_observableComponentFamily F Λ X γ).mp hroot |>.2)

/-! ## Two-observable component classes -/

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- A polymer touches the union support of a product observable exactly when
it touches at least one factor. -/
theorem observableRootTouches_mul_iff
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (γ : PlaquettePolymer Λ) :
    observableRootTouches (F.mul H) Λ γ ↔
      observableRootTouches F Λ γ ∨ observableRootTouches H Λ γ := by
  classical
  have hroot : observableRootPlaquettes Λ (F.mul H) =
      observableRootPlaquettes Λ F ∪ observableRootPlaquettes Λ H := by
    ext p
    rw [Finset.mem_union, mem_observableRootPlaquettes,
      mem_observableRootPlaquettes, mem_observableRootPlaquettes]
    change ¬Disjoint p.1.boundary.edgeSupport (F.support ∪ H.support) ↔ _
    rw [Finset.disjoint_union_right]
    tauto
  unfold observableRootTouches
  rw [hroot, Finset.disjoint_union_right]
  tauto

/-- Canonical components touching the first observable but not the second. -/
def firstOnlyComponentFamily (F H : LocalObservable d G)
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d)) :
    Finset (PlaquettePolymer Λ) :=
  (componentFamily Λ X).filter fun γ =>
    observableRootTouches F Λ γ ∧ ¬observableRootTouches H Λ γ

/-- Canonical components touching the second observable but not the first. -/
def secondOnlyComponentFamily (F H : LocalObservable d G)
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d)) :
    Finset (PlaquettePolymer Λ) :=
  (componentFamily Λ X).filter fun γ =>
    ¬observableRootTouches F Λ γ ∧ observableRootTouches H Λ γ

/-- Canonical components that already meet both observable supports. -/
def jointlyObservableComponentFamily (F H : LocalObservable d G)
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d)) :
    Finset (PlaquettePolymer Λ) :=
  (componentFamily Λ X).filter fun γ =>
    observableRootTouches F Λ γ ∧ observableRootTouches H Λ γ

/-- Canonical components avoiding both observable supports. -/
def twoObservableAwayComponentFamily (F H : LocalObservable d G)
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d)) :
    Finset (PlaquettePolymer Λ) :=
  (componentFamily Λ X).filter fun γ =>
    ¬observableRootTouches F Λ γ ∧ ¬observableRootTouches H Λ γ

@[simp]
theorem mem_firstOnlyComponentFamily
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) (γ : PlaquettePolymer Λ) :
    γ ∈ firstOnlyComponentFamily F H Λ X ↔
      γ ∈ componentFamily Λ X ∧ observableRootTouches F Λ γ ∧
        ¬observableRootTouches H Λ γ := by
  simp [firstOnlyComponentFamily]

@[simp]
theorem mem_secondOnlyComponentFamily
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) (γ : PlaquettePolymer Λ) :
    γ ∈ secondOnlyComponentFamily F H Λ X ↔
      γ ∈ componentFamily Λ X ∧ ¬observableRootTouches F Λ γ ∧
        observableRootTouches H Λ γ := by
  simp [secondOnlyComponentFamily]

@[simp]
theorem mem_jointlyObservableComponentFamily
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) (γ : PlaquettePolymer Λ) :
    γ ∈ jointlyObservableComponentFamily F H Λ X ↔
      γ ∈ componentFamily Λ X ∧ observableRootTouches F Λ γ ∧
        observableRootTouches H Λ γ := by
  simp [jointlyObservableComponentFamily]

@[simp]
theorem mem_twoObservableAwayComponentFamily
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) (γ : PlaquettePolymer Λ) :
    γ ∈ twoObservableAwayComponentFamily F H Λ X ↔
      γ ∈ componentFamily Λ X ∧ ¬observableRootTouches F Λ γ ∧
        ¬observableRootTouches H Λ γ := by
  simp [twoObservableAwayComponentFamily]

/-- The four two-observable classes partition the canonical components. -/
theorem twoObservableComponentFamilies_partition
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) :
    ((firstOnlyComponentFamily F H Λ X ∪
        secondOnlyComponentFamily F H Λ X) ∪
      jointlyObservableComponentFamily F H Λ X) ∪
        twoObservableAwayComponentFamily F H Λ X = componentFamily Λ X := by
  classical
  ext γ
  simp only [Finset.mem_union, mem_firstOnlyComponentFamily,
    mem_secondOnlyComponentFamily, mem_jointlyObservableComponentFamily,
    mem_twoObservableAwayComponentFamily]
  constructor
  · rintro (((⟨hgamma, _, _⟩ | ⟨hgamma, _, _⟩) |
        ⟨hgamma, _, _⟩) | ⟨hgamma, _, _⟩) <;> exact hgamma
  · intro hgamma
    by_cases hF : observableRootTouches F Λ γ
    · by_cases hH : observableRootTouches H Λ γ
      · exact Or.inl (Or.inr ⟨hgamma, hF, hH⟩)
      · exact Or.inl (Or.inl (Or.inl ⟨hgamma, hF, hH⟩))
    · by_cases hH : observableRootTouches H Λ γ
      · exact Or.inl (Or.inl (Or.inr ⟨hgamma, hF, hH⟩))
      · exact Or.inr ⟨hgamma, hF, hH⟩

/-! ## Exclusive marked root decorations -/

/-- A complete observable-root decoration is a compatible family of bulk
polymers, every member of which touches the observable.  The empty decoration
records the zero-plaquette marked term. -/
def ObservableRootDecoration (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) :=
  {Γ : Finset (PlaquettePolymer Λ) //
    ((Γ : Set (PlaquettePolymer Λ)).Pairwise fun γ δ =>
      ¬plaquettePolymerIncompatible Λ γ δ) ∧
    ∀ γ ∈ Γ, observableRootTouches F Λ γ}

instance (F : LocalObservable d G) (Λ : FiniteSpecification d G) :
    Fintype (ObservableRootDecoration F Λ) := by
  classical
  let candidates :=
    (Finset.univ : Finset (Finset (PlaquettePolymer Λ))).filter
      (fun Γ : Finset (PlaquettePolymer Λ) =>
      ((Γ : Set (PlaquettePolymer Λ)).Pairwise fun γ δ =>
        ¬plaquettePolymerIncompatible Λ γ δ) ∧
      ∀ γ ∈ Γ, observableRootTouches F Λ γ)
  exact Fintype.ofFinset candidates fun D => by
    change D ∈ candidates ↔
      (((D : Set (PlaquettePolymer Λ)).Pairwise fun γ δ =>
        ¬plaquettePolymerIncompatible Λ γ δ) ∧
      ∀ γ ∈ D, observableRootTouches F Λ γ)
    simp [candidates]

instance (F : LocalObservable d G) (Λ : FiniteSpecification d G) :
    DecidableEq (ObservableRootDecoration F Λ) := Classical.decEq _

/-- Untyped plaquette support carried by a complete root decoration. -/
def ObservableRootDecoration.support
    {F : LocalObservable d G} {Λ : FiniteSpecification d G}
    (D : ObservableRootDecoration F Λ) : Finset (Plaquette d) :=
  polymerFamilySupport Λ D.1

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Compatibility makes the untyped plaquette supports in a complete root
decoration pairwise disjoint. -/
theorem ObservableRootDecoration.pairwiseDisjoint_support
    {F : LocalObservable d G} {Λ : FiniteSpecification d G}
    (D : ObservableRootDecoration F Λ) :
    (D.1 : Set (PlaquettePolymer Λ)).PairwiseDisjoint
      PlaquettePolymer.support := by
  intro γ hγ δ hδ hγδ
  change Disjoint γ.support δ.support
  rw [Finset.disjoint_left]
  intro p hpγ hpδ
  rcases Finset.mem_map.mp hpγ with ⟨q, hqγ, hqp⟩
  rcases Finset.mem_map.mp hpδ with ⟨r, hrδ, hrp⟩
  have hqr : q = r := Subtype.ext (hqp.trans hrp.symm)
  exact (D.2.1 hγ hδ hγδ) ⟨q, hqγ, r, hrδ, Or.inl hqr⟩

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- The size of a compatible decoration is the sum of the sizes of its
connected polymer members. -/
theorem ObservableRootDecoration.card_support
    {F : LocalObservable d G} {Λ : FiniteSpecification d G}
    (D : ObservableRootDecoration F Λ) :
    D.support.card = ∑ γ ∈ D.1, γ.1.card := by
  classical
  unfold ObservableRootDecoration.support polymerFamilySupport
  rw [Finset.card_biUnion D.pairwiseDisjoint_support]
  apply Finset.sum_congr rfl
  intro γ _
  exact Finset.card_map _

/-! ## Exact bivariate decoration roots -/

/-- A complete product-observable decoration containing an intrinsic bridge:
one of its connected plaquette polymers touches both observable supports. -/
def TwoObservableBridgeDecoration (F H : LocalObservable d G)
    (Λ : FiniteSpecification d G) :=
  {D : ObservableRootDecoration (F.mul H) Λ //
    ∃ γ ∈ D.1, observableRootTouches F Λ γ ∧
      observableRootTouches H Λ γ}

instance (F H : LocalObservable d G) (Λ : FiniteSpecification d G) :
    Fintype (TwoObservableBridgeDecoration F H Λ) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

instance (F H : LocalObservable d G) (Λ : FiniteSpecification d G) :
    DecidableEq (TwoObservableBridgeDecoration F H Λ) := Classical.decEq _

/-- Untyped plaquette support absorbed into a bridge decoration. -/
def TwoObservableBridgeDecoration.support
    {F H : LocalObservable d G} {Λ : FiniteSpecification d G}
    (D : TwoObservableBridgeDecoration F H Λ) : Finset (Plaquette d) :=
  D.1.support

/-- Two complete one-sided decorations cannot coexist if either one already
touches the opposite observable or if one of their absorbed polymers is
incompatible with an absorbed polymer on the other side. -/
def observableRootDecorationsCrossIncompatible
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (D : ObservableRootDecoration F Λ)
    (E : ObservableRootDecoration H Λ) : Prop :=
  (∃ γ ∈ D.1, observableRootTouches H Λ γ) ∨
  (∃ δ ∈ E.1, observableRootTouches F Λ δ) ∨
  (∃ γ ∈ D.1, ∃ δ ∈ E.1,
    plaquettePolymerIncompatible Λ γ δ)

instance (F H : LocalObservable d G) (Λ : FiniteSpecification d G) :
    DecidableRel (observableRootDecorationsCrossIncompatible F H Λ) :=
  fun _ _ => Classical.propDecidable _

/-- A bulk polymer conflicts with a complete root decoration if it either
touches the observable directly or is incompatible with a polymer already
absorbed into the decoration. -/
def observableRootDecorationTouches
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (D : ObservableRootDecoration F Λ) (γ : PlaquettePolymer Λ) : Prop :=
  observableRootTouches F Λ γ ∨
    ∃ δ ∈ D.1, plaquettePolymerIncompatible Λ δ γ

instance (F : LocalObservable d G) (Λ : FiniteSpecification d G) :
    DecidableRel (observableRootDecorationTouches F Λ) :=
  fun _ _ => Classical.propDecidable _

/-- Exact bivariate decorated-root gas.  Left and right roots carry one
source each.  A bridge root carries both sources and is exclusive with every
other source root. -/
def bivariateDecoratedObservableRootModel
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) :
    FinitePolymerModel
      (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration H Λ) ⊕
          TwoObservableBridgeDecoration F H Λ) :=
  (plaquettePolymerModel Λ Φ β).augmentBivariateExclusiveRoots
    (observableRootDecorationTouches F Λ)
    (observableRootDecorationTouches H Λ)
    (fun D γ => observableRootDecorationTouches (F.mul H) Λ D.1 γ)
    (observableRootDecorationsCrossIncompatible F H Λ)
    (fun D => α * markedSubsetWeight F Λ Φ β D.support)
    (fun E => θ * markedSubsetWeight H Λ Φ β E.support)
    (fun D => α * θ * markedSubsetWeight (F.mul H) Λ Φ β D.support)

@[simp]
theorem bivariateDecoratedObservableRootModel_bulk_activity
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ)
    (γ : PlaquettePolymer Λ) :
    (bivariateDecoratedObservableRootModel F H Λ Φ β α θ).activity
      (Sum.inl (Sum.inl (Sum.inl γ))) =
        (plaquettePolymerModel Λ Φ β).activity γ := rfl

theorem bivariateDecoratedObservableRootModel_incompatible_source_independent
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ α' θ' : ℂ)
    (q r : ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) :
    (bivariateDecoratedObservableRootModel F H Λ Φ β α θ).incompatible q r ↔
      (bivariateDecoratedObservableRootModel F H Λ Φ β α' θ').incompatible q r :=
  Iff.rfl

@[simp]
theorem bivariateDecoratedObservableRootModel_left_activity
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ)
    (D : ObservableRootDecoration F Λ) :
    (bivariateDecoratedObservableRootModel F H Λ Φ β α θ).activity
      (Sum.inl (Sum.inl (Sum.inr D))) =
        α * markedSubsetWeight F Λ Φ β D.support := rfl

@[simp]
theorem bivariateDecoratedObservableRootModel_right_activity
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ)
    (E : ObservableRootDecoration H Λ) :
    (bivariateDecoratedObservableRootModel F H Λ Φ β α θ).activity
      (Sum.inl (Sum.inr E)) =
        θ * markedSubsetWeight H Λ Φ β E.support := rfl

@[simp]
theorem bivariateDecoratedObservableRootModel_bridge_activity
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ)
    (D : TwoObservableBridgeDecoration F H Λ) :
    (bivariateDecoratedObservableRootModel F H Λ Φ β α θ).activity
      (Sum.inr D) =
        α * θ * markedSubsetWeight (F.mul H) Λ Φ β D.support := rfl

/-- Source bidegree on the exact decorated gas: bulk polymers have degree
`(0,0)`, left and right decorations have degrees `(1,0)` and `(0,1)`, and
an intrinsic bridge decoration has degree `(1,1)`. -/
def bivariateDecoratedObservableRootGrading
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G) :
    (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) → Fin 2 → ℕ
  | Sum.inl (Sum.inl (Sum.inl _)), _ => 0
  | Sum.inl (Sum.inl (Sum.inr _)), i => if i = 0 then 1 else 0
  | Sum.inl (Sum.inr _), i => if i = 1 then 1 else 0
  | Sum.inr _, _ => 1

/-- The two scalar source values as a function on the two source
coordinates. -/
def bivariateObservableSourceValues (α θ : ℂ) : Fin 2 → ℂ :=
  fun i => if i = 0 then α else θ

theorem bigradedMultiplicity_bivariateDecorated_zero
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration H Λ) ⊕
          TwoObservableBridgeDecoration F H Λ)) :
    FinitePolymerModel.bigradedMultiplicity
        (bivariateDecoratedObservableRootGrading F H Λ) X 0 =
      (∑ D : ObservableRootDecoration F Λ,
          X (Sum.inl (Sum.inl (Sum.inr D)))) +
        ∑ B : TwoObservableBridgeDecoration F H Λ, X (Sum.inr B) := by
  classical
  simp [FinitePolymerModel.bigradedMultiplicity,
    bivariateDecoratedObservableRootGrading, Fintype.sum_sum_type]

theorem bigradedMultiplicity_bivariateDecorated_one
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration H Λ) ⊕
          TwoObservableBridgeDecoration F H Λ)) :
    FinitePolymerModel.bigradedMultiplicity
        (bivariateDecoratedObservableRootGrading F H Λ) X 1 =
      (∑ E : ObservableRootDecoration H Λ,
          X (Sum.inl (Sum.inr E))) +
        ∑ B : TwoObservableBridgeDecoration F H Λ, X (Sum.inr B) := by
  classical
  simp [FinitePolymerModel.bigradedMultiplicity,
    bivariateDecoratedObservableRootGrading, Fintype.sum_sum_type]

/-- Bidegree `(1,1)` has exactly one intrinsic bridge root, or else has one
left and one right decoration root. -/
theorem bivariateDecorated_mixed_root_pattern
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration H Λ) ⊕
          TwoObservableBridgeDecoration F H Λ))
    (hzero : FinitePolymerModel.bigradedMultiplicity
      (bivariateDecoratedObservableRootGrading F H Λ) X 0 = 1)
    (hone : FinitePolymerModel.bigradedMultiplicity
      (bivariateDecoratedObservableRootGrading F H Λ) X 1 = 1) :
    (∃ B : TwoObservableBridgeDecoration F H Λ,
        X (Sum.inr B) = 1) ∨
      ∃ D : ObservableRootDecoration F Λ,
        ∃ E : ObservableRootDecoration H Λ,
          X (Sum.inl (Sum.inl (Sum.inr D))) = 1 ∧
            X (Sum.inl (Sum.inr E)) = 1 := by
  classical
  rw [bigradedMultiplicity_bivariateDecorated_zero F H Λ X] at hzero
  rw [bigradedMultiplicity_bivariateDecorated_one F H Λ X] at hone
  by_cases hbridge : ∃ B : TwoObservableBridgeDecoration F H Λ,
      X (Sum.inr B) ≠ 0
  · rcases hbridge with ⟨B, hB⟩
    left
    refine ⟨B, ?_⟩
    have hle : X (Sum.inr B) ≤
        ∑ B' : TwoObservableBridgeDecoration F H Λ, X (Sum.inr B') := by
      exact Finset.single_le_sum
        (f := fun B' : TwoObservableBridgeDecoration F H Λ => X (Sum.inr B'))
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ B)
    omega
  · have hbridgeZero : ∀ B : TwoObservableBridgeDecoration F H Λ,
        X (Sum.inr B) = 0 := by
      intro B
      exact not_ne_iff.mp (not_exists.mp hbridge B)
    have hleftSum :
        ∑ D : ObservableRootDecoration F Λ,
          X (Sum.inl (Sum.inl (Sum.inr D))) = 1 := by
      simpa [hbridgeZero] using hzero
    have hrightSum :
        ∑ E : ObservableRootDecoration H Λ,
          X (Sum.inl (Sum.inr E)) = 1 := by
      simpa [hbridgeZero] using hone
    have hleftExists : ∃ D : ObservableRootDecoration F Λ,
        X (Sum.inl (Sum.inl (Sum.inr D))) ≠ 0 := by
      by_contra h
      push Not at h
      simp [h] at hleftSum
    have hrightExists : ∃ E : ObservableRootDecoration H Λ,
        X (Sum.inl (Sum.inr E)) ≠ 0 := by
      by_contra h
      push Not at h
      simp [h] at hrightSum
    rcases hleftExists with ⟨D, hD⟩
    rcases hrightExists with ⟨E, hE⟩
    right
    refine ⟨D, E, ?_, ?_⟩
    · have hle : X (Sum.inl (Sum.inl (Sum.inr D))) ≤
          ∑ D' : ObservableRootDecoration F Λ,
            X (Sum.inl (Sum.inl (Sum.inr D'))) := by
        exact Finset.single_le_sum
          (f := fun D' : ObservableRootDecoration F Λ =>
            X (Sum.inl (Sum.inl (Sum.inr D'))))
          (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ D)
      omega
    · have hle : X (Sum.inl (Sum.inr E)) ≤
          ∑ E' : ObservableRootDecoration H Λ,
            X (Sum.inl (Sum.inr E')) := by
        exact Finset.single_le_sum
          (f := fun E' : ObservableRootDecoration H Λ =>
            X (Sum.inl (Sum.inr E')))
          (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ E)
      omega

/-- Distinguished occurrence of a left decoration root. -/
def bivariateDecoratedLeftRootVertex
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration H Λ) ⊕
          TwoObservableBridgeDecoration F H Λ))
    (D : ObservableRootDecoration F Λ)
    (hD : X (Sum.inl (Sum.inl (Sum.inr D))) = 1) :
    FinitePolymerModel.MayerVertex X :=
  ⟨Sum.inl (Sum.inl (Sum.inr D)), ⟨0, by omega⟩⟩

/-- Distinguished occurrence of a right decoration root. -/
def bivariateDecoratedRightRootVertex
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : FinitePolymerModel.MayerMultiIndex
      (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration H Λ) ⊕
          TwoObservableBridgeDecoration F H Λ))
    (E : ObservableRootDecoration H Λ)
    (hE : X (Sum.inl (Sum.inr E)) = 1) :
    FinitePolymerModel.MayerVertex X :=
  ⟨Sum.inl (Sum.inr E), ⟨0, by omega⟩⟩

/-- Every nonzero `(1,1)` Mayer term has a literal support-spanning root
witness.  It either contains an intrinsic bridge decoration (whose subtype
data supplies a polymer touching both observables), or its unique left and
right decoration occurrences are joined by a simple path in the actual
Mayer incompatibility graph. -/
theorem bivariateDecorated_mixed_nonzero_spanning_witness
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
    (hterm : (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).mayerClusterTerm X ≠ 0) :
    (∃ B : TwoObservableBridgeDecoration F H Λ,
        X (Sum.inr B) = 1) ∨
      ∃ (D : ObservableRootDecoration F Λ)
        (E : ObservableRootDecoration H Λ)
        (hD : X (Sum.inl (Sum.inl (Sum.inr D))) = 1)
        (hE : X (Sum.inl (Sum.inr E)) = 1),
        ∃ path :
          ((bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).mayerIncompatibilityGraph X).Walk
              (bivariateDecoratedLeftRootVertex F H Λ X D hD)
              (bivariateDecoratedRightRootVertex F H Λ X E hE),
          path.IsPath := by
  rcases bivariateDecorated_mixed_root_pattern F H Λ X hzero hone with
    ⟨B, hB⟩ | ⟨D, E, hD, hE⟩
  · exact Or.inl ⟨B, hB⟩
  · right
    refine ⟨D, E, hD, hE, ?_⟩
    have hconnected :
        ((bivariateDecoratedObservableRootModel
          F H Λ Φ β 1 1).mayerIncompatibilityGraph X).Connected := by
      by_contra hnot
      exact hterm
        ((bivariateDecoratedObservableRootModel
          F H Λ Φ β 1 1).mayerClusterTerm_eq_zero_of_not_connected X hnot)
    exact hconnected.preconnected.exists_isPath
      (bivariateDecoratedLeftRootVertex F H Λ X D hD)
      (bivariateDecoratedRightRootVertex F H Λ X E hE)

/-- Scaling the unit-source decorated gas by its bidegree gives exactly the
gas with physical left and right sources. -/
theorem bivariateDecoratedObservableRootModel_scaled_activity
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ)
    (q : ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) :
    (Polymer.FinitePolymerModel.scaleByBigradedSource
        (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1)
        (bivariateDecoratedObservableRootGrading F H Λ)
        (bivariateObservableSourceValues α θ)).activity q =
      (bivariateDecoratedObservableRootModel F H Λ Φ β α θ).activity q := by
  rcases q with (((q | D) | E) | B) <;>
    simp [Polymer.FinitePolymerModel.scaleByBigradedSource,
      bivariateDecoratedObservableRootModel,
      Polymer.FinitePolymerModel.augmentBivariateExclusiveRoots,
      Polymer.FinitePolymerModel.augmentTwoColorExclusiveRoots,
      Polymer.FinitePolymerModel.augmentExclusiveRoots,
      bivariateDecoratedObservableRootGrading,
      bivariateObservableSourceValues, Fin.prod_univ_two]

/-- The source-scaled unit gas and the physical-source gas have identical
finite partition functions. -/
theorem bivariateDecoratedObservableRootModel_scaled_partitionFunction
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) :
    (Polymer.FinitePolymerModel.scaleByBigradedSource
        (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1)
        (bivariateDecoratedObservableRootGrading F H Λ)
        (bivariateObservableSourceValues α θ)).partitionFunction =
      (bivariateDecoratedObservableRootModel F H Λ Φ β α θ).partitionFunction := by
  classical
  unfold Polymer.FinitePolymerModel.partitionFunction
    Polymer.FinitePolymerModel.partitionOn
  have hfamilies :
      (Polymer.FinitePolymerModel.scaleByBigradedSource
          (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1)
          (bivariateDecoratedObservableRootGrading F H Λ)
          (bivariateObservableSourceValues α θ)).compatibleFamilies
            Finset.univ =
        (bivariateDecoratedObservableRootModel F H Λ Φ β α θ).compatibleFamilies
          Finset.univ := rfl
  rw [hfamilies]
  apply Finset.sum_congr rfl
  intro Γ _
  unfold Polymer.FinitePolymerModel.familyWeight
  apply Finset.prod_congr rfl
  intro q _
  exact bivariateDecoratedObservableRootModel_scaled_activity
    F H Λ Φ β α θ q

/-- The exclusive-root hard-core model whose root value stores the complete
marked decoration.  Its source coefficient is designed to reproduce the
exact marked numerator after the remaining finite reindexing. -/
def decoratedObservableRootModel
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ) :
    FinitePolymerModel
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) :=
  (plaquettePolymerModel Λ Φ β).augmentExclusiveRoots
    (observableRootDecorationTouches F Λ)
    (fun D => α * markedSubsetWeight F Λ Φ β D.support)

@[simp]
theorem decoratedObservableRootModel_root_activity
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ)
    (D : ObservableRootDecoration F Λ) :
    (decoratedObservableRootModel F Λ Φ β α).activity (Sum.inr D) =
      α * markedSubsetWeight F Λ Φ β D.support := rfl

@[simp]
theorem decoratedObservableRootModel_roots_exclusive
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ)
    (D E : ObservableRootDecoration F Λ) :
    (decoratedObservableRootModel F Λ Φ β α).incompatible
      (Sum.inr D) (Sum.inr E) := by
  trivial

/-- The root-touching canonical components of a plaquette subset form a
complete root decoration. -/
def observableRootDecorationOfSubset
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) : ObservableRootDecoration F Λ := by
  refine ⟨observableComponentFamily F Λ X, ?_, ?_⟩
  · intro γ hγ δ hδ hγδ
    exact componentFamily_compatible Λ Φ β X
      ((mem_observableComponentFamily F Λ X γ).mp hγ).1
      ((mem_observableComponentFamily F Λ X δ).mp hδ).1 hγδ
  · intro γ hγ
    exact ((mem_observableComponentFamily F Λ X γ).mp hγ).2

@[simp]
theorem observableRootDecorationOfSubset_val
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) :
    (observableRootDecorationOfSubset F Λ Φ β X).1 =
      observableComponentFamily F Λ X := rfl

/-- Standard KP weight for the exact decorated-root gas. -/
def decoratedObservableRootKPWeight
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) → ℝ :=
  (plaquettePolymerModel Λ Φ β).augmentRootKPWeight
    (observableRootDecorationTouches F Λ) plaquetteKPWeight

/-- Bulk polymer types allowed alongside a fixed complete root decoration. -/
def observableRootDecorationCompatibleBulk
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (D : ObservableRootDecoration F Λ) : Finset (PlaquettePolymer Λ) :=
  Finset.univ.filter fun γ => ¬observableRootDecorationTouches F Λ D γ

/-- All compatible decorated-root/bulk-family pairs. -/
def observableRootDecoratedPairs
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    Finset (ObservableRootDecoration F Λ × Finset (PlaquettePolymer Λ)) := by
  classical
  exact Finset.univ.filter fun pair =>
    (plaquettePolymerModel Λ Φ β).Compatible pair.2 ∧
      pair.2 ⊆ observableRootDecorationCompatibleBulk F Λ pair.1

/-- The model-specific decorated pairs are exactly the generic admissible
root/bulk pairs for the exclusive-root augmentation. -/
theorem observableRootDecoratedPairs_eq_exclusiveRootPairs
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    observableRootDecoratedPairs F Λ Φ β =
      (plaquettePolymerModel Λ Φ β).exclusiveRootPairs
        (observableRootDecorationTouches F Λ) := by
  classical
  ext pair
  simp only [observableRootDecoratedPairs, Polymer.FinitePolymerModel.exclusiveRootPairs,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcompatible, hsubset⟩
    refine ⟨hcompatible, fun gamma hgamma => ?_⟩
    exact (Finset.mem_filter.mp (hsubset hgamma)).2
  · rintro ⟨hcompatible, hallowed⟩
    refine ⟨hcompatible, fun gamma hgamma => ?_⟩
    rw [observableRootDecorationCompatibleBulk, Finset.mem_filter]
    exact ⟨Finset.mem_univ gamma, hallowed gamma hgamma⟩

/-- Coefficient of the exclusive decorated source, written directly as its
finite compatible-family sum. -/
def decoratedObservableRootCoefficient
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) : ℂ :=
  ∑ pair ∈ observableRootDecoratedPairs F Λ Φ β,
    markedSubsetWeight F Λ Φ β pair.1.support *
      (plaquettePolymerModel Λ Φ β).familyWeight pair.2

/-- The explicit lattice disk supplies a genuine KP certificate for the
exclusive decorated-root model at zero source. -/
theorem decoratedObservableRootModel_koteckyPreiss_zero
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    (decoratedObservableRootModel F Λ Φ β 0).KoteckyPreissCertificate
      Finset.univ (decoratedObservableRootKPWeight F Λ Φ β) := by
  have hbase :
      (plaquettePolymerModel Λ Φ β).KoteckyPreissCertificate
        Finset.univ plaquetteKPWeight := by
    apply plaquettePolymerModel_koteckyPreiss Λ Φ β
      (cubicPlaquetteAnimalCertificate Λ)
    exact perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
      (16 * d) (2 ^ (16 * d)) hβ
  simpa [decoratedObservableRootModel, decoratedObservableRootKPWeight] using
    (plaquettePolymerModel Λ Φ β).koteckyPreissCertificate_augmentExclusiveRoots_zero
        (observableRootDecorationTouches F Λ) plaquetteKPWeight hbase

/-! ## Bivariate decorated-root KP regularization -/

/-- Zero-source KP weight for the exact bivariate decorated gas, obtained by
the three successive exclusive-root lifts. -/
def bivariateDecoratedObservableRootKPWeight
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) → ℝ :=
  let M := plaquettePolymerModel Λ Φ β
  let Mleft := M.augmentExclusiveRoots
    (observableRootDecorationTouches F Λ) (fun _ => 0)
  let aleft := M.augmentRootKPWeight
    (observableRootDecorationTouches F Λ) plaquetteKPWeight
  let Mright := Mleft.augmentExclusiveRoots
    (Polymer.FinitePolymerModel.twoColorRightTouches
      (observableRootDecorationTouches H Λ)
      (observableRootDecorationsCrossIncompatible F H Λ)) (fun _ => 0)
  let aright := Mleft.augmentRootKPWeight
    (Polymer.FinitePolymerModel.twoColorRightTouches
      (observableRootDecorationTouches H Λ)
      (observableRootDecorationsCrossIncompatible F H Λ)) aleft
  Mright.augmentRootKPWeight
    (Polymer.FinitePolymerModel.bivariateBridgeTouches
      (fun (B : TwoObservableBridgeDecoration F H Λ) γ =>
        observableRootDecorationTouches (F.mul H) Λ B.1 γ)) aright

@[simp]
theorem bivariateDecoratedObservableRootKPWeight_bulk
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (γ : PlaquettePolymer Λ) :
    bivariateDecoratedObservableRootKPWeight F H Λ Φ β
        (Sum.inl (Sum.inl (Sum.inl γ))) = plaquetteKPWeight γ := rfl

theorem bivariateDecoratedObservableRootKPWeight_nonneg
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    ∀ q, 0 ≤ bivariateDecoratedObservableRootKPWeight F H Λ Φ β q := by
  let M := plaquettePolymerModel Λ Φ β
  let Mleft := M.augmentExclusiveRoots
    (observableRootDecorationTouches F Λ) (fun _ => 0)
  let aleft := M.augmentRootKPWeight
    (observableRootDecorationTouches F Λ) plaquetteKPWeight
  let Mright := Mleft.augmentExclusiveRoots
    (Polymer.FinitePolymerModel.twoColorRightTouches
      (observableRootDecorationTouches H Λ)
      (observableRootDecorationsCrossIncompatible F H Λ)) (fun _ => 0)
  let aright := Mleft.augmentRootKPWeight
    (Polymer.FinitePolymerModel.twoColorRightTouches
      (observableRootDecorationTouches H Λ)
      (observableRootDecorationsCrossIncompatible F H Λ)) aleft
  have hbulk : ∀ γ : PlaquettePolymer Λ, 0 ≤ plaquetteKPWeight γ := by
    intro γ
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num)).le
  have hleft : ∀ q, 0 ≤ aleft q := by
    exact M.augmentRootKPWeight_nonneg
      (observableRootDecorationTouches F Λ) plaquetteKPWeight hbulk
  have hright : ∀ q, 0 ≤ aright q := by
    exact Mleft.augmentRootKPWeight_nonneg
      (Polymer.FinitePolymerModel.twoColorRightTouches
        (observableRootDecorationTouches H Λ)
        (observableRootDecorationsCrossIncompatible F H Λ)) aleft hleft
  simpa only [bivariateDecoratedObservableRootKPWeight, M, Mleft, Mright,
    aleft, aright] using
      Mright.augmentRootKPWeight_nonneg
        (Polymer.FinitePolymerModel.bivariateBridgeTouches
          (fun (B : TwoObservableBridgeDecoration F H Λ) γ =>
            observableRootDecorationTouches (F.mul H) Λ B.1 γ)) aright hright

/-- The full exact bivariate decoration type inherits the explicit bulk KP
certificate at the zero-source expansion point. -/
theorem bivariateDecoratedObservableRootModel_koteckyPreiss_zero
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    (bivariateDecoratedObservableRootModel F H Λ Φ β 0 0).KoteckyPreissCertificate Finset.univ
        (bivariateDecoratedObservableRootKPWeight F H Λ Φ β) := by
  classical
  let M := plaquettePolymerModel Λ Φ β
  have hbase : M.KoteckyPreissCertificate Finset.univ plaquetteKPWeight := by
    dsimp [M]
    apply plaquettePolymerModel_koteckyPreiss Λ Φ β
      (cubicPlaquetteAnimalCertificate Λ)
    exact perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
      (16 * d) (2 ^ (16 * d)) hβ
  let Mleft := M.augmentExclusiveRoots
    (observableRootDecorationTouches F Λ) (fun _ => 0)
  let aleft := M.augmentRootKPWeight
    (observableRootDecorationTouches F Λ) plaquetteKPWeight
  have hleft : Mleft.KoteckyPreissCertificate Finset.univ aleft := by
    exact M.koteckyPreissCertificate_augmentExclusiveRoots_zero
      (observableRootDecorationTouches F Λ) plaquetteKPWeight hbase
  let Mright := Mleft.augmentExclusiveRoots
    (Polymer.FinitePolymerModel.twoColorRightTouches
      (observableRootDecorationTouches H Λ)
      (observableRootDecorationsCrossIncompatible F H Λ)) (fun _ => 0)
  let aright := Mleft.augmentRootKPWeight
    (Polymer.FinitePolymerModel.twoColorRightTouches
      (observableRootDecorationTouches H Λ)
      (observableRootDecorationsCrossIncompatible F H Λ)) aleft
  have hright : Mright.KoteckyPreissCertificate Finset.univ aright := by
    exact Mleft.koteckyPreissCertificate_augmentExclusiveRoots_zero
      (Polymer.FinitePolymerModel.twoColorRightTouches
        (observableRootDecorationTouches H Λ)
        (observableRootDecorationsCrossIncompatible F H Λ)) aleft hleft
  have hbridge := Mright.koteckyPreissCertificate_augmentExclusiveRoots_zero
    (Polymer.FinitePolymerModel.bivariateBridgeTouches
      (fun (B : TwoObservableBridgeDecoration F H Λ) γ =>
        observableRootDecorationTouches (F.mul H) Λ B.1 γ))
    aright hright
  simpa only [bivariateDecoratedObservableRootModel,
    bivariateDecoratedObservableRootKPWeight,
    Polymer.FinitePolymerModel.augmentBivariateExclusiveRoots,
    Polymer.FinitePolymerModel.augmentTwoColorExclusiveRoots,
    M, Mleft, Mright, aleft, aright, zero_mul] using hbridge

/-- Predicate selecting the three source-polymer summands of the exact
bivariate decorated type. -/
def BivariateDecoratedObservableRootIsSource
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G) :
    (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) → Prop
  | Sum.inl (Sum.inl (Sum.inl _)) => False
  | _ => True

instance (F H : LocalObservable d G) (Λ : FiniteSpecification d G) :
    DecidablePred (BivariateDecoratedObservableRootIsSource F H Λ) :=
  fun q => Classical.propDecidable
    (BivariateDecoratedObservableRootIsSource F H Λ q)

/-- The regularized KP weight keeps the bulk weight unchanged and gives every
source polymer one unit beyond its zero-source touching budget. -/
def bivariateDecoratedObservableRootRegularizedKPWeight
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) → ℝ
  | Sum.inl (Sum.inl (Sum.inl γ)) => plaquetteKPWeight γ
  | q => bivariateDecoratedObservableRootKPWeight F H Λ Φ β q + 1

@[simp]
theorem bivariateDecoratedObservableRootRegularizedKPWeight_bulk
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (γ : PlaquettePolymer Λ) :
    bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β
        (Sum.inl (Sum.inl (Sum.inl γ))) = plaquetteKPWeight γ := rfl

@[simp]
theorem bivariateDecoratedObservableRootRegularizedKPWeight_left
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (D : ObservableRootDecoration F Λ) :
    bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β
        (Sum.inl (Sum.inl (Sum.inr D))) =
      bivariateDecoratedObservableRootKPWeight F H Λ Φ β
        (Sum.inl (Sum.inl (Sum.inr D))) + 1 := rfl

@[simp]
theorem bivariateDecoratedObservableRootRegularizedKPWeight_right
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (E : ObservableRootDecoration H Λ) :
    bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β
        (Sum.inl (Sum.inr E)) =
      bivariateDecoratedObservableRootKPWeight F H Λ Φ β
        (Sum.inl (Sum.inr E)) + 1 := rfl

@[simp]
theorem bivariateDecoratedObservableRootRegularizedKPWeight_bridge
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (B : TwoObservableBridgeDecoration F H Λ) :
    bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β (Sum.inr B) =
      bivariateDecoratedObservableRootKPWeight F H Λ Φ β (Sum.inr B) + 1 := rfl

/-- Total tilted mass of all source polymers at a pair of source values. -/
def bivariateDecoratedObservableSourceTiltedMass
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) : ℝ :=
  ∑ q, if BivariateDecoratedObservableRootIsSource F H Λ q then
    ‖(bivariateDecoratedObservableRootModel F H Λ Φ β α θ).activity q‖ *
      Real.exp
        (bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β q)
    else 0

theorem bivariateDecoratedObservableSourceTiltedMass_nonneg
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) :
    0 ≤ bivariateDecoratedObservableSourceTiltedMass F H Λ Φ β α θ := by
  unfold bivariateDecoratedObservableSourceTiltedMass
  exact Finset.sum_nonneg fun q _ => by
    split_ifs
    · exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    · exact le_rfl

/-- A positive common source small enough that the complete finite collection
of decorated roots uses at most the fixed KP reserve. -/
def bivariateDecoratedObservableRootRegularization
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) : ℝ :=
  min 1 (twoRootSourceReserve /
    (bivariateDecoratedObservableSourceTiltedMass F H Λ Φ β 1 1 + 1))

theorem bivariateDecoratedObservableRootRegularization_pos
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    0 < bivariateDecoratedObservableRootRegularization F H Λ Φ β := by
  unfold bivariateDecoratedObservableRootRegularization
  apply lt_min (by norm_num)
  have hmass := bivariateDecoratedObservableSourceTiltedMass_nonneg
    F H Λ Φ β 1 1
  exact div_pos twoRootSourceReserve_pos (by linarith)

theorem bivariateDecoratedObservableRootRegularization_le_one
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    bivariateDecoratedObservableRootRegularization F H Λ Φ β ≤ 1 := by
  exact min_le_left _ _

theorem bivariateDecoratedObservableRootRegularization_mul_mass_le
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    bivariateDecoratedObservableRootRegularization F H Λ Φ β *
        bivariateDecoratedObservableSourceTiltedMass F H Λ Φ β 1 1 ≤
      twoRootSourceReserve := by
  let S := bivariateDecoratedObservableSourceTiltedMass F H Λ Φ β 1 1
  let ρ := bivariateDecoratedObservableRootRegularization F H Λ Φ β
  have hS : 0 ≤ S :=
    bivariateDecoratedObservableSourceTiltedMass_nonneg F H Λ Φ β 1 1
  have hden : 0 < S + 1 := by linarith
  have hρ : ρ ≤ twoRootSourceReserve / (S + 1) := by
    exact min_le_right _ _
  calc
    ρ * S ≤ (twoRootSourceReserve / (S + 1)) * S :=
      mul_le_mul_of_nonneg_right hρ hS
    _ ≤ twoRootSourceReserve := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hden).2
      nlinarith [twoRootSourceReserve_pos.le]

/-- Each source activity at the common regularization is bounded by the
regularization times its unit-source activity.  Bridge roots gain the
stronger factor `ρ²`. -/
theorem norm_bivariateDecoratedObservableRootModel_regularized_source_activity_le
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (q : ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ)
    (hq : BivariateDecoratedObservableRootIsSource F H Λ q) :
    ‖(bivariateDecoratedObservableRootModel F H Λ Φ β
        (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
        (bivariateDecoratedObservableRootRegularization F H Λ Φ β)).activity q‖ ≤
      bivariateDecoratedObservableRootRegularization F H Λ Φ β *
        ‖(bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).activity q‖ := by
  have hρ : 0 ≤ bivariateDecoratedObservableRootRegularization F H Λ Φ β :=
    (bivariateDecoratedObservableRootRegularization_pos F H Λ Φ β).le
  have hρone : bivariateDecoratedObservableRootRegularization F H Λ Φ β ≤ 1 :=
    bivariateDecoratedObservableRootRegularization_le_one F H Λ Φ β
  rcases q with (((γ | D) | E) | B)
  · simp [BivariateDecoratedObservableRootIsSource] at hq
  · simp only [bivariateDecoratedObservableRootModel_left_activity]
    simp only [one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ]
    exact le_rfl
  · simp only [bivariateDecoratedObservableRootModel_right_activity]
    simp only [one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ]
    exact le_rfl
  · simp only [bivariateDecoratedObservableRootModel_bridge_activity]
    simp only [one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ]
    apply mul_le_mul_of_nonneg_right _
      (norm_nonneg (markedSubsetWeight (F.mul H) Λ Φ β B.support))
    exact mul_le_of_le_one_right hρ hρone

/-- The complete tilted source mass at the regularized source is bounded by
the fixed reserve. -/
theorem bivariateDecoratedObservableSourceTiltedMass_regularized_le
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    bivariateDecoratedObservableSourceTiltedMass F H Λ Φ β
        (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
        (bivariateDecoratedObservableRootRegularization F H Λ Φ β) ≤
      twoRootSourceReserve := by
  let ρ := bivariateDecoratedObservableRootRegularization F H Λ Φ β
  calc
    _ ≤ ρ * bivariateDecoratedObservableSourceTiltedMass F H Λ Φ β 1 1 := by
      unfold bivariateDecoratedObservableSourceTiltedMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q _
      by_cases hq : BivariateDecoratedObservableRootIsSource F H Λ q
      · rw [if_pos hq, if_pos hq]
        calc
          _ ≤ (bivariateDecoratedObservableRootRegularization F H Λ Φ β *
                ‖(bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).activity q‖) *
                Real.exp
                  (bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β q) :=
            mul_le_mul_of_nonneg_right
              (norm_bivariateDecoratedObservableRootModel_regularized_source_activity_le
                F H Λ Φ β q hq) (Real.exp_pos _).le
          _ = _ := by ring
      · simp [hq]
    _ ≤ _ :=
      bivariateDecoratedObservableRootRegularization_mul_mass_le F H Λ Φ β

theorem bivariateDecoratedObservableRootRegularizedKPWeight_nonneg
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    ∀ q, 0 ≤
      bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β q := by
  rintro (((γ | D) | E) | B)
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num)).le
  · exact add_nonneg
      (bivariateDecoratedObservableRootKPWeight_nonneg F H Λ Φ β _) zero_le_one
  · exact add_nonneg
      (bivariateDecoratedObservableRootKPWeight_nonneg F H Λ Φ β _) zero_le_one
  · exact add_nonneg
      (bivariateDecoratedObservableRootKPWeight_nonneg F H Λ Φ β _) zero_le_one

/-- Switching on the common regularized source changes a KP incompatibility
sum by at most the total tilted mass of all source polymers. -/
theorem bivariateDecoratedObservableRoot_regularizedKPSum_le_zero_add_sourceMass
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (q : ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) :
    let ρ := bivariateDecoratedObservableRootRegularization F H Λ Φ β
    let Aρ := bivariateDecoratedObservableRootModel F H Λ Φ β ρ ρ
    let A₀ := bivariateDecoratedObservableRootModel F H Λ Φ β 0 0
    let aρ := bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β
    let a₀ := bivariateDecoratedObservableRootKPWeight F H Λ Φ β
    (∑ r, if Aρ.incompatible q r then
        ‖Aρ.activity r‖ * Real.exp (aρ r) else 0) ≤
      (∑ r, if A₀.incompatible q r then
        ‖A₀.activity r‖ * Real.exp (a₀ r) else 0) +
      bivariateDecoratedObservableSourceTiltedMass F H Λ Φ β ρ ρ := by
  classical
  dsimp only
  calc
    _ ≤ ∑ r, ((if (bivariateDecoratedObservableRootModel F H Λ Φ β 0 0).incompatible q r then
            ‖(bivariateDecoratedObservableRootModel F H Λ Φ β 0 0).activity r‖ *
              Real.exp
                (bivariateDecoratedObservableRootKPWeight F H Λ Φ β r)
          else 0) +
        (if BivariateDecoratedObservableRootIsSource F H Λ r then
            ‖(bivariateDecoratedObservableRootModel F H Λ Φ β
                (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
                (bivariateDecoratedObservableRootRegularization F H Λ Φ β)).activity r‖ *
              Real.exp
                (bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β r)
          else 0)) := by
      apply Finset.sum_le_sum
      rintro (((r | D) | E) | B) _
      · have hiff :=
          bivariateDecoratedObservableRootModel_incompatible_source_independent
            F H Λ Φ β
            (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
            (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
            0 0 q (Sum.inl (Sum.inl (Sum.inl r)))
        have hsource :
            ¬BivariateDecoratedObservableRootIsSource F H Λ
              (Sum.inl (Sum.inl (Sum.inl r))) := by
          simp [BivariateDecoratedObservableRootIsSource]
        have hterm :
            ‖(bivariateDecoratedObservableRootModel F H Λ Φ β
                (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
                (bivariateDecoratedObservableRootRegularization F H Λ Φ β)).activity
                  (Sum.inl (Sum.inl (Sum.inl r)))‖ *
                Real.exp (bivariateDecoratedObservableRootRegularizedKPWeight
                  F H Λ Φ β (Sum.inl (Sum.inl (Sum.inl r)))) =
              ‖(bivariateDecoratedObservableRootModel F H Λ Φ β 0 0).activity
                  (Sum.inl (Sum.inl (Sum.inl r)))‖ *
                Real.exp (bivariateDecoratedObservableRootKPWeight
                  F H Λ Φ β (Sum.inl (Sum.inl (Sum.inl r)))) := by
          simp [bivariateDecoratedObservableRootRegularizedKPWeight]
        by_cases hinc :
            (bivariateDecoratedObservableRootModel F H Λ Φ β
              (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
              (bivariateDecoratedObservableRootRegularization F H Λ Φ β)).incompatible
                q (Sum.inl (Sum.inl (Sum.inl r)))
        · have hinc0 := hiff.mp hinc
          rw [if_pos hinc, if_pos hinc0, if_neg hsource, hterm, add_zero]
        · have hinc0 :
              ¬(bivariateDecoratedObservableRootModel F H Λ Φ β 0 0).incompatible
                q (Sum.inl (Sum.inl (Sum.inl r))) := fun h => hinc (hiff.mpr h)
          rw [if_neg hinc, if_neg hinc0, if_neg hsource, add_zero]
      · have hiff :=
          bivariateDecoratedObservableRootModel_incompatible_source_independent
            F H Λ Φ β
            (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
            (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
            0 0 q (Sum.inl (Sum.inl (Sum.inr D)))
        have hsource : BivariateDecoratedObservableRootIsSource F H Λ
            (Sum.inl (Sum.inl (Sum.inr D))) := by trivial
        have hzeroTerm :
            ‖(bivariateDecoratedObservableRootModel F H Λ Φ β 0 0).activity
                (Sum.inl (Sum.inl (Sum.inr D)))‖ *
              Real.exp (bivariateDecoratedObservableRootKPWeight F H Λ Φ β
                (Sum.inl (Sum.inl (Sum.inr D)))) = 0 := by simp
        by_cases hinc :
            (bivariateDecoratedObservableRootModel F H Λ Φ β
              (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
              (bivariateDecoratedObservableRootRegularization F H Λ Φ β)).incompatible
                q (Sum.inl (Sum.inl (Sum.inr D)))
        · have hinc0 := hiff.mp hinc
          rw [if_pos hinc, if_pos hinc0, if_pos hsource, hzeroTerm, zero_add]
        · have hinc0 :
              ¬(bivariateDecoratedObservableRootModel F H Λ Φ β 0 0).incompatible
                q (Sum.inl (Sum.inl (Sum.inr D))) := fun h => hinc (hiff.mpr h)
          rw [if_neg hinc, if_neg hinc0, if_pos hsource, zero_add]
          exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      · have hiff :=
          bivariateDecoratedObservableRootModel_incompatible_source_independent
            F H Λ Φ β
            (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
            (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
            0 0 q (Sum.inl (Sum.inr E))
        have hsource : BivariateDecoratedObservableRootIsSource F H Λ
            (Sum.inl (Sum.inr E)) := by trivial
        have hzeroTerm :
            ‖(bivariateDecoratedObservableRootModel F H Λ Φ β 0 0).activity
                (Sum.inl (Sum.inr E))‖ *
              Real.exp (bivariateDecoratedObservableRootKPWeight F H Λ Φ β
                (Sum.inl (Sum.inr E))) = 0 := by simp
        by_cases hinc :
            (bivariateDecoratedObservableRootModel F H Λ Φ β
              (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
              (bivariateDecoratedObservableRootRegularization F H Λ Φ β)).incompatible
                q (Sum.inl (Sum.inr E))
        · have hinc0 := hiff.mp hinc
          rw [if_pos hinc, if_pos hinc0, if_pos hsource, hzeroTerm, zero_add]
        · have hinc0 :
              ¬(bivariateDecoratedObservableRootModel F H Λ Φ β 0 0).incompatible
                q (Sum.inl (Sum.inr E)) := fun h => hinc (hiff.mpr h)
          rw [if_neg hinc, if_neg hinc0, if_pos hsource, zero_add]
          exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      · have hiff :=
          bivariateDecoratedObservableRootModel_incompatible_source_independent
            F H Λ Φ β
            (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
            (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
            0 0 q (Sum.inr B)
        have hsource : BivariateDecoratedObservableRootIsSource F H Λ
            (Sum.inr B) := by trivial
        have hzeroTerm :
            ‖(bivariateDecoratedObservableRootModel F H Λ Φ β 0 0).activity
                (Sum.inr B)‖ *
              Real.exp (bivariateDecoratedObservableRootKPWeight F H Λ Φ β
                (Sum.inr B)) = 0 := by simp
        by_cases hinc :
            (bivariateDecoratedObservableRootModel F H Λ Φ β
              (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
              (bivariateDecoratedObservableRootRegularization F H Λ Φ β)).incompatible
                q (Sum.inr B)
        · have hinc0 := hiff.mp hinc
          rw [if_pos hinc, if_pos hinc0, if_pos hsource, hzeroTerm, zero_add]
        · have hinc0 :
              ¬(bivariateDecoratedObservableRootModel F H Λ Φ β 0 0).incompatible
                q (Sum.inr B) := fun h => hinc (hiff.mpr h)
          rw [if_neg hinc, if_neg hinc0, if_pos hsource, zero_add]
          exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      rw [Finset.sum_add_distrib]
      rfl

/-- The exact bivariate decorated gas can be switched on at an explicit
positive common source while retaining a genuine KP certificate.  The proof
uses the quantitative quarter-budget reserve of the plaquette gas and the
complete finite tilted mass of all decorated source polymers. -/
theorem bivariateDecoratedObservableRootModel_koteckyPreiss_regularized
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let ρ := bivariateDecoratedObservableRootRegularization F H Λ Φ β
    (bivariateDecoratedObservableRootModel F H Λ Φ β ρ ρ).KoteckyPreissCertificate Finset.univ
        (bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β) := by
  classical
  dsimp only
  let ρ := bivariateDecoratedObservableRootRegularization F H Λ Φ β
  let Aρ := bivariateDecoratedObservableRootModel F H Λ Φ β ρ ρ
  let A₀ := bivariateDecoratedObservableRootModel F H Λ Φ β 0 0
  let aρ := bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β
  let a₀ := bivariateDecoratedObservableRootKPWeight F H Λ Φ β
  have hzero : A₀.KoteckyPreissCertificate Finset.univ a₀ := by
    exact bivariateDecoratedObservableRootModel_koteckyPreiss_zero F H Λ Φ hβ
  have hsource :
      bivariateDecoratedObservableSourceTiltedMass F H Λ Φ β ρ ρ ≤
        twoRootSourceReserve := by
    exact bivariateDecoratedObservableSourceTiltedMass_regularized_le F H Λ Φ β
  have hsmall : perturbationMajorant Φ β <
      dobrushinThreshold (16 * d) (2 ^ (16 * d)) :=
    perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
      (16 * d) (2 ^ (16 * d)) hβ
  refine ⟨?_, ?_⟩
  · exact bivariateDecoratedObservableRootRegularizedKPWeight_nonneg
      F H Λ Φ β
  · intro q _hq
    rw [Finset.sum_filter]
    have hcompare :
        (∑ r, if Aρ.incompatible q r then
            ‖Aρ.activity r‖ * Real.exp (aρ r) else 0) ≤
          (∑ r, if A₀.incompatible q r then
            ‖A₀.activity r‖ * Real.exp (a₀ r) else 0) +
          bivariateDecoratedObservableSourceTiltedMass F H Λ Φ β ρ ρ := by
      simpa [Aρ, A₀, aρ, a₀, ρ] using
        bivariateDecoratedObservableRoot_regularizedKPSum_le_zero_add_sourceMass
          F H Λ Φ β q
    rcases q with (((γ | D) | E) | B)
    · have hbulk := plaquettePolymerModel_kp_incompatible_sum_le_quarter
          Λ Φ β (cubicPlaquetteAnimalCertificate Λ) hsmall γ
      rw [Finset.sum_filter] at hbulk
      have hzeroBulk :
          (∑ r, if A₀.incompatible (Sum.inl (Sum.inl (Sum.inl γ))) r then
              ‖A₀.activity r‖ * Real.exp (a₀ r) else 0) ≤
            (γ.1.card : ℝ) * (Real.log 2 / 4) := by
        dsimp only [A₀, a₀]
        simpa [bivariateDecoratedObservableRootModel,
          Polymer.FinitePolymerModel.augmentBivariateExclusiveRoots,
          Polymer.FinitePolymerModel.augmentTwoColorExclusiveRoots,
          Polymer.FinitePolymerModel.augmentExclusiveRoots,
          Fintype.sum_sum_type] using hbulk
      have hcard : (1 : ℝ) ≤ (γ.1.card : ℝ) := by
        exact_mod_cast γ.2.1.card_pos
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
      calc
        _ ≤ (∑ r, if A₀.incompatible
              (Sum.inl (Sum.inl (Sum.inl γ))) r then
              ‖A₀.activity r‖ * Real.exp (a₀ r) else 0) +
            bivariateDecoratedObservableSourceTiltedMass F H Λ Φ β ρ ρ :=
          hcompare
        _ ≤ (γ.1.card : ℝ) * (Real.log 2 / 4) +
            twoRootSourceReserve := add_le_add hzeroBulk hsource
        _ ≤ (γ.1.card : ℝ) * Real.log 2 := by
          unfold twoRootSourceReserve
          nlinarith
        _ = aρ (Sum.inl (Sum.inl (Sum.inl γ))) := by
          simp [aρ, plaquetteKPWeight]
    · have hz := hzero.2 (Sum.inl (Sum.inl (Sum.inr D)))
          (Finset.mem_univ _)
      rw [Finset.sum_filter] at hz
      calc
        _ ≤ (∑ r, if A₀.incompatible
              (Sum.inl (Sum.inl (Sum.inr D))) r then
              ‖A₀.activity r‖ * Real.exp (a₀ r) else 0) +
            bivariateDecoratedObservableSourceTiltedMass F H Λ Φ β ρ ρ :=
          hcompare
        _ ≤ a₀ (Sum.inl (Sum.inl (Sum.inr D))) +
            twoRootSourceReserve := add_le_add hz hsource
        _ ≤ a₀ (Sum.inl (Sum.inl (Sum.inr D))) + 1 :=
          add_le_add_right twoRootSourceReserve_le_one
            (a₀ (Sum.inl (Sum.inl (Sum.inr D))))
        _ = aρ (Sum.inl (Sum.inl (Sum.inr D))) := by
          exact (bivariateDecoratedObservableRootRegularizedKPWeight_left
            F H Λ Φ β D).symm
    · have hz := hzero.2 (Sum.inl (Sum.inr E)) (Finset.mem_univ _)
      rw [Finset.sum_filter] at hz
      calc
        _ ≤ (∑ r, if A₀.incompatible (Sum.inl (Sum.inr E)) r then
              ‖A₀.activity r‖ * Real.exp (a₀ r) else 0) +
            bivariateDecoratedObservableSourceTiltedMass F H Λ Φ β ρ ρ :=
          hcompare
        _ ≤ a₀ (Sum.inl (Sum.inr E)) + twoRootSourceReserve :=
          add_le_add hz hsource
        _ ≤ a₀ (Sum.inl (Sum.inr E)) + 1 :=
          add_le_add_right twoRootSourceReserve_le_one
            (a₀ (Sum.inl (Sum.inr E)))
        _ = aρ (Sum.inl (Sum.inr E)) := by
          exact (bivariateDecoratedObservableRootRegularizedKPWeight_right
            F H Λ Φ β E).symm
    · have hz := hzero.2 (Sum.inr B) (Finset.mem_univ _)
      rw [Finset.sum_filter] at hz
      calc
        _ ≤ (∑ r, if A₀.incompatible (Sum.inr B) r then
              ‖A₀.activity r‖ * Real.exp (a₀ r) else 0) +
            bivariateDecoratedObservableSourceTiltedMass F H Λ Φ β ρ ρ :=
          hcompare
        _ ≤ a₀ (Sum.inr B) + twoRootSourceReserve :=
          add_le_add hz hsource
        _ ≤ a₀ (Sum.inr B) + 1 :=
          add_le_add_right twoRootSourceReserve_le_one (a₀ (Sum.inr B))
        _ = aρ (Sum.inr B) := by
          exact (bivariateDecoratedObservableRootRegularizedKPWeight_bridge
            F H Λ Φ β B).symm

/-- The bidegree-scaled unit-source gas inherits the regularized KP
certificate. -/
theorem bivariateDecoratedObservableRootModel_scaled_koteckyPreiss_regularized
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let ρ := bivariateDecoratedObservableRootRegularization F H Λ Φ β
    ((bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).scaleByBigradedSource
        (bivariateDecoratedObservableRootGrading F H Λ)
        (bivariateObservableSourceValues ρ ρ)).KoteckyPreissCertificate
          Finset.univ
          (bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β) := by
  classical
  dsimp only
  let ρ := bivariateDecoratedObservableRootRegularization F H Λ Φ β
  let As := (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).scaleByBigradedSource
      (bivariateDecoratedObservableRootGrading F H Λ)
      (bivariateObservableSourceValues ρ ρ)
  let Aρ := bivariateDecoratedObservableRootModel F H Λ Φ β ρ ρ
  let a := bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β
  have hregular : Aρ.KoteckyPreissCertificate Finset.univ a := by
    exact bivariateDecoratedObservableRootModel_koteckyPreiss_regularized
      F H Λ Φ hβ
  refine ⟨hregular.1, ?_⟩
  intro q _hq
  have hq := hregular.2 q (Finset.mem_univ q)
  change (∑ r ∈ Finset.univ.filter (As.incompatible q),
      ‖As.activity r‖ * Real.exp (a r)) ≤ a q
  simpa only [As, Aρ,
    bivariateDecoratedObservableRootModel_scaled_activity] using hq

/-- The complete regularized decorated bivariate gas has summable positive-
degree Mayer majorant by the explicit KP certificate. -/
theorem bivariateDecoratedObservableRootModel_regularized_summable_normMayerDegreeSum_succ
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let ρ := bivariateDecoratedObservableRootRegularization F H Λ Φ β
    Summable (fun n : ℕ ↦
      ((bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).scaleByBigradedSource
          (bivariateDecoratedObservableRootGrading F H Λ)
          (bivariateObservableSourceValues ρ ρ)).normMayerDegreeSum
            (n + 1)) := by
  dsimp only
  let A := (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).scaleByBigradedSource
    (bivariateDecoratedObservableRootGrading F H Λ)
      (bivariateObservableSourceValues
        (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
        (bivariateDecoratedObservableRootRegularization F H Λ Φ β))
  change Summable (fun n : ℕ => A.normMayerDegreeSum (n + 1))
  exact A.summable_normMayerDegreeSum_succ_of_koteckyPreiss_certified
    (bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β)
    (bivariateDecoratedObservableRootModel_scaled_koteckyPreiss_regularized
      F H Λ Φ hβ)

/-- Genuine pinned spanning-tree summability at every polymer of the complete
regularized decorated gas. -/
theorem bivariateDecoratedObservableRootModel_regularized_summable_pinnedMayerTreeDegreeSum_succ
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (root : ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) :
    let ρ := bivariateDecoratedObservableRootRegularization F H Λ Φ β
    Summable (fun n : ℕ ↦
      ((bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).scaleByBigradedSource
          (bivariateDecoratedObservableRootGrading F H Λ)
          (bivariateObservableSourceValues ρ ρ)).pinnedMayerTreeDegreeSum
            root (n + 1)) := by
  dsimp only
  exact Polymer.FinitePolymerModel.summable_pinnedMayerTreeDegreeSum_succ_of_koteckyPreiss_certified
    ((bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).scaleByBigradedSource
        (bivariateDecoratedObservableRootGrading F H Λ)
        (bivariateObservableSourceValues
          (bivariateDecoratedObservableRootRegularization F H Λ Φ β)
          (bivariateDecoratedObservableRootRegularization F H Λ Φ β)))
    (bivariateDecoratedObservableRootRegularizedKPWeight F H Λ Φ β)
    (bivariateDecoratedObservableRootModel_scaled_koteckyPreiss_regularized
      F H Λ Φ hβ) root

/-- The bidegree `(1,1)` connected coefficient of the exact decorated
observable gas. -/
def bivariateDecoratedObservableMixedMayerDegreeSum
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (n : ℕ) : ℂ :=
  (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).bigradedMixedMayerDegreeSum
      (bivariateDecoratedObservableRootGrading F H Λ) n

/-- Genuine absolute summability of the support-graded mixed connected Mayer
sector, transferred from the nonzero-source KP gas. -/
theorem summable_norm_bivariateDecoratedObservableMixedMayerDegreeSum_succ
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable (fun n : ℕ ↦
      ‖bivariateDecoratedObservableMixedMayerDegreeSum F H Λ Φ β (n + 1)‖) := by
  let M := bivariateDecoratedObservableRootModel F H Λ Φ β 1 1
  let grading := bivariateDecoratedObservableRootGrading F H Λ
  let ρ := bivariateDecoratedObservableRootRegularization F H Λ Φ β
  let alpha := bivariateObservableSourceValues (ρ : ℂ) (ρ : ℂ)
  have hρ : ρ ≠ 0 := ne_of_gt
    (bivariateDecoratedObservableRootRegularization_pos F H Λ Φ β)
  have halpha0 : alpha 0 ≠ 0 := by
    simpa [alpha, bivariateObservableSourceValues] using hρ
  have halpha1 : alpha 1 ≠ 0 := by
    simpa [alpha, bivariateObservableSourceValues] using hρ
  have hscaled : Summable (fun n : ℕ ↦
      (M.scaleByBigradedSource grading alpha).normMayerDegreeSum (n + 1)) := by
    exact bivariateDecoratedObservableRootModel_regularized_summable_normMayerDegreeSum_succ
      F H Λ Φ hβ
  simpa [bivariateDecoratedObservableMixedMayerDegreeSum, M, grading, alpha] using
    M.summable_norm_bigradedMixedMayerDegreeSum_succ_of_scaled
      grading alpha halpha0 halpha1 hscaled

omit [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- The KP weight of a complete decoration is bounded by the ordinary
observable-root tilted mass plus the KP weights of the polymers absorbed into
the decoration. -/
theorem decoratedObservableRootKPWeight_root_le_base_add_decoration
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (D : ObservableRootDecoration F Λ) :
    decoratedObservableRootKPWeight F Λ Φ β (Sum.inr D) ≤
      oneObservableRootKPWeight F Λ Φ β (Sum.inr ()) +
        ∑ δ ∈ D.1, plaquetteKPWeight δ := by
  classical
  let M := plaquettePolymerModel Λ Φ β
  let w : PlaquettePolymer Λ → ℝ := fun γ =>
    ‖M.activity γ‖ * Real.exp (plaquetteKPWeight γ)
  have hKP : M.KoteckyPreissCertificate Finset.univ plaquetteKPWeight := by
    dsimp [M]
    apply plaquettePolymerModel_koteckyPreiss Λ Φ β
      (cubicPlaquetteAnimalCertificate Λ)
    exact perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
      (16 * d) (2 ^ (16 * d)) hβ
  have hpoint (gamma : PlaquettePolymer Λ) :
      (if observableRootDecorationTouches F Λ D gamma then w gamma else 0) ≤
        (if observableRootTouches F Λ gamma then w gamma else 0) +
          ∑ delta ∈ D.1,
            if plaquettePolymerIncompatible Λ delta gamma then w gamma else 0 := by
    by_cases hroot : observableRootTouches F Λ gamma
    · have htouch : observableRootDecorationTouches F Λ D gamma :=
        Or.inl hroot
      rw [if_pos htouch, if_pos hroot]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
    · by_cases hdecoration :
          ∃ delta ∈ D.1, plaquettePolymerIncompatible Λ delta gamma
      · rcases hdecoration with ⟨delta, hdelta, hinc⟩
        have htouch : observableRootDecorationTouches F Λ D gamma :=
          Or.inr ⟨delta, hdelta, hinc⟩
        rw [if_pos htouch, if_neg hroot, zero_add]
        have hnonneg : ∀ eta ∈ D.1,
            0 ≤ if plaquettePolymerIncompatible Λ eta gamma then
              w gamma else 0 := by
          intro eta _
          split_ifs
          · positivity
          · exact le_rfl
        calc
          w gamma = if plaquettePolymerIncompatible Λ delta gamma then
              w gamma else 0 := by rw [if_pos hinc]
          _ ≤ ∑ eta ∈ D.1,
              if plaquettePolymerIncompatible Λ eta gamma then
                w gamma else 0 :=
            Finset.single_le_sum hnonneg hdelta
      · have hnot : ¬observableRootDecorationTouches F Λ D gamma := by
          rintro (h | h)
          · exact hroot h
          · exact hdecoration h
        rw [if_neg hnot, if_neg hroot, zero_add]
        exact Finset.sum_nonneg fun _ _ => by
          split_ifs
          · positivity
          · exact le_rfl
  have hincompatible (delta : PlaquettePolymer Λ) :
      (∑ gamma : PlaquettePolymer Λ,
          if plaquettePolymerIncompatible Λ delta gamma then
            w gamma else 0) ≤ plaquetteKPWeight delta := by
    have h := hKP.2 delta (Finset.mem_univ delta)
    rw [Finset.sum_filter] at h
    simpa [M, w] using h
  change (∑ gamma : PlaquettePolymer Λ,
      if observableRootDecorationTouches F Λ D gamma then
        w gamma else 0) ≤
    (∑ gamma : PlaquettePolymer Λ,
      if observableRootTouches F Λ gamma then w gamma else 0) +
      ∑ delta ∈ D.1, plaquetteKPWeight delta
  calc
    (∑ gamma : PlaquettePolymer Λ,
        if observableRootDecorationTouches F Λ D gamma then
          w gamma else 0) ≤
      ∑ gamma : PlaquettePolymer Λ,
        ((if observableRootTouches F Λ gamma then w gamma else 0) +
          ∑ delta ∈ D.1,
            if plaquettePolymerIncompatible Λ delta gamma then
              w gamma else 0) :=
        Finset.sum_le_sum fun gamma _ => hpoint gamma
    _ = (∑ gamma : PlaquettePolymer Λ,
          if observableRootTouches F Λ gamma then w gamma else 0) +
        ∑ delta ∈ D.1,
          ∑ gamma : PlaquettePolymer Λ,
            if plaquettePolymerIncompatible Λ delta gamma then
              w gamma else 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ (∑ gamma : PlaquettePolymer Λ,
          if observableRootTouches F Λ gamma then w gamma else 0) +
        ∑ delta ∈ D.1, plaquetteKPWeight delta := by
      gcongr with delta hdelta
      exact hincompatible delta

/-- Fully explicit support version of the decorated-root KP budget.  The
additional cost is exactly the sum of the ordinary bulk KP weights already
absorbed into the decoration. -/
theorem decoratedObservableRootKPWeight_root_le_support_add_decoration
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (D : ObservableRootDecoration F Λ) :
    decoratedObservableRootKPWeight F Λ Φ β (Sum.inr D) ≤
      (4 * d * F.support.card : ℕ) * Real.log 2 +
        ∑ δ ∈ D.1, plaquetteKPWeight δ := by
  let s : ℝ := ∑ δ ∈ D.1, plaquetteKPWeight δ
  calc
    _ ≤ oneObservableRootKPWeight F Λ Φ β (Sum.inr ()) +
          s :=
      decoratedObservableRootKPWeight_root_le_base_add_decoration
        F Λ Φ hβ D
    _ ≤ (4 * d * F.support.card : ℕ) * Real.log 2 +
          s :=
      add_le_add_left
        (oneObservableRootKPWeight_root_le_support F Λ Φ hβ) s

/-- Uniform animal bound for all connected polymers touching the observable,
with the extra `2^|γ|` tilt required by the KP root weight. -/
theorem sum_observableRoot_tiltedAnimalWeight_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ∑ γ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
        (observableRootTouches F Λ),
        (2 * perturbationMajorant Φ β) ^ γ.1.card ≤
      ((observableRootPlaquettes Λ F).card : ℝ) *
        ((2 * perturbationMajorant Φ β) /
          (1 - (2 ^ (16 * d) : ℝ) *
            (2 * perturbationMajorant Φ β))) := by
  classical
  let q : ℝ := 2 * perturbationMajorant Φ β
  let R := observableRootPlaquettes Λ F
  have hq : 0 ≤ q :=
    mul_nonneg (by norm_num) (perturbationMajorant_nonneg Φ β)
  have hsmall :
      ((cubicPlaquetteAnimalCertificate Λ).animalConstant : ℝ) * q < 1 := by
    simpa [q] using
      animalConstant_mul_two_mul_perturbationMajorant_lt_one Φ hβ
  have hpoint (gamma : PlaquettePolymer Λ) :
      (if observableRootTouches F Λ gamma then q ^ gamma.1.card else 0) ≤
        ∑ p ∈ R, if p ∈ gamma.1 then q ^ gamma.1.card else 0 := by
    by_cases htouch : observableRootTouches F Λ gamma
    · obtain ⟨p, hpγ, hpR⟩ := (observableRootTouches_iff F Λ gamma).mp htouch
      rw [if_pos htouch]
      have hnonneg : ∀ r ∈ R,
          0 ≤ if r ∈ gamma.1 then q ^ gamma.1.card else 0 := by
        intro r _
        split_ifs
        · exact pow_nonneg hq _
        · exact le_rfl
      calc
        q ^ gamma.1.card =
            if p ∈ gamma.1 then q ^ gamma.1.card else 0 := by simp [hpγ]
        _ ≤ ∑ r ∈ R, if r ∈ gamma.1 then q ^ gamma.1.card else 0 :=
          Finset.single_le_sum hnonneg hpR
    · rw [if_neg htouch]
      exact Finset.sum_nonneg fun p _ => by
        split_ifs
        · exact pow_nonneg hq _
        · exact le_rfl
  have hroot (p : ActivePlaquette Λ) :
      (∑ gamma : PlaquettePolymer Λ,
          if p ∈ gamma.1 then q ^ gamma.1.card else 0) ≤
        q / (1 -
          ((cubicPlaquetteAnimalCertificate Λ).animalConstant : ℝ) * q) := by
    rw [← Finset.sum_filter]
    exact sum_rootedPlaquettePolymerWeights_le Λ
      (cubicPlaquetteAnimalCertificate Λ) p hq hsmall
  suffices hbound :
      (∑ gamma ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
          (observableRootTouches F Λ), q ^ gamma.1.card) ≤
        (R.card : ℝ) *
          (q / (1 -
            ((cubicPlaquetteAnimalCertificate Λ).animalConstant : ℝ) * q)) by
    simpa [q, R] using hbound
  rw [Finset.sum_filter]
  calc
    (∑ gamma : PlaquettePolymer Λ,
        if observableRootTouches F Λ gamma then q ^ gamma.1.card else 0) ≤
      ∑ gamma : PlaquettePolymer Λ,
        ∑ p ∈ R, if p ∈ gamma.1 then q ^ gamma.1.card else 0 :=
      Finset.sum_le_sum fun gamma _ => hpoint gamma
    _ = ∑ p ∈ R, ∑ gamma : PlaquettePolymer Λ,
        if p ∈ gamma.1 then q ^ gamma.1.card else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _p ∈ R,
        q / (1 -
          ((cubicPlaquetteAnimalCertificate Λ).animalConstant : ℝ) * q) := by
      exact Finset.sum_le_sum fun p _ => hroot p
    _ = (R.card : ℝ) *
        (q / (1 -
          ((cubicPlaquetteAnimalCertificate Λ).animalConstant : ℝ) * q)) := by
      simp

/-- A marked decoration together with its residual KP budget is dominated by
the product of the twice-tilted animal weights of its connected members.
The only remaining prefactor depends on the recorded observable support. -/
theorem norm_markedSubsetWeight_mul_exp_decoratedRootKPWeight_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (D : ObservableRootDecoration F Λ) :
    ‖markedSubsetWeight F Λ Φ β D.support‖ *
        Real.exp
          (decoratedObservableRootKPWeight F Λ Φ β (Sum.inr D)) ≤
      ‖F.toBoundedContinuousMap‖ *
        Real.exp (((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2) *
        ∏ δ ∈ D.1,
          (2 * perturbationMajorant Φ β) ^ δ.1.card := by
  classical
  let q : ℝ := perturbationMajorant Φ β
  let b : ℝ := ((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2
  let s : ℝ := ∑ δ ∈ D.1, plaquetteKPWeight δ
  have hq : 0 ≤ q := perturbationMajorant_nonneg Φ β
  have hmarked : ‖markedSubsetWeight F Λ Φ β D.support‖ ≤
      ‖F.toBoundedContinuousMap‖ * q ^ D.support.card := by
    simpa [q] using norm_markedSubsetWeight_le F Λ Φ β D.support
  have hroot : decoratedObservableRootKPWeight F Λ Φ β (Sum.inr D) ≤
      b + s := by
    simpa [b, s] using
      decoratedObservableRootKPWeight_root_le_support_add_decoration
        F Λ Φ hβ D
  have hqpower : q ^ D.support.card =
      ∏ δ ∈ D.1, q ^ δ.1.card := by
    rw [D.card_support]
    exact (Finset.prod_pow_eq_pow_sum D.1 (fun δ => δ.1.card) q).symm
  have hexps : Real.exp s = ∏ δ ∈ D.1, (2 : ℝ) ^ δ.1.card := by
    dsimp [s]
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro δ _
    rw [plaquetteKPWeight, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hprod :
      (∏ δ ∈ D.1, (2 : ℝ) ^ δ.1.card) *
          ∏ δ ∈ D.1, q ^ δ.1.card =
        ∏ δ ∈ D.1, (2 * q) ^ δ.1.card := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [mul_pow]
  calc
    ‖markedSubsetWeight F Λ Φ β D.support‖ *
          Real.exp
            (decoratedObservableRootKPWeight F Λ Φ β (Sum.inr D)) ≤
        (‖F.toBoundedContinuousMap‖ * q ^ D.support.card) *
          Real.exp (b + s) := by
      exact mul_le_mul hmarked (Real.exp_le_exp.mpr hroot)
        (Real.exp_pos _).le
        (mul_nonneg (norm_nonneg _) (pow_nonneg hq _))
    _ = ‖F.toBoundedContinuousMap‖ * Real.exp b *
        ∏ δ ∈ D.1, (2 * q) ^ δ.1.card := by
      rw [hqpower, Real.exp_add, hexps]
      calc
        (‖F.toBoundedContinuousMap‖ * ∏ δ ∈ D.1, q ^ δ.1.card) *
            (Real.exp b * ∏ δ ∈ D.1, (2 : ℝ) ^ δ.1.card) =
          ‖F.toBoundedContinuousMap‖ * Real.exp b *
            ((∏ δ ∈ D.1, (2 : ℝ) ^ δ.1.card) *
              ∏ δ ∈ D.1, q ^ δ.1.card) := by ring
        _ = ‖F.toBoundedContinuousMap‖ * Real.exp b *
            ∏ δ ∈ D.1, (2 * q) ^ δ.1.card := by
          rw [hprod]
    _ = ‖F.toBoundedContinuousMap‖ *
        Real.exp (((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2) *
        ∏ δ ∈ D.1,
          (2 * perturbationMajorant Φ β) ^ δ.1.card := by
      rfl

/-- Complete compatible root decorations are dominated by the ordinary
finite-set exponential of all connected polymers touching the observable.
This removes any dependence on the cardinality of the decoration type. -/
theorem sum_observableRootDecoration_product_le_exp
    (F : LocalObservable d G) (Λ : FiniteSpecification d G) {q : ℝ}
    (hq : 0 ≤ q) :
    ∑ D : ObservableRootDecoration F Λ,
        ∏ δ ∈ D.1, q ^ δ.1.card ≤
      Real.exp
        (∑ γ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
          (observableRootTouches F Λ), q ^ γ.1.card) := by
  classical
  let S : Finset (PlaquettePolymer Λ) :=
    Finset.univ.filter (observableRootTouches F Λ)
  let image : Finset (Finset (PlaquettePolymer Λ)) :=
    (Finset.univ : Finset (ObservableRootDecoration F Λ)).image
      fun D => D.1
  have himage :
      (∑ D : ObservableRootDecoration F Λ,
          ∏ δ ∈ D.1, q ^ δ.1.card) =
        ∑ Γ ∈ image, ∏ δ ∈ Γ, q ^ δ.1.card := by
    dsimp [image]
    rw [Finset.sum_image]
    intro D _ E _ hDE
    exact Subtype.ext hDE
  have hsubset : image ⊆ S.powerset := by
    intro Γ hΓ
    rcases Finset.mem_image.mp hΓ with ⟨D, _hD, rfl⟩
    rw [Finset.mem_powerset]
    intro δ hδ
    simpa [S] using D.2.2 δ hδ
  rw [himage]
  calc
    (∑ Γ ∈ image, ∏ δ ∈ Γ, q ^ δ.1.card) ≤
        ∑ Γ ∈ S.powerset, ∏ δ ∈ Γ, q ^ δ.1.card :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun Γ _ _ => Finset.prod_nonneg fun δ _ => pow_nonneg hq _)
    _ = ∏ δ ∈ S, (1 + q ^ δ.1.card) := by
      rw [Finset.prod_one_add]
    _ ≤ Real.exp (∑ δ ∈ S, q ^ δ.1.card) :=
      Real.prod_one_add_le_exp_sum S fun δ => pow_nonneg hq _

/-- The sum of every exact decorated-root activity times its certified
residual tree budget has a volume-independent bound depending only on the
observable support and the explicit scalar animal majorant. -/
theorem sum_norm_markedSubsetWeight_mul_exp_decoratedRootKPWeight_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ∑ D : ObservableRootDecoration F Λ,
        ‖markedSubsetWeight F Λ Φ β D.support‖ *
          Real.exp
            (decoratedObservableRootKPWeight F Λ Φ β (Sum.inr D)) ≤
      ‖F.toBoundedContinuousMap‖ *
        Real.exp (((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2) *
        Real.exp
          (((observableRootPlaquettes Λ F).card : ℝ) *
            ((2 * perturbationMajorant Φ β) /
              (1 - (2 ^ (16 * d) : ℝ) *
                (2 * perturbationMajorant Φ β)))) := by
  classical
  let q : ℝ := 2 * perturbationMajorant Φ β
  let c : ℝ := ‖F.toBoundedContinuousMap‖ *
    Real.exp (((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2)
  let A : ℝ :=
    ∑ γ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
      (observableRootTouches F Λ), q ^ γ.1.card
  let B : ℝ := ((observableRootPlaquettes Λ F).card : ℝ) *
    (q / (1 - (2 ^ (16 * d) : ℝ) * q))
  have hq : 0 ≤ q :=
    mul_nonneg (by norm_num) (perturbationMajorant_nonneg Φ β)
  have hc : 0 ≤ c :=
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hdecorations :
      (∑ D : ObservableRootDecoration F Λ,
          ∏ δ ∈ D.1, q ^ δ.1.card) ≤ Real.exp A := by
    simpa [A] using sum_observableRootDecoration_product_le_exp F Λ hq
  have hanimals : A ≤ B := by
    simpa [A, B, q] using
      sum_observableRoot_tiltedAnimalWeight_le F Λ Φ hβ
  change (∑ D : ObservableRootDecoration F Λ,
      ‖markedSubsetWeight F Λ Φ β D.support‖ *
        Real.exp
          (decoratedObservableRootKPWeight F Λ Φ β (Sum.inr D))) ≤
    c * Real.exp B
  calc
    _ ≤ ∑ D : ObservableRootDecoration F Λ,
        c * ∏ δ ∈ D.1, q ^ δ.1.card := by
      exact Finset.sum_le_sum fun D _ => by
        simpa [c, q] using
          norm_markedSubsetWeight_mul_exp_decoratedRootKPWeight_le
            F Λ Φ hβ D
    _ = c * ∑ D : ObservableRootDecoration F Λ,
        ∏ δ ∈ D.1, q ^ δ.1.card := by
      rw [Finset.mul_sum]
    _ ≤ c * Real.exp A :=
      mul_le_mul_of_nonneg_left hdecorations hc
    _ ≤ c * Real.exp B :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hanimals) hc

/-- Every exact marked root decoration has a certified residual Mayer-tree
budget on the explicit strong-coupling disk. -/
theorem decoratedObservableRootModel_tsum_residualSymmetricPinnedTreeDegreeSum_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (D : ObservableRootDecoration F Λ) :
    ∑' n : ℕ,
        (decoratedObservableRootModel F Λ Φ β 0).residualSymmetricPinnedTreeDegreeSum
          (Sum.inr D) n ≤
      Real.exp (decoratedObservableRootKPWeight F Λ Φ β (Sum.inr D)) := by
  exact (decoratedObservableRootModel
    F Λ Φ β 0).tsum_residualSymmetricPinnedTreeDegreeSum_le_of_koteckyPreiss_certified
      (decoratedObservableRootKPWeight F Λ Φ β)
      (decoratedObservableRootModel_koteckyPreiss_zero F Λ Φ hβ) (Sum.inr D)

/-- Absolute summability of the residual rooted-tree orbit at each exact
decoration. -/
theorem decoratedObservableRootModel_summable_residualSymmetricPinnedTreeDegreeSum
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (D : ObservableRootDecoration F Λ) :
    Summable
      ((decoratedObservableRootModel F Λ Φ β 0).residualSymmetricPinnedTreeDegreeSum
        (Sum.inr D)) := by
  exact (decoratedObservableRootModel
    F Λ Φ β 0).summable_residualSymmetricPinnedTreeDegreeSum_of_koteckyPreiss
    (decoratedObservableRootKPWeight F Λ Φ β)
    (decoratedObservableRootModel F Λ Φ β 0).rootedTreeOrbitBound
    (decoratedObservableRootModel_koteckyPreiss_zero F Λ Φ hβ)
    (Sum.inr D)

/-- Degree-`n` majorant obtained by distinguishing the unique complete
observable decoration and deleting its source occurrence. -/
def decoratedObservableRootLinearTreeMajorantDegreeSum
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (n : ℕ) : ℝ :=
  ∑ D : ObservableRootDecoration F Λ,
    ‖markedSubsetWeight F Λ Φ β D.support‖ *
      (decoratedObservableRootModel F Λ Φ β 0).residualSymmetricPinnedTreeDegreeSum
        (Sum.inr D) n

/-- The complete one-root tree majorant is summable on the explicit lattice
disk, uniformly over all complete decoration values. -/
theorem summable_decoratedObservableRootLinearTreeMajorantDegreeSum
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable (decoratedObservableRootLinearTreeMajorantDegreeSum F Λ Φ β) := by
  unfold decoratedObservableRootLinearTreeMajorantDegreeSum
  apply summable_sum
  intro D _
  exact (decoratedObservableRootModel_summable_residualSymmetricPinnedTreeDegreeSum
    F Λ Φ hβ D).mul_left
      ‖markedSubsetWeight F Λ Φ β D.support‖

/-- The total one-root tree majorant is bounded by the explicit uniform sum
of decorated activities times their KP budgets. -/
theorem tsum_decoratedObservableRootLinearTreeMajorantDegreeSum_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ∑' n : ℕ,
        decoratedObservableRootLinearTreeMajorantDegreeSum F Λ Φ β n ≤
      ‖F.toBoundedContinuousMap‖ *
        Real.exp (((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2) *
        Real.exp
          (((observableRootPlaquettes Λ F).card : ℝ) *
            ((2 * perturbationMajorant Φ β) /
              (1 - (2 ^ (16 * d) : ℝ) *
                (2 * perturbationMajorant Φ β)))) := by
  have hsummable (D : ObservableRootDecoration F Λ) : Summable (fun n : ℕ =>
      ‖markedSubsetWeight F Λ Φ β D.support‖ *
        (decoratedObservableRootModel F Λ Φ β 0).residualSymmetricPinnedTreeDegreeSum
          (Sum.inr D) n) :=
    (decoratedObservableRootModel_summable_residualSymmetricPinnedTreeDegreeSum
      F Λ Φ hβ D).mul_left _
  unfold decoratedObservableRootLinearTreeMajorantDegreeSum
  rw [Summable.tsum_finsetSum (fun D _ => hsummable D)]
  calc
    _ = ∑ D : ObservableRootDecoration F Λ,
        ‖markedSubsetWeight F Λ Φ β D.support‖ *
          (∑' n : ℕ,
            (decoratedObservableRootModel F Λ Φ β 0).residualSymmetricPinnedTreeDegreeSum
              (Sum.inr D) n) := by
      apply Finset.sum_congr rfl
      intro D _
      rw [tsum_mul_left]
    _ ≤ ∑ D : ObservableRootDecoration F Λ,
        ‖markedSubsetWeight F Λ Φ β D.support‖ *
          Real.exp
            (decoratedObservableRootKPWeight F Λ Φ β (Sum.inr D)) := by
      apply Finset.sum_le_sum
      intro D _
      exact mul_le_mul_of_nonneg_left
        (decoratedObservableRootModel_tsum_residualSymmetricPinnedTreeDegreeSum_le
          F Λ Φ hβ D) (norm_nonneg _)
    _ ≤ _ :=
      sum_norm_markedSubsetWeight_mul_exp_decoratedRootKPWeight_le
        F Λ Φ hβ

/-- The fixed-labelled connected exponential formula also holds for the
exact exclusive decorated-root gas. -/
theorem decoratedObservableRootModel_restrictedSymmetricMayerPowerSeries_eq_formalMayerLog
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ) :
    (decoratedObservableRootModel F Λ Φ β α).restrictedSymmetricMayerPowerSeries
        Finset.univ =
      (decoratedObservableRootModel F Λ Φ β α).formalMayerLog Finset.univ := by
  exact (decoratedObservableRootModel
    F Λ Φ β α).restrictedSymmetricMayerPowerSeries_eq_formalMayerLog
    Finset.univ

/-- Scaling the common observable source records the total multiplicity of
all complete root decorations in each connected Mayer term. -/
theorem decoratedObservableRootModel_mayerClusterTerm_source
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)) :
    (decoratedObservableRootModel F Λ Φ β α).mayerClusterTerm X =
      α ^ FinitePolymerModel.exclusiveRootMultiplicity X *
        (decoratedObservableRootModel F Λ Φ β 1).mayerClusterTerm X := by
  simpa [decoratedObservableRootModel] using
    (plaquettePolymerModel Λ Φ β).mayerClusterTerm_augmentExclusiveRoots_mul
      (observableRootDecorationTouches F Λ)
      (fun D => markedSubsetWeight F Λ Φ β D.support) α X

/-- The multiplicity-one connected coefficient in one fixed total Mayer
degree for the exact decorated observable gas. -/
def decoratedObservableRootLinearMayerDegreeSum
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (n : ℕ) : ℂ :=
  (decoratedObservableRootModel F Λ Φ β 1).exclusiveRootLinearMayerDegreeSum n

/-- Every fixed decorated one-root Mayer coefficient is entire in the
coupling.  This is finite algebra over the entire bulk and marked-subset
activities. -/
theorem analyticOnNhd_decoratedObservableRootMayerClusterTerm
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)) :
    AnalyticOnNhd ℂ
      (fun β ↦ (decoratedObservableRootModel F Λ Φ β 1).mayerClusterTerm X)
      Set.univ := by
  unfold decoratedObservableRootModel FinitePolymerModel.mayerClusterTerm
    FinitePolymerModel.mayerActivityMonomial
  change AnalyticOnNhd ℂ (fun β ↦
    (((decoratedObservableRootModel F Λ Φ 0 1).mayerUrsell X : ℂ) /
      (FinitePolymerModel.mayerSymmetryFactor X : ℂ)) *
      ∏ γ, (decoratedObservableRootModel F Λ Φ β 1).activity γ ^ X γ)
    Set.univ
  apply analyticOnNhd_const.mul
  apply Finset.analyticOnNhd_fun_prod Finset.univ
  rintro (γ | D) _
  · change AnalyticOnNhd ℂ
      (fun β ↦ subsetWeight Λ Φ β γ.support ^ X (Sum.inl γ)) Set.univ
    exact (subsetWeight_entire Λ Φ γ.support).pow (X (Sum.inl γ))
  · change AnalyticOnNhd ℂ (fun β ↦
      (1 * markedSubsetWeight F Λ Φ β D.support) ^ X (Sum.inr D)) Set.univ
    simpa only [one_mul] using
      (markedSubsetWeight_entire F Λ Φ D.support).pow (X (Sum.inr D))

/-- Each fixed total-degree coefficient of the connected decorated-root
series is entire. -/
theorem analyticOnNhd_decoratedObservableRootLinearMayerDegreeSum
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (n : ℕ) :
    AnalyticOnNhd ℂ
      (fun β ↦ decoratedObservableRootLinearMayerDegreeSum F Λ Φ β n)
      Set.univ := by
  unfold decoratedObservableRootLinearMayerDegreeSum
    FinitePolymerModel.exclusiveRootLinearMayerDegreeSum
  apply Finset.analyticOnNhd_fun_sum
  intro X _
  by_cases hX : FinitePolymerModel.exclusiveRootMultiplicity X = 1
  · simp only [hX, if_true]
    exact analyticOnNhd_decoratedObservableRootMayerClusterTerm F Λ Φ X
  · simp only [hX, if_false]
    exact analyticOnNhd_const

/-- Unfolded form of the decorated connected coefficient, with the trivial
unit source multiplication removed. -/
theorem decoratedObservableRootLinearMayerDegreeSum_eq_exclusive
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (n : ℕ) :
    decoratedObservableRootLinearMayerDegreeSum F Λ Φ β n =
      ((plaquettePolymerModel Λ Φ β).augmentExclusiveRoots
        (observableRootDecorationTouches F Λ)
        (fun D => markedSubsetWeight F Λ Φ β D.support)).exclusiveRootLinearMayerDegreeSum n := by
  simp [decoratedObservableRootLinearMayerDegreeSum,
    decoratedObservableRootModel]

/-- The exact multiplicity-one connected coefficient is dominated degree by
degree by the fully summed complete-decoration residual tree majorant. -/
theorem norm_decoratedObservableRootLinearMayerDegreeSum_succ_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (n : ℕ) :
    ‖decoratedObservableRootLinearMayerDegreeSum F Λ Φ β (n + 1)‖ ≤
      decoratedObservableRootLinearTreeMajorantDegreeSum F Λ Φ β n := by
  simpa [decoratedObservableRootLinearMayerDegreeSum,
    decoratedObservableRootLinearTreeMajorantDegreeSum,
    decoratedObservableRootModel] using
      (plaquettePolymerModel Λ Φ β).norm_exclusiveRootLinearMayerDegreeSum_succ_le
        (observableRootDecorationTouches F Λ)
        (fun D => markedSubsetWeight F Λ Φ β D.support) n

/-- Genuine absolute convergence of the exact multiplicity-one connected
Mayer series for an arbitrary local observable. -/
theorem summable_norm_decoratedObservableRootLinearMayerDegreeSum_succ
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable (fun n : ℕ =>
      ‖decoratedObservableRootLinearMayerDegreeSum F Λ Φ β (n + 1)‖) := by
  exact Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (norm_decoratedObservableRootLinearMayerDegreeSum_succ_le F Λ Φ β)
    (summable_decoratedObservableRootLinearTreeMajorantDegreeSum F Λ Φ hβ)

/-- Absolute summability including the harmless degree-zero coefficient. -/
theorem summable_norm_decoratedObservableRootLinearMayerDegreeSum
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable (fun n : ℕ =>
      ‖decoratedObservableRootLinearMayerDegreeSum F Λ Φ β n‖) := by
  exact (summable_nat_add_iff
    (f := fun n : ℕ =>
      ‖decoratedObservableRootLinearMayerDegreeSum F Λ Φ β n‖) 1).mp
        (summable_norm_decoratedObservableRootLinearMayerDegreeSum_succ
          F Λ Φ hβ)

/-- Consequently the exact complex multiplicity-one connected series itself
is summable. -/
theorem summable_decoratedObservableRootLinearMayerDegreeSum_succ
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable (fun n : ℕ =>
      decoratedObservableRootLinearMayerDegreeSum F Λ Φ β (n + 1)) :=
  (summable_norm_decoratedObservableRootLinearMayerDegreeSum_succ
    F Λ Φ hβ).of_norm

/-- The total norm of the exact one-root connected series inherits the
explicit, volume-independent decorated KP/tree bound. -/
theorem tsum_norm_decoratedObservableRootLinearMayerDegreeSum_succ_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ∑' n : ℕ,
        ‖decoratedObservableRootLinearMayerDegreeSum F Λ Φ β (n + 1)‖ ≤
      ‖F.toBoundedContinuousMap‖ *
        Real.exp (((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2) *
        Real.exp
          (((observableRootPlaquettes Λ F).card : ℝ) *
            ((2 * perturbationMajorant Φ β) /
              (1 - (2 ^ (16 * d) : ℝ) *
                (2 * perturbationMajorant Φ β)))) := by
  calc
    _ ≤ ∑' n : ℕ,
        decoratedObservableRootLinearTreeMajorantDegreeSum F Λ Φ β n := by
      exact (summable_norm_decoratedObservableRootLinearMayerDegreeSum_succ
        F Λ Φ hβ).tsum_le_tsum
          (norm_decoratedObservableRootLinearMayerDegreeSum_succ_le
            F Λ Φ β)
          (summable_decoratedObservableRootLinearTreeMajorantDegreeSum
            F Λ Φ hβ)
    _ ≤ _ :=
      tsum_decoratedObservableRootLinearTreeMajorantDegreeSum_le
        F Λ Φ hβ

/-- The exact symmetric connected degree coefficient is explicitly graded by
the total decorated-root multiplicity.  Its term with exponent one is
`decoratedObservableRootLinearMayerDegreeSum`. -/
theorem decoratedObservableRootModel_symmetricMayerDegreeSum_source
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ) (n : ℕ) :
    (decoratedObservableRootModel F Λ Φ β α).symmetricMayerDegreeSum n =
      ∑ X ∈ FinitePolymerModel.mayerMultiIndicesOfDegree
          (P := PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) n,
        α ^ FinitePolymerModel.exclusiveRootMultiplicity X *
          (decoratedObservableRootModel F Λ Φ β 1).mayerClusterTerm X := by
  simpa [decoratedObservableRootModel] using
    (plaquettePolymerModel Λ Φ β).symmetricMayerDegreeSum_augmentExclusiveRoots_mul
      (observableRootDecorationTouches F Λ)
      (fun D => markedSubsetWeight F Λ Φ β D.support) α n

/-- The plaquette supports of the root-touching and away components cover the
original active subset. -/
theorem observableComponentSupport_union_awayComponentSupport
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) (hX : X ⊆ Λ.activePlaquettes) :
    polymerFamilySupport Λ (observableComponentFamily F Λ X) ∪
        polymerFamilySupport Λ (awayComponentFamily F Λ X) = X := by
  classical
  unfold polymerFamilySupport
  rw [← Finset.union_biUnion,
    observableComponentFamily_union_awayComponentFamily F Λ X]
  exact polymerFamilySupport_componentFamily_eq Λ X hX

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- Distinct members of a canonical component family read disjoint dynamic
coordinate sets. -/
theorem componentFamily_coordinateSupport_disjoint
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d))
    {γ δ : PlaquettePolymer Λ} (hγ : γ ∈ componentFamily Λ X)
    (hδ : δ ∈ componentFamily Λ X) (hγδ : γ ≠ δ) :
    Disjoint (subsetCoordinateSupport Λ γ.support : Set Λ.dynamicEdges)
      (subsetCoordinateSupport Λ δ.support : Set Λ.dynamicEdges) := by
  classical
  have hγS : γ.support ∈ componentSupports Λ X := by
    rcases Finset.mem_image.mp hγ with ⟨c, hc, rfl⟩
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hδS : δ.support ∈ componentSupports Λ X := by
    rcases Finset.mem_image.mp hδ with ⟨c, hc, rfl⟩
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hsupport : γ.support ≠ δ.support := fun h =>
    hγδ (PlaquettePolymer.support_injective h)
  exact pairwise_disjoint_componentCoordinateSupports Λ X hγS hδS hsupport

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- Distinct canonical components have disjoint untyped plaquette supports. -/
theorem componentFamily_support_disjoint
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d))
    {γ δ : PlaquettePolymer Λ} (hγ : γ ∈ componentFamily Λ X)
    (hδ : δ ∈ componentFamily Λ X) (hγδ : γ ≠ δ) :
    Disjoint γ.support δ.support := by
  classical
  have hγS : γ.support ∈ componentSupports Λ X := by
    rcases Finset.mem_image.mp hγ with ⟨c, hc, rfl⟩
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hδS : δ.support ∈ componentSupports Λ X := by
    rcases Finset.mem_image.mp hδ with ⟨c, hc, rfl⟩
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hsupport : γ.support ≠ δ.support := fun h =>
    hγδ (PlaquettePolymer.support_injective h)
  exact pairwise_disjoint_componentSupports Λ X hγS hδS hsupport

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- Dynamic-coordinate membership in a polymer-family support can be exposed
at one member of the family. -/
theorem mem_subsetCoordinateSupport_polymerFamilySupport_iff
    (Λ : FiniteSpecification d G) (Gamma : Finset (PlaquettePolymer Λ))
    (e : Λ.dynamicEdges) :
    e ∈ subsetCoordinateSupport Λ (polymerFamilySupport Λ Gamma) ↔
      ∃ gamma ∈ Gamma, e ∈ subsetCoordinateSupport Λ gamma.support := by
  classical
  simp only [subsetCoordinateSupport, polymerFamilySupport,
    Finset.mem_biUnion]
  constructor
  · rintro ⟨p, ⟨gamma, hgamma, hpgamma⟩, hep⟩
    exact ⟨gamma, hgamma, p, hpgamma, hep⟩
  · rintro ⟨gamma, hgamma, p, hpgamma, hep⟩
    exact ⟨p, ⟨gamma, hgamma, hpgamma⟩, hep⟩

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
@[simp]
theorem mem_polymerFamilySupport_iff
    (Λ : FiniteSpecification d G) (Gamma : Finset (PlaquettePolymer Λ))
    (p : Plaquette d) :
    p ∈ polymerFamilySupport Λ Gamma ↔ ∃ gamma ∈ Gamma, p ∈ gamma.support := by
  classical
  simp [polymerFamilySupport]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- Two disjoint subfamilies of one canonical component family read disjoint
dynamic coordinate sets. -/
theorem componentSubfamilies_coordinateSupport_disjoint
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d))
    (Gamma Delta : Finset (PlaquettePolymer Λ))
    (hGamma : Gamma ⊆ componentFamily Λ X)
    (hDelta : Delta ⊆ componentFamily Λ X)
    (hdisjoint : Disjoint Gamma Delta) :
    Disjoint
      (subsetCoordinateSupport Λ (polymerFamilySupport Λ Gamma) :
        Set Λ.dynamicEdges)
      (subsetCoordinateSupport Λ (polymerFamilySupport Λ Delta) :
        Set Λ.dynamicEdges) := by
  classical
  rw [Set.disjoint_left]
  intro e heGamma heDelta
  rcases (mem_subsetCoordinateSupport_polymerFamilySupport_iff Λ Gamma e).mp
      heGamma with ⟨gamma, hgamma, hegamma⟩
  rcases (mem_subsetCoordinateSupport_polymerFamilySupport_iff Λ Delta e).mp
      heDelta with ⟨delta, hdelta, hedelta⟩
  have hne : gamma ≠ delta := by
    intro heq
    subst delta
    exact Finset.disjoint_left.mp hdisjoint hgamma hdelta
  exact Set.disjoint_left.mp
    (componentFamily_coordinateSupport_disjoint Λ X
      (hGamma hgamma) (hDelta hdelta) hne) hegamma hedelta

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- The underlying plaquette unions of two disjoint canonical component
subfamilies are disjoint as well. -/
theorem componentSubfamilies_support_disjoint
    (Λ : FiniteSpecification d G) (X : Finset (Plaquette d))
    (Gamma Delta : Finset (PlaquettePolymer Λ))
    (hGamma : Gamma ⊆ componentFamily Λ X)
    (hDelta : Delta ⊆ componentFamily Λ X)
    (hdisjoint : Disjoint Gamma Delta) :
    Disjoint (polymerFamilySupport Λ Gamma)
      (polymerFamilySupport Λ Delta) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpGamma hpDelta
  rcases (mem_polymerFamilySupport_iff Λ Gamma p).mp hpGamma with
    ⟨gamma, hgamma, hpgamma⟩
  rcases (mem_polymerFamilySupport_iff Λ Delta p).mp hpDelta with
    ⟨delta, hdelta, hpdelta⟩
  have hne : gamma ≠ delta := by
    intro heq
    subst delta
    exact Finset.disjoint_left.mp hdisjoint hgamma hdelta
  exact Finset.disjoint_left.mp
    (componentFamily_support_disjoint Λ X
      (hGamma hgamma) (hDelta hdelta) hne) hpgamma hpdelta

/-- An observable is coordinate-disjoint from any canonical component
subfamily whose members all avoid that observable. -/
theorem disjoint_observableCoordinateSupport_componentSubfamily
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Gamma : Finset (PlaquettePolymer Λ))
    (havoid : ∀ gamma ∈ Gamma, ¬observableRootTouches F Λ gamma) :
    Disjoint (observableCoordinateSupport F Λ : Set Λ.dynamicEdges)
      (subsetCoordinateSupport Λ (polymerFamilySupport Λ Gamma) :
        Set Λ.dynamicEdges) := by
  classical
  rw [Set.disjoint_left]
  intro e heF heGamma
  rcases (mem_subsetCoordinateSupport_polymerFamilySupport_iff Λ Gamma e).mp
      heGamma with ⟨gamma, hgamma, hegamma⟩
  apply havoid gamma hgamma
  rw [observableRootTouches_iff]
  rcases Finset.mem_biUnion.mp hegamma with ⟨p, hpgamma, hep⟩
  rcases Finset.mem_map.mp hpgamma with ⟨q, hqgamma, hqp⟩
  refine ⟨q, hqgamma, ?_⟩
  rw [mem_observableRootPlaquettes, Finset.not_disjoint_iff]
  refine ⟨e.1, ?_, ?_⟩
  · have hep' : e.1 ∈ p.boundary.edgeSupport := by
      simpa [plaquetteCoordinateSupport] using hep
    have hqp' : q.1 = p := hqp
    rw [hqp']
    exact hep'
  · simpa [observableCoordinateSupport] using heF

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
/-- Disjoint recorded supports give disjoint dynamic observable-coordinate
supports in every finite specification. -/
theorem disjoint_observableCoordinateSupport_of_disjoint_support
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (hFH : Disjoint F.support H.support) :
    Disjoint (observableCoordinateSupport F Λ : Set Λ.dynamicEdges)
      (observableCoordinateSupport H Λ : Set Λ.dynamicEdges) := by
  rw [Set.disjoint_left]
  intro e heF heH
  exact Finset.disjoint_left.mp hFH
    (by simpa [observableCoordinateSupport] using heF)
    (by simpa [observableCoordinateSupport] using heH)

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem subsetCoordinateSupport_union
    (Λ : FiniteSpecification d G) (A B : Finset (Plaquette d)) :
    subsetCoordinateSupport Λ (A ∪ B) =
      subsetCoordinateSupport Λ A ∪ subsetCoordinateSupport Λ B := by
  classical
  ext e
  simp only [subsetCoordinateSupport, Finset.mem_biUnion,
    Finset.mem_union]
  constructor
  · rintro ⟨p, hpA | hpB, hep⟩
    · exact Or.inl ⟨p, hpA, hep⟩
    · exact Or.inr ⟨p, hpB, hep⟩
  · rintro (⟨p, hpA, hep⟩ | ⟨p, hpB, hep⟩)
    · exact ⟨p, Or.inl hpA, hep⟩
    · exact ⟨p, Or.inr hpB, hep⟩

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
theorem observableCoordinateSupport_mul
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G) :
    observableCoordinateSupport (F.mul H) Λ =
      observableCoordinateSupport F Λ ∪ observableCoordinateSupport H Λ := by
  classical
  ext e
  simp [observableCoordinateSupport, LocalObservable.mul]

/-- If no canonical plaquette component touches both disjoint observable
supports, the doubly marked weight factors into the two one-root decorations
and the ordinary family of components avoiding both roots.  This is the exact
finite cancellation statement for the non-spanning sector. -/
theorem markedSubsetWeight_mul_eq_separatedRootComponents
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) (hX : X ⊆ Λ.activePlaquettes)
    (hFH : Disjoint F.support H.support)
    (hjoint : jointlyObservableComponentFamily F H Λ X = ∅) :
    markedSubsetWeight (F.mul H) Λ Φ β X =
      markedSubsetWeight F Λ Φ β
          (polymerFamilySupport Λ (firstOnlyComponentFamily F H Λ X)) *
        markedSubsetWeight H Λ Φ β
          (polymerFamilySupport Λ (secondOnlyComponentFamily F H Λ X)) *
        (plaquettePolymerModel Λ Φ β).familyWeight
          (twoObservableAwayComponentFamily F H Λ X) := by
  classical
  let GammaF := firstOnlyComponentFamily F H Λ X
  let GammaH := secondOnlyComponentFamily F H Λ X
  let GammaAway := twoObservableAwayComponentFamily F H Λ X
  let A := polymerFamilySupport Λ GammaF
  let B := polymerFamilySupport Λ GammaH
  let C := polymerFamilySupport Λ GammaAway
  have hGammaF : GammaF ⊆ componentFamily Λ X := by
    intro gamma hgamma
    exact (mem_firstOnlyComponentFamily F H Λ X gamma).mp hgamma |>.1
  have hGammaH : GammaH ⊆ componentFamily Λ X := by
    intro gamma hgamma
    exact (mem_secondOnlyComponentFamily F H Λ X gamma).mp hgamma |>.1
  have hGammaAway : GammaAway ⊆ componentFamily Λ X := by
    intro gamma hgamma
    exact (mem_twoObservableAwayComponentFamily F H Λ X gamma).mp hgamma |>.1
  have hdisjointFH : Disjoint GammaF GammaH := by
    rw [Finset.disjoint_left]
    intro gamma hgammaF hgammaH
    exact ((mem_secondOnlyComponentFamily F H Λ X gamma).mp hgammaH).2.1
      ((mem_firstOnlyComponentFamily F H Λ X gamma).mp hgammaF).2.1
  have hdisjointFAway : Disjoint GammaF GammaAway := by
    rw [Finset.disjoint_left]
    intro gamma hgammaF hgammaAway
    exact ((mem_twoObservableAwayComponentFamily F H Λ X gamma).mp
      hgammaAway).2.1
        ((mem_firstOnlyComponentFamily F H Λ X gamma).mp hgammaF).2.1
  have hdisjointHAway : Disjoint GammaH GammaAway := by
    rw [Finset.disjoint_left]
    intro gamma hgammaH hgammaAway
    exact ((mem_twoObservableAwayComponentFamily F H Λ X gamma).mp
      hgammaAway).2.2
        ((mem_secondOnlyComponentFamily F H Λ X gamma).mp hgammaH).2.2
  have hpart : (GammaF ∪ GammaH) ∪ GammaAway = componentFamily Λ X := by
    have h := twoObservableComponentFamilies_partition F H Λ X
    simpa [GammaF, GammaH, GammaAway, hjoint] using h
  have hcover : (A ∪ B) ∪ C = X := by
    unfold A B C polymerFamilySupport
    rw [← Finset.union_biUnion, ← Finset.union_biUnion, hpart]
    exact polymerFamilySupport_componentFamily_eq Λ X hX
  have hAB : Disjoint A B := by
    exact componentSubfamilies_support_disjoint Λ X GammaF GammaH
      hGammaF hGammaH hdisjointFH
  have hAC : Disjoint A C := by
    exact componentSubfamilies_support_disjoint Λ X GammaF GammaAway
      hGammaF hGammaAway hdisjointFAway
  have hBC : Disjoint B C := by
    exact componentSubfamilies_support_disjoint Λ X GammaH GammaAway
      hGammaH hGammaAway hdisjointHAway
  have hcoordAB : Disjoint
      (subsetCoordinateSupport Λ A : Set Λ.dynamicEdges)
      (subsetCoordinateSupport Λ B : Set Λ.dynamicEdges) := by
    exact componentSubfamilies_coordinateSupport_disjoint Λ X GammaF GammaH
      hGammaF hGammaH hdisjointFH
  have hcoordAC : Disjoint
      (subsetCoordinateSupport Λ A : Set Λ.dynamicEdges)
      (subsetCoordinateSupport Λ C : Set Λ.dynamicEdges) := by
    exact componentSubfamilies_coordinateSupport_disjoint Λ X GammaF GammaAway
      hGammaF hGammaAway hdisjointFAway
  have hcoordBC : Disjoint
      (subsetCoordinateSupport Λ B : Set Λ.dynamicEdges)
      (subsetCoordinateSupport Λ C : Set Λ.dynamicEdges) := by
    exact componentSubfamilies_coordinateSupport_disjoint Λ X GammaH GammaAway
      hGammaH hGammaAway hdisjointHAway
  have hF_B : Disjoint
      (observableCoordinateSupport F Λ : Set Λ.dynamicEdges)
      (subsetCoordinateSupport Λ B : Set Λ.dynamicEdges) := by
    exact disjoint_observableCoordinateSupport_componentSubfamily F Λ GammaH
      (fun gamma hgamma =>
        (mem_secondOnlyComponentFamily F H Λ X gamma).mp hgamma |>.2.1)
  have hH_A : Disjoint
      (observableCoordinateSupport H Λ : Set Λ.dynamicEdges)
      (subsetCoordinateSupport Λ A : Set Λ.dynamicEdges) := by
    exact disjoint_observableCoordinateSupport_componentSubfamily H Λ GammaF
      (fun gamma hgamma =>
        (mem_firstOnlyComponentFamily F H Λ X gamma).mp hgamma |>.2.2)
  have hF_C : Disjoint
      (observableCoordinateSupport F Λ : Set Λ.dynamicEdges)
      (subsetCoordinateSupport Λ C : Set Λ.dynamicEdges) := by
    exact disjoint_observableCoordinateSupport_componentSubfamily F Λ GammaAway
      (fun gamma hgamma =>
        (mem_twoObservableAwayComponentFamily F H Λ X gamma).mp hgamma |>.2.1)
  have hH_C : Disjoint
      (observableCoordinateSupport H Λ : Set Λ.dynamicEdges)
      (subsetCoordinateSupport Λ C : Set Λ.dynamicEdges) := by
    exact disjoint_observableCoordinateSupport_componentSubfamily H Λ GammaAway
      (fun gamma hgamma =>
        (mem_twoObservableAwayComponentFamily F H Λ X gamma).mp hgamma |>.2.2)
  have hF_H : Disjoint
      (observableCoordinateSupport F Λ : Set Λ.dynamicEdges)
      (observableCoordinateSupport H Λ : Set Λ.dynamicEdges) :=
    disjoint_observableCoordinateSupport_of_disjoint_support F H Λ hFH
  have hedgesAB : Disjoint
      ((observableCoordinateSupport F Λ : Set Λ.dynamicEdges) ∪
        (subsetCoordinateSupport Λ A : Set Λ.dynamicEdges))
      ((observableCoordinateSupport H Λ : Set Λ.dynamicEdges) ∪
        (subsetCoordinateSupport Λ B : Set Λ.dynamicEdges)) := by
    rw [Set.disjoint_left]
    intro e heLeft heRight
    rcases heLeft with heF | heA
    · rcases heRight with heH | heB
      · exact Set.disjoint_left.mp hF_H heF heH
      · exact Set.disjoint_left.mp hF_B heF heB
    · rcases heRight with heH | heB
      · exact Set.disjoint_left.mp hH_A heH heA
      · exact Set.disjoint_left.mp hcoordAB heA heB
  have hABC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro p hpAB hpC
    rcases Finset.mem_union.mp hpAB with hpA | hpB
    · exact Finset.disjoint_left.mp hAC hpA hpC
    · exact Finset.disjoint_left.mp hBC hpB hpC
  have hedgesC : Disjoint
      ((observableCoordinateSupport (F.mul H) Λ : Set Λ.dynamicEdges) ∪
        (subsetCoordinateSupport Λ (A ∪ B) : Set Λ.dynamicEdges))
      (subsetCoordinateSupport Λ C : Set Λ.dynamicEdges) := by
    rw [Set.disjoint_left]
    intro e heLeft heC
    rcases heLeft with heObs | heAB
    · have heObs' : e ∈ observableCoordinateSupport (F.mul H) Λ := heObs
      rw [observableCoordinateSupport_mul] at heObs'
      rcases Finset.mem_union.mp heObs' with heF | heH
      · exact Set.disjoint_left.mp hF_C heF heC
      · exact Set.disjoint_left.mp hH_C heH heC
    · have heAB' : e ∈ subsetCoordinateSupport Λ (A ∪ B) := heAB
      rw [subsetCoordinateSupport_union] at heAB'
      rcases Finset.mem_union.mp heAB' with heA | heB
      · exact Set.disjoint_left.mp hcoordAC heA heC
      · exact Set.disjoint_left.mp hcoordBC heB heC
  have hAwayCompatible :
      (plaquettePolymerModel Λ Φ β).Compatible GammaAway := by
    intro gamma hgamma delta hdelta hne
    exact componentFamily_compatible Λ Φ β X
      (hGammaAway hgamma) (hGammaAway hdelta) hne
  have hAwayCanonical : GammaAway = componentFamily Λ C := by
    exact compatibleFamily_eq_componentFamily Λ Φ β GammaAway C
      hAwayCompatible rfl
  calc
    markedSubsetWeight (F.mul H) Λ Φ β X =
        markedSubsetWeight (F.mul H) Λ Φ β ((A ∪ B) ∪ C) := by
      rw [hcover]
    _ = markedSubsetWeight (F.mul H) Λ Φ β (A ∪ B) *
        subsetWeight Λ Φ β C :=
      markedSubsetWeight_union_of_disjoint (F.mul H) Λ Φ β
        (A ∪ B) C hABC hedgesC
    _ = (markedSubsetWeight F Λ Φ β A *
          markedSubsetWeight H Λ Φ β B) * subsetWeight Λ Φ β C := by
      rw [markedSubsetWeight_mul_union_of_disjoint F H Λ Φ β A B hAB hedgesAB]
    _ = (markedSubsetWeight F Λ Φ β A *
          markedSubsetWeight H Λ Φ β B) *
        (plaquettePolymerModel Λ Φ β).familyWeight GammaAway := by
      rw [subsetWeight_eq_componentFamilyWeight Λ Φ β C
        (polymerFamilySupport_subset_active Λ GammaAway), ← hAwayCanonical]
    _ = _ := rfl

/-- The plaquette unions carried by the root and away component families are
disjoint. -/
theorem disjoint_observableComponentSupport_awayComponentSupport
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) :
    Disjoint (polymerFamilySupport Λ (observableComponentFamily F Λ X))
      (polymerFamilySupport Λ (awayComponentFamily F Λ X)) := by
  classical
  rw [Finset.disjoint_left]
  intro p hproot hpaway
  rcases (mem_polymerFamilySupport_iff Λ
    (observableComponentFamily F Λ X) p).mp hproot with ⟨γ, hγ, hpγ⟩
  rcases (mem_polymerFamilySupport_iff Λ
    (awayComponentFamily F Λ X) p).mp hpaway with ⟨δ, hδ, hpδ⟩
  have hγdata := (mem_observableComponentFamily F Λ X γ).mp hγ
  have hδdata := (mem_awayComponentFamily F Λ X δ).mp hδ
  have hγδ : γ ≠ δ := by
    intro h
    subst δ
    exact hδdata.2 hγdata.2
  exact Finset.disjoint_left.mp
    (componentFamily_support_disjoint Λ X hγdata.1 hδdata.1 hγδ)
    hpγ hpδ

/-- The unions of dynamic coordinate supports of the root and away component
families are disjoint. -/
theorem disjoint_observableComponentSupport_awayComponentSupport_coordinates
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) :
    Disjoint
      (subsetCoordinateSupport Λ
        (polymerFamilySupport Λ (observableComponentFamily F Λ X)) :
          Set Λ.dynamicEdges)
      (subsetCoordinateSupport Λ
        (polymerFamilySupport Λ (awayComponentFamily F Λ X)) :
          Set Λ.dynamicEdges) := by
  classical
  rw [Set.disjoint_left]
  intro e heroot heaway
  have heroot' : e ∈ subsetCoordinateSupport Λ
      (polymerFamilySupport Λ (observableComponentFamily F Λ X)) := heroot
  have heaway' : e ∈ subsetCoordinateSupport Λ
      (polymerFamilySupport Λ (awayComponentFamily F Λ X)) := heaway
  rcases (mem_subsetCoordinateSupport_polymerFamilySupport_iff Λ
    (observableComponentFamily F Λ X) e).mp heroot' with ⟨γ, hγ, heγ⟩
  rcases (mem_subsetCoordinateSupport_polymerFamilySupport_iff Λ
    (awayComponentFamily F Λ X) e).mp heaway' with ⟨δ, hδ, heδ⟩
  have hγdata := (mem_observableComponentFamily F Λ X γ).mp hγ
  have hδdata := (mem_awayComponentFamily F Λ X δ).mp hδ
  have hγδ : γ ≠ δ := by
    intro h
    subst δ
    exact hδdata.2 hγdata.2
  exact Set.disjoint_left.mp
    (componentFamily_coordinateSupport_disjoint Λ X hγdata.1 hδdata.1 hγδ)
    heγ heδ

/-- Every away component avoids the dynamic coordinate support of the local
observable. -/
theorem disjoint_observableCoordinateSupport_awayComponentSupport
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) :
    Disjoint (observableCoordinateSupport F Λ : Set Λ.dynamicEdges)
      (subsetCoordinateSupport Λ
        (polymerFamilySupport Λ (awayComponentFamily F Λ X)) :
          Set Λ.dynamicEdges) := by
  classical
  rw [Set.disjoint_left]
  intro e heF heaway
  have heaway' : e ∈ subsetCoordinateSupport Λ
      (polymerFamilySupport Λ (awayComponentFamily F Λ X)) := heaway
  rcases (mem_subsetCoordinateSupport_polymerFamilySupport_iff Λ
    (awayComponentFamily F Λ X) e).mp heaway' with ⟨δ, hδ, heδ⟩
  have hδdata := (mem_awayComponentFamily F Λ X δ).mp hδ
  apply hδdata.2
  rw [observableRootTouches_iff]
  rcases Finset.mem_biUnion.mp heδ with ⟨p, hpδ, hep⟩
  rcases Finset.mem_map.mp hpδ with ⟨q, hqδ, hqp⟩
  refine ⟨q, hqδ, ?_⟩
  rw [mem_observableRootPlaquettes, Finset.not_disjoint_iff]
  refine ⟨e.1, ?_, ?_⟩
  · have hep' : e.1 ∈ p.boundary.edgeSupport := by
      simpa [plaquetteCoordinateSupport] using hep
    have hqp' : q.1 = p := hqp
    rw [hqp']
    exact hep'
  · simpa [observableCoordinateSupport] using heF

/-- The away subfamily remains compatible. -/
theorem awayComponentFamily_compatible
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) :
    (plaquettePolymerModel Λ Φ β).Compatible
      (awayComponentFamily F Λ X) := by
  intro γ hγ δ hδ hγδ
  exact componentFamily_compatible Λ Φ β X
    ((mem_awayComponentFamily F Λ X γ).mp hγ).1
    ((mem_awayComponentFamily F Λ X δ).mp hδ).1 hγδ

/-- The away family is precisely allowed alongside the canonical complete
root decoration of the same plaquette subset. -/
theorem awayComponentFamily_subset_decorationCompatibleBulk
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) :
    awayComponentFamily F Λ X ⊆
      observableRootDecorationCompatibleBulk F Λ
        (observableRootDecorationOfSubset F Λ Φ β X) := by
  classical
  intro γ hγ
  rw [observableRootDecorationCompatibleBulk, Finset.mem_filter]
  refine ⟨Finset.mem_univ γ, ?_⟩
  intro hconflict
  rcases hconflict with htouch | ⟨δ, hδ, hδγ⟩
  · exact ((mem_awayComponentFamily F Λ X γ).mp hγ).2 htouch
  · have hδroot : δ ∈ observableComponentFamily F Λ X := by
      simpa using hδ
    have hδdata := (mem_observableComponentFamily F Λ X δ).mp hδroot
    have hγdata := (mem_awayComponentFamily F Λ X γ).mp hγ
    have hδγne : δ ≠ γ := by
      intro h
      subst γ
      exact hγdata.2 hδdata.2
    exact componentFamily_compatible Λ Φ β X
      hδdata.1 hγdata.1 hδγne hδγ

/-- Canonical decorated pair attached to a plaquette subset. -/
def observableRootDecoratedPairOfSubset
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) :
    ObservableRootDecoration F Λ × Finset (PlaquettePolymer Λ) :=
  (observableRootDecorationOfSubset F Λ Φ β X,
    awayComponentFamily F Λ X)

theorem observableRootDecoratedPairOfSubset_mem
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) :
    observableRootDecoratedPairOfSubset F Λ Φ β X ∈
      observableRootDecoratedPairs F Λ Φ β := by
  classical
  rw [observableRootDecoratedPairs, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, awayComponentFamily_compatible F Λ Φ β X,
    awayComponentFamily_subset_decorationCompatibleBulk F Λ Φ β X⟩

/-- The canonical decorated pair remembers the original active plaquette
subset. -/
theorem observableRootDecoratedPairOfSubset_injectiveOn
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    Set.InjOn (observableRootDecoratedPairOfSubset F Λ Φ β)
      (Λ.activePlaquettes.powerset :
        Set (Finset (Plaquette d))) := by
  classical
  intro X hX Y hY hpair
  have hroot : observableComponentFamily F Λ X =
      observableComponentFamily F Λ Y := by
    have hfst := congrArg Prod.fst hpair
    exact congrArg Subtype.val hfst
  have haway : awayComponentFamily F Λ X =
      awayComponentFamily F Λ Y := congrArg Prod.snd hpair
  have hcoverX := observableComponentSupport_union_awayComponentSupport
    F Λ X (Finset.mem_powerset.mp hX)
  have hcoverY := observableComponentSupport_union_awayComponentSupport
    F Λ Y (Finset.mem_powerset.mp hY)
  rw [← hcoverX, ← hcoverY, hroot, haway]

/-- Every admissible complete-decoration/bulk-family pair comes from the
canonical component split of a unique active plaquette subset. -/
theorem observableRootDecoratedPairOfSubset_surjective
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (pair : ObservableRootDecoration F Λ ×
      Finset (PlaquettePolymer Λ))
    (hpair : pair ∈ observableRootDecoratedPairs F Λ Φ β) :
    ∃ X ∈ Λ.activePlaquettes.powerset,
      observableRootDecoratedPairOfSubset F Λ Φ β X = pair := by
  classical
  rcases pair with ⟨D, Γ⟩
  have hdata := (Finset.mem_filter.mp hpair).2
  have hΓcompatible := hdata.1
  have hΓallowed := hdata.2
  let X := D.support ∪ polymerFamilySupport Λ Γ
  have hXsub : X ⊆ Λ.activePlaquettes := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpD | hpΓ
    · exact polymerFamilySupport_subset_active Λ D.1 hpD
    · exact polymerFamilySupport_subset_active Λ Γ hpΓ
  have hcombined : (plaquettePolymerModel Λ Φ β).Compatible (D.1 ∪ Γ) := by
    intro γ hγ δ hδ hγδ
    rcases Finset.mem_union.mp hγ with hγD | hγΓ
    · rcases Finset.mem_union.mp hδ with hδD | hδΓ
      · exact D.2.1 hγD hδD hγδ
      · intro hinc
        have hallowed := (Finset.mem_filter.mp (hΓallowed hδΓ)).2
        exact hallowed (Or.inr ⟨γ, hγD, hinc⟩)
    · rcases Finset.mem_union.mp hδ with hδD | hδΓ
      · intro hinc
        have hallowed := (Finset.mem_filter.mp (hΓallowed hγΓ)).2
        exact hallowed (Or.inr ⟨δ, hδD,
          plaquettePolymerIncompatible_symmetric Λ hinc⟩)
      · exact hΓcompatible hγΓ hδΓ hγδ
  have hcover : polymerFamilySupport Λ (D.1 ∪ Γ) = X := by
    unfold X ObservableRootDecoration.support polymerFamilySupport
    exact Finset.union_biUnion
  have hcanonical : D.1 ∪ Γ = componentFamily Λ X :=
    compatibleFamily_eq_componentFamily Λ Φ β (D.1 ∪ Γ) X
      hcombined hcover
  have hroot : observableComponentFamily F Λ X = D.1 := by
    ext γ
    constructor
    · intro hγ
      have hγdata := (mem_observableComponentFamily F Λ X γ).mp hγ
      have hγunion : γ ∈ D.1 ∪ Γ := hcanonical ▸ hγdata.1
      rcases Finset.mem_union.mp hγunion with hγD | hγΓ
      · exact hγD
      · have hallowed := (Finset.mem_filter.mp (hΓallowed hγΓ)).2
        exact (hallowed (Or.inl hγdata.2)).elim
    · intro hγD
      apply (mem_observableComponentFamily F Λ X γ).mpr
      refine ⟨hcanonical ▸ Finset.mem_union_left Γ hγD, ?_⟩
      exact D.2.2 γ hγD
  have haway : awayComponentFamily F Λ X = Γ := by
    ext γ
    constructor
    · intro hγ
      have hγdata := (mem_awayComponentFamily F Λ X γ).mp hγ
      have hγunion : γ ∈ D.1 ∪ Γ := hcanonical ▸ hγdata.1
      rcases Finset.mem_union.mp hγunion with hγD | hγΓ
      · exact (hγdata.2 (D.2.2 γ hγD)).elim
      · exact hγΓ
    · intro hγΓ
      apply (mem_awayComponentFamily F Λ X γ).mpr
      refine ⟨hcanonical ▸ Finset.mem_union_right D.1 hγΓ, ?_⟩
      have hallowed := (Finset.mem_filter.mp (hΓallowed hγΓ)).2
      exact fun htouch => hallowed (Or.inl htouch)
  refine ⟨X, Finset.mem_powerset.mpr hXsub, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    exact hroot
  · exact haway

/-- Exact marked connected-component factorization: every canonical
component avoiding the observable support factors into its ordinary polymer
activity, while all root-touching components remain together in one marked
weight. -/
theorem markedSubsetWeight_eq_rootComponentWeight_mul_awayFamilyWeight
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) (hX : X ⊆ Λ.activePlaquettes) :
    markedSubsetWeight F Λ Φ β X =
      markedSubsetWeight F Λ Φ β
          (polymerFamilySupport Λ (observableComponentFamily F Λ X)) *
        (plaquettePolymerModel Λ Φ β).familyWeight
          (awayComponentFamily F Λ X) := by
  classical
  let Γroot := observableComponentFamily F Λ X
  let Γaway := awayComponentFamily F Λ X
  let A := polymerFamilySupport Λ Γroot
  let B := polymerFamilySupport Λ Γaway
  have hcover : A ∪ B = X := by
    simpa [A, B, Γroot, Γaway] using
      observableComponentSupport_union_awayComponentSupport F Λ X hX
  have hAB : Disjoint A B := by
    simpa [A, B, Γroot, Γaway] using
      disjoint_observableComponentSupport_awayComponentSupport F Λ X
  have hrootEdges : Disjoint
      (subsetCoordinateSupport Λ A : Set Λ.dynamicEdges)
      (subsetCoordinateSupport Λ B : Set Λ.dynamicEdges) := by
    simpa [A, B, Γroot, Γaway] using
      disjoint_observableComponentSupport_awayComponentSupport_coordinates
        F Λ X
  have hobservableEdges : Disjoint
      (observableCoordinateSupport F Λ : Set Λ.dynamicEdges)
      (subsetCoordinateSupport Λ B : Set Λ.dynamicEdges) := by
    simpa [B, Γaway] using
      disjoint_observableCoordinateSupport_awayComponentSupport F Λ X
  have hedges : Disjoint
      ((observableCoordinateSupport F Λ : Set Λ.dynamicEdges) ∪
        (subsetCoordinateSupport Λ A : Set Λ.dynamicEdges))
      (subsetCoordinateSupport Λ B : Set Λ.dynamicEdges) := by
    rw [Set.disjoint_left]
    intro e he heB
    rcases he with heF | heA
    · exact Set.disjoint_left.mp hobservableEdges heF heB
    · exact Set.disjoint_left.mp hrootEdges heA heB
  have hawayCompatible :
      (plaquettePolymerModel Λ Φ β).Compatible Γaway := by
    intro γ hγ δ hδ hγδ
    exact componentFamily_compatible Λ Φ β X
      ((mem_awayComponentFamily F Λ X γ).mp hγ).1
      ((mem_awayComponentFamily F Λ X δ).mp hδ).1 hγδ
  have hcanonical : Γaway = componentFamily Λ B := by
    apply compatibleFamily_eq_componentFamily Λ Φ β Γaway B hawayCompatible
    rfl
  calc
    markedSubsetWeight F Λ Φ β X = markedSubsetWeight F Λ Φ β (A ∪ B) := by
      rw [hcover]
    _ = markedSubsetWeight F Λ Φ β A * subsetWeight Λ Φ β B :=
      markedSubsetWeight_union_of_disjoint F Λ Φ β A B hAB hedges
    _ = markedSubsetWeight F Λ Φ β A *
        (plaquettePolymerModel Λ Φ β).familyWeight Γaway := by
      rw [subsetWeight_eq_componentFamilyWeight Λ Φ β B
        (polymerFamilySupport_subset_active Λ Γaway), ← hcanonical]
    _ = markedSubsetWeight F Λ Φ β
          (polymerFamilySupport Λ (observableComponentFamily F Λ X)) *
        (plaquettePolymerModel Λ Φ β).familyWeight
          (awayComponentFamily F Λ X) := rfl

/-- Exact observable-root component expansion of the finite-volume numerator.
Every summand consists of one possibly disconnected marked root decoration
and an ordinary compatible family of components avoiding the observable. -/
theorem complexObservableNumerator_eq_sum_rootComponentWeight_mul_awayFamilyWeight
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    complexObservableNumerator F Λ Φ β =
      ∑ X ∈ Λ.activePlaquettes.powerset,
        markedSubsetWeight F Λ Φ β
            (polymerFamilySupport Λ (observableComponentFamily F Λ X)) *
          (plaquettePolymerModel Λ Φ β).familyWeight
            (awayComponentFamily F Λ X) := by
  rw [complexObservableNumerator_eq_sum_markedSubsetWeight]
  apply Finset.sum_congr rfl
  intro X hX
  exact markedSubsetWeight_eq_rootComponentWeight_mul_awayFamilyWeight
    F Λ Φ β X (Finset.mem_powerset.mp hX)

/-- The exclusive decorated-root coefficient is exactly the arbitrary local
observable numerator.  This is the finite reindexing that turns the marked
component decomposition into a genuine source-polymer expansion. -/
theorem decoratedObservableRootCoefficient_eq_complexObservableNumerator
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    decoratedObservableRootCoefficient F Λ Φ β =
      complexObservableNumerator F Λ Φ β := by
  rw [complexObservableNumerator_eq_sum_rootComponentWeight_mul_awayFamilyWeight]
  unfold decoratedObservableRootCoefficient
  symm
  apply Finset.sum_bij
    (fun X _ => observableRootDecoratedPairOfSubset F Λ Φ β X)
  · intro X _hX
    exact observableRootDecoratedPairOfSubset_mem F Λ Φ β X
  · intro X hX Y hY hXY
    exact observableRootDecoratedPairOfSubset_injectiveOn F Λ Φ β hX hY hXY
  · intro pair hpair
    rcases observableRootDecoratedPairOfSubset_surjective F Λ Φ β pair hpair with
      ⟨X, hX, hmap⟩
    exact ⟨X, hX, hmap⟩
  · intro X _hX
    rfl

/-- The exact source polynomial written in vacuum-polymer plus exclusive
decorated-root form. -/
def decoratedObservableSourcePartition
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ) : ℂ :=
  (plaquettePolymerModel Λ Φ β).partitionFunction +
    α * decoratedObservableRootCoefficient F Λ Φ β

/-- The decorated-root source polynomial is exactly the original arbitrary
local-observable source partition. -/
theorem decoratedObservableSourcePartition_eq_oneObservableSourcePartition
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ) :
    decoratedObservableSourcePartition F Λ Φ β α =
      oneObservableSourcePartition F Λ Φ β α := by
  rw [decoratedObservableSourcePartition, oneObservableSourcePartition,
    complexPartitionFunction_eq_polymerPartition,
    decoratedObservableRootCoefficient_eq_complexObservableNumerator]

/-- The full partition function of the exclusive decorated-root gas is the
exact observable source polynomial. -/
theorem decoratedObservableRootModel_partitionFunction
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ) :
    (decoratedObservableRootModel F Λ Φ β α).partitionFunction =
      decoratedObservableSourcePartition F Λ Φ β α := by
  rw [decoratedObservableRootModel]
  rw [Polymer.FinitePolymerModel.augmentExclusiveRoots_partitionFunction]
  rw [← observableRootDecoratedPairs_eq_exclusiveRootPairs F Λ Φ β]
  unfold decoratedObservableSourcePartition decoratedObservableRootCoefficient
  rw [Finset.mul_sum]
  apply congrArg (fun z : ℂ =>
    (plaquettePolymerModel Λ Φ β).partitionFunction + z)
  apply Finset.sum_congr rfl
  intro pair _hpair
  ring

/-- Consequently the augmented polymer gas reproduces the original
arbitrary-local-observable source partition exactly. -/
theorem decoratedObservableRootModel_partitionFunction_eq_oneObservableSourcePartition
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ) :
    (decoratedObservableRootModel F Λ Φ β α).partitionFunction =
      oneObservableSourcePartition F Λ Φ β α := by
  rw [decoratedObservableRootModel_partitionFunction,
    decoratedObservableSourcePartition_eq_oneObservableSourcePartition]

/-! ## Exact connected-series representation of one observable -/

/-- The generic exclusive-root partition coefficient is the concrete
decorated observable coefficient. -/
theorem plaquettePolymerModel_exclusiveRootPartitionCoefficient_eq_decorated
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    (plaquettePolymerModel Λ Φ β).exclusiveRootPartitionCoefficient
        (observableRootDecorationTouches F Λ)
        (fun D => markedSubsetWeight F Λ Φ β D.support) =
      decoratedObservableRootCoefficient F Λ Φ β := by
  unfold Polymer.FinitePolymerModel.exclusiveRootPartitionCoefficient
    decoratedObservableRootCoefficient
  rw [← observableRootDecoratedPairs_eq_exclusiveRootPairs F Λ Φ β]

/-- On the explicit strong-coupling disk, the exact marked numerator is the
vacuum polymer partition function times the absolutely convergent connected
one-root Mayer series. -/
theorem complexObservableNumerator_eq_polymerPartition_mul_tsum_connectedRoot
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    complexObservableNumerator F Λ Φ β =
      (plaquettePolymerModel Λ Φ β).partitionFunction *
        ∑' n : ℕ,
          decoratedObservableRootLinearMayerDegreeSum F Λ Φ β n := by
  have hsummable : Summable (fun n : ℕ =>
      ‖((plaquettePolymerModel Λ Φ β).augmentExclusiveRoots
          (observableRootDecorationTouches F Λ)
          (fun D => markedSubsetWeight F Λ Φ β D.support)).exclusiveRootLinearMayerDegreeSum
        (n + 1)‖) := by
    apply (summable_norm_decoratedObservableRootLinearMayerDegreeSum_succ
      F Λ Φ hβ).congr
    intro n
    rw [decoratedObservableRootLinearMayerDegreeSum_eq_exclusive]
  have hgeneric :=
    (plaquettePolymerModel Λ Φ β).exclusiveRootPartitionCoefficient_eq_partitionFunction_mul_tsum
      (observableRootDecorationTouches F Λ)
      (fun D => markedSubsetWeight F Λ Φ β D.support) hsummable
  rw [plaquettePolymerModel_exclusiveRootPartitionCoefficient_eq_decorated,
    decoratedObservableRootCoefficient_eq_complexObservableNumerator] at hgeneric
  simp_rw [← decoratedObservableRootLinearMayerDegreeSum_eq_exclusive] at hgeneric
  exact hgeneric

/-- Whenever the finite-volume vacuum partition function is nonzero, the
normalized arbitrary-local-observable expectation is exactly its absolutely
convergent connected decorated-root cluster series. -/
theorem complexGibbsExpectation_eq_tsum_connectedDecoratedRoot
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (hZ : complexPartitionFunction Λ Φ β ≠ 0) :
    complexGibbsExpectation F Λ Φ β =
      ∑' n : ℕ,
        decoratedObservableRootLinearMayerDegreeSum F Λ Φ β n := by
  unfold complexGibbsExpectation
  rw [complexObservableNumerator_eq_polymerPartition_mul_tsum_connectedRoot
    F Λ Φ hβ, ← complexPartitionFunction_eq_polymerPartition]
  rw [← mul_assoc, inv_mul_cancel₀ hZ, one_mul]

/-! ## Exact separated and bridge sectors for two observables -/

/-- The first-only canonical components, regarded as a complete decoration
for the first observable. -/
def firstOnlyRootDecorationOfSubset
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) : ObservableRootDecoration F Λ := by
  refine ⟨firstOnlyComponentFamily F H Λ X, ?_, ?_⟩
  · intro γ hγ δ hδ hne
    exact componentFamily_compatible Λ Φ β X
      ((mem_firstOnlyComponentFamily F H Λ X γ).mp hγ).1
      ((mem_firstOnlyComponentFamily F H Λ X δ).mp hδ).1 hne
  · intro γ hγ
    exact ((mem_firstOnlyComponentFamily F H Λ X γ).mp hγ).2.1

/-- The second-only canonical components, regarded as a complete decoration
for the second observable. -/
def secondOnlyRootDecorationOfSubset
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) : ObservableRootDecoration H Λ := by
  refine ⟨secondOnlyComponentFamily F H Λ X, ?_, ?_⟩
  · intro γ hγ δ hδ hne
    exact componentFamily_compatible Λ Φ β X
      ((mem_secondOnlyComponentFamily F H Λ X γ).mp hγ).1
      ((mem_secondOnlyComponentFamily F H Λ X δ).mp hδ).1 hne
  · intro γ hγ
    exact ((mem_secondOnlyComponentFamily F H Λ X γ).mp hγ).2.2

/-- Admissible separated data: a left decoration, a right decoration, and a
compatible bulk family avoiding both.  Cross compatibility forces the left
decoration to avoid the second support and the right decoration to avoid the
first support. -/
def separatedObservableRootTriples
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    Finset ((ObservableRootDecoration F Λ ×
      ObservableRootDecoration H Λ) × Finset (PlaquettePolymer Λ)) := by
  classical
  exact Finset.univ.filter fun triple =>
    (plaquettePolymerModel Λ Φ β).Compatible triple.2 ∧
    ¬observableRootDecorationsCrossIncompatible F H Λ
      triple.1.1 triple.1.2 ∧
    triple.2 ⊆ observableRootDecorationCompatibleBulk F Λ triple.1.1 ∧
    triple.2 ⊆ observableRootDecorationCompatibleBulk H Λ triple.1.2

/-- Canonical separated triple of a plaquette subset. -/
def separatedObservableRootTripleOfSubset
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d)) :=
  ((firstOnlyRootDecorationOfSubset F H Λ Φ β X,
      secondOnlyRootDecorationOfSubset F H Λ Φ β X),
    twoObservableAwayComponentFamily F H Λ X)

/-- The canonical separated triple is admissible when no component already
touches both supports. -/
theorem separatedObservableRootTripleOfSubset_mem
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d))
    (_hjoint : jointlyObservableComponentFamily F H Λ X = ∅) :
    separatedObservableRootTripleOfSubset F H Λ Φ β X ∈
      separatedObservableRootTriples F H Λ Φ β := by
  classical
  rw [separatedObservableRootTriples, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_, ?_⟩
  · intro γ hγ δ hδ hne
    exact componentFamily_compatible Λ Φ β X
      ((mem_twoObservableAwayComponentFamily F H Λ X γ).mp hγ).1
      ((mem_twoObservableAwayComponentFamily F H Λ X δ).mp hδ).1 hne
  · rintro (hleft | hright | hcross)
    · rcases hleft with ⟨γ, hγ, hγH⟩
      exact ((mem_firstOnlyComponentFamily F H Λ X γ).mp hγ).2.2 hγH
    · rcases hright with ⟨δ, hδ, hδF⟩
      exact ((mem_secondOnlyComponentFamily F H Λ X δ).mp hδ).2.1 hδF
    · rcases hcross with ⟨γ, hγ, δ, hδ, hγδ⟩
      have hγdata := (mem_firstOnlyComponentFamily F H Λ X γ).mp hγ
      have hδdata := (mem_secondOnlyComponentFamily F H Λ X δ).mp hδ
      have hne : γ ≠ δ := by
        intro h
        subst δ
        exact hδdata.2.1 hγdata.2.1
      exact componentFamily_compatible Λ Φ β X
        hγdata.1 hδdata.1 hne hγδ
  · intro γ hγ
    rw [observableRootDecorationCompatibleBulk, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rintro (hγF | ⟨δ, hδ, hδγ⟩)
    · exact ((mem_twoObservableAwayComponentFamily F H Λ X γ).mp hγ).2.1 hγF
    · have hδdata := (mem_firstOnlyComponentFamily F H Λ X δ).mp hδ
      have hγdata := (mem_twoObservableAwayComponentFamily F H Λ X γ).mp hγ
      have hne : δ ≠ γ := fun h => by
        subst γ
        exact hγdata.2.1 hδdata.2.1
      exact componentFamily_compatible Λ Φ β X
        hδdata.1 hγdata.1 hne hδγ
  · intro γ hγ
    rw [observableRootDecorationCompatibleBulk, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rintro (hγH | ⟨δ, hδ, hδγ⟩)
    · exact ((mem_twoObservableAwayComponentFamily F H Λ X γ).mp hγ).2.2 hγH
    · have hδdata := (mem_secondOnlyComponentFamily F H Λ X δ).mp hδ
      have hγdata := (mem_twoObservableAwayComponentFamily F H Λ X γ).mp hγ
      have hne : δ ≠ γ := fun h => by
        subst γ
        exact hγdata.2.2 hδdata.2.2
      exact componentFamily_compatible Λ Φ β X
        hδdata.1 hγdata.1 hne hδγ

/-- In the separated sector the supports of the left, right, and away
component families recover the original active subset. -/
theorem separatedComponentSupports_cover
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (X : Finset (Plaquette d)) (hX : X ⊆ Λ.activePlaquettes)
    (hjoint : jointlyObservableComponentFamily F H Λ X = ∅) :
    (polymerFamilySupport Λ (firstOnlyComponentFamily F H Λ X) ∪
      polymerFamilySupport Λ (secondOnlyComponentFamily F H Λ X)) ∪
      polymerFamilySupport Λ (twoObservableAwayComponentFamily F H Λ X) = X := by
  classical
  unfold polymerFamilySupport
  rw [← Finset.union_biUnion, ← Finset.union_biUnion]
  have hpart := twoObservableComponentFamilies_partition F H Λ X
  rw [hjoint] at hpart
  simp only [Finset.union_empty] at hpart
  rw [hpart]
  exact polymerFamilySupport_componentFamily_eq Λ X hX

/-- The canonical separated triple remembers its active plaquette subset. -/
theorem separatedObservableRootTripleOfSubset_injectiveOn
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    {X Y : Finset (Plaquette d)}
    (hX : X ⊆ Λ.activePlaquettes) (hY : Y ⊆ Λ.activePlaquettes)
    (hjointX : jointlyObservableComponentFamily F H Λ X = ∅)
    (hjointY : jointlyObservableComponentFamily F H Λ Y = ∅)
    (heq : separatedObservableRootTripleOfSubset F H Λ Φ β X =
      separatedObservableRootTripleOfSubset F H Λ Φ β Y) :
    X = Y := by
  have hleft : firstOnlyComponentFamily F H Λ X =
      firstOnlyComponentFamily F H Λ Y := by
    have h := congrArg (fun triple => triple.1.1.1) heq
    exact h
  have hright : secondOnlyComponentFamily F H Λ X =
      secondOnlyComponentFamily F H Λ Y := by
    have h := congrArg (fun triple => triple.1.2.1) heq
    exact h
  have haway : twoObservableAwayComponentFamily F H Λ X =
      twoObservableAwayComponentFamily F H Λ Y :=
    congrArg Prod.snd heq
  rw [← separatedComponentSupports_cover F H Λ X hX hjointX,
    ← separatedComponentSupports_cover F H Λ Y hY hjointY,
    hleft, hright, haway]

/-- Every admissible separated triple is the canonical component split of a
unique active plaquette subset with no intrinsically bridging component. -/
theorem separatedObservableRootTripleOfSubset_surjective
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (triple : (ObservableRootDecoration F Λ ×
      ObservableRootDecoration H Λ) × Finset (PlaquettePolymer Λ))
    (htriple : triple ∈ separatedObservableRootTriples F H Λ Φ β) :
    ∃ X ∈ Λ.activePlaquettes.powerset,
      jointlyObservableComponentFamily F H Λ X = ∅ ∧
      separatedObservableRootTripleOfSubset F H Λ Φ β X = triple := by
  classical
  rcases triple with ⟨⟨D, E⟩, Γ⟩
  have hdata := (Finset.mem_filter.mp htriple).2
  rcases hdata with ⟨hΓcompatible, hcross, hΓF, hΓH⟩
  have hDavoidH : ∀ γ ∈ D.1, ¬observableRootTouches H Λ γ := by
    intro γ hγ htouch
    exact hcross (Or.inl ⟨γ, hγ, htouch⟩)
  have hEavoidF : ∀ δ ∈ E.1, ¬observableRootTouches F Λ δ := by
    intro δ hδ htouch
    exact hcross (Or.inr (Or.inl ⟨δ, hδ, htouch⟩))
  have hDEcompatible : ∀ γ ∈ D.1, ∀ δ ∈ E.1,
      ¬plaquettePolymerIncompatible Λ γ δ := by
    intro γ hγ δ hδ hinc
    exact hcross (Or.inr (Or.inr ⟨γ, hγ, δ, hδ, hinc⟩))
  let X := (D.support ∪ E.support) ∪ polymerFamilySupport Λ Γ
  have hXsub : X ⊆ Λ.activePlaquettes := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpDE | hpΓ
    · rcases Finset.mem_union.mp hpDE with hpD | hpE
      · exact polymerFamilySupport_subset_active Λ D.1 hpD
      · exact polymerFamilySupport_subset_active Λ E.1 hpE
    · exact polymerFamilySupport_subset_active Λ Γ hpΓ
  have hcombined : (plaquettePolymerModel Λ Φ β).Compatible
      ((D.1 ∪ E.1) ∪ Γ) := by
    intro γ hγ δ hδ hne
    rcases Finset.mem_union.mp hγ with hγDE | hγΓ
    · rcases Finset.mem_union.mp hγDE with hγD | hγE
      · rcases Finset.mem_union.mp hδ with hδDE | hδΓ
        · rcases Finset.mem_union.mp hδDE with hδD | hδE
          · exact D.2.1 hγD hδD hne
          · exact hDEcompatible γ hγD δ hδE
        · have hallowed := (Finset.mem_filter.mp (hΓF hδΓ)).2
          exact fun hinc => hallowed (Or.inr ⟨γ, hγD, hinc⟩)
      · rcases Finset.mem_union.mp hδ with hδDE | hδΓ
        · rcases Finset.mem_union.mp hδDE with hδD | hδE
          · exact fun hinc => hDEcompatible δ hδD γ hγE
              (plaquettePolymerIncompatible_symmetric Λ hinc)
          · exact E.2.1 hγE hδE hne
        · have hallowed := (Finset.mem_filter.mp (hΓH hδΓ)).2
          exact fun hinc => hallowed (Or.inr ⟨γ, hγE, hinc⟩)
    · rcases Finset.mem_union.mp hδ with hδDE | hδΓ
      · rcases Finset.mem_union.mp hδDE with hδD | hδE
        · have hallowed := (Finset.mem_filter.mp (hΓF hγΓ)).2
          exact fun hinc => hallowed (Or.inr ⟨δ, hδD,
            plaquettePolymerIncompatible_symmetric Λ hinc⟩)
        · have hallowed := (Finset.mem_filter.mp (hΓH hγΓ)).2
          exact fun hinc => hallowed (Or.inr ⟨δ, hδE,
            plaquettePolymerIncompatible_symmetric Λ hinc⟩)
      · exact hΓcompatible hγΓ hδΓ hne
  have hcover : polymerFamilySupport Λ ((D.1 ∪ E.1) ∪ Γ) = X := by
    unfold X ObservableRootDecoration.support polymerFamilySupport
    rw [Finset.union_biUnion, Finset.union_biUnion]
  have hcanonical : (D.1 ∪ E.1) ∪ Γ = componentFamily Λ X :=
    compatibleFamily_eq_componentFamily Λ Φ β ((D.1 ∪ E.1) ∪ Γ) X
      hcombined hcover
  have hfirst : firstOnlyComponentFamily F H Λ X = D.1 := by
    ext γ
    constructor
    · intro hγ
      have hγdata := (mem_firstOnlyComponentFamily F H Λ X γ).mp hγ
      have hγunion : γ ∈ (D.1 ∪ E.1) ∪ Γ := hcanonical ▸ hγdata.1
      rcases Finset.mem_union.mp hγunion with hγDE | hγΓ
      · rcases Finset.mem_union.mp hγDE with hγD | hγE
        · exact hγD
        · exact (hEavoidF γ hγE hγdata.2.1).elim
      · have hallowed := (Finset.mem_filter.mp (hΓF hγΓ)).2
        exact (hallowed (Or.inl hγdata.2.1)).elim
    · intro hγD
      apply (mem_firstOnlyComponentFamily F H Λ X γ).mpr
      exact ⟨hcanonical ▸ Finset.mem_union_left Γ
          (Finset.mem_union_left E.1 hγD),
        D.2.2 γ hγD, hDavoidH γ hγD⟩
  have hsecond : secondOnlyComponentFamily F H Λ X = E.1 := by
    ext γ
    constructor
    · intro hγ
      have hγdata := (mem_secondOnlyComponentFamily F H Λ X γ).mp hγ
      have hγunion : γ ∈ (D.1 ∪ E.1) ∪ Γ := hcanonical ▸ hγdata.1
      rcases Finset.mem_union.mp hγunion with hγDE | hγΓ
      · rcases Finset.mem_union.mp hγDE with hγD | hγE
        · exact (hDavoidH γ hγD hγdata.2.2).elim
        · exact hγE
      · have hallowed := (Finset.mem_filter.mp (hΓH hγΓ)).2
        exact (hallowed (Or.inl hγdata.2.2)).elim
    · intro hγE
      apply (mem_secondOnlyComponentFamily F H Λ X γ).mpr
      exact ⟨hcanonical ▸ Finset.mem_union_left Γ
          (Finset.mem_union_right D.1 hγE),
        hEavoidF γ hγE, E.2.2 γ hγE⟩
  have haway : twoObservableAwayComponentFamily F H Λ X = Γ := by
    ext γ
    constructor
    · intro hγ
      have hγdata := (mem_twoObservableAwayComponentFamily F H Λ X γ).mp hγ
      have hγunion : γ ∈ (D.1 ∪ E.1) ∪ Γ := hcanonical ▸ hγdata.1
      rcases Finset.mem_union.mp hγunion with hγDE | hγΓ
      · rcases Finset.mem_union.mp hγDE with hγD | hγE
        · exact (hγdata.2.1 (D.2.2 γ hγD)).elim
        · exact (hγdata.2.2 (E.2.2 γ hγE)).elim
      · exact hγΓ
    · intro hγΓ
      apply (mem_twoObservableAwayComponentFamily F H Λ X γ).mpr
      have hallowedF := (Finset.mem_filter.mp (hΓF hγΓ)).2
      have hallowedH := (Finset.mem_filter.mp (hΓH hγΓ)).2
      exact ⟨hcanonical ▸ Finset.mem_union_right (D.1 ∪ E.1) hγΓ,
        fun htouch => hallowedF (Or.inl htouch),
        fun htouch => hallowedH (Or.inl htouch)⟩
  have hjoint : jointlyObservableComponentFamily F H Λ X = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨γ, hγ⟩
    have hγdata := (mem_jointlyObservableComponentFamily F H Λ X γ).mp hγ
    have hγunion : γ ∈ (D.1 ∪ E.1) ∪ Γ := hcanonical ▸ hγdata.1
    rcases Finset.mem_union.mp hγunion with hγDE | hγΓ
    · rcases Finset.mem_union.mp hγDE with hγD | hγE
      · exact hDavoidH γ hγD hγdata.2.2
      · exact hEavoidF γ hγE hγdata.2.1
    · have hallowed := (Finset.mem_filter.mp (hΓF hγΓ)).2
      exact hallowed (Or.inl hγdata.2.1)
  refine ⟨X, Finset.mem_powerset.mpr hXsub, hjoint, ?_⟩
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      exact hfirst
    · apply Subtype.ext
      exact hsecond
  · exact haway

/-- Mixed partition coefficient contributed by two compatible one-sided
decorations and a common away family. -/
def separatedObservableRootCoefficient
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) : ℂ :=
  ∑ triple ∈ separatedObservableRootTriples F H Λ Φ β,
    markedSubsetWeight F Λ Φ β triple.1.1.support *
      markedSubsetWeight H Λ Φ β triple.1.2.support *
      (plaquettePolymerModel Λ Φ β).familyWeight triple.2

/-- The separated decorated coefficient is exactly the sum of doubly marked
plaquette subsets having no component which touches both observable
supports. -/
theorem separatedObservableRootCoefficient_eq_sum_no_joint
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (hFH : Disjoint F.support H.support) :
    separatedObservableRootCoefficient F H Λ Φ β =
      ∑ X ∈ Λ.activePlaquettes.powerset.filter
          (fun X => jointlyObservableComponentFamily F H Λ X = ∅),
        markedSubsetWeight (F.mul H) Λ Φ β X := by
  classical
  unfold separatedObservableRootCoefficient
  symm
  apply Finset.sum_bij
    (fun X _ => separatedObservableRootTripleOfSubset F H Λ Φ β X)
  · intro X hX
    have hdata := (Finset.mem_filter.mp hX).2
    exact separatedObservableRootTripleOfSubset_mem F H Λ Φ β X hdata
  · intro X hX Y hY heq
    have hXdata := Finset.mem_filter.mp hX
    have hYdata := Finset.mem_filter.mp hY
    exact separatedObservableRootTripleOfSubset_injectiveOn F H Λ Φ β
      (Finset.mem_powerset.mp hXdata.1) (Finset.mem_powerset.mp hYdata.1)
      hXdata.2 hYdata.2 heq
  · intro triple htriple
    rcases separatedObservableRootTripleOfSubset_surjective
        F H Λ Φ β triple htriple with ⟨X, hX, hjoint, hmap⟩
    exact ⟨X, Finset.mem_filter.mpr ⟨hX, hjoint⟩, hmap⟩
  · intro X hX
    have hdata := Finset.mem_filter.mp hX
    exact markedSubsetWeight_mul_eq_separatedRootComponents F H Λ Φ β X
      (Finset.mem_powerset.mp hdata.1) hFH hdata.2

/-- Admissible bridge-root/bulk-family pairs.  The bridge subtype records
that an absorbed connected component already touches both supports. -/
def bridgeObservableRootPairs
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    Finset (TwoObservableBridgeDecoration F H Λ ×
      Finset (PlaquettePolymer Λ)) := by
  classical
  exact Finset.univ.filter fun pair =>
    (pair.1.1, pair.2) ∈
      observableRootDecoratedPairs (F.mul H) Λ Φ β

/-- Canonical bridge decoration of a subset with a jointly touching
component. -/
def bridgeRootDecorationOfSubset
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d))
    (hjoint : jointlyObservableComponentFamily F H Λ X ≠ ∅) :
    TwoObservableBridgeDecoration F H Λ := by
  refine ⟨observableRootDecorationOfSubset (F.mul H) Λ Φ β X, ?_⟩
  obtain ⟨γ, hγ⟩ := Finset.nonempty_iff_ne_empty.mpr hjoint
  have hγdata := (mem_jointlyObservableComponentFamily F H Λ X γ).mp hγ
  refine ⟨γ, ?_, hγdata.2.1, hγdata.2.2⟩
  apply (mem_observableComponentFamily (F.mul H) Λ X γ).mpr
  exact ⟨hγdata.1, (observableRootTouches_mul_iff F H Λ γ).mpr
    (Or.inl hγdata.2.1)⟩

/-- Canonical bridge-root/bulk-family pair. -/
def bridgeObservableRootPairOfSubset
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d))
    (hjoint : jointlyObservableComponentFamily F H Λ X ≠ ∅) :=
  (bridgeRootDecorationOfSubset F H Λ Φ β X hjoint,
    awayComponentFamily (F.mul H) Λ X)

theorem bridgeObservableRootPairOfSubset_mem
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (X : Finset (Plaquette d))
    (hjoint : jointlyObservableComponentFamily F H Λ X ≠ ∅) :
    bridgeObservableRootPairOfSubset F H Λ Φ β X hjoint ∈
      bridgeObservableRootPairs F H Λ Φ β := by
  classical
  rw [bridgeObservableRootPairs, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  simpa [bridgeObservableRootPairOfSubset, bridgeRootDecorationOfSubset,
    observableRootDecoratedPairOfSubset] using
      observableRootDecoratedPairOfSubset_mem (F.mul H) Λ Φ β X

/-- The canonical bridge pair is injective on active subsets. -/
theorem bridgeObservableRootPairOfSubset_injectiveOn
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    {X Y : Finset (Plaquette d)}
    (hX : X ∈ Λ.activePlaquettes.powerset)
    (hY : Y ∈ Λ.activePlaquettes.powerset)
    (hjointX : jointlyObservableComponentFamily F H Λ X ≠ ∅)
    (hjointY : jointlyObservableComponentFamily F H Λ Y ≠ ∅)
    (heq : bridgeObservableRootPairOfSubset F H Λ Φ β X hjointX =
      bridgeObservableRootPairOfSubset F H Λ Φ β Y hjointY) :
    X = Y := by
  have heq' : observableRootDecoratedPairOfSubset (F.mul H) Λ Φ β X =
      observableRootDecoratedPairOfSubset (F.mul H) Λ Φ β Y := by
    apply Prod.ext
    · have h := congrArg (fun pair => pair.1.1) heq
      simpa [bridgeObservableRootPairOfSubset, bridgeRootDecorationOfSubset,
        observableRootDecoratedPairOfSubset] using h
    · change awayComponentFamily (F.mul H) Λ X =
        awayComponentFamily (F.mul H) Λ Y
      have h := congrArg Prod.snd heq
      exact h
  apply observableRootDecoratedPairOfSubset_injectiveOn (F.mul H) Λ Φ β
    hX hY heq'

/-- Every admissible bridge pair is canonical for a unique active subset
whose component split has a nonempty jointly-touching class. -/
theorem bridgeObservableRootPairOfSubset_surjective
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (pair : TwoObservableBridgeDecoration F H Λ ×
      Finset (PlaquettePolymer Λ))
    (hpair : pair ∈ bridgeObservableRootPairs F H Λ Φ β) :
    ∃ (X : Finset (Plaquette d))
        (_hX : X ∈ Λ.activePlaquettes.powerset)
        (hjoint : jointlyObservableComponentFamily F H Λ X ≠ ∅),
      bridgeObservableRootPairOfSubset F H Λ Φ β X hjoint = pair := by
  classical
  rcases pair with ⟨D, Γ⟩
  have hdecorated : (D.1, Γ) ∈
      observableRootDecoratedPairs (F.mul H) Λ Φ β :=
    (Finset.mem_filter.mp hpair).2
  rcases observableRootDecoratedPairOfSubset_surjective
      (F.mul H) Λ Φ β (D.1, Γ) hdecorated with ⟨X, hX, hmap⟩
  have hroot : observableComponentFamily (F.mul H) Λ X = D.1.1 := by
    have h := congrArg (fun pair => pair.1.1) hmap
    exact h
  obtain ⟨γ, hγD, hγF, hγH⟩ := D.2
  have hγcomponent : γ ∈ componentFamily Λ X :=
    ((mem_observableComponentFamily (F.mul H) Λ X γ).mp
      (hroot.symm ▸ hγD)).1
  have hγjoint : γ ∈ jointlyObservableComponentFamily F H Λ X :=
    (mem_jointlyObservableComponentFamily F H Λ X γ).mpr
      ⟨hγcomponent, hγF, hγH⟩
  have hjoint : jointlyObservableComponentFamily F H Λ X ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨γ, hγjoint⟩
  have haway : awayComponentFamily (F.mul H) Λ X = Γ :=
    congrArg Prod.snd hmap
  refine ⟨X, hX, hjoint, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    have h := congrArg Prod.fst hmap
    exact h
  · exact haway

/-- Mixed partition coefficient carried by intrinsic bridge roots. -/
def bridgeObservableRootCoefficient
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) : ℂ :=
  ∑ pair ∈ bridgeObservableRootPairs F H Λ Φ β,
    markedSubsetWeight (F.mul H) Λ Φ β pair.1.support *
      (plaquettePolymerModel Λ Φ β).familyWeight pair.2

/-- The bridge coefficient is exactly the complementary sum of doubly
marked subsets with a jointly-touching connected component. -/
theorem bridgeObservableRootCoefficient_eq_sum_joint
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    bridgeObservableRootCoefficient F H Λ Φ β =
      ∑ X ∈ Λ.activePlaquettes.powerset.filter
          (fun X => jointlyObservableComponentFamily F H Λ X ≠ ∅),
        markedSubsetWeight (F.mul H) Λ Φ β X := by
  classical
  unfold bridgeObservableRootCoefficient
  symm
  apply Finset.sum_bij
    (fun X hX => bridgeObservableRootPairOfSubset F H Λ Φ β X
      (Finset.mem_filter.mp hX).2)
  · intro X hX
    exact bridgeObservableRootPairOfSubset_mem F H Λ Φ β X
      (Finset.mem_filter.mp hX).2
  · intro X hX Y hY heq
    exact bridgeObservableRootPairOfSubset_injectiveOn F H Λ Φ β
      (Finset.mem_filter.mp hX).1 (Finset.mem_filter.mp hY).1
      (Finset.mem_filter.mp hX).2 (Finset.mem_filter.mp hY).2 heq
  · intro pair hpair
    rcases bridgeObservableRootPairOfSubset_surjective
        F H Λ Φ β pair hpair with ⟨X, hX, hjoint, hmap⟩
    exact ⟨X, Finset.mem_filter.mpr ⟨hX, hjoint⟩, hmap⟩
  · intro X hX
    exact markedSubsetWeight_eq_rootComponentWeight_mul_awayFamilyWeight
      (F.mul H) Λ Φ β X (Finset.mem_powerset.mp (Finset.mem_filter.mp hX).1)

/-- Exact mixed-sector exhaustion: separated two-root configurations and
intrinsic bridge-root configurations partition the product-observable
numerator. -/
theorem separated_add_bridge_eq_complexObservableNumerator
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (hFH : Disjoint F.support H.support) :
    separatedObservableRootCoefficient F H Λ Φ β +
        bridgeObservableRootCoefficient F H Λ Φ β =
      complexObservableNumerator (F.mul H) Λ Φ β := by
  rw [separatedObservableRootCoefficient_eq_sum_no_joint F H Λ Φ β hFH,
    bridgeObservableRootCoefficient_eq_sum_joint,
    complexObservableNumerator_eq_sum_markedSubsetWeight]
  exact Finset.sum_filter_add_sum_filter_not
    Λ.activePlaquettes.powerset
    (fun X => jointlyObservableComponentFamily F H Λ X = ∅)
    (fun X => markedSubsetWeight (F.mul H) Λ Φ β X)

/-! ### Matching the exact sectors with the nested augmented gas -/

/-- Indices for the second one-sided augmentation: either no left root is
present (an ordinary `H` decorated pair), or one compatible left root is
present (a separated triple). -/
def rightStageDecoratedIndices
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :=
  (observableRootDecoratedPairs H Λ Φ β).disjSum
    (separatedObservableRootTriples F H Λ Φ β)

/-- Encode a right-stage index as a right root together with an admissible
family of the already left-augmented gas. -/
def rightStagePairOfIndex
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (_Φ : RealPlaquettePotential G) (_β : ℂ) :
    (ObservableRootDecoration H Λ × Finset (PlaquettePolymer Λ)) ⊕
      ((ObservableRootDecoration F Λ × ObservableRootDecoration H Λ) ×
        Finset (PlaquettePolymer Λ)) →
      ObservableRootDecoration H Λ ×
        Finset (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)
  | Sum.inl pair => (pair.1, pair.2.disjSum ∅)
  | Sum.inr triple => (triple.1.2, triple.2.disjSum {triple.1.1})

/-- Every encoded right-stage index is an admissible exclusive-root pair. -/
theorem rightStagePairOfIndex_mem
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ)
    (index : (ObservableRootDecoration H Λ × Finset (PlaquettePolymer Λ)) ⊕
      ((ObservableRootDecoration F Λ × ObservableRootDecoration H Λ) ×
        Finset (PlaquettePolymer Λ)))
    (hindex : index ∈ rightStageDecoratedIndices F H Λ Φ β) :
    rightStagePairOfIndex F H Λ Φ β index ∈
      (decoratedObservableRootModel F Λ Φ β α).exclusiveRootPairs
        (Polymer.FinitePolymerModel.twoColorRightTouches
          (observableRootDecorationTouches H Λ)
          (observableRootDecorationsCrossIncompatible F H Λ)) := by
  classical
  rcases index with pair | triple
  · have hpair : pair ∈ observableRootDecoratedPairs H Λ Φ β := by
      simpa [rightStageDecoratedIndices] using hindex
    rcases pair with ⟨E, Γ⟩
    have hdata := (Finset.mem_filter.mp hpair).2
    rw [Polymer.FinitePolymerModel.exclusiveRootPairs, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · apply ((plaquettePolymerModel Λ Φ β).augmentExclusiveRoots_compatible_disjSum_iff
        (observableRootDecorationTouches F Λ)
        (fun D => α * markedSubsetWeight F Λ Φ β D.support) Γ ∅).mpr
      exact ⟨hdata.1, by simp, by simp⟩
    · intro x hx
      rcases x with γ | D
      · have hγ : γ ∈ Γ := by
          simpa only [rightStagePairOfIndex, Finset.inl_mem_disjSum] using hx
        exact (Finset.mem_filter.mp (hdata.2 hγ)).2
      · simp only [rightStagePairOfIndex, Finset.inr_mem_disjSum,
          Finset.notMem_empty] at hx
  · have htriple : triple ∈ separatedObservableRootTriples F H Λ Φ β := by
      simpa [rightStageDecoratedIndices] using hindex
    rcases triple with ⟨⟨D, E⟩, Γ⟩
    have hdata := (Finset.mem_filter.mp htriple).2
    rw [Polymer.FinitePolymerModel.exclusiveRootPairs, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · apply ((plaquettePolymerModel Λ Φ β).augmentExclusiveRoots_compatible_disjSum_iff
        (observableRootDecorationTouches F Λ)
        (fun D => α * markedSubsetWeight F Λ Φ β D.support) Γ {D}).mpr
      refine ⟨hdata.1, by simp, ?_⟩
      intro D' hD' γ hγ
      have hD'eq : D' = D := by simpa using hD'
      subst D'
      exact (Finset.mem_filter.mp (hdata.2.2.1 hγ)).2
    · intro x hx
      rcases x with γ | D'
      · have hγ : γ ∈ Γ := by
          simpa only [rightStagePairOfIndex, Finset.inl_mem_disjSum] using hx
        exact (Finset.mem_filter.mp (hdata.2.2.2 hγ)).2
      · have hD'eq : D' = D := by
          simpa only [rightStagePairOfIndex, Finset.inr_mem_disjSum,
            Finset.mem_singleton] using hx
        subst D'
        exact hdata.2.1

theorem rightStagePairOfIndex_injectiveOn
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    Set.InjOn (rightStagePairOfIndex F H Λ Φ β)
      (rightStageDecoratedIndices F H Λ Φ β : Set _) := by
  classical
  intro i _hi j _hj hij
  rcases i with pair | triple <;> rcases j with other | otherTriple
  · rcases pair with ⟨E, Γ⟩
    rcases other with ⟨E', Γ'⟩
    have hroot : E = E' := congrArg Prod.fst hij
    have hfamily : Γ.disjSum (∅ : Finset (ObservableRootDecoration F Λ)) =
        Γ'.disjSum ∅ := congrArg Prod.snd hij
    have hΓ : Γ = Γ' := (Finset.disjSum_inj.mp hfamily).1
    subst E'
    subst Γ'
    rfl
  · rcases pair with ⟨E, Γ⟩
    rcases otherTriple with ⟨⟨D', E'⟩, Γ'⟩
    have hfamily : Γ.disjSum (∅ : Finset (ObservableRootDecoration F Λ)) =
        Γ'.disjSum {D'} := congrArg Prod.snd hij
    have hright := (Finset.disjSum_inj.mp hfamily).2
    simp at hright
  · rcases triple with ⟨⟨D, E⟩, Γ⟩
    rcases other with ⟨E', Γ'⟩
    have hfamily : Γ.disjSum {D} =
        Γ'.disjSum (∅ : Finset (ObservableRootDecoration F Λ)) :=
      congrArg Prod.snd hij
    have hright := (Finset.disjSum_inj.mp hfamily).2
    simp at hright
  · rcases triple with ⟨⟨D, E⟩, Γ⟩
    rcases otherTriple with ⟨⟨D', E'⟩, Γ'⟩
    have hroot : E = E' := congrArg Prod.fst hij
    have hfamily : Γ.disjSum {D} = Γ'.disjSum {D'} := congrArg Prod.snd hij
    have hparts := Finset.disjSum_inj.mp hfamily
    have hD : D = D' := by
      simpa using hparts.2
    have hΓ : Γ = Γ' := hparts.1
    subst D'
    subst E'
    subst Γ'
    rfl

theorem rightStagePairOfIndex_surjective
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ)
    (pair : ObservableRootDecoration H Λ ×
      Finset (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ))
    (hpair : pair ∈
      (decoratedObservableRootModel F Λ Φ β α).exclusiveRootPairs
        (Polymer.FinitePolymerModel.twoColorRightTouches
          (observableRootDecorationTouches H Λ)
          (observableRootDecorationsCrossIncompatible F H Λ))) :
    ∃ index ∈ rightStageDecoratedIndices F H Λ Φ β,
      rightStagePairOfIndex F H Λ Φ β index = pair := by
  classical
  rcases pair with ⟨E, Ξ⟩
  have hdata := (Finset.mem_filter.mp hpair).2
  let Γ := Ξ.toLeft
  let Δ := Ξ.toRight
  have hsplit : Ξ = Γ.disjSum Δ := by
    exact (Finset.toLeft_disjSum_toRight (u := Ξ)).symm
  have hcompatibleSplit :
      (decoratedObservableRootModel F Λ Φ β α).Compatible
        (Γ.disjSum Δ) := hsplit ▸ hdata.1
  have hleftData :=
    ((plaquettePolymerModel Λ Φ β).augmentExclusiveRoots_compatible_disjSum_iff
      (observableRootDecorationTouches F Λ)
      (fun D => α * markedSubsetWeight F Λ Φ β D.support) Γ Δ).mp
      hcompatibleSplit
  by_cases hΔempty : Δ = ∅
  · have hHpair : (E, Γ) ∈ observableRootDecoratedPairs H Λ Φ β := by
      rw [observableRootDecoratedPairs, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hleftData.1, ?_⟩
      intro γ hγ
      rw [observableRootDecorationCompatibleBulk, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hallowed := hdata.2 (Sum.inl γ) (by
        rw [hsplit, hΔempty]
        exact Finset.inl_mem_disjSum.mpr hγ)
      exact hallowed
    let index :
        (ObservableRootDecoration H Λ × Finset (PlaquettePolymer Λ)) ⊕
          ((ObservableRootDecoration F Λ × ObservableRootDecoration H Λ) ×
            Finset (PlaquettePolymer Λ)) := Sum.inl (E, Γ)
    refine ⟨index, ?_, ?_⟩
    · simpa [index, rightStageDecoratedIndices] using hHpair
    · apply Prod.ext
      · rfl
      · simp only [index, rightStagePairOfIndex]
        rw [← hΔempty, ← hsplit]
  · obtain ⟨D, hD⟩ := Finset.nonempty_iff_ne_empty.mpr hΔempty
    have hΔsingle : Δ = {D} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hD, fun D' hD' => (Finset.card_le_one.mp hleftData.2.1) D' hD' D hD⟩
    have hcross : ¬observableRootDecorationsCrossIncompatible F H Λ D E := by
      have hallowed := hdata.2 (Sum.inr D) (by
        rw [hsplit]
        exact Finset.inr_mem_disjSum.mpr hD)
      exact hallowed
    have htriple : ((D, E), Γ) ∈
        separatedObservableRootTriples F H Λ Φ β := by
      rw [separatedObservableRootTriples, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hleftData.1, hcross, ?_, ?_⟩
      · intro γ hγ
        rw [observableRootDecorationCompatibleBulk, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hleftData.2.2 D (hΔsingle ▸ Finset.mem_singleton_self D)
          γ hγ⟩
      · intro γ hγ
        rw [observableRootDecorationCompatibleBulk, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        exact hdata.2 (Sum.inl γ) (by
          rw [hsplit]
          exact Finset.inl_mem_disjSum.mpr hγ)
    let index :
        (ObservableRootDecoration H Λ × Finset (PlaquettePolymer Λ)) ⊕
          ((ObservableRootDecoration F Λ × ObservableRootDecoration H Λ) ×
            Finset (PlaquettePolymer Λ)) := Sum.inr ((D, E), Γ)
    refine ⟨index, ?_, ?_⟩
    · simpa [index, rightStageDecoratedIndices] using htriple
    · apply Prod.ext
      · rfl
      · simp only [index, rightStagePairOfIndex]
        rw [← hΔsingle, ← hsplit]

/-- The second exclusive-root stage consists exactly of the ordinary
`H` numerator sector plus the separated mixed sector. -/
theorem rightStageExclusiveRootSum_eq
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) :
    (∑ pair ∈
        (decoratedObservableRootModel F Λ Φ β α).exclusiveRootPairs
          (Polymer.FinitePolymerModel.twoColorRightTouches
            (observableRootDecorationTouches H Λ)
            (observableRootDecorationsCrossIncompatible F H Λ)),
      (θ * markedSubsetWeight H Λ Φ β pair.1.support) *
        (decoratedObservableRootModel F Λ Φ β α).familyWeight pair.2) =
      θ * complexObservableNumerator H Λ Φ β +
        α * θ * separatedObservableRootCoefficient F H Λ Φ β := by
  classical
  let indexWeight :
      (ObservableRootDecoration H Λ × Finset (PlaquettePolymer Λ)) ⊕
        ((ObservableRootDecoration F Λ × ObservableRootDecoration H Λ) ×
          Finset (PlaquettePolymer Λ)) → ℂ
    | Sum.inl pair =>
        θ * markedSubsetWeight H Λ Φ β pair.1.support *
          (plaquettePolymerModel Λ Φ β).familyWeight pair.2
    | Sum.inr triple =>
        α * θ *
          (markedSubsetWeight F Λ Φ β triple.1.1.support *
            markedSubsetWeight H Λ Φ β triple.1.2.support *
            (plaquettePolymerModel Λ Φ β).familyWeight triple.2)
  have hsum :
      (∑ pair ∈
          (decoratedObservableRootModel F Λ Φ β α).exclusiveRootPairs
            (Polymer.FinitePolymerModel.twoColorRightTouches
              (observableRootDecorationTouches H Λ)
              (observableRootDecorationsCrossIncompatible F H Λ)),
        (θ * markedSubsetWeight H Λ Φ β pair.1.support) *
          (decoratedObservableRootModel F Λ Φ β α).familyWeight pair.2) =
        ∑ index ∈ rightStageDecoratedIndices F H Λ Φ β,
          indexWeight index := by
    symm
    apply Finset.sum_bij (fun index _ =>
      rightStagePairOfIndex F H Λ Φ β index)
    · exact fun index hindex =>
        rightStagePairOfIndex_mem F H Λ Φ β α index hindex
    · intro i hi j hj hij
      exact rightStagePairOfIndex_injectiveOn F H Λ Φ β hi hj hij
    · intro pair hpair
      rcases rightStagePairOfIndex_surjective F H Λ Φ β α pair hpair with
        ⟨index, hindex, hmap⟩
      exact ⟨index, hindex, hmap⟩
    · intro index hindex
      rcases index with pair | triple
      · rcases pair with ⟨E, Γ⟩
        simp only [indexWeight, rightStagePairOfIndex]
        simp only [decoratedObservableRootModel]
        rw [(plaquettePolymerModel Λ Φ β).augmentExclusiveRoots_familyWeight_disjSum
          (observableRootDecorationTouches F Λ)
          (fun D => α * markedSubsetWeight F Λ Φ β D.support) Γ ∅]
        simp
      · rcases triple with ⟨⟨D, E⟩, Γ⟩
        simp only [indexWeight, rightStagePairOfIndex]
        simp only [decoratedObservableRootModel]
        rw [(plaquettePolymerModel Λ Φ β).augmentExclusiveRoots_familyWeight_disjSum
          (observableRootDecorationTouches F Λ)
          (fun D => α * markedSubsetWeight F Λ Φ β D.support) Γ {D}]
        simp only [Finset.prod_singleton]
        ring
  rw [hsum]
  unfold rightStageDecoratedIndices
  rw [Finset.sum_disjSum]
  simp only [indexWeight]
  rw [← decoratedObservableRootCoefficient_eq_complexObservableNumerator H Λ Φ β]
  unfold decoratedObservableRootCoefficient separatedObservableRootCoefficient
  rw [Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (fun x y : ℂ => x + y)
  · apply Finset.sum_congr rfl
    intro pair _
    ring
  · apply Finset.sum_congr rfl
    intro triple _
    ring

/-- Encode an intrinsic bridge pair as a bridge-stage exclusive-root pair;
the intermediate one-sided root families are both empty. -/
def bridgeStagePairOfPair
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (_Φ : RealPlaquettePotential G) (_β : ℂ) :
    TwoObservableBridgeDecoration F H Λ × Finset (PlaquettePolymer Λ) →
      TwoObservableBridgeDecoration F H Λ ×
        Finset ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
          ObservableRootDecoration H Λ)
  | pair => (pair.1,
      (pair.2.disjSum (∅ : Finset (ObservableRootDecoration F Λ))).disjSum
        (∅ : Finset (ObservableRootDecoration H Λ)))

theorem bridgeStagePairOfPair_mem
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ)
    (pair : TwoObservableBridgeDecoration F H Λ ×
      Finset (PlaquettePolymer Λ))
    (hpair : pair ∈ bridgeObservableRootPairs F H Λ Φ β) :
    bridgeStagePairOfPair F H Λ Φ β pair ∈
      ((decoratedObservableRootModel F Λ Φ β α).augmentExclusiveRoots
        (Polymer.FinitePolymerModel.twoColorRightTouches
          (observableRootDecorationTouches H Λ)
          (observableRootDecorationsCrossIncompatible F H Λ))
        (fun E => θ * markedSubsetWeight H Λ Φ β E.support)).exclusiveRootPairs
          (Polymer.FinitePolymerModel.bivariateBridgeTouches
            (fun D γ => observableRootDecorationTouches (F.mul H) Λ D.1 γ)) := by
  classical
  rcases pair with ⟨D, Γ⟩
  have hdecorated : (D.1, Γ) ∈
      observableRootDecoratedPairs (F.mul H) Λ Φ β :=
    (Finset.mem_filter.mp hpair).2
  have hdata := (Finset.mem_filter.mp hdecorated).2
  rw [Polymer.FinitePolymerModel.exclusiveRootPairs, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · apply ((decoratedObservableRootModel F Λ Φ β α).augmentExclusiveRoots_compatible_disjSum_iff
      (Polymer.FinitePolymerModel.twoColorRightTouches
        (observableRootDecorationTouches H Λ)
        (observableRootDecorationsCrossIncompatible F H Λ))
      (fun E => θ * markedSubsetWeight H Λ Φ β E.support)
      (Γ.disjSum ∅) ∅).mpr
    refine ⟨?_, by simp, by simp⟩
    apply ((plaquettePolymerModel Λ Φ β).augmentExclusiveRoots_compatible_disjSum_iff
      (observableRootDecorationTouches F Λ)
      (fun D => α * markedSubsetWeight F Λ Φ β D.support) Γ ∅).mpr
    exact ⟨hdata.1, by simp, by simp⟩
  · intro x hx
    rcases x with x | E
    · rcases x with γ | D'
      · have hγ : γ ∈ Γ := by
          simpa only [bridgeStagePairOfPair, Finset.inl_mem_disjSum] using hx
        exact (Finset.mem_filter.mp (hdata.2 hγ)).2
      · have : D' ∈ (∅ : Finset (ObservableRootDecoration F Λ)) := by
          simpa only [bridgeStagePairOfPair, Finset.inl_mem_disjSum,
            Finset.inr_mem_disjSum] using hx
        simp at this
    · have : E ∈ (∅ : Finset (ObservableRootDecoration H Λ)) := by
        simpa only [bridgeStagePairOfPair, Finset.inr_mem_disjSum] using hx
      simp at this

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [GaugeHaarProbability G] in
theorem bridgeStagePairOfPair_injective
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    Function.Injective (bridgeStagePairOfPair F H Λ Φ β) := by
  classical
  rintro ⟨D, Γ⟩ ⟨E, Δ⟩ heq
  have hroot : D = E := congrArg Prod.fst heq
  have hfamily := congrArg Prod.snd heq
  have houter := (Finset.disjSum_inj.mp hfamily).1
  have hinner : Γ = Δ := (Finset.disjSum_inj.mp houter).1
  subst E
  subst Δ
  rfl

theorem bridgeStagePairOfPair_surjective
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ)
    (pair : TwoObservableBridgeDecoration F H Λ ×
      Finset ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration H Λ))
    (hpair : pair ∈
      ((decoratedObservableRootModel F Λ Φ β α).augmentExclusiveRoots
        (Polymer.FinitePolymerModel.twoColorRightTouches
          (observableRootDecorationTouches H Λ)
          (observableRootDecorationsCrossIncompatible F H Λ))
        (fun E => θ * markedSubsetWeight H Λ Φ β E.support)).exclusiveRootPairs
          (Polymer.FinitePolymerModel.bivariateBridgeTouches
            (fun D γ => observableRootDecorationTouches (F.mul H) Λ D.1 γ))) :
    ∃ bridgePair ∈ bridgeObservableRootPairs F H Λ Φ β,
      bridgeStagePairOfPair F H Λ Φ β bridgePair = pair := by
  classical
  rcases pair with ⟨D, Ξ⟩
  have hdata := (Finset.mem_filter.mp hpair).2
  let ΞL := Ξ.toLeft
  let ΔH := Ξ.toRight
  have hsplitH : Ξ = ΞL.disjSum ΔH :=
    (Finset.toLeft_disjSum_toRight (u := Ξ)).symm
  have hΔHempty : ΔH = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨E, hE⟩
    exact hdata.2 (Sum.inr E) (hsplitH ▸ Finset.inr_mem_disjSum.mpr hE) trivial
  let Γ := ΞL.toLeft
  let ΔF := ΞL.toRight
  have hsplitF : ΞL = Γ.disjSum ΔF :=
    (Finset.toLeft_disjSum_toRight (u := ΞL)).symm
  have hΔFempty : ΔF = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨D', hD'⟩
    exact hdata.2 (Sum.inl (Sum.inr D')) (by
      rw [hsplitH, hΔHempty, hsplitF]
      exact Finset.inl_mem_disjSum.mpr (Finset.inr_mem_disjSum.mpr hD')) trivial
  have hcompatibleH :
      (decoratedObservableRootModel F Λ Φ β α).Compatible ΞL := by
    have hsplitCompatible := hsplitH ▸ hdata.1
    exact (((decoratedObservableRootModel F Λ Φ β α).augmentExclusiveRoots_compatible_disjSum_iff
      (Polymer.FinitePolymerModel.twoColorRightTouches
        (observableRootDecorationTouches H Λ)
        (observableRootDecorationsCrossIncompatible F H Λ))
      (fun E => θ * markedSubsetWeight H Λ Φ β E.support) ΞL ΔH).mp
      hsplitCompatible).1
  have hcompatibleF : (plaquettePolymerModel Λ Φ β).Compatible Γ := by
    have hsplitCompatible := hsplitF ▸ hcompatibleH
    exact (((plaquettePolymerModel Λ Φ β).augmentExclusiveRoots_compatible_disjSum_iff
      (observableRootDecorationTouches F Λ)
      (fun D => α * markedSubsetWeight F Λ Φ β D.support) Γ ΔF).mp
      hsplitCompatible).1
  have hbridgePair : (D, Γ) ∈ bridgeObservableRootPairs F H Λ Φ β := by
    rw [bridgeObservableRootPairs, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [observableRootDecoratedPairs, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hcompatibleF, ?_⟩
    intro γ hγ
    rw [observableRootDecorationCompatibleBulk, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact hdata.2 (Sum.inl (Sum.inl γ)) (by
      rw [hsplitH, hΔHempty, hsplitF]
      exact Finset.inl_mem_disjSum.mpr (Finset.inl_mem_disjSum.mpr hγ))
  refine ⟨(D, Γ), hbridgePair, ?_⟩
  apply Prod.ext
  · rfl
  · simp only [bridgeStagePairOfPair]
    rw [← hΔFempty, ← hsplitF, ← hΔHempty, ← hsplitH]

/-- The final exclusive bridge stage is exactly the intrinsic bridge
coefficient, with its bilinear source factor. -/
theorem bridgeStageExclusiveRootSum_eq
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) :
    (∑ pair ∈
        ((decoratedObservableRootModel F Λ Φ β α).augmentExclusiveRoots
          (Polymer.FinitePolymerModel.twoColorRightTouches
            (observableRootDecorationTouches H Λ)
            (observableRootDecorationsCrossIncompatible F H Λ))
          (fun E => θ * markedSubsetWeight H Λ Φ β E.support)).exclusiveRootPairs
            (Polymer.FinitePolymerModel.bivariateBridgeTouches
              (fun (D : TwoObservableBridgeDecoration F H Λ)
                (γ : PlaquettePolymer Λ) =>
                observableRootDecorationTouches (F.mul H) Λ D.1 γ)),
      (α * θ * markedSubsetWeight (F.mul H) Λ Φ β pair.1.support) *
        ((decoratedObservableRootModel F Λ Φ β α).augmentExclusiveRoots
          (Polymer.FinitePolymerModel.twoColorRightTouches
            (observableRootDecorationTouches H Λ)
            (observableRootDecorationsCrossIncompatible F H Λ))
          (fun E => θ * markedSubsetWeight H Λ Φ β E.support)).familyWeight
            pair.2) =
      α * θ * bridgeObservableRootCoefficient F H Λ Φ β := by
  classical
  calc
    _ = ∑ pair ∈ bridgeObservableRootPairs F H Λ Φ β,
        α * θ *
          (markedSubsetWeight (F.mul H) Λ Φ β pair.1.support *
            (plaquettePolymerModel Λ Φ β).familyWeight pair.2) := by
      symm
      apply Finset.sum_bij (fun pair _ => bridgeStagePairOfPair F H Λ Φ β pair)
      · exact fun pair hpair =>
          bridgeStagePairOfPair_mem F H Λ Φ β α θ pair hpair
      · intro pair hpair other hother heq
        exact bridgeStagePairOfPair_injective F H Λ Φ β heq
      · intro pair hpair
        rcases bridgeStagePairOfPair_surjective
            F H Λ Φ β α θ pair hpair with ⟨source, hsource, hmap⟩
        exact ⟨source, hsource, hmap⟩
      · intro pair hpair
        rcases pair with ⟨D, Γ⟩
        simp only [bridgeStagePairOfPair]
        rw [(decoratedObservableRootModel F Λ Φ β α).augmentExclusiveRoots_familyWeight_disjSum
          (Polymer.FinitePolymerModel.twoColorRightTouches
            (observableRootDecorationTouches H Λ)
            (observableRootDecorationsCrossIncompatible F H Λ))
          (fun E => θ * markedSubsetWeight H Λ Φ β E.support)
          (Γ.disjSum ∅) ∅]
        simp only [Finset.prod_empty, mul_one]
        simp only [decoratedObservableRootModel]
        rw [(plaquettePolymerModel Λ Φ β).augmentExclusiveRoots_familyWeight_disjSum
          (observableRootDecorationTouches F Λ)
          (fun D => α * markedSubsetWeight F Λ Φ β D.support) Γ ∅]
        simp
        ring
    _ = _ := by
      unfold bridgeObservableRootCoefficient
      rw [Finset.mul_sum]

/-- The full bivariate decorated gas is exactly the physical two-observable
source partition.  Its mixed compatible-family coefficient is the proved
sum of the separated and intrinsic-bridge sectors. -/
theorem bivariateDecoratedObservableRootModel_partitionFunction
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ)
    (hFH : Disjoint F.support H.support) :
    (bivariateDecoratedObservableRootModel F H Λ Φ β α θ).partitionFunction =
      twoObservableSourcePartition F H Λ Φ β α θ := by
  unfold bivariateDecoratedObservableRootModel
    Polymer.FinitePolymerModel.augmentBivariateExclusiveRoots
    Polymer.FinitePolymerModel.augmentTwoColorExclusiveRoots
  rw [Polymer.FinitePolymerModel.augmentExclusiveRoots_partitionFunction]
  rw [Polymer.FinitePolymerModel.augmentExclusiveRoots_partitionFunction]
  have hleft :=
    decoratedObservableRootModel_partitionFunction_eq_oneObservableSourcePartition
      F Λ Φ β α
  simp only [decoratedObservableRootModel] at hleft
  rw [hleft]
  have hright := rightStageExclusiveRootSum_eq F H Λ Φ β α θ
  simp only [decoratedObservableRootModel] at hright
  rw [hright]
  have hbridge := bridgeStageExclusiveRootSum_eq F H Λ Φ β α θ
  simp only [decoratedObservableRootModel] at hbridge
  rw [hbridge]
  rw [oneObservableSourcePartition]
  unfold twoObservableSourcePartition
  rw [← separated_add_bridge_eq_complexObservableNumerator F H Λ Φ β hFH]
  ring

/-- The finite total source polynomial of the decorated bivariate gas is
literally the physical two-observable source polynomial. -/
theorem bivariateDecoratedObservableRoot_totalPartitionPolynomial
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (hFH : Disjoint F.support H.support) :
    (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).bigradedTotalPartitionPolynomial
          (bivariateDecoratedObservableRootGrading F H Λ) =
      MvPolynomial.C (complexPartitionFunction Λ Φ β) +
        MvPolynomial.X 0 *
          MvPolynomial.C (complexObservableNumerator F Λ Φ β) +
        MvPolynomial.X 1 *
          MvPolynomial.C (complexObservableNumerator H Λ Φ β) +
        MvPolynomial.X 0 * MvPolynomial.X 1 *
          MvPolynomial.C
            (complexObservableNumerator (F.mul H) Λ Φ β) := by
  apply MvPolynomial.funext
  intro alpha
  have halpha :
      alpha = bivariateObservableSourceValues (alpha 0) (alpha 1) := by
    funext i
    fin_cases i <;> simp [bivariateObservableSourceValues]
  rw [Polymer.FinitePolymerModel.eval_bigradedTotalPartitionPolynomial]
  rw [halpha,
    bivariateDecoratedObservableRootModel_scaled_partitionFunction,
    bivariateDecoratedObservableRootModel_partitionFunction F H Λ Φ β
      (alpha 0) (alpha 1) hFH]
  simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  unfold twoObservableSourcePartition
  simp [bivariateObservableSourceValues]

theorem bivariateDecoratedObservableRoot_vacuumPartitionCoefficient
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (hFH : Disjoint F.support H.support) :
    (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).bigradedVacuumPartitionCoefficient
          (bivariateDecoratedObservableRootGrading F H Λ) =
      complexPartitionFunction Λ Φ β := by
  have h := congrArg MvPolynomial.constantCoeff
    (bivariateDecoratedObservableRoot_totalPartitionPolynomial
      F H Λ Φ β hFH)
  simpa [Polymer.FinitePolymerModel.bigradedVacuumPartitionCoefficient] using h

theorem bivariateDecoratedObservableRoot_firstPartitionCoefficient
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (hFH : Disjoint F.support H.support) :
    (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).bigradedFirstPartitionCoefficient
          (bivariateDecoratedObservableRootGrading F H Λ) =
      complexObservableNumerator F Λ Φ β := by
  have h := congrArg (fun p => MvPolynomial.constantCoeff
    (MvPolynomial.pderiv (0 : Fin 2) p))
      (bivariateDecoratedObservableRoot_totalPartitionPolynomial
        F H Λ Φ β hFH)
  simpa [Polymer.FinitePolymerModel.bigradedFirstPartitionCoefficient] using h

theorem bivariateDecoratedObservableRoot_secondPartitionCoefficient
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (hFH : Disjoint F.support H.support) :
    (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).bigradedSecondPartitionCoefficient
          (bivariateDecoratedObservableRootGrading F H Λ) =
      complexObservableNumerator H Λ Φ β := by
  have h := congrArg (fun p => MvPolynomial.constantCoeff
    (MvPolynomial.pderiv (1 : Fin 2) p))
      (bivariateDecoratedObservableRoot_totalPartitionPolynomial
        F H Λ Φ β hFH)
  simpa [Polymer.FinitePolymerModel.bigradedSecondPartitionCoefficient] using h

theorem bivariateDecoratedObservableRoot_mixedPartitionCoefficient
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (hFH : Disjoint F.support H.support) :
    (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).bigradedMixedPartitionCoefficient
          (bivariateDecoratedObservableRootGrading F H Λ) =
      complexObservableNumerator (F.mul H) Λ Φ β := by
  have h := congrArg (fun p => MvPolynomial.constantCoeff
    (MvPolynomial.pderiv (0 : Fin 2)
      (MvPolynomial.pderiv (1 : Fin 2) p)))
      (bivariateDecoratedObservableRoot_totalPartitionPolynomial
        F H Λ Φ β hFH)
  simpa [Polymer.FinitePolymerModel.bigradedMixedPartitionCoefficient] using h

/-- All three connected source sectors of the exact bivariate decorated gas
are genuinely absolutely summable on the explicit lattice disk. -/
theorem summable_norm_bivariateDecoratedObservableSourceSectors_succ
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let M := bivariateDecoratedObservableRootModel F H Λ Φ β 1 1
    let grading := bivariateDecoratedObservableRootGrading F H Λ
    Summable (fun n : ℕ ↦
        ‖M.bigradedFirstLinearMayerDegreeSum grading (n + 1)‖) ∧
      Summable (fun n : ℕ ↦
        ‖M.bigradedSecondLinearMayerDegreeSum grading (n + 1)‖) ∧
      Summable (fun n : ℕ ↦
        ‖M.bigradedMixedMayerDegreeSum grading (n + 1)‖) := by
  dsimp only
  let M := bivariateDecoratedObservableRootModel F H Λ Φ β 1 1
  let grading := bivariateDecoratedObservableRootGrading F H Λ
  let ρ := bivariateDecoratedObservableRootRegularization F H Λ Φ β
  let alpha := bivariateObservableSourceValues (ρ : ℂ) (ρ : ℂ)
  have hρ : ρ ≠ 0 := ne_of_gt
    (bivariateDecoratedObservableRootRegularization_pos F H Λ Φ β)
  have halpha0 : alpha 0 ≠ 0 := by
    simpa [alpha, bivariateObservableSourceValues] using hρ
  have halpha1 : alpha 1 ≠ 0 := by
    simpa [alpha, bivariateObservableSourceValues] using hρ
  have hscaled : Summable (fun n : ℕ ↦
      (M.scaleByBigradedSource grading alpha).normMayerDegreeSum (n + 1)) := by
    exact bivariateDecoratedObservableRootModel_regularized_summable_normMayerDegreeSum_succ
      F H Λ Φ hβ
  exact ⟨
    M.summable_norm_bigradedFirstLinearMayerDegreeSum_succ_of_scaled
      grading alpha halpha0 hscaled,
    M.summable_norm_bigradedSecondLinearMayerDegreeSum_succ_of_scaled
      grading alpha halpha1 hscaled,
    M.summable_norm_bigradedMixedMayerDegreeSum_succ_of_scaled
      grading alpha halpha0 halpha1 hscaled⟩

/-- The finite-volume truncated correlation is exactly the absolutely
convergent bidegree `(1,1)` Mayer series of the support-graded decorated gas.
Every term in this series belongs to the left--right or intrinsic-bridge
sector of the exact source reindexing. -/
theorem complexGibbsTruncatedCorrelation_eq_tsum_bivariateDecoratedMixed
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hFH : Disjoint F.support H.support)
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    complexGibbsExpectation (F.mul H) Λ Φ β -
        complexGibbsExpectation F Λ Φ β *
          complexGibbsExpectation H Λ Φ β =
      ∑' n : ℕ,
        bivariateDecoratedObservableMixedMayerDegreeSum F H Λ Φ β n := by
  let M := bivariateDecoratedObservableRootModel F H Λ Φ β 1 1
  let grading := bivariateDecoratedObservableRootGrading F H Λ
  let C0 : ℂ := ∑' n : ℕ, M.bigradedFirstLinearMayerDegreeSum grading n
  let C1 : ℂ := ∑' n : ℕ, M.bigradedSecondLinearMayerDegreeSum grading n
  let C01 : ℂ := ∑' n : ℕ, M.bigradedMixedMayerDegreeSum grading n
  have hsums := summable_norm_bivariateDecoratedObservableSourceSectors_succ
    F H Λ Φ hβ
  have hpoint := M.bigradedPartitionCoefficients_eq_connected grading
    hsums.1 hsums.2.1 hsums.2.2
  have hvac : M.bigradedVacuumPartitionCoefficient grading =
      complexPartitionFunction Λ Φ β :=
    bivariateDecoratedObservableRoot_vacuumPartitionCoefficient
      F H Λ Φ β hFH
  have hfirst : complexObservableNumerator F Λ Φ β =
      complexPartitionFunction Λ Φ β * C0 := by
    calc
      _ = M.bigradedFirstPartitionCoefficient grading :=
        (bivariateDecoratedObservableRoot_firstPartitionCoefficient
          F H Λ Φ β hFH).symm
      _ = M.bigradedVacuumPartitionCoefficient grading * C0 := hpoint.1
      _ = _ := by rw [hvac]
  have hsecond : complexObservableNumerator H Λ Φ β =
      complexPartitionFunction Λ Φ β * C1 := by
    calc
      _ = M.bigradedSecondPartitionCoefficient grading :=
        (bivariateDecoratedObservableRoot_secondPartitionCoefficient
          F H Λ Φ β hFH).symm
      _ = M.bigradedVacuumPartitionCoefficient grading * C1 := hpoint.2.1
      _ = _ := by rw [hvac]
  have hmixed : complexObservableNumerator (F.mul H) Λ Φ β =
      complexPartitionFunction Λ Φ β * (C01 + C0 * C1) := by
    calc
      _ = M.bigradedMixedPartitionCoefficient grading :=
        (bivariateDecoratedObservableRoot_mixedPartitionCoefficient
          F H Λ Φ β hFH).symm
      _ = M.bigradedVacuumPartitionCoefficient grading *
          (C01 + C0 * C1) := hpoint.2.2
      _ = _ := by rw [hvac]
  have hZ : complexPartitionFunction Λ Φ β ≠ 0 :=
    complexPartitionFunction_ne_zero_of_norm_lt_latticeRadius Λ Φ hβ
  rw [show (∑' n : ℕ,
      bivariateDecoratedObservableMixedMayerDegreeSum F H Λ Φ β n) = C01 by
    rfl]
  unfold complexGibbsExpectation
  rw [hfirst, hsecond, hmixed]
  field_simp [hZ]; ring

/-! ## Exact two-observable cumulant series -/

/-- Degree-`n` cumulant of the exact decorated-root series.  The Cauchy
product removes the pair of disconnected one-root clusters at the same total
degree. -/
def decoratedObservableTruncatedMayerDegreeSum
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (n : ℕ) : ℂ :=
  decoratedObservableRootLinearMayerDegreeSum (F.mul H) Λ Φ β n -
    ∑ pair ∈ Finset.antidiagonal n,
      decoratedObservableRootLinearMayerDegreeSum F Λ Φ β pair.1 *
        decoratedObservableRootLinearMayerDegreeSum H Λ Φ β pair.2

/-- The exact arbitrary-observable cumulant coefficients are absolutely
summable on the explicit strong-coupling disk. -/
theorem summable_norm_decoratedObservableTruncatedMayerDegreeSum
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable (fun n : ℕ =>
      ‖decoratedObservableTruncatedMayerDegreeSum F H Λ Φ β n‖) := by
  let CF : ℕ → ℂ := fun n =>
    decoratedObservableRootLinearMayerDegreeSum F Λ Φ β n
  let CH : ℕ → ℂ := fun n =>
    decoratedObservableRootLinearMayerDegreeSum H Λ Φ β n
  let CFH : ℕ → ℂ := fun n =>
    decoratedObservableRootLinearMayerDegreeSum (F.mul H) Λ Φ β n
  let Conv : ℕ → ℂ := fun n =>
    ∑ pair ∈ Finset.antidiagonal n, CF pair.1 * CH pair.2
  have hFnorm : Summable (fun n => ‖CF n‖) :=
    summable_norm_decoratedObservableRootLinearMayerDegreeSum F Λ Φ hβ
  have hHnorm : Summable (fun n => ‖CH n‖) :=
    summable_norm_decoratedObservableRootLinearMayerDegreeSum H Λ Φ hβ
  have hFHnorm : Summable (fun n => ‖CFH n‖) :=
    summable_norm_decoratedObservableRootLinearMayerDegreeSum
      (F.mul H) Λ Φ hβ
  have hConvNorm : Summable (fun n => ‖Conv n‖) :=
    summable_norm_sum_mul_antidiagonal_of_summable_norm hFnorm hHnorm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => norm_sub_le (CFH n) (Conv n))
    (hFHnorm.add hConvNorm)

/-- The finite-volume truncated correlation is exactly the absolutely
convergent degreewise cumulant series of the decorated observable roots. -/
theorem complexGibbsTruncatedCorrelation_eq_tsum_decoratedCumulant
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (hZ : complexPartitionFunction Λ Φ β ≠ 0) :
    complexGibbsExpectation (F.mul H) Λ Φ β -
        complexGibbsExpectation F Λ Φ β *
          complexGibbsExpectation H Λ Φ β =
      ∑' n : ℕ,
        decoratedObservableTruncatedMayerDegreeSum F H Λ Φ β n := by
  let CF : ℕ → ℂ := fun n =>
    decoratedObservableRootLinearMayerDegreeSum F Λ Φ β n
  let CH : ℕ → ℂ := fun n =>
    decoratedObservableRootLinearMayerDegreeSum H Λ Φ β n
  let CFH : ℕ → ℂ := fun n =>
    decoratedObservableRootLinearMayerDegreeSum (F.mul H) Λ Φ β n
  let Conv : ℕ → ℂ := fun n =>
    ∑ pair ∈ Finset.antidiagonal n, CF pair.1 * CH pair.2
  have hFnorm : Summable (fun n => ‖CF n‖) :=
    summable_norm_decoratedObservableRootLinearMayerDegreeSum F Λ Φ hβ
  have hHnorm : Summable (fun n => ‖CH n‖) :=
    summable_norm_decoratedObservableRootLinearMayerDegreeSum H Λ Φ hβ
  have hFHnorm : Summable (fun n => ‖CFH n‖) :=
    summable_norm_decoratedObservableRootLinearMayerDegreeSum
      (F.mul H) Λ Φ hβ
  have hConvNorm : Summable (fun n => ‖Conv n‖) :=
    summable_norm_sum_mul_antidiagonal_of_summable_norm hFnorm hHnorm
  have hConvSum :
      (∑' n, CF n) * (∑' n, CH n) = ∑' n, Conv n :=
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      hFnorm hHnorm
  rw [complexGibbsExpectation_eq_tsum_connectedDecoratedRoot
      (F.mul H) Λ Φ hβ hZ,
    complexGibbsExpectation_eq_tsum_connectedDecoratedRoot F Λ Φ hβ hZ,
    complexGibbsExpectation_eq_tsum_connectedDecoratedRoot H Λ Φ hβ hZ]
  change (∑' n, CFH n) - (∑' n, CF n) * (∑' n, CH n) = _
  rw [hConvSum]
  change (∑' n, CFH n) - ∑' n, Conv n =
    (∑' n, (CFH n - Conv n))
  exact (Summable.tsum_sub hFHnorm.of_norm hConvNorm.of_norm).symm

end

end YangMills.StrongCoupling
