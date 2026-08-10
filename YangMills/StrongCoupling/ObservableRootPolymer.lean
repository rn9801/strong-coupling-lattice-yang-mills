/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.Augmented
import YangMills.StrongCoupling.BoundaryGeometry
import YangMills.StrongCoupling.Counting

/-!
# Observable-root plaquette polymer gases

The constructions here instantiate the abstract augmented polymer gas with
the plaquette roots already used in the lattice geometry.  No influence
matrix or Douglas compatibility layer is involved: a source root is adjacent
exactly to bulk polymers containing a plaquette incident to the recorded edge
support of its local observable.
-/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Polymer

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- A bulk plaquette polymer touches an observable root when its plaquette
support meets the finite observable-root plaquette set. -/
def observableRootTouches (F : LocalObservable d G)
    (Λ : FiniteSpecification d G) (γ : PlaquettePolymer Λ) : Prop :=
  ¬Disjoint γ.1 (observableRootPlaquettes Λ F)

instance (F : LocalObservable d G) (Λ : FiniteSpecification d G) :
    DecidablePred (observableRootTouches F Λ) :=
  fun _ => Classical.propDecidable _

@[simp]
theorem observableRootTouches_iff
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (γ : PlaquettePolymer Λ) :
    observableRootTouches F Λ γ ↔
      ∃ p ∈ γ.1, p ∈ observableRootPlaquettes Λ F := by
  rw [observableRootTouches, Finset.not_disjoint_iff]

/-- The finite gas with one source vertex for `F`. -/
def oneObservableRootModel
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ) :
    FinitePolymerModel (PlaquettePolymer Λ ⊕ Unit) :=
  (plaquettePolymerModel Λ Φ β).augmentRoots
    (fun _ γ => observableRootTouches F Λ γ) (fun _ => α)

@[simp]
theorem oneObservableRootModel_root_bulk_incompatible
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ) (γ : PlaquettePolymer Λ) :
    (oneObservableRootModel F Λ Φ β α).incompatible (Sum.inr ()) (Sum.inl γ) ↔
      observableRootTouches F Λ γ := Iff.rfl

@[simp]
theorem oneObservableRootModel_root_activity
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ) :
    (oneObservableRootModel F Λ Φ β α).activity (Sum.inr ()) = α := rfl

/-- Two labelled observable sources used by truncated correlations. -/
def twoObservableRootTouches
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (r : Fin 2) (γ : PlaquettePolymer Λ) : Prop :=
  if r = 0 then observableRootTouches F Λ γ
  else observableRootTouches H Λ γ

instance (F H : LocalObservable d G) (Λ : FiniteSpecification d G) :
    DecidableRel (twoObservableRootTouches F H Λ) :=
  fun _ _ => Classical.propDecidable _

/-- The finite gas with distinct source vertices for `F` and `H`.  The two
roots are mutually compatible; they become linked only through a connected
cluster of bulk plaquette polymers. -/
def twoObservableRootModel
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) :
    FinitePolymerModel (PlaquettePolymer Λ ⊕ Fin 2) :=
  (plaquettePolymerModel Λ Φ β).augmentRoots
    (twoObservableRootTouches F H Λ) (fun r => if r = 0 then α else θ)

@[simp]
theorem twoObservableRootModel_distinct_roots_compatible
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) :
    ¬(twoObservableRootModel F H Λ Φ β α θ).incompatible
      (Sum.inr (0 : Fin 2)) (Sum.inr (1 : Fin 2)) := by
  simp [twoObservableRootModel]

@[simp]
theorem twoObservableRootModel_first_root_bulk
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) (γ : PlaquettePolymer Λ) :
    (twoObservableRootModel F H Λ Φ β α θ).incompatible
      (Sum.inr (0 : Fin 2)) (Sum.inl γ) ↔ observableRootTouches F Λ γ := by
  simp [twoObservableRootModel, twoObservableRootTouches]

@[simp]
theorem twoObservableRootModel_second_root_bulk
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) (γ : PlaquettePolymer Λ) :
    (twoObservableRootModel F H Λ Φ β α θ).incompatible
      (Sum.inr (1 : Fin 2)) (Sum.inl γ) ↔ observableRootTouches H Λ γ := by
  simp [twoObservableRootModel, twoObservableRootTouches]

/-! ## Exact observable source partitions -/

/-- The exact finite-volume partition function with one formal observable
source.  Its two coefficients are represented by the vacuum and marked
plaquette expansions, respectively. -/
def oneObservableSourcePartition
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ) : ℂ :=
  complexPartitionFunction Λ Φ β + α * complexObservableNumerator F Λ Φ β

@[simp]
theorem oneObservableSourcePartition_zero
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    oneObservableSourcePartition F Λ Φ β 0 =
      complexPartitionFunction Λ Φ β := by
  simp [oneObservableSourcePartition]

/-- After division by the vacuum partition function, the coefficient of the
adjoined root is the exact finite-volume expectation of the arbitrary local
observable. -/
theorem oneObservableSourcePartition_div
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ)
    (hZ : complexPartitionFunction Λ Φ β ≠ 0) :
    oneObservableSourcePartition F Λ Φ β α /
        complexPartitionFunction Λ Φ β =
      1 + α * complexGibbsExpectation F Λ Φ β := by
  unfold oneObservableSourcePartition complexGibbsExpectation
  field_simp

/-- The exact two-source partition polynomial.  Its bilinear coefficient is
the marked numerator for the product observable. -/
def twoObservableSourcePartition
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) : ℂ :=
  complexPartitionFunction Λ Φ β +
    α * complexObservableNumerator F Λ Φ β +
    θ * complexObservableNumerator H Λ Φ β +
    α * θ * complexObservableNumerator (F.mul H) Λ Φ β

/-- Exact normalized two-source identity.  This is the algebraic input whose
connected bilinear logarithmic coefficient gives the truncated correlation. -/
theorem twoObservableSourcePartition_div
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ)
    (hZ : complexPartitionFunction Λ Φ β ≠ 0) :
    twoObservableSourcePartition F H Λ Φ β α θ /
        complexPartitionFunction Λ Φ β =
      1 + α * complexGibbsExpectation F Λ Φ β +
        θ * complexGibbsExpectation H Λ Φ β +
        α * θ * complexGibbsExpectation (F.mul H) Λ Φ β := by
  unfold twoObservableSourcePartition complexGibbsExpectation
  field_simp

/-- The connected two-root coefficient is exactly the finite-volume
truncated correlation. -/
theorem twoObservable_connectedCoefficient
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (hZ : complexPartitionFunction Λ Φ β ≠ 0) :
    (complexObservableNumerator (F.mul H) Λ Φ β *
          complexPartitionFunction Λ Φ β -
        complexObservableNumerator F Λ Φ β *
          complexObservableNumerator H Λ Φ β) /
        (complexPartitionFunction Λ Φ β) ^ 2 =
      complexGibbsExpectation (F.mul H) Λ Φ β -
        complexGibbsExpectation F Λ Φ β *
          complexGibbsExpectation H Λ Φ β := by
  unfold complexGibbsExpectation
  field_simp

end

end YangMills.StrongCoupling
