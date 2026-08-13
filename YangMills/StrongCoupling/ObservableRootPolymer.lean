/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.Augmented
import YangMills.Polymer.LabelledMayerExponential
import YangMills.Polymer.LabelledRootedForestSpecies
import YangMills.Polymer.LabelledTreeSummation
import YangMills.Polymer.TwoRootSource
import YangMills.StrongCoupling.BoundaryGeometry
import YangMills.StrongCoupling.Counting

/-!
# Observable-root plaquette polymer gases

The constructions here instantiate the abstract augmented polymer gas with
the plaquette roots already used in the lattice geometry.  A source root is
adjacent exactly to bulk polymers containing a plaquette incident to the
recorded edge support of its local observable.
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

/-! ## Fixed-labelled bivariate source series -/

/-- Total-activity partition series for the two compatible geometric
observable roots, retaining their two sources as multivariable-polynomial
coefficients. -/
def twoObservableRootSourcePartitionPowerSeries
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    PowerSeries Polymer.BivariateSourcePowerSeries.Coeff :=
  (plaquettePolymerModel Λ Φ β).twoRootSourcePartitionPowerSeries
    (twoObservableRootTouches F H Λ) (fun _ => 1)

/-- Connected counterpart of `twoObservableRootSourcePartitionPowerSeries`. -/
def twoObservableRootSourceMayerPowerSeries
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    PowerSeries Polymer.BivariateSourcePowerSeries.Coeff :=
  (plaquettePolymerModel Λ Φ β).twoRootSourceMayerPowerSeries
    (twoObservableRootTouches F H Λ) (fun _ => 1)

/-- Degree-`n` connected coefficient containing each compatible geometric
observable root exactly once. -/
def twoObservableRootMixedMayerDegreeSum
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (n : ℕ) : ℂ :=
  ((plaquettePolymerModel Λ Φ β).augmentRoots
    (twoObservableRootTouches F H Λ) (fun _ => 1)).twoRootMixedMayerDegreeSum n

/-- Exact bivariate fixed-labelled exponential formula for the geometric
two-root plaquette gas. -/
theorem expOf_twoObservableRootSourceMayerPowerSeries
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    Polymer.BivariateSourcePowerSeries.expOf
        (twoObservableRootSourceMayerPowerSeries F H Λ Φ β) =
      twoObservableRootSourcePartitionPowerSeries F H Λ Φ β := by
  exact (plaquettePolymerModel Λ Φ β).expOf_twoRootSourceMayerPowerSeries
    (twoObservableRootTouches F H Λ) (fun _ => 1)

/-- The mixed partition coefficient splits exactly into its genuinely
two-root connected part and the product of the two one-root connected parts,
before evaluating total activity. -/
theorem twoObservableRootSource_mixedCoefficient
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    Polymer.BivariateSourcePowerSeries.mixedCoefficient
        (twoObservableRootSourcePartitionPowerSeries F H Λ Φ β) =
      Polymer.BivariateSourcePowerSeries.constantSource
          (twoObservableRootSourcePartitionPowerSeries F H Λ Φ β) *
        (Polymer.BivariateSourcePowerSeries.mixedCoefficient
            (twoObservableRootSourceMayerPowerSeries F H Λ Φ β) +
          Polymer.BivariateSourcePowerSeries.linearCoefficient 0
              (twoObservableRootSourceMayerPowerSeries F H Λ Φ β) *
            Polymer.BivariateSourcePowerSeries.linearCoefficient 1
              (twoObservableRootSourceMayerPowerSeries F H Λ Φ β)) := by
  exact (plaquettePolymerModel Λ Φ β).mixedCoefficient_twoRootSourcePartitionPowerSeries
    (twoObservableRootTouches F H Λ) (fun _ => 1)

/-- Coefficient extraction from the concrete two-source Mayer series is the
mixed degree sum defined above. -/
theorem coeff_mixedCoefficient_twoObservableRootSourceMayerPowerSeries
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (n : ℕ) :
    PowerSeries.coeff n
        (Polymer.BivariateSourcePowerSeries.mixedCoefficient
          (twoObservableRootSourceMayerPowerSeries F H Λ Φ β)) =
      twoObservableRootMixedMayerDegreeSum F H Λ Φ β n := by
  exact (plaquettePolymerModel Λ Φ β).coeff_mixedCoefficient_twoRootSourceMayerPowerSeries
    (twoObservableRootTouches F H Λ) (fun _ => 1) n

/-! ## Explicit KP certificates for the augmented root gases -/

/-- Genuine KP weight for the one-observable augmented gas at zero source. -/
def oneObservableRootKPWeight
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    (PlaquettePolymer Λ ⊕ Unit) → ℝ :=
  (plaquettePolymerModel Λ Φ β).augmentRootKPWeight
    (fun _ γ => observableRootTouches F Λ γ) plaquetteKPWeight

/-- Genuine KP weight for the two-observable augmented gas at zero source. -/
def twoObservableRootKPWeight
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    (PlaquettePolymer Λ ⊕ Fin 2) → ℝ :=
  (plaquettePolymerModel Λ Φ β).augmentRootKPWeight
    (twoObservableRootTouches F H Λ) plaquetteKPWeight

/-- The explicit lattice disk supplies a standard KP certificate for the
one-root augmented gas at zero source activity. -/
theorem oneObservableRootModel_koteckyPreiss_zero
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    (oneObservableRootModel F Λ Φ β 0).KoteckyPreissCertificate
      Finset.univ (oneObservableRootKPWeight F Λ Φ β) := by
  have hbase :
      (plaquettePolymerModel Λ Φ β).KoteckyPreissCertificate
        Finset.univ plaquetteKPWeight := by
    apply plaquettePolymerModel_koteckyPreiss Λ Φ β
      (cubicPlaquetteAnimalCertificate Λ)
    exact perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
      (16 * d) (2 ^ (16 * d)) hβ
  simpa [oneObservableRootModel, oneObservableRootKPWeight] using
    (plaquettePolymerModel Λ Φ β).koteckyPreissCertificate_augmentRoots_zero
      (fun _ γ => observableRootTouches F Λ γ) plaquetteKPWeight hbase

/-- The corresponding explicit certificate for two labelled observable
roots.  The roots remain mutually compatible and both have zero source
activity at the expansion point. -/
theorem twoObservableRootModel_koteckyPreiss_zero
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    (twoObservableRootModel F H Λ Φ β 0 0).KoteckyPreissCertificate
      Finset.univ (twoObservableRootKPWeight F H Λ Φ β) := by
  have hbase :
      (plaquettePolymerModel Λ Φ β).KoteckyPreissCertificate
        Finset.univ plaquetteKPWeight := by
    apply plaquettePolymerModel_koteckyPreiss Λ Φ β
      (cubicPlaquetteAnimalCertificate Λ)
    exact perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
      (16 * d) (2 ^ (16 * d)) hβ
  simpa [twoObservableRootModel, twoObservableRootKPWeight] using
    (plaquettePolymerModel Λ Φ β).koteckyPreissCertificate_augmentRoots_zero
      (twoObservableRootTouches F H Λ) plaquetteKPWeight hbase

/-- The tilted mass attached to an observable root is controlled uniformly
by the number of active plaquettes incident to its support.  This is a direct
consequence of the standard KP inequality applied at one-plaquette polymers. -/
theorem oneObservableRootKPWeight_root_le_card_mul_log_two
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    oneObservableRootKPWeight F Λ Φ β (Sum.inr ()) ≤
      ((observableRootPlaquettes Λ F).card : ℝ) * Real.log 2 := by
  classical
  let M := plaquettePolymerModel Λ Φ β
  let R := observableRootPlaquettes Λ F
  let w : PlaquettePolymer Λ → ℝ := fun γ =>
    ‖M.activity γ‖ * Real.exp (plaquetteKPWeight γ)
  have hKP : M.KoteckyPreissCertificate Finset.univ plaquetteKPWeight := by
    dsimp [M]
    apply plaquettePolymerModel_koteckyPreiss Λ Φ β
      (cubicPlaquetteAnimalCertificate Λ)
    exact perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
      (16 * d) (2 ^ (16 * d)) hβ
  have hpoint : ∀ γ : PlaquettePolymer Λ,
      (if observableRootTouches F Λ γ then w γ else 0) ≤
        ∑ p ∈ R, if p ∈ γ.1 then w γ else 0 := by
    intro γ
    by_cases htouch : observableRootTouches F Λ γ
    · obtain ⟨p, hpγ, hpR⟩ := (observableRootTouches_iff F Λ γ).mp htouch
      rw [if_pos htouch]
      calc
        w γ = if p ∈ γ.1 then w γ else 0 := by simp [hpγ]
        _ ≤ ∑ q ∈ R, if q ∈ γ.1 then w γ else 0 := by
          have hnonneg : ∀ q ∈ R,
              0 ≤ if q ∈ γ.1 then w γ else 0 := by
            intro q _
            split_ifs
            · exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
            · exact le_rfl
          have hle := Finset.single_le_sum
            (s := R) (f := fun q => if q ∈ γ.1 then w γ else 0)
            hnonneg (show p ∈ R from hpR)
          exact hle
    · rw [if_neg htouch]
      exact Finset.sum_nonneg fun p _ => by
        split_ifs
        · exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
        · exact le_rfl
  have hsingle : ∀ p ∈ R,
      (∑ γ : PlaquettePolymer Λ, if p ∈ γ.1 then w γ else 0) ≤ Real.log 2 := by
    intro p _hpR
    have h := hKP.2 (singletonPlaquettePolymer Λ p) (Finset.mem_univ _)
    rw [Finset.sum_filter] at h
    have hdom :
        (∑ γ : PlaquettePolymer Λ, if p ∈ γ.1 then w γ else 0) ≤
          ∑ γ : PlaquettePolymer Λ,
            if M.incompatible (singletonPlaquettePolymer Λ p) γ then w γ else 0 := by
      apply Finset.sum_le_sum
      intro γ _
      by_cases hpγ : p ∈ γ.1
      · have hinc : M.incompatible (singletonPlaquettePolymer Λ p) γ := by
          simpa [M] using
            singletonPlaquettePolymer_incompatible_of_mem Λ Φ β p γ hpγ
        simp [hpγ, hinc]
      · simp [hpγ]
        positivity
    calc
      (∑ γ : PlaquettePolymer Λ, if p ∈ γ.1 then w γ else 0) ≤
          ∑ γ : PlaquettePolymer Λ,
            if M.incompatible (singletonPlaquettePolymer Λ p) γ then w γ else 0 :=
        hdom
      _ ≤ plaquetteKPWeight (singletonPlaquettePolymer Λ p) := by
        simpa [M, w] using h
      _ = Real.log 2 := by
        simp [plaquetteKPWeight]
  change (∑ γ : PlaquettePolymer Λ,
      if observableRootTouches F Λ γ then w γ else 0) ≤
    (R.card : ℝ) * Real.log 2
  calc
    (∑ γ : PlaquettePolymer Λ,
        if observableRootTouches F Λ γ then w γ else 0) ≤
        ∑ γ : PlaquettePolymer Λ,
          ∑ p ∈ R, if p ∈ γ.1 then w γ else 0 :=
      Finset.sum_le_sum fun γ _ => hpoint γ
    _ = ∑ p ∈ R,
        ∑ γ : PlaquettePolymer Λ, if p ∈ γ.1 then w γ else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _p ∈ R, Real.log 2 := by
      exact Finset.sum_le_sum hsingle
    _ = (R.card : ℝ) * Real.log 2 := by simp

/-- Consequently the one-root KP weight has the required local-observable
prefactor, uniformly in volume and exterior data. -/
theorem oneObservableRootKPWeight_root_le_support
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    oneObservableRootKPWeight F Λ Φ β (Sum.inr ()) ≤
      (4 * d * F.support.card : ℕ) * Real.log 2 := by
  calc
    oneObservableRootKPWeight F Λ Φ β (Sum.inr ()) ≤
        ((observableRootPlaquettes Λ F).card : ℝ) * Real.log 2 :=
      oneObservableRootKPWeight_root_le_card_mul_log_two F Λ Φ hβ
    _ ≤ (4 * d * F.support.card : ℕ) * Real.log 2 := by
      gcongr
      exact_mod_cast card_observableRootPlaquettes_le Λ F

@[simp]
theorem twoObservableRootKPWeight_first_root
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    twoObservableRootKPWeight F H Λ Φ β (Sum.inr (0 : Fin 2)) =
      oneObservableRootKPWeight F Λ Φ β (Sum.inr ()) := by
  classical
  change (∑ γ : PlaquettePolymer Λ,
      if twoObservableRootTouches F H Λ 0 γ then
        ‖(plaquettePolymerModel Λ Φ β).activity γ‖ *
          Real.exp (plaquetteKPWeight γ) else 0) =
    ∑ γ : PlaquettePolymer Λ, if observableRootTouches F Λ γ then
      ‖(plaquettePolymerModel Λ Φ β).activity γ‖ *
        Real.exp (plaquetteKPWeight γ) else 0
  apply Finset.sum_congr rfl
  intro γ _
  simp [twoObservableRootTouches]

@[simp]
theorem twoObservableRootKPWeight_second_root
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    twoObservableRootKPWeight F H Λ Φ β (Sum.inr (1 : Fin 2)) =
      oneObservableRootKPWeight H Λ Φ β (Sum.inr ()) := by
  classical
  change (∑ γ : PlaquettePolymer Λ,
      if twoObservableRootTouches F H Λ 1 γ then
        ‖(plaquettePolymerModel Λ Φ β).activity γ‖ *
          Real.exp (plaquetteKPWeight γ) else 0) =
    ∑ γ : PlaquettePolymer Λ, if observableRootTouches H Λ γ then
      ‖(plaquettePolymerModel Λ Φ β).activity γ‖ *
        Real.exp (plaquetteKPWeight γ) else 0
  apply Finset.sum_congr rfl
  intro γ _
  simp [twoObservableRootTouches]

/-- Explicit local-support prefactor at the first root of the two-source gas. -/
theorem twoObservableRootKPWeight_first_root_le_support
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    twoObservableRootKPWeight F H Λ Φ β (Sum.inr (0 : Fin 2)) ≤
      (4 * d * F.support.card : ℕ) * Real.log 2 := by
  rw [twoObservableRootKPWeight_first_root]
  exact oneObservableRootKPWeight_root_le_support F Λ Φ hβ

/-- Explicit local-support prefactor at the second root of the two-source gas. -/
theorem twoObservableRootKPWeight_second_root_le_support
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    twoObservableRootKPWeight F H Λ Φ β (Sum.inr (1 : Fin 2)) ≤
      (4 * d * H.support.card : ℕ) * Real.log 2 := by
  rw [twoObservableRootKPWeight_second_root]
  exact oneObservableRootKPWeight_root_le_support H Λ Φ hβ

/-! ## A nonzero-source KP regularization -/

/-- A fixed part of the quantitative bulk reserve used to switch on both
labelled roots. -/
def twoRootSourceReserve : ℝ := Real.log 2 / 8

theorem twoRootSourceReserve_pos : 0 < twoRootSourceReserve := by
  unfold twoRootSourceReserve
  positivity

theorem twoRootSourceReserve_le_one : twoRootSourceReserve ≤ 1 := by
  have hlog : Real.log 2 < 2 - 1 :=
    Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
  unfold twoRootSourceReserve
  linarith

/-- Small positive activities for the two labelled roots.  The exponential
factor exactly cancels their enlarged KP weight in the certificate. -/
def twoObservableRootRegularizedActivity
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (r : Fin 2) : ℂ :=
  ((twoRootSourceReserve * Real.exp
    (-(twoObservableRootKPWeight F H Λ Φ β (Sum.inr r) + 1)) : ℝ) : ℂ)

/-- Bulk weights are unchanged; each labelled root gets one unit of reserve
beyond its zero-source KP weight. -/
def twoObservableRootRegularizedKPWeight
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    (PlaquettePolymer Λ ⊕ Fin 2) → ℝ
  | Sum.inl γ => plaquetteKPWeight γ
  | Sum.inr r =>
      twoObservableRootKPWeight F H Λ Φ β (Sum.inr r) + 1

theorem twoObservableRootRegularizedActivity_pos
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (r : Fin 2) :
    0 < (twoObservableRootRegularizedActivity F H Λ Φ β r).re := by
  unfold twoObservableRootRegularizedActivity
  simp only [Complex.ofReal_re]
  exact mul_pos twoRootSourceReserve_pos (Real.exp_pos _)

theorem norm_regularizedRootActivity_mul_exp_weight
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (r : Fin 2) :
    ‖twoObservableRootRegularizedActivity F H Λ Φ β r‖ *
        Real.exp (twoObservableRootRegularizedKPWeight F H Λ Φ β
          (Sum.inr r)) =
      twoRootSourceReserve := by
  let w := twoObservableRootKPWeight F H Λ Φ β (Sum.inr r) + 1
  have hreserve : 0 ≤ twoRootSourceReserve := twoRootSourceReserve_pos.le
  have hexp : 0 ≤ Real.exp (-w) := (Real.exp_pos _).le
  change ‖((twoRootSourceReserve * Real.exp (-w) : ℝ) : ℂ)‖ *
      Real.exp w = twoRootSourceReserve
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hreserve hexp), Real.exp_neg]
  field_simp

/-- Both labelled roots can be switched on at explicit positive activities
while retaining a genuine KP certificate.  The proof spends one quarter of
the bulk budget on the two roots and uses the quantitative reserve left by
the lattice strong-coupling radius. -/
theorem twoObservableRootModel_koteckyPreiss_regularized
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ((plaquettePolymerModel Λ Φ β).augmentRoots
      (twoObservableRootTouches F H Λ)
      (twoObservableRootRegularizedActivity F H Λ Φ β)).KoteckyPreissCertificate
        Finset.univ
        (twoObservableRootRegularizedKPWeight F H Λ Φ β) := by
  classical
  let M := plaquettePolymerModel Λ Φ β
  let touches := twoObservableRootTouches F H Λ
  let epsilon := twoObservableRootRegularizedActivity F H Λ Φ β
  let aRoot : Fin 2 → ℝ := fun r =>
    twoObservableRootKPWeight F H Λ Φ β (Sum.inr r)
  have hsmall : perturbationMajorant Φ β <
      dobrushinThreshold (16 * d) (2 ^ (16 * d)) :=
    perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
      (16 * d) (2 ^ (16 * d)) hβ
  have hbaseNonneg : ∀ γ : PlaquettePolymer Λ, 0 ≤ plaquetteKPWeight γ := by
    intro γ
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num)).le
  have haRootNonneg (r : Fin 2) : 0 ≤ aRoot r := by
    have h := M.augmentRootKPWeight_nonneg touches plaquetteKPWeight
      hbaseNonneg (Sum.inr r)
    simpa [M, touches, aRoot, twoObservableRootKPWeight] using h
  refine ⟨?_, ?_⟩
  · rintro (γ | r)
    · exact hbaseNonneg γ
    · exact add_nonneg (haRootNonneg r) zero_le_one
  · rintro (γ | r) _
    · have hbulk :=
        plaquettePolymerModel_kp_incompatible_sum_le_quarter
          Λ Φ β (cubicPlaquetteAnimalCertificate Λ) hsmall γ
      rw [Finset.sum_filter] at hbulk
      have hroots :
          (∑ s : Fin 2,
            if touches s γ then
              ‖epsilon s‖ * Real.exp (aRoot s + 1) else 0) ≤
            Real.log 2 / 4 := by
        calc
          _ ≤ ∑ _s : Fin 2, twoRootSourceReserve := by
            apply Finset.sum_le_sum
            intro s _
            by_cases hs : touches s γ
            · rw [if_pos hs]
              exact le_of_eq (by
                simpa [epsilon, aRoot,
                  twoObservableRootRegularizedKPWeight] using
                    norm_regularizedRootActivity_mul_exp_weight
                      F H Λ Φ β s)
            · simp [hs, twoRootSourceReserve_pos.le]
          _ = 2 * twoRootSourceReserve := by simp [Fin.sum_univ_two]
          _ = Real.log 2 / 4 := by
            unfold twoRootSourceReserve
            ring
      have hcard : 1 ≤ γ.1.card := γ.2.1.card_pos
      have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      rw [Finset.sum_filter, Fintype.sum_sum_type]
      change
        (∑ δ : PlaquettePolymer Λ,
            if M.incompatible γ δ then
              ‖M.activity δ‖ * Real.exp (plaquetteKPWeight δ) else 0) +
          (∑ s : Fin 2,
            if touches s γ then
              ‖epsilon s‖ * Real.exp (aRoot s + 1) else 0) ≤
          plaquetteKPWeight γ
      calc
        _ ≤ (γ.1.card : ℝ) * (Real.log 2 / 4) +
            Real.log 2 / 4 := add_le_add hbulk hroots
        _ ≤ (γ.1.card : ℝ) * Real.log 2 := by
          have hcardReal : (1 : ℝ) ≤ (γ.1.card : ℝ) := by
            exact_mod_cast hcard
          nlinarith
        _ = plaquetteKPWeight γ := rfl
    · rw [Finset.sum_filter, Fintype.sum_sum_type]
      change
        (∑ γ : PlaquettePolymer Λ,
            if touches r γ then
              ‖M.activity γ‖ * Real.exp (plaquetteKPWeight γ) else 0) +
          (∑ s : Fin 2,
            if r = s then
              ‖epsilon s‖ * Real.exp (aRoot s + 1) else 0) ≤
          aRoot r + 1
      have hbulkRoot :
          (∑ γ : PlaquettePolymer Λ,
            if touches r γ then
              ‖M.activity γ‖ * Real.exp (plaquetteKPWeight γ) else 0) =
            aRoot r := by
        rfl
      have hself :
          (∑ s : Fin 2,
            if r = s then
              ‖epsilon s‖ * Real.exp (aRoot s + 1) else 0) =
            twoRootSourceReserve := by
        rw [Finset.sum_eq_single r]
        · simpa [epsilon, aRoot,
            twoObservableRootRegularizedKPWeight] using
            norm_regularizedRootActivity_mul_exp_weight F H Λ Φ β r
        · intro s _ hsr
          simp [hsr.symm]
        · simp
      rw [hbulkRoot, hself]
      linarith [twoRootSourceReserve_le_one]

theorem twoObservableRootRegularizedActivity_ne_zero
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (r : Fin 2) :
    twoObservableRootRegularizedActivity F H Λ Φ β r ≠ 0 := by
  intro hzero
  have hpos := twoObservableRootRegularizedActivity_pos F H Λ Φ β r
  rw [hzero] at hpos
  norm_num at hpos

/-- The full positive-degree Mayer majorant is summable after both observable
roots are switched on at the explicit regularizing activities. -/
theorem twoObservableRootModel_regularized_summable_normMayerDegreeSum_succ
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable (fun n : ℕ ↦
      ((plaquettePolymerModel Λ Φ β).augmentRoots
        (twoObservableRootTouches F H Λ)
        (twoObservableRootRegularizedActivity F H Λ Φ β)).normMayerDegreeSum
          (n + 1)) := by
  exact ((plaquettePolymerModel Λ Φ β).augmentRoots
    (twoObservableRootTouches F H Λ)
    (twoObservableRootRegularizedActivity F H Λ Φ β)).summable_normMayerDegreeSum_succ_of_koteckyPreiss_certified
      (twoObservableRootRegularizedKPWeight F H Λ Φ β)
      (twoObservableRootModel_koteckyPreiss_regularized F H Λ Φ hβ)

/-- Genuine pinned spanning-tree summability at either nonzero labelled root
of the regularized geometric source gas. -/
theorem twoObservableRootModel_regularized_summable_pinnedMayerTreeDegreeSum_succ
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) (r : Fin 2) :
    Summable (fun n : ℕ ↦
      ((plaquettePolymerModel Λ Φ β).augmentRoots
        (twoObservableRootTouches F H Λ)
        (twoObservableRootRegularizedActivity F H Λ Φ β)).pinnedMayerTreeDegreeSum
          (Sum.inr r) (n + 1)) := by
  exact YangMills.Polymer.FinitePolymerModel.summable_pinnedMayerTreeDegreeSum_succ_of_koteckyPreiss_certified
      ((plaquettePolymerModel Λ Φ β).augmentRoots
        (twoObservableRootTouches F H Λ)
        (twoObservableRootRegularizedActivity F H Λ Φ β))
      (twoObservableRootRegularizedKPWeight F H Λ Φ β)
      (twoObservableRootModel_koteckyPreiss_regularized F H Λ Φ hβ)
      (Sum.inr r)

/-- Genuine absolute summability of the first one-root connected sector at
unit source, obtained by rescaling from the nonzero-source KP gas. -/
theorem twoObservableRootModel_summable_norm_firstRootLinearMayerDegreeSum_succ
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable (fun n : ℕ ↦
      ‖((plaquettePolymerModel Λ Φ β).augmentRoots
        (twoObservableRootTouches F H Λ) (fun _ => 1)).firstRootLinearMayerDegreeSum
          (n + 1)‖) := by
  let M := plaquettePolymerModel Λ Φ β
  let touches := twoObservableRootTouches F H Λ
  let epsilon := twoObservableRootRegularizedActivity F H Λ Φ β
  apply M.summable_norm_firstRootLinearMayerDegreeSum_succ_of_scaled
    touches (fun _ => 1) epsilon
  · exact twoObservableRootRegularizedActivity_ne_zero F H Λ Φ β 0
  · simpa [M, touches, epsilon] using
      twoObservableRootModel_regularized_summable_normMayerDegreeSum_succ
        F H Λ Φ hβ

/-- Genuine absolute summability of the second one-root connected sector at
unit source. -/
theorem twoObservableRootModel_summable_norm_secondRootLinearMayerDegreeSum_succ
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable (fun n : ℕ ↦
      ‖((plaquettePolymerModel Λ Φ β).augmentRoots
        (twoObservableRootTouches F H Λ) (fun _ => 1)).secondRootLinearMayerDegreeSum
          (n + 1)‖) := by
  let M := plaquettePolymerModel Λ Φ β
  let touches := twoObservableRootTouches F H Λ
  let epsilon := twoObservableRootRegularizedActivity F H Λ Φ β
  apply M.summable_norm_secondRootLinearMayerDegreeSum_succ_of_scaled
    touches (fun _ => 1) epsilon
  · exact twoObservableRootRegularizedActivity_ne_zero F H Λ Φ β 1
  · simpa [M, touches, epsilon] using
      twoObservableRootModel_regularized_summable_normMayerDegreeSum_succ
        F H Λ Φ hβ

/-- Genuine KP/tree summability of the connected sector containing both
compatible labelled observable roots, at unit source activity. -/
theorem twoObservableRootModel_summable_norm_twoRootMixedMayerDegreeSum_succ
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable (fun n : ℕ ↦
      ‖twoObservableRootMixedMayerDegreeSum F H Λ Φ β (n + 1)‖) := by
  let M := plaquettePolymerModel Λ Φ β
  let touches := twoObservableRootTouches F H Λ
  let epsilon := twoObservableRootRegularizedActivity F H Λ Φ β
  apply M.summable_norm_twoRootMixedMayerDegreeSum_succ_of_scaled
    touches (fun _ => 1) epsilon
  · exact twoObservableRootRegularizedActivity_ne_zero F H Λ Φ β 0
  · exact twoObservableRootRegularizedActivity_ne_zero F H Λ Φ β 1
  · simpa [M, touches, epsilon] using
      twoObservableRootModel_regularized_summable_normMayerDegreeSum_succ
        F H Λ Φ hβ

/-- Exact deletion of the two unit-activity geometric observable roots.  The
remaining degree-`n` orbit is the genuinely two-pinned, root-free symmetric
tree sum. -/
theorem twoObservableRootModel_mixedMayerTreeDegreeSum_add_two
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (n : ℕ) :
    ((plaquettePolymerModel Λ Φ β).augmentRoots
      (twoObservableRootTouches F H Λ) (fun _ => 1)).twoRootMixedMayerTreeDegreeSum
        (n + 2) =
      ((plaquettePolymerModel Λ Φ β).augmentRoots
        (twoObservableRootTouches F H Λ) (fun _ => 0)).residualSymmetricTwoPinnedTreeDegreeSum
          n := by
  simpa using
    (plaquettePolymerModel Λ Φ β).twoRootMixedMayerTreeDegreeSum_add_two
      (twoObservableRootTouches F H Λ) (fun _ => 1) n

/-- The finite geometric two-source partition coefficient has the exact
connected decomposition, with every infinite Mayer series justified by the
explicit nonzero-root KP certificate above. -/
theorem twoObservableRootModel_mixedPartitionCoefficient_eq_vacuum_mul_connected
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    (plaquettePolymerModel Λ Φ β).twoRootMixedPartitionCoefficient
        (twoObservableRootTouches F H Λ) (fun _ => 1) =
      (plaquettePolymerModel Λ Φ β).twoRootVacuumPartitionCoefficient
          (twoObservableRootTouches F H Λ) (fun _ => 1) *
        ((∑' n : ℕ,
            twoObservableRootMixedMayerDegreeSum F H Λ Φ β n) +
          (∑' n : ℕ,
              ((plaquettePolymerModel Λ Φ β).augmentRoots
                (twoObservableRootTouches F H Λ) (fun _ => 1)).firstRootLinearMayerDegreeSum
                  n) *
            ∑' n : ℕ,
              ((plaquettePolymerModel Λ Φ β).augmentRoots
                (twoObservableRootTouches F H Λ) (fun _ => 1)).secondRootLinearMayerDegreeSum
                  n) := by
  refine YangMills.Polymer.FinitePolymerModel.twoRootMixedPartitionCoefficient_eq_vacuum_mul_connected
    (plaquettePolymerModel Λ Φ β)
    (twoObservableRootTouches F H Λ) (fun _ => 1) ?_ ?_ ?_
  · exact twoObservableRootModel_summable_norm_firstRootLinearMayerDegreeSum_succ
      F H Λ Φ hβ
  · exact twoObservableRootModel_summable_norm_secondRootLinearMayerDegreeSum_succ
      F H Λ Φ hβ
  · simpa [twoObservableRootMixedMayerDegreeSum] using
      twoObservableRootModel_summable_norm_twoRootMixedMayerDegreeSum_succ
        F H Λ Φ hβ

/-- Exact connected formal logarithm for the one-observable augmented gas.
This is the fixed-labelled Mayer exponential formula on the concrete source
type, before evaluating a source derivative at zero. -/
theorem oneObservableRootModel_restrictedSymmetricMayerPowerSeries_eq_formalMayerLog
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ) :
    (oneObservableRootModel F Λ Φ β α).restrictedSymmetricMayerPowerSeries
        Finset.univ =
      (oneObservableRootModel F Λ Φ β α).formalMayerLog Finset.univ := by
  exact (oneObservableRootModel F Λ Φ β α).restrictedSymmetricMayerPowerSeries_eq_formalMayerLog
    Finset.univ

/-- Exact connected formal logarithm for the two labelled observable roots. -/
theorem twoObservableRootModel_restrictedSymmetricMayerPowerSeries_eq_formalMayerLog
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) :
    (twoObservableRootModel F H Λ Φ β α θ).restrictedSymmetricMayerPowerSeries
        Finset.univ =
      (twoObservableRootModel F H Λ Φ β α θ).formalMayerLog Finset.univ := by
  exact (twoObservableRootModel F H Λ Φ β α θ).restrictedSymmetricMayerPowerSeries_eq_formalMayerLog
    Finset.univ

/-- Exact symmetric forest summability at the adjoined one-observable root. -/
theorem oneObservableRootModel_tsum_kpMayerForestDegreeSum_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) (h : ℕ) :
    ∑' k : ℕ,
        (oneObservableRootModel F Λ Φ β 0).kpMayerForestDegreeSum
          Finset.univ h (Sum.inr ()) k ≤
      Real.exp (oneObservableRootKPWeight F Λ Φ β (Sum.inr ())) := by
  exact (oneObservableRootModel F Λ Φ β 0).tsum_kpMayerForestDegreeSum_le_exp_of_koteckyPreiss
      Finset.univ (oneObservableRootKPWeight F Λ Φ β)
      (oneObservableRootModel_koteckyPreiss_zero F Λ Φ hβ)
      h (Sum.inr ()) (Finset.mem_univ _)

/-- Exact symmetric forest summability at either adjoined two-observable
root. -/
theorem twoObservableRootModel_tsum_kpMayerForestDegreeSum_le
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (h : ℕ) (r : Fin 2) :
    ∑' k : ℕ,
        (twoObservableRootModel F H Λ Φ β 0 0).kpMayerForestDegreeSum
          Finset.univ h (Sum.inr r) k ≤
      Real.exp (twoObservableRootKPWeight F H Λ Φ β (Sum.inr r)) := by
  exact (twoObservableRootModel F H Λ Φ β 0 0).tsum_kpMayerForestDegreeSum_le_exp_of_koteckyPreiss
      Finset.univ (twoObservableRootKPWeight F H Λ Φ β)
      (twoObservableRootModel_koteckyPreiss_zero F H Λ Φ hβ)
      h (Sum.inr r) (Finset.mem_univ _)

/-- The symmetry-normalized residual root-tree series is summable at the
one-observable root.  Removing the root activity before setting the source
to zero is the normalization needed for a source derivative. -/
theorem oneObservableRootModel_tsum_residualSymmetricPinnedTreeDegreeSum_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ∑' n : ℕ,
        (oneObservableRootModel F Λ Φ β 0).residualSymmetricPinnedTreeDegreeSum
          (Sum.inr ()) n ≤
      Real.exp (oneObservableRootKPWeight F Λ Φ β (Sum.inr ())) := by
  exact (oneObservableRootModel F Λ Φ β 0).tsum_residualSymmetricPinnedTreeDegreeSum_le_of_koteckyPreiss_certified
      (oneObservableRootKPWeight F Λ Φ β)
      (oneObservableRootModel_koteckyPreiss_zero F Λ Φ hβ) (Sum.inr ())

/-- The same residual rooted-tree estimate holds at either labelled source
of the two-observable gas.  These are the two one-root estimates entering
the eventual connected two-root cancellation argument. -/
theorem twoObservableRootModel_tsum_residualSymmetricPinnedTreeDegreeSum_le
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) (r : Fin 2) :
    ∑' n : ℕ,
        (twoObservableRootModel F H Λ Φ β 0 0).residualSymmetricPinnedTreeDegreeSum
          (Sum.inr r) n ≤
      Real.exp (twoObservableRootKPWeight F H Λ Φ β (Sum.inr r)) := by
  exact (twoObservableRootModel F H Λ Φ β 0 0).tsum_residualSymmetricPinnedTreeDegreeSum_le_of_koteckyPreiss_certified
      (twoObservableRootKPWeight F H Λ Φ β)
      (twoObservableRootModel_koteckyPreiss_zero F H Λ Φ hβ) (Sum.inr r)

/-- Uniform one-source residual tree budget with an explicit observable-
support prefactor. -/
theorem oneObservableRootModel_tsum_residualSymmetricPinnedTreeDegreeSum_le_support
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ∑' n : ℕ,
        (oneObservableRootModel F Λ Φ β 0).residualSymmetricPinnedTreeDegreeSum
          (Sum.inr ()) n ≤
      (2 : ℝ) ^ (4 * d * F.support.card) := by
  calc
    _ ≤ Real.exp (oneObservableRootKPWeight F Λ Φ β (Sum.inr ())) :=
      oneObservableRootModel_tsum_residualSymmetricPinnedTreeDegreeSum_le
        F Λ Φ hβ
    _ ≤ Real.exp (((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2) := by
      exact Real.exp_le_exp.mpr
        (oneObservableRootKPWeight_root_le_support F Λ Φ hβ)
    _ = (2 : ℝ) ^ (4 * d * F.support.card) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Explicit residual tree budget at the first source of the two-root gas. -/
theorem twoObservableRootModel_first_tsum_residualSymmetricPinnedTreeDegreeSum_le_support
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ∑' n : ℕ,
        (twoObservableRootModel F H Λ Φ β 0 0).residualSymmetricPinnedTreeDegreeSum
          (Sum.inr (0 : Fin 2)) n ≤
      (2 : ℝ) ^ (4 * d * F.support.card) := by
  calc
    _ ≤ Real.exp (twoObservableRootKPWeight F H Λ Φ β
        (Sum.inr (0 : Fin 2))) :=
      twoObservableRootModel_tsum_residualSymmetricPinnedTreeDegreeSum_le
        F H Λ Φ hβ 0
    _ ≤ Real.exp (((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2) := by
      exact Real.exp_le_exp.mpr
        (twoObservableRootKPWeight_first_root_le_support F H Λ Φ hβ)
    _ = (2 : ℝ) ^ (4 * d * F.support.card) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Explicit residual tree budget at the second source of the two-root gas. -/
theorem twoObservableRootModel_second_tsum_residualSymmetricPinnedTreeDegreeSum_le_support
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ∑' n : ℕ,
        (twoObservableRootModel F H Λ Φ β 0 0).residualSymmetricPinnedTreeDegreeSum
          (Sum.inr (1 : Fin 2)) n ≤
      (2 : ℝ) ^ (4 * d * H.support.card) := by
  calc
    _ ≤ Real.exp (twoObservableRootKPWeight F H Λ Φ β
        (Sum.inr (1 : Fin 2))) :=
      twoObservableRootModel_tsum_residualSymmetricPinnedTreeDegreeSum_le
        F H Λ Φ hβ 1
    _ ≤ Real.exp (((4 * d * H.support.card : ℕ) : ℝ) * Real.log 2) := by
      exact Real.exp_le_exp.mpr
        (twoObservableRootKPWeight_second_root_le_support F H Λ Φ hβ)
    _ = (2 : ℝ) ^ (4 * d * H.support.card) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- The complete positive-degree Mayer majorant for the one-root augmented
gas is summable directly from its standard KP certificate. -/
theorem oneObservableRootModel_summable_normMayerDegreeSum_succ
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable (fun n : ℕ ↦
      (oneObservableRootModel F Λ Φ β 0).normMayerDegreeSum (n + 1)) := by
  exact (oneObservableRootModel F Λ Φ β 0).summable_normMayerDegreeSum_succ_of_koteckyPreiss_certified
      (oneObservableRootKPWeight F Λ Φ β)
      (oneObservableRootModel_koteckyPreiss_zero F Λ Φ hβ)

/-- The complete positive-degree Mayer majorant for the two-root augmented
gas is likewise summable on the explicit lattice disk. -/
theorem twoObservableRootModel_summable_normMayerDegreeSum_succ
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable (fun n : ℕ ↦
      (twoObservableRootModel F H Λ Φ β 0 0).normMayerDegreeSum (n + 1)) := by
  exact (twoObservableRootModel F H Λ Φ β 0 0).summable_normMayerDegreeSum_succ_of_koteckyPreiss_certified
      (twoObservableRootKPWeight F H Λ Φ β)
      (twoObservableRootModel_koteckyPreiss_zero F H Λ Φ hβ)

/-! ## Concrete tree bounds for augmented observable-root clusters -/

/-- Every one-observable-root Mayer term is dominated by its sharp spanning-
tree majorant, with the exact augmented multi-index symmetry factor. -/
theorem oneObservableRootModel_norm_mayerClusterTerm_le_tree
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ)
    (X : FinitePolymerModel.MayerMultiIndex (PlaquettePolymer Λ ⊕ Unit)) :
    ‖(oneObservableRootModel F Λ Φ β α).mayerClusterTerm X‖ ≤
      (oneObservableRootModel F Λ Φ β α).mayerTreeMajorant X := by
  exact FinitePolymerModel.norm_mayerClusterTerm_le_mayerTreeMajorant
    (oneObservableRootModel F Λ Φ β α) X

/-- Multiplicity-pinned tree bound at the adjoined one-observable root. -/
theorem oneObservableRootModel_pinnedTreeBound
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ)
    (X : FinitePolymerModel.MayerMultiIndex (PlaquettePolymer Λ ⊕ Unit)) :
    (X (Sum.inr ()) : ℝ) *
        ‖(oneObservableRootModel F Λ Φ β α).mayerClusterTerm X‖ ≤
      (X (Sum.inr ()) : ℝ) *
        (oneObservableRootModel F Λ Φ β α).mayerTreeMajorant X := by
  exact FinitePolymerModel.pinned_norm_mayerClusterTerm_le_tree
    (oneObservableRootModel F Λ Φ β α) (Sum.inr ()) X

/-- The two-source augmented gas has the same sharp pinned tree domination at
each labelled observable root. -/
theorem twoObservableRootModel_pinnedTreeBound
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) (r : Fin 2)
    (X : FinitePolymerModel.MayerMultiIndex (PlaquettePolymer Λ ⊕ Fin 2)) :
    (X (Sum.inr r) : ℝ) *
        ‖(twoObservableRootModel F H Λ Φ β α θ).mayerClusterTerm X‖ ≤
      (X (Sum.inr r) : ℝ) *
        (twoObservableRootModel F H Λ Φ β α θ).mayerTreeMajorant X := by
  exact FinitePolymerModel.pinned_norm_mayerClusterTerm_le_tree
    (twoObservableRootModel F H Λ Φ β α θ) (Sum.inr r) X

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
