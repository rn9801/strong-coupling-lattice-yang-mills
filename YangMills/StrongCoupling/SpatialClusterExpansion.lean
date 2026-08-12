/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.BoundaryGeometry
import YangMills.StrongCoupling.MarkedComponentExpansion

/-!
# Spatially weighted strong-coupling cluster expansion

This file adds the plaquette-cardinality tilt used to convert the connected
observable-root Mayer expansion into spatial tails.  The tilt is chosen from
the strict slack in the existing explicit animal-counting/KP certificate; no
influence-matrix or Dobrushin comparison theorem is used.
-/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Polymer

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-! ## Strict scalar slack -/

/-- An explicit factor greater than one which keeps the cardinality-tilted
plaquette majorant inside the original animal-counting threshold. -/
def plaquetteCardinalityTilt
    (Φ : RealPlaquettePotential G) (β : ℂ) : ℝ :=
  let q := perturbationMajorant Φ β
  let T := dobrushinThreshold (16 * d) (2 ^ (16 * d))
  if q = 0 then 2 else (q + T) / (2 * q)

theorem one_lt_plaquetteCardinalityTilt
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    1 < plaquetteCardinalityTilt (d := d) Φ β := by
  let q := perturbationMajorant Φ β
  let T := dobrushinThreshold (16 * d) (2 ^ (16 * d))
  have hq : 0 ≤ q := perturbationMajorant_nonneg Φ β
  have hqT : q < T := by
    exact perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
      (16 * d) (2 ^ (16 * d)) hβ
  unfold plaquetteCardinalityTilt
  dsimp only
  split_ifs with hzero
  · norm_num
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
    apply (lt_div_iff₀ (mul_pos (by norm_num) hqpos)).2
    linarith

theorem plaquetteCardinalityTilt_nonneg
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    0 ≤ plaquetteCardinalityTilt (d := d) Φ β :=
  (one_lt_plaquetteCardinalityTilt Φ hβ).le.trans' zero_le_one

theorem plaquetteCardinalityTilt_mul_perturbationMajorant_lt_threshold
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    plaquetteCardinalityTilt (d := d) Φ β * perturbationMajorant Φ β <
      dobrushinThreshold (16 * d) (2 ^ (16 * d)) := by
  let q := perturbationMajorant Φ β
  let T := dobrushinThreshold (16 * d) (2 ^ (16 * d))
  have hqT : q < T := by
    exact perturbationMajorant_lt_dobrushinThreshold_of_norm_lt_radius Φ
      (16 * d) (2 ^ (16 * d)) hβ
  have hT : 0 < T := dobrushinThreshold_pos _ _
  unfold plaquetteCardinalityTilt
  dsimp only
  split_ifs with hzero
  · simpa [hzero] using
      (dobrushinThreshold_pos (16 * d) (2 ^ (16 * d)))
  · have hq : 0 ≤ q := perturbationMajorant_nonneg Φ β
    have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
    have heq : ((q + T) / (2 * q)) * q = (q + T) / 2 := by
      field_simp
    rw [heq]
    linarith

/-! ## Tilted bulk KP certificate -/

/-- Multiplying every bulk activity by `t ^ |support|` preserves the
quantitative quarter-budget KP estimate whenever `t*q` remains below the
same explicit animal threshold. -/
theorem plaquettePolymerModel_scaleByCard_kp_incompatible_sum_le_quarter
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) (β : ℂ)
    (t : ℝ) (ht : 0 ≤ t)
    (hsmall : t * perturbationMajorant Φ β <
      dobrushinThreshold (16 * d) (2 ^ (16 * d)))
    (γ : PlaquettePolymer Λ) :
    let Mt := (plaquettePolymerModel Λ Φ β).scaleByNatWeight
      (fun δ => δ.1.card) (t : ℂ)
    ∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
        (Mt.incompatible γ),
        ‖Mt.activity δ‖ * Real.exp (plaquetteKPWeight δ) ≤
      (γ.1.card : ℝ) * (Real.log 2 / 4) := by
  classical
  dsimp only
  let q := perturbationMajorant Φ β
  let r := t * q
  let cert := cubicPlaquetteAnimalCertificate Λ
  have hq : 0 ≤ q := perturbationMajorant_nonneg Φ β
  have hr : 0 ≤ r := mul_nonneg ht hq
  have hthreshold : r <
      dobrushinThreshold cert.degreeBound cert.animalConstant := by
    simpa [r, q, cert] using hsmall
  rw [dobrushinThreshold, lt_min_iff, lt_min_iff] at hthreshold
  rcases hthreshold with ⟨_hrEight, hrAnimal, hrDegree⟩
  have hCr : (cert.animalConstant : ℝ) * (2 * r) < 1 := by
    have hCnonneg : 0 ≤ (cert.animalConstant : ℝ) := by positivity
    have hdenpos : 0 < (16 : ℝ) * (cert.animalConstant + 1) := by
      positivity
    have hmul := (lt_div_iff₀ hdenpos).mp hrAnimal
    nlinarith
  have hsum := sum_incompatiblePlaquettePolymerWeights_le
    Λ cert γ (mul_nonneg (by norm_num) hr) hCr
  have hpoint : ∀ δ : PlaquettePolymer Λ,
      ‖((plaquettePolymerModel Λ Φ β).scaleByNatWeight
          (fun η => η.1.card) (t : ℂ)).activity δ‖ *
          Real.exp (plaquetteKPWeight δ) ≤
        (2 * r) ^ δ.1.card := by
    intro δ
    have hactivity := norm_plaquettePolymer_activity_le Λ Φ β δ
    have hexp : Real.exp (plaquetteKPWeight δ) =
        (2 : ℝ) ^ δ.1.card := by
      rw [plaquetteKPWeight, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [hexp]
    change ‖(t : ℂ) ^ δ.1.card *
        (plaquettePolymerModel Λ Φ β).activity δ‖ *
          (2 : ℝ) ^ δ.1.card ≤ _
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht]
    calc
      (t ^ δ.1.card * ‖(plaquettePolymerModel Λ Φ β).activity δ‖) *
          (2 : ℝ) ^ δ.1.card ≤
        (t ^ δ.1.card * q ^ δ.1.card) * (2 : ℝ) ^ δ.1.card := by
          gcongr
          simpa [q, PlaquettePolymer.support] using hactivity
      _ = (2 * r) ^ δ.1.card := by
        simp only [r, mul_pow]
        ring
  have hweighted :
      ∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
          ((plaquettePolymerModel Λ Φ β).incompatible γ),
          ‖((plaquettePolymerModel Λ Φ β).scaleByNatWeight
              (fun η => η.1.card) (t : ℂ)).activity δ‖ *
            Real.exp (plaquetteKPWeight δ) ≤
        (γ.1.card : ℝ) * (cert.degreeBound + 1) *
          ((2 * r) /
            (1 - (cert.animalConstant : ℝ) * (2 * r))) := by
    calc
      _ ≤ ∑ δ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
            (plaquettePolymerIncompatible Λ γ),
            (2 * r) ^ δ.1.card := by
          apply Finset.sum_le_sum
          intro δ _
          exact hpoint δ
      _ ≤ _ := hsum
  have hfrac :
      (2 * r) / (1 - (cert.animalConstant : ℝ) * (2 * r)) ≤ 4 * r := by
    have hCnonneg : 0 ≤ (cert.animalConstant : ℝ) := by positivity
    have hdenpos : 0 < (16 : ℝ) * (cert.animalConstant + 1) := by
      positivity
    have hmul := (lt_div_iff₀ hdenpos).mp hrAnimal
    have hhalf : (cert.animalConstant : ℝ) * (2 * r) ≤ 1 / 2 := by
      nlinarith
    have hden : 0 < 1 - (cert.animalConstant : ℝ) * (2 * r) := by
      linarith
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hlocal :
      (cert.degreeBound + 1 : ℝ) * (4 * r) ≤ Real.log 2 / 4 := by
    have hdenpos : 0 < (16 : ℝ) * (cert.degreeBound + 1) := by
      positivity
    have hmul := (lt_div_iff₀ hdenpos).mp hrDegree
    have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  calc
    _ ≤ (γ.1.card : ℝ) * (cert.degreeBound + 1) *
        ((2 * r) /
          (1 - (cert.animalConstant : ℝ) * (2 * r))) := by
      simpa [Polymer.FinitePolymerModel.scaleByNatWeight] using hweighted
    _ ≤ (γ.1.card : ℝ) * (cert.degreeBound + 1) * (4 * r) := by
      gcongr
    _ = (γ.1.card : ℝ) *
        ((cert.degreeBound + 1 : ℝ) * (4 * r)) := by ring
    _ ≤ (γ.1.card : ℝ) * (Real.log 2 / 4) :=
      mul_le_mul_of_nonneg_left hlocal (Nat.cast_nonneg _)

/-- Genuine KP certificate for the explicitly chosen cardinality tilt of
the bulk plaquette gas. -/
theorem plaquettePolymerModel_cardinalityTilt_koteckyPreiss
    (Λ : FiniteSpecification d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ((plaquettePolymerModel Λ Φ β).scaleByNatWeight
      (fun γ => γ.1.card)
      (plaquetteCardinalityTilt (d := d) Φ β : ℂ)).KoteckyPreissCertificate
        Finset.univ plaquetteKPWeight := by
  let t := plaquetteCardinalityTilt (d := d) Φ β
  have ht : 0 ≤ t := plaquetteCardinalityTilt_nonneg Φ hβ
  have hsmall : t * perturbationMajorant Φ β <
      dobrushinThreshold (16 * d) (2 ^ (16 * d)) :=
    plaquetteCardinalityTilt_mul_perturbationMajorant_lt_threshold Φ hβ
  refine ⟨?_, ?_⟩
  · intro γ
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num)).le
  · intro γ _hγ
    have hquarter :=
      plaquettePolymerModel_scaleByCard_kp_incompatible_sum_le_quarter
        Λ Φ β t ht hsmall γ
    have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    calc
      _ ≤ (γ.1.card : ℝ) * (Real.log 2 / 4) := hquarter
      _ ≤ (γ.1.card : ℝ) * Real.log 2 := by
        gcongr
        nlinarith
      _ = plaquetteKPWeight γ := rfl

/-! ## The support weight on the exact two-observable gas -/

/-- Number of plaquettes carried by each kind of polymer in the exact
bivariate decorated gas.  Complete source decorations are charged for every
plaquette they absorb. -/
def bivariateDecoratedObservablePlaquetteCardinality
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G) :
    (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) → ℕ
  | Sum.inl (Sum.inl (Sum.inl γ)) => γ.1.card
  | Sum.inl (Sum.inl (Sum.inr D)) => D.support.card
  | Sum.inl (Sum.inr E) => E.support.card
  | Sum.inr B => B.support.card

/-- The exact decorated gas with every activity multiplied by the explicit
plaquette-cardinality tilt. -/
def bivariateDecoratedObservableCardinalityTiltedModel
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) :=
  (bivariateDecoratedObservableRootModel F H Λ Φ β α θ).scaleByNatWeight
    (bivariateDecoratedObservablePlaquetteCardinality F H Λ)
    (plaquetteCardinalityTilt (d := d) Φ β : ℂ)

@[simp]
theorem bivariateDecoratedObservableCardinalityTiltedModel_bulk_activity
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ)
    (γ : PlaquettePolymer Λ) :
    (bivariateDecoratedObservableCardinalityTiltedModel
      F H Λ Φ β α θ).activity (Sum.inl (Sum.inl (Sum.inl γ))) =
      (plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ γ.1.card *
        (plaquettePolymerModel Λ Φ β).activity γ := rfl

@[simp]
theorem bivariateDecoratedObservableCardinalityTiltedModel_left_activity
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ)
    (D : ObservableRootDecoration F Λ) :
    (bivariateDecoratedObservableCardinalityTiltedModel
      F H Λ Φ β α θ).activity (Sum.inl (Sum.inl (Sum.inr D))) =
      (plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ D.support.card *
        (α * markedSubsetWeight F Λ Φ β D.support) := rfl

@[simp]
theorem bivariateDecoratedObservableCardinalityTiltedModel_right_activity
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ)
    (E : ObservableRootDecoration H Λ) :
    (bivariateDecoratedObservableCardinalityTiltedModel
      F H Λ Φ β α θ).activity (Sum.inl (Sum.inr E)) =
      (plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ E.support.card *
        (θ * markedSubsetWeight H Λ Φ β E.support) := rfl

@[simp]
theorem bivariateDecoratedObservableCardinalityTiltedModel_bridge_activity
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ)
    (B : TwoObservableBridgeDecoration F H Λ) :
    (bivariateDecoratedObservableCardinalityTiltedModel
      F H Λ Φ β α θ).activity (Sum.inr B) =
      (plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ B.support.card *
        (α * θ * markedSubsetWeight (F.mul H) Λ Φ β B.support) := rfl

/-- Zero-source KP weight for the cardinality-tilted decorated gas.  Source
roots receive their exact touching mass from the already tilted bulk gas. -/
def bivariateDecoratedObservableCardinalityTiltKPWeight
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) → ℝ :=
  let M := (plaquettePolymerModel Λ Φ β).scaleByNatWeight
    (fun γ => γ.1.card) (plaquetteCardinalityTilt (d := d) Φ β : ℂ)
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
theorem bivariateDecoratedObservableCardinalityTiltKPWeight_bulk
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (γ : PlaquettePolymer Λ) :
    bivariateDecoratedObservableCardinalityTiltKPWeight F H Λ Φ β
        (Sum.inl (Sum.inl (Sum.inl γ))) = plaquetteKPWeight γ := rfl

theorem bivariateDecoratedObservableCardinalityTiltKPWeight_nonneg
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ∀ q, 0 ≤
      bivariateDecoratedObservableCardinalityTiltKPWeight F H Λ Φ β q := by
  let M := (plaquettePolymerModel Λ Φ β).scaleByNatWeight
    (fun γ => γ.1.card) (plaquetteCardinalityTilt (d := d) Φ β : ℂ)
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
  have hbase := plaquettePolymerModel_cardinalityTilt_koteckyPreiss
    Λ Φ hβ
  have hleft : ∀ q, 0 ≤ aleft q :=
    M.augmentRootKPWeight_nonneg
      (observableRootDecorationTouches F Λ) plaquetteKPWeight hbase.1
  have hright : ∀ q, 0 ≤ aright q :=
    Mleft.augmentRootKPWeight_nonneg
      (Polymer.FinitePolymerModel.twoColorRightTouches
        (observableRootDecorationTouches H Λ)
        (observableRootDecorationsCrossIncompatible F H Λ)) aleft hleft
  simpa only [bivariateDecoratedObservableCardinalityTiltKPWeight,
    M, Mleft, Mright, aleft, aright] using
      Mright.augmentRootKPWeight_nonneg
        (Polymer.FinitePolymerModel.bivariateBridgeTouches
          (fun (B : TwoObservableBridgeDecoration F H Λ) γ =>
            observableRootDecorationTouches (F.mul H) Λ B.1 γ))
        aright hright

/-- The complete cardinality-tilted decorated gas inherits the tilted bulk
KP certificate at zero source. -/
theorem bivariateDecoratedObservableCardinalityTiltedModel_koteckyPreiss_zero
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    (bivariateDecoratedObservableCardinalityTiltedModel
      F H Λ Φ β 0 0).KoteckyPreissCertificate Finset.univ
        (bivariateDecoratedObservableCardinalityTiltKPWeight
          F H Λ Φ β) := by
  classical
  let M := (plaquettePolymerModel Λ Φ β).scaleByNatWeight
    (fun γ => γ.1.card) (plaquetteCardinalityTilt (d := d) Φ β : ℂ)
  have hbase : M.KoteckyPreissCertificate Finset.univ plaquetteKPWeight := by
    exact plaquettePolymerModel_cardinalityTilt_koteckyPreiss Λ Φ hβ
  let Mleft := M.augmentExclusiveRoots
    (observableRootDecorationTouches F Λ) (fun _ => 0)
  let aleft := M.augmentRootKPWeight
    (observableRootDecorationTouches F Λ) plaquetteKPWeight
  have hleft : Mleft.KoteckyPreissCertificate Finset.univ aleft :=
    M.koteckyPreissCertificate_augmentExclusiveRoots_zero
      (observableRootDecorationTouches F Λ) plaquetteKPWeight hbase
  let Mright := Mleft.augmentExclusiveRoots
    (Polymer.FinitePolymerModel.twoColorRightTouches
      (observableRootDecorationTouches H Λ)
      (observableRootDecorationsCrossIncompatible F H Λ)) (fun _ => 0)
  let aright := Mleft.augmentRootKPWeight
    (Polymer.FinitePolymerModel.twoColorRightTouches
      (observableRootDecorationTouches H Λ)
      (observableRootDecorationsCrossIncompatible F H Λ)) aleft
  have hright : Mright.KoteckyPreissCertificate Finset.univ aright :=
    Mleft.koteckyPreissCertificate_augmentExclusiveRoots_zero
      (Polymer.FinitePolymerModel.twoColorRightTouches
        (observableRootDecorationTouches H Λ)
        (observableRootDecorationsCrossIncompatible F H Λ)) aleft hleft
  let bridgeTouches : TwoObservableBridgeDecoration F H Λ →
      ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
        ObservableRootDecoration H Λ) → Prop :=
    Polymer.FinitePolymerModel.bivariateBridgeTouches
      (fun (B : TwoObservableBridgeDecoration F H Λ) γ =>
        observableRootDecorationTouches (F.mul H) Λ B.1 γ)
  let Mbridge := Mright.augmentExclusiveRoots bridgeTouches (fun _ => 0)
  let abridge := Mright.augmentRootKPWeight bridgeTouches aright
  have hbridge : Mbridge.KoteckyPreissCertificate Finset.univ abridge :=
    Mright.koteckyPreissCertificate_augmentExclusiveRoots_zero
      bridgeTouches aright hright
  refine ⟨?_, ?_⟩
  · simpa only [bivariateDecoratedObservableCardinalityTiltKPWeight,
      bridgeTouches, abridge, M, Mleft, Mright, aleft, aright] using hbridge.1
  · intro q _hq
    have hq := hbridge.2 q (Finset.mem_univ q)
    rw [Finset.sum_filter] at hq ⊢
    simpa [bivariateDecoratedObservableCardinalityTiltedModel,
      bivariateDecoratedObservablePlaquetteCardinality,
      bivariateDecoratedObservableRootModel,
      bivariateDecoratedObservableCardinalityTiltKPWeight,
      Polymer.FinitePolymerModel.scaleByNatWeight,
      Polymer.FinitePolymerModel.augmentBivariateExclusiveRoots,
      Polymer.FinitePolymerModel.augmentTwoColorExclusiveRoots,
      Polymer.FinitePolymerModel.augmentExclusiveRoots,
      M, Mleft, Mright, aleft, aright, bridgeTouches, Mbridge, abridge]
      using hq

/-! ## Uniform tilted decoration budgets -/

/-- The zero-source KP weight for one complete observable decoration after
the plaquette-cardinality tilt. -/
def decoratedObservableCardinalityTiltKPWeight
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ → ℝ :=
  ((plaquettePolymerModel Λ Φ β).scaleByNatWeight
      (fun γ => γ.1.card)
      (plaquetteCardinalityTilt (d := d) Φ β : ℂ)).augmentRootKPWeight
    (observableRootDecorationTouches F Λ) plaquetteKPWeight

@[simp]
theorem bivariateDecoratedObservableCardinalityTiltKPWeight_left
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (D : ObservableRootDecoration F Λ) :
    bivariateDecoratedObservableCardinalityTiltKPWeight F H Λ Φ β
        (Sum.inl (Sum.inl (Sum.inr D))) =
      decoratedObservableCardinalityTiltKPWeight F Λ Φ β (Sum.inr D) := by
  rfl

@[simp]
theorem bivariateDecoratedObservableCardinalityTiltKPWeight_right
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (E : ObservableRootDecoration H Λ) :
    bivariateDecoratedObservableCardinalityTiltKPWeight F H Λ Φ β
        (Sum.inl (Sum.inr E)) =
      decoratedObservableCardinalityTiltKPWeight H Λ Φ β (Sum.inr E) := by
  classical
  simp [bivariateDecoratedObservableCardinalityTiltKPWeight,
    decoratedObservableCardinalityTiltKPWeight,
    Polymer.FinitePolymerModel.augmentRootKPWeight,
    Polymer.FinitePolymerModel.twoColorRightTouches]

@[simp]
theorem bivariateDecoratedObservableCardinalityTiltKPWeight_bridge
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (B : TwoObservableBridgeDecoration F H Λ) :
    bivariateDecoratedObservableCardinalityTiltKPWeight F H Λ Φ β
        (Sum.inr B) =
      decoratedObservableCardinalityTiltKPWeight (F.mul H) Λ Φ β
        (Sum.inr B.1) := by
  classical
  simp [bivariateDecoratedObservableCardinalityTiltKPWeight,
    decoratedObservableCardinalityTiltKPWeight,
    Polymer.FinitePolymerModel.augmentRootKPWeight,
    Polymer.FinitePolymerModel.bivariateBridgeTouches,
    Polymer.FinitePolymerModel.twoColorRightTouches]

/-- The tilted bulk mass of all polymers touching an observable is bounded by
one singleton KP budget per incident plaquette. -/
theorem cardinalityTiltedObservableTouchingMass_le_card_mul_log_two
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let M := (plaquettePolymerModel Λ Φ β).scaleByNatWeight
      (fun γ => γ.1.card)
      (plaquetteCardinalityTilt (d := d) Φ β : ℂ)
    (∑ γ : PlaquettePolymer Λ,
      if observableRootTouches F Λ γ then
        ‖M.activity γ‖ * Real.exp (plaquetteKPWeight γ) else 0) ≤
      ((observableRootPlaquettes Λ F).card : ℝ) * Real.log 2 := by
  classical
  dsimp only
  let M := (plaquettePolymerModel Λ Φ β).scaleByNatWeight
    (fun γ => γ.1.card)
    (plaquetteCardinalityTilt (d := d) Φ β : ℂ)
  let R := observableRootPlaquettes Λ F
  let w : PlaquettePolymer Λ → ℝ := fun γ =>
    ‖M.activity γ‖ * Real.exp (plaquetteKPWeight γ)
  have hKP : M.KoteckyPreissCertificate Finset.univ plaquetteKPWeight := by
    simpa [M] using
      (plaquettePolymerModel_cardinalityTilt_koteckyPreiss Λ Φ hβ)
  have hpoint : ∀ γ : PlaquettePolymer Λ,
      (if observableRootTouches F Λ γ then w γ else 0) ≤
        ∑ p ∈ R, if p ∈ γ.1 then w γ else 0 := by
    intro γ
    by_cases htouch : observableRootTouches F Λ γ
    · obtain ⟨p, hpγ, hpR⟩ := (observableRootTouches_iff F Λ γ).mp htouch
      rw [if_pos htouch]
      have hnonneg : ∀ q ∈ R,
          0 ≤ if q ∈ γ.1 then w γ else 0 := by
        intro q _
        split_ifs
        · exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
        · exact le_rfl
      calc
        w γ = if p ∈ γ.1 then w γ else 0 := by simp [hpγ]
        _ ≤ ∑ q ∈ R, if q ∈ γ.1 then w γ else 0 :=
          Finset.single_le_sum hnonneg hpR
    · rw [if_neg htouch]
      exact Finset.sum_nonneg fun p _ => by
        split_ifs
        · exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
        · exact le_rfl
  have hsingle : ∀ p ∈ R,
      (∑ γ : PlaquettePolymer Λ, if p ∈ γ.1 then w γ else 0) ≤
        Real.log 2 := by
    intro p _hpR
    have h := hKP.2 (singletonPlaquettePolymer Λ p) (Finset.mem_univ _)
    rw [Finset.sum_filter] at h
    have hdom :
        (∑ γ : PlaquettePolymer Λ, if p ∈ γ.1 then w γ else 0) ≤
          ∑ γ : PlaquettePolymer Λ,
            if M.incompatible (singletonPlaquettePolymer Λ p) γ then
              w γ else 0 := by
      apply Finset.sum_le_sum
      intro γ _
      by_cases hpγ : p ∈ γ.1
      · have hinc : M.incompatible (singletonPlaquettePolymer Λ p) γ := by
          simpa [M, Polymer.FinitePolymerModel.scaleByNatWeight] using
            singletonPlaquettePolymer_incompatible_of_mem Λ Φ β p γ hpγ
        simp [hpγ, hinc]
      · simp [hpγ]
        positivity
    calc
      (∑ γ : PlaquettePolymer Λ, if p ∈ γ.1 then w γ else 0) ≤
          ∑ γ : PlaquettePolymer Λ,
            if M.incompatible (singletonPlaquettePolymer Λ p) γ then
              w γ else 0 := hdom
      _ ≤ plaquetteKPWeight (singletonPlaquettePolymer Λ p) := by
        simpa [w] using h
      _ = Real.log 2 := by simp [plaquetteKPWeight]
  change (∑ γ : PlaquettePolymer Λ,
      if observableRootTouches F Λ γ then w γ else 0) ≤
    (R.card : ℝ) * Real.log 2
  calc
    _ ≤ ∑ γ : PlaquettePolymer Λ,
        ∑ p ∈ R, if p ∈ γ.1 then w γ else 0 :=
      Finset.sum_le_sum fun γ _ => hpoint γ
    _ = ∑ p ∈ R,
        ∑ γ : PlaquettePolymer Λ, if p ∈ γ.1 then w γ else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _p ∈ R, Real.log 2 := Finset.sum_le_sum hsingle
    _ = (R.card : ℝ) * Real.log 2 := by simp

/-- A complete tilted decoration pays the linear observable-root budget plus
the ordinary KP weights of the mutually compatible polymers absorbed into
the decoration. -/
theorem decoratedObservableCardinalityTiltKPWeight_root_le_support_add_decoration
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (D : ObservableRootDecoration F Λ) :
    decoratedObservableCardinalityTiltKPWeight F Λ Φ β (Sum.inr D) ≤
      (4 * d * F.support.card : ℕ) * Real.log 2 +
        ∑ δ ∈ D.1, plaquetteKPWeight δ := by
  classical
  let M := (plaquettePolymerModel Λ Φ β).scaleByNatWeight
    (fun γ => γ.1.card)
    (plaquetteCardinalityTilt (d := d) Φ β : ℂ)
  let w : PlaquettePolymer Λ → ℝ := fun γ =>
    ‖M.activity γ‖ * Real.exp (plaquetteKPWeight γ)
  have hKP : M.KoteckyPreissCertificate Finset.univ plaquetteKPWeight := by
    simpa [M] using
      (plaquettePolymerModel_cardinalityTilt_koteckyPreiss Λ Φ hβ)
  have hpoint (γ : PlaquettePolymer Λ) :
      (if observableRootDecorationTouches F Λ D γ then w γ else 0) ≤
        (if observableRootTouches F Λ γ then w γ else 0) +
          ∑ δ ∈ D.1,
            if plaquettePolymerIncompatible Λ δ γ then w γ else 0 := by
    by_cases hroot : observableRootTouches F Λ γ
    · have htouch : observableRootDecorationTouches F Λ D γ := Or.inl hroot
      rw [if_pos htouch, if_pos hroot]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
    · by_cases hdecoration :
          ∃ δ ∈ D.1, plaquettePolymerIncompatible Λ δ γ
      · rcases hdecoration with ⟨δ, hδ, hinc⟩
        have htouch : observableRootDecorationTouches F Λ D γ :=
          Or.inr ⟨δ, hδ, hinc⟩
        rw [if_pos htouch, if_neg hroot, zero_add]
        have hnonneg : ∀ η ∈ D.1,
            0 ≤ if plaquettePolymerIncompatible Λ η γ then w γ else 0 := by
          intro η _
          split_ifs
          · positivity
          · exact le_rfl
        calc
          w γ = if plaquettePolymerIncompatible Λ δ γ then w γ else 0 := by
            rw [if_pos hinc]
          _ ≤ ∑ η ∈ D.1,
              if plaquettePolymerIncompatible Λ η γ then w γ else 0 :=
            Finset.single_le_sum hnonneg hδ
      · have hnot : ¬observableRootDecorationTouches F Λ D γ := by
          rintro (h | h)
          · exact hroot h
          · exact hdecoration h
        rw [if_neg hnot, if_neg hroot, zero_add]
        exact Finset.sum_nonneg fun _ _ => by
          split_ifs
          · positivity
          · exact le_rfl
  have hincompatible (δ : PlaquettePolymer Λ) :
      (∑ γ : PlaquettePolymer Λ,
          if plaquettePolymerIncompatible Λ δ γ then w γ else 0) ≤
        plaquetteKPWeight δ := by
    have h := hKP.2 δ (Finset.mem_univ δ)
    rw [Finset.sum_filter] at h
    simpa [M, w, Polymer.FinitePolymerModel.scaleByNatWeight] using h
  have hbase :
      (∑ γ : PlaquettePolymer Λ,
          if observableRootTouches F Λ γ then w γ else 0) ≤
        (4 * d * F.support.card : ℕ) * Real.log 2 := by
    calc
      _ ≤ ((observableRootPlaquettes Λ F).card : ℝ) * Real.log 2 := by
        simpa [M, w] using
          (cardinalityTiltedObservableTouchingMass_le_card_mul_log_two
            F Λ Φ hβ)
      _ ≤ (4 * d * F.support.card : ℕ) * Real.log 2 := by
        gcongr
        exact_mod_cast card_observableRootPlaquettes_le Λ F
  change (∑ γ : PlaquettePolymer Λ,
      if observableRootDecorationTouches F Λ D γ then w γ else 0) ≤ _
  calc
    _ ≤ ∑ γ : PlaquettePolymer Λ,
        ((if observableRootTouches F Λ γ then w γ else 0) +
          ∑ δ ∈ D.1,
            if plaquettePolymerIncompatible Λ δ γ then w γ else 0) :=
      Finset.sum_le_sum fun γ _ => hpoint γ
    _ = (∑ γ : PlaquettePolymer Λ,
          if observableRootTouches F Λ γ then w γ else 0) +
        ∑ δ ∈ D.1,
          ∑ γ : PlaquettePolymer Λ,
            if plaquettePolymerIncompatible Λ δ γ then w γ else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ (4 * d * F.support.card : ℕ) * Real.log 2 +
        ∑ δ ∈ D.1, plaquetteKPWeight δ := by
      exact add_le_add hbase
        (Finset.sum_le_sum fun δ _ => hincompatible δ)

/-- Uniform animal bound at the cardinality-tilted activity.  The strict
slack built into `plaquetteCardinalityTilt` makes the displayed denominator
positive. -/
theorem sum_observableRoot_cardinalityTiltedAnimalWeight_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let r := plaquetteCardinalityTilt (d := d) Φ β *
      perturbationMajorant Φ β
    ∑ γ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
        (observableRootTouches F Λ),
        (2 * r) ^ γ.1.card ≤
      ((observableRootPlaquettes Λ F).card : ℝ) *
        ((2 * r) /
          (1 - (2 ^ (16 * d) : ℝ) * (2 * r))) := by
  classical
  dsimp only
  let r := plaquetteCardinalityTilt (d := d) Φ β *
    perturbationMajorant Φ β
  let q : ℝ := 2 * r
  let R := observableRootPlaquettes Λ F
  let cert := cubicPlaquetteAnimalCertificate Λ
  have hr : 0 ≤ r := mul_nonneg
    (plaquetteCardinalityTilt_nonneg Φ hβ)
    (perturbationMajorant_nonneg Φ β)
  have hthreshold : r <
      dobrushinThreshold cert.degreeBound cert.animalConstant := by
    simpa [r, cert] using
      plaquetteCardinalityTilt_mul_perturbationMajorant_lt_threshold Φ hβ
  have hsmall : (cert.animalConstant : ℝ) * q < 1 := by
    rw [dobrushinThreshold, lt_min_iff, lt_min_iff] at hthreshold
    rcases hthreshold with ⟨_hrEight, hrAnimal, _hrDegree⟩
    have hdenpos : 0 < (16 : ℝ) * (cert.animalConstant + 1) := by
      positivity
    have hmul := (lt_div_iff₀ hdenpos).mp hrAnimal
    dsimp only [q]
    nlinarith
  have hq : 0 ≤ q := mul_nonneg (by norm_num) hr
  have hpoint (γ : PlaquettePolymer Λ) :
      (if observableRootTouches F Λ γ then q ^ γ.1.card else 0) ≤
        ∑ p ∈ R, if p ∈ γ.1 then q ^ γ.1.card else 0 := by
    by_cases htouch : observableRootTouches F Λ γ
    · obtain ⟨p, hpγ, hpR⟩ := (observableRootTouches_iff F Λ γ).mp htouch
      rw [if_pos htouch]
      have hnonneg : ∀ s ∈ R,
          0 ≤ if s ∈ γ.1 then q ^ γ.1.card else 0 := by
        intro s _
        split_ifs
        · exact pow_nonneg hq _
        · exact le_rfl
      calc
        q ^ γ.1.card = if p ∈ γ.1 then q ^ γ.1.card else 0 := by
          simp [hpγ]
        _ ≤ ∑ s ∈ R, if s ∈ γ.1 then q ^ γ.1.card else 0 :=
          Finset.single_le_sum hnonneg hpR
    · rw [if_neg htouch]
      exact Finset.sum_nonneg fun p _ => by
        split_ifs
        · exact pow_nonneg hq _
        · exact le_rfl
  have hroot (p : ActivePlaquette Λ) :
      (∑ γ : PlaquettePolymer Λ,
          if p ∈ γ.1 then q ^ γ.1.card else 0) ≤
        q / (1 - (cert.animalConstant : ℝ) * q) := by
    rw [← Finset.sum_filter]
    exact sum_rootedPlaquettePolymerWeights_le Λ cert p hq hsmall
  suffices hbound :
      (∑ γ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
          (observableRootTouches F Λ), q ^ γ.1.card) ≤
        (R.card : ℝ) *
          (q / (1 - (cert.animalConstant : ℝ) * q)) by
    simpa [q, r, R, cert] using hbound
  rw [Finset.sum_filter]
  calc
    (∑ γ : PlaquettePolymer Λ,
        if observableRootTouches F Λ γ then q ^ γ.1.card else 0) ≤
      ∑ γ : PlaquettePolymer Λ,
        ∑ p ∈ R, if p ∈ γ.1 then q ^ γ.1.card else 0 :=
      Finset.sum_le_sum fun γ _ => hpoint γ
    _ = ∑ p ∈ R, ∑ γ : PlaquettePolymer Λ,
        if p ∈ γ.1 then q ^ γ.1.card else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _p ∈ R,
        q / (1 - (cert.animalConstant : ℝ) * q) :=
      Finset.sum_le_sum fun p _ => hroot p
    _ = (R.card : ℝ) *
        (q / (1 - (cert.animalConstant : ℝ) * q)) := by simp

/-- Termwise tilted decoration estimate.  It is the exact analogue of the
untilted marked-root estimate, with `t * perturbationMajorant` replacing the
original plaquette majorant. -/
theorem norm_cardinalityTiltedMarkedSubsetWeight_mul_exp_rootKPWeight_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (D : ObservableRootDecoration F Λ) :
    ‖(plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ D.support.card *
        markedSubsetWeight F Λ Φ β D.support‖ *
        Real.exp
          (decoratedObservableCardinalityTiltKPWeight
            F Λ Φ β (Sum.inr D)) ≤
      ‖F.toBoundedContinuousMap‖ *
        Real.exp (((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2) *
        ∏ δ ∈ D.1,
          (2 * (plaquetteCardinalityTilt (d := d) Φ β *
            perturbationMajorant Φ β)) ^ δ.1.card := by
  classical
  let t := plaquetteCardinalityTilt (d := d) Φ β
  let q := perturbationMajorant Φ β
  let r := t * q
  let b : ℝ := ((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2
  let s : ℝ := ∑ δ ∈ D.1, plaquetteKPWeight δ
  have ht : 0 ≤ t := plaquetteCardinalityTilt_nonneg Φ hβ
  have hq : 0 ≤ q := perturbationMajorant_nonneg Φ β
  have hr : 0 ≤ r := mul_nonneg ht hq
  have hmarked : ‖markedSubsetWeight F Λ Φ β D.support‖ ≤
      ‖F.toBoundedContinuousMap‖ * q ^ D.support.card := by
    simpa [q] using norm_markedSubsetWeight_le F Λ Φ β D.support
  have hroot :
      decoratedObservableCardinalityTiltKPWeight
          F Λ Φ β (Sum.inr D) ≤ b + s := by
    simpa [b, s] using
      decoratedObservableCardinalityTiltKPWeight_root_le_support_add_decoration
        F Λ Φ hβ D
  have hrpower : r ^ D.support.card =
      ∏ δ ∈ D.1, r ^ δ.1.card := by
    rw [D.card_support]
    exact (Finset.prod_pow_eq_pow_sum D.1 (fun δ => δ.1.card) r).symm
  have hexps : Real.exp s = ∏ δ ∈ D.1, (2 : ℝ) ^ δ.1.card := by
    dsimp [s]
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro δ _
    rw [plaquetteKPWeight, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht]
  calc
    (t ^ D.support.card * ‖markedSubsetWeight F Λ Φ β D.support‖) *
          Real.exp
            (decoratedObservableCardinalityTiltKPWeight
              F Λ Φ β (Sum.inr D)) ≤
        (t ^ D.support.card *
          (‖F.toBoundedContinuousMap‖ * q ^ D.support.card)) *
            Real.exp (b + s) := by
      gcongr
    _ = ‖F.toBoundedContinuousMap‖ * Real.exp b *
        ∏ δ ∈ D.1, (2 * r) ^ δ.1.card := by
      rw [Real.exp_add, hexps]
      calc
        t ^ D.support.card *
              (‖F.toBoundedContinuousMap‖ * q ^ D.support.card) *
              (Real.exp b * ∏ δ ∈ D.1, (2 : ℝ) ^ δ.1.card) =
            ‖F.toBoundedContinuousMap‖ * Real.exp b *
              ((t * q) ^ D.support.card *
                ∏ δ ∈ D.1, (2 : ℝ) ^ δ.1.card) := by
          rw [mul_pow]
          ring
        _ = ‖F.toBoundedContinuousMap‖ * Real.exp b *
              ((∏ δ ∈ D.1, r ^ δ.1.card) *
                ∏ δ ∈ D.1, (2 : ℝ) ^ δ.1.card) := by
          rw [show t * q = r by rfl, hrpower]
        _ = ‖F.toBoundedContinuousMap‖ * Real.exp b *
              ∏ δ ∈ D.1, (2 * r) ^ δ.1.card := by
          congr 1
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro δ _
          rw [← mul_pow]
          congr 1
          ring
    _ = _ := by rfl

/-- Explicit box-independent upper bound for the complete tilted decoration
mass of one observable. -/
def observableCardinalityTiltDecorationBudget
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℂ) : ℝ :=
  let r := plaquetteCardinalityTilt (d := d) Φ β *
    perturbationMajorant Φ β
  ‖F.toBoundedContinuousMap‖ *
    Real.exp (((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2) *
    Real.exp (((4 * d * F.support.card : ℕ) : ℝ) *
      ((2 * r) / (1 - (2 ^ (16 * d) : ℝ) * (2 * r))))

theorem sum_norm_cardinalityTiltedMarkedSubsetWeight_mul_exp_rootKPWeight_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ∑ D : ObservableRootDecoration F Λ,
      ‖(plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ D.support.card *
          markedSubsetWeight F Λ Φ β D.support‖ *
        Real.exp
          (decoratedObservableCardinalityTiltKPWeight
            F Λ Φ β (Sum.inr D)) ≤
      observableCardinalityTiltDecorationBudget (d := d) F Φ β := by
  classical
  let r := plaquetteCardinalityTilt (d := d) Φ β *
    perturbationMajorant Φ β
  let q : ℝ := 2 * r
  let c : ℝ := ‖F.toBoundedContinuousMap‖ *
    Real.exp (((4 * d * F.support.card : ℕ) : ℝ) * Real.log 2)
  let A : ℝ :=
    ∑ γ ∈ (Finset.univ : Finset (PlaquettePolymer Λ)).filter
      (observableRootTouches F Λ), q ^ γ.1.card
  let B : ℝ := ((observableRootPlaquettes Λ F).card : ℝ) *
    (q / (1 - (2 ^ (16 * d) : ℝ) * q))
  let U : ℝ := ((4 * d * F.support.card : ℕ) : ℝ) *
    (q / (1 - (2 ^ (16 * d) : ℝ) * q))
  have hr : 0 ≤ r := mul_nonneg
    (plaquetteCardinalityTilt_nonneg Φ hβ)
    (perturbationMajorant_nonneg Φ β)
  have hq : 0 ≤ q := mul_nonneg (by norm_num) hr
  have hden : 0 < 1 - (2 ^ (16 * d) : ℝ) * q := by
    have hthreshold :=
      plaquetteCardinalityTilt_mul_perturbationMajorant_lt_threshold Φ hβ
    rw [dobrushinThreshold, lt_min_iff, lt_min_iff] at hthreshold
    rcases hthreshold with ⟨_hEight, hAnimal, _hDegree⟩
    have hdenpos : 0 < (16 : ℝ) * ((2 ^ (16 * d) : ℕ) + 1) := by
      positivity
    have hmul := (lt_div_iff₀ hdenpos).mp hAnimal
    have hC : 0 ≤ (2 ^ (16 * d) : ℝ) := by positivity
    have hcoeff : 2 * (2 ^ (16 * d) : ℝ) ≤
        16 * ((2 ^ (16 * d) : ℕ) + 1) := by
      norm_num
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hcoeff hr
    dsimp only [q, r]
    nlinarith [hscaled]
  have hfrac : 0 ≤ q / (1 - (2 ^ (16 * d) : ℝ) * q) :=
    div_nonneg hq hden.le
  have hc : 0 ≤ c :=
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hdecorations :
      (∑ D : ObservableRootDecoration F Λ,
          ∏ δ ∈ D.1, q ^ δ.1.card) ≤ Real.exp A := by
    simpa [A] using sum_observableRootDecoration_product_le_exp F Λ hq
  have hanimals : A ≤ B := by
    simpa [A, B, q, r] using
      sum_observableRoot_cardinalityTiltedAnimalWeight_le F Λ Φ hβ
  have hBU : B ≤ U := by
    dsimp only [B, U]
    gcongr
    exact_mod_cast card_observableRootPlaquettes_le Λ F
  change (∑ D : ObservableRootDecoration F Λ,
      ‖(plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ D.support.card *
          markedSubsetWeight F Λ Φ β D.support‖ *
        Real.exp
          (decoratedObservableCardinalityTiltKPWeight
            F Λ Φ β (Sum.inr D))) ≤ c * Real.exp U
  calc
    _ ≤ ∑ D : ObservableRootDecoration F Λ,
        c * ∏ δ ∈ D.1, q ^ δ.1.card := by
      exact Finset.sum_le_sum fun D _ => by
        simpa [c, q, r] using
          norm_cardinalityTiltedMarkedSubsetWeight_mul_exp_rootKPWeight_le
            F Λ Φ hβ D
    _ = c * ∑ D : ObservableRootDecoration F Λ,
        ∏ δ ∈ D.1, q ^ δ.1.card := by rw [Finset.mul_sum]
    _ ≤ c * Real.exp A := mul_le_mul_of_nonneg_left hdecorations hc
    _ ≤ c * Real.exp B :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hanimals) hc
    _ ≤ c * Real.exp U :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hBU) hc

/-! ## Absolute one-root spatial summability -/

/-- Number of plaquettes carried by a bulk polymer or by a complete
observable-root decoration. -/
def decoratedObservablePlaquetteCardinality
    (F : LocalObservable d G) (Λ : FiniteSpecification d G) :
    PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ → ℕ
  | Sum.inl γ => γ.1.card
  | Sum.inr D => D.support.card

/-- The exact decorated one-root gas with the common strict
plaquette-cardinality tilt applied to every activity. -/
def decoratedObservableCardinalityTiltedModel
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ) :=
  ((plaquettePolymerModel Λ Φ β).scaleByNatWeight
      (fun γ => γ.1.card)
      (plaquetteCardinalityTilt (d := d) Φ β : ℂ)).augmentExclusiveRoots
    (observableRootDecorationTouches F Λ)
    (fun D =>
      (plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ D.support.card *
        (α * markedSubsetWeight F Λ Φ β D.support))

@[simp]
theorem decoratedObservableCardinalityTiltedModel_bulk_activity
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ)
    (γ : PlaquettePolymer Λ) :
    (decoratedObservableCardinalityTiltedModel F Λ Φ β α).activity
        (Sum.inl γ) =
      (plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ γ.1.card *
        (plaquettePolymerModel Λ Φ β).activity γ := rfl

@[simp]
theorem decoratedObservableCardinalityTiltedModel_root_activity
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ)
    (D : ObservableRootDecoration F Λ) :
    (decoratedObservableCardinalityTiltedModel F Λ Φ β α).activity
        (Sum.inr D) =
      (plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ D.support.card *
        (α * markedSubsetWeight F Λ Φ β D.support) := rfl

/-- The direct tilted one-root model is exactly the common natural-weight
scaling of the unweighted decorated gas at the level of every Mayer term. -/
theorem decoratedObservableCardinalityTiltedModel_mayerClusterTerm
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α : ℂ)
    (X : FinitePolymerModel.MayerMultiIndex
      (PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ)) :
    (decoratedObservableCardinalityTiltedModel F Λ Φ β α).mayerClusterTerm X =
      (plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^
          FinitePolymerModel.weightedMultiplicity
            (decoratedObservablePlaquetteCardinality F Λ) X *
        (decoratedObservableRootModel F Λ Φ β α).mayerClusterTerm X := by
  let A := decoratedObservableCardinalityTiltedModel F Λ Φ β α
  let B := (decoratedObservableRootModel F Λ Φ β α).scaleByNatWeight
    (decoratedObservablePlaquetteCardinality F Λ)
    (plaquetteCardinalityTilt (d := d) Φ β : ℂ)
  have hactivity : ∀ q, A.activity q = B.activity q := by
    rintro (γ | D) <;> rfl
  have hmonomial : A.mayerActivityMonomial X = B.mayerActivityMonomial X := by
    unfold FinitePolymerModel.mayerActivityMonomial
    apply Finset.prod_congr rfl
    intro q _
    rw [hactivity q]
  have hterm : A.mayerClusterTerm X = B.mayerClusterTerm X := by
    unfold FinitePolymerModel.mayerClusterTerm
    rw [hmonomial]
    rfl
  change A.mayerClusterTerm X = _
  rw [hterm]
  exact (decoratedObservableRootModel F Λ Φ β α).mayerClusterTerm_scaleByNatWeight
    (decoratedObservablePlaquetteCardinality F Λ)
    (plaquetteCardinalityTilt (d := d) Φ β : ℂ) X

/-- The zero-source cardinality-tilted one-root gas inherits the genuine KP
certificate from the tilted bulk gas. -/
theorem decoratedObservableCardinalityTiltedModel_koteckyPreiss_zero
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    (decoratedObservableCardinalityTiltedModel F Λ Φ β 0).KoteckyPreissCertificate
      Finset.univ (decoratedObservableCardinalityTiltKPWeight F Λ Φ β) := by
  let M := (plaquettePolymerModel Λ Φ β).scaleByNatWeight
    (fun γ => γ.1.card)
    (plaquetteCardinalityTilt (d := d) Φ β : ℂ)
  have hM : M.KoteckyPreissCertificate Finset.univ plaquetteKPWeight := by
    simpa [M] using plaquettePolymerModel_cardinalityTilt_koteckyPreiss Λ Φ hβ
  simpa [decoratedObservableCardinalityTiltedModel,
    decoratedObservableCardinalityTiltKPWeight, M,
    mul_zero] using
      M.koteckyPreissCertificate_augmentExclusiveRoots_zero
        (observableRootDecorationTouches F Λ) plaquetteKPWeight hM

/-- Degree majorant for the absolute cardinality-tilted one-root sector. -/
def decoratedObservableCardinalityTiltedLinearTreeMajorantDegreeSum
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (n : ℕ) : ℝ :=
  ∑ D : ObservableRootDecoration F Λ,
    ‖(plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ D.support.card *
        markedSubsetWeight F Λ Φ β D.support‖ *
      (decoratedObservableCardinalityTiltedModel F Λ Φ β 0).residualSymmetricPinnedTreeDegreeSum
        (Sum.inr D) n

/-- Every fixed tilted root decoration has a summable residual rooted-tree
orbit. -/
theorem summable_decoratedObservableCardinalityTilted_residualTree
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (D : ObservableRootDecoration F Λ) :
    Summable ((decoratedObservableCardinalityTiltedModel F Λ Φ β 0).residualSymmetricPinnedTreeDegreeSum
      (Sum.inr D)) := by
  let A := decoratedObservableCardinalityTiltedModel F Λ Φ β 0
  let a := decoratedObservableCardinalityTiltKPWeight F Λ Φ β
  have hKP : A.KoteckyPreissCertificate Finset.univ a := by
    simpa [A, a] using
      decoratedObservableCardinalityTiltedModel_koteckyPreiss_zero F Λ Φ hβ
  exact A.summable_residualSymmetricPinnedTreeDegreeSum_of_koteckyPreiss
    a A.rootedTreeOrbitBound hKP (Sum.inr D)

/-- The complete absolute one-root spatial tree majorant is summable. -/
theorem summable_decoratedObservableCardinalityTiltedLinearTreeMajorantDegreeSum
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable
      (decoratedObservableCardinalityTiltedLinearTreeMajorantDegreeSum
        F Λ Φ β) := by
  unfold decoratedObservableCardinalityTiltedLinearTreeMajorantDegreeSum
  apply summable_sum
  intro D _
  exact (summable_decoratedObservableCardinalityTilted_residualTree
    F Λ Φ hβ D).mul_left _

/-- The total tilted one-root tree majorant is bounded uniformly in the
finite specification and its exterior field. -/
theorem tsum_decoratedObservableCardinalityTiltedLinearTreeMajorantDegreeSum_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ∑' n : ℕ,
        decoratedObservableCardinalityTiltedLinearTreeMajorantDegreeSum
          F Λ Φ β n ≤
      observableCardinalityTiltDecorationBudget (d := d) F Φ β := by
  have hsummable (D : ObservableRootDecoration F Λ) : Summable (fun n : ℕ =>
      ‖(plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ D.support.card *
          markedSubsetWeight F Λ Φ β D.support‖ *
        (decoratedObservableCardinalityTiltedModel F Λ Φ β 0).residualSymmetricPinnedTreeDegreeSum
          (Sum.inr D) n) :=
    (summable_decoratedObservableCardinalityTilted_residualTree
      F Λ Φ hβ D).mul_left _
  unfold decoratedObservableCardinalityTiltedLinearTreeMajorantDegreeSum
  rw [Summable.tsum_finsetSum (fun D _ => hsummable D)]
  calc
    _ = ∑ D : ObservableRootDecoration F Λ,
        ‖(plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ D.support.card *
            markedSubsetWeight F Λ Φ β D.support‖ *
          (∑' n : ℕ,
            (decoratedObservableCardinalityTiltedModel F Λ Φ β 0).residualSymmetricPinnedTreeDegreeSum
              (Sum.inr D) n) := by
      apply Finset.sum_congr rfl
      intro D _
      rw [tsum_mul_left]
    _ ≤ ∑ D : ObservableRootDecoration F Λ,
        ‖(plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ D.support.card *
            markedSubsetWeight F Λ Φ β D.support‖ *
          Real.exp
            (decoratedObservableCardinalityTiltKPWeight
              F Λ Φ β (Sum.inr D)) := by
      apply Finset.sum_le_sum
      intro D _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact
        (decoratedObservableCardinalityTiltedModel F Λ Φ β 0).tsum_residualSymmetricPinnedTreeDegreeSum_le_of_koteckyPreiss_certified
            (decoratedObservableCardinalityTiltKPWeight F Λ Φ β)
            (decoratedObservableCardinalityTiltedModel_koteckyPreiss_zero
              F Λ Φ hβ) (Sum.inr D)
    _ ≤ _ :=
      sum_norm_cardinalityTiltedMarkedSubsetWeight_mul_exp_rootKPWeight_le
        F Λ Φ hβ

/-- At every positive degree, the absolute cardinality-tilted one-root Mayer
coefficient is controlled by the complete rooted-tree majorant. -/
theorem decoratedObservableCardinalityTiltedLinearNormMayerDegreeSum_succ_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (n : ℕ) :
    (decoratedObservableCardinalityTiltedModel F Λ Φ β 1).exclusiveRootLinearNormMayerDegreeSum
        (n + 1) ≤
      decoratedObservableCardinalityTiltedLinearTreeMajorantDegreeSum
        F Λ Φ β n := by
  let M := (plaquettePolymerModel Λ Φ β).scaleByNatWeight
    (fun γ => γ.1.card)
    (plaquetteCardinalityTilt (d := d) Φ β : ℂ)
  let rootActivity : ObservableRootDecoration F Λ → ℂ := fun D =>
    (plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ D.support.card *
      markedSubsetWeight F Λ Φ β D.support
  simpa [decoratedObservableCardinalityTiltedModel,
    decoratedObservableCardinalityTiltedLinearTreeMajorantDegreeSum,
    M, rootActivity, one_mul, mul_zero] using
      M.exclusiveRootLinearNormMayerDegreeSum_succ_le
        (observableRootDecorationTouches F Λ) rootActivity n

/-- Genuine absolute spatial summability of all multiplicity-one decorated
clusters. -/
theorem summable_decoratedObservableCardinalityTiltedLinearNormMayerDegreeSum_succ
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Summable (fun n : ℕ =>
      (decoratedObservableCardinalityTiltedModel F Λ Φ β 1).exclusiveRootLinearNormMayerDegreeSum
        (n + 1)) := by
  exact Summable.of_nonneg_of_le
    (fun n => by
      unfold Polymer.FinitePolymerModel.exclusiveRootLinearNormMayerDegreeSum
      exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity)
    (decoratedObservableCardinalityTiltedLinearNormMayerDegreeSum_succ_le
      F Λ Φ β)
    (summable_decoratedObservableCardinalityTiltedLinearTreeMajorantDegreeSum
      F Λ Φ hβ)

/-- Quantitative volume-free bound for the full absolute cardinality-tilted
one-root Mayer sector. -/
theorem tsum_decoratedObservableCardinalityTiltedLinearNormMayerDegreeSum_succ_le
    (F : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ∑' n : ℕ,
      (decoratedObservableCardinalityTiltedModel F Λ Φ β 1).exclusiveRootLinearNormMayerDegreeSum
        (n + 1) ≤
      observableCardinalityTiltDecorationBudget (d := d) F Φ β := by
  calc
    _ ≤ ∑' n : ℕ,
        decoratedObservableCardinalityTiltedLinearTreeMajorantDegreeSum
          F Λ Φ β n := by
      exact
        (summable_decoratedObservableCardinalityTiltedLinearNormMayerDegreeSum_succ
          F Λ Φ hβ).tsum_le_tsum
            (decoratedObservableCardinalityTiltedLinearNormMayerDegreeSum_succ_le
              F Λ Φ β)
            (summable_decoratedObservableCardinalityTiltedLinearTreeMajorantDegreeSum
              F Λ Φ hβ)
    _ ≤ _ :=
      tsum_decoratedObservableCardinalityTiltedLinearTreeMajorantDegreeSum_le
        F Λ Φ hβ

/-! ## Positive-source regularization after the spatial tilt -/

/-- The tilted bulk keeps its linear KP weight; each tilted source polymer
gets one additional unit beyond its exact zero-source touching budget. -/
def bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    (((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) → ℝ
  | Sum.inl (Sum.inl (Sum.inl γ)) => plaquetteKPWeight γ
  | q => bivariateDecoratedObservableCardinalityTiltKPWeight
      F H Λ Φ β q + 1

@[simp]
theorem bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight_bulk
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) (γ : PlaquettePolymer Λ) :
    bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
      F H Λ Φ β (Sum.inl (Sum.inl (Sum.inl γ))) = plaquetteKPWeight γ := rfl

@[simp]
theorem bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight_left
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (D : ObservableRootDecoration F Λ) :
    bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
        F H Λ Φ β (Sum.inl (Sum.inl (Sum.inr D))) =
      bivariateDecoratedObservableCardinalityTiltKPWeight
        F H Λ Φ β (Sum.inl (Sum.inl (Sum.inr D))) + 1 := rfl

@[simp]
theorem bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight_right
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (E : ObservableRootDecoration H Λ) :
    bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
        F H Λ Φ β (Sum.inl (Sum.inr E)) =
      bivariateDecoratedObservableCardinalityTiltKPWeight
        F H Λ Φ β (Sum.inl (Sum.inr E)) + 1 := rfl

@[simp]
theorem bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight_bridge
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (B : TwoObservableBridgeDecoration F H Λ) :
    bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
        F H Λ Φ β (Sum.inr B) =
      bivariateDecoratedObservableCardinalityTiltKPWeight
        F H Λ Φ β (Sum.inr B) + 1 := rfl

theorem bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight_nonneg
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ∀ q, 0 ≤ bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
      F H Λ Φ β q := by
  rintro (((γ | D) | E) | B)
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num)).le
  · exact add_nonneg
      (bivariateDecoratedObservableCardinalityTiltKPWeight_nonneg
        F H Λ Φ hβ _) zero_le_one
  · exact add_nonneg
      (bivariateDecoratedObservableCardinalityTiltKPWeight_nonneg
        F H Λ Φ hβ _) zero_le_one
  · exact add_nonneg
      (bivariateDecoratedObservableCardinalityTiltKPWeight_nonneg
        F H Λ Φ hβ _) zero_le_one

/-- Complete mass of the three tilted source colours at specified source
values, including their regularized KP exponential weights. -/
def bivariateDecoratedObservableCardinalityTiltSourceMass
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) : ℝ :=
  ∑ q, if BivariateDecoratedObservableRootIsSource F H Λ q then
    ‖(bivariateDecoratedObservableCardinalityTiltedModel
        F H Λ Φ β α θ).activity q‖ *
      Real.exp
        (bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
          F H Λ Φ β q)
    else 0

theorem bivariateDecoratedObservableCardinalityTiltSourceMass_nonneg
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ) :
    0 ≤ bivariateDecoratedObservableCardinalityTiltSourceMass
      F H Λ Φ β α θ := by
  unfold bivariateDecoratedObservableCardinalityTiltSourceMass
  exact Finset.sum_nonneg fun q _ => by
    split_ifs
    · exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    · exact le_rfl

/-- The three-colour tilted source mass written as the two complete
one-sided decoration sums and the intrinsic-bridge subtype sum. -/
theorem bivariateDecoratedObservableCardinalityTiltSourceMass_one_one_eq
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    bivariateDecoratedObservableCardinalityTiltSourceMass
        F H Λ Φ β 1 1 =
      (∑ D : ObservableRootDecoration F Λ,
        ‖(plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ D.support.card *
          markedSubsetWeight F Λ Φ β D.support‖ *
          Real.exp
            (decoratedObservableCardinalityTiltKPWeight F Λ Φ β
              (Sum.inr D) + 1)) +
      (∑ E : ObservableRootDecoration H Λ,
        ‖(plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ E.support.card *
          markedSubsetWeight H Λ Φ β E.support‖ *
          Real.exp
            (decoratedObservableCardinalityTiltKPWeight H Λ Φ β
              (Sum.inr E) + 1)) +
      ∑ B : TwoObservableBridgeDecoration F H Λ,
        ‖(plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^ B.support.card *
          markedSubsetWeight (F.mul H) Λ Φ β B.support‖ *
          Real.exp
            (decoratedObservableCardinalityTiltKPWeight (F.mul H) Λ Φ β
              (Sum.inr B.1) + 1) := by
  classical
  simp [bivariateDecoratedObservableCardinalityTiltSourceMass,
    bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight,
    BivariateDecoratedObservableRootIsSource,
    bivariateDecoratedObservableCardinalityTiltedModel_left_activity,
    bivariateDecoratedObservableCardinalityTiltedModel_right_activity,
    bivariateDecoratedObservableCardinalityTiltedModel_bridge_activity,
    norm_mul, norm_pow]

/-- Explicit volume-free budget for all three tilted source colours. -/
def bivariateDecoratedObservableCardinalityTiltUniformSourceBudget
    (F H : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℂ) : ℝ :=
  Real.exp 1 *
    (observableCardinalityTiltDecorationBudget (d := d) F Φ β +
      observableCardinalityTiltDecorationBudget (d := d) H Φ β +
      observableCardinalityTiltDecorationBudget (d := d) (F.mul H) Φ β)

set_option maxHeartbeats 800000 in
-- The three nested finite source colours make elaboration of the explicit
-- `Finset` comparison substantially heavier than the surrounding KP lemmas.
theorem bivariateDecoratedObservableCardinalityTiltSourceMass_le_uniformBudget
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    bivariateDecoratedObservableCardinalityTiltSourceMass
        F H Λ Φ β 1 1 ≤
      bivariateDecoratedObservableCardinalityTiltUniformSourceBudget
        (d := d) F H Φ β := by
  classical
  let t := plaquetteCardinalityTilt (d := d) Φ β
  let fF : ObservableRootDecoration F Λ → ℝ := fun D =>
    ‖(t : ℂ) ^ D.support.card *
      markedSubsetWeight F Λ Φ β D.support‖ *
      Real.exp
        (decoratedObservableCardinalityTiltKPWeight F Λ Φ β (Sum.inr D))
  let fH : ObservableRootDecoration H Λ → ℝ := fun E =>
    ‖(t : ℂ) ^ E.support.card *
      markedSubsetWeight H Λ Φ β E.support‖ *
      Real.exp
        (decoratedObservableCardinalityTiltKPWeight H Λ Φ β (Sum.inr E))
  let fFH : ObservableRootDecoration (F.mul H) Λ → ℝ := fun D =>
    ‖(t : ℂ) ^ D.support.card *
      markedSubsetWeight (F.mul H) Λ Φ β D.support‖ *
      Real.exp
        (decoratedObservableCardinalityTiltKPWeight
          (F.mul H) Λ Φ β (Sum.inr D))
  have hfF : ∀ D, 0 ≤ fF D := by
    intro D
    exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hfH : ∀ E, 0 ≤ fH E := by
    intro E
    exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hfFH : ∀ D, 0 ≤ fFH D := by
    intro D
    exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hF : (∑ D, fF D) ≤
      observableCardinalityTiltDecorationBudget (d := d) F Φ β := by
    simpa [fF, t] using
      sum_norm_cardinalityTiltedMarkedSubsetWeight_mul_exp_rootKPWeight_le
        F Λ Φ hβ
  have hH : (∑ E, fH E) ≤
      observableCardinalityTiltDecorationBudget (d := d) H Φ β := by
    simpa [fH, t] using
      sum_norm_cardinalityTiltedMarkedSubsetWeight_mul_exp_rootKPWeight_le
        H Λ Φ hβ
  have hFH : (∑ D, fFH D) ≤
      observableCardinalityTiltDecorationBudget (d := d) (F.mul H) Φ β := by
    simpa [fFH, t] using
      sum_norm_cardinalityTiltedMarkedSubsetWeight_mul_exp_rootKPWeight_le
        (F.mul H) Λ Φ hβ
  have hbridge : (∑ B : TwoObservableBridgeDecoration F H Λ, fFH B.1) ≤
      ∑ D : ObservableRootDecoration (F.mul H) Λ, fFH D := by
    let s : Finset (ObservableRootDecoration (F.mul H) Λ) :=
      Finset.univ.filter fun D =>
        ∃ γ ∈ D.1, observableRootTouches F Λ γ ∧
          observableRootTouches H Λ γ
    calc
      (∑ B : TwoObservableBridgeDecoration F H Λ, fFH B.1) =
          ∑ D ∈ s, fFH D :=
        (Finset.sum_subtype s (by intro D; simp [s]) fFH).symm
      _ ≤ ∑ D ∈ (Finset.univ :
          Finset (ObservableRootDecoration (F.mul H) Λ)), fFH D :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun D _ _ => hfFH D)
      _ = ∑ D : ObservableRootDecoration (F.mul H) Λ, fFH D := by simp
  rw [bivariateDecoratedObservableCardinalityTiltSourceMass_one_one_eq]
  simp_rw [Real.exp_add, ← mul_assoc]
  change (∑ D, fF D * Real.exp 1) +
      (∑ E, fH E * Real.exp 1) +
      (∑ B : TwoObservableBridgeDecoration F H Λ, fFH B.1 * Real.exp 1) ≤ _
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  unfold bivariateDecoratedObservableCardinalityTiltUniformSourceBudget
  calc
    (∑ D, fF D) * Real.exp 1 +
        (∑ E, fH E) * Real.exp 1 +
        (∑ B : TwoObservableBridgeDecoration F H Λ, fFH B.1) *
          Real.exp 1 ≤
      observableCardinalityTiltDecorationBudget (d := d) F Φ β *
          Real.exp 1 +
        observableCardinalityTiltDecorationBudget (d := d) H Φ β *
          Real.exp 1 +
        observableCardinalityTiltDecorationBudget (d := d) (F.mul H) Φ β *
          Real.exp 1 := by
      gcongr
      exact hbridge.trans hFH
    _ = Real.exp 1 *
        (observableCardinalityTiltDecorationBudget (d := d) F Φ β +
          observableCardinalityTiltDecorationBudget (d := d) H Φ β +
          observableCardinalityTiltDecorationBudget (d := d) (F.mul H) Φ β) := by
      ring

theorem observableCardinalityTiltDecorationBudget_nonneg
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℂ) :
    0 ≤ observableCardinalityTiltDecorationBudget (d := d) F Φ β := by
  unfold observableCardinalityTiltDecorationBudget
  exact mul_nonneg
    (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (Real.exp_pos _).le

theorem bivariateDecoratedObservableCardinalityTiltUniformSourceBudget_nonneg
    (F H : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℂ) :
    0 ≤ bivariateDecoratedObservableCardinalityTiltUniformSourceBudget
      (d := d) F H Φ β := by
  unfold bivariateDecoratedObservableCardinalityTiltUniformSourceBudget
  exact mul_nonneg (Real.exp_pos _).le
    (add_nonneg
      (add_nonneg
        (observableCardinalityTiltDecorationBudget_nonneg (d := d) F Φ β)
        (observableCardinalityTiltDecorationBudget_nonneg (d := d) H Φ β))
      (observableCardinalityTiltDecorationBudget_nonneg
        (d := d) (F.mul H) Φ β))

/-- Positive common source used to switch on the finite collection of
cardinality-tilted decorations while spending at most the fixed KP reserve. -/
def bivariateDecoratedObservableCardinalityTiltRegularization
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) : ℝ :=
  min 1 (twoRootSourceReserve /
    (bivariateDecoratedObservableCardinalityTiltSourceMass
      F H Λ Φ β 1 1 + 1))

/-- A box-independent source radius obtained by replacing the finite source
mass by its explicit uniform decoration budget. -/
def bivariateDecoratedObservableCardinalityTiltUniformRegularization
    (F H : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℂ) : ℝ :=
  min 1 (twoRootSourceReserve /
    (bivariateDecoratedObservableCardinalityTiltUniformSourceBudget
      (d := d) F H Φ β + 1))

theorem bivariateDecoratedObservableCardinalityTiltUniformRegularization_pos
    (F H : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℂ) :
    0 < bivariateDecoratedObservableCardinalityTiltUniformRegularization
      (d := d) F H Φ β := by
  unfold bivariateDecoratedObservableCardinalityTiltUniformRegularization
  apply lt_min (by norm_num)
  exact div_pos twoRootSourceReserve_pos (by
    have h :=
      bivariateDecoratedObservableCardinalityTiltUniformSourceBudget_nonneg
        (d := d) F H Φ β
    linarith)

theorem bivariateDecoratedObservableCardinalityTiltUniformRegularization_le
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    bivariateDecoratedObservableCardinalityTiltUniformRegularization
        (d := d) F H Φ β ≤
      bivariateDecoratedObservableCardinalityTiltRegularization
        F H Λ Φ β := by
  let S := bivariateDecoratedObservableCardinalityTiltSourceMass
    F H Λ Φ β 1 1
  let B := bivariateDecoratedObservableCardinalityTiltUniformSourceBudget
    (d := d) F H Φ β
  have hS : 0 ≤ S :=
    bivariateDecoratedObservableCardinalityTiltSourceMass_nonneg
      F H Λ Φ β 1 1
  have hSB : S ≤ B := by
    simpa [S, B] using
      bivariateDecoratedObservableCardinalityTiltSourceMass_le_uniformBudget
        F H Λ Φ hβ
  have hfrac : twoRootSourceReserve / (B + 1) ≤
      twoRootSourceReserve / (S + 1) :=
    div_le_div_of_nonneg_left twoRootSourceReserve_pos.le (by linarith)
      (by linarith)
  unfold bivariateDecoratedObservableCardinalityTiltUniformRegularization
    bivariateDecoratedObservableCardinalityTiltRegularization
  exact min_le_min_left 1 hfrac

theorem bivariateDecoratedObservableCardinalityTiltRegularization_pos
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    0 < bivariateDecoratedObservableCardinalityTiltRegularization
      F H Λ Φ β := by
  unfold bivariateDecoratedObservableCardinalityTiltRegularization
  apply lt_min (by norm_num)
  have hmass :=
    bivariateDecoratedObservableCardinalityTiltSourceMass_nonneg
      F H Λ Φ β 1 1
  exact div_pos twoRootSourceReserve_pos (by linarith)

theorem bivariateDecoratedObservableCardinalityTiltRegularization_le_one
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    bivariateDecoratedObservableCardinalityTiltRegularization
      F H Λ Φ β ≤ 1 :=
  min_le_left _ _

theorem bivariateDecoratedObservableCardinalityTiltRegularization_mul_mass_le
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    bivariateDecoratedObservableCardinalityTiltRegularization F H Λ Φ β *
        bivariateDecoratedObservableCardinalityTiltSourceMass
          F H Λ Φ β 1 1 ≤ twoRootSourceReserve := by
  let S := bivariateDecoratedObservableCardinalityTiltSourceMass
    F H Λ Φ β 1 1
  let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
    F H Λ Φ β
  have hS : 0 ≤ S :=
    bivariateDecoratedObservableCardinalityTiltSourceMass_nonneg
      F H Λ Φ β 1 1
  have hden : 0 < S + 1 := by linarith
  have hρ : ρ ≤ twoRootSourceReserve / (S + 1) := min_le_right _ _
  calc
    ρ * S ≤ (twoRootSourceReserve / (S + 1)) * S :=
      mul_le_mul_of_nonneg_right hρ hS
    _ ≤ twoRootSourceReserve := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hden).2
      nlinarith [twoRootSourceReserve_pos.le]

/-- At the common regularization, every tilted source activity is bounded by
`ρ` times its tilted unit-source activity. -/
theorem norm_bivariateDecoratedObservableCardinalityTiltedModel_regularized_source_activity_le
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (q : ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ)
    (hq : BivariateDecoratedObservableRootIsSource F H Λ q) :
    let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
      F H Λ Φ β
    ‖(bivariateDecoratedObservableCardinalityTiltedModel
        F H Λ Φ β ρ ρ).activity q‖ ≤
      ρ * ‖(bivariateDecoratedObservableCardinalityTiltedModel
        F H Λ Φ β 1 1).activity q‖ := by
  dsimp only
  let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
    F H Λ Φ β
  have hρ : 0 ≤ ρ :=
    (bivariateDecoratedObservableCardinalityTiltRegularization_pos
      F H Λ Φ β).le
  have hρone : ρ ≤ 1 :=
    bivariateDecoratedObservableCardinalityTiltRegularization_le_one
      F H Λ Φ β
  have hunscaled :
      ‖(bivariateDecoratedObservableRootModel F H Λ Φ β ρ ρ).activity q‖ ≤
        ρ * ‖(bivariateDecoratedObservableRootModel
          F H Λ Φ β 1 1).activity q‖ := by
    rcases q with (((γ | D) | E) | B)
    · simp [BivariateDecoratedObservableRootIsSource] at hq
    · simp only [bivariateDecoratedObservableRootModel_left_activity,
        one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hρ]
      exact le_rfl
    · simp only [bivariateDecoratedObservableRootModel_right_activity,
        one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hρ]
      exact le_rfl
    · simp only [bivariateDecoratedObservableRootModel_bridge_activity,
        one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hρ]
      apply mul_le_mul_of_nonneg_right _
        (norm_nonneg (markedSubsetWeight (F.mul H) Λ Φ β B.support))
      exact mul_le_of_le_one_right hρ hρone
  change ‖(plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^
      bivariateDecoratedObservablePlaquetteCardinality F H Λ q *
        (bivariateDecoratedObservableRootModel F H Λ Φ β ρ ρ).activity q‖ ≤
    ρ * ‖(plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^
      bivariateDecoratedObservablePlaquetteCardinality F H Λ q *
        (bivariateDecoratedObservableRootModel F H Λ Φ β 1 1).activity q‖
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖(plaquetteCardinalityTilt (d := d) Φ β : ℂ) ^
          bivariateDecoratedObservablePlaquetteCardinality F H Λ q‖ *
        (ρ * ‖(bivariateDecoratedObservableRootModel
          F H Λ Φ β 1 1).activity q‖) :=
      mul_le_mul_of_nonneg_left hunscaled (norm_nonneg _)
    _ = _ := by ring

/-- The complete cardinality-tilted source mass at the regularized source
uses at most the fixed reserve. -/
theorem bivariateDecoratedObservableCardinalityTiltSourceMass_regularized_le
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ) :
    let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
      F H Λ Φ β
    bivariateDecoratedObservableCardinalityTiltSourceMass
      F H Λ Φ β ρ ρ ≤ twoRootSourceReserve := by
  dsimp only
  let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
    F H Λ Φ β
  calc
    _ ≤ ρ * bivariateDecoratedObservableCardinalityTiltSourceMass
        F H Λ Φ β 1 1 := by
      unfold bivariateDecoratedObservableCardinalityTiltSourceMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q _
      by_cases hq : BivariateDecoratedObservableRootIsSource F H Λ q
      · rw [if_pos hq, if_pos hq]
        calc
          _ ≤ (ρ *
                ‖(bivariateDecoratedObservableCardinalityTiltedModel
                  F H Λ Φ β 1 1).activity q‖) *
                Real.exp
                  (bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
                    F H Λ Φ β q) :=
            mul_le_mul_of_nonneg_right
              (norm_bivariateDecoratedObservableCardinalityTiltedModel_regularized_source_activity_le
                F H Λ Φ β q hq) (Real.exp_pos _).le
          _ = _ := by ring
      · simp [hq]
    _ ≤ _ :=
      bivariateDecoratedObservableCardinalityTiltRegularization_mul_mass_le
        F H Λ Φ β

/-- Switching on the regularized tilted sources changes any KP
incompatibility sum by at most the complete tilted source mass. -/
theorem bivariateDecoratedObservableCardinalityTilt_regularizedKPSum_le_zero_add_sourceMass
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β : ℂ)
    (q : ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) :
    let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
      F H Λ Φ β
    let Aρ := bivariateDecoratedObservableCardinalityTiltedModel
      F H Λ Φ β ρ ρ
    let A₀ := bivariateDecoratedObservableCardinalityTiltedModel
      F H Λ Φ β 0 0
    let aρ :=
      bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
        F H Λ Φ β
    let a₀ := bivariateDecoratedObservableCardinalityTiltKPWeight
      F H Λ Φ β
    (∑ r, if Aρ.incompatible q r then
        ‖Aρ.activity r‖ * Real.exp (aρ r) else 0) ≤
      (∑ r, if A₀.incompatible q r then
        ‖A₀.activity r‖ * Real.exp (a₀ r) else 0) +
      bivariateDecoratedObservableCardinalityTiltSourceMass
        F H Λ Φ β ρ ρ := by
  classical
  dsimp only
  let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
    F H Λ Φ β
  let Aρ := bivariateDecoratedObservableCardinalityTiltedModel
    F H Λ Φ β ρ ρ
  let A₀ := bivariateDecoratedObservableCardinalityTiltedModel
    F H Λ Φ β 0 0
  let aρ := bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
    F H Λ Φ β
  let a₀ := bivariateDecoratedObservableCardinalityTiltKPWeight
    F H Λ Φ β
  calc
    _ ≤ ∑ r, ((if A₀.incompatible q r then
          ‖A₀.activity r‖ * Real.exp (a₀ r) else 0) +
        (if BivariateDecoratedObservableRootIsSource F H Λ r then
          ‖Aρ.activity r‖ * Real.exp (aρ r) else 0)) := by
      apply Finset.sum_le_sum
      rintro (((γ | D) | E) | B) _
      · have hsource :
            ¬BivariateDecoratedObservableRootIsSource F H Λ
              (Sum.inl (Sum.inl (Sum.inl γ))) := by
          simp [BivariateDecoratedObservableRootIsSource]
        have hiff :
            Aρ.incompatible q (Sum.inl (Sum.inl (Sum.inl γ))) ↔
              A₀.incompatible q (Sum.inl (Sum.inl (Sum.inl γ))) := Iff.rfl
        have hterm :
            ‖Aρ.activity (Sum.inl (Sum.inl (Sum.inl γ)))‖ *
                Real.exp (aρ (Sum.inl (Sum.inl (Sum.inl γ)))) =
              ‖A₀.activity (Sum.inl (Sum.inl (Sum.inl γ)))‖ *
                Real.exp (a₀ (Sum.inl (Sum.inl (Sum.inl γ)))) := by
          simp only [Aρ, A₀, aρ, a₀,
            bivariateDecoratedObservableCardinalityTiltedModel_bulk_activity,
            bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight_bulk,
            bivariateDecoratedObservableCardinalityTiltKPWeight_bulk]
        by_cases hinc :
            Aρ.incompatible q (Sum.inl (Sum.inl (Sum.inl γ)))
        · have hinc0 := hiff.mp hinc
          rw [if_pos hinc, if_pos hinc0, if_neg hsource, hterm, add_zero]
        · have hinc0 :
              ¬A₀.incompatible q (Sum.inl (Sum.inl (Sum.inl γ))) :=
            fun h => hinc (hiff.mpr h)
          rw [if_neg hinc, if_neg hinc0, if_neg hsource, add_zero]
      · have hsource : BivariateDecoratedObservableRootIsSource F H Λ
            (Sum.inl (Sum.inl (Sum.inr D))) := by trivial
        have hiff :
            Aρ.incompatible q (Sum.inl (Sum.inl (Sum.inr D))) ↔
              A₀.incompatible q (Sum.inl (Sum.inl (Sum.inr D))) := Iff.rfl
        have hzeroTerm :
            ‖A₀.activity (Sum.inl (Sum.inl (Sum.inr D)))‖ *
              Real.exp (a₀ (Sum.inl (Sum.inl (Sum.inr D)))) = 0 := by
          simp [A₀,
            bivariateDecoratedObservableCardinalityTiltedModel_left_activity]
        by_cases hinc : Aρ.incompatible q
            (Sum.inl (Sum.inl (Sum.inr D)))
        · have hinc0 := hiff.mp hinc
          rw [if_pos hinc, if_pos hinc0, if_pos hsource,
            hzeroTerm, zero_add]
        · have hinc0 : ¬A₀.incompatible q
              (Sum.inl (Sum.inl (Sum.inr D))) := fun h => hinc (hiff.mpr h)
          rw [if_neg hinc, if_neg hinc0, if_pos hsource, zero_add]
          exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      · have hsource : BivariateDecoratedObservableRootIsSource F H Λ
            (Sum.inl (Sum.inr E)) := by trivial
        have hiff : Aρ.incompatible q (Sum.inl (Sum.inr E)) ↔
            A₀.incompatible q (Sum.inl (Sum.inr E)) := Iff.rfl
        have hzeroTerm :
            ‖A₀.activity (Sum.inl (Sum.inr E))‖ *
              Real.exp (a₀ (Sum.inl (Sum.inr E))) = 0 := by
          simp [A₀,
            bivariateDecoratedObservableCardinalityTiltedModel_right_activity]
        by_cases hinc : Aρ.incompatible q (Sum.inl (Sum.inr E))
        · have hinc0 := hiff.mp hinc
          rw [if_pos hinc, if_pos hinc0, if_pos hsource,
            hzeroTerm, zero_add]
        · have hinc0 : ¬A₀.incompatible q (Sum.inl (Sum.inr E)) :=
            fun h => hinc (hiff.mpr h)
          rw [if_neg hinc, if_neg hinc0, if_pos hsource, zero_add]
          exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      · have hsource : BivariateDecoratedObservableRootIsSource F H Λ
            (Sum.inr B) := by trivial
        have hiff : Aρ.incompatible q (Sum.inr B) ↔
            A₀.incompatible q (Sum.inr B) := Iff.rfl
        have hzeroTerm :
            ‖A₀.activity (Sum.inr B)‖ * Real.exp (a₀ (Sum.inr B)) = 0 := by
          simp [A₀,
            bivariateDecoratedObservableCardinalityTiltedModel_bridge_activity]
        by_cases hinc : Aρ.incompatible q (Sum.inr B)
        · have hinc0 := hiff.mp hinc
          rw [if_pos hinc, if_pos hinc0, if_pos hsource,
            hzeroTerm, zero_add]
        · have hinc0 : ¬A₀.incompatible q (Sum.inr B) :=
            fun h => hinc (hiff.mpr h)
          rw [if_neg hinc, if_neg hinc0, if_pos hsource, zero_add]
          exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      rw [Finset.sum_add_distrib]
      rfl

/-- Genuine nonzero-source KP certificate for the full cardinality-tilted
left/right/bridge gas.  It is obtained solely from the explicit
animal-counting reserve and the finite source regularization. -/
theorem bivariateDecoratedObservableCardinalityTiltedModel_koteckyPreiss_regularized
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
      F H Λ Φ β
    (bivariateDecoratedObservableCardinalityTiltedModel
      F H Λ Φ β ρ ρ).KoteckyPreissCertificate Finset.univ
        (bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
          F H Λ Φ β) := by
  classical
  dsimp only
  let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
    F H Λ Φ β
  let Aρ := bivariateDecoratedObservableCardinalityTiltedModel
    F H Λ Φ β ρ ρ
  let A₀ := bivariateDecoratedObservableCardinalityTiltedModel
    F H Λ Φ β 0 0
  let aρ := bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
    F H Λ Φ β
  let a₀ := bivariateDecoratedObservableCardinalityTiltKPWeight
    F H Λ Φ β
  let t := plaquetteCardinalityTilt (d := d) Φ β
  have ht : 0 ≤ t := plaquetteCardinalityTilt_nonneg Φ hβ
  have hsmall : t * perturbationMajorant Φ β <
      dobrushinThreshold (16 * d) (2 ^ (16 * d)) :=
    plaquetteCardinalityTilt_mul_perturbationMajorant_lt_threshold Φ hβ
  have hzero : A₀.KoteckyPreissCertificate Finset.univ a₀ := by
    exact bivariateDecoratedObservableCardinalityTiltedModel_koteckyPreiss_zero
      F H Λ Φ hβ
  have hsource :
      bivariateDecoratedObservableCardinalityTiltSourceMass
          F H Λ Φ β ρ ρ ≤ twoRootSourceReserve :=
    bivariateDecoratedObservableCardinalityTiltSourceMass_regularized_le
      F H Λ Φ β
  refine ⟨?_, ?_⟩
  · exact
      bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight_nonneg
        F H Λ Φ hβ
  · intro q _hq
    rw [Finset.sum_filter]
    have hcompare :
        (∑ r, if Aρ.incompatible q r then
            ‖Aρ.activity r‖ * Real.exp (aρ r) else 0) ≤
          (∑ r, if A₀.incompatible q r then
            ‖A₀.activity r‖ * Real.exp (a₀ r) else 0) +
          bivariateDecoratedObservableCardinalityTiltSourceMass
            F H Λ Φ β ρ ρ := by
      simpa [Aρ, A₀, aρ, a₀, ρ] using
        bivariateDecoratedObservableCardinalityTilt_regularizedKPSum_le_zero_add_sourceMass
          F H Λ Φ β q
    rcases q with (((γ | D) | E) | B)
    · have hbulk :=
        plaquettePolymerModel_scaleByCard_kp_incompatible_sum_le_quarter
          Λ Φ β t ht hsmall γ
      dsimp only at hbulk
      rw [Finset.sum_filter] at hbulk
      have hzeroBulk :
          (∑ r, if A₀.incompatible (Sum.inl (Sum.inl (Sum.inl γ))) r then
              ‖A₀.activity r‖ * Real.exp (a₀ r) else 0) ≤
            (γ.1.card : ℝ) * (Real.log 2 / 4) := by
        dsimp only [A₀, a₀]
        simpa [bivariateDecoratedObservableCardinalityTiltedModel,
          bivariateDecoratedObservablePlaquetteCardinality,
          bivariateDecoratedObservableRootModel,
          bivariateDecoratedObservableCardinalityTiltKPWeight,
          Polymer.FinitePolymerModel.scaleByNatWeight,
          Polymer.FinitePolymerModel.augmentBivariateExclusiveRoots,
          Polymer.FinitePolymerModel.augmentTwoColorExclusiveRoots,
          Polymer.FinitePolymerModel.augmentExclusiveRoots,
          Fintype.sum_sum_type, t] using hbulk
      have hcard : (1 : ℝ) ≤ (γ.1.card : ℝ) := by
        exact_mod_cast γ.2.1.card_pos
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
      calc
        _ ≤ (∑ r, if A₀.incompatible
              (Sum.inl (Sum.inl (Sum.inl γ))) r then
              ‖A₀.activity r‖ * Real.exp (a₀ r) else 0) +
            bivariateDecoratedObservableCardinalityTiltSourceMass
              F H Λ Φ β ρ ρ := hcompare
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
            bivariateDecoratedObservableCardinalityTiltSourceMass
              F H Λ Φ β ρ ρ := hcompare
        _ ≤ a₀ (Sum.inl (Sum.inl (Sum.inr D))) +
            twoRootSourceReserve := add_le_add hz hsource
        _ ≤ a₀ (Sum.inl (Sum.inl (Sum.inr D))) + 1 :=
          add_le_add_right twoRootSourceReserve_le_one _
        _ = aρ (Sum.inl (Sum.inl (Sum.inr D))) := by
          exact
            (bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight_left
              F H Λ Φ β D).symm
    · have hz := hzero.2 (Sum.inl (Sum.inr E)) (Finset.mem_univ _)
      rw [Finset.sum_filter] at hz
      calc
        _ ≤ (∑ r, if A₀.incompatible (Sum.inl (Sum.inr E)) r then
              ‖A₀.activity r‖ * Real.exp (a₀ r) else 0) +
            bivariateDecoratedObservableCardinalityTiltSourceMass
              F H Λ Φ β ρ ρ := hcompare
        _ ≤ a₀ (Sum.inl (Sum.inr E)) + twoRootSourceReserve :=
          add_le_add hz hsource
        _ ≤ a₀ (Sum.inl (Sum.inr E)) + 1 :=
          add_le_add_right twoRootSourceReserve_le_one _
        _ = aρ (Sum.inl (Sum.inr E)) := by
          exact
            (bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight_right
              F H Λ Φ β E).symm
    · have hz := hzero.2 (Sum.inr B) (Finset.mem_univ _)
      rw [Finset.sum_filter] at hz
      calc
        _ ≤ (∑ r, if A₀.incompatible (Sum.inr B) r then
              ‖A₀.activity r‖ * Real.exp (a₀ r) else 0) +
            bivariateDecoratedObservableCardinalityTiltSourceMass
              F H Λ Φ β ρ ρ := hcompare
        _ ≤ a₀ (Sum.inr B) + twoRootSourceReserve :=
          add_le_add hz hsource
        _ ≤ a₀ (Sum.inr B) + 1 :=
          add_le_add_right twoRootSourceReserve_le_one _
        _ = aρ (Sum.inr B) := by
          exact
            (bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight_bridge
              F H Λ Φ β B).symm

/-! ## Weighted Mayer and tree summability -/

/-- Source rescaling commutes pointwise with the common plaquette-cardinality
tilt. -/
theorem bivariateDecoratedObservableCardinalityTiltedModel_scaled_activity
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) (β α θ : ℂ)
    (q : ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) :
    ((bivariateDecoratedObservableCardinalityTiltedModel
        F H Λ Φ β 1 1).scaleByBigradedSource
          (bivariateDecoratedObservableRootGrading F H Λ)
          (bivariateObservableSourceValues α θ)).activity q =
      (bivariateDecoratedObservableCardinalityTiltedModel
        F H Λ Φ β α θ).activity q := by
  rcases q with (((γ | D) | E) | B) <;>
    simp [Polymer.FinitePolymerModel.scaleByBigradedSource,
      bivariateDecoratedObservableCardinalityTiltedModel,
      Polymer.FinitePolymerModel.scaleByNatWeight,
      bivariateDecoratedObservablePlaquetteCardinality,
      bivariateDecoratedObservableRootModel,
      Polymer.FinitePolymerModel.augmentBivariateExclusiveRoots,
      Polymer.FinitePolymerModel.augmentTwoColorExclusiveRoots,
      Polymer.FinitePolymerModel.augmentExclusiveRoots,
      bivariateDecoratedObservableRootGrading,
      bivariateObservableSourceValues, Fin.prod_univ_two] <;> ring

/-- The source-scaled unit-source tilted gas has the genuine regularized KP
certificate. -/
theorem bivariateDecoratedObservableCardinalityTiltedModel_scaled_koteckyPreiss_regularized
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
      F H Λ Φ β
    ((bivariateDecoratedObservableCardinalityTiltedModel
        F H Λ Φ β 1 1).scaleByBigradedSource
          (bivariateDecoratedObservableRootGrading F H Λ)
          (bivariateObservableSourceValues ρ ρ)).KoteckyPreissCertificate
      Finset.univ
      (bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
        F H Λ Φ β) := by
  classical
  dsimp only
  let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
    F H Λ Φ β
  let As := (bivariateDecoratedObservableCardinalityTiltedModel
    F H Λ Φ β 1 1).scaleByBigradedSource
      (bivariateDecoratedObservableRootGrading F H Λ)
      (bivariateObservableSourceValues ρ ρ)
  let Aρ := bivariateDecoratedObservableCardinalityTiltedModel
    F H Λ Φ β ρ ρ
  let a := bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
    F H Λ Φ β
  have hregular : Aρ.KoteckyPreissCertificate Finset.univ a :=
    bivariateDecoratedObservableCardinalityTiltedModel_koteckyPreiss_regularized
      F H Λ Φ hβ
  refine ⟨hregular.1, ?_⟩
  intro q _hq
  have hq := hregular.2 q (Finset.mem_univ q)
  change (∑ r ∈ Finset.univ.filter (As.incompatible q),
      ‖As.activity r‖ * Real.exp (a r)) ≤ a q
  simpa only [As, Aρ,
    bivariateDecoratedObservableCardinalityTiltedModel_scaled_activity] using hq

/-- Full positive-degree Mayer majorant of the cardinality-tilted decorated
gas is summable after the positive source regularization. -/
theorem bivariateDecoratedObservableCardinalityTiltedModel_summable_normMayerDegreeSum_succ
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
      F H Λ Φ β
    Summable (fun n : ℕ ↦
      ((bivariateDecoratedObservableCardinalityTiltedModel
          F H Λ Φ β 1 1).scaleByBigradedSource
        (bivariateDecoratedObservableRootGrading F H Λ)
        (bivariateObservableSourceValues ρ ρ)).normMayerDegreeSum (n + 1)) := by
  dsimp only
  exact
    ((bivariateDecoratedObservableCardinalityTiltedModel
      F H Λ Φ β 1 1).scaleByBigradedSource
        (bivariateDecoratedObservableRootGrading F H Λ)
        (bivariateObservableSourceValues
          (bivariateDecoratedObservableCardinalityTiltRegularization
            F H Λ Φ β)
          (bivariateDecoratedObservableCardinalityTiltRegularization
            F H Λ Φ β))).summable_normMayerDegreeSum_succ_of_koteckyPreiss_certified
      (bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
        F H Λ Φ β)
      (bivariateDecoratedObservableCardinalityTiltedModel_scaled_koteckyPreiss_regularized
        F H Λ Φ hβ)

/-- Every pinned spanning-tree series of the regularized
cardinality-tilted gas is genuinely summable. -/
theorem bivariateDecoratedObservableCardinalityTiltedModel_summable_pinnedMayerTreeDegreeSum_succ
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (root : ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) :
    let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
      F H Λ Φ β
    Summable (fun n : ℕ ↦
      ((bivariateDecoratedObservableCardinalityTiltedModel
          F H Λ Φ β 1 1).scaleByBigradedSource
        (bivariateDecoratedObservableRootGrading F H Λ)
        (bivariateObservableSourceValues ρ ρ)).pinnedMayerTreeDegreeSum
          root (n + 1)) := by
  dsimp only
  exact
    Polymer.FinitePolymerModel.summable_pinnedMayerTreeDegreeSum_succ_of_koteckyPreiss_certified
      ((bivariateDecoratedObservableCardinalityTiltedModel
        F H Λ Φ β 1 1).scaleByBigradedSource
          (bivariateDecoratedObservableRootGrading F H Λ)
          (bivariateObservableSourceValues
            (bivariateDecoratedObservableCardinalityTiltRegularization
              F H Λ Φ β)
            (bivariateDecoratedObservableCardinalityTiltRegularization
              F H Λ Φ β)))
      (bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
        F H Λ Φ β)
      (bivariateDecoratedObservableCardinalityTiltedModel_scaled_koteckyPreiss_regularized
        F H Λ Φ hβ) root

/-- The exact mixed observable-root sector is absolutely summable with the
strict exponential weight `t ^ totalPlaquetteCardinality`. -/
theorem summable_bivariateDecoratedObservableMixedCardinalityWeightedNormDegreeSum_succ
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let M := bivariateDecoratedObservableRootModel F H Λ Φ β 1 1
    let grading := bivariateDecoratedObservableRootGrading F H Λ
    let weight := bivariateDecoratedObservablePlaquetteCardinality F H Λ
    let t := plaquetteCardinalityTilt (d := d) Φ β
    Summable (fun n : ℕ ↦
      M.bigradedMixedWeightedNormDegreeSum grading weight t (n + 1)) := by
  dsimp only
  let M := bivariateDecoratedObservableRootModel F H Λ Φ β 1 1
  let grading := bivariateDecoratedObservableRootGrading F H Λ
  let weight := bivariateDecoratedObservablePlaquetteCardinality F H Λ
  let t := plaquetteCardinalityTilt (d := d) Φ β
  let Mt := M.scaleByNatWeight weight (t : ℂ)
  let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
    F H Λ Φ β
  let alpha := bivariateObservableSourceValues (ρ : ℂ) (ρ : ℂ)
  have ht : 0 ≤ t := plaquetteCardinalityTilt_nonneg Φ hβ
  have hρ : ρ ≠ 0 := ne_of_gt
    (bivariateDecoratedObservableCardinalityTiltRegularization_pos
      F H Λ Φ β)
  have halpha0 : alpha 0 ≠ 0 := by
    simpa [alpha, bivariateObservableSourceValues] using hρ
  have halpha1 : alpha 1 ≠ 0 := by
    simpa [alpha, bivariateObservableSourceValues] using hρ
  have hscaled : Summable (fun n : ℕ ↦
      (Mt.scaleByBigradedSource grading alpha).normMayerDegreeSum
        (n + 1)) := by
    simpa [Mt, M, weight, t, grading, alpha,
      bivariateDecoratedObservableCardinalityTiltedModel] using
      (bivariateDecoratedObservableCardinalityTiltedModel_summable_normMayerDegreeSum_succ
        F H Λ Φ hβ)
  have hmixed : Summable (fun n : ℕ ↦
      Mt.bigradedMixedNormDegreeSum grading (n + 1)) := by
    apply Summable.of_nonneg_of_le
    · intro n
      unfold Polymer.FinitePolymerModel.bigradedMixedNormDegreeSum
      exact Finset.sum_nonneg fun X _ => by
        split_ifs
        · exact norm_nonneg _
        · exact le_rfl
    · intro n
      exact Mt.bigradedMixedNormDegreeSum_le_scaled
        grading alpha halpha0 halpha1 (n + 1)
    · exact hscaled.mul_left (‖alpha 0‖ * ‖alpha 1‖)⁻¹
  simpa [M, grading, weight, t, Mt,
    Polymer.FinitePolymerModel.bigradedMixedWeightedNormDegreeSum_eq_scaleByNatWeight
      M grading weight t ht] using hmixed

/-- The weighted mixed sector has a quantitative volume-free pinned/tree
bound.  The only remaining observable dependence is the explicit positive
source regularization; importantly, no sum over bulk polymers or volume
cardinality occurs. -/
theorem tsum_bivariateDecoratedObservableMixedCardinalityWeightedNormDegreeSum_succ_le
    (F H : LocalObservable d G) (Λ : FiniteSpecification d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    let M := bivariateDecoratedObservableRootModel F H Λ Φ β 1 1
    let grading := bivariateDecoratedObservableRootGrading F H Λ
    let weight := bivariateDecoratedObservablePlaquetteCardinality F H Λ
    let t := plaquetteCardinalityTilt (d := d) Φ β
    let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
      F H Λ Φ β
    ∑' n : ℕ,
        M.bigradedMixedWeightedNormDegreeSum grading weight t (n + 1) ≤
      (ρ * ρ)⁻¹ * twoRootSourceReserve := by
  classical
  dsimp only
  let M := bivariateDecoratedObservableRootModel F H Λ Φ β 1 1
  let grading := bivariateDecoratedObservableRootGrading F H Λ
  let weight := bivariateDecoratedObservablePlaquetteCardinality F H Λ
  let t := plaquetteCardinalityTilt (d := d) Φ β
  let Mt := M.scaleByNatWeight weight (t : ℂ)
  let ρ := bivariateDecoratedObservableCardinalityTiltRegularization
    F H Λ Φ β
  let alpha := bivariateObservableSourceValues (ρ : ℂ) (ρ : ℂ)
  let As := Mt.scaleByBigradedSource grading alpha
  let Aρ := bivariateDecoratedObservableCardinalityTiltedModel
    F H Λ Φ β ρ ρ
  let a := bivariateDecoratedObservableCardinalityTiltRegularizedKPWeight
    F H Λ Φ β
  have ht : 0 ≤ t := plaquetteCardinalityTilt_nonneg Φ hβ
  have hρpos : 0 < ρ :=
    bivariateDecoratedObservableCardinalityTiltRegularization_pos
      F H Λ Φ β
  have hρ : ρ ≠ 0 := ne_of_gt hρpos
  have halpha0 : alpha 0 ≠ 0 := by
    simpa [alpha, bivariateObservableSourceValues] using hρ
  have halpha1 : alpha 1 ≠ 0 := by
    simpa [alpha, bivariateObservableSourceValues] using hρ
  have hKP : As.KoteckyPreissCertificate Finset.univ a := by
    simpa [As, Mt, M, weight, t, grading, alpha, a,
      bivariateDecoratedObservableCardinalityTiltedModel] using
      (bivariateDecoratedObservableCardinalityTiltedModel_scaled_koteckyPreiss_regularized
        F H Λ Φ hβ)
  have hpinsummable (q : ((PlaquettePolymer Λ ⊕
      ObservableRootDecoration F Λ) ⊕ ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) :
      Summable (fun n : ℕ ↦ As.pinnedMayerTreeDegreeSum q (n + 1)) :=
    As.summable_pinnedMayerTreeDegreeSum_succ_of_koteckyPreiss_certified
      a hKP q
  have hmajorSummable : Summable (fun n : ℕ ↦
      (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
        ∑ q, (grading q 0 : ℝ) *
          As.pinnedMayerTreeDegreeSum q (n + 1)) := by
    apply Summable.mul_left
    apply summable_sum
    intro q _
    exact (hpinsummable q).mul_left (grading q 0 : ℝ)
  have hpoint (n : ℕ) :
      M.bigradedMixedWeightedNormDegreeSum grading weight t (n + 1) ≤
        (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
          ∑ q, (grading q 0 : ℝ) *
            As.pinnedMayerTreeDegreeSum q (n + 1) := by
    calc
      M.bigradedMixedWeightedNormDegreeSum grading weight t (n + 1) =
          Mt.bigradedMixedNormDegreeSum grading (n + 1) := by
        simpa [Mt] using
          (M.bigradedMixedWeightedNormDegreeSum_eq_scaleByNatWeight
            grading weight t ht (n + 1))
      _ ≤ (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
          As.bigradedMixedNormDegreeSum grading (n + 1) := by
        simpa [As] using
          (Mt.bigradedMixedNormDegreeSum_le_scaled_mixed
            grading alpha halpha0 halpha1 (n + 1))
      _ ≤ (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
          ∑ q, (grading q 0 : ℝ) *
            As.pinnedMayerTreeDegreeSum q (n + 1) := by
        exact mul_le_mul_of_nonneg_left
          (As.bigradedMixedNormDegreeSum_le_sum_firstGrading_pinnedMayerTreeDegreeSum
            grading (n + 1)) (inv_nonneg.mpr (mul_nonneg (norm_nonneg _)
              (norm_nonneg _)))
  have hweighted :=
    summable_bivariateDecoratedObservableMixedCardinalityWeightedNormDegreeSum_succ
      F H Λ Φ hβ
  have hpin (q : ((PlaquettePolymer Λ ⊕ ObservableRootDecoration F Λ) ⊕
      ObservableRootDecoration H Λ) ⊕ TwoObservableBridgeDecoration F H Λ) :
      ∑' n : ℕ, As.pinnedMayerTreeDegreeSum q (n + 1) ≤
        ‖As.activity q‖ * Real.exp (a q) :=
    As.tsum_pinnedMayerTreeDegreeSum_succ_le_of_koteckyPreiss_certified
      a hKP q
  have hAsActivity (q : ((PlaquettePolymer Λ ⊕
      ObservableRootDecoration F Λ) ⊕ ObservableRootDecoration H Λ) ⊕
        TwoObservableBridgeDecoration F H Λ) :
      As.activity q = Aρ.activity q := by
    simpa [As, Mt, M, weight, t, grading, alpha, Aρ,
      bivariateDecoratedObservableCardinalityTiltedModel] using
      (bivariateDecoratedObservableCardinalityTiltedModel_scaled_activity
        F H Λ Φ β (ρ : ℂ) (ρ : ℂ) q)
  have hsource :
      ∑ q, (grading q 0 : ℝ) * ‖As.activity q‖ * Real.exp (a q) ≤
        bivariateDecoratedObservableCardinalityTiltSourceMass
          F H Λ Φ β ρ ρ := by
    unfold bivariateDecoratedObservableCardinalityTiltSourceMass
    apply Finset.sum_le_sum
    rintro (((γ | D) | E) | B) _
    · simp only [grading, bivariateDecoratedObservableRootGrading,
        Nat.cast_zero, zero_mul,
        BivariateDecoratedObservableRootIsSource, if_false]
      exact le_rfl
    · rw [hAsActivity]
      simp only [grading, bivariateDecoratedObservableRootGrading,
        Fin.isValue, ↓reduceIte, Nat.cast_one, one_mul,
        BivariateDecoratedObservableRootIsSource, if_true]
      exact le_rfl
    · have hne : (0 : Fin 2) ≠ 1 := by decide
      simp only [grading, bivariateDecoratedObservableRootGrading,
        hne, if_false, Nat.cast_zero, zero_mul,
        BivariateDecoratedObservableRootIsSource, if_true]
      exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    · rw [hAsActivity]
      simp only [grading, bivariateDecoratedObservableRootGrading,
        Nat.cast_one, one_mul,
        BivariateDecoratedObservableRootIsSource, if_true]
      exact le_rfl
  calc
    (∑' n : ℕ,
        M.bigradedMixedWeightedNormDegreeSum grading weight t (n + 1)) ≤
      ∑' n : ℕ, (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
        ∑ q, (grading q 0 : ℝ) *
          As.pinnedMayerTreeDegreeSum q (n + 1) :=
      hweighted.tsum_le_tsum hpoint hmajorSummable
    _ = (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
        ∑ q, (grading q 0 : ℝ) *
          (∑' n : ℕ, As.pinnedMayerTreeDegreeSum q (n + 1)) := by
      rw [tsum_mul_left]
      rw [Summable.tsum_finsetSum (fun q _ ↦
        (hpinsummable q).mul_left (grading q 0 : ℝ))]
      apply congrArg
      apply Finset.sum_congr rfl
      intro q _
      rw [tsum_mul_left]
    _ ≤ (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
        ∑ q, (grading q 0 : ℝ) * ‖As.activity q‖ *
          Real.exp (a q) := by
      apply mul_le_mul_of_nonneg_left _
        (inv_nonneg.mpr (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      apply Finset.sum_le_sum
      intro q _
      calc
        (grading q 0 : ℝ) *
            (∑' n : ℕ, As.pinnedMayerTreeDegreeSum q (n + 1)) ≤
          (grading q 0 : ℝ) * (‖As.activity q‖ * Real.exp (a q)) :=
            mul_le_mul_of_nonneg_left (hpin q) (Nat.cast_nonneg _)
        _ = (grading q 0 : ℝ) * ‖As.activity q‖ *
            Real.exp (a q) := by ring
    _ ≤ (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
        bivariateDecoratedObservableCardinalityTiltSourceMass
          F H Λ Φ β ρ ρ :=
      mul_le_mul_of_nonneg_left hsource
        (inv_nonneg.mpr (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ ≤ (‖alpha 0‖ * ‖alpha 1‖)⁻¹ *
        twoRootSourceReserve := by
      apply mul_le_mul_of_nonneg_left
      · exact
          bivariateDecoratedObservableCardinalityTiltSourceMass_regularized_le
            F H Λ Φ β
      · exact inv_nonneg.mpr (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (ρ * ρ)⁻¹ * twoRootSourceReserve := by
      simp [alpha, bivariateObservableSourceValues, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hρpos]

end

end YangMills.StrongCoupling
