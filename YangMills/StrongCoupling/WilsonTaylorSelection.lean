/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.ThermodynamicCluster
import YangMills.Wilson.CenterSelection
import Mathlib.Data.Finsupp.BigOperators

/-!
# Center selection for Wilson Taylor monomials

This module proves the algebraic core of the strong-coupling area law.  On a
free finite plaquette region every edge read by the action is integrated.
The integral of a Wilson loop times character/conjugate-character Taylor
insertions vanishes unless their finite plaquette charge screens the loop.

The proof is an edgewise product-Haar change of variables.  It uses neither
the Dobrushin baseline nor the Douglas compatibility layer.
-/

open MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Wilson
open scoped BigOperators

noncomputable section

local instance wilsonSelectionDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]
  {rho : ContinuousUnitaryRepData G n}

/-- Wilson loop with explicit character and conjugate-character
multiplicities.  These are precisely the monomials in the Taylor expansion
of the real Wilson plaquette action. -/
def wilsonTaylorMonomial {x : Site d} (C : Lattice.Cubic.Path x x)
    (a b : Plaquette d →₀ ℕ) (A : Configuration d G) : ℂ :=
  rho.normalizedCharacter (holonomy A C) *
    a.prod (fun p k ↦ rho.normalizedCharacter (holonomy A p.boundary) ^ k) *
    b.prod (fun p k ↦
      star (rho.normalizedCharacter (holonomy A p.boundary)) ^ k)

/-- The finite plaquette carrier of the loop and both multiplicity fields. -/
def wilsonTaylorCarrier {x : Site d} (C : Lattice.Cubic.Path x x)
    (a b : Plaquette d →₀ ℕ) : Finset (Plaquette d) :=
  a.support ∪ b.support

/-- Canonical free-boundary specification integrating every edge read by the
Taylor fields or by the Wilson loop.  The active plaquettes are still exactly
the Taylor carrier; adjoining the finitely many loop edges only adds normalized
Haar coordinates and does not add action terms. -/
def wilsonTaylorSpecification {x : Site d} (C : Lattice.Cubic.Path x x)
    (a b : Plaquette d →₀ ℕ) : FiniteSpecification d G :=
  { activePlaquettes := wilsonTaylorCarrier C a b
    dynamicEdges :=
      (wilsonTaylorCarrier C a b).biUnion (fun p ↦ p.boundary.edgeSupport) ∪
        C.edgeSupport
    exterior := fun _ ↦ 1 }

@[simp]
theorem wilsonTaylorSpecification_activePlaquettes {x : Site d}
    (C : Lattice.Cubic.Path x x) (a b : Plaquette d →₀ ℕ) :
    (wilsonTaylorSpecification (G := G) C a b).activePlaquettes =
      wilsonTaylorCarrier C a b := rfl

@[simp]
theorem wilsonTaylorSpecification_dynamicEdges {x : Site d}
    (C : Lattice.Cubic.Path x x) (a b : Plaquette d →₀ ℕ) :
    (wilsonTaylorSpecification (G := G) C a b).dynamicEdges =
      (wilsonTaylorCarrier C a b).biUnion (fun p ↦ p.boundary.edgeSupport) ∪
        C.edgeSupport := rfl

/-- Twist one dynamic coordinate of a finite specification. -/
def twistDynamic (kappa : CenterChargeData rho)
    (Lambda : FiniteSpecification d G) (e : Lambda.dynamicEdges)
    (U : DynamicConfiguration Lambda) : DynamicConfiguration Lambda :=
  fun q ↦ if q = e then kappa.z * U q else U q

/-- The coordinatewise center twist as a measurable automorphism. -/
def twistDynamicMeasurableEquiv (kappa : CenterChargeData rho)
    (Lambda : FiniteSpecification d G) (e : Lambda.dynamicEdges) :
    DynamicConfiguration Lambda ≃ᵐ DynamicConfiguration Lambda :=
  MeasurableEquiv.piCongrRight fun q ↦
    if h : q = e then MeasurableEquiv.mulLeft kappa.z else MeasurableEquiv.refl G

@[simp]
theorem twistDynamicMeasurableEquiv_apply
    (kappa : CenterChargeData rho) (Lambda : FiniteSpecification d G)
    (e : Lambda.dynamicEdges) (U : DynamicConfiguration Lambda) :
    twistDynamicMeasurableEquiv kappa Lambda e U =
      twistDynamic kappa Lambda e U := by
  funext q
  change (if h : q = e then MeasurableEquiv.mulLeft kappa.z
      else MeasurableEquiv.refl G) (U q) = _
  by_cases h : q = e
  · subst q
    simp [twistDynamicMeasurableEquiv, twistDynamic]
  · simp [twistDynamicMeasurableEquiv, twistDynamic, h]

/-- Product Haar is invariant under a twist of one dynamic edge. -/
theorem measurePreserving_twistDynamic
    (kappa : CenterChargeData rho) (Lambda : FiniteSpecification d G)
    (e : Lambda.dynamicEdges) :
    MeasurePreserving (twistDynamicMeasurableEquiv kappa Lambda e)
      Lambda.haarMeasure Lambda.haarMeasure := by
  have hcoord : MeasurePreserving (twistDynamic kappa Lambda e)
      Lambda.haarMeasure Lambda.haarMeasure := by
    simpa only [FiniteSpecification.haarMeasure, ProductHaar.measure,
      twistDynamic] using
    (ProductHaar.measurePreserving_coordinatewise
      (G := G) (fun _ : Lambda.dynamicEdges ↦ GaugeHaarProbability.haar G)
      (fun q g ↦ if q = e then kappa.z * g else g)
      (fun q ↦ by
        by_cases h : q = e
        · subst q
          simpa using GaugeHaarProbability.measurePreserving_mulLeft G kappa.z
        · simpa [h] using MeasureTheory.MeasurePreserving.id
            (μ := GaugeHaarProbability.haar G)))
  have hfun :
      (⇑(twistDynamicMeasurableEquiv kappa Lambda e)) =
        twistDynamic kappa Lambda e := by
    funext U
    exact twistDynamicMeasurableEquiv_apply kappa Lambda e U
  rw [hfun]
  exact hcoord

/-- Gluing a twisted dynamic configuration is the full edge twist on every
dynamic edge. -/
theorem evaluate_twistDynamic
    (kappa : CenterChargeData rho) (Lambda : FiniteSpecification d G)
    (e : Lambda.dynamicEdges) (U : DynamicConfiguration Lambda) :
    Lambda.evaluate (twistDynamic kappa Lambda e U) =
      twistEdge kappa.z e.1 (Lambda.evaluate U) := by
  funext q
  unfold twistEdge
  by_cases hq : q ∈ Lambda.dynamicEdges
  · rw [Lambda.evaluate_of_mem _ q hq]
    by_cases h : (⟨q, hq⟩ : Lambda.dynamicEdges) = e
    · have hv : q = e.1 := congrArg Subtype.val h
      subst q
      simp [twistDynamic, h, Lambda.evaluate_of_mem U e.1 e.2]
    · have hv : q ≠ e.1 := fun hv ↦ h (Subtype.ext hv)
      simp [twistDynamic, h, hv, Lambda.evaluate_of_mem U q hq]
  · rw [Lambda.evaluate_of_not_mem _ q hq]
    have hv : q ≠ e.1 := fun hv ↦ hq (hv ▸ e.2)
    simp [hv, Lambda.evaluate_of_not_mem U q hq]

/-- A full Taylor monomial is an eigenfunction of one edge twist, with
eigenvalue equal to its net integer charge at that edge. -/
theorem wilsonTaylorMonomial_twistEdge
    (kappa : CenterChargeData rho) {x : Site d}
    (C : Lattice.Cubic.Path x x) (a b : Plaquette d →₀ ℕ)
    (e : PositiveEdge d) (A : Configuration d G) :
    wilsonTaylorMonomial (rho := rho) C a b (twistEdge kappa.z e A) =
      kappa.omega ^ Lattice.Cubic.taylorChargeAt C a b e *
        wilsonTaylorMonomial (rho := rho) C a b A := by
  unfold wilsonTaylorMonomial Lattice.Cubic.taylorChargeAt
  rw [kappa.normalizedCharacter_holonomy_twistEdge e A C]
  have homega : kappa.omega ≠ 0 := by
    intro h
    simpa [h] using kappa.norm_omega
  have phase_prod (c : Plaquette d →₀ ℕ)
      (s : Plaquette d → ℤ) :
      ∏ p ∈ c.support, kappa.omega ^ ((c p : ℤ) * s p) =
        kappa.omega ^ c.sum (fun p k ↦ (k : ℤ) * s p) := by
    classical
    unfold Finsupp.sum
    induction c.support using Finset.induction_on with
    | empty => simp
    | @insert p S hp ih =>
        rw [Finset.prod_insert hp, Finset.sum_insert hp,
          zpow_add₀ homega, ih]
  have ha : a.prod (fun p k ↦
      rho.normalizedCharacter (holonomy (twistEdge kappa.z e A) p.boundary) ^ k) =
      kappa.omega ^
          a.sum (fun p k ↦ (k : ℤ) * p.boundary.edgeIncidence e) *
        a.prod (fun p k ↦ rho.normalizedCharacter (holonomy A p.boundary) ^ k) := by
    classical
    unfold Finsupp.prod
    rw [← phase_prod a (fun p ↦ p.boundary.edgeIncidence e),
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    dsimp only
    rw [kappa.normalizedCharacter_holonomy_twistEdge e A p.boundary]
    rw [mul_pow, ← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  have hb : b.prod (fun p k ↦
      star (rho.normalizedCharacter
        (holonomy (twistEdge kappa.z e A) p.boundary)) ^ k) =
      kappa.omega ^
          (-b.sum (fun p k ↦ (k : ℤ) * p.boundary.edgeIncidence e)) *
        b.prod (fun p k ↦
          star (rho.normalizedCharacter (holonomy A p.boundary)) ^ k) := by
    classical
    have hneg :
        -b.sum (fun p k ↦ (k : ℤ) * p.boundary.edgeIncidence e) =
          b.sum (fun p k ↦ (k : ℤ) * (-p.boundary.edgeIncidence e)) := by
      unfold Finsupp.sum
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    unfold Finsupp.prod
    rw [hneg,
      ← phase_prod b (fun p ↦ -p.boundary.edgeIncidence e),
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    dsimp only
    rw [kappa.normalizedCharacter_holonomy_twistEdge e A p.boundary]
    rw [star_mul, kappa.star_omega_zpow, mul_pow]
    have hphasepow :
        (kappa.omega ^ (-p.boundary.edgeIncidence e)) ^ b p =
          kappa.omega ^ ((b p : ℤ) * (-p.boundary.edgeIncidence e)) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    rw [hphasepow]
    ring
  rw [ha, hb]
  rw [sub_eq_add_neg, zpow_add₀ homega, zpow_add₀ homega]
  ring

/-- The integrated Taylor monomial on its free carrier. -/
def wilsonTaylorIntegral {x : Site d} (C : Lattice.Cubic.Path x x)
    (a b : Plaquette d →₀ ℕ) : ℂ :=
  let Lambda := wilsonTaylorSpecification (G := G) C a b
  ∫ U, wilsonTaylorMonomial (rho := rho) C a b (Lambda.evaluate U)
    ∂Lambda.haarMeasure

set_option maxHeartbeats 800000

/-- If one edge has nontrivial net center charge, the Taylor monomial integral
vanishes.  Every loop and Taylor-carrier edge is dynamic by construction. -/
theorem wilsonTaylorIntegral_eq_zero_of_charge_ne_zero
    (kappa : FiniteCenterChargeData rho) {x : Site d}
    (C : Lattice.Cubic.Path x x) (a b : Plaquette d →₀ ℕ)
    (e : (wilsonTaylorSpecification (G := G) C a b).dynamicEdges)
    (he : (Lattice.Cubic.taylorChargeAt C a b e.1 :
      ZMod (orderOf kappa.toCenterChargeData.omega)) ≠ 0) :
    wilsonTaylorIntegral (rho := rho) C a b = 0 := by
  let Lambda := wilsonTaylorSpecification (G := G) C a b
  let kappa0 := kappa.toCenterChargeData
  have homega : kappa0.omega ≠ 0 := by
    intro h
    simpa [h] using kappa0.norm_omega
  let u : ℂˣ := Units.mk0 kappa0.omega homega
  have hphase : kappa0.omega ^ Lattice.Cubic.taylorChargeAt C a b e.1 ≠ 1 := by
    intro hphase
    apply he
    rw [CharP.intCast_eq_zero_iff]
    have hupow : u ^ Lattice.Cubic.taylorChargeAt C a b e.1 = 1 := by
      apply Units.ext
      simpa [u] using hphase
    have hdvd : (orderOf u : ℤ) ∣
        Lattice.Cubic.taylorChargeAt C a b e.1 :=
      orderOf_dvd_iff_zpow_eq_one.mpr hupow
    simpa [u, ← orderOf_units] using hdvd
  unfold wilsonTaylorIntegral
  apply YangMills.Probability.integral_eq_zero_of_measurePreserving_eigen
    Lambda.haarMeasure (twistDynamicMeasurableEquiv kappa0 Lambda e)
    (measurePreserving_twistDynamic kappa0 Lambda e)
    (fun U ↦ wilsonTaylorMonomial (rho := rho) C a b (Lambda.evaluate U))
    (kappa0.omega ^ Lattice.Cubic.taylorChargeAt C a b e.1) hphase
  intro U
  rw [twistDynamicMeasurableEquiv_apply, evaluate_twistDynamic]
  exact wilsonTaylorMonomial_twistEdge kappa0 C a b e.1 (Lambda.evaluate U)

/-- Away from the finite set of integrated loop/carrier edges, every integer
charge coefficient vanishes already before reduction modulo the center order. -/
theorem taylorChargeAt_eq_zero_of_not_mem_dynamic {x : Site d}
    (C : Lattice.Cubic.Path x x) (a b : Plaquette d →₀ ℕ)
    (e : PositiveEdge d)
    (he : e ∉ (wilsonTaylorSpecification (G := G) C a b).dynamicEdges) :
    Lattice.Cubic.taylorChargeAt C a b e = 0 := by
  have hC : C.edgeIncidence e = 0 := by
    apply Lattice.Cubic.Path.edgeChain_apply_eq_zero_of_not_mem_edgeSupport
      (R := ℤ) C e
    intro heC
    apply he
    exact Finset.mem_union_right _ heC
  have ha : a.sum (fun p k ↦ (k : ℤ) * p.boundary.edgeIncidence e) = 0 := by
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro p hp
    have hep : e ∉ p.boundary.edgeSupport := by
      intro hep
      apply he
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨p, Finset.mem_union_left _ hp, hep⟩
    have hinc : p.boundary.edgeIncidence e = 0 :=
      Lattice.Cubic.Path.edgeChain_apply_eq_zero_of_not_mem_edgeSupport
        (R := ℤ) p.boundary e hep
    dsimp only
    rw [hinc, mul_zero]
  have hb : b.sum (fun p k ↦ (k : ℤ) * p.boundary.edgeIncidence e) = 0 := by
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro p hp
    have hep : e ∉ p.boundary.edgeSupport := by
      intro hep
      apply he
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨p, Finset.mem_union_right _ hp, hep⟩
    have hinc : p.boundary.edgeIncidence e = 0 :=
      Lattice.Cubic.Path.edgeChain_apply_eq_zero_of_not_mem_edgeSupport
        (R := ℤ) p.boundary e hep
    dsimp only
    rw [hinc, mul_zero]
  unfold Lattice.Cubic.taylorChargeAt
  rw [hC, ha, hb]
  ring

/-- A nonzero integrated Taylor monomial supplies a finite center-charge
screening chain for the loop. -/
theorem taylorScreens_of_wilsonTaylorIntegral_ne_zero
    (kappa : FiniteCenterChargeData rho) {x : Site d}
    (C : Lattice.Cubic.Path x x) (a b : Plaquette d →₀ ℕ)
    (hI : wilsonTaylorIntegral (rho := rho) C a b ≠ 0) :
    Lattice.Cubic.TaylorScreens
      (orderOf kappa.toCenterChargeData.omega) C a b := by
  intro e
  by_contra he
  by_cases hedyn : e ∈
      (wilsonTaylorSpecification (G := G) C a b).dynamicEdges
  · exact hI (wilsonTaylorIntegral_eq_zero_of_charge_ne_zero
      kappa C a b ⟨e, hedyn⟩ he)
  · apply he
    rw [taylorChargeAt_eq_zero_of_not_mem_dynamic C a b e hedyn]
    exact Int.cast_zero

/-- The first possibly nonzero center-charged Wilson Taylor term has order at
least the loop's algebraic center filling area. -/
theorem centerFillingArea_le_taylorOrder_of_wilsonTaylorIntegral_ne_zero
    (kappa : FiniteCenterChargeData rho) {x : Site d}
    (C : Lattice.Cubic.Path x x) (a b : Plaquette d →₀ ℕ)
    (hI : wilsonTaylorIntegral (rho := rho) C a b ≠ 0) :
    Lattice.Cubic.centerFillingArea
        (orderOf kappa.toCenterChargeData.omega) C ≤
      Lattice.Cubic.taylorOrder a b :=
  Lattice.Cubic.centerFillingArea_le_taylorOrder _ C a b
    (taylorScreens_of_wilsonTaylorIntegral_ne_zero kappa C a b hI)

end

end YangMills.StrongCoupling
