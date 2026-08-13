/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.WilsonTaylorSelection
import YangMills.Lattice.RectangleCharge
import YangMills.StrongCoupling.MarkedExpansion
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Analytic.Order

/-!
# Labelled Wilson Taylor words

The `N`th derivative of the Wilson plaquette Boltzmann weight is most
conveniently expanded as a finite sum of labelled words of length `N`.
Each letter chooses a plaquette and either its normalized character or its
complex conjugate.  This file proves the edgewise center-selection rule for
such words and relates their length to the symmetric multiplicity fields of
`WilsonTaylorSelection`.

The labelled formulation avoids multinomial normalization issues: labels are
kept until after Haar selection, while the two `Finsupp` fields record only
the resulting cubical charge.
-/

open MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Wilson
open scoped Topology
open scoped BigOperators

noncomputable section

local instance wilsonJetsDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [CompactSpace G] [T2Space G]
  [GaugeHaarProbability G]
  {rho : ContinuousUnitaryRepData G n}

/-- One labelled Taylor insertion.  `false` denotes the normalized
character and `true` its complex conjugate. -/
abbrev WilsonTaylorLetter (d : ℕ) := Plaquette d × Bool

/-- Value of one labelled Taylor insertion. -/
def wilsonTaylorLetterValue (rho : ContinuousUnitaryRepData G n)
    (q : WilsonTaylorLetter d) (A : Configuration d G) : ℂ :=
  if q.2 then
    star (rho.normalizedCharacter (holonomy A q.1.boundary))
  else
    rho.normalizedCharacter (holonomy A q.1.boundary)

/-- Wilson insertion multiplied by a labelled word of plaquette insertions. -/
def wilsonTaylorWordMonomial {x : Site d}
    (rho : ContinuousUnitaryRepData G n) (C : Lattice.Cubic.Path x x)
    (w : List (WilsonTaylorLetter d)) (A : Configuration d G) : ℂ :=
  rho.normalizedCharacter (holonomy A C) *
    (w.map fun q ↦ wilsonTaylorLetterValue rho q A).prod

/-- Net integer center charge of a labelled Taylor word at one edge. -/
def wilsonTaylorWordChargeAt {x : Site d}
    (C : Lattice.Cubic.Path x x) (w : List (WilsonTaylorLetter d))
    (e : PositiveEdge d) : ℤ :=
  C.edgeIncidence e + (w.map fun q ↦
    if q.2 then -q.1.boundary.edgeIncidence e
    else q.1.boundary.edgeIncidence e).sum

/-- Character multiplicities obtained by forgetting the labels of a word. -/
def wilsonTaylorWordPositive : List (WilsonTaylorLetter d) → Plaquette d →₀ ℕ
  | [] => 0
  | q :: w => if q.2 then wilsonTaylorWordPositive w
      else Finsupp.single q.1 1 + wilsonTaylorWordPositive w

/-- Conjugate-character multiplicities obtained by forgetting the labels of
a word. -/
def wilsonTaylorWordNegative : List (WilsonTaylorLetter d) → Plaquette d →₀ ℕ
  | [] => 0
  | q :: w => if q.2 then Finsupp.single q.1 1 + wilsonTaylorWordNegative w
      else wilsonTaylorWordNegative w

@[simp]
theorem taylorOrder_wordMultiplicity :
    ∀ w : List (WilsonTaylorLetter d),
      Lattice.Cubic.taylorOrder (wilsonTaylorWordPositive w)
          (wilsonTaylorWordNegative w) = w.length := by
  intro w
  induction w with
  | nil => simp [wilsonTaylorWordPositive, wilsonTaylorWordNegative,
      Lattice.Cubic.taylorOrder]
  | cons q w ih =>
      rcases q with ⟨p, s⟩
      cases s
      · simp [wilsonTaylorWordPositive, wilsonTaylorWordNegative,
          Lattice.Cubic.taylorOrder, Finsupp.sum_add_index]
        unfold Lattice.Cubic.taylorOrder at ih
        omega
      · simp [wilsonTaylorWordPositive, wilsonTaylorWordNegative,
          Lattice.Cubic.taylorOrder, Finsupp.sum_add_index]
        unfold Lattice.Cubic.taylorOrder at ih
        omega

@[simp]
theorem taylorChargeAt_wordMultiplicity {x : Site d}
    (C : Lattice.Cubic.Path x x) :
    ∀ (w : List (WilsonTaylorLetter d)) (e : PositiveEdge d),
      Lattice.Cubic.taylorChargeAt C (wilsonTaylorWordPositive w)
          (wilsonTaylorWordNegative w) e =
        wilsonTaylorWordChargeAt C w e := by
  intro w
  induction w with
  | nil =>
      intro e
      simp [wilsonTaylorWordPositive, wilsonTaylorWordNegative,
        Lattice.Cubic.taylorChargeAt, wilsonTaylorWordChargeAt]
  | cons q w ih =>
      intro e
      rcases q with ⟨p, s⟩
      cases s
      · simp [wilsonTaylorWordPositive, wilsonTaylorWordNegative,
          Lattice.Cubic.taylorChargeAt, wilsonTaylorWordChargeAt,
          Finsupp.sum_add_index]
        rw [Finsupp.sum_add_index (by simp) (by simp [add_mul])]
        rw [Finsupp.sum_single_index (by simp)]
        norm_num at *
        have h := ih e
        unfold Lattice.Cubic.taylorChargeAt wilsonTaylorWordChargeAt at h
        linarith
      · simp [wilsonTaylorWordPositive, wilsonTaylorWordNegative,
          Lattice.Cubic.taylorChargeAt, wilsonTaylorWordChargeAt,
          Finsupp.sum_add_index]
        rw [Finsupp.sum_add_index (by simp) (by simp [add_mul])]
        rw [Finsupp.sum_single_index (by simp)]
        norm_num at *
        have h := ih e
        unfold Lattice.Cubic.taylorChargeAt wilsonTaylorWordChargeAt at h
        linarith

/-- One labelled insertion is an eigenfunction of an edge-center twist. -/
theorem wilsonTaylorLetterValue_twistEdge
    (kappa : CenterChargeData rho) (q : WilsonTaylorLetter d)
    (e : PositiveEdge d) (A : Configuration d G) :
    wilsonTaylorLetterValue rho q (twistEdge kappa.z e A) =
      kappa.omega ^ (if q.2 then -q.1.boundary.edgeIncidence e
        else q.1.boundary.edgeIncidence e) *
        wilsonTaylorLetterValue rho q A := by
  rcases q with ⟨p, s⟩
  cases s
  · simp only [wilsonTaylorLetterValue, Bool.false_eq_true, if_false]
    exact kappa.normalizedCharacter_holonomy_twistEdge e A p.boundary
  · simp only [wilsonTaylorLetterValue, if_true]
    rw [kappa.normalizedCharacter_holonomy_twistEdge e A p.boundary,
      star_mul, kappa.star_omega_zpow]
    ring

/-- A labelled word has eigenvalue given by its total edge charge. -/
theorem wilsonTaylorWordMonomial_twistEdge
    (kappa : CenterChargeData rho) {x : Site d}
    (C : Lattice.Cubic.Path x x) (w : List (WilsonTaylorLetter d))
    (e : PositiveEdge d) (A : Configuration d G) :
    wilsonTaylorWordMonomial rho C w (twistEdge kappa.z e A) =
      kappa.omega ^ wilsonTaylorWordChargeAt C w e *
        wilsonTaylorWordMonomial rho C w A := by
  have homega : kappa.omega ≠ 0 := by
    intro h
    simpa [h] using kappa.norm_omega
  have hword : ∀ v : List (WilsonTaylorLetter d),
      (v.map fun q ↦ wilsonTaylorLetterValue rho q (twistEdge kappa.z e A)).prod =
        kappa.omega ^ ((v.map fun q ↦
          if q.2 then -q.1.boundary.edgeIncidence e
          else q.1.boundary.edgeIncidence e).sum) *
          (v.map fun q ↦ wilsonTaylorLetterValue rho q A).prod := by
    intro v
    induction v with
    | nil => simp
    | cons q v ih =>
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        rw [wilsonTaylorLetterValue_twistEdge kappa q e A, ih,
          zpow_add₀ homega]
        ring
  unfold wilsonTaylorWordMonomial wilsonTaylorWordChargeAt
  rw [kappa.normalizedCharacter_holonomy_twistEdge e A C, hword,
    zpow_add₀ homega]
  ring

/-- Haar integral of a labelled Taylor word in an arbitrary finite
specification. -/
def wilsonTaylorWordIntegral (Lambda : FiniteSpecification d G)
    {x : Site d} (C : Lattice.Cubic.Path x x)
    (w : List (WilsonTaylorLetter d)) : ℂ :=
  ∫ U, wilsonTaylorWordMonomial rho C w (Lambda.evaluate U)
    ∂Lambda.haarMeasure

/-- A labelled word vanishes whenever one integrated edge carries
nontrivial center charge. -/
theorem wilsonTaylorWordIntegral_eq_zero_of_charge_ne_zero
    (kappa : FiniteCenterChargeData rho) (Lambda : FiniteSpecification d G)
    {x : Site d} (C : Lattice.Cubic.Path x x)
    (w : List (WilsonTaylorLetter d)) (e : Lambda.dynamicEdges)
    (he : (wilsonTaylorWordChargeAt C w e.1 :
      ZMod (orderOf kappa.toCenterChargeData.omega)) ≠ 0) :
    wilsonTaylorWordIntegral (rho := rho) Lambda C w = 0 := by
  let kappa0 := kappa.toCenterChargeData
  have homega : kappa0.omega ≠ 0 := by
    intro h
    simpa [h] using kappa0.norm_omega
  let u : ℂˣ := Units.mk0 kappa0.omega homega
  have hphase : kappa0.omega ^ wilsonTaylorWordChargeAt C w e.1 ≠ 1 := by
    intro hphase
    apply he
    rw [CharP.intCast_eq_zero_iff]
    have hupow : u ^ wilsonTaylorWordChargeAt C w e.1 = 1 := by
      apply Units.ext
      simpa [u] using hphase
    have hdvd : (orderOf u : ℤ) ∣ wilsonTaylorWordChargeAt C w e.1 :=
      orderOf_dvd_iff_zpow_eq_one.mpr hupow
    simpa [u, ← orderOf_units] using hdvd
  unfold wilsonTaylorWordIntegral
  apply YangMills.Probability.integral_eq_zero_of_measurePreserving_eigen
    Lambda.haarMeasure (twistDynamicMeasurableEquiv kappa0 Lambda e)
    (measurePreserving_twistDynamic kappa0 Lambda e)
    (fun U ↦ wilsonTaylorWordMonomial rho C w (Lambda.evaluate U))
    (kappa0.omega ^ wilsonTaylorWordChargeAt C w e.1) hphase
  intro U
  rw [twistDynamicMeasurableEquiv_apply, evaluate_twistDynamic]
  exact wilsonTaylorWordMonomial_twistEdge kappa0 C w e.1 (Lambda.evaluate U)

/-- If a specification integrates every loop edge and every edge on each
word plaquette, a nonzero word supplies a center screening field. -/
theorem taylorScreens_wordMultiplicity_of_integral_ne_zero
    (kappa : FiniteCenterChargeData rho) (Lambda : FiniteSpecification d G)
    {x : Site d} (C : Lattice.Cubic.Path x x)
    (w : List (WilsonTaylorLetter d))
    (hC : C.edgeSupport ⊆ Lambda.dynamicEdges)
    (hw : ∀ q ∈ w, q.1.boundary.edgeSupport ⊆ Lambda.dynamicEdges)
    (hI : wilsonTaylorWordIntegral (rho := rho) Lambda C w ≠ 0) :
    Lattice.Cubic.TaylorScreens
      (orderOf kappa.toCenterChargeData.omega) C
      (wilsonTaylorWordPositive w) (wilsonTaylorWordNegative w) := by
  intro e
  rw [taylorChargeAt_wordMultiplicity]
  by_contra he
  by_cases hedyn : e ∈ Lambda.dynamicEdges
  · exact hI (wilsonTaylorWordIntegral_eq_zero_of_charge_ne_zero
      kappa Lambda C w ⟨e, hedyn⟩ he)
  · apply he
    have hCzero : C.edgeIncidence e = 0 :=
      Lattice.Cubic.Path.edgeChain_apply_eq_zero_of_not_mem_edgeSupport
        (R := ℤ) C e (fun heC ↦ hedyn (hC heC))
    have hwordzero : ((w.map fun q ↦
        if q.2 then -q.1.boundary.edgeIncidence e
        else q.1.boundary.edgeIncidence e).sum) = 0 := by
      apply List.sum_eq_zero
      intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨q, hq, rfl⟩ := hz
      have hqzero : q.1.boundary.edgeIncidence e = 0 :=
        Lattice.Cubic.Path.edgeChain_apply_eq_zero_of_not_mem_edgeSupport
          (R := ℤ) q.1.boundary e (fun heq ↦ hedyn (hw q hq heq))
      simp [hqzero]
    simp [wilsonTaylorWordChargeAt, hCzero, hwordzero]

/-- Hence every nonzero labelled word has length at least the loop's center
filling area. -/
theorem centerFillingArea_le_length_of_wilsonTaylorWordIntegral_ne_zero
    (kappa : FiniteCenterChargeData rho) (Lambda : FiniteSpecification d G)
    {x : Site d} (C : Lattice.Cubic.Path x x)
    (w : List (WilsonTaylorLetter d))
    (hC : C.edgeSupport ⊆ Lambda.dynamicEdges)
    (hw : ∀ q ∈ w, q.1.boundary.edgeSupport ⊆ Lambda.dynamicEdges)
    (hI : wilsonTaylorWordIntegral (rho := rho) Lambda C w ≠ 0) :
    Lattice.Cubic.centerFillingArea
        (orderOf kappa.toCenterChargeData.omega) C ≤ w.length := by
  rw [← taylorOrder_wordMultiplicity (w := w)]
  exact Lattice.Cubic.centerFillingArea_le_taylorOrder _ C _ _
    (taylorScreens_wordMultiplicity_of_integral_ne_zero
      kappa Lambda C w hC hw hI)

/-! ## Wilson-action moments -/

/-- A labelled Taylor word chosen from the active plaquettes by a function on
`Fin N`. -/
def wilsonTaylorWordOfLabel (Lambda : FiniteSpecification d G) {N : ℕ}
    (ell : Fin N → Lambda.activePlaquettes × Bool) :
    List (WilsonTaylorLetter d) :=
  List.ofFn fun i ↦ ((ell i).1.1, (ell i).2)

@[simp]
theorem length_wilsonTaylorWordOfLabel
    (Lambda : FiniteSpecification d G) {N : ℕ}
    (ell : Fin N → Lambda.activePlaquettes × Bool) :
    (wilsonTaylorWordOfLabel Lambda ell).length = N := by
  simp [wilsonTaylorWordOfLabel]

theorem mem_active_of_mem_wilsonTaylorWordOfLabel
    (Lambda : FiniteSpecification d G) {N : ℕ}
    (ell : Fin N → Lambda.activePlaquettes × Bool)
    {q : WilsonTaylorLetter d}
    (hq : q ∈ wilsonTaylorWordOfLabel Lambda ell) :
    q.1 ∈ Lambda.activePlaquettes := by
  simp only [wilsonTaylorWordOfLabel, List.mem_ofFn] at hq
  obtain ⟨i, rfl⟩ := hq
  exact (ell i).1.2

/-- The real normalized Wilson plaquette potential is the half-sum of the
character and its conjugate. -/
theorem wilsonPotential_eq_half_character_add_star
    (rho : ContinuousUnitaryRepData G n) (g : G) :
    (rho.wilsonPotential g : ℂ) =
      (2 : ℂ)⁻¹ * (rho.normalizedCharacter g +
        star (rho.normalizedCharacter g)) := by
  rw [rho.wilsonPotential_apply]
  apply Complex.ext
  · simp
    ring
  · simp

/-- The `N`th power of the finite Wilson action is the finite labelled-word
sum, with the expected factor `2⁻ᴺ`. -/
theorem action_wilsonPotential_pow_eq_sum_word
    (rho : ContinuousUnitaryRepData G n)
    (Lambda : FiniteSpecification d G) (N : ℕ)
    (U : DynamicConfiguration Lambda) :
    (FiniteVolume.action Lambda rho.wilsonPotential U : ℂ) ^ N =
      (2 : ℂ)⁻¹ ^ N *
        ∑ ell : Fin N → Lambda.activePlaquettes × Bool,
          ((wilsonTaylorWordOfLabel Lambda ell).map
            (fun q ↦ wilsonTaylorLetterValue rho q (Lambda.evaluate U))).prod := by
  have haction : (FiniteVolume.action Lambda rho.wilsonPotential U : ℂ) =
      ∑ q : Lambda.activePlaquettes × Bool,
        (2 : ℂ)⁻¹ * wilsonTaylorLetterValue rho (q.1.1, q.2)
          (Lambda.evaluate U) := by
    unfold FiniteVolume.action
    push_cast
    simp_rw [wilsonPotential_eq_half_character_add_star]
    rw [Finset.sum_subtype Lambda.activePlaquettes (fun _ ↦ Iff.rfl),
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p _
    rw [Fintype.sum_bool]
    simp [wilsonTaylorLetterValue, plaquetteHolonomy]
    ring
  rw [haction]
  rw [Fintype.sum_pow]
  simp_rw [Finset.prod_mul_distrib, Finset.prod_const]
  change _ = (2 : ℂ)⁻¹ ^ N * _
  unfold wilsonTaylorWordOfLabel
  simp only [List.map_ofFn, List.prod_ofFn, Function.comp_apply]
  rw [show (Finset.univ : Finset (Fin N)).card = N by simp,
    Finset.mul_sum]

/-- Moment obtained by differentiating an observable numerator `N` times. -/
def complexObservableNumeratorMoment (F : LocalObservable d G)
    (Lambda : FiniteSpecification d G) (Phi : RealPlaquettePotential G)
    (N : ℕ) (beta : ℂ) : ℂ :=
  ∫ U, (FiniteVolume.action Lambda Phi U : ℂ) ^ N *
      complexBoltzmannWeight Lambda Phi beta U * F (Lambda.evaluate U)
    ∂Lambda.haarMeasure

@[simp]
theorem complexObservableNumeratorMoment_zero
    (F : LocalObservable d G) (Lambda : FiniteSpecification d G)
    (Phi : RealPlaquettePotential G) (N : ℕ) :
    complexObservableNumeratorMoment F Lambda Phi N 0 =
      ∫ U, (FiniteVolume.action Lambda Phi U : ℂ) ^ N *
        F (Lambda.evaluate U) ∂Lambda.haarMeasure := by
  unfold complexObservableNumeratorMoment
  simp [complexBoltzmannWeight]

/-- At zero coupling, a Wilson-action moment is the finite sum of the
labelled Taylor-word Haar integrals. -/
theorem complexObservableNumeratorMoment_wilsonLoop_zero
    (rho : ContinuousUnitaryRepData G n)
    (Lambda : FiniteSpecification d G) {x : Site d}
    (C : Lattice.Cubic.Path x x) (N : ℕ) :
    complexObservableNumeratorMoment (rho.wilsonLoop C) Lambda
        rho.wilsonPotential N 0 =
      (2 : ℂ)⁻¹ ^ N *
        ∑ ell : Fin N → Lambda.activePlaquettes × Bool,
          wilsonTaylorWordIntegral (rho := rho) Lambda C
            (wilsonTaylorWordOfLabel Lambda ell) := by
  rw [complexObservableNumeratorMoment_zero]
  rw [show (∫ U, (FiniteVolume.action Lambda rho.wilsonPotential U : ℂ) ^ N *
        rho.wilsonLoop C (Lambda.evaluate U) ∂Lambda.haarMeasure) =
      ∫ U, (2 : ℂ)⁻¹ ^ N *
        (∑ ell : Fin N → Lambda.activePlaquettes × Bool,
          wilsonTaylorWordMonomial rho C
            (wilsonTaylorWordOfLabel Lambda ell) (Lambda.evaluate U))
        ∂Lambda.haarMeasure by
    apply integral_congr_ae
    exact ae_of_all _ fun U ↦ by
      dsimp only
      rw [action_wilsonPotential_pow_eq_sum_word rho Lambda N,
        rho.wilsonLoop_apply]
      unfold wilsonTaylorWordMonomial
      rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell _
      ring]
  rw [integral_const_mul]
  rw [integral_finsetSum]
  · rfl
  · intro ell _
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    let hprod : Continuous fun U : DynamicConfiguration Lambda ↦
        ∏ i : Fin N, wilsonTaylorLetterValue rho
          ((ell i).1.1, (ell i).2) (Lambda.evaluate U) := by
      apply continuous_finsetProd Finset.univ
      intro i _
      exact continuous_if_const ((ell i).2 = true) (fun _ ↦
        (rho.continuous_normalizedCharacter.comp
          ((continuous_holonomy (ell i).1.1.boundary).comp
            Lambda.continuous_evaluate)).star) (fun _ ↦
        rho.continuous_normalizedCharacter.comp
          ((continuous_holonomy (ell i).1.1.boundary).comp
            Lambda.continuous_evaluate))
    have hcontinuous : Continuous fun U : DynamicConfiguration Lambda ↦
        wilsonTaylorWordMonomial rho C
          (wilsonTaylorWordOfLabel Lambda ell) (Lambda.evaluate U) := by
      convert (rho.continuous_normalizedCharacter.comp
        ((continuous_holonomy C).comp Lambda.continuous_evaluate)).mul
        hprod using 1
      ext U
      simp [wilsonTaylorWordMonomial, wilsonTaylorWordOfLabel,
        List.prod_ofFn, List.map_ofFn, wilsonTaylorLetterValue, hprod]
    exact hcontinuous.continuousOn

/-- If every edge read by the finite Wilson action and the loop is dynamic,
all moments below the algebraic filling area vanish. -/
theorem complexObservableNumeratorMoment_wilsonLoop_zero_of_lt_fillingArea
    (kappa : FiniteCenterChargeData rho)
    (Lambda : FiniteSpecification d G) {x : Site d}
    (C : Lattice.Cubic.Path x x) (N : ℕ)
    (hC : C.edgeSupport ⊆ Lambda.dynamicEdges)
    (hactive : ∀ p ∈ Lambda.activePlaquettes,
      p.boundary.edgeSupport ⊆ Lambda.dynamicEdges)
    (hN : N < Lattice.Cubic.centerFillingArea
      (orderOf kappa.toCenterChargeData.omega) C) :
    complexObservableNumeratorMoment (rho.wilsonLoop C) Lambda
        rho.wilsonPotential N 0 = 0 := by
  rw [complexObservableNumeratorMoment_wilsonLoop_zero]
  suffices ∀ ell : Fin N → Lambda.activePlaquettes × Bool,
      wilsonTaylorWordIntegral (rho := rho) Lambda C
        (wilsonTaylorWordOfLabel Lambda ell) = 0 by
    simp [this]
  intro ell
  by_contra hword
  have harea := centerFillingArea_le_length_of_wilsonTaylorWordIntegral_ne_zero
    kappa Lambda C (wilsonTaylorWordOfLabel Lambda ell) hC
    (fun q hq ↦ hactive q.1
      (mem_active_of_mem_wilsonTaylorWordOfLabel Lambda ell hq)) hword
  rw [length_wilsonTaylorWordOfLabel] at harea
  omega

/-! ## Numerator derivatives -/

/-- Multiplying the `N`th moment by one more action factor gives its
pointwise derivative in the coupling. -/
theorem hasDerivAt_complexObservableNumeratorMomentIntegrand
    (F : LocalObservable d G) (Lambda : FiniteSpecification d G)
    (Phi : RealPlaquettePotential G) (N : ℕ) (beta : ℂ)
    (U : DynamicConfiguration Lambda) :
    HasDerivAt
      (fun z ↦ (FiniteVolume.action Lambda Phi U : ℂ) ^ N *
        complexBoltzmannWeight Lambda Phi z U * F (Lambda.evaluate U))
      ((FiniteVolume.action Lambda Phi U : ℂ) ^ (N + 1) *
        complexBoltzmannWeight Lambda Phi beta U * F (Lambda.evaluate U)) beta := by
  convert ((hasDerivAt_complexBoltzmannWeight Lambda Phi beta U).const_mul
    ((FiniteVolume.action Lambda Phi U : ℂ) ^ N)).mul_const
      (F (Lambda.evaluate U)) using 1 <;>
    simp [complexBoltzmannDerivative, complexBoltzmannWeight, pow_succ,
      mul_comm]
  left
  ring

/-- Every finite observable moment differentiates to the next moment. -/
theorem hasDerivAt_complexObservableNumeratorMoment
    (F : LocalObservable d G) (Lambda : FiniteSpecification d G)
    (Phi : RealPlaquettePotential G) (N : ℕ) (beta0 : ℂ) :
    HasDerivAt (complexObservableNumeratorMoment F Lambda Phi N)
      (complexObservableNumeratorMoment F Lambda Phi (N + 1) beta0) beta0 := by
  let B := actionBound Lambda Phi
  let R := ‖beta0‖ + 1
  let C := B ^ (N + 1) * Real.exp (R * B) *
    ‖F.toBoundedContinuousMap‖
  have hB : 0 ≤ B := actionBound_nonneg Lambda Phi
  have hmeas : ∀ᶠ beta in nhds beta0,
      AEStronglyMeasurable
        (fun U ↦ (FiniteVolume.action Lambda Phi U : ℂ) ^ N *
          complexBoltzmannWeight Lambda Phi beta U * F (Lambda.evaluate U))
        Lambda.haarMeasure :=
    Filter.Eventually.of_forall fun beta ↦
      ((((Complex.continuous_ofReal.comp (continuous_action Lambda Phi)).pow N).mul
        (continuous_complexBoltzmannWeight Lambda Phi beta)).mul
          (F.toContinuousMap.continuous.comp Lambda.continuous_evaluate)).aestronglyMeasurable
  have hbase : Integrable
      (fun U ↦ (FiniteVolume.action Lambda Phi U : ℂ) ^ N *
        complexBoltzmannWeight Lambda Phi beta0 U * F (Lambda.evaluate U))
      Lambda.haarMeasure := by
    apply Integrable.of_bound
      ((((Complex.continuous_ofReal.comp (continuous_action Lambda Phi)).pow N).mul
        (continuous_complexBoltzmannWeight Lambda Phi beta0)).mul
          (F.toContinuousMap.continuous.comp Lambda.continuous_evaluate)).aestronglyMeasurable
      (B ^ N * Real.exp (‖beta0‖ * B) * ‖F.toBoundedContinuousMap‖)
    exact ae_of_all _ fun U ↦ by
      change ‖(FiniteVolume.action Lambda Phi U : ℂ) ^ N *
        complexBoltzmannWeight Lambda Phi beta0 U * F (Lambda.evaluate U)‖ ≤ _
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real]
      gcongr
      · simpa only [B] using norm_action_le Lambda Phi U
      · exact norm_complexBoltzmannWeight_le Lambda Phi beta0 U
      · exact F.norm_apply_le (Lambda.evaluate U)
  have hderivMeas : AEStronglyMeasurable
      (fun U ↦ (FiniteVolume.action Lambda Phi U : ℂ) ^ (N + 1) *
        complexBoltzmannWeight Lambda Phi beta0 U * F (Lambda.evaluate U))
      Lambda.haarMeasure :=
    ((((Complex.continuous_ofReal.comp (continuous_action Lambda Phi)).pow (N + 1)).mul
      (continuous_complexBoltzmannWeight Lambda Phi beta0)).mul
        (F.toContinuousMap.continuous.comp Lambda.continuous_evaluate)).aestronglyMeasurable
  have hbound : ∀ᵐ U ∂Lambda.haarMeasure, ∀ beta ∈ Metric.ball beta0 1,
      ‖(FiniteVolume.action Lambda Phi U : ℂ) ^ (N + 1) *
        complexBoltzmannWeight Lambda Phi beta U * F (Lambda.evaluate U)‖ ≤ C := by
    refine ae_of_all _ fun U beta hbeta ↦ ?_
    have hbetaNorm : ‖beta‖ ≤ R := by
      calc
        ‖beta‖ = ‖beta0 + (beta - beta0)‖ := by ring_nf
        _ ≤ ‖beta0‖ + ‖beta - beta0‖ := norm_add_le _ _
        _ ≤ ‖beta0‖ + 1 := add_le_add_right
          ((show ‖beta - beta0‖ < 1 by
            simpa only [Metric.mem_ball, dist_eq_norm] using hbeta).le) _
        _ = R := rfl
    simp only [norm_mul, norm_pow, Complex.norm_real]
    calc
      _ ≤ B ^ (N + 1) * Real.exp (‖beta‖ * B) *
          ‖F.toBoundedContinuousMap‖ := by
        gcongr
        · simpa only [B] using norm_action_le Lambda Phi U
        · exact norm_complexBoltzmannWeight_le Lambda Phi beta U
        · exact F.norm_apply_le (Lambda.evaluate U)
      _ ≤ B ^ (N + 1) * Real.exp (R * B) *
          ‖F.toBoundedContinuousMap‖ := by
        gcongr
      _ = C := rfl
  have hdiff : ∀ᵐ U ∂Lambda.haarMeasure, ∀ beta ∈ Metric.ball beta0 1,
      HasDerivAt
        (fun z ↦ (FiniteVolume.action Lambda Phi U : ℂ) ^ N *
          complexBoltzmannWeight Lambda Phi z U * F (Lambda.evaluate U))
        ((FiniteVolume.action Lambda Phi U : ℂ) ^ (N + 1) *
          complexBoltzmannWeight Lambda Phi beta U * F (Lambda.evaluate U)) beta :=
    ae_of_all _ fun U beta _ ↦
      hasDerivAt_complexObservableNumeratorMomentIntegrand F Lambda Phi N beta U
  simpa only [complexObservableNumeratorMoment] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun beta U ↦ (FiniteVolume.action Lambda Phi U : ℂ) ^ N *
        complexBoltzmannWeight Lambda Phi beta U * F (Lambda.evaluate U))
      (F' := fun beta U ↦ (FiniteVolume.action Lambda Phi U : ℂ) ^ (N + 1) *
        complexBoltzmannWeight Lambda Phi beta U * F (Lambda.evaluate U))
      (bound := fun _ ↦ C)
      (Metric.ball_mem_nhds beta0 (by norm_num : (0 : ℝ) < 1))
      hmeas hbase hderivMeas hbound (integrable_const C) hdiff).2

/-- The iterated derivative of the finite numerator is its corresponding
action moment. -/
theorem iteratedDeriv_complexObservableNumerator
    (F : LocalObservable d G) (Lambda : FiniteSpecification d G)
    (Phi : RealPlaquettePotential G) (N : ℕ) (beta : ℂ) :
    iteratedDeriv N (complexObservableNumerator F Lambda Phi) beta =
      complexObservableNumeratorMoment F Lambda Phi N beta := by
  induction N generalizing beta with
  | zero =>
      unfold complexObservableNumeratorMoment complexObservableNumerator
      simp
  | succ N ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv N (complexObservableNumerator F Lambda Phi) =ᶠ[nhds beta]
          complexObservableNumeratorMoment F Lambda Phi N := by
        filter_upwards [] with z
        exact ih (beta := z)
      rw [heq.deriv_eq]
      exact (hasDerivAt_complexObservableNumeratorMoment
        F Lambda Phi N beta).deriv

/-- Full-edge center selection kills every finite numerator jet strictly
below the filling area. -/
theorem iteratedDeriv_complexObservableNumerator_wilsonLoop_zero_of_lt_fillingArea
    (kappa : FiniteCenterChargeData rho)
    (Lambda : FiniteSpecification d G) {x : Site d}
    (C : Lattice.Cubic.Path x x) (N : ℕ)
    (hC : C.edgeSupport ⊆ Lambda.dynamicEdges)
    (hactive : ∀ p ∈ Lambda.activePlaquettes,
      p.boundary.edgeSupport ⊆ Lambda.dynamicEdges)
    (hN : N < Lattice.Cubic.centerFillingArea
      (orderOf kappa.toCenterChargeData.omega) C) :
    iteratedDeriv N
      (complexObservableNumerator (rho.wilsonLoop C) Lambda rho.wilsonPotential) 0 = 0 := by
  rw [iteratedDeriv_complexObservableNumerator]
  exact complexObservableNumeratorMoment_wilsonLoop_zero_of_lt_fillingArea
    kappa Lambda C N hC hactive hN

/-- Division by the nonvanishing partition function does not lower the
center-selected order of vanishing.  Thus the normalized finite-volume
Wilson expectation has the same zero Taylor jet below the filling area as
its unnormalized numerator. -/
theorem iteratedDeriv_complexGibbsExpectation_wilsonLoop_zero_of_lt_fillingArea
    (kappa : FiniteCenterChargeData rho)
    (Lambda : FiniteSpecification d G) {x : Site d}
    (C : Lattice.Cubic.Path x x) (N : ℕ)
    (hC : C.edgeSupport ⊆ Lambda.dynamicEdges)
    (hactive : ∀ p ∈ Lambda.activePlaquettes,
      p.boundary.edgeSupport ⊆ Lambda.dynamicEdges)
    (hN : N < Lattice.Cubic.centerFillingArea
      (orderOf kappa.toCenterChargeData.omega) C) :
    iteratedDeriv N
      (complexGibbsExpectation (rho.wilsonLoop C) Lambda rho.wilsonPotential) 0 = 0 := by
  let A := Lattice.Cubic.centerFillingArea
    (orderOf kappa.toCenterChargeData.omega) C
  let Z := complexPartitionFunction Lambda rho.wilsonPotential
  let Q := complexObservableNumerator (rho.wilsonLoop C) Lambda rho.wilsonPotential
  have hQ : AnalyticAt ℂ Q 0 :=
    complexObservableNumerator_entire (rho.wilsonLoop C) Lambda
      rho.wilsonPotential 0 (Set.mem_univ 0)
  have hZ : AnalyticAt ℂ Z 0 :=
    complexPartitionFunction_entire Lambda rho.wilsonPotential
      0 (Set.mem_univ 0)
  have hZ0 : Z 0 ≠ 0 := by
    simp [Z]
  have hZinv : AnalyticAt ℂ Z⁻¹ 0 := hZ.inv hZ0
  have hQorder : (A : ℕ∞) ≤ analyticOrderAt Q 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hQ]
    intro i hi
    exact iteratedDeriv_complexObservableNumerator_wilsonLoop_zero_of_lt_fillingArea
      kappa Lambda C i hC hactive hi
  have hproduct : AnalyticAt ℂ (Z⁻¹ * Q) 0 := hZinv.mul hQ
  have hproductOrder : (A : ℕ∞) ≤ analyticOrderAt (Z⁻¹ * Q) 0 := by
    rw [analyticOrderAt_mul hZinv hQ]
    exact hQorder.trans (le_add_left (le_refl _))
  have hjets :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hproduct).mp hproductOrder
  change iteratedDeriv N (Z⁻¹ * Q) 0 = 0
  exact hjets N hN

/-! ## Direct rectangular filling-order selection -/

/-- A nonzero labelled Taylor word screening an `r`-by-`s` rectangle has at
least `r * s` letters. This is the direct rectangular form of center
selection; it does not pass through the abstract filling infimum. -/
theorem rectangle_area_le_length_of_wilsonTaylorWordIntegral_ne_zero
    (kappa : FiniteCenterChargeData rho) (Lambda : FiniteSpecification d G)
    (x : Site d) (i j : Fin d) (hij : i ≠ j) (r s : ℕ)
    (w : List (WilsonTaylorLetter d))
    (hC : (Lattice.Cubic.Path.rectangleBoundary x i j r s).edgeSupport ⊆
      Lambda.dynamicEdges)
    (hw : ∀ q ∈ w, q.1.boundary.edgeSupport ⊆ Lambda.dynamicEdges)
    (hI : wilsonTaylorWordIntegral (rho := rho) Lambda
      (Lattice.Cubic.Path.rectangleBoundary x i j r s) w ≠ 0) :
    r * s ≤ w.length := by
  have hm : orderOf kappa.toCenterChargeData.omega ≠ 1 := by
    intro h
    exact kappa.toCenterChargeData.nontrivial (orderOf_eq_one_iff.mp h)
  rw [← taylorOrder_wordMultiplicity (w := w)]
  exact Lattice.Cubic.rectangle_area_le_taylorOrder_of_taylorScreens
    (orderOf kappa.toCenterChargeData.omega) hm x i j hij r s _ _
    (taylorScreens_wordMultiplicity_of_integral_ne_zero
      kappa Lambda (Lattice.Cubic.Path.rectangleBoundary x i j r s) w hC hw hI)

/-- Every Wilson-action moment below the geometric rectangle area vanishes. -/
theorem complexObservableNumeratorMoment_wilsonRectangle_zero_of_lt_area
    (kappa : FiniteCenterChargeData rho)
    (Lambda : FiniteSpecification d G) (x : Site d)
    (i j : Fin d) (hij : i ≠ j) (r s N : ℕ)
    (hC : (Lattice.Cubic.Path.rectangleBoundary x i j r s).edgeSupport ⊆
      Lambda.dynamicEdges)
    (hactive : ∀ p ∈ Lambda.activePlaquettes,
      p.boundary.edgeSupport ⊆ Lambda.dynamicEdges)
    (hN : N < r * s) :
    complexObservableNumeratorMoment
        (rho.wilsonLoop (Lattice.Cubic.Path.rectangleBoundary x i j r s))
        Lambda rho.wilsonPotential N 0 = 0 := by
  rw [complexObservableNumeratorMoment_wilsonLoop_zero]
  suffices ∀ ell : Fin N → Lambda.activePlaquettes × Bool,
      wilsonTaylorWordIntegral (rho := rho) Lambda
        (Lattice.Cubic.Path.rectangleBoundary x i j r s)
        (wilsonTaylorWordOfLabel Lambda ell) = 0 by
    simp [this]
  intro ell
  by_contra hword
  have harea := rectangle_area_le_length_of_wilsonTaylorWordIntegral_ne_zero
    kappa Lambda x i j hij r s (wilsonTaylorWordOfLabel Lambda ell) hC
    (fun q hq ↦ hactive q.1
      (mem_active_of_mem_wilsonTaylorWordOfLabel Lambda ell hq)) hword
  rw [length_wilsonTaylorWordOfLabel] at harea
  omega

/-- The finite normalized Wilson expectation has zero Taylor jet in every
order strictly below the rectangle area. -/
theorem iteratedDeriv_complexGibbsExpectation_wilsonRectangle_zero_of_lt_area
    (kappa : FiniteCenterChargeData rho)
    (Lambda : FiniteSpecification d G) (x : Site d)
    (i j : Fin d) (hij : i ≠ j) (r s N : ℕ)
    (hC : (Lattice.Cubic.Path.rectangleBoundary x i j r s).edgeSupport ⊆
      Lambda.dynamicEdges)
    (hactive : ∀ p ∈ Lambda.activePlaquettes,
      p.boundary.edgeSupport ⊆ Lambda.dynamicEdges)
    (hN : N < r * s) :
    iteratedDeriv N
      (complexGibbsExpectation
        (rho.wilsonLoop (Lattice.Cubic.Path.rectangleBoundary x i j r s))
        Lambda rho.wilsonPotential) 0 = 0 := by
  let A := r * s
  let Z := complexPartitionFunction Lambda rho.wilsonPotential
  let Q := complexObservableNumerator
    (rho.wilsonLoop (Lattice.Cubic.Path.rectangleBoundary x i j r s))
    Lambda rho.wilsonPotential
  have hQ : AnalyticAt ℂ Q 0 :=
    complexObservableNumerator_entire
      (rho.wilsonLoop (Lattice.Cubic.Path.rectangleBoundary x i j r s))
      Lambda rho.wilsonPotential 0 (Set.mem_univ 0)
  have hZ : AnalyticAt ℂ Z 0 :=
    complexPartitionFunction_entire Lambda rho.wilsonPotential
      0 (Set.mem_univ 0)
  have hZ0 : Z 0 ≠ 0 := by simp [Z]
  have hZinv : AnalyticAt ℂ Z⁻¹ 0 := hZ.inv hZ0
  have hQorder : (A : ℕ∞) ≤ analyticOrderAt Q 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hQ]
    intro q hq
    rw [iteratedDeriv_complexObservableNumerator]
    exact complexObservableNumeratorMoment_wilsonRectangle_zero_of_lt_area
      kappa Lambda x i j hij r s q hC hactive hq
  have hproduct : AnalyticAt ℂ (Z⁻¹ * Q) 0 := hZinv.mul hQ
  have hproductOrder : (A : ℕ∞) ≤ analyticOrderAt (Z⁻¹ * Q) 0 := by
    rw [analyticOrderAt_mul hZinv hQ]
    exact hQorder.trans (le_add_left (le_refl _))
  have hjets :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hproduct).mp hproductOrder
  change iteratedDeriv N (Z⁻¹ * Q) 0 = 0
  exact hjets N hN

end

end YangMills.StrongCoupling
