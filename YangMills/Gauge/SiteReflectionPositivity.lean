/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.SiteReflection
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Finite-volume site-reflection positivity

After supplying a reflection-adapted partition of a finite set of edge
variables, a field is recorded as `(U₀, U₋, U₊)`: variables in the integer
reflection plane and two reflected copies of the strict half-volume
variables.  The Wilson action is supplied in the form

`S(U₀, U₋, U₊) = S₊(U₀, U₋) + S₀(U₀) + S₊(U₀, U₊)`.

This file proves the product-Haar Fubini identity turning the reflected Gibbs
pairing into an integral of products of half-volume amplitudes.  On the
diagonal it is a weighted square modulus.  The positive algebra consists of
all continuous complex observables of `(U₀, U₊)`; no gauge-invariance
hypothesis is imposed.  The geometric identification of this abstract split
with every standard reflection-symmetric cubic `FiniteSpecification` is a
separate future theorem.
-/

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace YangMills.Gauge

noncomputable section

namespace SiteReflection

/-- A configuration on one strict side of a site-reflection plane. -/
abbrev SideConfiguration (G : Type*) (P : Type*) := P → G

/-- The edge variables fixed by an integer/site reflection. -/
abbrev PlaneConfiguration (G : Type*) (O : Type*) := O → G

/-- Variables visible to an observable in the positive half-volume. -/
abbrev HalfConfiguration (G : Type*) (P O : Type*) :=
  PlaneConfiguration G O × SideConfiguration G P

/-- The plane variables followed by the negative and positive reflected copies. -/
abbrev ReflectedConfiguration (G : Type*) (P O : Type*) :=
  PlaneConfiguration G O ×
    (SideConfiguration G P × SideConfiguration G P)

/-- A single finite label family for the plane, negative, and positive edge
variables.  This is the source type before applying the reflection partition. -/
abbrev ReflectedLabel (P O : Type*) := O ⊕ (P ⊕ P)

variable {G P O : Type*}

/-- The measurable equivalence implementing the finite variable partition
`A ↦ (A₀, A₋, A₊)`. -/
def reflectedVariableEquiv [MeasurableSpace G] :
    (ReflectedLabel P O → G) ≃ᵐ ReflectedConfiguration G P O :=
  (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : O ⊕ (P ⊕ P) => G)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : P ⊕ P => G)))

/-- The exact normal form obtained by partitioning a finite Wilson action into
positive plaquettes, their reflected partners, and plaquettes in the integer
reflection plane.  The fixed label types make the product-measure split
canonical. -/
structure WilsonActionDecomposition (G : Type*) (P O : Type*)
    [TopologicalSpace G] where
  positiveAction : C(HalfConfiguration G P O, ℝ)
  planeAction : C(PlaneConfiguration G O, ℝ)

variable [TopologicalSpace G]

namespace WilsonActionDecomposition

/-- The full action reconstructed from its positive-side and plane pieces. -/
def action (D : WilsonActionDecomposition G P O) :
    ReflectedConfiguration G P O → ℝ :=
  fun U => D.positiveAction (U.1, U.2.1) + D.planeAction U.1 +
    D.positiveAction (U.1, U.2.2)

/-- The decomposed finite Wilson action is continuous. -/
theorem continuous_action (D : WilsonActionDecomposition G P O) :
    Continuous D.action := by
  unfold action
  fun_prop

/-- Reflection exchanges the two strict half-volume fields and fixes the
variables in the integer plane. -/
def reflect (U : ReflectedConfiguration G P O) :
    ReflectedConfiguration G P O :=
  (U.1, (U.2.2, U.2.1))

omit [TopologicalSpace G] in
@[simp]
theorem reflect_reflect (U : ReflectedConfiguration G P O) :
    reflect (reflect U) = U := by
  rcases U with ⟨Uzero, Uminus, Uplus⟩
  rfl

theorem continuous_reflect :
    Continuous (reflect : ReflectedConfiguration G P O →
      ReflectedConfiguration G P O) := by
  unfold reflect
  fun_prop

@[simp]
theorem action_reflect (D : WilsonActionDecomposition G P O)
    (U : ReflectedConfiguration G P O) :
    D.action (reflect U) = D.action U := by
  simp only [action, reflect]
  ring

end WilsonActionDecomposition

/-- A positive-side observable is an arbitrary continuous function of the
plane variables and the positive strict half-volume variables. -/
abbrev PositiveObservable (G : Type*) (P O : Type*) [TopologicalSpace G] :=
  C(HalfConfiguration G P O, ℂ)

/-- Lift a positive-side observable to the full reflected finite volume. -/
def liftPositive (F : PositiveObservable G P O) :
    C(ReflectedConfiguration G P O, ℂ) where
  toFun U := F (U.1, U.2.2)
  continuous_toFun := by fun_prop

/-- Pointwise complex conjugation of a continuous observable. -/
def observableConj {X : Type*} [TopologicalSpace X] (F : C(X, ℂ)) : C(X, ℂ) where
  toFun x := conj (F x)
  continuous_toFun := Complex.continuous_conj.comp F.continuous

/-- Anti-linear reflection of a full finite-volume observable. -/
def theta (F : C(ReflectedConfiguration G P O, ℂ)) :
    C(ReflectedConfiguration G P O, ℂ) where
  toFun U := conj (F (WilsonActionDecomposition.reflect U))
  continuous_toFun := Complex.continuous_conj.comp
    (F.continuous.comp WilsonActionDecomposition.continuous_reflect)

@[simp]
theorem theta_apply (F : C(ReflectedConfiguration G P O, ℂ))
    (U : ReflectedConfiguration G P O) :
    theta F U = conj (F (WilsonActionDecomposition.reflect U)) :=
  rfl

@[simp]
theorem theta_liftPositive_apply (F : PositiveObservable G P O)
    (U : ReflectedConfiguration G P O) :
    theta (liftPositive F) U = conj (F (U.1, U.2.1)) :=
  rfl

@[simp]
theorem theta_add (F H : C(ReflectedConfiguration G P O, ℂ)) :
    theta (F + H) = theta F + theta H := by
  ext U
  simp [theta, map_add]

@[simp]
theorem theta_mul (F H : C(ReflectedConfiguration G P O, ℂ)) :
    theta (F * H) = theta F * theta H := by
  ext U
  simp [theta, map_mul]

@[simp]
theorem theta_smul (c : ℂ) (F : C(ReflectedConfiguration G P O, ℂ)) :
    theta (c • F) = conj c • theta F := by
  ext U
  simp [theta, map_mul]

@[simp]
theorem theta_observableConj (F : C(ReflectedConfiguration G P O, ℂ)) :
    theta (observableConj F) = observableConj (theta F) := by
  ext U
  simp [theta, observableConj]

@[simp]
theorem theta_theta (F : C(ReflectedConfiguration G P O, ℂ)) :
    theta (theta F) = F := by
  ext U
  simp [theta]

@[simp]
theorem liftPositive_add (F H : PositiveObservable G P O) :
    liftPositive (F + H) = liftPositive F + liftPositive H := by
  ext U
  rfl

@[simp]
theorem liftPositive_mul (F H : PositiveObservable G P O) :
    liftPositive (F * H) = liftPositive F * liftPositive H := by
  ext U
  rfl

@[simp]
theorem liftPositive_smul (c : ℂ) (F : PositiveObservable G P O) :
    liftPositive (c • F) = c • liftPositive F := by
  ext U
  rfl

@[simp]
theorem liftPositive_observableConj (F : PositiveObservable G P O) :
    liftPositive (observableConj F) = observableConj (liftPositive F) := by
  ext U
  rfl

section WilsonPlaquettes

open Lattice.Cubic

variable {d : ℕ} [Group G] [IsTopologicalGroup G]

/-- Construct the positive part of the action from an explicit finite family
of Wilson plaquettes evaluated in a continuous half-volume field. -/
def positiveWilsonAction (Φ : RealPlaquettePotential G)
    (evaluate : C(HalfConfiguration G P O, Configuration d G))
    (plaquettes : Finset (Plaquette d)) : C(HalfConfiguration G P O, ℝ) where
  toFun U := ∑ p ∈ plaquettes, Φ (holonomy (evaluate U) p.boundary)
  continuous_toFun := by
    exact continuous_finsetSum plaquettes fun p _ =>
      Φ.toContinuousMap.continuous.comp
        ((continuous_holonomy p.boundary).comp evaluate.continuous)

/-- Construct the action in the reflection plane from explicit Wilson
plaquettes evaluated in the plane field. -/
def planeWilsonAction (Φ : RealPlaquettePotential G)
    (evaluate : C(PlaneConfiguration G O, Configuration d G))
    (plaquettes : Finset (Plaquette d)) : C(PlaneConfiguration G O, ℝ) where
  toFun U := ∑ p ∈ plaquettes, Φ (holonomy (evaluate U) p.boundary)
  continuous_toFun := by
    exact continuous_finsetSum plaquettes fun p _ =>
      Φ.toContinuousMap.continuous.comp
        ((continuous_holonomy p.boundary).comp evaluate.continuous)

/-- An explicit finite Wilson-plaquette action supplies the reflection
decomposition used below.  Its two strict-side sums are related geometrically
by `RealPlaquettePotential.apply_holonomy_siteReflectConfiguration`. -/
def WilsonActionDecomposition.ofWilsonPlaquettes
    (Φ : RealPlaquettePotential G)
    (evaluatePositive : C(HalfConfiguration G P O, Configuration d G))
    (evaluatePlane : C(PlaneConfiguration G O, Configuration d G))
    (positivePlaquettes planePlaquettes : Finset (Plaquette d)) :
    WilsonActionDecomposition G P O where
  positiveAction := positiveWilsonAction Φ evaluatePositive positivePlaquettes
  planeAction := planeWilsonAction Φ evaluatePlane planePlaquettes

end WilsonPlaquettes

section Haar

variable [Group G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [CompactSpace G] [GaugeHaarProbability G]
  [Fintype P] [Fintype O]

/-- Product Haar on the variables fixed by site reflection. -/
abbrev planeHaar : Measure (PlaneConfiguration G O) :=
  ProductHaar.measure G O

/-- Product Haar on one strict half of the finite volume. -/
abbrev sideHaar : Measure (SideConfiguration G P) :=
  ProductHaar.measure G P

/-- The product-Haar measure after the reflection variable partition. -/
abbrev reflectedHaar : Measure (ReflectedConfiguration G P O) :=
  (planeHaar (G := G) (O := O)).prod
    ((sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P)))

omit [BorelSpace G] [CompactSpace G] in
/-- The explicit variable partition preserves finite product Haar. -/
theorem measurePreserving_reflectedVariableEquiv :
    MeasurePreserving (reflectedVariableEquiv (G := G) (P := P) (O := O))
      (ProductHaar.measure G (ReflectedLabel P O)) reflectedHaar := by
  let splitOuter := MeasureTheory.measurePreserving_sumPiEquivProdPi
    (fun _ : O ⊕ (P ⊕ P) => GaugeHaarProbability.haar G)
  let splitSides := MeasureTheory.measurePreserving_sumPiEquivProdPi
    (fun _ : P ⊕ P => GaugeHaarProbability.haar G)
  exact (MeasurePreserving.prod
      (MeasurePreserving.id (planeHaar (G := G) (O := O))) splitSides).comp splitOuter

variable (D : WilsonActionDecomposition G P O)

namespace WilsonActionDecomposition

omit [Group G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] [Fintype P] [Fintype O] in
/-- Reflection preserves the uniform norm of every continuous full-volume
observable. -/
theorem theta_preserves_norm
    (F : C(ReflectedConfiguration G P O, ℂ)) :
    ‖theta F‖ = ‖F‖ := by
  apply le_antisymm
  · rw [ContinuousMap.norm_le (theta F) (norm_nonneg F)]
    intro U
    rw [show ‖theta F U‖ = ‖F (reflect U)‖ by simp [theta]]
    exact F.norm_coe_le_norm _
  · rw [ContinuousMap.norm_le F (norm_nonneg (theta F))]
    intro U
    calc
      ‖F U‖ = ‖theta F (reflect U)‖ := by simp [theta]
      _ ≤ ‖theta F‖ := (theta F).norm_coe_le_norm _

/-- The Boltzmann weight of the decomposed finite Wilson action. -/
def boltzmannWeight (β : ℝ) (U : ReflectedConfiguration G P O) : ℝ :=
  Real.exp (β * D.action U)

omit [Group G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G] [Fintype P] [Fintype O] in
theorem continuous_boltzmannWeight (β : ℝ) :
    Continuous (D.boltzmannWeight β) := by
  exact Real.continuous_exp.comp (continuous_const.mul D.continuous_action)

theorem integrable_boltzmannWeight (β : ℝ) :
    Integrable (D.boltzmannWeight β) reflectedHaar :=
  (D.continuous_boltzmannWeight β).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Partition function in the reflection-adapted variables. -/
def partitionFunction (β : ℝ) : ℝ :=
  ∫ U, D.boltzmannWeight β U ∂reflectedHaar

theorem partitionFunction_pos (β : ℝ) : 0 < D.partitionFunction β := by
  unfold partitionFunction boltzmannWeight
  exact integral_exp_pos (D.integrable_boltzmannWeight β)

/-- The half-volume amplitude at fixed plane field. -/
def halfAmplitude (β : ℝ) (F : PositiveObservable G P O)
    (Uzero : PlaneConfiguration G O) : ℂ :=
  ∫ Uplus, (Real.exp (β * D.positiveAction (Uzero, Uplus)) : ℂ) * F (Uzero, Uplus)
    ∂sideHaar

/-- The unnormalized reflection pairing, written in its factorized
half-volume form. -/
def factorizedPairing (β : ℝ) (F H : PositiveObservable G P O) : ℂ :=
  ∫ Uzero, (Real.exp (β * D.planeAction Uzero) : ℂ) *
      conj (D.halfAmplitude β F Uzero) * D.halfAmplitude β H Uzero
    ∂planeHaar

/-- The unnormalized Gibbs integral of `(ΘF) H` on the full reflected volume. -/
def gibbsReflectionPairing (β : ℝ) (F H : PositiveObservable G P O) : ℂ :=
  ∫ U, (D.boltzmannWeight β U : ℂ) *
      theta (liftPositive F) U * liftPositive H U
    ∂reflectedHaar

/-- The full reflected Gibbs integrand is continuous and hence integrable on
the compact finite product of group variables. -/
theorem integrable_gibbsReflectionIntegrand (β : ℝ)
    (F H : PositiveObservable G P O) :
    Integrable (fun U => (D.boltzmannWeight β U : ℂ) *
      theta (liftPositive F) U * liftPositive H U) reflectedHaar := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact ((Complex.continuous_ofReal.comp (D.continuous_boltzmannWeight β)).mul
    (theta (liftPositive F)).continuous).mul (liftPositive H).continuous

omit [BorelSpace G] [SecondCountableTopology G] [CompactSpace G] [Fintype O] in
/-- At fixed plane field the two strict-side Haar integrals factor. -/
theorem integral_sidePair_eq_halfAmplitude (β : ℝ)
    (F H : PositiveObservable G P O) (Uzero : PlaneConfiguration G O) :
    (∫ V : SideConfiguration G P × SideConfiguration G P,
        (D.boltzmannWeight β (Uzero, V) : ℂ) *
          theta (liftPositive F) (Uzero, V) * liftPositive H (Uzero, V)
      ∂(sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P))) =
      (Real.exp (β * D.planeAction Uzero) : ℂ) *
        conj (D.halfAmplitude β F Uzero) * D.halfAmplitude β H Uzero := by
  let leftFactor : SideConfiguration G P → ℂ := fun Uminus =>
    conj ((Real.exp (β * D.positiveAction (Uzero, Uminus)) : ℂ) *
      F (Uzero, Uminus))
  let rightFactor : SideConfiguration G P → ℂ := fun Uplus =>
    (Real.exp (β * D.positiveAction (Uzero, Uplus)) : ℂ) * H (Uzero, Uplus)
  have hpoint : ∀ V : SideConfiguration G P × SideConfiguration G P,
      (D.boltzmannWeight β (Uzero, V) : ℂ) *
          theta (liftPositive F) (Uzero, V) * liftPositive H (Uzero, V) =
        (Real.exp (β * D.planeAction Uzero) : ℂ) *
          (leftFactor V.1 * rightFactor V.2) := by
    intro V
    simp only [boltzmannWeight, WilsonActionDecomposition.action,
      theta, WilsonActionDecomposition.reflect, liftPositive, ContinuousMap.coe_mk,
      leftFactor, rightFactor]
    rw [show β * (D.positiveAction (Uzero, V.1) + D.planeAction Uzero +
        D.positiveAction (Uzero, V.2)) =
      β * D.positiveAction (Uzero, V.1) + β * D.planeAction Uzero +
        β * D.positiveAction (Uzero, V.2) by ring]
    rw [Real.exp_add, Real.exp_add]
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  rw [integral_prod_mul leftFactor rightFactor]
  rw [show (∫ Uminus, leftFactor Uminus ∂sideHaar) =
      conj (D.halfAmplitude β F Uzero) by
    change (∫ Uminus, conj ((Real.exp
      (β * D.positiveAction (Uzero, Uminus)) : ℂ) * F (Uzero, Uminus))
      ∂sideHaar) = _
    rw [integral_conj]
    rfl]
  change (Real.exp (β * D.planeAction Uzero) : ℂ) *
      (conj (D.halfAmplitude β F Uzero) * D.halfAmplitude β H Uzero) = _
  ring

/-- Fubini and the reflection variable partition identify the full Gibbs
integral with the factorized half-volume pairing. -/
theorem gibbsReflectionPairing_eq_factorized (β : ℝ)
    (F H : PositiveObservable G P O) :
    D.gibbsReflectionPairing β F H = D.factorizedPairing β F H := by
  unfold gibbsReflectionPairing factorizedPairing reflectedHaar
  rw [integral_prod _ (D.integrable_gibbsReflectionIntegrand β F H)]
  congr 1
  funext Uzero
  exact D.integral_sidePair_eq_halfAmplitude β F H Uzero

/-- The weighted half-volume amplitude as a continuous function of the plane
field. -/
def weightedAmplitude (β : ℝ) (F : PositiveObservable G P O) :
    C(PlaneConfiguration G O, ℂ) where
  toFun Uzero :=
    (Real.exp (β * D.planeAction Uzero / 2) : ℂ) * D.halfAmplitude β F Uzero
  continuous_toFun := by
    let K : C(HalfConfiguration G P O, ℂ) :=
      ⟨fun U => (Real.exp (β * D.positiveAction U) : ℂ) * F U, by fun_prop⟩
    let Kswap : C(SideConfiguration G P × PlaneConfiguration G O, ℂ) :=
      ⟨fun U => K (U.2, U.1), by fun_prop⟩
    let Kcurried : C(SideConfiguration G P,
        C(PlaneConfiguration G O, ℂ)) := ContinuousMap.curry Kswap
    have hKint : Integrable Kcurried sideHaar :=
      Kcurried.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    let A : C(PlaneConfiguration G O, ℂ) := ∫ Uside, Kcurried Uside ∂sideHaar
    have hA : ∀ Uzero, A Uzero = D.halfAmplitude β F Uzero := by
      intro Uzero
      exact ContinuousMap.integral_apply hKint Uzero
    apply Continuous.mul
    · fun_prop
    · apply A.continuous.congr
      intro Uzero
      exact hA Uzero

omit [Fintype O] in
@[simp]
theorem weightedAmplitude_apply (β : ℝ) (F : PositiveObservable G P O)
    (Uzero : PlaneConfiguration G O) :
    D.weightedAmplitude β F Uzero =
      (Real.exp (β * D.planeAction Uzero / 2) : ℂ) *
        D.halfAmplitude β F Uzero :=
  rfl

/-- The factorized reflection pairing is the ordinary complex `L²` inner
product of the weighted half-volume amplitudes. -/
theorem factorizedPairing_eq_inner (β : ℝ)
    (F H : PositiveObservable G P O) :
    D.factorizedPairing β F H =
      ⟪ContinuousMap.toLp 2 planeHaar ℂ (D.weightedAmplitude β F),
        ContinuousMap.toLp 2 planeHaar ℂ (D.weightedAmplitude β H)⟫_ℂ := by
  rw [MeasureTheory.ContinuousMap.inner_toLp]
  unfold factorizedPairing
  apply integral_congr_ae
  filter_upwards with Uzero
  simp only [weightedAmplitude_apply, map_mul]
  norm_cast
  rw [Complex.conj_ofReal]
  rw [show Real.exp (β * D.planeAction Uzero) =
      Real.exp (β * D.planeAction Uzero / 2) *
        Real.exp (β * D.planeAction Uzero / 2) by
    rw [← Real.exp_add]
    congr 1
    ring]
  push_cast
  ring

omit [BorelSpace G] [SecondCountableTopology G] [CompactSpace G] in
/-- The reflection pairing before normalization is a weighted square modulus. -/
theorem factorizedPairing_self_eq_squareModulus (β : ℝ)
    (F : PositiveObservable G P O) :
    D.factorizedPairing β F F =
      ∫ Uzero, (Real.exp (β * D.planeAction Uzero) : ℂ) *
        (Complex.normSq (D.halfAmplitude β F Uzero) : ℂ) ∂planeHaar := by
  unfold factorizedPairing
  congr 1
  funext Uzero
  rw [mul_assoc, show conj (D.halfAmplitude β F Uzero) *
      D.halfAmplitude β F Uzero =
      D.halfAmplitude β F Uzero * conj (D.halfAmplitude β F Uzero) by ac_rfl]
  rw [Complex.mul_conj]

/-- Finite-volume site reflection positivity for the full positive algebra.
The statement holds for every real coupling, and in particular for every
`β ≥ 0` required by Milestone 17. -/
theorem siteReflectionPositivity (β : ℝ)
    (F : PositiveObservable G P O) :
    Complex.im (D.gibbsReflectionPairing β F F) = 0 ∧
      0 ≤ Complex.re (D.gibbsReflectionPairing β F F) := by
  rw [D.gibbsReflectionPairing_eq_factorized,
    D.factorizedPairing_eq_inner]
  let f := ContinuousMap.toLp 2 planeHaar ℂ (D.weightedAmplitude β F)
  change Complex.im ⟪f, f⟫_ℂ = 0 ∧ 0 ≤ Complex.re ⟪f, f⟫_ℂ
  exact ⟨inner_self_im (𝕜 := ℂ) f, inner_self_nonneg (𝕜 := ℂ) (x := f)⟩

/-- The normalized reflection inner product induced by the finite-volume
Wilson Gibbs state. -/
def reflectionInnerProduct (β : ℝ) (F H : PositiveObservable G P O) : ℂ :=
  (D.partitionFunction β : ℂ)⁻¹ * D.gibbsReflectionPairing β F H

theorem reflectionInnerProduct_self_nonneg (β : ℝ)
    (F : PositiveObservable G P O) :
    Complex.im (D.reflectionInnerProduct β F F) = 0 ∧
      0 ≤ Complex.re (D.reflectionInnerProduct β F F) := by
  rw [reflectionInnerProduct, D.gibbsReflectionPairing_eq_factorized,
    D.factorizedPairing_eq_inner]
  have hZ : 0 < D.partitionFunction β := D.partitionFunction_pos β
  let f := ContinuousMap.toLp 2 planeHaar ℂ (D.weightedAmplitude β F)
  change Complex.im ((D.partitionFunction β : ℂ)⁻¹ * ⟪f, f⟫_ℂ) = 0 ∧
    0 ≤ Complex.re ((D.partitionFunction β : ℂ)⁻¹ * ⟪f, f⟫_ℂ)
  rw [inner_self_eq_norm_sq_to_K]
  have hscale : ((D.partitionFunction β : ℂ)⁻¹) =
      ((D.partitionFunction β)⁻¹ : ℝ) := by norm_cast
  rw [hscale]
  constructor
  · rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    change (D.partitionFunction β)⁻¹ *
      Complex.im ((((‖f‖ : ℝ) : ℂ) ^ 2)) = 0
    rw [← Complex.ofReal_pow, Complex.ofReal_im, mul_zero]
  · rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    change 0 ≤ (D.partitionFunction β)⁻¹ *
      Complex.re ((((‖f‖ : ℝ) : ℂ) ^ 2))
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact mul_nonneg (inv_nonneg.mpr hZ.le) (sq_nonneg ‖f‖)

/-- Cauchy--Schwarz for the normalized reflection inner product. -/
theorem normSq_reflectionInnerProduct_le (β : ℝ)
    (F H : PositiveObservable G P O) :
    Complex.normSq (D.reflectionInnerProduct β F H) ≤
      Complex.re (D.reflectionInnerProduct β F F) *
        Complex.re (D.reflectionInnerProduct β H H) := by
  let f := ContinuousMap.toLp 2 planeHaar ℂ (D.weightedAmplitude β F)
  let h := ContinuousMap.toLp 2 planeHaar ℂ (D.weightedAmplitude β H)
  have hCS := inner_mul_inner_self_le (𝕜 := ℂ) f h
  have hconj : ‖⟪h, f⟫_ℂ‖ = ‖⟪f, h⟫_ℂ‖ := by rw [norm_inner_symm]
  rw [hconj, ← sq] at hCS
  have hZ : 0 < D.partitionFunction β := D.partitionFunction_pos β
  rw [reflectionInnerProduct, reflectionInnerProduct,
    reflectionInnerProduct, D.gibbsReflectionPairing_eq_factorized,
    D.gibbsReflectionPairing_eq_factorized,
    D.gibbsReflectionPairing_eq_factorized,
    D.factorizedPairing_eq_inner, D.factorizedPairing_eq_inner,
    D.factorizedPairing_eq_inner]
  have hscale : ((D.partitionFunction β : ℂ)⁻¹) =
      ((D.partitionFunction β)⁻¹ : ℝ) := by norm_cast
  have hleft : Complex.normSq
      ((D.partitionFunction β : ℂ)⁻¹ * ⟪f, h⟫_ℂ) =
      ((D.partitionFunction β)⁻¹) ^ 2 * ‖⟪f, h⟫_ℂ‖ ^ 2 := by
    rw [Complex.normSq_mul, hscale, Complex.normSq_ofReal,
      ← Complex.sq_norm]
    ring
  have hdiag_f : Complex.re
      ((D.partitionFunction β : ℂ)⁻¹ * ⟪f, f⟫_ℂ) =
      (D.partitionFunction β)⁻¹ * ‖f‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, hscale]
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    change (D.partitionFunction β)⁻¹ *
      Complex.re ((((‖f‖ : ℝ) : ℂ) ^ 2)) = _
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hdiag_h : Complex.re
      ((D.partitionFunction β : ℂ)⁻¹ * ⟪h, h⟫_ℂ) =
      (D.partitionFunction β)⁻¹ * ‖h‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, hscale]
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    change (D.partitionFunction β)⁻¹ *
      Complex.re ((((‖h‖ : ℝ) : ℂ) ^ 2)) = _
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hleft, hdiag_f, hdiag_h]
  calc
    ((D.partitionFunction β)⁻¹) ^ 2 * ‖⟪f, h⟫_ℂ‖ ^ 2 ≤
        ((D.partitionFunction β)⁻¹) ^ 2 *
          (‖f‖ ^ 2 * ‖h‖ ^ 2) := by
      gcongr
      nlinarith [norm_inner_le_norm (𝕜 := ℂ) f h,
        norm_nonneg ⟪f, h⟫_ℂ, norm_nonneg f, norm_nonneg h]
    _ = ((D.partitionFunction β)⁻¹ * ‖f‖ ^ 2) *
        ((D.partitionFunction β)⁻¹ * ‖h‖ ^ 2) := by ring

/-- Norm-form Cauchy--Schwarz for the reflection inner product. -/
theorem norm_reflectionInnerProduct_le (β : ℝ)
    (F H : PositiveObservable G P O) :
    ‖D.reflectionInnerProduct β F H‖ ≤
      Real.sqrt (Complex.re (D.reflectionInnerProduct β F F) *
        Complex.re (D.reflectionInnerProduct β H H)) := by
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt (by
    simpa only [Complex.sq_norm] using D.normSq_reflectionInnerProduct_le β F H)

section ExplicitWilsonRegression

open Lattice.Cubic

variable {d : ℕ} [IsTopologicalGroup G]

/-- Milestone-17 site reflection positivity instantiated with explicit finite
Wilson plaquette sums.  No assumption on the observables is present beyond
continuity on the positive half-volume. -/
theorem siteReflectionPositivity_ofWilsonPlaquettes
    (Φ : RealPlaquettePotential G)
    (evaluatePositive : C(HalfConfiguration G P O, Configuration d G))
    (evaluatePlane : C(PlaneConfiguration G O, Configuration d G))
    (positivePlaquettes planePlaquettes : Finset (Plaquette d))
    (β : ℝ) (F : PositiveObservable G P O) :
    let D := WilsonActionDecomposition.ofWilsonPlaquettes Φ evaluatePositive
      evaluatePlane positivePlaquettes planePlaquettes
    Complex.im (D.gibbsReflectionPairing β F F) = 0 ∧
      0 ≤ Complex.re (D.gibbsReflectionPairing β F F) := by
  exact (WilsonActionDecomposition.ofWilsonPlaquettes Φ evaluatePositive
    evaluatePlane positivePlaquettes planePlaquettes).siteReflectionPositivity β F

/-- Cauchy--Schwarz for the normalized reflection inner product of an
explicit finite Wilson plaquette action. -/
theorem normSq_reflectionInnerProduct_ofWilsonPlaquettes_le
    (Φ : RealPlaquettePotential G)
    (evaluatePositive : C(HalfConfiguration G P O, Configuration d G))
    (evaluatePlane : C(PlaneConfiguration G O, Configuration d G))
    (positivePlaquettes planePlaquettes : Finset (Plaquette d))
    (β : ℝ) (F H : PositiveObservable G P O) :
    let D := WilsonActionDecomposition.ofWilsonPlaquettes Φ evaluatePositive
      evaluatePlane positivePlaquettes planePlaquettes
    Complex.normSq (D.reflectionInnerProduct β F H) ≤
      Complex.re (D.reflectionInnerProduct β F F) *
        Complex.re (D.reflectionInnerProduct β H H) := by
  exact WilsonActionDecomposition.normSq_reflectionInnerProduct_le
    (WilsonActionDecomposition.ofWilsonPlaquettes Φ evaluatePositive
      evaluatePlane positivePlaquettes planePlaquettes) β F H

end ExplicitWilsonRegression

end WilsonActionDecomposition

end Haar

end SiteReflection

end

end YangMills.Gauge
