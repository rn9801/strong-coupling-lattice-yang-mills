/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.DiagonalReflection
import YangMills.Gauge.LinkReflectionPositivity

/-!
# Finite-volume diagonal-reflection positivity

Reflection through `x τ - x σ = k` leaves tangential plane edges fixed and
exchanges the two strict half-volumes.  At fixed plane field, plaquettes cut
by the diagonal plane have exactly the matrix-coefficient Gram kernel used in
the Taylor part of link-reflection positivity.  There are no crossing-link
variables and hence no gauge-fixing restriction on observables.

The proof conditions on the plane field, expands the cut-plaquette
exponential in its normally convergent Taylor series, expands each coefficient
into labelled matrix-coefficient words, and applies product-Haar Fubini.  The
inner integral is a Gram sum; integrating it over the common plane variables
preserves positivity.
-/

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace YangMills.Gauge.DiagonalReflection

noncomputable section

abbrev SideConfiguration (G : Type*) (P : Type*) := P → G
abbrev PlaneConfiguration (G : Type*) (O : Type*) := O → G
abbrev HalfConfiguration (G : Type*) (O P : Type*) :=
  PlaneConfiguration G O × SideConfiguration G P
abbrev ReflectedConfiguration (G : Type*) (O P : Type*) :=
  PlaneConfiguration G O ×
    (SideConfiguration G P × SideConfiguration G P)

abbrev PositiveObservable (G : Type*) (O P : Type*) [TopologicalSpace G] :=
  C(HalfConfiguration G O P, ℂ)

variable {G O P Q : Type*} {n : ℕ}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Reflection of the fixed-plane/two-side normal form. -/
def reflect (U : ReflectedConfiguration G O P) : ReflectedConfiguration G O P :=
  (U.1, (U.2.2, U.2.1))

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem reflect_reflect (U : ReflectedConfiguration G O P) :
    reflect (reflect U) = U := by
  rcases U with ⟨Uzero, Uminus, Uplus⟩
  rfl

omit [Group G] [IsTopologicalGroup G] in
theorem continuous_reflect :
    Continuous (reflect : ReflectedConfiguration G O P →
      ReflectedConfiguration G O P) := by
  unfold reflect
  fun_prop

/-- Lift a positive-side observable to the full reflected variables. -/
def liftPositive (F : PositiveObservable G O P) :
    C(ReflectedConfiguration G O P, ℂ) where
  toFun U := F (U.1, U.2.2)
  continuous_toFun := by fun_prop

/-- Anti-linear diagonal reflection in the labelled normal form. -/
def theta (F : C(ReflectedConfiguration G O P, ℂ)) :
    C(ReflectedConfiguration G O P, ℂ) where
  toFun U := conj (F (reflect U))
  continuous_toFun := by
    exact Complex.continuous_conj.comp <| F.continuous.comp continuous_reflect

omit [Group G] [IsTopologicalGroup G] in
@[simp]
theorem theta_liftPositive_apply (F : PositiveObservable G O P)
    (U : ReflectedConfiguration G O P) :
    theta (liftPositive F) U = conj (F (U.1, U.2.1)) := rfl

/-- Wilson data for a diagonal cut.  At fixed plane field,
`cutHolonomy q (Uzero,Uside)` is the positive-side half-holonomy of one cut
plaquette. -/
structure WilsonActionDecomposition (G : Type*) (n : ℕ) (O P Q : Type*)
    [Group G] [TopologicalSpace G] where
  representation : Wilson.ContinuousUnitaryRepData G n
  positiveAction : C(HalfConfiguration G O P, ℝ)
  planeAction : C(PlaneConfiguration G O, ℝ)
  cutHolonomy : Q → C(HalfConfiguration G O P, G)

namespace WilsonActionDecomposition

/-- The identity side transformation used because there is no crossing-link
field for a diagonal plane. -/
def identityGaugeFix : LinkReflection.CrossingForestGaugeFix G Empty P where
  leftMultiplier := fun _ _ => 1
  rightMultiplier := fun _ _ => 1
  continuous_leftMultiplier := fun _ => continuous_const
  continuous_rightMultiplier := fun _ => continuous_const

variable (D : WilsonActionDecomposition G n O P Q)

/-- Freeze the common plane field.  The remaining two-side Wilson action is
the Taylor/Fubini normal form already proved for cut plaquettes. -/
def slice (Uzero : PlaneConfiguration G O) :
    LinkReflection.WilsonActionDecomposition G n Empty P Q where
  gaugeFix := identityGaugeFix
  representation := D.representation
  positiveAction :=
    { toFun := fun Uside => D.positiveAction (Uzero, Uside)
      continuous_toFun := D.positiveAction.continuous.comp
        (continuous_const.prodMk continuous_id) }
  crossHolonomy := fun q =>
    { toFun := fun Uside => D.cutHolonomy q (Uzero, Uside)
      continuous_toFun := (D.cutHolonomy q).continuous.comp
        (continuous_const.prodMk continuous_id) }

/-- Restrict an observable to one fixed plane field. -/
def sliceObservable (F : PositiveObservable G O P)
    (Uzero : PlaneConfiguration G O) :
    LinkReflection.WilsonActionDecomposition.PositiveObservable G Empty P where
  toFun W := F (Uzero, W.2)
  continuous_toFun := F.continuous.comp (continuous_const.prodMk continuous_snd)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Every empty crossing field is the identity field. -/
theorem emptyCrossing_eq_one (U : Empty → G) : U = 1 := by
  funext e
  exact Empty.elim e

omit [IsTopologicalGroup G] in
/-- At every plane field the formal crossing-gauge identity is automatic for
every observable.  This removes gauge invariance from diagonal reflection. -/
theorem automaticGaugeFixIdentity (F : PositiveObservable G O P)
    (Uzero : PlaneConfiguration G O) :
    (D.slice Uzero).IsGaugeInvariant (sliceObservable F Uzero) := by
  intro Ucross Uside
  rw [emptyCrossing_eq_one Ucross]
  have hfix : (D.slice Uzero).gaugeFix.fixSide 1 Uside = Uside := by
    funext e
    simp [slice, identityGaugeFix, LinkReflection.CrossingForestGaugeFix.fixSide]
  rw [hfix]

omit [IsTopologicalGroup G] in
/-- Every family of cut plaquettes expands into the normalized finite
matrix-coefficient Gram kernel at fixed plane field. -/
theorem sum_wilsonPotential_eq_cutKernel [Fintype Q]
    (Uzero : PlaneConfiguration G O)
    (V : SideConfiguration G P × SideConfiguration G P) :
    (∑ q : Q, (D.representation.wilsonPotential
      (D.cutHolonomy q (Uzero, V.2) *
        (D.cutHolonomy q (Uzero, V.1))⁻¹) : ℂ)) =
      (2 * (n : ℂ))⁻¹ * (D.slice Uzero).crossKernel V :=
  (D.slice Uzero).sum_wilsonPotential_eq_crossKernel V

/-- Full Wilson action reconstructed from the plane, strict-half, and cut
plaquette pieces. -/
def action [Fintype Q] (U : ReflectedConfiguration G O P) : ℝ :=
  D.planeAction U.1 + (D.slice U.1).gaugeFixedAction U.2

omit [IsTopologicalGroup G] in
@[simp]
theorem action_reflect [Fintype Q] (U : ReflectedConfiguration G O P) :
    D.action (reflect U) = D.action U := by
  unfold action reflect
  change D.planeAction U.1 +
      (D.slice U.1).gaugeFixedAction U.2.swap = _
  rw [(D.slice U.1).gaugeFixedAction_swap]

theorem continuous_action [Fintype Q] : Continuous D.action := by
  change Continuous (fun U : ReflectedConfiguration G O P ↦
    D.planeAction U.1 +
      (D.positiveAction (U.1, U.2.1) + D.positiveAction (U.1, U.2.2) +
        ∑ q : Q, D.representation.wilsonPotential
          (D.cutHolonomy q (U.1, U.2.2) *
            (D.cutHolonomy q (U.1, U.2.1))⁻¹)))
  fun_prop

section Haar

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G]
  [Fintype O] [Fintype P] [Fintype Q]

abbrev planeHaar : Measure (PlaneConfiguration G O) := ProductHaar.measure G O
abbrev sideHaar : Measure (SideConfiguration G P) := ProductHaar.measure G P
abbrev reflectedHaar : Measure (ReflectedConfiguration G O P) :=
  (planeHaar (G := G) (O := O)).prod
    ((sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P)))

def boltzmannWeight (β : ℝ) (U : ReflectedConfiguration G O P) : ℝ :=
  Real.exp (β * D.action U)

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G] [Fintype O] [Fintype P] in
theorem continuous_boltzmannWeight (β : ℝ) :
    Continuous (D.boltzmannWeight β) :=
  Real.continuous_exp.comp (continuous_const.mul D.continuous_action)

theorem integrable_boltzmannWeight (β : ℝ) :
    Integrable (D.boltzmannWeight β) reflectedHaar :=
  (D.continuous_boltzmannWeight β).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def partitionFunction (β : ℝ) : ℝ :=
  ∫ U, D.boltzmannWeight β U ∂reflectedHaar

theorem partitionFunction_pos (β : ℝ) : 0 < D.partitionFunction β := by
  unfold partitionFunction boltzmannWeight
  exact integral_exp_pos (D.integrable_boltzmannWeight β)

/-- The full unnormalized diagonal reflected Gibbs pairing. -/
def gibbsReflectionPairing (β : ℝ) (F H : PositiveObservable G O P) : ℂ :=
  ∫ U, (D.boltzmannWeight β U : ℂ) *
      theta (liftPositive F) U * liftPositive H U ∂reflectedHaar

theorem integrable_gibbsReflectionIntegrand (β : ℝ)
    (F H : PositiveObservable G O P) :
    Integrable (fun U => (D.boltzmannWeight β U : ℂ) *
      theta (liftPositive F) U * liftPositive H U) reflectedHaar := by
  apply Continuous.integrable_of_hasCompactSupport _
    (HasCompactSupport.of_compactSpace _)
  exact ((Complex.continuous_ofReal.comp (D.continuous_boltzmannWeight β)).mul
    (theta (liftPositive F)).continuous).mul (liftPositive H).continuous

/-- Pairing after conditioning on the common plane field. -/
def factorizedPairing (β : ℝ) (F H : PositiveObservable G O P) : ℂ :=
  ∫ Uzero, (Real.exp (β * D.planeAction Uzero) : ℂ) *
      (D.slice Uzero).gaugeFixedPairing β
        (sliceObservable F Uzero) (sliceObservable H Uzero)
    ∂planeHaar

/-- The diagonal pairing written as the plane integral of the explicit
Taylor/Fubini Gram series. -/
def taylorPairing (β : ℝ) (F H : PositiveObservable G O P) : ℂ :=
  ∫ Uzero, (Real.exp (β * D.planeAction Uzero) : ℂ) *
      (D.slice Uzero).taylorPairing β
        (sliceObservable F Uzero) (sliceObservable H Uzero)
    ∂planeHaar

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [Fintype O] in
/-- At fixed plane field, product-Haar Fubini gives the Taylor normal-form
pairing on the two strict halves. -/
theorem integral_sides_eq_slicePairing (β : ℝ)
    (F H : PositiveObservable G O P) (Uzero : PlaneConfiguration G O) :
    (∫ V : SideConfiguration G P × SideConfiguration G P,
      (D.boltzmannWeight β (Uzero, V) : ℂ) *
        theta (liftPositive F) (Uzero, V) * liftPositive H (Uzero, V)
      ∂(sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P))) =
      (Real.exp (β * D.planeAction Uzero) : ℂ) *
        (D.slice Uzero).gaugeFixedPairing β
          (sliceObservable F Uzero) (sliceObservable H Uzero) := by
  unfold LinkReflection.WilsonActionDecomposition.gaugeFixedPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with V
  simp only [boltzmannWeight, action, theta, reflect, liftPositive,
    ContinuousMap.coe_mk, sliceObservable]
  rw [show β * (D.planeAction Uzero + (D.slice Uzero).gaugeFixedAction V) =
      β * D.planeAction Uzero + β * (D.slice Uzero).gaugeFixedAction V by ring,
    Real.exp_add]
  push_cast
  ring

/-- Fubini identifies the full diagonal Gibbs pairing with its conditioned
plane-field form. -/
theorem gibbsReflectionPairing_eq_factorized (β : ℝ)
    (F H : PositiveObservable G O P) :
    D.gibbsReflectionPairing β F H = D.factorizedPairing β F H := by
  unfold gibbsReflectionPairing factorizedPairing reflectedHaar
  rw [integral_prod _ (D.integrable_gibbsReflectionIntegrand β F H)]
  congr 1
  funext Uzero
  exact D.integral_sides_eq_slicePairing β F H Uzero

/-- The full diagonal Gibbs pairing equals its explicit cut-plaquette
Taylor/Fubini Gram expansion. -/
theorem gibbsReflectionPairing_eq_taylorPairing (β : ℝ)
    (F H : PositiveObservable G O P) :
    D.gibbsReflectionPairing β F H = D.taylorPairing β F H := by
  rw [D.gibbsReflectionPairing_eq_factorized]
  unfold factorizedPairing taylorPairing
  apply integral_congr_ae
  filter_upwards with Uzero
  rw [(D.slice Uzero).gaugeFixedPairing_eq_taylorPairing]

theorem integrable_factorizedIntegrand (β : ℝ)
    (F H : PositiveObservable G O P) :
    Integrable (fun Uzero => (Real.exp (β * D.planeAction Uzero) : ℂ) *
      (D.slice Uzero).gaugeFixedPairing β
        (sliceObservable F Uzero) (sliceObservable H Uzero)) planeHaar := by
  have h := (D.integrable_gibbsReflectionIntegrand β F H).integral_prod_left
  exact h.congr <| ae_of_all _ fun Uzero =>
    D.integral_sides_eq_slicePairing β F H Uzero

/-- Finite-volume diagonal reflection positivity for the full continuous
positive algebra at nonnegative Wilson coupling.  There is no gauge-invariance
hypothesis on the observable. -/
theorem diagonalReflectionPositivity {β : ℝ} (hβ : 0 ≤ β)
    (F : PositiveObservable G O P) :
    Complex.im (D.gibbsReflectionPairing β F F) = 0 ∧
      0 ≤ Complex.re (D.gibbsReflectionPairing β F F) := by
  rw [D.gibbsReflectionPairing_eq_factorized]
  let K : PlaneConfiguration G O → ℂ := fun Uzero =>
    (Real.exp (β * D.planeAction Uzero) : ℂ) *
      (D.slice Uzero).gaugeFixedPairing β
        (sliceObservable F Uzero) (sliceObservable F Uzero)
  have hK : Integrable K planeHaar := D.integrable_factorizedIntegrand β F F
  have hpoint : ∀ Uzero, Complex.im (K Uzero) = 0 ∧ 0 ≤ Complex.re (K Uzero) := by
    intro Uzero
    have hinner := (D.slice Uzero).taylorPairing_self_nonneg hβ
      (sliceObservable F Uzero)
    rw [← (D.slice Uzero).gaugeFixedPairing_eq_taylorPairing] at hinner
    constructor
    · dsimp only [K]
      rw [Complex.mul_im]
      change Real.exp (β * D.planeAction Uzero) * _ + 0 * _ = 0
      rw [hinner.1]
      ring
    · dsimp only [K]
      rw [Complex.mul_re]
      change 0 ≤ Real.exp (β * D.planeAction Uzero) * _ - 0 * _
      simpa only [zero_mul, sub_zero] using
        mul_nonneg (Real.exp_pos _).le hinner.2
  change Complex.im (∫ Uzero, K Uzero ∂planeHaar) = 0 ∧
    0 ≤ Complex.re (∫ Uzero, K Uzero ∂planeHaar)
  constructor
  · calc
      Complex.im (∫ Uzero, K Uzero ∂planeHaar) =
          ∫ Uzero, Complex.im (K Uzero) ∂planeHaar := (integral_im hK).symm
      _ = 0 := by
        simp_rw [fun Uzero => (hpoint Uzero).1]
        simp
  · calc
      0 ≤ ∫ Uzero, Complex.re (K Uzero) ∂planeHaar :=
        integral_nonneg fun Uzero => (hpoint Uzero).2
      _ = Complex.re (∫ Uzero, K Uzero ∂planeHaar) := integral_re hK

/-- Additivity in the reflected argument. -/
theorem gibbsReflectionPairing_add_left (β : ℝ)
    (F K H : PositiveObservable G O P) :
    D.gibbsReflectionPairing β (F + K) H =
      D.gibbsReflectionPairing β F H + D.gibbsReflectionPairing β K H := by
  unfold gibbsReflectionPairing
  rw [← integral_add (D.integrable_gibbsReflectionIntegrand β F H)
    (D.integrable_gibbsReflectionIntegrand β K H)]
  apply integral_congr_ae
  filter_upwards with U
  change (D.boltzmannWeight β U : ℂ) *
      conj (F (U.1, U.2.1) + K (U.1, U.2.1)) * H (U.1, U.2.2) =
    (D.boltzmannWeight β U : ℂ) *
        conj (F (U.1, U.2.1)) * H (U.1, U.2.2) +
      (D.boltzmannWeight β U : ℂ) *
        conj (K (U.1, U.2.1)) * H (U.1, U.2.2)
  rw [map_add]
  ring

omit [IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] in
/-- Conjugate scalar linearity in the reflected argument. -/
theorem gibbsReflectionPairing_smul_left (β : ℝ) (c : ℂ)
    (F H : PositiveObservable G O P) :
    D.gibbsReflectionPairing β (c • F) H =
      conj c * D.gibbsReflectionPairing β F H := by
  unfold gibbsReflectionPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with U
  change (D.boltzmannWeight β U : ℂ) *
      conj (c * F (U.1, U.2.1)) * H (U.1, U.2.2) =
    conj c * ((D.boltzmannWeight β U : ℂ) *
      conj (F (U.1, U.2.1)) * H (U.1, U.2.2))
  rw [map_mul]
  ring

/-- Hermitian symmetry of the diagonal reflected Gibbs pairing. -/
theorem gibbsReflectionPairing_conj_symm (β : ℝ)
    (F H : PositiveObservable G O P) :
    conj (D.gibbsReflectionPairing β H F) =
      D.gibbsReflectionPairing β F H := by
  rw [D.gibbsReflectionPairing_eq_factorized,
    D.gibbsReflectionPairing_eq_factorized]
  unfold factorizedPairing
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with Uzero
  rw [map_mul, Complex.conj_ofReal,
    (D.slice Uzero).gaugeFixedPairing_conj_symm]

/-- Cauchy--Schwarz for the unnormalized diagonal reflected Gibbs pairing. -/
theorem normSq_gibbsReflectionPairing_le {β : ℝ} (hβ : 0 ≤ β)
    (F H : PositiveObservable G O P) :
    Complex.normSq (D.gibbsReflectionPairing β F H) ≤
      Complex.re (D.gibbsReflectionPairing β F F) *
        Complex.re (D.gibbsReflectionPairing β H H) := by
  letI : PreInnerProductSpace.Core ℂ (PositiveObservable G O P) := {
    inner := D.gibbsReflectionPairing β
    conj_inner_symm := D.gibbsReflectionPairing_conj_symm β
    re_inner_nonneg := fun F => (D.diagonalReflectionPositivity hβ F).2
    add_left := D.gibbsReflectionPairing_add_left β
    smul_left := fun F H c => D.gibbsReflectionPairing_smul_left β c F H
  }
  have hCS := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ
    (PositiveObservable G O P) _ _ _ _ F H
  change ‖D.gibbsReflectionPairing β F H‖ *
      ‖D.gibbsReflectionPairing β H F‖ ≤
    Complex.re (D.gibbsReflectionPairing β F F) *
      Complex.re (D.gibbsReflectionPairing β H H) at hCS
  have hnorm : ‖D.gibbsReflectionPairing β H F‖ =
      ‖D.gibbsReflectionPairing β F H‖ := by
    rw [← D.gibbsReflectionPairing_conj_symm β F H, Complex.norm_conj]
  rw [hnorm, ← sq, Complex.sq_norm] at hCS
  exact hCS

/-- Normalized diagonal reflection inner product. -/
def reflectionInnerProduct (β : ℝ) (F H : PositiveObservable G O P) : ℂ :=
  (D.partitionFunction β : ℂ)⁻¹ * D.gibbsReflectionPairing β F H

theorem reflectionInnerProduct_self_nonneg {β : ℝ} (hβ : 0 ≤ β)
    (F : PositiveObservable G O P) :
    Complex.im (D.reflectionInnerProduct β F F) = 0 ∧
      0 ≤ Complex.re (D.reflectionInnerProduct β F F) := by
  have hpos := D.diagonalReflectionPositivity hβ F
  have hZ := D.partitionFunction_pos β
  unfold reflectionInnerProduct
  have hscale : ((D.partitionFunction β : ℂ)⁻¹) =
      ((D.partitionFunction β)⁻¹ : ℝ) := by
    symm
    exact Complex.ofReal_inv _
  rw [hscale]
  constructor
  · rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      hpos.1, mul_zero]
  · rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr hZ.le) hpos.2

/-- Cauchy--Schwarz for the normalized diagonal reflection inner product. -/
theorem normSq_reflectionInnerProduct_le {β : ℝ} (hβ : 0 ≤ β)
    (F H : PositiveObservable G O P) :
    Complex.normSq (D.reflectionInnerProduct β F H) ≤
      Complex.re (D.reflectionInnerProduct β F F) *
        Complex.re (D.reflectionInnerProduct β H H) := by
  have hCS := D.normSq_gibbsReflectionPairing_le hβ F H
  have hZ := D.partitionFunction_pos β
  unfold reflectionInnerProduct
  have hscale : ((D.partitionFunction β : ℂ)⁻¹) =
      ((D.partitionFunction β)⁻¹ : ℝ) := by
    symm
    exact Complex.ofReal_inv _
  rw [hscale, Complex.normSq_mul, Complex.normSq_ofReal]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have hs : 0 ≤ (D.partitionFunction β)⁻¹ := inv_nonneg.mpr hZ.le
  calc
    (D.partitionFunction β)⁻¹ * (D.partitionFunction β)⁻¹ *
        Complex.normSq (D.gibbsReflectionPairing β F H) ≤
      (D.partitionFunction β)⁻¹ * (D.partitionFunction β)⁻¹ *
        (Complex.re (D.gibbsReflectionPairing β F F) *
          Complex.re (D.gibbsReflectionPairing β H H)) := by
      gcongr
    _ = ((D.partitionFunction β)⁻¹ *
          Complex.re (D.gibbsReflectionPairing β F F)) *
        ((D.partitionFunction β)⁻¹ *
          Complex.re (D.gibbsReflectionPairing β H H)) := by ring

end Haar

end WilsonActionDecomposition

end

end YangMills.Gauge.DiagonalReflection
