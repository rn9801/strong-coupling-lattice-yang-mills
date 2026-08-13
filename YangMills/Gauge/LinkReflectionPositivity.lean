/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.SiteReflectionPositivity
import YangMills.Wilson.Representation
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Finite-volume link-reflection positivity

This file fixes the conventions for reflection in the half-integer hyperplane
`x_τ = k + 1/2`.  A crossing positive edge is fixed setwise and its oriented
value is inverted.  The remaining edge variables occur in two reflected side
families.  Unlike integer/site reflection positivity, the positive algebra is
restricted to observables invariant under the crossing-edge forest gauge fix.

The proof has three explicit steps.

1. Every crossing edge is set to `1`.  The induced change on each remaining
   edge is left and right multiplication by fixed group elements.  Product
   Haar is therefore preserved coordinate by coordinate.
2. A cross-plane Wilson plaquette becomes `g₊ * g₋⁻¹`.  Its real
   normalized character is expanded into matrix coefficients of a continuous
   unitary representation, including both orientations.
3. The exponential is expanded in its Taylor series.  Every Taylor
   coefficient is a finite sum of products `conj (A F) * A H`; Fubini turns
   the diagonal pairing into a sum of nonnegative square moduli.

The fixed finite label types below are the reflection/gauge-fixing normal form
of a symmetric finite lattice.  No Douglas compatibility module is imported:
the pinned Douglas gauge-fixing file leaves its Faddeev--Popov identity as a
hypothesis and contains no reflection-positivity theorem.
-/

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace YangMills.Gauge

noncomputable section

namespace LinkReflection

/-- Variables on the crossing links fixed setwise by a half-integer reflection. -/
abbrev CrossingConfiguration (G : Type*) (C : Type*) := C → G

/-- Variables strictly on one side of a half-integer reflection plane. -/
abbrev SideConfiguration (G : Type*) (P : Type*) := P → G

/-- Variables visible to a positive-side link-reflection observable. -/
abbrev HalfConfiguration (G : Type*) (C P : Type*) :=
  CrossingConfiguration G C × SideConfiguration G P

/-- Crossing variables followed by the negative and positive side fields. -/
abbrev ReflectedConfiguration (G : Type*) (C P : Type*) :=
  CrossingConfiguration G C ×
    (SideConfiguration G P × SideConfiguration G P)

variable {G C P Q : Type*}

/-- Pointwise inversion of the crossing-link field. -/
def invertCrossing [Group G] (U : CrossingConfiguration G C) :
    CrossingConfiguration G C := fun e ↦ (U e)⁻¹

@[simp]
theorem invertCrossing_apply [Group G] (U : CrossingConfiguration G C) (e : C) :
    invertCrossing U e = (U e)⁻¹ := rfl

@[simp]
theorem invertCrossing_invertCrossing [Group G] (U : CrossingConfiguration G C) :
    invertCrossing (invertCrossing U) = U := by
  funext e
  simp [invertCrossing]

/-- Half-integer reflection in the fixed labelled-variable normal form. -/
def reflect [Group G] (U : ReflectedConfiguration G C P) :
    ReflectedConfiguration G C P :=
  (invertCrossing U.1, (U.2.2, U.2.1))

@[simp]
theorem reflect_reflect [Group G] (U : ReflectedConfiguration G C P) :
    reflect (reflect U) = U := by
  rcases U with ⟨Ucross, Uminus, Uplus⟩
  simp [reflect]

/-- Reflection-compatible simultaneous gauge fixing of the crossing-edge
forest.  At fixed crossing field, every side coordinate is transformed by
left and right multiplication, the form produced by a lattice gauge
transformation at the endpoints of the crossing forest. -/
structure CrossingForestGaugeFix (G : Type*) (C P : Type*)
    [Group G] [TopologicalSpace G] where
  leftMultiplier : CrossingConfiguration G C → P → G
  rightMultiplier : CrossingConfiguration G C → P → G
  continuous_leftMultiplier : ∀ e, Continuous fun U ↦ leftMultiplier U e
  continuous_rightMultiplier : ∀ e, Continuous fun U ↦ rightMultiplier U e

variable [Group G] [TopologicalSpace G]

namespace CrossingForestGaugeFix

/-- The induced transformation of the nonforest side variables. -/
def fixSide (D : CrossingForestGaugeFix G C P)
    (Ucross : CrossingConfiguration G C) (U : SideConfiguration G P) :
    SideConfiguration G P :=
  fun e ↦ D.leftMultiplier Ucross e * U e * D.rightMultiplier Ucross e

@[simp]
theorem fixSide_apply (D : CrossingForestGaugeFix G C P)
    (Ucross : CrossingConfiguration G C) (U : SideConfiguration G P) (e : P) :
    D.fixSide Ucross U e =
      D.leftMultiplier Ucross e * U e * D.rightMultiplier Ucross e := rfl

theorem continuous_fixSide (D : CrossingForestGaugeFix G C P)
    [IsTopologicalGroup G] :
    Continuous (fun U : CrossingConfiguration G C × SideConfiguration G P ↦
      D.fixSide U.1 U.2) := by
  apply continuous_pi
  intro e
  exact ((D.continuous_leftMultiplier e |>.comp continuous_fst).mul
      (continuous_apply e |>.comp continuous_snd)).mul
    (D.continuous_rightMultiplier e |>.comp continuous_fst)

/-- For fixed crossing links, the transformation of the side variables is a
measurable equivalence; its inverse uses the inverse endpoint multipliers. -/
def fixSideEquiv (D : CrossingForestGaugeFix G C P)
    (Ucross : CrossingConfiguration G C) [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] [IsTopologicalGroup G] [Fintype P] :
    SideConfiguration G P ≃ᵐ SideConfiguration G P where
  toFun := D.fixSide Ucross
  invFun := fun U e ↦
    (D.leftMultiplier Ucross e)⁻¹ * U e * (D.rightMultiplier Ucross e)⁻¹
  left_inv U := by
    funext e
    simp [fixSide, mul_assoc]
  right_inv U := by
    funext e
    simp [fixSide, mul_assoc]
  measurable_toFun := (D.continuous_fixSide.comp
    (continuous_const.prodMk continuous_id)).measurable
  measurable_invFun := by
    apply Continuous.measurable
    apply continuous_pi
    intro e
    exact ((continuous_const.mul (continuous_apply e)).mul continuous_const)

section Haar

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [IsTopologicalGroup G] [CompactSpace G] [GaugeHaarProbability G] [Fintype P]

/-- For a fixed crossing field, the forest gauge fix preserves side product
Haar because it is coordinatewise left/right multiplication. -/
theorem measurePreserving_fixSide (D : CrossingForestGaugeFix G C P)
    (Ucross : CrossingConfiguration G C) :
    MeasurePreserving (D.fixSide Ucross)
      (ProductHaar.measure G P) (ProductHaar.measure G P) := by
  simpa only [ProductHaar.measure] using
    (ProductHaar.measurePreserving_coordinatewise (G := G)
      (fun _ : P ↦ GaugeHaarProbability.haar G)
      (fun e x ↦ D.leftMultiplier Ucross e * x * D.rightMultiplier Ucross e)
      (fun e ↦ GaugeHaarProbability.measurePreserving_mulLeft_mulRight G
        (D.leftMultiplier Ucross e) (D.rightMultiplier Ucross e)))

/-- The measurable-equivalence form of crossing-forest Haar invariance. -/
theorem measurePreserving_fixSideEquiv (D : CrossingForestGaugeFix G C P)
    (Ucross : CrossingConfiguration G C) :
    MeasurePreserving (D.fixSideEquiv Ucross)
      (ProductHaar.measure G P) (ProductHaar.measure G P) :=
  D.measurePreserving_fixSide Ucross

end Haar

end CrossingForestGaugeFix

/-- Gauge-fixed link-reflection Wilson data.  `crossHolonomy q U` is the
positive-side half-holonomy of a plaquette meeting the reflection plane. -/
structure WilsonActionDecomposition (G : Type*) (n : ℕ) (C P Q : Type*)
    [Group G] [TopologicalSpace G] where
  gaugeFix : CrossingForestGaugeFix G C P
  representation : Wilson.ContinuousUnitaryRepData G n
  positiveAction : C(SideConfiguration G P, ℝ)
  crossHolonomy : Q → C(SideConfiguration G P, G)

namespace WilsonActionDecomposition

variable {n : ℕ} (D : WilsonActionDecomposition G n C P Q)

/-- One oriented matrix coefficient in the character expansion.  The Boolean
index records the two orientations occurring in the real Wilson action. -/
def orientedMatrixCoefficient (b : Bool) (i j : Fin n) (g : G) : ℂ :=
  if b then conj ((D.representation.ρ g : Matrix (Fin n) (Fin n) ℂ) i j)
  else (D.representation.ρ g : Matrix (Fin n) (Fin n) ℂ) i j

/-- The matrix-coefficient contraction for one orientation is the character
of `g * h⁻¹`. -/
theorem sum_matrixCoefficient_mul_conj (g h : G) :
    (∑ i : Fin n, ∑ j : Fin n,
      (D.representation.ρ g : Matrix (Fin n) (Fin n) ℂ) i j *
        conj ((D.representation.ρ h : Matrix (Fin n) (Fin n) ℂ) i j)) =
      D.representation.character (g * h⁻¹) := by
  simp only [Wilson.ContinuousUnitaryRepData.character, map_mul, map_inv,
    Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.inv_val,
    Matrix.star_eq_conjTranspose, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, starRingEnd_apply]

/-- Adding the reversed orientation gives twice the real part of the
character, explicitly as a sum of rank-one kernels. -/
theorem sum_orientedMatrixCoefficient_mul_conj (g h : G) :
    (∑ b : Bool, ∑ i : Fin n, ∑ j : Fin n,
      D.orientedMatrixCoefficient b i j g *
        conj (D.orientedMatrixCoefficient b i j h)) =
      2 * (D.representation.character (g * h⁻¹)).re := by
  rw [Fintype.sum_bool]
  simp only [orientedMatrixCoefficient, Bool.false_eq_true, ↓reduceIte,
    starRingEnd_apply, star_star]
  have hreverse := D.sum_matrixCoefficient_mul_conj h g
  have hforward := D.sum_matrixCoefficient_mul_conj g h
  have hstar : (∑ i : Fin n, ∑ j : Fin n,
      conj ((D.representation.ρ g : Matrix (Fin n) (Fin n) ℂ) i j) *
        (D.representation.ρ h : Matrix (Fin n) (Fin n) ℂ) i j) =
      conj (D.representation.character (g * h⁻¹)) := by
    calc
      _ = (∑ i : Fin n, ∑ j : Fin n,
          (D.representation.ρ h : Matrix (Fin n) (Fin n) ℂ) i j *
            conj ((D.representation.ρ g : Matrix (Fin n) (Fin n) ℂ) i j)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = D.representation.character (h * g⁻¹) := hreverse
      _ = conj (D.representation.character (g * h⁻¹)) := by
        rw [show h * g⁻¹ = (g * h⁻¹)⁻¹ by simp]
        rw [D.representation.character_inv]
        rfl
  change (∑ i : Fin n, ∑ j : Fin n,
      conj ((D.representation.ρ g : Matrix (Fin n) (Fin n) ℂ) i j) *
        (D.representation.ρ h : Matrix (Fin n) (Fin n) ℂ) i j) +
      (∑ i : Fin n, ∑ j : Fin n,
        (D.representation.ρ g : Matrix (Fin n) (Fin n) ℂ) i j *
          conj ((D.representation.ρ h : Matrix (Fin n) (Fin n) ℂ) i j)) = _
  rw [hstar]
  rw [hforward]
  apply Complex.ext
  · simp
    ring
  · simp

/-- Finite feature labels for all cross-plane plaquettes, orientations, and
matrix coefficients. -/
abbrev CrossLetter (Q : Type*) (n : ℕ) := Q × Bool × Fin n × Fin n

/-- One positive-side matrix-coefficient feature. -/
def crossFeature (a : CrossLetter Q n) (U : SideConfiguration G P) : ℂ :=
  D.orientedMatrixCoefficient a.2.1 a.2.2.1 a.2.2.2
    (D.crossHolonomy a.1 U)

/-- The finite rank-one kernel generated by all cross-plane matrix
coefficients. -/
def crossKernel [Fintype Q]
    (V : SideConfiguration G P × SideConfiguration G P) : ℂ :=
  ∑ a : CrossLetter Q n, conj (D.crossFeature a V.1) * D.crossFeature a V.2

theorem continuous_crossFeature [IsTopologicalGroup G]
    (a : CrossLetter Q n) : Continuous (D.crossFeature a) := by
  unfold crossFeature orientedMatrixCoefficient
  have hentry (i j : Fin n) : Continuous fun g : G ↦
      (D.representation.ρ g : Matrix (Fin n) (Fin n) ℂ) i j :=
    (continuous_apply j).comp ((continuous_apply i).comp
      (continuous_subtype_val.comp D.representation.continuous_ρ))
  split
  · exact Complex.continuous_conj.comp <| hentry _ _ |>.comp
      (D.crossHolonomy a.1).continuous
  · exact hentry _ _ |>.comp (D.crossHolonomy a.1).continuous

theorem continuous_crossKernel [Fintype Q]
    [IsTopologicalGroup G] : Continuous D.crossKernel := by
  unfold crossKernel
  apply continuous_finsetSum Finset.univ
  intro a _ha
  exact (Complex.continuous_conj.comp
    ((D.continuous_crossFeature a).comp continuous_fst)).mul
      ((D.continuous_crossFeature a).comp continuous_snd)

/-- The Wilson cross-plane action is exactly the normalized finite feature
kernel.  This is the trace-expansion identity used by the Taylor proof. -/
theorem sum_wilsonPotential_eq_crossKernel [Fintype Q]
    (V : SideConfiguration G P × SideConfiguration G P) :
    (∑ q : Q, (D.representation.wilsonPotential
      (D.crossHolonomy q V.2 * (D.crossHolonomy q V.1)⁻¹) : ℂ)) =
      (2 * (n : ℂ))⁻¹ * D.crossKernel V := by
  unfold crossKernel
  rw [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  change (D.representation.wilsonPotential
      (D.crossHolonomy q V.2 * (D.crossHolonomy q V.1)⁻¹) : ℂ) =
    (2 * (n : ℂ))⁻¹ *
      ∑ a : Bool × Fin n × Fin n,
        conj (D.orientedMatrixCoefficient a.1 a.2.1 a.2.2
          (D.crossHolonomy q V.1)) *
        D.orientedMatrixCoefficient a.1 a.2.1 a.2.2
          (D.crossHolonomy q V.2)
  simp only [Fintype.sum_prod_type]
  have horiented := D.sum_orientedMatrixCoefficient_mul_conj
    (D.crossHolonomy q V.2) (D.crossHolonomy q V.1)
  have hkernel :
      (∑ b : Bool, ∑ i : Fin n, ∑ j : Fin n,
        conj (D.orientedMatrixCoefficient b i j (D.crossHolonomy q V.1)) *
          D.orientedMatrixCoefficient b i j (D.crossHolonomy q V.2)) =
        2 * (D.representation.character
          (D.crossHolonomy q V.2 * (D.crossHolonomy q V.1)⁻¹)).re := by
    calc
      _ = ∑ b : Bool, ∑ i : Fin n, ∑ j : Fin n,
          D.orientedMatrixCoefficient b i j (D.crossHolonomy q V.2) *
            conj (D.orientedMatrixCoefficient b i j
              (D.crossHolonomy q V.1)) := by
        apply Finset.sum_congr rfl
        intro b _hb
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = _ := horiented
  rw [hkernel]
  simp only [Wilson.ContinuousUnitaryRepData.wilsonPotential_apply,
    Wilson.ContinuousUnitaryRepData.normalizedCharacter]
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast D.representation.dimension_pos.ne'
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast D.representation.dimension_pos.ne'
  rw [show (n : ℂ)⁻¹ = ((n : ℝ)⁻¹ : ℝ) by
    symm
    exact Complex.ofReal_inv (n : ℝ)]
  rw [show (2 * (n : ℂ))⁻¹ = ((2 * (n : ℝ))⁻¹ : ℝ) by
    symm
    convert Complex.ofReal_inv (2 * (n : ℝ)) using 1; norm_num]
  push_cast
  apply Complex.ext
  · simp
    field_simp
  · simp

/-- The Wilson action after all crossing links have been fixed to `1`. -/
def gaugeFixedAction [Fintype Q]
    (U : SideConfiguration G P × SideConfiguration G P) : ℝ :=
  D.positiveAction U.1 + D.positiveAction U.2 +
    ∑ q : Q, D.representation.wilsonPotential
      (D.crossHolonomy q U.2 * (D.crossHolonomy q U.1)⁻¹)

theorem continuous_gaugeFixedAction [Fintype Q]
    [IsTopologicalGroup G] : Continuous D.gaugeFixedAction := by
  unfold gaugeFixedAction
  fun_prop

/-- The unfixed action is the pullback of the gauge-fixed Wilson action.  On
the negative side the crossing field is inverted, as dictated by link
reflection. -/
def action [Fintype Q] (U : ReflectedConfiguration G C P) : ℝ :=
  D.gaugeFixedAction
    (D.gaugeFix.fixSide (invertCrossing U.1) U.2.1,
      D.gaugeFix.fixSide U.1 U.2.2)

theorem continuous_action [Fintype Q]
    [IsTopologicalGroup G] : Continuous D.action := by
  unfold action
  apply D.continuous_gaugeFixedAction.comp
  have hinv : Continuous fun U : CrossingConfiguration G C ↦ invertCrossing U := by
    apply continuous_pi
    intro e
    exact continuous_inv.comp (continuous_apply e)
  have hminus : Continuous fun U : ReflectedConfiguration G C P ↦
      D.gaugeFix.fixSide (invertCrossing U.1) U.2.1 :=
    D.gaugeFix.continuous_fixSide.comp <|
      (hinv.comp continuous_fst).prodMk
        (continuous_fst.comp (continuous_snd : Continuous fun U :
          ReflectedConfiguration G C P ↦ U.2))
  have hplus : Continuous fun U : ReflectedConfiguration G C P ↦
      D.gaugeFix.fixSide U.1 U.2.2 :=
    D.gaugeFix.continuous_fixSide.comp <|
      continuous_fst.prodMk
        (continuous_snd.comp (continuous_snd : Continuous fun U :
          ReflectedConfiguration G C P ↦ U.2))
  exact hminus.prodMk hplus

@[simp]
theorem action_reflect [Fintype Q] (U : ReflectedConfiguration G C P) :
    D.action (reflect U) = D.action U := by
  simp only [action, reflect, invertCrossing_invertCrossing,
    gaugeFixedAction]
  congr 1
  · rw [add_comm (D.positiveAction _) (D.positiveAction _)]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [← D.representation.wilsonPotential.inv_invariant]
  simp only [mul_inv_rev, inv_inv]

/-- A positive-side observable before the crossing forest is gauge fixed. -/
abbrev PositiveObservable (G : Type*) (C P : Type*) [TopologicalSpace G] :=
  C(HalfConfiguration G C P, ℂ)

/-- The exact gauge-invariance condition needed for link reflection: replacing
the crossing field by `1` and applying its endpoint gauge transformation to
the remaining side links leaves the observable unchanged. -/
def IsGaugeInvariant (F : PositiveObservable G C P) : Prop :=
  ∀ Ucross Uside, F (Ucross, Uside) =
    F (1, D.gaugeFix.fixSide Ucross Uside)

theorem isGaugeInvariant_zero : D.IsGaugeInvariant 0 := by
  intro Ucross Uside
  rfl

theorem IsGaugeInvariant.add {F H : PositiveObservable G C P}
    (hF : D.IsGaugeInvariant F) (hH : D.IsGaugeInvariant H) :
    D.IsGaugeInvariant (F + H) := by
  intro Ucross Uside
  simp only [ContinuousMap.add_apply]
  rw [hF, hH]

theorem IsGaugeInvariant.smul (c : ℂ) {F : PositiveObservable G C P}
    (hF : D.IsGaugeInvariant F) : D.IsGaugeInvariant (c • F) := by
  intro Ucross Uside
  simp only [ContinuousMap.smul_apply]
  rw [hF]

/-- The positive algebra used for half-integer reflection: continuous
observables satisfying the crossing-forest gauge-invariance identity. -/
def gaugeInvariantSubmodule : Submodule ℂ (PositiveObservable G C P) where
  carrier := {F | D.IsGaugeInvariant F}
  zero_mem' := D.isGaugeInvariant_zero
  add_mem' := fun hF hH ↦ IsGaugeInvariant.add D hF hH
  smul_mem' := fun c _F hF ↦ IsGaugeInvariant.smul D c hF

/-- Gauge-invariant positive-side observables. -/
abbrev GaugeInvariantObservable := gaugeInvariantSubmodule D

/-- Lift a positive-side observable to the full reflected variables. -/
def liftPositive (F : PositiveObservable G C P) :
    C(ReflectedConfiguration G C P, ℂ) where
  toFun U := F (U.1, U.2.2)
  continuous_toFun := by fun_prop

/-- Anti-linear half-integer reflection. -/
def theta [IsTopologicalGroup G]
    (F : C(ReflectedConfiguration G C P, ℂ)) :
    C(ReflectedConfiguration G C P, ℂ) where
  toFun U := conj (F (reflect U))
  continuous_toFun := by
    have hinv : Continuous fun U : CrossingConfiguration G C ↦ invertCrossing U := by
      apply continuous_pi
      intro e
      exact continuous_inv.comp (continuous_apply e)
    exact Complex.continuous_conj.comp <| F.continuous.comp <|
      (hinv.comp continuous_fst).prodMk
        (continuous_snd.comp continuous_snd |>.prodMk
          (continuous_fst.comp continuous_snd))

@[simp]
theorem theta_liftPositive_apply [IsTopologicalGroup G]
    (F : PositiveObservable G C P) (U : ReflectedConfiguration G C P) :
    theta (liftPositive F) U = conj (F (invertCrossing U.1, U.2.1)) := rfl

section Haar

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [IsTopologicalGroup G] [CompactSpace G] [GaugeHaarProbability G]
  [Fintype C] [Fintype P] [Fintype Q]

/-- Product Haar on the crossing links. -/
abbrev crossingHaar : Measure (CrossingConfiguration G C) :=
  ProductHaar.measure G C

/-- Product Haar on either strict half-volume. -/
abbrev sideHaar : Measure (SideConfiguration G P) :=
  ProductHaar.measure G P

/-- Product Haar in the half-integer reflection variables. -/
abbrev reflectedHaar : Measure (ReflectedConfiguration G C P) :=
  (crossingHaar (G := G) (C := C)).prod
    ((sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P)))

/-- The finite-volume Boltzmann weight before gauge fixing. -/
def boltzmannWeight (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (U : ReflectedConfiguration G C P) : ℝ :=
  Real.exp (β * D.action U)

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G] [Fintype C] [Fintype P] in
theorem continuous_boltzmannWeight (D : WilsonActionDecomposition G n C P Q) (β : ℝ) :
    Continuous (D.boltzmannWeight β) := by
  exact Real.continuous_exp.comp (continuous_const.mul D.continuous_action)

/-- The unnormalized Gibbs pairing of reflected positive observables. -/
def gibbsReflectionPairing (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) : ℂ :=
  ∫ U, (D.boltzmannWeight β U : ℂ) *
      theta (liftPositive F) U * liftPositive H U ∂reflectedHaar

/-- Finite-volume partition function in the link-reflection variables. -/
def partitionFunction (D : WilsonActionDecomposition G n C P Q) (β : ℝ) : ℝ :=
  ∫ U, D.boltzmannWeight β U ∂reflectedHaar

theorem integrable_boltzmannWeight
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ) :
    Integrable (D.boltzmannWeight β) reflectedHaar :=
  (D.continuous_boltzmannWeight β).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem partitionFunction_pos
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ) :
    0 < D.partitionFunction β := by
  unfold partitionFunction boltzmannWeight
  exact integral_exp_pos (D.integrable_boltzmannWeight β)

/-- Normalized reflection inner product on the gauge-invariant positive
algebra. -/
def reflectionInnerProduct (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) : ℂ :=
  (D.partitionFunction β : ℂ)⁻¹ * D.gibbsReflectionPairing β F H

/-- The pairing after the crossing forest has been fixed to the identity. -/
def gaugeFixedPairing (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) : ℂ :=
  ∫ V : SideConfiguration G P × SideConfiguration G P,
    (Real.exp (β * D.gaugeFixedAction V) : ℂ) *
      conj (F (1, V.1)) * H (1, V.2)
    ∂(sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P))

/-- A labelled Taylor word in cross-plane matrix coefficients. -/
abbrev CrossWord (Q : Type*) (n m : ℕ) := Fin m → CrossLetter Q n

/-- Product of the positive-side features specified by a Taylor word. -/
def crossMonomial (D : WilsonActionDecomposition G n C P Q) {m : ℕ}
    (w : CrossWord Q n m) (U : SideConfiguration G P) : ℂ :=
  ∏ r, D.crossFeature (w r) U

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G] [Fintype C] [Fintype P] [Fintype Q] in
theorem continuous_crossMonomial
    (D : WilsonActionDecomposition G n C P Q) {m : ℕ}
    (w : CrossWord Q n m) : Continuous (D.crossMonomial w) := by
  unfold crossMonomial
  apply continuous_finsetProd Finset.univ
  intro r _hr
  exact D.continuous_crossFeature (w r)

/-- The half-volume amplitude attached to one labelled Taylor word. -/
def taylorAmplitude (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F : PositiveObservable G C P) {m : ℕ} (w : CrossWord Q n m) : ℂ :=
  ∫ U, (Real.exp (β * D.positiveAction U) : ℂ) * F (1, U) *
      D.crossMonomial w U ∂sideHaar

/-- The positive Taylor coefficient of degree `m`. -/
def taylorCoefficient (_D : WilsonActionDecomposition G n C P Q)
    (β : ℝ) (m : ℕ) : ℝ :=
  (β / (2 * n : ℝ)) ^ m / m.factorial

/-- Taylor/Fubini expansion of the gauge-fixed reflection pairing.  Every
degree is a finite Gram sum indexed by labelled matrix-coefficient words. -/
def taylorPairing (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) : ℂ :=
  ∑' m : ℕ, (D.taylorCoefficient β m : ℂ) *
    ∑ w : CrossWord Q n m,
      conj (D.taylorAmplitude β F w) * D.taylorAmplitude β H w

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [IsTopologicalGroup G] [CompactSpace G] [GaugeHaarProbability G]
  [Fintype C] [Fintype P] in
/-- Powers of the rank-one cross kernel expand as a finite sum over labelled
Taylor words. -/
theorem crossKernel_pow_eq_sum_words
    (D : WilsonActionDecomposition G n C P Q) (m : ℕ)
    (V : SideConfiguration G P × SideConfiguration G P) :
    D.crossKernel V ^ m =
      ∑ w : CrossWord Q n m,
        conj (D.crossMonomial w V.1) * D.crossMonomial w V.2 := by
  rw [crossKernel, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro w _hw
  unfold crossMonomial
  rw [map_prod, ← Finset.prod_mul_distrib]

/-- Continuous cross-plane exponential argument. -/
def crossExponentArgument (D : WilsonActionDecomposition G n C P Q) (β : ℝ) :
    C(SideConfiguration G P × SideConfiguration G P, ℂ) where
  toFun V := (β / (2 * n : ℝ) : ℂ) * D.crossKernel V
  continuous_toFun := continuous_const.mul D.continuous_crossKernel

/-- The factor containing the two strict-half actions and observables, before
inserting any cross-plane Taylor letters. -/
def sidePairingFactor (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) :
    C(SideConfiguration G P × SideConfiguration G P, ℂ) where
  toFun V :=
    (Real.exp (β * D.positiveAction V.1) : ℂ) *
      (Real.exp (β * D.positiveAction V.2) : ℂ) *
      conj (F (1, V.1)) * H (1, V.2)
  continuous_toFun := by fun_prop

/-- Degree-`m` Taylor integrand of the cross-plane Boltzmann factor. -/
def taylorIntegrand (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) (m : ℕ) :
    C(SideConfiguration G P × SideConfiguration G P, ℂ) :=
  D.sidePairingFactor β F H *
    ((m.factorial : ℂ)⁻¹ • (D.crossExponentArgument β) ^ m)

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] [Fintype C] in
/-- The Taylor integrands are normally summable in the uniform norm.  This is
the analytic justification for exchanging the exponential series and Haar
integration below. -/
theorem summable_norm_taylorIntegrand
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) :
    Summable fun m ↦ ‖D.taylorIntegrand β F H m‖ := by
  let K := D.crossExponentArgument β
  have hExp : Summable fun m : ℕ ↦
      ‖(m.factorial : ℂ)⁻¹ • K ^ m‖ :=
    NormedSpace.norm_expSeries_summable' K
  have hmajor : Summable fun m : ℕ ↦
      ‖D.sidePairingFactor β F H‖ * ‖(m.factorial : ℂ)⁻¹ • K ^ m‖ :=
    Summable.mul_left _ hExp
  refine hmajor.of_nonneg_of_le (fun m ↦ norm_nonneg _) (fun m ↦ ?_)
  unfold taylorIntegrand
  exact norm_mul_le _ _

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] [Fintype C] in
/-- Pointwise summation of the cross-plane Taylor integrands. -/
theorem tsum_taylorIntegrand_apply
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P)
    (V : SideConfiguration G P × SideConfiguration G P) :
    (∑' m : ℕ, D.taylorIntegrand β F H m V) =
      D.sidePairingFactor β F H V *
        Complex.exp (D.crossExponentArgument β V) := by
  rw [Complex.exp_eq_exp_ℂ]
  refine HasSum.congr_fun ((NormedSpace.expSeries_div_hasSum_exp
    (D.crossExponentArgument β V)).mul_left
      (D.sidePairingFactor β F H V)) (fun m ↦ ?_) |>.tsum_eq
  simp [taylorIntegrand]
  ring

omit [Fintype C] in
/-- The normally convergent Taylor series may be integrated term by term
against product Haar. -/
theorem tsum_integral_taylorIntegrand
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) :
    (∑' m : ℕ, ∫ V, D.taylorIntegrand β F H m V
      ∂(sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P))) =
      ∫ V, ∑' m : ℕ, D.taylorIntegrand β F H m V
        ∂(sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P)) := by
  let μ := (sideHaar (G := G) (P := P)).prod
    (sideHaar (G := G) (P := P))
  apply integral_tsum_of_summable_integral_norm
  · intro m
    exact (D.taylorIntegrand β F H m).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · have hnorm := D.summable_norm_taylorIntegrand β F H
    refine hnorm.of_nonneg_of_le (fun m ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (fun m ↦ ?_)
    calc
      ∫ V, ‖D.taylorIntegrand β F H m V‖ ∂μ ≤
          ∫ _V, ‖D.taylorIntegrand β F H m‖ ∂μ := by
        apply integral_mono
        · exact (D.taylorIntegrand β F H m).continuous.norm.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        · exact integrable_const _
        · intro V
          exact (D.taylorIntegrand β F H m).norm_coe_le_norm V
      _ = ‖D.taylorIntegrand β F H m‖ := by simp [μ]

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] [Fintype C] in
/-- For a gauge-fixed cross-plane action, the Boltzmann integrand equals the
summed Taylor integrand pointwise. -/
theorem gaugeFixedIntegrand_eq_tsum
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P)
    (V : SideConfiguration G P × SideConfiguration G P) :
    (Real.exp (β * D.gaugeFixedAction V) : ℂ) *
        conj (F (1, V.1)) * H (1, V.2) =
      ∑' m : ℕ, D.taylorIntegrand β F H m V := by
  rw [D.tsum_taylorIntegrand_apply]
  have harg : D.crossExponentArgument β V =
      ((β * ∑ q : Q, D.representation.wilsonPotential
        (D.crossHolonomy q V.2 * (D.crossHolonomy q V.1)⁻¹) : ℝ) : ℂ) := by
    simp only [crossExponentArgument, ContinuousMap.coe_mk]
    push_cast
    rw [D.sum_wilsonPotential_eq_crossKernel V]
    ring
  rw [harg, ← Complex.ofReal_exp]
  simp only [sidePairingFactor, ContinuousMap.coe_mk]
  rw [show β * D.gaugeFixedAction V =
      β * D.positiveAction V.1 + β * D.positiveAction V.2 +
        β * ∑ q : Q, D.representation.wilsonPotential
          (D.crossHolonomy q V.2 * (D.crossHolonomy q V.1)⁻¹) by
    unfold gaugeFixedAction
    ring]
  rw [Real.exp_add, Real.exp_add]
  push_cast
  ring

omit [Fintype C] in
/-- Exact Taylor expansion of the gauge-fixed reflection pairing. -/
theorem gaugeFixedPairing_eq_tsum_integrals
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) :
    D.gaugeFixedPairing β F H =
      ∑' m : ℕ, ∫ V, D.taylorIntegrand β F H m V
        ∂(sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P)) := by
  rw [D.tsum_integral_taylorIntegrand β F H]
  unfold gaugeFixedPairing
  apply integral_congr_ae
  filter_upwards with V
  exact D.gaugeFixedIntegrand_eq_tsum β F H V

omit [BorelSpace G] [SecondCountableTopology G] [IsTopologicalGroup G]
  [Fintype C] [Fintype Q] in
/-- Fubini factorization for one labelled Taylor word. -/
theorem integral_word_eq_amplitudes
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) {m : ℕ} (w : CrossWord Q n m) :
    (∫ V : SideConfiguration G P × SideConfiguration G P,
      D.sidePairingFactor β F H V *
        (conj (D.crossMonomial w V.1) * D.crossMonomial w V.2)
      ∂(sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P))) =
      conj (D.taylorAmplitude β F w) * D.taylorAmplitude β H w := by
  let leftFactor : SideConfiguration G P → ℂ := fun U ↦
    conj ((Real.exp (β * D.positiveAction U) : ℂ) * F (1, U) *
      D.crossMonomial w U)
  let rightFactor : SideConfiguration G P → ℂ := fun U ↦
    (Real.exp (β * D.positiveAction U) : ℂ) * H (1, U) *
      D.crossMonomial w U
  have hpoint : ∀ V : SideConfiguration G P × SideConfiguration G P,
      D.sidePairingFactor β F H V *
          (conj (D.crossMonomial w V.1) * D.crossMonomial w V.2) =
        leftFactor V.1 * rightFactor V.2 := by
    intro V
    simp only [sidePairingFactor, ContinuousMap.coe_mk, leftFactor, rightFactor,
      map_mul, Complex.conj_ofReal]
    ring
  simp_rw [hpoint]
  rw [integral_prod_mul leftFactor rightFactor]
  rw [show (∫ U, leftFactor U ∂sideHaar) =
      conj (D.taylorAmplitude β F w) by
    change (∫ U, conj ((Real.exp (β * D.positiveAction U) : ℂ) *
      F (1, U) * D.crossMonomial w U) ∂sideHaar) = _
    rw [integral_conj]
    rfl]
  rfl

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] [Fintype C] in
/-- Pointwise degree-`m` expansion into a finite Gram kernel. -/
theorem taylorIntegrand_eq_sum_words
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) (m : ℕ)
    (V : SideConfiguration G P × SideConfiguration G P) :
    D.taylorIntegrand β F H m V =
      (D.taylorCoefficient β m : ℂ) *
        ∑ w : CrossWord Q n m,
          D.sidePairingFactor β F H V *
            (conj (D.crossMonomial w V.1) * D.crossMonomial w V.2) := by
  simp only [taylorIntegrand, ContinuousMap.mul_apply, ContinuousMap.smul_apply,
    ContinuousMap.pow_apply, crossExponentArgument, ContinuousMap.coe_mk]
  rw [mul_pow, D.crossKernel_pow_eq_sum_words]
  rw [← Finset.mul_sum]
  unfold taylorCoefficient
  push_cast
  ring

omit [Fintype C] in
/-- Each integrated Taylor coefficient is an explicit finite Gram sum. -/
theorem integral_taylorIntegrand_eq_gram
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) (m : ℕ) :
    (∫ V, D.taylorIntegrand β F H m V
      ∂(sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P))) =
      (D.taylorCoefficient β m : ℂ) *
        ∑ w : CrossWord Q n m,
          conj (D.taylorAmplitude β F w) * D.taylorAmplitude β H w := by
  simp_rw [D.taylorIntegrand_eq_sum_words β F H m]
  rw [integral_const_mul]
  rw [integral_finsetSum Finset.univ]
  · apply congrArg ((D.taylorCoefficient β m : ℂ) * ·)
    apply Finset.sum_congr rfl
    intro w _hw
    exact D.integral_word_eq_amplitudes β F H w
  · intro w _hw
    exact ((D.sidePairingFactor β F H).continuous.mul
      ((Complex.continuous_conj.comp
        ((D.continuous_crossMonomial w).comp continuous_fst)).mul
          ((D.continuous_crossMonomial w).comp continuous_snd))).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)

omit [Fintype C] in
/-- The gauge-fixed pairing is exactly its labelled Taylor/Fubini Gram
expansion. -/
theorem gaugeFixedPairing_eq_taylorPairing
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) :
    D.gaugeFixedPairing β F H = D.taylorPairing β F H := by
  rw [D.gaugeFixedPairing_eq_tsum_integrals]
  unfold taylorPairing
  apply tsum_congr
  intro m
  exact D.integral_taylorIntegrand_eq_gram β F H m

omit [Fintype C] in
/-- Absolute summability of the integrated Taylor coefficients. -/
theorem summable_integral_taylorIntegrand
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) :
    Summable fun m : ℕ ↦ ∫ V, D.taylorIntegrand β F H m V
      ∂(sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P)) := by
  let μ := (sideHaar (G := G) (P := P)).prod
    (sideHaar (G := G) (P := P))
  have hnorm := D.summable_norm_taylorIntegrand β F H
  apply Summable.of_norm
  refine hnorm.of_nonneg_of_le (fun m ↦ norm_nonneg _) (fun m ↦ ?_)
  calc
    ‖∫ V, D.taylorIntegrand β F H m V ∂μ‖ ≤
        ∫ V, ‖D.taylorIntegrand β F H m V‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _V, ‖D.taylorIntegrand β F H m‖ ∂μ := by
      apply integral_mono
      · exact (D.taylorIntegrand β F H m).continuous.norm.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact integrable_const _
      · intro V
        exact (D.taylorIntegrand β F H m).norm_coe_le_norm V
    _ = ‖D.taylorIntegrand β F H m‖ := by simp [μ]

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [IsTopologicalGroup G] [CompactSpace G] [GaugeHaarProbability G]
  [Fintype C] [Fintype P] [Fintype Q] in
theorem taylorCoefficient_nonneg
    (D : WilsonActionDecomposition G n C P Q) {β : ℝ} (hβ : 0 ≤ β) (m : ℕ) :
    0 ≤ D.taylorCoefficient β m := by
  unfold taylorCoefficient
  positivity [D.representation.dimension_pos]

omit [BorelSpace G] [SecondCountableTopology G] [IsTopologicalGroup G]
  [CompactSpace G] [Fintype C] in
/-- Every diagonal Taylor coefficient is a nonnegative real number. -/
theorem taylorGramTerm_self_nonneg
    (D : WilsonActionDecomposition G n C P Q) {β : ℝ} (hβ : 0 ≤ β)
    (F : PositiveObservable G C P) (m : ℕ) :
    Complex.im ((D.taylorCoefficient β m : ℂ) *
        ∑ w : CrossWord Q n m,
          conj (D.taylorAmplitude β F w) * D.taylorAmplitude β F w) = 0 ∧
      0 ≤ Complex.re ((D.taylorCoefficient β m : ℂ) *
        ∑ w : CrossWord Q n m,
          conj (D.taylorAmplitude β F w) * D.taylorAmplitude β F w) := by
  have hsum : (∑ w : CrossWord Q n m,
      conj (D.taylorAmplitude β F w) * D.taylorAmplitude β F w) =
      ((∑ w : CrossWord Q n m, ‖D.taylorAmplitude β F w‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro w _hw
    rw [Complex.conj_mul']
  rw [hsum]
  have hre : Complex.re
      (((∑ w : CrossWord Q n m, ‖D.taylorAmplitude β F w‖ ^ 2 : ℝ) : ℂ)) =
      ∑ w : CrossWord Q n m, ‖D.taylorAmplitude β F w‖ ^ 2 := rfl
  have him : Complex.im
      (((∑ w : CrossWord Q n m, ‖D.taylorAmplitude β F w‖ ^ 2 : ℝ) : ℂ)) = 0 := rfl
  constructor
  · rw [Complex.mul_im, him]
    simp
  · rw [Complex.mul_re, hre, him]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (D.taylorCoefficient_nonneg hβ m) <|
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

omit [Fintype C] in
/-- The exact Taylor/Fubini Gram expansion is positive on the diagonal for
`beta ≥ 0`. -/
theorem taylorPairing_self_nonneg
    (D : WilsonActionDecomposition G n C P Q) {β : ℝ} (hβ : 0 ≤ β)
    (F : PositiveObservable G C P) :
    Complex.im (D.taylorPairing β F F) = 0 ∧
      0 ≤ Complex.re (D.taylorPairing β F F) := by
  let term : ℕ → ℂ := fun m ↦ (D.taylorCoefficient β m : ℂ) *
    ∑ w : CrossWord Q n m,
      conj (D.taylorAmplitude β F w) * D.taylorAmplitude β F w
  have hsum : Summable term := by
    have hint := D.summable_integral_taylorIntegrand β F F
    apply hint.congr
    intro m
    exact D.integral_taylorIntegrand_eq_gram β F F m
  unfold taylorPairing
  constructor
  · rw [Complex.im_tsum hsum]
    exact HasSum.tsum_eq <| HasSum.congr_fun hasSum_zero fun m ↦
      (show Complex.im (term m) = 0 from
        D.taylorGramTerm_self_nonneg hβ F m |>.1)
  · rw [Complex.re_tsum hsum]
    exact tsum_nonneg fun m ↦ (D.taylorGramTerm_self_nonneg hβ F m).2

theorem integrable_gibbsReflectionIntegrand
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) :
    Integrable (fun U ↦ (D.boltzmannWeight β U : ℂ) *
      theta (liftPositive F) U * liftPositive H U) reflectedHaar := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact ((Complex.continuous_ofReal.comp (D.continuous_boltzmannWeight β)).mul
    (theta (liftPositive F)).continuous).mul (liftPositive H).continuous

omit [Fintype C] in
/-- At fixed crossing field, gauge invariance of both observables and
coordinatewise Haar invariance remove that crossing field from the reflected
integral.  This is the finite crossing-forest gauge-fixing step. -/
theorem integral_sides_eq_gaugeFixed
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P)
    (hF : D.IsGaugeInvariant F) (hH : D.IsGaugeInvariant H)
    (Ucross : CrossingConfiguration G C) :
    (∫ V : SideConfiguration G P × SideConfiguration G P,
      (D.boltzmannWeight β (Ucross, V) : ℂ) *
        theta (liftPositive F) (Ucross, V) * liftPositive H (Ucross, V)
      ∂(sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P))) =
    D.gaugeFixedPairing β F H := by
  let Eminus := D.gaugeFix.fixSideEquiv (invertCrossing Ucross)
  let Eplus := D.gaugeFix.fixSideEquiv Ucross
  let E : (SideConfiguration G P × SideConfiguration G P) ≃ᵐ
      (SideConfiguration G P × SideConfiguration G P) :=
    Eminus.prodCongr Eplus
  have hE : MeasurePreserving E
      ((sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P)))
      ((sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P))) :=
    MeasurePreserving.prod
      (CrossingForestGaugeFix.measurePreserving_fixSideEquiv D.gaugeFix
        (invertCrossing Ucross))
      (CrossingForestGaugeFix.measurePreserving_fixSideEquiv D.gaugeFix Ucross)
  let K : (SideConfiguration G P × SideConfiguration G P) → ℂ := fun W ↦
    (Real.exp (β * D.gaugeFixedAction W) : ℂ) *
      conj (F (1, W.1)) * H (1, W.2)
  have hpoint : ∀ V, (D.boltzmannWeight β (Ucross, V) : ℂ) *
        theta (liftPositive F) (Ucross, V) * liftPositive H (Ucross, V) = K (E V) := by
    intro V
    change (Real.exp (β * D.gaugeFixedAction
        (D.gaugeFix.fixSide (invertCrossing Ucross) V.1,
          D.gaugeFix.fixSide Ucross V.2)) : ℂ) *
        conj (F (invertCrossing Ucross, V.1)) * H (Ucross, V.2) =
      (Real.exp (β * D.gaugeFixedAction
        (D.gaugeFix.fixSide (invertCrossing Ucross) V.1,
          D.gaugeFix.fixSide Ucross V.2)) : ℂ) *
        conj (F (1, D.gaugeFix.fixSide (invertCrossing Ucross) V.1)) *
          H (1, D.gaugeFix.fixSide Ucross V.2)
    rw [hF (invertCrossing Ucross) V.1, hH Ucross V.2]
  simp_rw [hpoint]
  change (∫ V, K (E V) ∂_) = _
  rw [hE.integral_comp' K]
  rfl

/-- Fubini plus the forest gauge fix identifies the original reflected Gibbs
pairing with the gauge-fixed pairing. -/
theorem gibbsReflectionPairing_eq_gaugeFixed
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P)
    (hF : D.IsGaugeInvariant F) (hH : D.IsGaugeInvariant H) :
    D.gibbsReflectionPairing β F H = D.gaugeFixedPairing β F H := by
  unfold gibbsReflectionPairing reflectedHaar
  rw [integral_prod _ (D.integrable_gibbsReflectionIntegrand β F H)]
  simp_rw [D.integral_sides_eq_gaugeFixed β F H hF hH]
  simp

/-- Milestone 18: half-integer/link reflection positivity.  Gauge invariance
is required precisely for the crossing-forest gauge-fixing identity. -/
theorem linkReflectionPositivity
    (D : WilsonActionDecomposition G n C P Q) {β : ℝ} (hβ : 0 ≤ β)
    (F : PositiveObservable G C P) (hF : D.IsGaugeInvariant F) :
    Complex.im (D.gibbsReflectionPairing β F F) = 0 ∧
      0 ≤ Complex.re (D.gibbsReflectionPairing β F F) := by
  rw [D.gibbsReflectionPairing_eq_gaugeFixed β F F hF hF,
    D.gaugeFixedPairing_eq_taylorPairing]
  exact D.taylorPairing_self_nonneg hβ F

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [IsTopologicalGroup G] [CompactSpace G] [GaugeHaarProbability G]
  [Fintype C] [Fintype P] in
/-- The gauge-fixed action is symmetric under exchange of the two strict
halves. -/
theorem gaugeFixedAction_swap
    (D : WilsonActionDecomposition G n C P Q)
    (V : SideConfiguration G P × SideConfiguration G P) :
    D.gaugeFixedAction V.swap = D.gaugeFixedAction V := by
  rcases V with ⟨Vminus, Vplus⟩
  simp only [Prod.swap, gaugeFixedAction]
  congr 1
  · ring
  apply Finset.sum_congr rfl
  intro q _hq
  rw [← D.representation.wilsonPotential.inv_invariant]
  simp only [mul_inv_rev, inv_inv]

omit [Fintype C] in
theorem integrable_gaugeFixedPairingIntegrand
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) :
    Integrable (fun V : SideConfiguration G P × SideConfiguration G P ↦
      (Real.exp (β * D.gaugeFixedAction V) : ℂ) *
        conj (F (1, V.1)) * H (1, V.2))
      ((sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P))) := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact ((Complex.continuous_ofReal.comp <|
    Real.continuous_exp.comp (continuous_const.mul D.continuous_gaugeFixedAction)).mul
      (Complex.continuous_conj.comp <| F.continuous.comp
        (continuous_const.prodMk continuous_fst))).mul <|
          H.continuous.comp (continuous_const.prodMk continuous_snd)

omit [Fintype C] in
theorem gaugeFixedPairing_add_left
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F K H : PositiveObservable G C P) :
    D.gaugeFixedPairing β (F + K) H =
      D.gaugeFixedPairing β F H + D.gaugeFixedPairing β K H := by
  unfold gaugeFixedPairing
  rw [← integral_add (D.integrable_gaugeFixedPairingIntegrand β F H)
    (D.integrable_gaugeFixedPairingIntegrand β K H)]
  apply integral_congr_ae
  filter_upwards with V
  simp only [ContinuousMap.add_apply, map_add]
  ring

omit [BorelSpace G] [SecondCountableTopology G] [IsTopologicalGroup G]
  [CompactSpace G] [Fintype C] in
theorem gaugeFixedPairing_smul_left
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ) (c : ℂ)
    (F H : PositiveObservable G C P) :
    D.gaugeFixedPairing β (c • F) H =
      conj c * D.gaugeFixedPairing β F H := by
  unfold gaugeFixedPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with V
  change (Real.exp (β * D.gaugeFixedAction V) : ℂ) *
      conj (c * F (1, V.1)) * H (1, V.2) = _
  rw [map_mul]
  ring

omit [BorelSpace G] [SecondCountableTopology G] [IsTopologicalGroup G]
  [CompactSpace G] [Fintype C] in
/-- Hermitian symmetry of the gauge-fixed pairing. -/
theorem gaugeFixedPairing_conj_symm
    (D : WilsonActionDecomposition G n C P Q) (β : ℝ)
    (F H : PositiveObservable G C P) :
    conj (D.gaugeFixedPairing β H F) = D.gaugeFixedPairing β F H := by
  let K : (SideConfiguration G P × SideConfiguration G P) → ℂ := fun V ↦
    (Real.exp (β * D.gaugeFixedAction V) : ℂ) *
      conj (F (1, V.1)) * H (1, V.2)
  calc
    conj (D.gaugeFixedPairing β H F) =
        ∫ V : SideConfiguration G P × SideConfiguration G P,
          conj ((Real.exp (β * D.gaugeFixedAction V) : ℂ) *
            conj (H (1, V.1)) * F (1, V.2))
          ∂(sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P)) := by
      rw [integral_conj]
      rfl
    _ = ∫ V : SideConfiguration G P × SideConfiguration G P, K V.swap
          ∂(sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P)) := by
      apply integral_congr_ae
      filter_upwards with V
      have ha : D.gaugeFixedAction (V.2, V.1) = D.gaugeFixedAction V := by
        simpa only [Prod.swap] using D.gaugeFixedAction_swap V
      simp only [K, Prod.swap, ha, Complex.conj_ofReal, map_mul]
      change (Real.exp (β * D.gaugeFixedAction V) : ℂ) *
          conj (conj (H (1, V.1))) * conj (F (1, V.2)) = _
      rw [show conj (conj (H (1, V.1))) = H (1, V.1) by simp]
      ring
    _ = ∫ V : SideConfiguration G P × SideConfiguration G P, K V
          ∂(sideHaar (G := G) (P := P)).prod (sideHaar (G := G) (P := P)) :=
      integral_prod_swap K
    _ = D.gaugeFixedPairing β F H := rfl

omit [Fintype C] in
/-- Cauchy--Schwarz for the unnormalized gauge-fixed reflection form. -/
theorem normSq_gaugeFixedPairing_le
    (D : WilsonActionDecomposition G n C P Q) {β : ℝ} (hβ : 0 ≤ β)
    (F H : PositiveObservable G C P) :
    Complex.normSq (D.gaugeFixedPairing β F H) ≤
      Complex.re (D.gaugeFixedPairing β F F) *
        Complex.re (D.gaugeFixedPairing β H H) := by
  letI : PreInnerProductSpace.Core ℂ (PositiveObservable G C P) := {
    inner := D.gaugeFixedPairing β
    conj_inner_symm := D.gaugeFixedPairing_conj_symm β
    re_inner_nonneg := fun F ↦ by
      rw [D.gaugeFixedPairing_eq_taylorPairing]
      exact (D.taylorPairing_self_nonneg hβ F).2
    add_left := D.gaugeFixedPairing_add_left β
    smul_left := fun F H c ↦ D.gaugeFixedPairing_smul_left β c F H
  }
  have hCS := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ
    (PositiveObservable G C P) _ _ _ _ F H
  change ‖D.gaugeFixedPairing β F H‖ * ‖D.gaugeFixedPairing β H F‖ ≤
    Complex.re (D.gaugeFixedPairing β F F) *
      Complex.re (D.gaugeFixedPairing β H H) at hCS
  have hnorm : ‖D.gaugeFixedPairing β H F‖ =
      ‖D.gaugeFixedPairing β F H‖ := by
    rw [← D.gaugeFixedPairing_conj_symm β F H, Complex.norm_conj]
  rw [hnorm, ← sq, Complex.sq_norm] at hCS
  exact hCS

/-- Cauchy--Schwarz for the unnormalized half-integer reflected Gibbs
pairing, on the gauge-invariant positive algebra. -/
theorem normSq_gibbsReflectionPairing_le
    (D : WilsonActionDecomposition G n C P Q) {β : ℝ} (hβ : 0 ≤ β)
    (F H : PositiveObservable G C P)
    (hF : D.IsGaugeInvariant F) (hH : D.IsGaugeInvariant H) :
    Complex.normSq (D.gibbsReflectionPairing β F H) ≤
      Complex.re (D.gibbsReflectionPairing β F F) *
        Complex.re (D.gibbsReflectionPairing β H H) := by
  rw [D.gibbsReflectionPairing_eq_gaugeFixed β F H hF hH,
    D.gibbsReflectionPairing_eq_gaugeFixed β F F hF hF,
    D.gibbsReflectionPairing_eq_gaugeFixed β H H hH hH]
  exact D.normSq_gaugeFixedPairing_le hβ F H

theorem reflectionInnerProduct_self_nonneg
    (D : WilsonActionDecomposition G n C P Q) {β : ℝ} (hβ : 0 ≤ β)
    (F : PositiveObservable G C P) (hF : D.IsGaugeInvariant F) :
    Complex.im (D.reflectionInnerProduct β F F) = 0 ∧
      0 ≤ Complex.re (D.reflectionInnerProduct β F F) := by
  have hpos := D.linkReflectionPositivity hβ F hF
  have hZ := D.partitionFunction_pos β
  unfold reflectionInnerProduct
  have hscale : ((D.partitionFunction β : ℂ)⁻¹) =
      ((D.partitionFunction β)⁻¹ : ℝ) := by
    symm
    exact Complex.ofReal_inv _
  rw [hscale]
  constructor
  · rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hpos.1,
      mul_zero]
  · rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr hZ.le) hpos.2

/-- Cauchy--Schwarz for the normalized half-integer reflection inner product. -/
theorem normSq_reflectionInnerProduct_le
    (D : WilsonActionDecomposition G n C P Q) {β : ℝ} (hβ : 0 ≤ β)
    (F H : PositiveObservable G C P)
    (hF : D.IsGaugeInvariant F) (hH : D.IsGaugeInvariant H) :
    Complex.normSq (D.reflectionInnerProduct β F H) ≤
      Complex.re (D.reflectionInnerProduct β F F) *
        Complex.re (D.reflectionInnerProduct β H H) := by
  have hCS := D.normSq_gibbsReflectionPairing_le hβ F H hF hH
  have hZ := D.partitionFunction_pos β
  unfold reflectionInnerProduct
  have hscale : ((D.partitionFunction β : ℂ)⁻¹) =
      ((D.partitionFunction β)⁻¹ : ℝ) := by
    symm
    exact Complex.ofReal_inv _
  rw [hscale]
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
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

end LinkReflection

end

end YangMills.Gauge
