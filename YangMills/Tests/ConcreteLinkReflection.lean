/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.ConcreteLinkReflectionPositivity

/-!
# Regression tests for the concrete link-reflection bridge

These checks exercise the completed link-symmetric finite specification, its
finite positivity theorem, the explicit KP comparison with centered boxes,
and the unconditional strong-coupling conclusions at every half-integer
coordinate plane.  The examples also check that the observable
gauge-invariance premise is usable on a simple concrete observable.
-/

open Filter MeasureTheory
open YangMills.Gauge YangMills.Lattice.Cubic YangMills.StrongCoupling

namespace YangMills.Tests.ConcreteLinkReflection

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- The completed box has the exact link symmetry required by the concrete
finite bridge. -/
example (n : ℕ) (τ : Fin d) :
    (linkSymmetricSpecification G d n τ).LinkSymmetric τ 0 :=
  linkSymmetricSpecification_linkSymmetric n τ

/-- Every active plaquette in that specification reads only dynamic edges. -/
example (n : ℕ) (τ : Fin d) :
    (linkSymmetricSpecification G d n τ).PlaquetteClosed :=
  linkSymmetricSpecification_plaquetteClosed n τ

/-- The completed boxes have the same local thermodynamic limit as ordinary
centered boxes, by the explicit one-root KP boundary estimate. -/
example (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (F : LocalObservable d G) :
    Tendsto (fun n => localExpectation
      (linkSymmetricGibbsSequence Φ β τ n) F) atTop
      (nhds (∫ A, F A ∂centeredInfiniteVolumeMeasure η Φ β hβ)) :=
  tendsto_linkSymmetric_localExpectation_infiniteVolume η Φ β hβ τ F

/-- Concrete link-reflection positivity holds at every half-integer plane
for gauge-invariant positive-side observables throughout the KP disk. -/
example (η : ℕ → Configuration d G)
    {nρ : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G nρ)
    (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    (τ : Fin d) (k : ℤ) :
    LinkReflectionPositive
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) τ k :=
  centeredInfiniteVolume_linkReflectionPositive η ρ β hβ0 hβ τ k

/-- The corresponding reflected Cauchy--Schwarz theorem has the same
concrete hypotheses and holds on every parallel plane. -/
example (η : ℕ → Configuration d G)
    {nρ : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G nρ)
    (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    (τ : Fin d) (k : ℤ) :
    LinkReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) τ k :=
  centeredInfiniteVolume_linkReflectionCauchySchwarz η ρ β hβ0 hβ τ k

/-- A constant local observable really satisfies the gauge-invariance premise
of link reflection positivity; this is not left as an abstract assumption. -/
example (z : ℂ) :
    Gauge.IsGaugeInvariant (LocalObservable.const (d := d) (G := G) z) := by
  intro g A
  rfl

/-- Positivity can be applied to a concrete gauge-invariant observable with
both side-support and gauge-invariance obligations discharged. -/
example (η : ℕ → Configuration d G)
    {nρ : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G nρ)
    (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    (τ : Fin d) (k : ℤ) (z : ℂ) :
    Complex.im (∫ A,
        ((LocalObservable.const (d := d) (G := G) z)
          |>.linkReflectionProduct τ k
            (LocalObservable.const (d := d) (G := G) z)) A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) = 0 ∧
      0 ≤ Complex.re (∫ A,
        ((LocalObservable.const (d := d) (G := G) z)
          |>.linkReflectionProduct τ k
            (LocalObservable.const (d := d) (G := G) z)) A
        ∂centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) := by
  apply centeredInfiniteVolume_linkReflectionPositive
    η ρ β hβ0 hβ τ k
  · intro e he
    simp [LocalObservable.const] at he
  · intro g A
    rfl

#print axioms Gauge.FiniteSpecification.linkReflectionPositive_gibbsMeasure
#print axioms Gauge.FiniteSpecification.normSq_integral_gibbsMeasure_linkReflectionProduct_le
#print axioms linkSymmetricSpecification_linkSymmetric
#print axioms linkSymmetricSpecification_plaquetteClosed
#print axioms tendsto_linkSymmetric_localExpectation_infiniteVolume
#print axioms centeredInfiniteVolume_linkReflectionPositive
#print axioms centeredInfiniteVolume_linkReflectionCauchySchwarz

end

end YangMills.Tests.ConcreteLinkReflection
