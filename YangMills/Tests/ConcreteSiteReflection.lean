/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.ConcreteSiteReflectionPositivity

/-!
# Regression tests for the concrete site-reflection bridge

These checks exercise the geometric identification of centered cubic Gibbs
specifications with the labelled site-reflection normal form, its finite
positivity and Cauchy--Schwarz consequences, and their unconditional
cluster-expansion limits at every integer coordinate plane.
-/

open MeasureTheory
open YangMills.Gauge YangMills.Lattice.Cubic YangMills.StrongCoupling

namespace YangMills.Tests.ConcreteSiteReflection

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- The actual centered finite specification, with identity exterior data,
satisfies all three fields of the concrete symmetry predicate. -/
example (n : ℕ) (τ : Fin d) :
    (centeredSpecification n (1 : Configuration d G)).SiteSymmetric τ 0 :=
  centeredSpecification_one_siteSymmetric n τ

/-- Finite centered Gibbs measures satisfy site reflection positivity at
arbitrary real coupling; no gauge-invariance premise occurs. -/
example (Φ : RealPlaquettePotential G) (β : ℝ) (n : ℕ) (τ : Fin d) :
    SiteReflectionPositive
      (centeredGibbsSequence (fun _ => (1 : Configuration d G)) Φ β n :
        Measure (Configuration d G)) τ 0 :=
  centeredGibbsSequence_one_siteReflectionPositive Φ β n τ

/-- The same finite measures satisfy the squared Cauchy--Schwarz inequality
for every pair of positive-side local observables. -/
example (Φ : RealPlaquettePotential G) (β : ℝ) (n : ℕ) (τ : Fin d) :
    SiteReflectionCauchySchwarz
      (centeredGibbsSequence (fun _ => (1 : Configuration d G)) Φ β n :
        Measure (Configuration d G)) τ 0 :=
  centeredGibbsSequence_one_siteReflectionCauchySchwarz Φ β n τ

/-- The cluster-constructed infinite-volume measure is unconditionally
site-reflection positive at every integer coordinate plane. -/
example (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ) :
    SiteReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k :=
  centeredInfiniteVolume_siteReflectionPositive η Φ β hβ τ k

/-- A concrete smoke corollary applies positivity to the constant observable;
its support condition is discharged rather than assumed. -/
example (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ) (z : ℂ) :
    Complex.im (∫ A, ((LocalObservable.const (d := d) (G := G) z)
        |>.siteReflectionProduct τ k
          (LocalObservable.const (d := d) (G := G) z)) A
        ∂centeredInfiniteVolumeMeasure η Φ β hβ) = 0 ∧
      0 ≤ Complex.re (∫ A, ((LocalObservable.const (d := d) (G := G) z)
        |>.siteReflectionProduct τ k
          (LocalObservable.const (d := d) (G := G) z)) A
        ∂centeredInfiniteVolumeMeasure η Φ β hβ) := by
  apply centeredInfiniteVolume_siteReflectionPositive η Φ β hβ τ k
  intro e he
  simp [LocalObservable.const] at he

/-- Infinite-volume site Cauchy--Schwarz is likewise unconditional throughout
the explicit KP disk. -/
example (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ : Fin d) (k : ℤ) :
    SiteReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ k :=
  centeredInfiniteVolume_siteReflectionCauchySchwarz η Φ β hβ τ k

#print axioms Gauge.FiniteSpecification.siteReflectionPositive_gibbsMeasure
#print axioms Gauge.FiniteSpecification.normSq_integral_gibbsMeasure_siteReflectionProduct_le
#print axioms centeredSpecification_one_siteSymmetric
#print axioms centeredGibbsSequence_one_siteReflectionPositive
#print axioms centeredGibbsSequence_one_siteReflectionCauchySchwarz
#print axioms centeredInfiniteVolume_siteReflectionPositive
#print axioms centeredInfiniteVolume_siteReflectionCauchySchwarz

end

end YangMills.Tests.ConcreteSiteReflection
