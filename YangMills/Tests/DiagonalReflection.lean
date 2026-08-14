/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.ConcreteDiagonalReflectionPositivity

/-!
# Regression tests for diagonal reflection positivity

These checks exercise the diagonal lattice involution, the full positive
observable algebra, the explicit Taylor/Fubini Gram identity, finite-volume
positivity and Cauchy--Schwarz, and the cluster-expansion infinite-volume
transfer.
-/

open Filter MeasureTheory
open YangMills.Gauge YangMills.Lattice.Cubic YangMills.StrongCoupling

namespace YangMills.Tests.DiagonalReflection

noncomputable section

variable {d : ℕ} {G O P Q : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] [Fintype O] [Fintype P] [Fintype Q] {n : ℕ}

/-- The affine diagonal reflection has the expected two-dimensional formula. -/
example {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) (x : Site d) :
    diagonalReflection τ σ k x τ = x σ + k ∧
      diagonalReflection τ σ k x σ = x τ - k := by
  simp [hτσ]

/-- Diagonal reflection is genuinely involutive on configurations. -/
example {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) (A : Configuration d G) :
    diagonalReflectConfiguration τ σ k
      (diagonalReflectConfiguration τ σ k A) = A := by
  simp [hτσ]

/-- The lattice reflection also acts involutively on canonical plaquettes. -/
example {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) (p : Plaquette d) :
    (p.diagonalReflect τ σ k).diagonalReflect τ σ k = p := by
  simp [hτσ]

/-- Constants lie in every diagonal positive algebra. -/
example (τ σ : Fin d) (k : ℤ) (z : ℂ) :
    (LocalObservable.const (d := d) (G := G) z)
      |>.SupportedInDiagonalPositiveHalf τ σ k := by
  intro e he
  simp [LocalObservable.const] at he

open YangMills.Gauge.DiagonalReflection
open YangMills.Gauge.DiagonalReflection.WilsonActionDecomposition

variable (D : WilsonActionDecomposition G n O P Q)

/-- No gauge-invariance witness is needed: the empty crossing field makes the
formal gauge-fix identity automatic for every observable. -/
example (F : PositiveObservable G O P) (Uzero : PlaneConfiguration G O) :
    (D.slice Uzero).IsGaugeInvariant (sliceObservable F Uzero) :=
  D.automaticGaugeFixIdentity F Uzero

/-- The full diagonal Gibbs pairing is exactly the cut-plaquette
Taylor/Fubini Gram series. -/
example (β : ℝ) (F H : PositiveObservable G O P) :
    D.gibbsReflectionPairing β F H = D.taylorPairing β F H :=
  D.gibbsReflectionPairing_eq_taylorPairing β F H

/-- Finite-volume diagonal reflection positivity has no observable
gauge-invariance premise. -/
example {β : ℝ} (hβ : 0 ≤ β) (F : PositiveObservable G O P) :
    Complex.im (D.gibbsReflectionPairing β F F) = 0 ∧
      0 ≤ Complex.re (D.gibbsReflectionPairing β F F) :=
  D.diagonalReflectionPositivity hβ F

/-- The normalized diagonal reflection form obeys Cauchy--Schwarz. -/
example {β : ℝ} (hβ : 0 ≤ β) (F H : PositiveObservable G O P) :
    Complex.normSq (D.reflectionInnerProduct β F H) ≤
      Complex.re (D.reflectionInnerProduct β F F) *
        Complex.re (D.reflectionInnerProduct β H H) :=
  D.normSq_reflectionInnerProduct_le hβ F H

/-- The abstract local-limit theorem closes diagonal Cauchy--Schwarz. -/
example (μn : ℕ → ProbabilityMeasure (Configuration d G))
    (μ : Measure (Configuration d G)) (τ σ : Fin d) (k : ℤ)
    (hlim : ∀ O : LocalObservable d G,
      Tendsto (fun m => localExpectation (μn m) O) atTop
        (nhds (∫ A, O A ∂μ)))
    (hfinite : ∀ᶠ m in atTop,
      DiagonalReflectionCauchySchwarz
        (μn m : Measure (Configuration d G)) τ σ k) :
    DiagonalReflectionCauchySchwarz μ τ σ k :=
  diagonalReflectionCauchySchwarz_of_localExpectation_tendsto
    μn μ τ σ k hlim hfinite

/-- The strong-coupling infinite-volume transfer consumes precisely the KP
local-expectation limit and eventual finite diagonal positivity. -/
example (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (τ σ : Fin d) (k : ℤ)
    (hfinite : ∀ᶠ m in atTop,
      DiagonalReflectionPositive
        (centeredGibbsSequence η Φ β m : Measure (Configuration d G)) τ σ k) :
    DiagonalReflectionPositive
      (centeredInfiniteVolumeMeasure η Φ β hβ) τ σ k :=
  centeredInfiniteVolume_diagonalReflectionPositive_of_eventually
    η Φ β hβ τ σ k hfinite

/-- The ordinary centered identity-exterior box has the concrete diagonal
symmetry used by the finite Gibbs bridge. -/
example (m : ℕ) {τ σ : Fin d} (hτσ : τ ≠ σ) :
    (centeredSpecification m (1 : Configuration d G)).DiagonalSymmetric
      τ σ 0 :=
  centeredSpecification_one_diagonalSymmetric m hτσ

/-- The concrete cluster theorem removes the abstract eventual-positivity
premise and reaches every affine diagonal plane. -/
example (η : ℕ → Configuration d G)
    {nρ : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G nρ)
    (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) :
    DiagonalReflectionPositive
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) τ σ k :=
  centeredInfiniteVolume_diagonalReflectionPositive
    η ρ β hβ0 hβ hτσ k

/-- The same concrete hypotheses give diagonal reflected
Cauchy--Schwarz in infinite volume. -/
example (η : ℕ → Configuration d G)
    {nρ : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G nρ)
    (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) :
    DiagonalReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) τ σ k :=
  centeredInfiniteVolume_diagonalReflectionCauchySchwarz
    η ρ β hβ0 hβ hτσ k

#print axioms Gauge.diagonalReflectConfiguration_diagonalReflectConfiguration
#print axioms WilsonActionDecomposition.gibbsReflectionPairing_eq_taylorPairing
#print axioms Gauge.DiagonalReflection.WilsonActionDecomposition.diagonalReflectionPositivity
#print axioms Gauge.DiagonalReflection.WilsonActionDecomposition.normSq_reflectionInnerProduct_le
#print axioms diagonalReflectionPositive_of_localExpectation_tendsto
#print axioms diagonalReflectionCauchySchwarz_of_localExpectation_tendsto
#print axioms centeredInfiniteVolume_diagonalReflectionPositive_of_eventually
#print axioms centeredInfiniteVolume_diagonalReflectionCauchySchwarz_all_planes
#print axioms centeredSpecification_one_diagonalSymmetric
#print axioms centeredInfiniteVolume_diagonalReflectionPositive
#print axioms centeredInfiniteVolume_diagonalReflectionCauchySchwarz

end

end YangMills.Tests.DiagonalReflection
