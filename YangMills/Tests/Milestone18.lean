/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.LinkReflectionPositivity

/-!
# Milestone 18 regression: half-integer reflection positivity

This file checks the public statement shape, the gauge-invariant positive
algebra, the exact Taylor/Fubini Gram identity, positivity, and both
unnormalized and normalized Cauchy--Schwarz inequalities.
-/

open MeasureTheory
open YangMills.Gauge
open YangMills.Gauge.LinkReflection
open YangMills.Gauge.LinkReflection.WilsonActionDecomposition

namespace YangMills.Tests.Milestone18

noncomputable section

variable {G C P Q : Type*} [Group G] [TopologicalSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [IsTopologicalGroup G] [CompactSpace G] [GaugeHaarProbability G]
  [Fintype C] [Fintype P] [Fintype Q]
  {n : ℕ}

variable (D : WilsonActionDecomposition G n C P Q)

/-- Gauge invariance is preserved by a nontrivial linear combination, so the
positive domain really is a complex subspace. -/
example (F H : PositiveObservable G C P)
    (hF : D.IsGaugeInvariant F) (hH : D.IsGaugeInvariant H) (c : ℂ) :
    D.IsGaugeInvariant (c • F + H) :=
  IsGaugeInvariant.add D (IsGaugeInvariant.smul D c hF) hH

/-- The degree-zero cross-plane word contributes no matrix coefficient. -/
example (U : SideConfiguration G P) :
    D.crossMonomial (m := 0) (fun i ↦ Fin.elim0 i) U = 1 := by
  simp [WilsonActionDecomposition.crossMonomial]

/-- The exact Taylor/Fubini expansion is part of the public theorem surface. -/
example (β : ℝ) (F H : PositiveObservable G C P) :
    D.gaugeFixedPairing β F H = D.taylorPairing β F H :=
  D.gaugeFixedPairing_eq_taylorPairing β F H

/-- Half-integer positivity requires gauge invariance, unlike site
reflection positivity. -/
example {β : ℝ} (hβ : 0 ≤ β) (F : PositiveObservable G C P)
    (hF : D.IsGaugeInvariant F) :
    Complex.im (D.gibbsReflectionPairing β F F) = 0 ∧
      0 ≤ Complex.re (D.gibbsReflectionPairing β F F) :=
  D.linkReflectionPositivity hβ F hF

/-- The unnormalized reflection form obeys Cauchy--Schwarz. -/
example {β : ℝ} (hβ : 0 ≤ β) (F H : PositiveObservable G C P)
    (hF : D.IsGaugeInvariant F) (hH : D.IsGaugeInvariant H) :
    Complex.normSq (D.gibbsReflectionPairing β F H) ≤
      Complex.re (D.gibbsReflectionPairing β F F) *
        Complex.re (D.gibbsReflectionPairing β H H) :=
  D.normSq_gibbsReflectionPairing_le hβ F H hF hH

/-- The normalized reflection inner product obeys the same inequality. -/
example {β : ℝ} (hβ : 0 ≤ β) (F H : PositiveObservable G C P)
    (hF : D.IsGaugeInvariant F) (hH : D.IsGaugeInvariant H) :
    Complex.normSq (D.reflectionInnerProduct β F H) ≤
      Complex.re (D.reflectionInnerProduct β F F) *
        Complex.re (D.reflectionInnerProduct β H H) :=
  D.normSq_reflectionInnerProduct_le hβ F H hF hH

#print axioms Gauge.LinkReflection.WilsonActionDecomposition.sum_wilsonPotential_eq_crossKernel
#print axioms Gauge.LinkReflection.WilsonActionDecomposition.gaugeFixedPairing_eq_taylorPairing
#print axioms Gauge.LinkReflection.WilsonActionDecomposition.linkReflectionPositivity
#print axioms Gauge.LinkReflection.WilsonActionDecomposition.normSq_gibbsReflectionPairing_le
#print axioms Gauge.LinkReflection.WilsonActionDecomposition.normSq_reflectionInnerProduct_le

end

end YangMills.Tests.Milestone18
