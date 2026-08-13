/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.SiteReflectionPositivity

/-! Executable regressions for Milestone 17: integer/site reflection positivity. -/

namespace YangMills.Tests

open MeasureTheory
open Gauge Lattice.Cubic
open Gauge.SiteReflection

noncomputable section

variable {d : ℕ} {G P O : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [CompactSpace G] [GaugeHaarProbability G]
  [Fintype P] [Fintype O]

example : MeasurePreserving
    (reflectedVariableEquiv (G := G) (P := P) (O := O))
    (ProductHaar.measure G (ReflectedLabel P O)) reflectedHaar :=
  measurePreserving_reflectedVariableEquiv

example (Φ : RealPlaquettePotential G)
    (evaluatePositive : C(HalfConfiguration G P O, Configuration d G))
    (evaluatePlane : C(PlaneConfiguration G O, Configuration d G))
    (positivePlaquettes planePlaquettes : Finset (Plaquette d))
    (β : ℝ) (F : PositiveObservable G P O) :
    let D := WilsonActionDecomposition.ofWilsonPlaquettes Φ evaluatePositive
      evaluatePlane positivePlaquettes planePlaquettes
    Complex.im (D.gibbsReflectionPairing β F F) = 0 ∧
      0 ≤ Complex.re (D.gibbsReflectionPairing β F F) :=
  WilsonActionDecomposition.siteReflectionPositivity_ofWilsonPlaquettes
    Φ evaluatePositive evaluatePlane positivePlaquettes planePlaquettes β F

example (D : WilsonActionDecomposition G P O) (β : ℝ)
    (F H : PositiveObservable G P O) :
    Complex.normSq (D.reflectionInnerProduct β F H) ≤
      Complex.re (D.reflectionInnerProduct β F F) *
        Complex.re (D.reflectionInnerProduct β H H) :=
  D.normSq_reflectionInnerProduct_le β F H

example (D : WilsonActionDecomposition G P O) (β : ℝ)
    (F H : PositiveObservable G P O) :
    ‖D.reflectionInnerProduct β F H‖ ≤
      Real.sqrt (Complex.re (D.reflectionInnerProduct β F F) *
        Complex.re (D.reflectionInnerProduct β H H)) :=
  D.norm_reflectionInnerProduct_le β F H

#print axioms YangMills.Lattice.Cubic.siteReflection_involutive
#print axioms YangMills.Gauge.holonomy_siteReflectConfiguration
#print axioms YangMills.Gauge.SiteReflection.measurePreserving_reflectedVariableEquiv
#print axioms YangMills.Gauge.SiteReflection.WilsonActionDecomposition.gibbsReflectionPairing_eq_factorized
#print axioms YangMills.Gauge.SiteReflection.WilsonActionDecomposition.siteReflectionPositivity
#print axioms YangMills.Gauge.SiteReflection.WilsonActionDecomposition.normSq_reflectionInnerProduct_le

end

end YangMills.Tests
