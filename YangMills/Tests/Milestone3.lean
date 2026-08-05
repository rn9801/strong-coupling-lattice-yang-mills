/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.Observable

/-!
# Milestone 3 executable regressions

These examples lock path-holonomy covariance, loop conjugation, finite support,
and the two gauge-invariance statements required by the milestone exit
criterion.
-/

namespace YangMills.Tests.Milestone3

open YangMills.Gauge
open YangMills.Lattice.Cubic

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

example (g : GaugeTransformation d G) (A : Configuration d G)
    {x y : Site d} (p : Lattice.Cubic.Path x y) :
    holonomy (gaugeTransform g A) p =
      g x * holonomy A p * (g y)⁻¹ :=
  holonomy_gaugeTransform g A p

example (g : GaugeTransformation d G) (A : Configuration d G)
    {x : Site d} (p : Lattice.Cubic.Path x x) :
    holonomy (gaugeTransform g A) p =
      g x * holonomy A p * (g x)⁻¹ :=
  holonomy_loop_gaugeTransform g A p

example (φ : ContinuousClassFunction G) (p : Plaquette d) :
    IsGaugeInvariant (LocalObservable.plaquetteClassFunction φ p) :=
  LocalObservable.plaquetteClassFunction_gaugeInvariant φ p

/-- Milestone 3 Wilson-loop exit criterion. -/
example (χ : ContinuousClassFunction G) {x : Site d} (C : Lattice.Cubic.Path x x) :
    IsGaugeInvariant (LocalObservable.wilsonLoop χ C) :=
  LocalObservable.wilsonLoop_gaugeInvariant χ C

example (χ : ContinuousClassFunction G) {x : Site d} (C : Lattice.Cubic.Path x x)
    {A B : Configuration d G}
    (h : ∀ e ∈ C.edgeSupport, A e = B e) :
    LocalObservable.wilsonLoop χ C A = LocalObservable.wilsonLoop χ C B :=
  (LocalObservable.wilsonLoop χ C).dependsOn_support h

#print axioms YangMills.Gauge.holonomy_gaugeTransform
#print axioms YangMills.Gauge.LocalObservable.plaquetteClassFunction_gaugeInvariant
#print axioms YangMills.Gauge.LocalObservable.wilsonLoop_gaugeInvariant

end YangMills.Tests.Milestone3
