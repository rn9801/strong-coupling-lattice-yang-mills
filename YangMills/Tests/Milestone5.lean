/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Wilson.Loop

/-!
# Milestone 5 executable regressions

These examples lock the unitary character bounds, normalized Wilson potential,
finite-volume action invariance, Wilson-loop geometry, and center-phase exit
criteria.
-/

namespace YangMills.Tests.Milestone5

open YangMills.Gauge YangMills.Lattice.Cubic YangMills.Wilson

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

example (ρ : ContinuousUnitaryRepData G n) (g : G) :
    ‖ρ.character g‖ ≤ n :=
  ρ.norm_character_le g

example (ρ : ContinuousUnitaryRepData G n) (g : G) :
    ‖ρ.normalizedCharacter g‖ ≤ 1 :=
  ρ.norm_normalizedCharacter_le g

example (ρ : ContinuousUnitaryRepData G n) (β : ℝ) (g : G) :
    |Real.exp (β * ρ.wilsonPotential g) - 1| ≤ Real.exp |β| - 1 :=
  ρ.abs_exp_mul_wilsonPotential_sub_one_le β g

example (ρ : ContinuousUnitaryRepData G n) (Λ : FiniteSpecification d G)
    (g : GaugeTransformation d G) (hg : Λ.BoundaryCompatible g)
    (U : DynamicConfiguration Λ) :
    ρ.wilsonAction Λ (Λ.gaugeTransformDynamic g U) = ρ.wilsonAction Λ U :=
  ρ.wilsonAction_gaugeInvariant Λ g hg U

/-- Milestone 5 unit-bound exit criterion. -/
example (ρ : ContinuousUnitaryRepData G n) {x : Site d}
    (C : Lattice.Cubic.Path x x) (A : Configuration d G) :
    ‖ρ.wilsonLoop C A‖ ≤ 1 :=
  ρ.norm_wilsonLoop_le_one C A

/-- Milestone 5 gauge-invariance exit criterion. -/
example (ρ : ContinuousUnitaryRepData G n) {x : Site d}
    (C : Lattice.Cubic.Path x x) :
    IsGaugeInvariant (ρ.wilsonLoop C) :=
  ρ.wilsonLoop_gaugeInvariant C

example (ρ : ContinuousUnitaryRepData G n) {x : Site d}
    (C : Lattice.Cubic.Path x x) (A : Configuration d G) :
    ρ.wilsonLoop C.reverse A = star (ρ.wilsonLoop C A) :=
  ρ.wilsonLoop_reverse C A

example (ρ : ContinuousUnitaryRepData G n) {x y z : Site d}
    (p : Lattice.Cubic.Path x y) (e : EdgeBetween y z)
    (q : Lattice.Cubic.Path y x) (A : Configuration d G) :
    ρ.wilsonLoop (((p.cons e).cons (Quiver.reverse e)).comp q) A =
      ρ.wilsonLoop (p.comp q) A :=
  ρ.wilsonLoop_insert_reverse p e q A

/-- Milestone 5 center-transformation exit criterion. -/
example (ρ : ContinuousUnitaryRepData G n) (κ : CenterChargeData ρ)
    {x : Site d} (C : Lattice.Cubic.Path x x) (A B : Configuration d G)
    (hhol : holonomy B C = κ.z * holonomy A C) :
    ρ.wilsonLoop C B = κ.omega * ρ.wilsonLoop C A :=
  κ.wilsonLoop_center_holonomy C A B hhol

#print axioms YangMills.Wilson.ContinuousUnitaryRepData.norm_character_le
#print axioms YangMills.Wilson.ContinuousUnitaryRepData.norm_wilsonLoop_le_one
#print axioms YangMills.Wilson.ContinuousUnitaryRepData.wilsonLoop_gaugeInvariant
#print axioms YangMills.Wilson.CenterChargeData.wilsonLoop_center_holonomy

end

end YangMills.Tests.Milestone5
