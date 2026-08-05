/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Wilson.Representation

/-!
# Representation-labelled Wilson loops and center charge

Normalized characters label local Wilson-loop observables. This module proves
their pointwise unit bound, gauge invariance, orientation reversal, immediate
backtrack cancellation, and covariance under an explicitly supplied scalar
center phase.
-/

namespace YangMills.Wilson

open YangMills.Gauge YangMills.Lattice.Cubic

noncomputable section

namespace ContinuousUnitaryRepData

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The finite-volume Wilson action associated with the representation's real
normalized-character potential. -/
def wilsonAction (ρ : ContinuousUnitaryRepData G n)
    (Λ : FiniteSpecification d G) (U : DynamicConfiguration Λ) : ℝ :=
  FiniteVolume.action Λ ρ.wilsonPotential U

omit [IsTopologicalGroup G] in
/-- The Wilson action is invariant under boundary-compatible finite-volume
gauge transformations. -/
theorem wilsonAction_gaugeInvariant (ρ : ContinuousUnitaryRepData G n)
    (Λ : FiniteSpecification d G) (g : GaugeTransformation d G)
    (hg : Λ.BoundaryCompatible g) (U : DynamicConfiguration Λ) :
    ρ.wilsonAction Λ (Λ.gaugeTransformDynamic g U) = ρ.wilsonAction Λ U :=
  FiniteVolume.action_gaugeInvariant Λ ρ.wilsonPotential g hg U

/-- Representation-labelled normalized Wilson loop. -/
def wilsonLoop (ρ : ContinuousUnitaryRepData G n) {x : Site d}
    (C : Lattice.Cubic.Path x x) : LocalObservable d G :=
  LocalObservable.wilsonLoop ρ.normalizedCharacterClassFunction C

@[simp]
theorem wilsonLoop_apply (ρ : ContinuousUnitaryRepData G n) {x : Site d}
    (C : Lattice.Cubic.Path x x) (A : Configuration d G) :
    ρ.wilsonLoop C A = ρ.normalizedCharacter (holonomy A C) := by
  unfold wilsonLoop LocalObservable.wilsonLoop
  rw [LocalObservable.loopClassFunction_apply]
  rfl

@[simp]
theorem wilsonLoop_support (ρ : ContinuousUnitaryRepData G n) {x : Site d}
    (C : Lattice.Cubic.Path x x) :
    (ρ.wilsonLoop C).support = C.edgeSupport :=
  rfl

/-- Representation-labelled Wilson loops are gauge invariant. -/
theorem wilsonLoop_gaugeInvariant (ρ : ContinuousUnitaryRepData G n)
    {x : Site d} (C : Lattice.Cubic.Path x x) :
    IsGaugeInvariant (ρ.wilsonLoop C) :=
  LocalObservable.wilsonLoop_gaugeInvariant ρ.normalizedCharacterClassFunction C

/-- Every normalized Wilson loop has pointwise norm at most one. -/
theorem norm_wilsonLoop_le_one (ρ : ContinuousUnitaryRepData G n)
    {x : Site d} (C : Lattice.Cubic.Path x x) (A : Configuration d G) :
    ‖ρ.wilsonLoop C A‖ ≤ 1 := by
  rw [wilsonLoop_apply]
  exact ρ.norm_normalizedCharacter_le _

/-- Reversing a loop complex-conjugates its Wilson observable. -/
theorem wilsonLoop_reverse (ρ : ContinuousUnitaryRepData G n)
    {x : Site d} (C : Lattice.Cubic.Path x x) (A : Configuration d G) :
    ρ.wilsonLoop C.reverse A = star (ρ.wilsonLoop C A) := by
  simp only [wilsonLoop_apply, holonomy_reverse, normalizedCharacter_inv]

/-- Inserting an edge followed immediately by its reverse leaves a Wilson
loop unchanged. -/
theorem wilsonLoop_insert_reverse (ρ : ContinuousUnitaryRepData G n)
    {x y z : Site d} (p : Lattice.Cubic.Path x y) (e : EdgeBetween y z)
    (q : Lattice.Cubic.Path y x) (A : Configuration d G) :
    ρ.wilsonLoop (((p.cons e).cons (Quiver.reverse e)).comp q) A =
      ρ.wilsonLoop (p.comp q) A := by
  rw [wilsonLoop_apply, wilsonLoop_apply]
  apply congrArg ρ.normalizedCharacter
  simp only [holonomy_comp, holonomy_cons]
  rw [show signedEdgeValue A (Quiver.reverse e).1 = (signedEdgeValue A e.1)⁻¹ by
    exact signedEdgeValue_reverse A e.1]
  group

end ContinuousUnitaryRepData

/-- A chosen central element acting by a nontrivial scalar phase in a unitary
representation. This is the exact data needed for center-charge selection
arguments; it does not assume irreducibility or invoke Schur's lemma. -/
structure CenterChargeData {G : Type*} {n : ℕ} [Group G] [TopologicalSpace G]
    (ρ : ContinuousUnitaryRepData G n) where
  z : G
  central_z : ∀ g, z * g = g * z
  omega : ℂ
  norm_omega : ‖omega‖ = 1
  nontrivial : omega ≠ 1
  rho_z : (ρ.ρ z : Matrix (Fin n) (Fin n) ℂ) =
    omega • (1 : Matrix (Fin n) (Fin n) ℂ)

/-- Optional finite-order refinement of center-charge data. -/
structure FiniteCenterChargeData {G : Type*} {n : ℕ} [Group G]
    [TopologicalSpace G] (ρ : ContinuousUnitaryRepData G n)
    extends CenterChargeData ρ where
  order : ℕ
  two_le_order : 2 ≤ order
  omega_pow_order : toCenterChargeData.omega ^ order = 1

namespace CenterChargeData

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ρ : ContinuousUnitaryRepData G n}

omit [IsTopologicalGroup G] in
/-- The chosen center element acts on every represented group element by the
specified scalar phase. -/
theorem rho_center_mul (κ : CenterChargeData ρ) (g : G) :
    (ρ.ρ (κ.z * g) : Matrix (Fin n) (Fin n) ℂ) =
      κ.omega • (ρ.ρ g : Matrix (Fin n) (Fin n) ℂ) := by
  rw [map_mul, Matrix.UnitaryGroup.mul_val, κ.rho_z]
  simp

omit [IsTopologicalGroup G] in
/-- Character center-transformation law. -/
theorem character_center_mul (κ : CenterChargeData ρ) (g : G) :
    ρ.character (κ.z * g) = κ.omega * ρ.character g := by
  unfold ContinuousUnitaryRepData.character
  rw [κ.rho_center_mul]
  simp

omit [IsTopologicalGroup G] in
/-- Normalized-character center-transformation law. -/
theorem normalizedCharacter_center_mul (κ : CenterChargeData ρ) (g : G) :
    ρ.normalizedCharacter (κ.z * g) =
      κ.omega * ρ.normalizedCharacter g := by
  unfold ContinuousUnitaryRepData.normalizedCharacter
  rw [κ.character_center_mul]
  ring

omit [IsTopologicalGroup G] in
/-- The same center phase appears for multiplication on the right. -/
theorem normalizedCharacter_mul_center (κ : CenterChargeData ρ) (g : G) :
    ρ.normalizedCharacter (g * κ.z) =
      κ.omega * ρ.normalizedCharacter g := by
  rw [← κ.central_z g]
  exact κ.normalizedCharacter_center_mul g

/-- Wilson-loop center transformation expressed through a corresponding
change of loop holonomy. -/
theorem wilsonLoop_center_holonomy (κ : CenterChargeData ρ)
    {x : Site d} (C : Lattice.Cubic.Path x x) (A B : Configuration d G)
    (hhol : holonomy B C = κ.z * holonomy A C) :
    ρ.wilsonLoop C B = κ.omega * ρ.wilsonLoop C A := by
  simp only [ContinuousUnitaryRepData.wilsonLoop_apply, hhol,
    κ.normalizedCharacter_center_mul]

end CenterChargeData

end

end YangMills.Wilson
