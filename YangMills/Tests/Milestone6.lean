/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.FiniteGas

/-!
# Milestone 6 regression tests

The example below is a standalone one-polymer hard-core gas.  Its activity is
zero, so every nonempty family has zero weight and every restricted partition
function equals one.  In particular its finite KP deletion certificate is
checked directly, without importing any gauge-theory module.
-/

namespace YangMills.Tests.Milestone6

open YangMills.Polymer

noncomputable section

/-- A one-polymer model, deliberately defined using only the abstract layer. -/
def singletonGas : FinitePolymerModel (Fin 1) where
  incompatible γ δ := γ = δ
  decidableIncompatible := inferInstance
  symmetric_incompatible := fun _ _ h => h.symm
  self_incompatible := fun _ => rfl
  activity := fun _ => 0

@[simp]
theorem singletonGas_familyWeight (Γ : Finset (Fin 1)) :
    singletonGas.familyWeight Γ = if Γ = ∅ then 1 else 0 := by
  by_cases hΓ : Γ = ∅
  · simp [hΓ]
  · obtain ⟨γ, hγ⟩ := Finset.nonempty_iff_ne_empty.mpr hΓ
    have hcard : Γ.card ≠ 0 := Finset.card_ne_zero.mpr ⟨γ, hγ⟩
    simp [FinitePolymerModel.familyWeight, singletonGas, hΓ, hcard]

@[simp]
theorem singletonGas_partitionOn (S : Finset (Fin 1)) :
    singletonGas.partitionOn S = 1 := by
  classical
  rw [FinitePolymerModel.partitionOn]
  rw [Finset.sum_eq_single ∅]
  · simp [FinitePolymerModel.familyWeight]
  · intro Γ hΓ hΓne
    simp [singletonGas_familyWeight, hΓne]
  · intro hnot
    exfalso
    apply hnot
    simp only [FinitePolymerModel.compatibleFamilies, Finset.mem_filter,
      Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, by simp [FinitePolymerModel.Compatible]⟩

theorem singletonGas_finiteKP :
    singletonGas.FiniteKPCertificate Finset.univ := by
  intro T _ γ _
  change ‖(0 : ℂ) * singletonGas.partitionOn _‖ <
    ‖singletonGas.partitionOn (T.erase γ)‖
  rw [singletonGas_partitionOn]
  norm_num

/-- Standalone Milestone 6 exit theorem. -/
theorem singletonGas_partition_ne_zero :
    singletonGas.partitionFunction ≠ 0 :=
  singletonGas.partitionFunction_ne_zero_of_finiteKP singletonGas_finiteKP

#print axioms singletonGas_partition_ne_zero

end

end YangMills.Tests.Milestone6
