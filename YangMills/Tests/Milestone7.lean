/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.Cluster

/-! # Milestone 7 regression tests -/

namespace YangMills.Tests.Milestone7

open YangMills.Polymer
open YangMills.Polymer.FinitePolymerModel

noncomputable section

/-- An entire one-polymer family with identically zero activity. -/
def zeroAnalyticGas : AnalyticFamily (Fin 1) where
  incompatible γ δ := γ = δ
  decidableIncompatible := inferInstance
  symmetric_incompatible := fun _ _ h => h.symm
  self_incompatible := fun _ => rfl
  activity := fun _ _ => 0
  analytic_activity := fun _ => analyticOnNhd_const

theorem zeroAnalyticGas_dobrushinKP :
    zeroAnalyticGas.AnalyticDobrushinCertificate Finset.univ Set.univ
      (fun _ => 0) := by
  intro β _
  constructor
  · simp
  · intro γ _
    simp [zeroAnalyticGas, AnalyticFamily.model]

/-- The same analytic exit package follows from the genuinely local explicit
Dobrushin--KP inequality. -/
def zeroAnalyticGas_dobrushin_exit :=
  zeroAnalyticGas.analyticDobrushinKP Finset.univ Set.univ (fun _ => 0)
    zeroAnalyticGas_dobrushinKP

#print axioms FinitePolymerModel.ursell_eq_zero_of_not_connected
#print axioms FinitePolymerModel.norm_ursellGraph_le_tree_graphs
#print axioms zeroAnalyticGas_dobrushin_exit

end

end YangMills.Tests.Milestone7
