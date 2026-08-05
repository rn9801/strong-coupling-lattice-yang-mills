/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Finite abstract hard-core polymer gases

This module is deliberately independent of every Yang--Mills module. A model
has a finite polymer type, a symmetric reflexive incompatibility relation, and
complex activities. Partition functions are also defined on restricted finite
polymer sets, making deletion recursion and inductive zero-free certificates
available without changing the ambient type.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

/-- A finite hard-core polymer model. Incompatibility is symmetric and
reflexive; compatibility of a family only tests distinct members. -/
structure FinitePolymerModel (P : Type*) [Fintype P] where
  incompatible : P → P → Prop
  decidableIncompatible : DecidableRel incompatible
  symmetric_incompatible : Symmetric incompatible
  self_incompatible : ∀ γ, incompatible γ γ
  activity : P → ℂ

attribute [instance] FinitePolymerModel.decidableIncompatible

namespace FinitePolymerModel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- A family is compatible when no two distinct members are incompatible. -/
def Compatible (M : FinitePolymerModel P) (Γ : Finset P) : Prop :=
  (Γ : Set P).Pairwise fun γ δ => ¬M.incompatible γ δ

instance (M : FinitePolymerModel P) (Γ : Finset P) : Decidable (M.Compatible Γ) :=
  Classical.propDecidable _

/-- Product of activities in a polymer family. -/
def familyWeight (M : FinitePolymerModel P) (Γ : Finset P) : ℂ :=
  ∏ γ ∈ Γ, M.activity γ

/-- Compatible families drawn from a restricted finite polymer set. -/
def compatibleFamilies (M : FinitePolymerModel P) (S : Finset P) : Finset (Finset P) :=
  S.powerset.filter M.Compatible

/-- Restricted hard-core partition function. -/
def partitionOn (M : FinitePolymerModel P) (S : Finset P) : ℂ :=
  ∑ Γ ∈ M.compatibleFamilies S, M.familyWeight Γ

/-- The full finite polymer partition function. -/
def partitionFunction (M : FinitePolymerModel P) : ℂ :=
  M.partitionOn Finset.univ

/-- Polymers in `S` compatible with a proposed new polymer `γ`. -/
def compatibleWith (M : FinitePolymerModel P) (S : Finset P) (γ : P) : Finset P :=
  S.filter fun δ => ¬M.incompatible γ δ

omit [DecidableEq P] in
@[simp]
theorem compatibleFamilies_empty (M : FinitePolymerModel P) :
    M.compatibleFamilies ∅ = {∅} := by
  classical
  ext Γ
  simp only [compatibleFamilies, Finset.mem_filter, Finset.mem_powerset,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hΓ, _⟩
    exact Finset.Subset.antisymm hΓ (Finset.empty_subset Γ)
  · intro hΓ
    subst Γ
    refine ⟨Finset.empty_subset ∅, ?_⟩
    simp [Compatible]

omit [DecidableEq P] in
@[simp]
theorem familyWeight_empty (M : FinitePolymerModel P) : M.familyWeight ∅ = 1 := by
  simp [familyWeight]

omit [DecidableEq P] in
@[simp]
theorem partitionOn_empty (M : FinitePolymerModel P) : M.partitionOn ∅ = 1 := by
  classical
  simp [partitionOn]

theorem compatible_insert_iff (M : FinitePolymerModel P) {S : Finset P} {γ : P}
    (hγ : γ ∉ S) :
    M.Compatible (insert γ S) ↔
      M.Compatible S ∧ ∀ δ ∈ S, ¬M.incompatible γ δ := by
  have hsymm : Symmetric (fun a b => ¬M.incompatible a b) :=
    fun a b hab hba => hab (M.symmetric_incompatible hba)
  simpa only [Compatible, Finset.coe_insert] using
    (Set.pairwise_insert_of_symmetric_of_notMem hsymm hγ)

theorem familyWeight_insert (M : FinitePolymerModel P) {S : Finset P} {γ : P}
    (hγ : γ ∉ S) :
    M.familyWeight (insert γ S) = M.activity γ * M.familyWeight S := by
  simp [familyWeight, hγ]

/-- Deletion recursion for a restricted finite hard-core gas. -/
theorem partitionOn_delete (M : FinitePolymerModel P) (S : Finset P)
    {γ : P} (hγ : γ ∈ S) :
    M.partitionOn S = M.partitionOn (S.erase γ) +
      M.activity γ * M.partitionOn (M.compatibleWith (S.erase γ) γ) := by
  classical
  let R := S.erase γ
  have hγR : γ ∉ R := Finset.notMem_erase γ S
  have hS : S = insert γ R := (Finset.insert_erase hγ).symm
  rw [hS, Finset.erase_insert hγR]
  unfold partitionOn compatibleFamilies
  rw [Finset.powerset_insert]
  rw [Finset.filter_union]
  have hdisj : Disjoint
      (R.powerset.filter M.Compatible)
      ((R.powerset.image (insert γ)).filter M.Compatible) := by
    rw [Finset.disjoint_left]
    intro T hT hTi
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    rcases hT with ⟨hTR, _⟩
    simp only [Finset.mem_filter, Finset.mem_image] at hTi
    rcases hTi with ⟨⟨U, hUR, rfl⟩, _⟩
    exact hγR (hTR (Finset.mem_insert_self γ U))
  rw [Finset.sum_union hdisj]
  congr 1
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun T _ => insert γ T)
  · intro T hT
    rcases Finset.mem_filter.mp hT with ⟨hTpowerset, hcomp⟩
    have hTallowed := Finset.mem_powerset.mp hTpowerset
    have hTR : T ⊆ R := fun δ hδ => (Finset.mem_filter.mp (hTallowed hδ)).1
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨T, Finset.mem_powerset.mpr hTR, rfl⟩
    · exact (M.compatible_insert_iff (Finset.notMem_mono hTR hγR)).mpr
        ⟨hcomp, fun δ hδ => (Finset.mem_filter.mp (hTallowed hδ)).2⟩
  · intro T₁ h₁ T₂ h₂ heq
    have hT₁R : T₁ ⊆ R := fun δ hδ =>
      (Finset.mem_filter.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp h₁).1) hδ)).1
    have hT₂R : T₂ ⊆ R := fun δ hδ =>
      (Finset.mem_filter.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp h₂).1) hδ)).1
    have herase := congrArg (fun T : Finset P => T.erase γ) heq
    simpa [Finset.erase_insert, Finset.notMem_mono hT₁R hγR,
      Finset.notMem_mono hT₂R hγR] using herase
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_powerset] at hU
    rcases hU with ⟨⟨T, hTR, rfl⟩, hcomp⟩
    have hTcomp := (M.compatible_insert_iff (Finset.notMem_mono hTR hγR)).mp hcomp
    refine ⟨T, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, hTcomp.1⟩
    intro δ hδ
    exact Finset.mem_filter.mpr ⟨hTR hδ, hTcomp.2 δ hδ⟩
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    have hTR : T ⊆ R := fun δ hδ => (Finset.mem_filter.mp (hT.1 hδ)).1
    exact (M.familyWeight_insert (Finset.notMem_mono hTR hγR)).symm

/-- A finite zero-free certificate in deletion-ratio form. This formulation is
the induction-ready finite KP condition; later weighted estimates construct
it from explicit activity majorants. -/
def FiniteKPCertificate (M : FinitePolymerModel P) (S : Finset P) : Prop :=
  ∀ T ⊆ S, ∀ γ ∈ T,
    ‖M.activity γ * M.partitionOn (M.compatibleWith (T.erase γ) γ)‖ <
      ‖M.partitionOn (T.erase γ)‖

/-- A finite KP deletion certificate makes every restricted partition
function nonzero. -/
theorem partitionOn_ne_zero_of_finiteKP (M : FinitePolymerModel P) (S : Finset P)
    (hKP : M.FiniteKPCertificate S) : M.partitionOn S ≠ 0 := by
  classical
  by_cases hS : S = ∅
  · subst S
    simp
  · obtain ⟨γ, hγ⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    rw [M.partitionOn_delete S hγ]
    intro hzero
    have heq : M.partitionOn (S.erase γ) =
        -(M.activity γ * M.partitionOn (M.compatibleWith (S.erase γ) γ)) :=
      eq_neg_of_add_eq_zero_left hzero
    have hlt := hKP S Finset.Subset.rfl γ hγ
    rw [heq, norm_neg] at hlt
    exact lt_irrefl _ hlt

/-- Full-partition specialization of the finite KP nonvanishing theorem. -/
theorem partitionFunction_ne_zero_of_finiteKP (M : FinitePolymerModel P)
    (hKP : M.FiniteKPCertificate Finset.univ) :
    M.partitionFunction ≠ 0 :=
  M.partitionOn_ne_zero_of_finiteKP Finset.univ hKP

end FinitePolymerModel

end

end YangMills.Polymer
