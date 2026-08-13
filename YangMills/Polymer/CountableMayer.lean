/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.MayerEvaluation
import Mathlib.Data.Finsupp.Encodable

/-!
# Mayer clusters over a countable ambient polymer type

Thermodynamic cluster expansions use one stable, countable polymer type even
though every individual Mayer cluster has finite support.  This file extends
the finite-species definitions without changing their normalization: graph
vertices are labelled occurrences over the finite support of the multi-index,
and all products and sums are `Finsupp` products and sums.

The comparison theorems at the end show that these definitions are exactly
the existing finite Mayer definitions when the ambient type is finite.  This
is the countable extension of the model-independent polymer layer.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

/-- An abstract hard-core polymer model whose ambient type need not be
finite.  Finiteness enters only through individual Mayer multi-indices. -/
structure CountablePolymerModel (P : Type*) where
  incompatible : P → P → Prop
  decidableIncompatible : DecidableRel incompatible
  symmetric_incompatible : Symmetric incompatible
  self_incompatible : ∀ γ, incompatible γ γ
  activity : P → ℂ

attribute [instance] CountablePolymerModel.decidableIncompatible

namespace CountablePolymerModel

variable {P : Type*} [DecidableEq P]

/-- A finite Mayer multi-index in a possibly infinite polymer species. -/
abbrev MayerMultiIndex (P : Type*) := P →₀ ℕ

/-- Labelled occurrences, restricted to the finite support of a Mayer
multi-index. -/
abbrev MayerVertex (X : MayerMultiIndex P) :=
  Σ γ : {p // p ∈ X.support}, Fin (X γ.1)

/-- Incompatibility graph on the finitely many labelled occurrences. -/
def mayerIncompatibilityGraph (M : CountablePolymerModel P)
    (X : MayerMultiIndex P) : SimpleGraph (MayerVertex X) where
  Adj i j := i ≠ j ∧ M.incompatible i.1.1 j.1.1
  symm _ _ h := ⟨h.1.symm, M.symmetric_incompatible h.2⟩
  loopless := ⟨fun i h ↦ h.1 rfl⟩

/-- Ursell coefficient of a finite multi-index in a countable species. -/
def mayerUrsell (M : CountablePolymerModel P) (X : MayerMultiIndex P) : ℤ :=
  connectedSpanningGraphSum (M.mayerIncompatibilityGraph X)

/-- Product of multiplicity factorials.  Zero multiplicities are omitted by
the `Finsupp` product. -/
def mayerSymmetryFactor (X : MayerMultiIndex P) : ℕ :=
  X.prod fun _ n ↦ n.factorial

/-- Activity monomial of a finite multi-index. -/
def mayerActivityMonomial (M : CountablePolymerModel P)
    (X : MayerMultiIndex P) : ℂ :=
  X.prod fun γ n ↦ M.activity γ ^ n

/-- Symmetry-normalized connected Mayer term. -/
def mayerClusterTerm (M : CountablePolymerModel P)
    (X : MayerMultiIndex P) : ℂ :=
  (M.mayerUrsell X : ℂ) / (mayerSymmetryFactor X : ℂ) *
    M.mayerActivityMonomial X

/-- Total number of labelled occurrences. -/
def mayerDegree (X : MayerMultiIndex P) : ℕ :=
  X.sum fun _ n ↦ n

/-- Total weighted size, counted with multiplicity. -/
def mayerMass (size : P → ℕ) (X : MayerMultiIndex P) : ℕ :=
  X.sum fun γ n ↦ n * size γ

/-- The finite union of all geometric carriers occurring in a cluster. -/
def mayerCarrier {A : Type*} [DecidableEq A] (carrier : P → Finset A)
    (X : MayerMultiIndex P) : Finset A :=
  X.support.biUnion carrier

@[simp]
theorem mem_mayerCarrier {A : Type*} [DecidableEq A]
    (carrier : P → Finset A) (X : MayerMultiIndex P) (x : A) :
    x ∈ mayerCarrier carrier X ↔ ∃ γ ∈ X.support, x ∈ carrier γ := by
  simp [mayerCarrier]

theorem mayerUrsell_eq_zero_of_not_connected
    (M : CountablePolymerModel P) (X : MayerMultiIndex P)
    (hX : ¬(M.mayerIncompatibilityGraph X).Connected) :
    M.mayerUrsell X = 0 :=
  connectedSpanningGraphSum_eq_zero_of_not_connected hX

@[simp]
theorem mayerClusterTerm_eq_zero_of_not_connected
    (M : CountablePolymerModel P) (X : MayerMultiIndex P)
    (hX : ¬(M.mayerIncompatibilityGraph X).Connected) :
    M.mayerClusterTerm X = 0 := by
  simp [mayerClusterTerm, M.mayerUrsell_eq_zero_of_not_connected X hX]

/-! ## Analytic activity families -/

/-- A countable polymer model with entire single-polymer activities. -/
structure AnalyticFamily (P : Type*) where
  incompatible : P → P → Prop
  decidableIncompatible : DecidableRel incompatible
  symmetric_incompatible : Symmetric incompatible
  self_incompatible : ∀ γ, incompatible γ γ
  activity : ℂ → P → ℂ
  analytic_activity : ∀ γ,
    AnalyticOnNhd ℂ (fun β ↦ activity β γ) Set.univ

attribute [instance] AnalyticFamily.decidableIncompatible

namespace AnalyticFamily

/-- Fixed-coupling model belonging to a countable analytic family. -/
def model (A : AnalyticFamily P) (β : ℂ) : CountablePolymerModel P where
  incompatible := A.incompatible
  decidableIncompatible := A.decidableIncompatible
  symmetric_incompatible := A.symmetric_incompatible
  self_incompatible := A.self_incompatible
  activity := A.activity β

/-- A fixed finite Mayer cluster term is entire even when the ambient
polymer species is countable. -/
theorem analyticOnNhd_mayerClusterTerm
    (A : AnalyticFamily P) (X : MayerMultiIndex P) :
    AnalyticOnNhd ℂ (fun β ↦ (A.model β).mayerClusterTerm X) Set.univ := by
  unfold CountablePolymerModel.mayerClusterTerm
  apply AnalyticOnNhd.mul
  · exact (analyticOnNhd_const : AnalyticOnNhd ℂ
      (fun _ : ℂ ↦ ((A.model 0).mayerUrsell X : ℂ) /
        (CountablePolymerModel.mayerSymmetryFactor X : ℂ)) Set.univ)
  · unfold CountablePolymerModel.mayerActivityMonomial
    apply Finset.analyticOnNhd_fun_prod X.support
    intro γ _
    exact (A.analytic_activity γ).pow (X γ)

end AnalyticFamily

/-! ## Finite restrictions -/

/-- Restrict a countable model to a finite set of polymer species. -/
def restrict (M : CountablePolymerModel P) (S : Finset P) :
    FinitePolymerModel S where
  incompatible γ δ := M.incompatible γ.1 δ.1
  decidableIncompatible := fun γ δ ↦ M.decidableIncompatible γ.1 δ.1
  symmetric_incompatible _ _ h := M.symmetric_incompatible h
  self_incompatible γ := M.self_incompatible γ.1
  activity γ := M.activity γ.1

/-- Extend a finite-restriction multi-index by zero. -/
def extendMultiIndex (S : Finset P)
    (Y : FinitePolymerModel.MayerMultiIndex S) : MayerMultiIndex P :=
  Finsupp.mapDomain Subtype.val Y

@[simp]
theorem extendMultiIndex_apply_mem (S : Finset P)
    (Y : FinitePolymerModel.MayerMultiIndex S) (p : S) :
    extendMultiIndex S Y p.1 = Y p :=
  Finsupp.mapDomain_apply Subtype.val_injective Y p

theorem support_extendMultiIndex_subset (S : Finset P)
    (Y : FinitePolymerModel.MayerMultiIndex S) :
    (extendMultiIndex S Y).support ⊆ S := by
  intro p hp
  have hp' := Finsupp.mapDomain_support (f := Subtype.val) (s := Y) hp
  rcases Finset.mem_image.mp hp' with ⟨q, _hq, rfl⟩
  exact q.2

/-- Restrict a global multi-index to a finite species set. -/
def restrictMultiIndex (S : Finset P) (X : MayerMultiIndex P) :
    FinitePolymerModel.MayerMultiIndex S :=
  Finsupp.subtypeDomain (fun p ↦ p ∈ S) X

@[simp]
theorem restrictMultiIndex_apply (S : Finset P) (X : MayerMultiIndex P)
    (p : S) : restrictMultiIndex S X p = X p.1 := rfl

theorem extend_restrictMultiIndex (S : Finset P) (X : MayerMultiIndex P)
    (hX : X.support ⊆ S) :
    extendMultiIndex S (restrictMultiIndex S X) = X := by
  ext p
  by_cases hp : p ∈ S
  · let q : S := ⟨p, hp⟩
    simpa [q] using extendMultiIndex_apply_mem S (restrictMultiIndex S X) q
  · have hzero : X p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      exact fun hps ↦ hp (hX hps)
    have hnot : p ∉ (extendMultiIndex S (restrictMultiIndex S X)).support :=
      fun h ↦ hp (support_extendMultiIndex_subset S _ h)
    rw [Finsupp.notMem_support_iff.mp hnot, hzero]

@[simp]
theorem restrict_extendMultiIndex (S : Finset P)
    (Y : FinitePolymerModel.MayerMultiIndex S) :
    restrictMultiIndex S (extendMultiIndex S Y) = Y := by
  ext p
  exact extendMultiIndex_apply_mem S Y p

/-- Finite-restriction multi-indices are canonically the global
multi-indices whose support lies in the restricting species set. -/
def multiIndexRestrictionEquiv (S : Finset P) :
    FinitePolymerModel.MayerMultiIndex S ≃
      {X : MayerMultiIndex P // X.support ⊆ S} where
  toFun Y := ⟨extendMultiIndex S Y, support_extendMultiIndex_subset S Y⟩
  invFun X := restrictMultiIndex S X.1
  left_inv Y := restrict_extendMultiIndex S Y
  right_inv X := Subtype.ext (extend_restrictMultiIndex S X.1 X.2)

theorem restrictMultiIndex_injectiveOn (S : Finset P) :
    Set.InjOn (restrictMultiIndex S)
      {X : MayerMultiIndex P | X.support ⊆ S} := by
  intro X hX Y hY h
  rw [← extend_restrictMultiIndex S X hX,
    ← extend_restrictMultiIndex S Y hY, h]

theorem support_extendMultiIndex (S : Finset P)
    (Y : FinitePolymerModel.MayerMultiIndex S) :
    (extendMultiIndex S Y).support =
      Y.support.map ⟨Subtype.val, Subtype.val_injective⟩ := by
  rw [show extendMultiIndex S Y = Finsupp.mapDomain Subtype.val Y from rfl]
  ext p
  rw [Finsupp.mem_support_iff]
  constructor
  · intro hp
    by_contra hnot
    have hzero := Finsupp.mapDomain_of_not_mem_image_support
      (f := Subtype.val) (x := Y) (b := p) (by
        intro himage
        rcases himage with ⟨q, hq, rfl⟩
        exact hnot (Finset.mem_map.mpr ⟨q, hq, rfl⟩))
    exact hp hzero
  · intro hp
    rcases Finset.mem_map.mp hp with ⟨q, hq, rfl⟩
    simpa only [Function.Embedding.coeFn_mk] using
      (show Finsupp.mapDomain Subtype.val Y q.1 ≠ 0 by
        rw [Finsupp.mapDomain_apply Subtype.val_injective]
        exact Finsupp.mem_support_iff.mp hq)

/-- Occurrence vertices are unchanged by extension from a finite
restriction. -/
def mayerVertexExtendEquiv (S : Finset P)
    (Y : FinitePolymerModel.MayerMultiIndex S) :
    MayerVertex (extendMultiIndex S Y) ≃ FinitePolymerModel.MayerVertex Y where
  toFun i := by
    let q : S := ⟨i.1.1, support_extendMultiIndex_subset S Y i.1.2⟩
    exact ⟨q, Fin.cast (extendMultiIndex_apply_mem S Y q) i.2⟩
  invFun i := by
    let p : {p // p ∈ (extendMultiIndex S Y).support} :=
      ⟨i.1.1, by
        rw [support_extendMultiIndex]
        exact Finset.mem_map.mpr ⟨i.1,
          Finsupp.mem_support_iff.mpr (Nat.ne_of_gt
            (lt_of_le_of_lt (Nat.zero_le i.2) i.2.isLt)), rfl⟩⟩
    exact ⟨p, Fin.cast (extendMultiIndex_apply_mem S Y i.1).symm i.2⟩
  left_inv i := by
    cases i with
    | mk i n => cases i; apply Sigma.ext rfl; simp
  right_inv i := by
    cases i with
    | mk i n => apply Sigma.ext rfl; simp

/-- Restriction and extension give isomorphic incompatibility graphs. -/
def mayerIncompatibilityGraphRestrictIso (M : CountablePolymerModel P)
    (S : Finset P) (Y : FinitePolymerModel.MayerMultiIndex S) :
    (M.mayerIncompatibilityGraph (extendMultiIndex S Y)) ≃g
      ((M.restrict S).mayerIncompatibilityGraph Y) where
  toEquiv := mayerVertexExtendEquiv S Y
  map_rel_iff' := by
    intro a b
    change ((mayerVertexExtendEquiv S Y) a ≠ (mayerVertexExtendEquiv S Y) b ∧
        M.incompatible a.1.1 b.1.1) ↔
      (a ≠ b ∧ M.incompatible a.1.1 b.1.1)
    rw [(mayerVertexExtendEquiv S Y).injective.ne_iff]

theorem mayerUrsell_extendMultiIndex (M : CountablePolymerModel P)
    (S : Finset P) (Y : FinitePolymerModel.MayerMultiIndex S) :
    M.mayerUrsell (extendMultiIndex S Y) =
      (M.restrict S).mayerUrsell Y := by
  exact connectedSpanningGraphSum_eq_of_iso
    (mayerIncompatibilityGraphRestrictIso M S Y)

theorem mayerSymmetryFactor_extendMultiIndex (S : Finset P)
    (Y : FinitePolymerModel.MayerMultiIndex S) :
    mayerSymmetryFactor (extendMultiIndex S Y) =
      FinitePolymerModel.mayerSymmetryFactor Y := by
  rw [mayerSymmetryFactor, FinitePolymerModel.mayerSymmetryFactor,
    show extendMultiIndex S Y = Finsupp.mapDomain Subtype.val Y from rfl,
    Finsupp.prod_mapDomain_index_inj Subtype.val_injective,
    Finsupp.prod_fintype Y (fun _ n ↦ n.factorial)]
  intro p
  simp

theorem mayerActivityMonomial_extendMultiIndex (M : CountablePolymerModel P)
    (S : Finset P) (Y : FinitePolymerModel.MayerMultiIndex S) :
    M.mayerActivityMonomial (extendMultiIndex S Y) =
      (M.restrict S).mayerActivityMonomial Y := by
  rw [mayerActivityMonomial, FinitePolymerModel.mayerActivityMonomial,
    show extendMultiIndex S Y = Finsupp.mapDomain Subtype.val Y from rfl,
    Finsupp.prod_mapDomain_index_inj Subtype.val_injective,
    Finsupp.prod_fintype Y (fun γ n ↦ M.activity γ.1 ^ n) (by simp)]
  rfl

theorem mayerClusterTerm_extendMultiIndex (M : CountablePolymerModel P)
    (S : Finset P) (Y : FinitePolymerModel.MayerMultiIndex S) :
    M.mayerClusterTerm (extendMultiIndex S Y) =
      (M.restrict S).mayerClusterTerm Y := by
  rw [mayerClusterTerm, FinitePolymerModel.mayerClusterTerm,
    mayerUrsell_extendMultiIndex, mayerSymmetryFactor_extendMultiIndex,
    mayerActivityMonomial_extendMultiIndex]

/-! ## Uniform finite-restriction KP certificates -/

/-- A KP certificate on every finite restriction of a countable polymer
model, with one ambient weight function.  This is the finitary formulation
suited to thermodynamic cluster expansions: every finite partial sum lives in
one of these restrictions. -/
def FiniteRestrictionKPCertificate (M : CountablePolymerModel P)
    (a : P → ℝ) : Prop :=
  ∀ S : Finset P,
    (M.restrict S).KoteckyPreissCertificate Finset.univ (fun γ : S ↦ a γ.1)

/-- Absolute Mayer term with one occurrence of `root` distinguished. -/
def pinnedNormMayerTerm (M : CountablePolymerModel P) (root : P)
    (X : MayerMultiIndex P) : ℝ :=
  (X root : ℝ) * ‖M.mayerClusterTerm X‖

@[simp]
theorem pinnedNormMayerTerm_nonneg (M : CountablePolymerModel P)
    (root : P) (X : MayerMultiIndex P) :
    0 ≤ M.pinnedNormMayerTerm root X :=
  mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)

theorem pinnedNormMayerTerm_extendMultiIndex
    (M : CountablePolymerModel P) (S : Finset P)
    (root : S) (Y : FinitePolymerModel.MayerMultiIndex S) :
    M.pinnedNormMayerTerm root.1 (extendMultiIndex S Y) =
      (Y root : ℝ) * ‖(M.restrict S).mayerClusterTerm Y‖ := by
  rw [pinnedNormMayerTerm, extendMultiIndex_apply_mem,
    mayerClusterTerm_extendMultiIndex]

theorem pinnedNormMayerTerm_restrictMultiIndex
    (M : CountablePolymerModel P) (S : Finset P) (root : S)
    (X : MayerMultiIndex P) (hX : X.support ⊆ S) :
    M.pinnedNormMayerTerm root.1 X =
      (restrictMultiIndex S X root : ℝ) *
        ‖(M.restrict S).mayerClusterTerm (restrictMultiIndex S X)‖ := by
  calc
    M.pinnedNormMayerTerm root.1 X =
        M.pinnedNormMayerTerm root.1
          (extendMultiIndex S (restrictMultiIndex S X)) := by
      rw [extend_restrictMultiIndex S X hX]
    _ = (restrictMultiIndex S X root : ℝ) *
        ‖(M.restrict S).mayerClusterTerm (restrictMultiIndex S X)‖ :=
      pinnedNormMayerTerm_extendMultiIndex M S root _

/-- Uniform KP on finite restrictions bounds every finite partial sum of the
countable multiplicity-pinned Mayer series. -/
theorem sum_pinnedNormMayerTerm_le_of_finiteRestrictionKP
    (M : CountablePolymerModel P) (a : P → ℝ)
    (hKP : M.FiniteRestrictionKPCertificate a) (root : P)
    (U : Finset (MayerMultiIndex P)) :
    ∑ X ∈ U, M.pinnedNormMayerTerm root X ≤
      ‖M.activity root‖ * Real.exp (a root) := by
  let S : Finset P := insert root (U.biUnion fun X ↦ X.support)
  have hroot : root ∈ S := Finset.mem_insert_self root _
  let rootS : S := ⟨root, hroot⟩
  have hsupport : ∀ X ∈ U, X.support ⊆ S := by
    intro X hX p hp
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨X, hX, hp⟩)
  have hinj : Set.InjOn (restrictMultiIndex S) (U : Set (MayerMultiIndex P)) := by
    intro X hX Y hY hXY
    exact restrictMultiIndex_injectiveOn S
      (hsupport X hX) (hsupport Y hY) hXY
  let V : Finset (FinitePolymerModel.MayerMultiIndex S) :=
    U.image (restrictMultiIndex S)
  have hsum :
      ∑ X ∈ U, M.pinnedNormMayerTerm root X =
        ∑ Y ∈ V, (Y rootS : ℝ) *
          ‖(M.restrict S).mayerClusterTerm Y‖ := by
    calc
      ∑ X ∈ U, M.pinnedNormMayerTerm root X =
          ∑ X ∈ U, ((restrictMultiIndex S X rootS : ℕ) : ℝ) *
            ‖(M.restrict S).mayerClusterTerm (restrictMultiIndex S X)‖ := by
        apply Finset.sum_congr rfl
        intro X hX
        exact M.pinnedNormMayerTerm_restrictMultiIndex S rootS X
          (hsupport X hX)
      _ = ∑ Y ∈ V, (Y rootS : ℝ) *
          ‖(M.restrict S).mayerClusterTerm Y‖ := by
        exact (Finset.sum_image
          (f := fun Y : FinitePolymerModel.MayerMultiIndex S ↦
            (Y rootS : ℝ) * ‖(M.restrict S).mayerClusterTerm Y‖)
          hinj).symm
  rw [hsum]
  simpa [FiniteRestrictionKPCertificate, rootS] using
    (M.restrict S).sum_pinnedNormMayerTerm_le_of_koteckyPreiss_certified
      (fun γ : S ↦ a γ.1) (hKP S) rootS V

/-- Genuine absolute summability of the countable multiplicity-pinned Mayer
series.  No enumeration of the ambient species is used: summability follows
from uniform control of all finite partial sums. -/
theorem summable_pinnedNormMayerTerm_of_finiteRestrictionKP
    (M : CountablePolymerModel P) (a : P → ℝ)
    (hKP : M.FiniteRestrictionKPCertificate a) (root : P) :
    Summable (M.pinnedNormMayerTerm root) := by
  apply summable_of_sum_le (M.pinnedNormMayerTerm_nonneg root)
  intro U
  exact M.sum_pinnedNormMayerTerm_le_of_finiteRestrictionKP a hKP root U

/-- Quantitative countable pinned Mayer bound inherited verbatim from the
finite certified KP/tree expansion. -/
theorem tsum_pinnedNormMayerTerm_le_of_finiteRestrictionKP
    (M : CountablePolymerModel P) (a : P → ℝ)
    (hKP : M.FiniteRestrictionKPCertificate a) (root : P) :
    ∑' X, M.pinnedNormMayerTerm root X ≤
      ‖M.activity root‖ * Real.exp (a root) := by
  apply Real.tsum_le_of_sum_le (M.pinnedNormMayerTerm_nonneg root)
  intro U
  exact M.sum_pinnedNormMayerTerm_le_of_finiteRestrictionKP a hKP root U

/-- The tilted single-polymer mass incompatible with a fixed root. -/
def incompatibleTiltedActivity (M : CountablePolymerModel P) (a : P → ℝ)
    (root γ : P) : ℝ :=
  if M.incompatible root γ then ‖M.activity γ‖ * Real.exp (a γ) else 0

@[simp]
theorem incompatibleTiltedActivity_nonneg
    (M : CountablePolymerModel P) (a : P → ℝ) (root γ : P) :
    0 ≤ M.incompatibleTiltedActivity a root γ := by
  unfold incompatibleTiltedActivity
  split_ifs
  · exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  · exact le_rfl

/-- Uniform finite-restriction KP controls every finite partial sum of the
incompatible tilted activity in the countable species. -/
theorem sum_incompatibleTiltedActivity_le_of_finiteRestrictionKP
    (M : CountablePolymerModel P) (a : P → ℝ)
    (hKP : M.FiniteRestrictionKPCertificate a) (root : P)
    (U : Finset P) :
    ∑ γ ∈ U, M.incompatibleTiltedActivity a root γ ≤ a root := by
  let S : Finset P := insert root U
  let rootS : S := ⟨root, Finset.mem_insert_self root U⟩
  have hsub : U ⊆ S := Finset.subset_insert root U
  let V : Finset S := U.attach.map
    ⟨fun γ : U ↦ ⟨γ.1, hsub γ.2⟩, fun x y h ↦ by
      apply Subtype.ext
      exact congrArg (fun z : S ↦ z.1) h⟩
  calc
    ∑ γ ∈ U, M.incompatibleTiltedActivity a root γ =
        ∑ δ ∈ V, if (M.restrict S).incompatible rootS δ then
          ‖(M.restrict S).activity δ‖ * Real.exp (a δ.1) else 0 := by
      rw [← Finset.sum_attach]
      exact (Finset.sum_map (s := U.attach)
        (f := fun δ : S ↦ if (M.restrict S).incompatible rootS δ then
          ‖(M.restrict S).activity δ‖ * Real.exp (a δ.1) else 0)
        ⟨fun γ : U ↦ ⟨γ.1, hsub γ.2⟩,
          fun x y h ↦ by
            apply Subtype.ext
            exact congrArg (fun z : S ↦ z.1) h⟩).symm
    _ ≤ ∑ δ : S, if (M.restrict S).incompatible rootS δ then
          ‖(M.restrict S).activity δ‖ * Real.exp (a δ.1) else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ V)
      intro δ _ _
      split_ifs
      · exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      · exact le_rfl
    _ = ∑ δ ∈ (Finset.univ : Finset S).filter
          ((M.restrict S).incompatible rootS),
          ‖(M.restrict S).activity δ‖ * Real.exp (a δ.1) := by
      rw [Finset.sum_filter]
    _ ≤ a root := (hKP S).2 rootS (Finset.mem_univ _)

/-- Genuine summability of the incompatible tilted activity mass. -/
theorem summable_incompatibleTiltedActivity_of_finiteRestrictionKP
    (M : CountablePolymerModel P) (a : P → ℝ)
    (hKP : M.FiniteRestrictionKPCertificate a) (root : P) :
    Summable (M.incompatibleTiltedActivity a root) := by
  apply summable_of_sum_le (M.incompatibleTiltedActivity_nonneg a root)
  intro U
  exact M.sum_incompatibleTiltedActivity_le_of_finiteRestrictionKP a hKP root U

theorem tsum_incompatibleTiltedActivity_le_of_finiteRestrictionKP
    (M : CountablePolymerModel P) (a : P → ℝ)
    (hKP : M.FiniteRestrictionKPCertificate a) (root : P) :
    ∑' γ, M.incompatibleTiltedActivity a root γ ≤ a root := by
  apply Real.tsum_le_of_sum_le (M.incompatibleTiltedActivity_nonneg a root)
  intro U
  exact M.sum_incompatibleTiltedActivity_le_of_finiteRestrictionKP a hKP root U

/-! ## Exact finite-restriction Mayer sums -/

/-- The symmetric Mayer logarithm of a finite restriction is exactly the
ambient absolutely convergent multi-index series cut off to that restriction.
This is the bridge from the finite labelled exponential formula to stable
thermodynamic cluster coefficients. -/
theorem symmetricMayerSum_restrict_eq_tsum
    (M : CountablePolymerModel P) (S : Finset P)
    (a : P → ℝ) (hKP : M.FiniteRestrictionKPCertificate a) :
    (M.restrict S).symmetricMayerSum =
      ∑' X : MayerMultiIndex P,
        if X.support ⊆ S then M.mayerClusterTerm X else 0 := by
  rw [FinitePolymerModel.symmetricMayerSum_eq_tsum_mayerClusterTerm_of_koteckyPreiss
    (M.restrict S) (fun γ : S ↦ a γ.1) (hKP S)]
  calc
    (∑' Y : FinitePolymerModel.MayerMultiIndex S,
        (M.restrict S).mayerClusterTerm Y) =
        ∑' Y : FinitePolymerModel.MayerMultiIndex S,
          M.mayerClusterTerm (extendMultiIndex S Y) := by
      apply tsum_congr
      intro Y
      exact (mayerClusterTerm_extendMultiIndex M S Y).symm
    _ = ∑' X : {X : MayerMultiIndex P // X.support ⊆ S},
        M.mayerClusterTerm X.1 :=
      (multiIndexRestrictionEquiv S).tsum_eq
        (fun X : {X : MayerMultiIndex P // X.support ⊆ S} ↦
          M.mayerClusterTerm X.1)
    _ = ∑' X : MayerMultiIndex P,
        if X.support ⊆ S then M.mayerClusterTerm X else 0 := by
      rw [show (∑' X : {X : MayerMultiIndex P // X.support ⊆ S},
          M.mayerClusterTerm X.1) =
          ∑' X : MayerMultiIndex P,
            Set.indicator {X | X.support ⊆ S} M.mayerClusterTerm X from
        tsum_subtype {X : MayerMultiIndex P | X.support ⊆ S}
          M.mayerClusterTerm]
      apply tsum_congr
      intro X
      by_cases hX : X.support ⊆ S <;> simp [Set.indicator, hX]

/-! ## Exact comparison with the finite-species definitions -/

variable [Fintype P]

/-- Forget only that the ambient polymer type is finite. -/
def ofFinite (M : FinitePolymerModel P) : CountablePolymerModel P where
  incompatible := M.incompatible
  decidableIncompatible := M.decidableIncompatible
  symmetric_incompatible := M.symmetric_incompatible
  self_incompatible := M.self_incompatible
  activity := M.activity

/-- Relabel the support-restricted occurrence type by the existing finite
ambient occurrence type. -/
def mayerVertexEquiv (X : MayerMultiIndex P) :
    MayerVertex X ≃ FinitePolymerModel.MayerVertex X where
  toFun i := ⟨i.1.1, i.2⟩
  invFun i := ⟨⟨i.1, Finsupp.mem_support_iff.mpr (Nat.ne_of_gt
    (lt_of_le_of_lt (Nat.zero_le i.2) i.2.isLt))⟩, i.2⟩
  left_inv i := by cases i with | mk i n => cases i; rfl
  right_inv i := by cases i; rfl

/-- The support-restricted and finite-ambient incompatibility graphs are
isomorphic. -/
def mayerIncompatibilityGraphIso (M : FinitePolymerModel P)
    (X : MayerMultiIndex P) :
    ((ofFinite M).mayerIncompatibilityGraph X) ≃g
      (M.mayerIncompatibilityGraph X) where
  toEquiv := mayerVertexEquiv X
  map_rel_iff' := by
    intro a b
    change ((mayerVertexEquiv X) a ≠ (mayerVertexEquiv X) b ∧
        M.incompatible a.1.1 b.1.1) ↔
      (a ≠ b ∧ M.incompatible a.1.1 b.1.1)
    rw [(mayerVertexEquiv X).injective.ne_iff]

theorem mayerUrsell_ofFinite (M : FinitePolymerModel P)
    (X : MayerMultiIndex P) :
    (ofFinite M).mayerUrsell X = M.mayerUrsell X := by
  exact connectedSpanningGraphSum_eq_of_iso
    (mayerIncompatibilityGraphIso M X)

theorem mayerSymmetryFactor_eq_finite (X : MayerMultiIndex P) :
    mayerSymmetryFactor X = FinitePolymerModel.mayerSymmetryFactor X := by
  rw [mayerSymmetryFactor, FinitePolymerModel.mayerSymmetryFactor,
    Finsupp.prod_fintype X (fun _ n ↦ n.factorial)]
  intro γ
  simp

theorem mayerActivityMonomial_ofFinite (M : FinitePolymerModel P)
    (X : MayerMultiIndex P) :
    (ofFinite M).mayerActivityMonomial X = M.mayerActivityMonomial X := by
  rw [mayerActivityMonomial, FinitePolymerModel.mayerActivityMonomial,
    show (ofFinite M).activity = M.activity from rfl,
    Finsupp.prod_fintype X (fun γ n ↦ M.activity γ ^ n)]
  intro γ
  simp

theorem mayerClusterTerm_ofFinite (M : FinitePolymerModel P)
    (X : MayerMultiIndex P) :
    (ofFinite M).mayerClusterTerm X = M.mayerClusterTerm X := by
  rw [mayerClusterTerm, FinitePolymerModel.mayerClusterTerm,
    mayerUrsell_ofFinite, mayerSymmetryFactor_eq_finite,
    mayerActivityMonomial_ofFinite]

theorem mayerDegree_eq_finite (X : MayerMultiIndex P) :
    mayerDegree X = FinitePolymerModel.mayerDegree X := by
  rw [mayerDegree, FinitePolymerModel.mayerDegree,
    Finsupp.sum_fintype X (fun _ n ↦ n)]
  intro γ
  rfl

end CountablePolymerModel

end

end YangMills.Polymer
