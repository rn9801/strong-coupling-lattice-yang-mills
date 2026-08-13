/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.CountableMayer

/-!
# Relabeling finite polymer gases

An equivalence of polymer species preserving incompatibility and activity
preserves the hard-core partition function.  This small generic adapter keeps
finite-region geometry out of the abstract Mayer layer.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

namespace FinitePolymerModel

variable {P Q : Type*} [Fintype P] [DecidableEq P]
  [Fintype Q] [DecidableEq Q]

omit [DecidableEq P] [DecidableEq Q] in
theorem compatible_finsetCongr_iff
    (M : FinitePolymerModel P) (N : FinitePolymerModel Q)
    (e : P ≃ Q)
    (hinc : ∀ p q, N.incompatible (e p) (e q) ↔ M.incompatible p q)
    (S : Finset P) :
    N.Compatible (e.finsetCongr S) ↔ M.Compatible S := by
  constructor
  · intro h p hp q hq hpq hMpq
    have hep : e p ∈ e.finsetCongr S := by simpa using hp
    have heq : e q ∈ e.finsetCongr S := by simpa using hq
    exact h hep heq (e.injective.ne hpq) ((hinc p q).mpr hMpq)
  · intro h p hp q hq hpq hNpq
    have hp' : e.symm p ∈ S := by simpa using hp
    have hq' : e.symm q ∈ S := by simpa using hq
    apply h hp' hq' (e.symm.injective.ne hpq)
    apply (hinc (e.symm p) (e.symm q)).mp
    simpa using hNpq

omit [DecidableEq P] [DecidableEq Q] in
theorem familyWeight_finsetCongr
    (M : FinitePolymerModel P) (N : FinitePolymerModel Q)
    (e : P ≃ Q) (hact : ∀ p, N.activity (e p) = M.activity p)
    (S : Finset P) :
    N.familyWeight (e.finsetCongr S) = M.familyWeight S := by
  unfold familyWeight
  rw [Equiv.finsetCongr_apply, Finset.prod_map]
  simp only [Equiv.coe_toEmbedding]
  apply Finset.prod_congr rfl
  intro p _
  exact hact p

/-- Hard-core partition functions are invariant under an exact relabeling of
the polymer species. -/
theorem partitionFunction_eq_of_equiv
    (M : FinitePolymerModel P) (N : FinitePolymerModel Q)
    (e : P ≃ Q)
    (hinc : ∀ p q, N.incompatible (e p) (e q) ↔ M.incompatible p q)
    (hact : ∀ p, N.activity (e p) = M.activity p) :
    N.partitionFunction = M.partitionFunction := by
  unfold partitionFunction partitionOn compatibleFamilies
  rw [Finset.sum_filter, Finset.sum_filter]
  change (∑ S : Finset Q, if N.Compatible S then N.familyWeight S else 0) =
    ∑ S : Finset P, if M.Compatible S then M.familyWeight S else 0
  rw [← (e.finsetCongr.sum_comp
    (fun S : Finset Q ↦ if N.Compatible S then N.familyWeight S else 0))]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : M.Compatible S
  · rw [if_pos hS, if_pos ((compatible_finsetCongr_iff M N e hinc S).mpr hS),
      familyWeight_finsetCongr M N e hact S]
  · rw [if_neg hS, if_neg (fun h ↦ hS
      ((compatible_finsetCongr_iff M N e hinc S).mp h))]

end FinitePolymerModel

namespace CountablePolymerModel

variable {P Q : Type*} [DecidableEq P] [DecidableEq Q]

/-- Relabel a finite Mayer multi-index along an equivalence of countable
polymer species. -/
def relabelMultiIndex (e : P ≃ Q) : MayerMultiIndex P ≃ MayerMultiIndex Q :=
  Finsupp.equivCongrLeft e

@[simp]
theorem relabelMultiIndex_apply (e : P ≃ Q) (X : MayerMultiIndex P) (p : P) :
    relabelMultiIndex e X (e p) = X p := by
  simp [relabelMultiIndex, Finsupp.equivCongrLeft_apply,
    Finsupp.equivMapDomain_apply]

@[simp]
theorem support_relabelMultiIndex (e : P ≃ Q) (X : MayerMultiIndex P) :
    (relabelMultiIndex e X).support = X.support.map e.toEmbedding := by
  ext q
  rw [Finset.mem_map_equiv]
  simp only [Finsupp.mem_support_iff]
  rw [show relabelMultiIndex e X q = X (e.symm q) by rfl]

/-- Relabelled Mayer occurrences are canonically equivalent.  Constructing
this through `Equiv.sigmaCongr` keeps the dependent `Fin (X p)` casts out of
downstream graph arguments. -/
def mayerVertexRelabelEquiv (e : P ≃ Q) (X : MayerMultiIndex P) :
    MayerVertex (relabelMultiIndex e X) ≃ MayerVertex X := by
  let supportEquiv :
      {q // q ∈ (relabelMultiIndex e X).support} ≃ {p // p ∈ X.support} :=
    Equiv.subtypeEquiv e.symm fun q ↦ by
      rw [support_relabelMultiIndex e X, Finset.mem_map_equiv]
  exact Equiv.sigmaCongr supportEquiv fun _ ↦ finCongr (by rfl)

/-- Relabeling species by an incompatibility-preserving equivalence induces
an isomorphism of occurrence incompatibility graphs. -/
def mayerIncompatibilityGraphRelabelIso
    (M : CountablePolymerModel P) (N : CountablePolymerModel Q)
    (e : P ≃ Q)
    (hinc : ∀ p q, N.incompatible (e p) (e q) ↔ M.incompatible p q)
    (X : MayerMultiIndex P) :
    N.mayerIncompatibilityGraph (relabelMultiIndex e X) ≃g
      M.mayerIncompatibilityGraph X where
  toEquiv := mayerVertexRelabelEquiv e X
  map_rel_iff' := by
    intro a b
    change ((mayerVertexRelabelEquiv e X) a ≠
          (mayerVertexRelabelEquiv e X) b ∧
        M.incompatible (e.symm a.1.1) (e.symm b.1.1)) ↔
      (a ≠ b ∧ N.incompatible a.1.1 b.1.1)
    rw [(mayerVertexRelabelEquiv e X).injective.ne_iff]
    exact and_congr_right fun _ ↦
      (hinc (e.symm a.1.1) (e.symm b.1.1)).symm.trans (by simp)

theorem mayerUrsell_relabelMultiIndex
    (M : CountablePolymerModel P) (N : CountablePolymerModel Q)
    (e : P ≃ Q)
    (hinc : ∀ p q, N.incompatible (e p) (e q) ↔ M.incompatible p q)
    (X : MayerMultiIndex P) :
    N.mayerUrsell (relabelMultiIndex e X) = M.mayerUrsell X := by
  exact connectedSpanningGraphSum_eq_of_iso
    (mayerIncompatibilityGraphRelabelIso M N e hinc X)

theorem mayerSymmetryFactor_relabelMultiIndex (e : P ≃ Q)
    (X : MayerMultiIndex P) :
    mayerSymmetryFactor (relabelMultiIndex e X) = mayerSymmetryFactor X := by
  unfold mayerSymmetryFactor relabelMultiIndex
  rw [Finsupp.equivCongrLeft_apply, Finsupp.prod_equivMapDomain]

theorem mayerActivityMonomial_relabelMultiIndex
    (M : CountablePolymerModel P) (N : CountablePolymerModel Q)
    (e : P ≃ Q) (hact : ∀ p, N.activity (e p) = M.activity p)
    (X : MayerMultiIndex P) :
    N.mayerActivityMonomial (relabelMultiIndex e X) =
      M.mayerActivityMonomial X := by
  unfold mayerActivityMonomial relabelMultiIndex
  rw [Finsupp.equivCongrLeft_apply, Finsupp.prod_equivMapDomain]
  apply Finsupp.prod_congr
  intro p _
  rw [hact]

/-- The full countable Mayer cluster term is invariant under an exact
relabeling of polymer species. -/
theorem mayerClusterTerm_relabelMultiIndex
    (M : CountablePolymerModel P) (N : CountablePolymerModel Q)
    (e : P ≃ Q)
    (hinc : ∀ p q, N.incompatible (e p) (e q) ↔ M.incompatible p q)
    (hact : ∀ p, N.activity (e p) = M.activity p)
    (X : MayerMultiIndex P) :
    N.mayerClusterTerm (relabelMultiIndex e X) = M.mayerClusterTerm X := by
  rw [mayerClusterTerm, mayerClusterTerm,
    mayerUrsell_relabelMultiIndex M N e hinc X,
    mayerSymmetryFactor_relabelMultiIndex e X,
    mayerActivityMonomial_relabelMultiIndex M N e hact X]

end CountablePolymerModel

end

end YangMills.Polymer
