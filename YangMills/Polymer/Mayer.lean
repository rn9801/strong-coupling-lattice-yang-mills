/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.FiniteGas
import YangMills.Polymer.GraphExponential
import Mathlib.Data.Finsupp.Basic

/-!
# Mayer multi-indices and source-marked clusters

This file supplies the combinatorial language needed by the thermodynamic
limit and correlation proofs.  A cluster is a finite multi-index of polymers;
different copies of the same polymer are distinct vertices, and the Ursell
coefficient is the signed sum over connected spanning subgraphs of the
resulting incompatibility graph.

The source-marking convention follows the standard modified-partition-
function construction: scaling one distinguished polymer by `α` multiplies a
cluster term by `α` to exactly the multiplicity of that polymer.  Consequently
the coefficient linear in `α` consists precisely of clusters containing one
copy of the source.  Two source variables similarly isolate the connected
two-root contribution used for truncated correlations.

Mathematical references:

* R. Kotecký and D. Preiss, *Cluster expansion for abstract polymer models*,
  Commun. Math. Phys. 103 (1986), 491--498.
* D. Ueltschi, *Cluster expansions and correlation functions*, Moscow Math.
  J. 4 (2004), 511--522.

This module is part of the model-independent polymer layer.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

namespace FinitePolymerModel

variable {P : Type*} [Fintype P] [DecidableEq P]

local instance {V : Type*} [Fintype V] [DecidableEq V] :
    DecidableLE (Finpartition (Finset.univ : Finset V)) := Classical.decRel _

local instance {V : Type*} [Fintype V] [DecidableEq V] :
    DecidableLT (Finpartition (Finset.univ : Finset V)) := Classical.decRel _

local instance {V : Type*} [Fintype V] [DecidableEq V] :
    LocallyFiniteOrder (Finpartition (Finset.univ : Finset V)) :=
  Fintype.toLocallyFiniteOrder

/-- A finite polymer multi-index.  Its value is the multiplicity with which a
polymer occurs in a Mayer cluster. -/
abbrev MayerMultiIndex (P : Type*) := P →₀ ℕ

/-- Vertices of the incompatibility graph carried by a multi-index. -/
abbrev MayerVertex (X : MayerMultiIndex P) := Σ γ : P, Fin (X γ)

/-- Incompatibility graph of all labelled copies in a Mayer multi-index. -/
def mayerIncompatibilityGraph (M : FinitePolymerModel P)
    (X : MayerMultiIndex P) : SimpleGraph (MayerVertex X) where
  Adj i j := i ≠ j ∧ M.incompatible i.1 j.1
  symm _ _ h := ⟨h.1.symm, M.symmetric_incompatible h.2⟩
  loopless := ⟨fun _i h => h.1 rfl⟩

/-- Connected spanning subgraphs of a graph on an arbitrary finite vertex
type. -/
def mayerConnectedSpanningSubgraphs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (SimpleGraph V) := by
  classical
  exact (spanningSubgraphs G).filter SimpleGraph.Connected

/-- Signed connected-graph sum on an arbitrary finite vertex type. -/
def mayerUrsellGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℤ :=
  connectedSpanningGraphSum G

/-- The Ursell coefficient is the Möbius cumulant of the finite compatibility
moments.  This is the connected-component regrouping behind the symmetric
Mayer expansion. -/
theorem mayerUrsellGraph_eq_moebius_cancellation
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) :
    mayerUrsellGraph G =
      ∑ Q : Finpartition (Finset.univ : Finset V),
        IncidenceAlgebra.mu ℤ Q ⊤ *
          (if partitionEdgeFinset G Q = ∅ then 1 else 0) :=
  connectedSpanningGraphSum_eq_moebius_cancellation G

/-- Ursell coefficient of a polymer multi-index. -/
def mayerUrsell (M : FinitePolymerModel P) (X : MayerMultiIndex P) : ℤ :=
  mayerUrsellGraph (M.mayerIncompatibilityGraph X)

theorem mayerConnectedSpanningSubgraphs_eq_empty_of_not_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : ¬G.Connected) :
    mayerConnectedSpanningSubgraphs G = ∅ := by
  exact connectedSpanningSubgraphs_eq_empty_of_not_connected hG

/-- The multi-index Ursell coefficient vanishes unless its incompatibility
graph is connected.  This is the exact linked-cluster cancellation used by
both marked limits and truncated correlations. -/
theorem mayerUrsell_eq_zero_of_not_connected
    (M : FinitePolymerModel P) (X : MayerMultiIndex P)
    (hX : ¬(M.mayerIncompatibilityGraph X).Connected) :
    M.mayerUrsell X = 0 := by
  exact connectedSpanningGraphSum_eq_zero_of_not_connected hX

/-- Product of multiplicity factorials in the Mayer symmetry factor. -/
def mayerSymmetryFactor (X : MayerMultiIndex P) : ℕ :=
  ∏ γ : P, (X γ).factorial

/-- Activity monomial belonging to a multi-index. -/
def mayerActivityMonomial (M : FinitePolymerModel P)
    (X : MayerMultiIndex P) : ℂ :=
  ∏ γ : P, M.activity γ ^ X γ

/-- The normalized connected Mayer term. -/
def mayerClusterTerm (M : FinitePolymerModel P)
    (X : MayerMultiIndex P) : ℂ :=
  (M.mayerUrsell X : ℂ) / (mayerSymmetryFactor X : ℂ) *
    M.mayerActivityMonomial X

@[simp]
theorem mayerClusterTerm_eq_zero_of_not_connected
    (M : FinitePolymerModel P) (X : MayerMultiIndex P)
    (hX : ¬(M.mayerIncompatibilityGraph X).Connected) :
    M.mayerClusterTerm X = 0 := by
  simp [mayerClusterTerm, M.mayerUrsell_eq_zero_of_not_connected X hX]

/-- Polymers occurring with positive multiplicity. -/
def mayerSupport (X : MayerMultiIndex P) : Finset P :=
  Finset.univ.filter fun γ => 0 < X γ

@[simp]
theorem mem_mayerSupport (X : MayerMultiIndex P) (γ : P) :
    γ ∈ mayerSupport X ↔ 0 < X γ := by
  simp [mayerSupport]

/-- Total weighted size of a cluster, with multiplicity. -/
def mayerMass (size : P → ℕ) (X : MayerMultiIndex P) : ℕ :=
  ∑ γ : P, X γ * size γ

/-- A cluster is rooted at `root` when the root occurs. -/
def IsMayerRooted (X : MayerMultiIndex P) (root : P) : Prop :=
  0 < X root

/-- A cluster joins two roots when both occur in the same connected
incompatibility graph. -/
def IsTwoRootMayerCluster (M : FinitePolymerModel P)
    (X : MayerMultiIndex P) (root₁ root₂ : P) : Prop :=
  IsMayerRooted X root₁ ∧ IsMayerRooted X root₂ ∧
    (M.mayerIncompatibilityGraph X).Connected

/-- Scale one distinguished polymer activity by a source variable. -/
def scaleActivityAt (M : FinitePolymerModel P) (root : P) (α : ℂ) :
    FinitePolymerModel P where
  incompatible := M.incompatible
  decidableIncompatible := M.decidableIncompatible
  symmetric_incompatible := M.symmetric_incompatible
  self_incompatible := M.self_incompatible
  activity γ := if γ = root then α * M.activity γ else M.activity γ

@[simp]
theorem scaleActivityAt_incompatible (M : FinitePolymerModel P)
    (root : P) (α : ℂ) :
    (M.scaleActivityAt root α).incompatible = M.incompatible :=
  rfl

theorem mayerActivityMonomial_scaleActivityAt
    (M : FinitePolymerModel P) (X : MayerMultiIndex P)
    (root : P) (α : ℂ) :
    (M.scaleActivityAt root α).mayerActivityMonomial X =
      α ^ X root * M.mayerActivityMonomial X := by
  classical
  unfold mayerActivityMonomial scaleActivityAt
  rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset P))
    (f := fun γ => M.activity γ ^ X γ) (Finset.mem_univ root)]
  rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset P))
    (f := fun γ => (if γ = root then α * M.activity γ else M.activity γ) ^ X γ)
    (Finset.mem_univ root)]
  simp only [if_pos, mul_pow]
  have hrest :
      ∏ γ ∈ (Finset.univ : Finset P).erase root,
          (if γ = root then α * M.activity γ else M.activity γ) ^ X γ =
        ∏ γ ∈ (Finset.univ : Finset P).erase root,
          M.activity γ ^ X γ := by
    apply Finset.prod_congr rfl
    intro γ hγ
    have hne : γ ≠ root := (Finset.mem_erase.mp hγ).1
    simp [hne]
  rw [hrest]
  ring

/-- Source scaling multiplies a connected cluster term by the corresponding
source power.  In particular, terms linear in `α` are exactly those for which
the root multiplicity equals one. -/
theorem mayerClusterTerm_scaleActivityAt
    (M : FinitePolymerModel P) (X : MayerMultiIndex P)
    (root : P) (α : ℂ) :
    (M.scaleActivityAt root α).mayerClusterTerm X =
      α ^ X root * M.mayerClusterTerm X := by
  unfold mayerClusterTerm
  rw [mayerActivityMonomial_scaleActivityAt]
  change ((M.mayerUrsell X : ℂ) / (mayerSymmetryFactor X : ℂ)) *
      (α ^ X root * M.mayerActivityMonomial X) = _
  ring

/-- Scaling two source activities records both multiplicities.  The
coefficient bilinear in the two source variables is therefore supported on
clusters containing exactly one copy of each source; connectedness of the
Ursell term forces those two roots into one linked cluster. -/
theorem mayerClusterTerm_scaleActivityAt_scaleActivityAt
    (M : FinitePolymerModel P) (X : MayerMultiIndex P)
    (root₁ root₂ : P) (α₁ α₂ : ℂ) :
    ((M.scaleActivityAt root₁ α₁).scaleActivityAt root₂ α₂).mayerClusterTerm X =
      α₁ ^ X root₁ * α₂ ^ X root₂ * M.mayerClusterTerm X := by
  rw [mayerClusterTerm_scaleActivityAt, mayerClusterTerm_scaleActivityAt]
  ring

/-- Terms selected by the coefficient linear in one source. -/
def oneRootMayerTerm (M : FinitePolymerModel P)
    (root : P) (X : MayerMultiIndex P) : ℂ :=
  if X root = 1 then M.mayerClusterTerm X else 0

/-- Terms selected by the coefficient bilinear in two sources. -/
def twoRootMayerTerm (M : FinitePolymerModel P)
    (root₁ root₂ : P) (X : MayerMultiIndex P) : ℂ :=
  if X root₁ = 1 ∧ X root₂ = 1 then M.mayerClusterTerm X else 0

theorem twoRootMayerTerm_eq_zero_of_not_connected
    (M : FinitePolymerModel P) (root₁ root₂ : P)
    (X : MayerMultiIndex P)
    (hX : ¬(M.mayerIncompatibilityGraph X).Connected) :
    M.twoRootMayerTerm root₁ root₂ X = 0 := by
  simp [twoRootMayerTerm, M.mayerClusterTerm_eq_zero_of_not_connected X hX]

/-- At zero source, every term containing the marked polymer vanishes. -/
@[simp]
theorem mayerClusterTerm_scaleActivityAt_zero_of_rooted
    (M : FinitePolymerModel P) (X : MayerMultiIndex P) (root : P)
    (hroot : IsMayerRooted X root) :
    (M.scaleActivityAt root 0).mayerClusterTerm X = 0 := by
  rw [mayerClusterTerm_scaleActivityAt]
  simp [Nat.ne_of_gt hroot]

end FinitePolymerModel

end

end YangMills.Polymer
