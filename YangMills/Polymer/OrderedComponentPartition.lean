/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.RootedForestPartition
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Data.Finset.Sort

/-!
# The ordered set partition carried by finite graph components

Mathlib's `OrderedFinpartition` is the finite labelled-set partition used by
the Faà di Bruno formula.  This file constructs that partition from the
connected components of a graph on `Fin n`.  Components are ordered by their
largest vertex and vertices inside a component are ordered increasingly.

This is the missing adapter between root deletion of a labelled tree and the
factorially normalized exponential-species calculation.  It is entirely
polymer-independent graph combinatorics.
-/

namespace YangMills.Polymer

open SimpleGraph

noncomputable section

local instance orderedComponentConnectedComponentFintype {n : ℕ}
    (F : SimpleGraph (Fin n)) : Fintype F.ConnectedComponent :=
  Fintype.ofFinite F.ConnectedComponent

local instance orderedComponentSupportFintype {n : ℕ}
    (F : SimpleGraph (Fin n)) (c : F.ConnectedComponent) : Fintype ↑c :=
  Fintype.ofFinite ↑c

/-- The largest vertex in a connected component of a graph on `Fin n`. -/
def connectedComponentMax {n : ℕ} (F : SimpleGraph (Fin n))
    (c : F.ConnectedComponent) : Fin n :=
  (componentVertexFinset F c).max' ⟨c.out,
    (mem_componentVertexFinset F c c.out).mpr c.out_eq⟩

@[simp]
theorem connectedComponentMax_mem {n : ℕ} (F : SimpleGraph (Fin n))
    (c : F.ConnectedComponent) : connectedComponentMax F c ∈ c := by
  exact (mem_componentVertexFinset F c _).mp
    (Finset.max'_mem _ _)

/-- Distinct connected components have distinct largest vertices. -/
theorem connectedComponentMax_injective {n : ℕ}
    (F : SimpleGraph (Fin n)) :
    Function.Injective (connectedComponentMax F) := by
  intro c d hcd
  exact ConnectedComponent.eq_of_common_vertex
    (connectedComponentMax_mem F c)
    (hcd ▸ connectedComponentMax_mem F d)

/-- Linear order on connected components induced by their largest vertex. -/
@[reducible]
noncomputable def connectedComponentMaxLinearOrder {n : ℕ}
    (F : SimpleGraph (Fin n)) : LinearOrder F.ConnectedComponent :=
  LinearOrder.lift' (connectedComponentMax F)
    (connectedComponentMax_injective F)

/-- Increasing enumeration of connected components by largest vertex. -/
noncomputable def orderedConnectedComponentEquiv {n : ℕ}
    (F : SimpleGraph (Fin n)) :
    Fin (Fintype.card F.ConnectedComponent) ≃ F.ConnectedComponent := by
  letI : LinearOrder F.ConnectedComponent :=
    connectedComponentMaxLinearOrder F
  exact (Fintype.orderIsoFinOfCardEq F.ConnectedComponent rfl).toEquiv

/-- Increasing enumeration of the vertices of one connected component. -/
noncomputable def connectedComponentVertexEmbedding {n : ℕ}
    (F : SimpleGraph (Fin n)) (c : F.ConnectedComponent) :
    Fin (Fintype.card ↑c) ↪o Fin n :=
  (componentVertexFinset F c).orderEmbOfFin (by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (componentVertexEquiv F c))

@[simp]
theorem connectedComponentVertexEmbedding_mem {n : ℕ}
    (F : SimpleGraph (Fin n)) (c : F.ConnectedComponent)
    (i : Fin (Fintype.card ↑c)) :
    connectedComponentVertexEmbedding F c i ∈ c := by
  exact (mem_componentVertexFinset F c _).mp
    (Finset.orderEmbOfFin_mem _ _ _)

theorem connectedComponent_card_pos {n : ℕ}
    (F : SimpleGraph (Fin n)) (c : F.ConnectedComponent) :
    0 < Fintype.card ↑c := by
  exact Fintype.card_pos_iff.mpr ⟨⟨c.out, c.out_eq⟩⟩

/-- The final vertex in the increasing component enumeration is its maximum. -/
theorem connectedComponentVertexEmbedding_last {n : ℕ}
    (F : SimpleGraph (Fin n)) (c : F.ConnectedComponent) :
    connectedComponentVertexEmbedding F c
        ⟨Fintype.card ↑c - 1,
          Nat.sub_lt (connectedComponent_card_pos F c) (Nat.succ_pos 0)⟩ =
      connectedComponentMax F c := by
  unfold connectedComponentVertexEmbedding connectedComponentMax
  exact Finset.orderEmbOfFin_last _ (connectedComponent_card_pos F c)

/-- Root deletion of a graph on `Fin n` canonically partitions its labelled
vertices into ordered connected components. -/
noncomputable def orderedComponentPartition {n : ℕ}
    (F : SimpleGraph (Fin n)) : OrderedFinpartition n where
  length := Fintype.card F.ConnectedComponent
  partSize i := Fintype.card ↑(orderedConnectedComponentEquiv F i)
  partSize_pos i := connectedComponent_card_pos F _
  emb i := connectedComponentVertexEmbedding F
    (orderedConnectedComponentEquiv F i)
  emb_strictMono i :=
    (connectedComponentVertexEmbedding F
      (orderedConnectedComponentEquiv F i)).strictMono
  parts_strictMono := by
    intro i j hij
    dsimp only
    rw [connectedComponentVertexEmbedding_last,
      connectedComponentVertexEmbedding_last]
    letI : LinearOrder F.ConnectedComponent :=
      connectedComponentMaxLinearOrder F
    change connectedComponentMax F (orderedConnectedComponentEquiv F i) <
      connectedComponentMax F (orderedConnectedComponentEquiv F j)
    exact (Fintype.orderIsoFinOfCardEq
      F.ConnectedComponent rfl).strictMono hij
  disjoint := by
    intro i _hi j _hj hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    obtain ⟨a, rfl⟩ := hvi
    obtain ⟨b, hab⟩ := hvj
    have ha : (connectedComponentVertexEmbedding F
        (orderedConnectedComponentEquiv F i) a) ∈
        orderedConnectedComponentEquiv F i :=
      connectedComponentVertexEmbedding_mem F _ _
    have hb : (connectedComponentVertexEmbedding F
        (orderedConnectedComponentEquiv F j) b) ∈
        orderedConnectedComponentEquiv F j := by
      exact connectedComponentVertexEmbedding_mem F _ _
    have hb' : (connectedComponentVertexEmbedding F
        (orderedConnectedComponentEquiv F i) a) ∈
        orderedConnectedComponentEquiv F j := by
      rw [← hab]
      exact hb
    apply hij
    exact (orderedConnectedComponentEquiv F).injective <|
      ConnectedComponent.eq_of_common_vertex ha hb'
  cover v := by
    let c := F.connectedComponentMk v
    let i := (orderedConnectedComponentEquiv F).symm c
    have hic : orderedConnectedComponentEquiv F i = c := by
      simp [i]
    have hv : v ∈ orderedConnectedComponentEquiv F i := by
      rw [hic]
      exact ConnectedComponent.connectedComponentMk_mem
    have hrange : v ∈ Set.range (connectedComponentVertexEmbedding F
        (orderedConnectedComponentEquiv F i)) := by
      rw [connectedComponentVertexEmbedding,
        Finset.range_orderEmbOfFin]
      exact (mem_componentVertexFinset F _ v).mpr hv
    exact ⟨i, hrange⟩

@[simp]
theorem orderedComponentPartition_length {n : ℕ}
    (F : SimpleGraph (Fin n)) :
    (orderedComponentPartition F).length =
      Fintype.card F.ConnectedComponent :=
  rfl

/-- The `i`th part of the ordered component partition is exactly the support
of the corresponding connected component. -/
theorem range_orderedComponentPartition_emb {n : ℕ}
    (F : SimpleGraph (Fin n))
    (i : Fin (orderedComponentPartition F).length) :
    Set.range ((orderedComponentPartition F).emb i) =
      (componentVertexFinset F (orderedConnectedComponentEquiv F i) :
        Set (Fin n)) := by
  exact Finset.range_orderEmbOfFin _ _

/-! ## Fixed carriers for individual component blocks -/

/-- Increasing fixed-cardinality enumeration of a connected component,
viewed as an equivalence onto its support subtype. -/
noncomputable def connectedComponentFinEquiv {n : ℕ}
    (F : SimpleGraph (Fin n)) (c : F.ConnectedComponent) :
    Fin (Fintype.card ↑c) ≃ ↑c :=
  ((componentVertexFinset F c).orderIsoOfFin (by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (componentVertexEquiv F c))).toEquiv.trans
    (componentVertexEquiv F c)

@[simp]
theorem connectedComponentFinEquiv_val {n : ℕ}
    (F : SimpleGraph (Fin n)) (c : F.ConnectedComponent)
    (i : Fin (Fintype.card ↑c)) :
    (connectedComponentFinEquiv F c i).1 =
      connectedComponentVertexEmbedding F c i := by
  rfl

/-- The graph induced on the `i`th component, transported to the literal
carrier `Fin (partSize i)`. -/
def orderedComponentGraph {n : ℕ} (F : SimpleGraph (Fin n))
    (i : Fin (orderedComponentPartition F).length) :
    SimpleGraph (Fin ((orderedComponentPartition F).partSize i)) :=
  F.comap ((orderedComponentPartition F).emb i)

/-- The fixed-carrier component graph is isomorphic to Mathlib's canonical
connected-component graph. -/
noncomputable def orderedComponentGraphIso {n : ℕ}
    (F : SimpleGraph (Fin n))
    (i : Fin (orderedComponentPartition F).length) :
    orderedComponentGraph F i ≃g
      (orderedConnectedComponentEquiv F i).toSimpleGraph where
  toEquiv := connectedComponentFinEquiv F
    (orderedConnectedComponentEquiv F i)
  map_rel_iff' := by
    intro v w
    rw [ConnectedComponent.toSimpleGraph_adj]
    change F.Adj
      (connectedComponentFinEquiv F
        (orderedConnectedComponentEquiv F i) v).1
      (connectedComponentFinEquiv F
        (orderedConnectedComponentEquiv F i) w).1 ↔
    F.Adj ((orderedComponentPartition F).emb i v)
      ((orderedComponentPartition F).emb i w)
    rw [connectedComponentFinEquiv_val,
      connectedComponentFinEquiv_val]
    rfl

/-- Every fixed-carrier block of an acyclic graph is a tree. -/
theorem orderedComponentGraph_isTree {n : ℕ}
    {F : SimpleGraph (Fin n)} (hF : F.IsAcyclic)
    (i : Fin (orderedComponentPartition F).length) :
    (orderedComponentGraph F i).IsTree := by
  apply (orderedComponentGraphIso F i).isTree_iff.mpr
  exact hF.isTree_connectedComponent (orderedConnectedComponentEquiv F i)

/-! ## Reconstruction from fixed-carrier blocks -/

/-- Assemble graphs carried by the blocks of an ordered finite partition into
a graph on the complete labelled vertex set. -/
def assembleOrderedComponentGraphs {n : ℕ}
    (c : OrderedFinpartition n)
    (T : ∀ i : Fin c.length, SimpleGraph (Fin (c.partSize i))) :
    SimpleGraph (Fin n) :=
  ⨆ i, (T i).map (c.emb i)

theorem assembleOrderedComponentGraphs_adj {n : ℕ}
    (c : OrderedFinpartition n)
    (T : ∀ i : Fin c.length, SimpleGraph (Fin (c.partSize i)))
    (v w : Fin n) :
    (assembleOrderedComponentGraphs c T).Adj v w ↔
      ∃ (i : Fin c.length) (a b : Fin (c.partSize i)),
        (T i).Adj a b ∧ c.emb i a = v ∧ c.emb i b = w := by
  simp only [assembleOrderedComponentGraphs, SimpleGraph.iSup_adj]
  constructor
  · rintro ⟨i, hi⟩
    rw [SimpleGraph.map_adj'] at hi
    exact ⟨i, hi.2⟩
  · rintro ⟨i, a, b, hab, ha, hb⟩
    refine ⟨i, ?_⟩
    rw [SimpleGraph.map_adj']
    refine ⟨?_, a, b, hab, ha, hb⟩
    intro hvw
    apply hab.ne
    exact (c.emb_strictMono i).injective (ha.trans (hvw.trans hb.symm))

/-- A graph is recovered exactly by assembling the fixed-carrier graphs of
its canonically ordered connected components. -/
theorem assemble_orderedComponentGraphs {n : ℕ}
    (F : SimpleGraph (Fin n)) :
    assembleOrderedComponentGraphs (orderedComponentPartition F)
        (orderedComponentGraph F) = F := by
  classical
  ext v w
  constructor
  · intro hvw
    obtain ⟨i, a, b, hab, rfl, rfl⟩ :=
      (assembleOrderedComponentGraphs_adj
        (orderedComponentPartition F) (orderedComponentGraph F) _ _).mp hvw
    exact hab
  · intro hvw
    obtain ⟨i, a, hia⟩ :=
      (orderedComponentPartition F).cover v
    obtain ⟨j, b, hjb⟩ :=
      (orderedComponentPartition F).cover w
    have hai : (orderedComponentPartition F).emb i a ∈
        orderedConnectedComponentEquiv F i := by
      exact connectedComponentVertexEmbedding_mem F _ _
    have hbj : (orderedComponentPartition F).emb j b ∈
        orderedConnectedComponentEquiv F j := by
      exact connectedComponentVertexEmbedding_mem F _ _
    have hcomp : orderedConnectedComponentEquiv F i =
        orderedConnectedComponentEquiv F j := by
      apply ConnectedComponent.eq_of_common_vertex hai
      rw [hjb] at hbj
      rw [hia]
      rw [ConnectedComponent.mem_supp_iff]
      apply (ConnectedComponent.connectedComponentMk_eq_of_adj hvw).trans
      change w ∈ (orderedConnectedComponentEquiv F j).supp at hbj
      rw [ConnectedComponent.mem_supp_iff] at hbj
      exact hbj
    have hij : i = j := (orderedConnectedComponentEquiv F).injective hcomp
    subst j
    apply (assembleOrderedComponentGraphs_adj
      (orderedComponentPartition F) (orderedComponentGraph F) v w).mpr
    refine ⟨i, a, b, ?_, hia, hjb⟩
    change F.Adj
      ((orderedComponentPartition F).emb i a)
      ((orderedComponentPartition F).emb i b)
    simpa [hia, hjb] using hvw

/-- Assemble labels carried by fixed partition blocks. -/
def assembleOrderedComponentLabels {P : Type*} {n : ℕ}
    (c : OrderedFinpartition n)
    (label : ∀ i : Fin c.length, Fin (c.partSize i) → P) :
    Fin n → P :=
  fun v ↦ label (c.index v) (c.invEmbedding v)

/-- Restricting a global label to the blocks and assembling it again is the
identity. -/
theorem assemble_orderedComponentLabels {P : Type*} {n : ℕ}
    (c : OrderedFinpartition n) (label : Fin n → P) :
    assembleOrderedComponentLabels c
        (fun i j ↦ label (c.emb i j)) = label := by
  funext v
  simp [assembleOrderedComponentLabels]

/-! ## The complement of a distinguished `Option` root -/

/-- Canonical equivalence from `Fin n` to the complement of `none` in
`Option (Fin n)`. -/
def finEquivOptionAwayNone (n : ℕ) :
    Fin n ≃ {v : Option (Fin n) // v ≠ none} where
  toFun i := ⟨some i, Option.some_ne_none i⟩
  invFun v := v.1.get (Option.ne_none_iff_isSome.1 v.2)
  left_inv i := rfl
  right_inv v := by
    rcases v with ⟨(_ | i), hi⟩
    · exact (hi rfl).elim
    · rfl

@[simp]
theorem finEquivOptionAwayNone_apply (n : ℕ) (i : Fin n) :
    (finEquivOptionAwayNone n i).1 = some i :=
  rfl

/-- Root deletion from a graph on `Option (Fin n)`, transported back to its
fixed residual vertex type `Fin n`. -/
def awayGraphOnFin {n : ℕ} (T : SimpleGraph (Option (Fin n))) :
    SimpleGraph (Fin n) :=
  (awayGraph T none).comap (finEquivOptionAwayNone n).toEmbedding

/-- Residual vertices adjacent to the distinguished `none` root. -/
def fixedRootNeighborFinset {n : ℕ}
    (T : SimpleGraph (Option (Fin n))) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i ↦ T.Adj none (some i)

@[simp]
theorem mem_fixedRootNeighborFinset {n : ℕ}
    (T : SimpleGraph (Option (Fin n))) (i : Fin n) :
    i ∈ fixedRootNeighborFinset T ↔ T.Adj none (some i) := by
  simp [fixedRootNeighborFinset]

/-- Reconstruct a graph on `Option (Fin n)` from its residual graph and the
set of residual vertices attached to `none`. -/
def graphOfFixedRootData {n : ℕ} (F : SimpleGraph (Fin n))
    (attachments : Finset (Fin n)) : SimpleGraph (Option (Fin n)) where
  Adj v w := match v, w with
    | none, none => False
    | none, some j => j ∈ attachments
    | some i, none => i ∈ attachments
    | some i, some j => F.Adj i j
  symm := by
    intro v w
    cases v <;> cases w <;> simp [SimpleGraph.adj_comm]
  loopless := ⟨by
    intro v
    cases v <;> simp⟩

@[simp]
theorem graphOfFixedRootData_adj_none_some {n : ℕ}
    (F : SimpleGraph (Fin n)) (attachments : Finset (Fin n)) (i : Fin n) :
    (graphOfFixedRootData F attachments).Adj none (some i) ↔
      i ∈ attachments :=
  Iff.rfl

@[simp]
theorem graphOfFixedRootData_adj_some_some {n : ℕ}
    (F : SimpleGraph (Fin n)) (attachments : Finset (Fin n)) (i j : Fin n) :
    (graphOfFixedRootData F attachments).Adj (some i) (some j) ↔
      F.Adj i j :=
  Iff.rfl

@[simp]
theorem awayGraphOnFin_adj {n : ℕ}
    (T : SimpleGraph (Option (Fin n))) (i j : Fin n) :
    (awayGraphOnFin T).Adj i j ↔ T.Adj (some i) (some j) := by
  rfl

/-- Fixed root data lose no graph information. -/
theorem graphOfFixedRootData_fixedRootData {n : ℕ}
    (T : SimpleGraph (Option (Fin n))) :
    graphOfFixedRootData (awayGraphOnFin T)
      (fixedRootNeighborFinset T) = T := by
  classical
  ext v w
  cases v <;> cases w <;>
    simp [graphOfFixedRootData, SimpleGraph.adj_comm]

/-- Root deletion transported to `Fin n` is graph-isomorphic to the original
complement subtype. -/
def awayGraphOnFinIso {n : ℕ}
    (T : SimpleGraph (Option (Fin n))) :
    awayGraphOnFin T ≃g awayGraph T none where
  toEquiv := finEquivOptionAwayNone n
  map_rel_iff' := by
    intro i j
    rfl

/-- Ordered labelled-set partition of the residual vertices obtained by
deleting the distinguished `none` root. -/
noncomputable def orderedAwayComponentPartition {n : ℕ}
    (T : SimpleGraph (Option (Fin n))) : OrderedFinpartition n :=
  orderedComponentPartition (awayGraphOnFin T)

@[simp]
theorem orderedAwayComponentPartition_length {n : ℕ}
    (T : SimpleGraph (Option (Fin n))) :
    (orderedAwayComponentPartition T).length =
      Fintype.card (awayGraphOnFin T).ConnectedComponent :=
  rfl

/-- Every block of the ordered root-deletion partition is precisely one
connected component of the transported away graph. -/
theorem range_orderedAwayComponentPartition_emb {n : ℕ}
    (T : SimpleGraph (Option (Fin n)))
    (i : Fin (orderedAwayComponentPartition T).length) :
    Set.range ((orderedAwayComponentPartition T).emb i) =
      (componentVertexFinset (awayGraphOnFin T)
        (orderedConnectedComponentEquiv (awayGraphOnFin T) i) :
          Set (Fin n)) :=
  range_orderedComponentPartition_emb (awayGraphOnFin T) i

/-- The original root-complement component corresponding to the `i`th
fixed-carrier ordered block. -/
noncomputable def orderedAwayOriginalComponent {n : ℕ}
    (T : SimpleGraph (Option (Fin n)))
    (i : Fin (orderedAwayComponentPartition T).length) :
    (awayGraph T none).ConnectedComponent :=
  (awayGraphOnFinIso T).connectedComponentEquiv
    (orderedConnectedComponentEquiv (awayGraphOnFin T) i)

/-- Global residual vertex of the unique edge joining the `i`th component
to the deleted root. -/
noncomputable def orderedAwayChildRootVertex {n : ℕ}
    {T : SimpleGraph (Option (Fin n))} (hT : T.IsTree)
    (i : Fin (orderedAwayComponentPartition T).length) : Fin n :=
  (awayGraphOnFinIso T).symm
    (IsTree.childRoot hT none (orderedAwayOriginalComponent T i))

theorem orderedAwayChildRootVertex_mem {n : ℕ}
    {T : SimpleGraph (Option (Fin n))} (hT : T.IsTree)
    (i : Fin (orderedAwayComponentPartition T).length) :
    orderedAwayChildRootVertex hT i ∈
      orderedConnectedComponentEquiv (awayGraphOnFin T) i := by
  change orderedAwayChildRootVertex hT i ∈
    (orderedConnectedComponentEquiv (awayGraphOnFin T) i).supp
  rw [ConnectedComponent.mem_supp_iff]
  apply (ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map).mpr
  exact (ConnectedComponent.mem_supp_iff _ _).mp
    (IsTree.childRoot_mem hT none (orderedAwayOriginalComponent T i))

/-- Local fixed-carrier index of the unique attachment vertex. -/
noncomputable def orderedAwayChildRootIndex {n : ℕ}
    {T : SimpleGraph (Option (Fin n))} (hT : T.IsTree)
    (i : Fin (orderedAwayComponentPartition T).length) :
    Fin ((orderedAwayComponentPartition T).partSize i) :=
  (connectedComponentFinEquiv (awayGraphOnFin T)
    (orderedConnectedComponentEquiv (awayGraphOnFin T) i)).symm
      ⟨orderedAwayChildRootVertex hT i,
        orderedAwayChildRootVertex_mem hT i⟩

@[simp]
theorem orderedAwayComponentPartition_emb_childRootIndex {n : ℕ}
    {T : SimpleGraph (Option (Fin n))} (hT : T.IsTree)
    (i : Fin (orderedAwayComponentPartition T).length) :
    (orderedAwayComponentPartition T).emb i
        (orderedAwayChildRootIndex hT i) =
      orderedAwayChildRootVertex hT i := by
  have h := congrArg Subtype.val
    ((connectedComponentFinEquiv (awayGraphOnFin T)
      (orderedConnectedComponentEquiv (awayGraphOnFin T) i)).apply_symm_apply
        ⟨orderedAwayChildRootVertex hT i,
          orderedAwayChildRootVertex_mem hT i⟩)
  simpa only [connectedComponentFinEquiv_val] using h

/-- The selected fixed-carrier child root is genuinely adjacent to the
deleted parent root. -/
theorem adj_orderedAwayChildRootVertex {n : ℕ}
    {T : SimpleGraph (Option (Fin n))} (hT : T.IsTree)
    (i : Fin (orderedAwayComponentPartition T).length) :
    T.Adj none (some (orderedAwayChildRootVertex hT i)) := by
  let c := orderedAwayOriginalComponent T i
  let v := IsTree.childRoot hT none c
  have hadj : T.Adj none v.1 := IsTree.adj_childRoot hT none c
  have heq := congrArg Subtype.val
    ((awayGraphOnFinIso T).apply_symm_apply v)
  change T.Adj none
    ((awayGraphOnFinIso T) ((awayGraphOnFinIso T).symm v)).1
  rw [heq]
  exact hadj

/-- Assemble one distinguished local vertex from every ordered block. -/
def assembleOrderedComponentAttachments {n : ℕ}
    (c : OrderedFinpartition n)
    (root : ∀ i : Fin c.length, Fin (c.partSize i)) : Finset (Fin n) :=
  Finset.univ.image fun i ↦ c.emb i (root i)

/-- The local child-root indices obtained from a rooted tree reconstruct its
complete residual root-neighbor finset. -/
theorem assemble_orderedAwayChildRootIndices {n : ℕ}
    {T : SimpleGraph (Option (Fin n))} (hT : T.IsTree) :
    assembleOrderedComponentAttachments
        (orderedAwayComponentPartition T)
        (orderedAwayChildRootIndex hT) =
      fixedRootNeighborFinset T := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨i, _hi, hiv⟩ := Finset.mem_image.mp hv
    rw [← hiv, orderedAwayComponentPartition_emb_childRootIndex]
    exact (mem_fixedRootNeighborFinset T _).mpr
      (adj_orderedAwayChildRootVertex hT i)
  · intro hv
    have hvadj : T.Adj none (some v) :=
      (mem_fixedRootNeighborFinset T v).mp hv
    let F := awayGraphOnFin T
    let c : F.ConnectedComponent := F.connectedComponentMk v
    let i : Fin (orderedAwayComponentPartition T).length :=
      (orderedConnectedComponentEquiv F).symm c
    have hic : orderedConnectedComponentEquiv F i = c := by
      simp [i]
    have hvmem : (finEquivOptionAwayNone n v) ∈
        orderedAwayOriginalComponent T i := by
      change (finEquivOptionAwayNone n v) ∈
        ((awayGraphOnFinIso T).connectedComponentEquiv
          (orderedConnectedComponentEquiv F i)).supp
      rw [hic]
      exact ((ConnectedComponent.isoEquivSupp (awayGraphOnFinIso T) c)
        ⟨v, ConnectedComponent.connectedComponentMk_mem⟩).prop
    have hrootEq : (finEquivOptionAwayNone n v) =
        IsTree.childRoot hT none (orderedAwayOriginalComponent T i) :=
      IsTree.eq_childRoot_of_mem_of_adj hT none
        (orderedAwayOriginalComponent T i)
        (finEquivOptionAwayNone n v) hvmem (by simpa using hvadj)
    have hvroot : v = orderedAwayChildRootVertex hT i := by
      calc
        v = (awayGraphOnFinIso T).symm
            ((awayGraphOnFinIso T) v) := by simp
        _ = (awayGraphOnFinIso T).symm
            (IsTree.childRoot hT none
              (orderedAwayOriginalComponent T i)) :=
          congrArg (fun x ↦ (awayGraphOnFinIso T).symm x) hrootEq
        _ = orderedAwayChildRootVertex hT i := rfl
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rw [orderedAwayComponentPartition_emb_childRootIndex, ← hvroot]

/-- The `i`th rooted-away component graph on its literal fixed carrier. -/
def orderedAwayComponentGraph {n : ℕ}
    (T : SimpleGraph (Option (Fin n)))
    (i : Fin (orderedAwayComponentPartition T).length) :
    SimpleGraph (Fin ((orderedAwayComponentPartition T).partSize i)) :=
  orderedComponentGraph (awayGraphOnFin T) i

/-- Root deletion of a tree produces genuine fixed-carrier component trees.
This is the graph half of the labelled-set decomposition used in the KP
recurrence. -/
theorem orderedAwayComponentGraph_isTree {n : ℕ}
    {T : SimpleGraph (Option (Fin n))} (hT : T.IsTree)
    (i : Fin (orderedAwayComponentPartition T).length) :
    (orderedAwayComponentGraph T i).IsTree := by
  apply orderedComponentGraph_isTree
  exact (hT.2.induce {v | v ≠ none}).of_comap
    (finEquivOptionAwayNone n).toEmbedding

end

end YangMills.Polymer
