/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Decomposing a finite tree at its root

The components left after deleting the root of a tree are its child subtrees.
This file proves the structural fact needed by the KP species bridge: every
such component has exactly one vertex adjacent to the deleted root.

The development is graph-theoretic and independent of polymer activities and
of Yang--Mills.
-/

namespace YangMills.Polymer

open SimpleGraph

noncomputable section

variable {V : Type*}

/-- In an acyclic graph, two neighbors of `root` joined by a path avoiding
`root` must coincide.  Otherwise that path and the two root edges would give
two distinct paths from `root`. -/
theorem IsAcyclic.eq_of_adj_root_of_reachable_avoiding_root
    {G : SimpleGraph V} (hG : G.IsAcyclic)
    {root u v : V} (hru : G.Adj root u) (hrv : G.Adj root v)
    (p : G.Walk u v) (hp : p.IsPath) (hroot : root ∉ p.support) :
    u = v := by
  let q : G.Path root v := ⟨Walk.cons hru p, hp.cons hroot⟩
  have heq := hG.path_unique q (Path.singleton hrv)
  have hwalk : (Walk.cons hru p : G.Walk root v) =
      Walk.cons hrv Walk.nil := by
    simpa [q, Path.singleton_coe] using congrArg Subtype.val heq
  have hsnd := congrArg Walk.snd hwalk
  simpa using hsnd

/-- The graph induced on all vertices other than `root`. -/
def awayGraph (G : SimpleGraph V) (root : V) :
    SimpleGraph {v : V // v ≠ root} :=
  G.induce {v | v ≠ root}

/-- Inclusion of the graph away from `root` into the original graph. -/
def awayInclusion (G : SimpleGraph V) (root : V) :
    awayGraph G root →g G where
  toFun := Subtype.val
  map_rel' := id

/-- Two neighbors of `root` belonging to one component away from `root` are
equal. -/
theorem IsAcyclic.eq_of_adj_root_of_away_reachable
    {G : SimpleGraph V} (hG : G.IsAcyclic) {root u v : V}
    (hru : G.Adj root u) (hrv : G.Adj root v)
    (hu : u ≠ root) (hv : v ≠ root)
    (hreach : (awayGraph G root).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    u = v := by
  classical
  apply hreach.elim
  intro p
  let q := p.toPath.map (awayInclusion G root) Subtype.val_injective
  apply IsAcyclic.eq_of_adj_root_of_reachable_avoiding_root
    hG hru hrv q.1 q.2
  dsimp [q]
  change root ∉ (Walk.map (awayInclusion G root) p.toPath.1).support
  rw [Walk.support_map]
  simp [awayInclusion]

/-- Every component obtained by deleting the root of a tree is attached to
the root at exactly one vertex.  That vertex is the root of the corresponding
child subtree. -/
theorem IsTree.existsUnique_adj_root_in_awayComponent
    {G : SimpleGraph V} (hG : G.IsTree) (root : V)
    (c : (awayGraph G root).ConnectedComponent) :
    ∃! v : {x : V // x ≠ root}, v ∈ c ∧ G.Adj root v := by
  classical
  obtain ⟨u, hu⟩ := c.nonempty_supp
  have hreach : G.Reachable root u.1 :=
    hG.connected.preconnected root u.1
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  have hpne : ¬p.Nil := p.not_nil_of_ne u.2.symm
  have hrootTail : root ∉ p.tail.support := by
    rw [p.support_tail_of_not_nil hpne]
    have hnodup : (root :: p.support.tail).Nodup := by
      rw [p.cons_tail_support]
      exact hp.support_nodup
    exact (List.nodup_cons.mp hnodup).1
  have htailAway : ∀ x ∈ p.tail.support,
      x ∈ ({x : V | x ≠ root} : Set V) := by
    intro x hx hxr
    exact hrootTail (hxr ▸ hx)
  let v : {x : V // x ≠ root} :=
    ⟨p.snd, (p.adj_snd hpne).ne.symm⟩
  let qi := p.tail.induce ({x : V | x ≠ root} : Set V) htailAway
  have hreachAway : (awayGraph G root).Reachable v u := ⟨qi⟩
  have hvcomp : v ∈ c := by
    change v ∈ c.supp
    rw [ConnectedComponent.mem_supp_iff]
    rw [ConnectedComponent.sound hreachAway]
    exact (ConnectedComponent.mem_supp_iff c u).mp hu
  refine ⟨v, ⟨hvcomp, p.adj_snd hpne⟩, ?_⟩
  intro w hw
  apply Subtype.ext
  apply IsAcyclic.eq_of_adj_root_of_away_reachable
    hG.isAcyclic hw.2 (p.adj_snd hpne) w.2 v.2
  exact c.reachable_of_mem_supp hw.1 hvcomp

/-- Each root-deleted component, with its induced edges, is itself a tree. -/
theorem IsTree.awayComponent_isTree
    {G : SimpleGraph V} (hG : G.IsTree) (root : V)
    (c : (awayGraph G root).ConnectedComponent) :
    c.toSimpleGraph.IsTree :=
  (hG.isAcyclic.induce {v : V | v ≠ root}).isTree_connectedComponent c

/-- Canonical root of a child component: its unique vertex adjacent to the
deleted parent root. -/
noncomputable def IsTree.childRoot
    {G : SimpleGraph V} (hG : G.IsTree) (root : V)
    (c : (awayGraph G root).ConnectedComponent) : {x : V // x ≠ root} :=
  Classical.choose
    (IsTree.existsUnique_adj_root_in_awayComponent hG root c)

theorem IsTree.childRoot_mem
    {G : SimpleGraph V} (hG : G.IsTree) (root : V)
    (c : (awayGraph G root).ConnectedComponent) :
    IsTree.childRoot hG root c ∈ c :=
  (Classical.choose_spec
    (IsTree.existsUnique_adj_root_in_awayComponent hG root c)).1.1

theorem IsTree.adj_childRoot
    {G : SimpleGraph V} (hG : G.IsTree) (root : V)
    (c : (awayGraph G root).ConnectedComponent) :
    G.Adj root (IsTree.childRoot hG root c).1 :=
  (Classical.choose_spec
    (IsTree.existsUnique_adj_root_in_awayComponent hG root c)).1.2

theorem IsTree.eq_childRoot_of_mem_of_adj
    {G : SimpleGraph V} (hG : G.IsTree) (root : V)
    (c : (awayGraph G root).ConnectedComponent)
    (v : {x : V // x ≠ root}) (hv : v ∈ c)
    (hvadj : G.Adj root v.1) :
    v = IsTree.childRoot hG root c := by
  exact (Classical.choose_spec
    (IsTree.existsUnique_adj_root_in_awayComponent hG root c)).2 v ⟨hv, hvadj⟩

/-- Different child components have different canonical attachment
vertices. -/
theorem IsTree.childRoot_injective
    {G : SimpleGraph V} (hG : G.IsTree) (root : V) :
    Function.Injective (IsTree.childRoot hG root) := by
  intro c d hcd
  apply ConnectedComponent.eq_of_common_vertex
    (IsTree.childRoot_mem hG root c)
  simpa [hcd] using IsTree.childRoot_mem hG root d

/-- A rooted finite tree has at most `|V| - 1` child components. -/
theorem IsTree.card_awayComponent_le_card_sub_one
    [Fintype V] {G : SimpleGraph V}
    (hG : G.IsTree) (root : V) :
    Nat.card (awayGraph G root).ConnectedComponent ≤
      Fintype.card V - 1 := by
  classical
  calc
    Nat.card (awayGraph G root).ConnectedComponent ≤
        Nat.card {x : V // x ≠ root} :=
      Nat.card_le_card_of_injective (IsTree.childRoot hG root)
        (IsTree.childRoot_injective hG root)
    _ = Fintype.card {x : V // x ≠ root} :=
      Nat.card_eq_fintype_card
    _ = Fintype.card V - 1 := by
      rw [Fintype.card_subtype_compl (fun x : V => x = root)]
      simp

/-- The child components are pairwise disjoint.  Together with
`iUnion_awayComponentSupp`, this says that they form an unordered partition
of all non-root vertices. -/
theorem pairwise_disjoint_awayComponentSupp (G : SimpleGraph V) (root : V) :
    Pairwise fun c c' : (awayGraph G root).ConnectedComponent =>
      Disjoint c.supp c'.supp :=
  pairwise_disjoint_supp_connectedComponent (awayGraph G root)

/-- The child components cover every non-root vertex. -/
theorem iUnion_awayComponentSupp (G : SimpleGraph V) (root : V) :
    ⋃ c : (awayGraph G root).ConnectedComponent, c.supp = Set.univ :=
  iUnion_connectedComponentSupp (awayGraph G root)

/-- Choosing a connected component and then a vertex in its support is
equivalent to choosing a vertex of the graph.  Mathlib exposes the disjoint
cover lemmas separately; this equivalence is the finite-sum reindexing needed
by weighted component decompositions. -/
def connectedComponentVertexEquiv (G : SimpleGraph V) :
    (Σ c : G.ConnectedComponent, ↥c) ≃ V :=
  Equiv.sigmaFiberEquiv G.connectedComponentMk

local instance connectedComponentFintype [Finite V] (G : SimpleGraph V) :
    Fintype G.ConnectedComponent := Fintype.ofFinite G.ConnectedComponent

local instance connectedComponentSupportFintype [Finite V]
    (G : SimpleGraph V) (c : G.ConnectedComponent) : Fintype ↥c :=
  Fintype.ofFinite ↥c

/-- Finite sums may be regrouped exactly over connected components. -/
theorem sum_connectedComponents_sum
    [Fintype V] {R : Type*} [AddCommMonoid R]
    (G : SimpleGraph V) (f : V → R) :
    ∑ c : G.ConnectedComponent, ∑ v : ↥c, f v.1 =
      ∑ v : V, f v := by
  classical
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv (connectedComponentVertexEquiv G)
    (fun x => f x.2.1) f (fun _ => rfl)

/-- Complete structural decomposition of a rooted tree: the components away
from the root are disjoint child trees covering all remaining vertices, and
each has one canonical attachment to the root.  This is the graph-theoretic
input to the weighted labelled-species enumeration. -/
theorem IsTree.rootDecomposition
    {G : SimpleGraph V} (hG : G.IsTree) (root : V) :
    (∀ c : (awayGraph G root).ConnectedComponent,
        c.toSimpleGraph.IsTree) ∧
    (∀ c : (awayGraph G root).ConnectedComponent,
        ∃! v : {x : V // x ≠ root}, v ∈ c ∧ G.Adj root v) ∧
    (Pairwise fun c c' : (awayGraph G root).ConnectedComponent =>
        Disjoint c.supp c'.supp) ∧
    (⋃ c : (awayGraph G root).ConnectedComponent, c.supp) = Set.univ := by
  exact ⟨IsTree.awayComponent_isTree hG root,
    IsTree.existsUnique_adj_root_in_awayComponent hG root,
    pairwise_disjoint_awayComponentSupp G root,
    iUnion_awayComponentSupp G root⟩

/-! ## Lossless finite root data -/

/-- The neighbors of `root`, regarded as vertices of the graph with `root`
deleted.  Keeping this finset alongside `awayGraph` is a non-dependent way to
encode a rooted graph; it is considerably easier to count than a family of
component-indexed attachment subtypes. -/
def rootNeighborFinset [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) : Finset {v : V // v ≠ root} := by
  classical
  exact Finset.univ.filter fun v => G.Adj root v.1

@[simp]
theorem mem_rootNeighborFinset [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) (v : {v : V // v ≠ root}) :
    v ∈ rootNeighborFinset G root ↔ G.Adj root v.1 := by
  simp [rootNeighborFinset]

/-- Root deletion data for an arbitrary finite graph. -/
def rootedGraphData [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) :
    SimpleGraph {v : V // v ≠ root} × Finset {v : V // v ≠ root} :=
  (awayGraph G root, rootNeighborFinset G root)

/-- Root deletion loses no graph information: the graph away from the root
and the finite set of root neighbors determine every edge.  This is the
injectivity statement needed for the finite rooted-forest orbit count. -/
theorem rootedGraphData_injective [Fintype V] [DecidableEq V] (root : V) :
    Function.Injective (fun G : SimpleGraph V => rootedGraphData G root) := by
  classical
  intro G H hdata
  have haway : awayGraph G root = awayGraph H root :=
    congrArg Prod.fst hdata
  have hneighbors : rootNeighborFinset G root = rootNeighborFinset H root :=
    congrArg Prod.snd hdata
  ext v w
  by_cases hvr : v = root
  · subst v
    by_cases hwr : w = root
    · subst w
      simp
    · let w' : {x : V // x ≠ root} := ⟨w, hwr⟩
      have hw := Finset.ext_iff.mp hneighbors w'
      simpa [w'] using hw
  · by_cases hwr : w = root
    · subst w
      let v' : {x : V // x ≠ root} := ⟨v, hvr⟩
      have hv := Finset.ext_iff.mp hneighbors v'
      simpa [v', SimpleGraph.adj_comm] using hv
    · have hvw := congrFun (congrFun (SimpleGraph.ext_iff.mp haway)
          (⟨v, hvr⟩ : {x : V // x ≠ root})) ⟨w, hwr⟩
      simpa [awayGraph] using iff_of_eq hvw

/-- A non-dependent rooted-forest datum has exactly one selected attachment
in every component.  For data obtained from a tree this is the image of the
canonical `childRoot`; phrasing it as a finset intersection avoids transports
between dependent connected-component types. -/
def IsRootedForestData {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) (attachments : Finset W) : Prop :=
  F.IsAcyclic ∧
    ∀ c : F.ConnectedComponent,
      ∃! v : W, v ∈ c ∧ v ∈ attachments

/-- Deleting the root of a finite tree produces valid rooted-forest data:
the away graph is acyclic, and every one of its components contains exactly
one recorded root neighbor. -/
theorem IsTree.isRootedForestData_rootedGraphData
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsTree) (root : V) :
    IsRootedForestData (awayGraph G root) (rootNeighborFinset G root) := by
  refine ⟨hG.isAcyclic.induce {v | v ≠ root}, ?_⟩
  intro c
  obtain ⟨v, hv, huv⟩ :=
    IsTree.existsUnique_adj_root_in_awayComponent hG root c
  refine ⟨v, ⟨hv.1, (mem_rootNeighborFinset G root v).2 hv.2⟩, ?_⟩
  intro w hw
  exact huv w ⟨hw.1, (mem_rootNeighborFinset G root w).1 hw.2⟩

/-- The root-neighbor finset of a tree is exactly the image of its canonical
child-root map. -/
theorem IsTree.rootNeighborFinset_eq_image_childRoot
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsTree) (root : V) :
    rootNeighborFinset G root =
      (Finset.univ : Finset (awayGraph G root).ConnectedComponent).image
        fun c => IsTree.childRoot hG root c := by
  classical
  ext v
  constructor
  · intro hv
    let c := (awayGraph G root).connectedComponentMk v
    have hvc : v ∈ c := ConnectedComponent.connectedComponentMk_mem
    have hvadj : G.Adj root v.1 :=
      (mem_rootNeighborFinset G root v).1 hv
    have heq : v = IsTree.childRoot hG root c :=
      IsTree.eq_childRoot_of_mem_of_adj hG root c v hvc hvadj
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, heq.symm⟩
  · intro hv
    obtain ⟨c, _hc, hcv⟩ := Finset.mem_image.mp hv
    rw [← hcv, mem_rootNeighborFinset]
    exact IsTree.adj_childRoot hG root c

/-- Products over root neighbors can be indexed without duplication by the
root-deleted connected components. -/
theorem IsTree.prod_rootNeighborFinset
    [Fintype V] [DecidableEq V] {R : Type*} [CommMonoid R]
    {G : SimpleGraph V} (hG : G.IsTree) (root : V)
    (weight : {v : V // v ≠ root} → R) :
    ∏ v ∈ rootNeighborFinset G root, weight v =
      ∏ c : (awayGraph G root).ConnectedComponent,
        weight (IsTree.childRoot hG root c) := by
  classical
  rw [IsTree.rootNeighborFinset_eq_image_childRoot hG root,
    Finset.prod_image]
  exact (IsTree.childRoot_injective hG root).injOn

/-- The star joining `root` to a prescribed finset of non-root vertices. -/
def rootStar [DecidableEq V] (root : V)
    (attachments : Finset {v : V // v ≠ root}) : SimpleGraph V where
  Adj v w :=
    (v = root ∧ ∃ hw : w ≠ root, (⟨w, hw⟩ : {x : V // x ≠ root}) ∈ attachments) ∨
    (w = root ∧ ∃ hv : v ≠ root, (⟨v, hv⟩ : {x : V // x ≠ root}) ∈ attachments)
  symm v w := by
    tauto
  loopless := ⟨by
    intro v
    rintro (⟨hvr, hv⟩ | ⟨hvr, hv⟩)
    · exact hv.choose hvr
    · exact hv.choose hvr⟩

@[simp]
theorem rootStar_adj_root_left [DecidableEq V] (root : V)
    (attachments : Finset {v : V // v ≠ root})
    (v : {v : V // v ≠ root}) :
    (rootStar root attachments).Adj root v.1 ↔ v ∈ attachments := by
  simp [rootStar, v.2]

@[simp]
theorem rootStar_adj_root_right [DecidableEq V] (root : V)
    (attachments : Finset {v : V // v ≠ root})
    (v : {v : V // v ≠ root}) :
    (rootStar root attachments).Adj v.1 root ↔ v ∈ attachments := by
  rw [SimpleGraph.adj_comm]
  exact rootStar_adj_root_left root attachments v

theorem rootStar_not_adj_of_ne_root [DecidableEq V] (root : V)
    (attachments : Finset {v : V // v ≠ root})
    {v w : V} (hv : v ≠ root) (hw : w ≠ root) :
    ¬(rootStar root attachments).Adj v w := by
  simp [rootStar, hv, hw]

/-- Reconstruct a graph from its graph away from `root` and its selected
root-neighbor finset. -/
def graphOfRootedData [DecidableEq V] (root : V)
    (F : SimpleGraph {v : V // v ≠ root})
    (attachments : Finset {v : V // v ≠ root}) : SimpleGraph V :=
  F.map (Function.Embedding.subtype fun v : V => v ≠ root) ⊔
    rootStar root attachments

/-- Reconstructing the deletion data of a graph returns the original graph.
Thus `rootedGraphData` is not only injective but has an explicit left inverse,
which is the form used by the finite orbit equivalence. -/
theorem graphOfRootedData_rootedGraphData [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) :
    graphOfRootedData root (awayGraph G root)
      (rootNeighborFinset G root) = G := by
  classical
  ext v w
  by_cases hvr : v = root
  · subst v
    by_cases hwr : w = root
    · subst w
      simp [graphOfRootedData]
    · let w' : {x : V // x ≠ root} := ⟨w, hwr⟩
      have hmap : ¬((awayGraph G root).map
          (Function.Embedding.subtype fun v : V => v ≠ root)).Adj root w := by
        rw [SimpleGraph.map_adj]
        rintro ⟨u, _v, _huv, hu, _hv⟩
        exact u.2 hu
      simp only [graphOfRootedData, SimpleGraph.sup_adj, hmap, false_or]
      simpa [w'] using
        ((rootStar_adj_root_left root (rootNeighborFinset G root) w').trans
          (mem_rootNeighborFinset G root w'))
  · by_cases hwr : w = root
    · subst w
      let v' : {x : V // x ≠ root} := ⟨v, hvr⟩
      have hmap : ¬((awayGraph G root).map
          (Function.Embedding.subtype fun v : V => v ≠ root)).Adj v root := by
        rw [SimpleGraph.map_adj]
        rintro ⟨_u, w, _huw, _hu, hw⟩
        exact w.2 hw
      simp only [graphOfRootedData, SimpleGraph.sup_adj, hmap, false_or]
      simpa [v', SimpleGraph.adj_comm] using
        ((rootStar_adj_root_right root (rootNeighborFinset G root) v').trans
          (mem_rootNeighborFinset G root v'))
    · have hstar := rootStar_not_adj_of_ne_root root
          (rootNeighborFinset G root) hvr hwr
      simp only [graphOfRootedData, SimpleGraph.sup_adj, hstar, or_false]
      rw [SimpleGraph.map_adj]
      constructor
      · rintro ⟨v', w', hvw, hv', hw'⟩
        subst v
        subst w
        exact hvw
      · intro hvw
        exact ⟨⟨v, hvr⟩, ⟨w, hwr⟩, hvw, rfl, rfl⟩

/-- Extracting root data after reconstruction recovers both pieces.  No tree
hypothesis is needed. -/
theorem rootedGraphData_graphOfRootedData [Fintype V] [DecidableEq V]
    (root : V) (F : SimpleGraph {v : V // v ≠ root})
    (attachments : Finset {v : V // v ≠ root}) :
    rootedGraphData (graphOfRootedData root F attachments) root =
      (F, attachments) := by
  apply Prod.ext
  · ext v w
    have hv : v.1 ≠ root := v.2
    have hw : w.1 ≠ root := w.2
    have hstar := rootStar_not_adj_of_ne_root root attachments hv hw
    change ((F.map (Function.Embedding.subtype fun x : V => x ≠ root) ⊔
      rootStar root attachments).Adj v.1 w.1 ↔ F.Adj v w)
    rw [SimpleGraph.sup_adj, or_iff_left hstar]
    exact SimpleGraph.map_adj_apply
  · ext v
    change v ∈ rootNeighborFinset
        (graphOfRootedData root F attachments) root ↔ v ∈ attachments
    rw [mem_rootNeighborFinset]
    have hmap : ¬(F.map
        (Function.Embedding.subtype fun x : V => x ≠ root)).Adj root v.1 := by
      rw [SimpleGraph.map_adj]
      rintro ⟨u, _w, _huw, hu, _hw⟩
      exact u.2 hu
    rw [graphOfRootedData, SimpleGraph.sup_adj, or_iff_right hmap,
      rootStar_adj_root_left]

/-- Finite graphs with a distinguished root are equivalent to an ordinary
graph on the complement together with a finset of root attachments.  This is
the finite, transport-free carrier equivalence used in the orbit count. -/
def rootedGraphEquiv [Fintype V] [DecidableEq V] (root : V) :
    SimpleGraph V ≃
      (SimpleGraph {v : V // v ≠ root} × Finset {v : V // v ≠ root}) where
  toFun G := rootedGraphData G root
  invFun D := graphOfRootedData root D.1 D.2
  left_inv G := graphOfRootedData_rootedGraphData G root
  right_inv D := by
    rcases D with ⟨F, attachments⟩
    exact rootedGraphData_graphOfRootedData root F attachments

end

end YangMills.Polymer
