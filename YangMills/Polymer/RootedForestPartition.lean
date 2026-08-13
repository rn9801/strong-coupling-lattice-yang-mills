/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.GraphExponential
import YangMills.Polymer.RootedForestEnumeration
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Exponential

/-!
# The unordered component code of a finite forest

Root deletion turns a tree into an unordered family of nonempty component
trees.  This file packages the lossless finite orbit map in a common ambient
type: a component is recorded by its vertex finset and its ambient edge
finset.  In particular, no transport between the varying connected-component
subtypes remains in the subsequent weighted enumeration.

This is a model-independent polymer/combinatorics module.
-/

namespace YangMills.Polymer

open SimpleGraph
open scoped BigOperators

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W]

local instance forestPartitionConnectedComponentFintype (F : SimpleGraph W) :
    Fintype F.ConnectedComponent := Fintype.ofFinite F.ConnectedComponent

/-- The vertices belonging to a connected component, in the ambient finite
vertex type. -/
def componentVertexFinset (F : SimpleGraph W)
    (c : F.ConnectedComponent) : Finset W := by
  classical
  exact Finset.univ.filter fun v => v ∈ c

@[simp]
theorem mem_componentVertexFinset (F : SimpleGraph W)
    (c : F.ConnectedComponent) (v : W) :
    v ∈ componentVertexFinset F c ↔ v ∈ c := by
  simp [componentVertexFinset]

/-- Whether an ambient unordered edge has both endpoints in a component. -/
def edgeInsideComponent (F : SimpleGraph W)
    (c : F.ConnectedComponent) : Sym2 W → Prop :=
  Sym2.lift ⟨fun v w => v ∈ c ∧ w ∈ c, by
    intro v w
    exact propext and_comm⟩

@[simp]
theorem edgeInsideComponent_mk (F : SimpleGraph W)
    (c : F.ConnectedComponent) (v w : W) :
    edgeInsideComponent F c s(v, w) ↔ v ∈ c ∧ w ∈ c :=
  Iff.rfl

/-- The ambient edge finset carried by one connected component. -/
def componentEdgeFinset (F : SimpleGraph W)
    (c : F.ConnectedComponent) : Finset (Sym2 W) := by
  classical
  exact (finiteEdges F).filter (edgeInsideComponent F c)

@[simp]
theorem mem_componentEdgeFinset (F : SimpleGraph W)
    (c : F.ConnectedComponent) (e : Sym2 W) :
    e ∈ componentEdgeFinset F c ↔
      e ∈ finiteEdges F ∧ edgeInsideComponent F c e := by
  simp [componentEdgeFinset]

/-- Common ambient representation of a connected component: its vertices and
its edges. -/
abbrev ForestComponentData (W : Type*) := Finset W × Finset (Sym2 W)

/-- Data belonging to one connected component. -/
def connectedComponentData (F : SimpleGraph W)
    (c : F.ConnectedComponent) : ForestComponentData W :=
  (componentVertexFinset F c, componentEdgeFinset F c)

/-- Different connected components have different common-ambient data. -/
theorem connectedComponentData_injective (F : SimpleGraph W) :
    Function.Injective (connectedComponentData F) := by
  intro c d hcd
  have hvertices : componentVertexFinset F c = componentVertexFinset F d :=
    congrArg Prod.fst hcd
  have hcout : c.out ∈ c := c.out_eq
  have hdout : c.out ∈ d := by
    rw [← mem_componentVertexFinset, ← hvertices,
      mem_componentVertexFinset]
    exact hcout
  exact ConnectedComponent.eq_of_common_vertex hcout hdout

/-- The unordered family of all component data of a finite graph. -/
def forestComponentData (F : SimpleGraph W) :
    Finset (ForestComponentData W) :=
  Finset.univ.image (connectedComponentData F)

@[simp]
theorem mem_forestComponentData (F : SimpleGraph W)
    (D : ForestComponentData W) :
    D ∈ forestComponentData F ↔
      ∃ c : F.ConnectedComponent, connectedComponentData F c = D := by
  simp [forestComponentData]

theorem card_forestComponentData (F : SimpleGraph W) :
    (forestComponentData F).card = Fintype.card F.ConnectedComponent := by
  classical
  rw [forestComponentData, Finset.card_image_iff.mpr
    (connectedComponentData_injective F).injOn]
  simp

/-- Every edge of a graph lies in the data of its (unique) connected
component. -/
theorem mem_finiteEdges_iff_exists_componentEdgeFinset
    (F : SimpleGraph W) (e : Sym2 W) :
    e ∈ finiteEdges F ↔
      ∃ c : F.ConnectedComponent, e ∈ componentEdgeFinset F c := by
  constructor
  · intro he
    have heF : e ∈ F.edgeSet := (mem_finiteEdges F e).mp he
    induction e using Sym2.inductionOn with
    | _ v w =>
        have hv : v ∈ F.connectedComponentMk v :=
          ConnectedComponent.connectedComponentMk_mem
        have hw : w ∈ F.connectedComponentMk v :=
          (F.connectedComponentMk v).mem_supp_of_adj_mem_supp hv
            ((SimpleGraph.mem_edgeSet F).mp heF)
        exact ⟨F.connectedComponentMk v,
          (mem_componentEdgeFinset F _ _).mpr
            ⟨he, (edgeInsideComponent_mk F _ v w).mpr ⟨hv, hw⟩⟩⟩
  · rintro ⟨c, hc⟩
    exact (mem_componentEdgeFinset F c e).mp hc |>.1

/-- The unordered component data remembers precisely the graph's finite edge
set. -/
theorem mem_finiteEdges_iff_exists_forestComponentData
    (F : SimpleGraph W) (e : Sym2 W) :
    e ∈ finiteEdges F ↔
      ∃ D ∈ forestComponentData F, e ∈ D.2 := by
  rw [mem_finiteEdges_iff_exists_componentEdgeFinset]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨connectedComponentData F c, by simp, hc⟩
  · rintro ⟨D, hD, heD⟩
    obtain ⟨c, rfl⟩ := (mem_forestComponentData F D).mp hD
    exact ⟨c, heD⟩

/-- The passage from a graph to its unordered common-ambient component data
is lossless. -/
theorem forestComponentData_injective :
    Function.Injective (forestComponentData (W := W)) := by
  intro F H hFH
  apply finiteEdges_inj
  ext e
  rw [mem_finiteEdges_iff_exists_forestComponentData,
    mem_finiteEdges_iff_exists_forestComponentData, hFH]

/-! ## Valid unordered tree-component families -/

/-- Graph carried by common-ambient component data, restricted to the
recorded vertex finset. -/
def forestComponentGraph (D : ForestComponentData W) :
    SimpleGraph {v : W // v ∈ D.1} :=
  (SimpleGraph.fromEdgeSet (D.2 : Set (Sym2 W))).induce (D.1 : Set W)

/-- The canonical equivalence between the finite support recorded in a
component datum and Mathlib's connected-component support subtype. -/
def componentVertexEquiv (F : SimpleGraph W) (c : F.ConnectedComponent) :
    {v : W // v ∈ componentVertexFinset F c} ≃ ↑c where
  toFun v := ⟨v.1, (mem_componentVertexFinset F c v.1).mp v.2⟩
  invFun v := ⟨v.1, (mem_componentVertexFinset F c v.1).mpr v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The graph reconstructed from a genuine component datum is isomorphic to
Mathlib's induced graph on that connected component. -/
def connectedComponentDataIso (F : SimpleGraph W)
    (c : F.ConnectedComponent) :
    forestComponentGraph (connectedComponentData F c) ≃g c.toSimpleGraph where
  toEquiv := componentVertexEquiv F c
  map_rel_iff' := by
    intro v w
    change
      F.Adj v.1 w.1 ↔
        (s(v.1, w.1) ∈ componentEdgeFinset F c ∧ v.1 ≠ w.1)
    constructor
    · intro h
      have hv : v.1 ∈ c :=
        (mem_componentVertexFinset F c v.1).mp v.2
      have hw : w.1 ∈ c :=
        (mem_componentVertexFinset F c w.1).mp w.2
      refine ⟨(mem_componentEdgeFinset F c _).mpr ⟨?_, ?_⟩,
        h.ne⟩
      · exact (mem_finiteEdges F _).mpr
          ((SimpleGraph.mem_edgeSet F).mpr h)
      · exact (edgeInsideComponent_mk F c v.1 w.1).mpr ⟨hv, hw⟩
    · intro h
      exact (SimpleGraph.mem_edgeSet F).mp <|
        (mem_finiteEdges F _).mp
          ((mem_componentEdgeFinset F c _).mp h.1).1

/-- Both endpoints of an ambient unordered edge lie in a finset. -/
def edgeInsideFinset (b : Finset W) : Sym2 W → Prop :=
  Sym2.lift ⟨fun v w => v ∈ b ∧ w ∈ b, by
    intro v w
    exact propext and_comm⟩

@[simp]
theorem edgeInsideFinset_mk (b : Finset W) (v w : W) :
    edgeInsideFinset b s(v, w) ↔ v ∈ b ∧ w ∈ b :=
  Iff.rfl

/-- A common-ambient datum describes a nonempty tree below `G`. -/
def IsTreeComponentDataBelow (G : SimpleGraph W)
    (D : ForestComponentData W) : Prop :=
  D.1.Nonempty ∧
    D.2 ⊆ finiteEdges G ∧
    (∀ e ∈ D.2, edgeInsideFinset D.1 e) ∧
    (forestComponentGraph D).IsTree

/-- Every connected-component datum of an acyclic subgraph below `G` is a
valid tree datum below `G`. -/
theorem IsAcyclic.isTreeComponentDataBelow
    {F G : SimpleGraph W} (hF : F.IsAcyclic) (hFG : F ≤ G)
    (c : F.ConnectedComponent) :
    IsTreeComponentDataBelow G (connectedComponentData F c) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨c.out, (mem_componentVertexFinset F c c.out).mpr c.out_eq⟩
  · intro e he
    have heF := (mem_componentEdgeFinset F c e).mp he |>.1
    apply (mem_finiteEdges G e).mpr
    exact SimpleGraph.edgeSet_mono hFG ((mem_finiteEdges F e).mp heF)
  · intro e he
    have hins := (mem_componentEdgeFinset F c e).mp he |>.2
    induction e using Sym2.inductionOn with
    | _ v w =>
        have h := (edgeInsideComponent_mk F c v w).mp hins
        exact (edgeInsideFinset_mk (componentVertexFinset F c) v w).mpr
          ⟨(mem_componentVertexFinset F c v).mpr h.1,
            (mem_componentVertexFinset F c w).mpr h.2⟩
  · exact (connectedComponentDataIso F c).isTree_iff.mpr
      (hF.isTree_connectedComponent c)

/-- Finite collection of all valid component-tree data below `G`. -/
def treeComponentDataBelow (G : SimpleGraph W) :
    Finset (ForestComponentData W) := by
  classical
  exact Finset.univ.filter (IsTreeComponentDataBelow G)

@[simp]
theorem mem_treeComponentDataBelow (G : SimpleGraph W)
    (D : ForestComponentData W) :
    D ∈ treeComponentDataBelow G ↔ IsTreeComponentDataBelow G D := by
  classical
  simp [treeComponentDataBelow]

/-- Valid component-tree data with one allowed parent-attachment vertex
distinguished. -/
def rootedTreeComponentChoices (G : SimpleGraph W) (allowed : Finset W) :
    Finset (ForestComponentData W × W) := by
  classical
  exact ((treeComponentDataBelow G).product allowed).filter fun p =>
    p.2 ∈ p.1.1

@[simp]
theorem mem_rootedTreeComponentChoices (G : SimpleGraph W)
    (allowed : Finset W) (p : ForestComponentData W × W) :
    p ∈ rootedTreeComponentChoices G allowed ↔
      p.1 ∈ treeComponentDataBelow G ∧ p.2 ∈ allowed ∧ p.2 ∈ p.1.1 := by
  classical
  simp [rootedTreeComponentChoices, and_assoc]

/-- Valid unordered families of disjoint component trees covering the whole
ambient vertex type. -/
def treeComponentFamiliesBelow (G : SimpleGraph W) :
    Finset (Finset (ForestComponentData W)) := by
  classical
  exact (treeComponentDataBelow G).powerset.filter fun family =>
    ((family : Set (ForestComponentData W)).Pairwise
        fun D E => Disjoint D.1 E.1) ∧
      family.biUnion Prod.fst = Finset.univ

/-- Component vertex finsets of a graph are pairwise disjoint. -/
theorem forestComponentData_pairwise_disjoint (F : SimpleGraph W) :
    (forestComponentData F : Set (ForestComponentData W)).Pairwise
      fun D E => Disjoint D.1 E.1 := by
  intro D hD E hE hDE
  obtain ⟨c, rfl⟩ := (mem_forestComponentData F D).mp hD
  obtain ⟨d, rfl⟩ := (mem_forestComponentData F E).mp hE
  have hcd : c ≠ d := by
    intro h
    apply hDE
    rw [h]
  apply Finset.disjoint_left.mpr
  intro v hvc hvd
  apply hcd
  exact ConnectedComponent.eq_of_common_vertex
    ((mem_componentVertexFinset F c v).mp hvc)
    ((mem_componentVertexFinset F d v).mp hvd)

/-- Component vertex finsets cover the whole finite vertex type. -/
theorem biUnion_forestComponentData_fst (F : SimpleGraph W) :
    (forestComponentData F).biUnion Prod.fst = Finset.univ := by
  classical
  ext v
  constructor
  · intro _
    exact Finset.mem_univ v
  · intro _
    apply Finset.mem_biUnion.mpr
    let c := F.connectedComponentMk v
    refine ⟨connectedComponentData F c, ?_, ?_⟩
    · simp [c]
    · exact (mem_componentVertexFinset F c v).mpr
        ConnectedComponent.connectedComponentMk_mem

/-- The unordered component code of every acyclic subgraph below `G` is a
valid tree-component family below `G`. -/
theorem forestComponentData_mem_treeComponentFamiliesBelow
    {F G : SimpleGraph W} (hF : F.IsAcyclic) (hFG : F ≤ G) :
    forestComponentData F ∈ treeComponentFamiliesBelow G := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ?_, ?_,
    biUnion_forestComponentData_fst F⟩
  · intro D hD
    obtain ⟨c, rfl⟩ := (mem_forestComponentData F D).mp hD
    exact (mem_treeComponentDataBelow G _).mpr
      (IsAcyclic.isTreeComponentDataBelow hF hFG c)
  · exact forestComponentData_pairwise_disjoint F

/-- Acyclic spanning subgraphs below a finite ambient graph. -/
def spanningForestGraphsBelow (G : SimpleGraph W) :
    Finset (SimpleGraph W) := by
  classical
  exact Finset.univ.filter fun F => F ≤ G ∧ F.IsAcyclic

@[simp]
theorem mem_spanningForestGraphsBelow (G F : SimpleGraph W) :
    F ∈ spanningForestGraphsBelow G ↔ F ≤ G ∧ F.IsAcyclic := by
  classical
  simp [spanningForestGraphsBelow]

/-- The image of the finite forest enumeration is contained in the valid
unordered tree-family enumeration. -/
theorem image_forestComponentData_subset_treeComponentFamiliesBelow
    (G : SimpleGraph W) :
    (spanningForestGraphsBelow G).image forestComponentData ⊆
      treeComponentFamiliesBelow G := by
  classical
  intro family hfamily
  obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hfamily
  have hdata := (mem_spanningForestGraphsBelow G F).mp hF
  exact forestComponentData_mem_treeComponentFamiliesBelow hdata.2 hdata.1

/-- Regrouping a finite weighted graph sum by its unordered component code is
exact. -/
theorem sum_image_forestComponentData
    {R : Type*} [AddCommMonoid R]
    (graphs : Finset (SimpleGraph W))
    (weight : Finset (ForestComponentData W) → R) :
    ∑ F ∈ graphs, weight (forestComponentData F) =
      ∑ D ∈ graphs.image forestComponentData, weight D := by
  classical
  rw [Finset.sum_image forestComponentData_injective.injOn]

/-- Weighted finite forest-to-unordered-family bound.  This is the exact
orbit reindexing followed only by enlargement to all valid component-tree
families; no labelled graph or symmetry multiplicity is discarded. -/
theorem sum_spanningForestGraphsBelow_le_sum_treeComponentFamiliesBelow
    (G : SimpleGraph W)
    (weight : Finset (ForestComponentData W) → ℝ)
    (hweight : ∀ family, 0 ≤ weight family) :
    ∑ F ∈ spanningForestGraphsBelow G,
        weight (forestComponentData F) ≤
      ∑ family ∈ treeComponentFamiliesBelow G, weight family := by
  classical
  calc
    ∑ F ∈ spanningForestGraphsBelow G,
        weight (forestComponentData F) =
      ∑ family ∈ (spanningForestGraphsBelow G).image forestComponentData,
        weight family :=
      sum_image_forestComponentData (spanningForestGraphsBelow G) weight
    _ ≤ ∑ family ∈ treeComponentFamiliesBelow G, weight family :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (image_forestComponentData_subset_treeComponentFamiliesBelow G)
        (fun family _ _ => hweight family)

/-- The earlier root-complement forest enumeration is the generic forest
enumeration below the induced ambient graph. -/
theorem spanningForestGraphsAway_eq_spanningForestGraphsBelow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) :
    spanningForestGraphsAway G root =
      spanningForestGraphsBelow (awayGraph G root) := by
  classical
  ext F
  simp

/-- Weighted unordered-component bound in the root-deleted form consumed by
the Mayer tree decomposition. -/
theorem sum_spanningForestGraphsAway_le_sum_treeComponentFamiliesBelow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V)
    (weight : Finset (ForestComponentData {v : V // v ≠ root}) → ℝ)
    (hweight : ∀ family, 0 ≤ weight family) :
    ∑ F ∈ spanningForestGraphsAway G root,
        weight (forestComponentData F) ≤
      ∑ family ∈ treeComponentFamiliesBelow (awayGraph G root),
        weight family := by
  rw [spanningForestGraphsAway_eq_spanningForestGraphsBelow]
  exact sum_spanningForestGraphsBelow_le_sum_treeComponentFamiliesBelow
    (awayGraph G root) weight hweight

/-- Valid disjoint covering families are, in particular, arbitrary subsets of
the finite component-tree collection. -/
theorem treeComponentFamiliesBelow_subset_powerset (G : SimpleGraph W) :
    treeComponentFamiliesBelow G ⊆ (treeComponentDataBelow G).powerset := by
  classical
  intro family hfamily
  exact (Finset.mem_filter.mp hfamily).1

/-- The weighted unordered component-family enumeration is controlled by the
finite labelled-set exponential.  This is the precise tree-family analogue
of the `exp` appearing in the KP recursion. -/
theorem sum_treeComponentFamiliesBelow_prod_le_exp_sum
    (G : SimpleGraph W) (weight : ForestComponentData W → ℝ)
    (hweight : ∀ D, 0 ≤ weight D) :
    ∑ family ∈ treeComponentFamiliesBelow G,
        ∏ D ∈ family, weight D ≤
      Real.exp (∑ D ∈ treeComponentDataBelow G, weight D) := by
  classical
  calc
    ∑ family ∈ treeComponentFamiliesBelow G,
        ∏ D ∈ family, weight D ≤
      ∑ family ∈ (treeComponentDataBelow G).powerset,
        ∏ D ∈ family, weight D :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (treeComponentFamiliesBelow_subset_powerset G)
        (fun family _ _ => Finset.prod_nonneg fun D _ => hweight D)
    _ = ∏ D ∈ treeComponentDataBelow G, (1 + weight D) := by
      rw [Finset.prod_one_add]
    _ ≤ Real.exp (∑ D ∈ treeComponentDataBelow G, weight D) :=
      Real.prod_one_add_le_exp_sum _ hweight

/-! ## Composing component families with root attachments -/

/-- Total allowed root-attachment mass carried by common-ambient component
data. -/
def componentDataAttachmentMass (allowed : Finset W) (weight : W → ℝ)
    (D : ForestComponentData W) : ℝ :=
  ∑ v ∈ D.1.filter (· ∈ allowed), weight v

/-- Multiplicative vertex weight carried by component data. -/
def componentDataVertexWeight (weight : W → ℝ)
    (D : ForestComponentData W) : ℝ :=
  ∏ v ∈ D.1, weight v

/-- Full rooted component-tree weight: one allowed attachment mass times all
vertex weights in the component. -/
def componentDataRootedTreeWeight (allowed : Finset W)
    (attachmentWeight vertexWeight : W → ℝ)
    (D : ForestComponentData W) : ℝ :=
  componentDataAttachmentMass allowed attachmentWeight D *
    componentDataVertexWeight vertexWeight D

theorem componentDataAttachmentMass_nonneg
    (allowed : Finset W) (weight : W → ℝ)
    (hweight : ∀ v, 0 ≤ weight v) (D : ForestComponentData W) :
    0 ≤ componentDataAttachmentMass allowed weight D := by
  exact Finset.sum_nonneg fun v _ => hweight v

theorem componentDataRootedTreeWeight_nonneg
    (allowed : Finset W) (attachmentWeight vertexWeight : W → ℝ)
    (hattach : ∀ v, 0 ≤ attachmentWeight v)
    (hvertex : ∀ v, 0 ≤ vertexWeight v)
    (D : ForestComponentData W) :
    0 ≤ componentDataRootedTreeWeight allowed attachmentWeight
      vertexWeight D := by
  exact mul_nonneg
    (componentDataAttachmentMass_nonneg allowed attachmentWeight hattach D)
    (Finset.prod_nonneg fun v _ => hvertex v)

/-- Distinguishing the attachment vertex turns the component attachment mass
into an ordinary finite sum over rooted component-tree choices. -/
theorem sum_componentDataRootedTreeWeight_one_eq_sum_rootedChoices
    (G : SimpleGraph W) (allowed : Finset W)
    (vertexWeight : W → ℝ) :
    ∑ D ∈ treeComponentDataBelow G,
        componentDataRootedTreeWeight allowed (fun _ => 1)
          vertexWeight D =
      ∑ p ∈ rootedTreeComponentChoices G allowed,
        componentDataVertexWeight vertexWeight p.1 := by
  classical
  rw [rootedTreeComponentChoices]
  calc
    ∑ D ∈ treeComponentDataBelow G,
        componentDataRootedTreeWeight allowed (fun _ => 1)
          vertexWeight D =
      ∑ D ∈ treeComponentDataBelow G,
        ∑ v ∈ allowed.filter (· ∈ D.1),
          componentDataVertexWeight vertexWeight D := by
      apply Finset.sum_congr rfl
      intro D _
      rw [componentDataRootedTreeWeight,
        componentDataAttachmentMass]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcard :
          (D.1.filter (· ∈ allowed)).card =
            (allowed.filter (· ∈ D.1)).card := by
        congr 1
        ext v
        simp [and_comm]
      rw [hcard]
      ring
    _ = ∑ p ∈ ((treeComponentDataBelow G).product allowed).filter
          (fun p => p.2 ∈ p.1.1),
        componentDataVertexWeight vertexWeight p.1 := by
      rw [Finset.sum_filter]
      symm
      calc
        ∑ p ∈ (treeComponentDataBelow G).product allowed,
            (if p.2 ∈ p.1.1 then
              componentDataVertexWeight vertexWeight p.1 else 0) =
          ∑ D ∈ treeComponentDataBelow G,
            ∑ v ∈ allowed,
              (if v ∈ D.1 then componentDataVertexWeight vertexWeight D
              else 0) := by
          exact Finset.sum_product _ _ _
        _ = ∑ D ∈ treeComponentDataBelow G,
            ∑ v ∈ allowed.filter (· ∈ D.1),
              componentDataVertexWeight vertexWeight D := by
          apply Finset.sum_congr rfl
          intro D _
          rw [Finset.sum_filter]

/-- On a genuine connected component, the common-ambient attachment mass is
exactly the earlier component-choice sum. -/
theorem componentDataAttachmentMass_connectedComponentData
    (F : SimpleGraph W) (allowed : Finset W) (weight : W → ℝ)
    (c : F.ConnectedComponent) :
    componentDataAttachmentMass allowed weight
        (connectedComponentData F c) =
      ∑ v ∈ componentAttachmentChoices F allowed c, weight v := by
  classical
  apply Finset.sum_congr
  · ext v
    simp [connectedComponentData,
      componentAttachmentChoices, and_comm]
  · intro v _
    rfl

/-- Products of attachment masses over connected components agree with
products over the unordered common-ambient component code. -/
theorem prod_componentDataAttachmentMass_forestComponentData
    (F : SimpleGraph W) (allowed : Finset W) (weight : W → ℝ) :
    ∏ D ∈ forestComponentData F,
        componentDataAttachmentMass allowed weight D =
      ∏ c : F.ConnectedComponent,
        ∑ v ∈ componentAttachmentChoices F allowed c, weight v := by
  classical
  rw [forestComponentData,
    Finset.prod_image (connectedComponentData_injective F).injOn]
  apply Finset.prod_congr rfl
  intro c _
  exact componentDataAttachmentMass_connectedComponentData
    F allowed weight c

/-- The component vertex products multiply to the product over the complete
finite vertex type. -/
theorem prod_componentDataVertexWeight_forestComponentData
    (F : SimpleGraph W) (weight : W → ℝ) :
    ∏ D ∈ forestComponentData F, componentDataVertexWeight weight D =
      ∏ v : W, weight v := by
  classical
  rw [forestComponentData,
    Finset.prod_image (connectedComponentData_injective F).injOn]
  change (∏ c : F.ConnectedComponent,
      ∏ v ∈ componentVertexFinset F c, weight v) = _
  calc
    (∏ c : F.ConnectedComponent,
        ∏ v ∈ componentVertexFinset F c, weight v) =
      ∏ c : F.ConnectedComponent, ∏ v : ↑c, weight v.1 := by
        apply Finset.prod_congr rfl
        intro c _
        rw [← Finset.prod_subtype (componentVertexFinset F c)
          (by simp) weight]
    _ = ∏ v : W, weight v := by
      rw [← Fintype.prod_sigma']
      exact Fintype.prod_equiv (connectedComponentVertexEquiv F)
        (fun x => weight x.2.1) weight (fun _ => rfl)

/-- Product factorization for the full rooted component-tree weight. -/
theorem prod_componentDataRootedTreeWeight_forestComponentData
    (F : SimpleGraph W) (allowed : Finset W)
    (attachmentWeight vertexWeight : W → ℝ) :
    ∏ D ∈ forestComponentData F,
        componentDataRootedTreeWeight allowed attachmentWeight
          vertexWeight D =
      (∏ v : W, vertexWeight v) *
        ∏ c : F.ConnectedComponent,
          ∑ v ∈ componentAttachmentChoices F allowed c,
            attachmentWeight v := by
  classical
  rw [show (∏ D ∈ forestComponentData F,
      componentDataRootedTreeWeight allowed attachmentWeight
        vertexWeight D) =
      (∏ D ∈ forestComponentData F,
        componentDataAttachmentMass allowed attachmentWeight D) *
      ∏ D ∈ forestComponentData F,
        componentDataVertexWeight vertexWeight D by
          simp only [componentDataRootedTreeWeight]
          rw [Finset.prod_mul_distrib]]
  rw [prod_componentDataAttachmentMass_forestComponentData,
    prod_componentDataVertexWeight_forestComponentData]
  ring

/-- Complete finite rooted-tree combinatorial bound.  Root deletion, valid
component attachments, unordered component trees, and the labelled-set
exponential are composed in a single theorem. -/
theorem sum_rootedForestData_attachment_prod_le_exp_componentDataMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V)
    (attachmentWeight : {v : V // v ≠ root} → ℝ)
    (hweight : ∀ v, 0 ≤ attachmentWeight v) :
    ∑ D ∈ rootedForestDataFinset G root,
        ∏ v ∈ D.2, attachmentWeight v ≤
      Real.exp
        (∑ D ∈ treeComponentDataBelow (awayGraph G root),
          componentDataAttachmentMass (rootNeighborFinset G root)
            attachmentWeight D) := by
  classical
  let familyWeight :
      Finset (ForestComponentData {v : V // v ≠ root}) → ℝ :=
    fun family => ∏ D ∈ family,
      componentDataAttachmentMass (rootNeighborFinset G root)
        attachmentWeight D
  have hfamilyWeight : ∀ family, 0 ≤ familyWeight family := by
    intro family
    exact Finset.prod_nonneg fun D _ =>
      componentDataAttachmentMass_nonneg _ _ hweight D
  calc
    ∑ D ∈ rootedForestDataFinset G root,
        ∏ v ∈ D.2, attachmentWeight v =
      ∑ F ∈ spanningForestGraphsAway G root,
        ∏ c : F.ConnectedComponent,
          ∑ v ∈ componentAttachmentChoices F
            (rootNeighborFinset G root) c, attachmentWeight v := by
      simpa using
        (sum_rootedForestData_eq_sum_forest_prod_component
          G root (fun _ => (1 : ℝ)) attachmentWeight)
    _ = ∑ F ∈ spanningForestGraphsAway G root,
        familyWeight (forestComponentData F) := by
      apply Finset.sum_congr rfl
      intro F _
      exact (prod_componentDataAttachmentMass_forestComponentData F
        (rootNeighborFinset G root) attachmentWeight).symm
    _ ≤ ∑ family ∈ treeComponentFamiliesBelow (awayGraph G root),
        familyWeight family :=
      sum_spanningForestGraphsAway_le_sum_treeComponentFamiliesBelow
        G root familyWeight hfamilyWeight
    _ ≤ Real.exp
        (∑ D ∈ treeComponentDataBelow (awayGraph G root),
          componentDataAttachmentMass (rootNeighborFinset G root)
            attachmentWeight D) :=
      sum_treeComponentFamiliesBelow_prod_le_exp_sum
        (awayGraph G root)
        (componentDataAttachmentMass (rootNeighborFinset G root)
          attachmentWeight)
        (fun D => componentDataAttachmentMass_nonneg _ _ hweight D)

/-- Vertex-weighted form of the complete finite rooted-tree bound.  This is
the form used for activity monomials in the Mayer majorant. -/
theorem sum_rootedForestData_vertex_attachment_prod_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V)
    (attachmentWeight vertexWeight : {v : V // v ≠ root} → ℝ)
    (hattach : ∀ v, 0 ≤ attachmentWeight v)
    (hvertex : ∀ v, 0 ≤ vertexWeight v) :
    ∑ D ∈ rootedForestDataFinset G root,
        (∏ v : {v : V // v ≠ root}, vertexWeight v) *
          ∏ v ∈ D.2, attachmentWeight v ≤
      Real.exp
        (∑ D ∈ treeComponentDataBelow (awayGraph G root),
          componentDataRootedTreeWeight (rootNeighborFinset G root)
            attachmentWeight vertexWeight D) := by
  classical
  let familyWeight :
      Finset (ForestComponentData {v : V // v ≠ root}) → ℝ :=
    fun family => ∏ D ∈ family,
      componentDataRootedTreeWeight (rootNeighborFinset G root)
        attachmentWeight vertexWeight D
  have hfamilyWeight : ∀ family, 0 ≤ familyWeight family := by
    intro family
    exact Finset.prod_nonneg fun D _ =>
      componentDataRootedTreeWeight_nonneg _ _ _ hattach hvertex D
  calc
    ∑ D ∈ rootedForestDataFinset G root,
        (∏ v : {v : V // v ≠ root}, vertexWeight v) *
          ∏ v ∈ D.2, attachmentWeight v =
      ∑ F ∈ spanningForestGraphsAway G root,
        (∏ v : {v : V // v ≠ root}, vertexWeight v) *
          ∏ c : F.ConnectedComponent,
            ∑ v ∈ componentAttachmentChoices F
              (rootNeighborFinset G root) c, attachmentWeight v := by
      simpa using
        (sum_rootedForestData_eq_sum_forest_prod_component
          G root (fun _ => ∏ v : {v : V // v ≠ root}, vertexWeight v)
            attachmentWeight)
    _ = ∑ F ∈ spanningForestGraphsAway G root,
        familyWeight (forestComponentData F) := by
      apply Finset.sum_congr rfl
      intro F _
      exact (prod_componentDataRootedTreeWeight_forestComponentData F
        (rootNeighborFinset G root) attachmentWeight vertexWeight).symm
    _ ≤ ∑ family ∈ treeComponentFamiliesBelow (awayGraph G root),
        familyWeight family :=
      sum_spanningForestGraphsAway_le_sum_treeComponentFamiliesBelow
        G root familyWeight hfamilyWeight
    _ ≤ Real.exp
        (∑ D ∈ treeComponentDataBelow (awayGraph G root),
          componentDataRootedTreeWeight (rootNeighborFinset G root)
            attachmentWeight vertexWeight D) :=
      sum_treeComponentFamiliesBelow_prod_le_exp_sum
        (awayGraph G root)
        (componentDataRootedTreeWeight (rootNeighborFinset G root)
          attachmentWeight vertexWeight)
        (fun D => componentDataRootedTreeWeight_nonneg _ _ _
          hattach hvertex D)

/-- Fixed-root spanning-tree enumeration controlled by the unordered
component-tree exponential.  The left side is the exact number of spanning
trees times the residual vertex-weight monomial. -/
theorem card_spanningTreeGraphs_mul_prod_away_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V)
    (vertexWeight : {v : V // v ≠ root} → ℝ)
    (hvertex : ∀ v, 0 ≤ vertexWeight v) :
    ((spanningTreeGraphs G).card : ℝ) *
        (∏ v : {v : V // v ≠ root}, vertexWeight v) ≤
      Real.exp
        (∑ D ∈ treeComponentDataBelow (awayGraph G root),
          componentDataRootedTreeWeight (rootNeighborFinset G root)
            (fun _ => 1) vertexWeight D) := by
  classical
  let residualWeight : ℝ :=
    ∏ v : {v : V // v ≠ root}, vertexWeight v
  have hresidual : 0 ≤ residualWeight :=
    Finset.prod_nonneg fun v _ => hvertex v
  calc
    ((spanningTreeGraphs G).card : ℝ) * residualWeight =
      ∑ T ∈ spanningTreeGraphs G,
        residualWeight := by simp
    _ ≤ ∑ D ∈ rootedForestDataFinset G root,
        residualWeight :=
      sum_spanningTreeGraphs_rootedData_le_sum_rootedForestData
        G root (fun _ => residualWeight) (fun _ => hresidual)
    _ = ∑ D ∈ rootedForestDataFinset G root,
        residualWeight * ∏ _v ∈ D.2, (1 : ℝ) := by simp
    _ ≤ Real.exp
        (∑ D ∈ treeComponentDataBelow (awayGraph G root),
          componentDataRootedTreeWeight (rootNeighborFinset G root)
            (fun _ => 1) vertexWeight D) := by
      exact sum_rootedForestData_vertex_attachment_prod_le_exp
        G root (fun _ => 1) vertexWeight (fun _ => zero_le_one) hvertex

/-- Equivalent fixed-root bound with the exponent written as an ordinary sum
over component trees with a distinguished allowed attachment vertex. -/
theorem card_spanningTreeGraphs_mul_prod_away_le_exp_rootedChoices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V)
    (vertexWeight : {v : V // v ≠ root} → ℝ)
    (hvertex : ∀ v, 0 ≤ vertexWeight v) :
    ((spanningTreeGraphs G).card : ℝ) *
        (∏ v : {v : V // v ≠ root}, vertexWeight v) ≤
      Real.exp
        (∑ p ∈ rootedTreeComponentChoices (awayGraph G root)
            (rootNeighborFinset G root),
          componentDataVertexWeight vertexWeight p.1) := by
  have h := card_spanningTreeGraphs_mul_prod_away_le_exp
    G root vertexWeight hvertex
  rw [sum_componentDataRootedTreeWeight_one_eq_sum_rootedChoices] at h
  exact h

/-- Acyclicity turns every member of the unordered component family into an
actual tree (on the canonical connected-component subtype). -/
theorem IsAcyclic.componentData_isTree
    {F : SimpleGraph W} (hF : F.IsAcyclic)
    (c : F.ConnectedComponent) : c.toSimpleGraph.IsTree :=
  hF.isTree_connectedComponent c

end

end YangMills.Polymer
