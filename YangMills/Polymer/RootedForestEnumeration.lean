/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.RootedTreeDecomposition
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Real.Basic

/-!
# Enumerating root attachments of a finite forest

For a fixed finite forest, choosing exactly one root attachment in every
connected component is an ordinary finite Cartesian product.  This file
packages the corresponding bijection without dependent component transports:
the chosen function is sent to its finset image, and disjointness of connected
components makes that map injective.

This is the finite-product half of the rooted-tree orbit enumeration used by
the Kotecky--Preiss summation.
-/

namespace YangMills.Polymer

open SimpleGraph
open scoped BigOperators

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W]

local instance rootedForestConnectedComponentFintype (F : SimpleGraph W) :
    Fintype F.ConnectedComponent := Fintype.ofFinite F.ConnectedComponent

local instance rootedForestConnectedComponentDecidableEq (F : SimpleGraph W) :
    DecidableEq F.ConnectedComponent := Classical.decEq _

local instance rootedForestComponentSupportFintype (F : SimpleGraph W)
    (c : F.ConnectedComponent) : Fintype ↑c := Fintype.ofFinite ↑c

/-- Allowed attachment vertices lying in one connected component. -/
def componentAttachmentChoices (F : SimpleGraph W) (allowed : Finset W)
    (c : F.ConnectedComponent) : Finset W := by
  classical
  exact allowed.filter fun v => v ∈ c

@[simp]
theorem mem_componentAttachmentChoices (F : SimpleGraph W)
    (allowed : Finset W) (c : F.ConnectedComponent) (v : W) :
    v ∈ componentAttachmentChoices F allowed c ↔
      v ∈ allowed ∧ v ∈ c := by
  simp [componentAttachmentChoices]

/-- A componentwise attachment sum may be completed to the whole component
when the weight vanishes at disallowed vertices. -/
theorem sum_componentAttachmentChoices_eq_sum_component
    {R : Type*} [AddCommMonoid R]
    (F : SimpleGraph W) (allowed : Finset W)
    (c : F.ConnectedComponent) (weight : W → R)
    (hzero : ∀ v, v ∈ c → v ∉ allowed → weight v = 0) :
    ∑ v ∈ componentAttachmentChoices F allowed c, weight v =
      ∑ v : ↑c, weight v.1 := by
  classical
  rw [← Finset.sum_subtype
    ((Finset.univ : Finset W).filter fun v => v ∈ c) (by simp) weight]
  apply Finset.sum_subset
  · intro v hv
    have hvmem := (mem_componentAttachmentChoices F allowed c v).mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvmem.2⟩
  · intro v hvlarge hvsmall
    have hvc : v ∈ c := (Finset.mem_filter.mp hvlarge).2
    have hvnot : v ∉ allowed := by
      intro hvallowed
      exact hvsmall <| (mem_componentAttachmentChoices F allowed c v).mpr
        ⟨hvallowed, hvc⟩
    exact hzero v hvc hvnot

/-- Cartesian product of one allowed attachment choice per component. -/
def componentAttachmentFunctions (F : SimpleGraph W)
    (allowed : Finset W) :
    Finset (∀ c ∈ (Finset.univ : Finset F.ConnectedComponent), W) := by
  classical
  exact (Finset.univ : Finset F.ConnectedComponent).pi
    (componentAttachmentChoices F allowed)

/-- Forget the component index of a choice function and retain its image as a
finset of attachment vertices. -/
def componentAttachmentImage (F : SimpleGraph W)
    (f : ∀ c ∈ (Finset.univ : Finset F.ConnectedComponent), W) : Finset W := by
  classical
  exact (Finset.univ : Finset F.ConnectedComponent).image
    fun c => f c (Finset.mem_univ c)

/-- Attachment finsets that lie in `allowed` and meet every connected
component in exactly one vertex. -/
def validComponentAttachmentFinsets (F : SimpleGraph W)
    (allowed : Finset W) : Finset (Finset W) := by
  classical
  exact allowed.powerset.filter fun attachments =>
    ∀ c : F.ConnectedComponent,
      ∃! v : W, v ∈ c ∧ v ∈ attachments

theorem componentAttachmentImage_subset_allowed
    (F : SimpleGraph W) (allowed : Finset W)
    {f : ∀ c ∈ (Finset.univ : Finset F.ConnectedComponent), W}
    (hf : f ∈ componentAttachmentFunctions F allowed) :
    componentAttachmentImage F f ⊆ allowed := by
  intro v hv
  obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp hv
  exact (mem_componentAttachmentChoices F allowed c _).mp
    ((Finset.mem_pi.mp hf) c (Finset.mem_univ c)) |>.1

theorem componentAttachmentImage_existsUnique
    (F : SimpleGraph W) (allowed : Finset W)
    {f : ∀ c ∈ (Finset.univ : Finset F.ConnectedComponent), W}
    (hf : f ∈ componentAttachmentFunctions F allowed)
    (c : F.ConnectedComponent) :
    ∃! v : W, v ∈ c ∧ v ∈ componentAttachmentImage F f := by
  let v := f c (Finset.mem_univ c)
  have hvc : v ∈ c :=
    (mem_componentAttachmentChoices F allowed c v).mp
      ((Finset.mem_pi.mp hf) c (Finset.mem_univ c)) |>.2
  refine ⟨v, ⟨hvc, Finset.mem_image.mpr
    ⟨c, Finset.mem_univ c, rfl⟩⟩, ?_⟩
  intro w hw
  obtain ⟨d, _hd, hdw⟩ := Finset.mem_image.mp hw.2
  have hwd : w ∈ d := by
    rw [← hdw]
    exact (mem_componentAttachmentChoices F allowed d _).mp
      ((Finset.mem_pi.mp hf) d (Finset.mem_univ d)) |>.2
  have hcd : c = d := ConnectedComponent.eq_of_common_vertex hw.1 hwd
  calc
    w = f d (Finset.mem_univ d) := hdw.symm
    _ = f c (Finset.mem_univ c) := by rw [hcd]
    _ = v := rfl

/-- Choice functions have distinct attachment images.  The crucial point is
that values belonging to different components cannot coincide. -/
theorem componentAttachmentImage_injOn (F : SimpleGraph W)
    (allowed : Finset W) :
    Set.InjOn (componentAttachmentImage F)
      (componentAttachmentFunctions F allowed) := by
  intro f hf g hg hfg
  funext c hc
  have hfc := (mem_componentAttachmentChoices F allowed c _).mp
    ((Finset.mem_pi.mp hf) c hc) |>.2
  have hfmem : f c hc ∈ componentAttachmentImage F f :=
    Finset.mem_image.mpr ⟨c, Finset.mem_univ c, by congr⟩
  have hfmemg : f c hc ∈ componentAttachmentImage F g := by
    rw [← hfg]
    exact hfmem
  obtain ⟨d, _hd, hgd⟩ := Finset.mem_image.mp hfmemg
  have hgdcomp : g d (Finset.mem_univ d) ∈ d :=
    (mem_componentAttachmentChoices F allowed d _).mp
      ((Finset.mem_pi.mp hg) d (Finset.mem_univ d)) |>.2
  have hfcd : f c hc ∈ d := hgd ▸ hgdcomp
  have hcd : c = d := ConnectedComponent.eq_of_common_vertex hfc hfcd
  calc
    f c hc = g d (Finset.mem_univ d) := hgd.symm
    _ = g c hc := by cases hcd; rfl

/-- Values chosen in distinct connected components are distinct. -/
theorem componentAttachmentFunction_injective
    (F : SimpleGraph W) (allowed : Finset W)
    {f : ∀ c ∈ (Finset.univ : Finset F.ConnectedComponent), W}
    (hf : f ∈ componentAttachmentFunctions F allowed) :
    Function.Injective (fun c : F.ConnectedComponent =>
      f c (Finset.mem_univ c)) := by
  intro c d hcd
  have hfc : f c (Finset.mem_univ c) ∈ c :=
    (mem_componentAttachmentChoices F allowed c _).mp
      ((Finset.mem_pi.mp hf) c (Finset.mem_univ c)) |>.2
  have hfd : f d (Finset.mem_univ d) ∈ d :=
    (mem_componentAttachmentChoices F allowed d _).mp
      ((Finset.mem_pi.mp hf) d (Finset.mem_univ d)) |>.2
  have hfcd : f c (Finset.mem_univ c) ∈ d := by
    have hmemEq :
        (f c (Finset.mem_univ c) ∈ d) =
          (f d (Finset.mem_univ d) ∈ d) :=
      congrArg (fun v : W => v ∈ d) hcd
    exact hmemEq.mpr hfd
  exact ConnectedComponent.eq_of_common_vertex hfc hfcd

/-- Products over an attachment image retain one factor per component. -/
theorem prod_componentAttachmentImage
    {R : Type*} [CommMonoid R]
    (F : SimpleGraph W) (allowed : Finset W) (weight : W → R)
    {f : ∀ c ∈ (Finset.univ : Finset F.ConnectedComponent), W}
    (hf : f ∈ componentAttachmentFunctions F allowed) :
    ∏ v ∈ componentAttachmentImage F f, weight v =
      ∏ c : F.ConnectedComponent, weight (f c (Finset.mem_univ c)) := by
  classical
  rw [componentAttachmentImage, Finset.prod_image]
  exact componentAttachmentFunction_injective F allowed hf |>.injOn

/-- Images of componentwise choices are exactly the valid attachment
finsets. -/
theorem image_componentAttachmentFunctions_eq_valid
    (F : SimpleGraph W) (allowed : Finset W) :
    (componentAttachmentFunctions F allowed).image
        (componentAttachmentImage F) =
      validComponentAttachmentFinsets F allowed := by
  classical
  ext attachments
  constructor
  · intro h
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr
      (componentAttachmentImage_subset_allowed F allowed hf),
      componentAttachmentImage_existsUnique F allowed hf⟩
  · intro h
    have hvalid := Finset.mem_filter.mp h
    have hsub : attachments ⊆ allowed := Finset.mem_powerset.mp hvalid.1
    let f : ∀ c ∈ (Finset.univ : Finset F.ConnectedComponent), W :=
      fun c _ => Classical.choose (hvalid.2 c)
    have hfprop : ∀ c, f c (Finset.mem_univ c) ∈ c ∧
        f c (Finset.mem_univ c) ∈ attachments := fun c =>
      Classical.choose_spec (hvalid.2 c) |>.1
    have hf : f ∈ componentAttachmentFunctions F allowed := by
      apply Finset.mem_pi.mpr
      intro c hc
      apply (mem_componentAttachmentChoices F allowed c _).mpr
      exact ⟨hsub (hfprop c).2, (hfprop c).1⟩
    apply Finset.mem_image.mpr
    refine ⟨f, hf, ?_⟩
    ext v
    constructor
    · intro hv
      obtain ⟨c, _hc, hcv⟩ := Finset.mem_image.mp hv
      rw [← hcv]
      exact (hfprop c).2
    · intro hv
      let c := F.connectedComponentMk v
      have hvc : v ∈ c := ConnectedComponent.connectedComponentMk_mem
      have hchosen := hfprop c
      have heq : v = f c (Finset.mem_univ c) :=
        (Classical.choose_spec (hvalid.2 c)).2 v ⟨hvc, hv⟩
      exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, heq.symm⟩

/-- The root-neighbor finset of a tree is one of the valid attachment
finsets for its root-deleted forest. -/
theorem IsTree.rootNeighborFinset_mem_valid
    {V : Type*} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} (hT : T.IsTree) (root : V) :
    rootNeighborFinset T root ∈
      validComponentAttachmentFinsets (awayGraph T root)
        (rootNeighborFinset T root) := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_powerset.mpr Finset.Subset.rfl,
    (YangMills.Polymer.IsTree.isRootedForestData_rootedGraphData hT root).2⟩

/-- If `T` is a spanning tree below an ambient graph `G`, its attachment
finset is valid among the ambient root-neighbor choices. -/
theorem IsTree.rootNeighborFinset_mem_valid_of_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G T : SimpleGraph V} (hT : T.IsTree) (hTG : T ≤ G) (root : V) :
    rootNeighborFinset T root ∈
      validComponentAttachmentFinsets (awayGraph T root)
        (rootNeighborFinset G root) := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ?_,
    (YangMills.Polymer.IsTree.isRootedForestData_rootedGraphData hT root).2⟩
  intro v hv
  exact (mem_rootNeighborFinset G root v).2 <|
    hTG ((mem_rootNeighborFinset T root v).1 hv)

/-! ## Finite rooted-tree data below an ambient graph -/

/-- Spanning trees of a finite ambient graph, retained as graphs rather than
edge finsets so that root deletion is directly available. -/
def spanningTreeGraphs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (SimpleGraph V) := by
  classical
  exact Finset.univ.filter fun T => T ≤ G ∧ T.IsTree

@[simp]
theorem mem_spanningTreeGraphs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : SimpleGraph V) :
    T ∈ spanningTreeGraphs G ↔ T ≤ G ∧ T.IsTree := by
  classical
  simp [spanningTreeGraphs]

/-- All acyclic root-deleted graphs below `G`, equipped with exactly one
ambiently allowed attachment in each component. -/
def rootedForestDataFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) :
    Finset (SimpleGraph {v : V // v ≠ root} ×
      Finset {v : V // v ≠ root}) := by
  classical
  exact Finset.univ.filter fun D =>
    D.1 ≤ awayGraph G root ∧ D.1.IsAcyclic ∧
      D.2 ∈ validComponentAttachmentFinsets D.1
        (rootNeighborFinset G root)

@[simp]
theorem mem_rootedForestDataFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V)
    (D : SimpleGraph {v : V // v ≠ root} ×
      Finset {v : V // v ≠ root}) :
    D ∈ rootedForestDataFinset G root ↔
      D.1 ≤ awayGraph G root ∧ D.1.IsAcyclic ∧
        D.2 ∈ validComponentAttachmentFinsets D.1
          (rootNeighborFinset G root) := by
  classical
  simp [rootedForestDataFinset]

/-- Acyclic spanning graphs on the complement of `root`. -/
def spanningForestGraphsAway
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) :
    Finset (SimpleGraph {v : V // v ≠ root}) := by
  classical
  exact Finset.univ.filter fun F => F ≤ awayGraph G root ∧ F.IsAcyclic

@[simp]
theorem mem_spanningForestGraphsAway
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V)
    (F : SimpleGraph {v : V // v ≠ root}) :
    F ∈ spanningForestGraphsAway G root ↔
      F ≤ awayGraph G root ∧ F.IsAcyclic := by
  classical
  simp [spanningForestGraphsAway]

theorem mem_rootedForestDataFinset_iff_forest_attachment
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V)
    (D : SimpleGraph {v : V // v ≠ root} ×
      Finset {v : V // v ≠ root}) :
    D ∈ rootedForestDataFinset G root ↔
      D.1 ∈ spanningForestGraphsAway G root ∧
        D.2 ∈ validComponentAttachmentFinsets D.1
          (rootNeighborFinset G root) := by
  rw [mem_rootedForestDataFinset, mem_spanningForestGraphsAway]
  tauto

/-- Root data extracted from a spanning tree belongs to the finite ambient
forest-data enumeration. -/
theorem rootedGraphData_mem_rootedForestDataFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {G T : SimpleGraph V} (hT : T.IsTree) (hTG : T ≤ G) (root : V) :
    rootedGraphData T root ∈ rootedForestDataFinset G root := by
  classical
  apply (mem_rootedForestDataFinset G root _).mpr
  refine ⟨?_, hT.isAcyclic.induce {v | v ≠ root}, ?_⟩
  · intro v w hvw
    exact hTG hvw
  · exact IsTree.rootNeighborFinset_mem_valid_of_le hT hTG root

/-- Root data actually arising from spanning trees. -/
def rootedSpanningTreeDataFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) :
    Finset (SimpleGraph {v : V // v ≠ root} ×
      Finset {v : V // v ≠ root}) := by
  classical
  exact (spanningTreeGraphs G).image fun T => rootedGraphData T root

theorem rootedSpanningTreeDataFinset_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) :
    rootedSpanningTreeDataFinset G root ⊆ rootedForestDataFinset G root := by
  classical
  intro D hD
  rw [rootedSpanningTreeDataFinset] at hD
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hD
  have hdata := (mem_spanningTreeGraphs G T).mp hT
  exact rootedGraphData_mem_rootedForestDataFinset hdata.2 hdata.1 root

/-- Lossless root deletion preserves the exact number of spanning trees. -/
theorem card_rootedSpanningTreeDataFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) :
    (rootedSpanningTreeDataFinset G root).card =
      (spanningTreeGraphs G).card := by
  classical
  rw [rootedSpanningTreeDataFinset]
  exact Finset.card_image_iff.mpr
    (rootedGraphData_injective root).injOn

/-- Any nonnegative tree-data weight may be summed after root deletion by
enlarging to all acyclic forest data. -/
theorem sum_spanningTreeGraphs_rootedData_le_sum_rootedForestData
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V)
    (weight : (SimpleGraph {v : V // v ≠ root} ×
      Finset {v : V // v ≠ root}) → ℝ)
    (hweight : ∀ D, 0 ≤ weight D) :
    ∑ T ∈ spanningTreeGraphs G, weight (rootedGraphData T root) ≤
      ∑ D ∈ rootedForestDataFinset G root, weight D := by
  classical
  calc
    ∑ T ∈ spanningTreeGraphs G, weight (rootedGraphData T root) =
        ∑ D ∈ rootedSpanningTreeDataFinset G root, weight D := by
      rw [rootedSpanningTreeDataFinset,
        Finset.sum_image (rootedGraphData_injective root).injOn]
    _ ≤ ∑ D ∈ rootedForestDataFinset G root, weight D :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (rootedSpanningTreeDataFinset_subset G root)
        (fun D _hD _hnot => hweight D)

/-- Exact finite product formula for root attachments of a fixed forest. -/
theorem card_validComponentAttachmentFinsets
    (F : SimpleGraph W) (allowed : Finset W) :
    (validComponentAttachmentFinsets F allowed).card =
      ∏ c : F.ConnectedComponent,
        (componentAttachmentChoices F allowed c).card := by
  classical
  rw [← image_componentAttachmentFunctions_eq_valid]
  rw [Finset.card_image_iff.mpr
    (componentAttachmentImage_injOn F allowed)]
  change Multiset.card
      ((Finset.univ : Finset F.ConnectedComponent).1.pi
        (fun c => (componentAttachmentChoices F allowed c).1)) = _
  simpa using (Multiset.card_pi
    (Finset.univ : Finset F.ConnectedComponent).1
    (fun c => (componentAttachmentChoices F allowed c).1))

/-- Weighted finite product formula for root attachments.  This is the exact
factorization consumed by the KP child mass after the root-deleted forest is
fixed. -/
theorem sum_validComponentAttachmentFinsets_prod
    {R : Type*} [CommSemiring R]
    (F : SimpleGraph W) (allowed : Finset W) (weight : W → R) :
    ∏ c : F.ConnectedComponent,
        ∑ v ∈ componentAttachmentChoices F allowed c, weight v =
    ∑ attachments ∈ validComponentAttachmentFinsets F allowed,
        ∏ v ∈ attachments, weight v := by
  classical
  calc
    ∏ c : F.ConnectedComponent,
        ∑ v ∈ componentAttachmentChoices F allowed c, weight v =
      ∑ f ∈ componentAttachmentFunctions F allowed,
        ∏ c : F.ConnectedComponent,
          weight (f c (Finset.mem_univ c)) := by
      simpa only [Finset.prod_attach_univ] using
        (Finset.prod_sum (R := R)
          (Finset.univ : Finset F.ConnectedComponent)
          (componentAttachmentChoices F allowed) (fun _ v => weight v))
    _ = ∑ f ∈ componentAttachmentFunctions F allowed,
        ∏ v ∈ componentAttachmentImage F f, weight v := by
      apply Finset.sum_congr rfl
      intro f hf
      exact (prod_componentAttachmentImage F allowed weight hf).symm
    _ = ∑ attachments ∈
          (componentAttachmentFunctions F allowed).image
            (componentAttachmentImage F),
        ∏ v ∈ attachments, weight v := by
      rw [Finset.sum_image (componentAttachmentImage_injOn F allowed)]
    _ = ∑ attachments ∈ validComponentAttachmentFinsets F allowed,
        ∏ v ∈ attachments, weight v := by
      rw [image_componentAttachmentFunctions_eq_valid]

/-- Exact weighted regrouping of all rooted-forest data: first choose the
root-deleted forest, then choose one allowed attachment independently in each
component. -/
theorem sum_rootedForestData_eq_sum_forest_prod_component
    {V : Type*} [Fintype V] [DecidableEq V]
    {R : Type*} [CommSemiring R]
    (G : SimpleGraph V) (root : V)
    (forestWeight : SimpleGraph {v : V // v ≠ root} → R)
    (attachmentWeight : {v : V // v ≠ root} → R) :
    ∑ D ∈ rootedForestDataFinset G root,
        forestWeight D.1 * ∏ v ∈ D.2, attachmentWeight v =
      ∑ F ∈ spanningForestGraphsAway G root,
        forestWeight F *
          ∏ c : F.ConnectedComponent,
            ∑ v ∈ componentAttachmentChoices F
              (rootNeighborFinset G root) c, attachmentWeight v := by
  classical
  calc
    ∑ D ∈ rootedForestDataFinset G root,
        forestWeight D.1 * ∏ v ∈ D.2, attachmentWeight v =
      ∑ F ∈ spanningForestGraphsAway G root,
        ∑ attachments ∈ validComponentAttachmentFinsets F
            (rootNeighborFinset G root),
          forestWeight F * ∏ v ∈ attachments, attachmentWeight v := by
      exact Finset.sum_finset_product'
        (rootedForestDataFinset G root)
        (spanningForestGraphsAway G root)
        (fun F => validComponentAttachmentFinsets F
          (rootNeighborFinset G root))
        (mem_rootedForestDataFinset_iff_forest_attachment G root)
        (f := fun F attachments =>
          forestWeight F * ∏ v ∈ attachments, attachmentWeight v)
    _ = ∑ F ∈ spanningForestGraphsAway G root,
        forestWeight F *
          ∏ c : F.ConnectedComponent,
            ∑ v ∈ componentAttachmentChoices F
              (rootNeighborFinset G root) c, attachmentWeight v := by
      apply Finset.sum_congr rfl
      intro F _hF
      rw [← Finset.mul_sum,
        ← sum_validComponentAttachmentFinsets_prod]

/-- For a spanning tree below `G`, the product of the actual canonical child
attachments is bounded by the product of the independent componentwise
attachment sums allowed by `G`.  This is the precise finite inequality that
turns root deletion into KP branching. -/
theorem IsTree.prod_childRoot_le_prod_componentAttachmentChoices_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    {G T : SimpleGraph V} (hT : T.IsTree) (hTG : T ≤ G) (root : V)
    (weight : {v : V // v ≠ root} → ℝ)
    (hweight : ∀ v, 0 ≤ weight v) :
    ∏ c : (awayGraph T root).ConnectedComponent,
        weight (YangMills.Polymer.IsTree.childRoot hT root c) ≤
      ∏ c : (awayGraph T root).ConnectedComponent,
        ∑ v ∈ componentAttachmentChoices (awayGraph T root)
          (rootNeighborFinset G root) c, weight v := by
  classical
  rw [← YangMills.Polymer.IsTree.prod_rootNeighborFinset hT root weight]
  rw [sum_validComponentAttachmentFinsets_prod]
  exact Finset.single_le_sum
    (s := validComponentAttachmentFinsets (awayGraph T root)
      (rootNeighborFinset G root))
    (f := fun attachments => ∏ v ∈ attachments, weight v)
    (fun attachments _hattachments =>
      Finset.prod_nonneg fun v _ => hweight v)
    (IsTree.rootNeighborFinset_mem_valid_of_le hT hTG root)

end

end YangMills.Polymer
