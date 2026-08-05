/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Finite graph component sets

Reusable conversion between connected components of a graph induced on a
finite vertex set and nonempty connected `Finset`s in the ambient graph.
-/

namespace YangMills.Polymer.GraphComponents

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- A vertex label constant across every edge is constant along every
reachable pair. -/
theorem label_eq_of_reachable {W : Type*} (G : SimpleGraph V) (f : V → W)
    (hedge : ∀ {u v}, G.Adj u v → f u = f v) {u v : V}
    (huv : G.Reachable u v) : f u = f v := by
  rcases huv with ⟨p⟩
  induction p with
  | nil => rfl
  | cons h p ih => exact (hedge h).trans ih

/-- Ambient vertex set belonging to one component of an induced graph. -/
def componentFinset (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    (c : (G.induce (X : Set V)).ConnectedComponent) : Finset V :=
  (X.attach.filter fun v => v ∈ c.supp).map
    ⟨fun v => v.1, Subtype.val_injective⟩

omit [Fintype V] in
theorem componentFinset_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (c : (G.induce (X : Set V)).ConnectedComponent) :
    (componentFinset G X c).Nonempty := by
  refine ⟨c.out.1, ?_⟩
  apply Finset.mem_map.mpr
  exact ⟨c.out, Finset.mem_filter.mpr ⟨by simp, c.out_eq⟩, rfl⟩

omit [Fintype V] in
theorem componentFinset_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (c : (G.induce (X : Set V)).ConnectedComponent) :
    componentFinset G X c ⊆ X := by
  intro v hv
  rcases Finset.mem_map.mp hv with ⟨w, _, rfl⟩
  exact w.2

omit [Fintype V] in
/-- A component of an induced graph is connected as an ambient induced
subgraph after forgetting the nested subtype. -/
theorem connected_induce_componentFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (c : (G.induce (X : Set V)).ConnectedComponent) :
    (G.induce (componentFinset G X c : Set V)).Connected := by
  let f : c.toSimpleGraph →g G.induce (componentFinset G X c : Set V) := {
    toFun u := ⟨u.1.1, by
      apply Finset.mem_map.mpr
      exact ⟨u.1, Finset.mem_filter.mpr ⟨by simp, u.2⟩, rfl⟩⟩
    map_rel' := fun h => h }
  letI : Nonempty {v // v ∈ componentFinset G X c} :=
    ⟨⟨c.out.1, by
      apply Finset.mem_map.mpr
      exact ⟨c.out, Finset.mem_filter.mpr ⟨by simp, c.out_eq⟩, rfl⟩⟩⟩
  refine ⟨?_⟩
  intro u v
  rcases Finset.mem_map.mp u.2 with ⟨wu, hwu, hwuval⟩
  rcases Finset.mem_map.mp v.2 with ⟨wv, hwv, hwvval⟩
  have hreach := c.reachable_toSimpleGraph
    (Finset.mem_filter.mp hwu).2 (Finset.mem_filter.mp hwv).2
  have hmapped := hreach.map f
  convert hmapped using 1
  · exact Subtype.ext hwuval.symm
  · exact Subtype.ext hwvval.symm

/-- Finite family of all component vertex sets. -/
def componentFinsets (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) : Finset (Finset V) :=
  Finset.univ.image (componentFinset G X)

omit [Fintype V] in
theorem mem_componentFinsets (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (Y : Finset V) :
    Y ∈ componentFinsets G X ↔
      ∃ c : (G.induce (X : Set V)).ConnectedComponent,
        componentFinset G X c = Y := by
  simp [componentFinsets]

omit [Fintype V] in
/-- Distinct component vertex sets are disjoint. -/
theorem pairwise_disjoint_componentFinsets (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) :
    (componentFinsets G X : Set (Finset V)).Pairwise Disjoint := by
  intro A hA B hB hAB
  rcases (mem_componentFinsets G X A).mp hA with ⟨a, rfl⟩
  rcases (mem_componentFinsets G X B).mp hB with ⟨b, rfl⟩
  have hab : a ≠ b := by
    intro h
    subst b
    exact hAB rfl
  apply Finset.disjoint_left.mpr
  intro v hva hvb
  rcases Finset.mem_map.mp hva with ⟨va, hva, hval⟩
  rcases Finset.mem_map.mp hvb with ⟨vb, hvb, hval'⟩
  have hvab : va.1 = vb.1 := hval.trans hval'.symm
  have hsupp : va ∈ a.supp ∩ b.supp := by
    refine ⟨(Finset.mem_filter.mp hva).2, ?_⟩
    have hvavb : va = vb := Subtype.ext hvab
    simpa [hvavb] using (Finset.mem_filter.mp hvb).2
  exact (Set.disjoint_left.mp
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent _ hab)) hsupp.1 hsupp.2

omit [Fintype V] in
/-- A vertex cannot belong to two different component finsets. -/
theorem component_eq_of_mem
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    {a b : (G.induce (X : Set V)).ConnectedComponent} {v : V}
    (hva : v ∈ componentFinset G X a) (hvb : v ∈ componentFinset G X b) :
    a = b := by
  rcases Finset.mem_map.mp hva with ⟨va, hva, hvaVal⟩
  rcases Finset.mem_map.mp hvb with ⟨vb, hvb, hvbVal⟩
  have hvab : va = vb := Subtype.ext (hvaVal.trans hvbVal.symm)
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (Finset.mem_filter.mp hva).2 (hvab ▸ (Finset.mem_filter.mp hvb).2)

omit [Fintype V] in
/-- Vertices in distinct induced components cannot be adjacent in the ambient
graph. -/
theorem not_adj_of_mem_componentFinset_of_ne
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    {a b : (G.induce (X : Set V)).ConnectedComponent} (hab : a ≠ b)
    {v w : V} (hv : v ∈ componentFinset G X a)
    (hw : w ∈ componentFinset G X b) : ¬G.Adj v w := by
  intro hadj
  rcases Finset.mem_map.mp hv with ⟨va, hva, hvaVal⟩
  rcases Finset.mem_map.mp hw with ⟨wb, hwb, hwbVal⟩
  have hinduced : (G.induce (X : Set V)).Adj va wb := by
    change G.Adj va.1 wb.1
    have hvaVal' : va.1 = v := hvaVal
    have hwbVal' : wb.1 = w := hwbVal
    rw [hvaVal', hwbVal']
    exact hadj
  have hcomponents :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hinduced
  have hvaComp : (G.induce (X : Set V)).connectedComponentMk va = a :=
    (Finset.mem_filter.mp hva).2
  have hwbComp : (G.induce (X : Set V)).connectedComponentMk wb = b :=
    (Finset.mem_filter.mp hwb).2
  exact hab (hvaComp.symm.trans (hcomponents.trans hwbComp))

omit [Fintype V] in
/-- The component sets cover the original finite vertex set. -/
theorem biUnion_componentFinsets (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) :
    (componentFinsets G X).biUnion id = X := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_biUnion.mp hv with ⟨Y, hY, hvY⟩
    rcases (mem_componentFinsets G X Y).mp hY with ⟨c, rfl⟩
    exact componentFinset_subset G X c hvY
  · intro hv
    let x : (X : Set V) := ⟨v, hv⟩
    let c := (G.induce (X : Set V)).connectedComponentMk x
    apply Finset.mem_biUnion.mpr
    refine ⟨componentFinset G X c, ?_, ?_⟩
    · exact (mem_componentFinsets G X _).mpr ⟨c, rfl⟩
    · apply Finset.mem_map.mpr
      exact ⟨x, Finset.mem_filter.mpr ⟨by simp,
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩, rfl⟩

end

end YangMills.Polymer.GraphComponents
