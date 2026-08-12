/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.CenteredClusterGeometry
import YangMills.StrongCoupling.ClusterBoundaryExpansion

/-!
# Cluster boundary tails along the centered exhaustion

This file turns the finite-volume one-root boundary estimate into a uniform
centered-box estimate.  The proof uses a finite, recursively generated
neighborhood in the ambient plaquette-incidence graph.  Thus it needs no
coordinate formula for graph distance and, in particular, no influence
matrix or Dobrushin comparison theorem.
-/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Polymer

noncomputable section

local instance centeredBoundaryExpansionDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- A finite over-approximation to the neighbors of an ambient spatial
vertex.  Including harmless extra roots and the plaquette itself keeps the
recursive metric ball elementary. -/
def globalObservableSpatialNeighborCover
    (S T : Finset (PositiveEdge d))
    (x : GlobalBivariateObservableSpatialVertex d) :
    Finset (GlobalBivariateObservableSpatialVertex d) := by
  classical
  exact match x with
    | Sum.inl p =>
        (p.boundary.edgeSupport.biUnion incidentPlaquettes).map
            ⟨Sum.inl, Sum.inl_injective⟩ ∪
          (Finset.univ : Finset (Fin 2)).map ⟨Sum.inr, Sum.inr_injective⟩
    | Sum.inr i =>
        ((if i = 0 then S else T).biUnion incidentPlaquettes).map
          ⟨Sum.inl, Sum.inl_injective⟩

theorem mem_globalObservableSpatialNeighborCover_of_adj
    (S T : Finset (PositiveEdge d))
    {x y : GlobalBivariateObservableSpatialVertex d}
    (hxy : (globalBivariateObservableSpatialGraph S T).Adj x y) :
    y ∈ globalObservableSpatialNeighborCover S T x := by
  classical
  rcases x with p | i <;> rcases y with q | j
  · change p ≠ q ∧
      ¬Disjoint p.boundary.edgeSupport q.boundary.edgeSupport at hxy
    simp only [globalObservableSpatialNeighborCover, Finset.mem_union]
    left
    apply Finset.mem_map.mpr
    refine ⟨q, ?_, rfl⟩
    rw [Finset.not_disjoint_iff] at hxy
    obtain ⟨e, hep, heq⟩ := hxy.2
    exact Finset.mem_biUnion.mpr
      ⟨e, hep, mem_incidentPlaquettes_of_mem_boundary e q heq⟩
  · simp only [globalObservableSpatialNeighborCover, Finset.mem_union]
    right
    exact Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩
  · change ¬Disjoint q.boundary.edgeSupport
      (if i = 0 then S else T) at hxy
    simp only [globalObservableSpatialNeighborCover]
    apply Finset.mem_map.mpr
    refine ⟨q, ?_, rfl⟩
    rw [Finset.not_disjoint_iff] at hxy
    obtain ⟨e, heq, heS⟩ := hxy
    exact Finset.mem_biUnion.mpr
      ⟨e, heS, mem_incidentPlaquettes_of_mem_boundary e q heq⟩
  · change False at hxy
    exact hxy.elim

/-- A finite ambient ball grown from the first observable root. -/
def globalObservableSpatialFiniteBall
    (S T : Finset (PositiveEdge d)) : ℕ →
    Finset (GlobalBivariateObservableSpatialVertex d)
  | 0 => {Sum.inr 0}
  | n + 1 =>
      globalObservableSpatialFiniteBall S T n ∪
        (globalObservableSpatialFiniteBall S T n).biUnion
          (globalObservableSpatialNeighborCover S T)

theorem globalObservableSpatialFiniteBall_subset_succ
    (S T : Finset (PositiveEdge d)) (n : ℕ) :
    globalObservableSpatialFiniteBall S T n ⊆
      globalObservableSpatialFiniteBall S T (n + 1) := by
  intro x hx
  exact Finset.mem_union_left _ hx

theorem globalObservableSpatialFiniteBall_mono
    (S T : Finset (PositiveEdge d)) {m n : ℕ} (hmn : m ≤ n) :
    globalObservableSpatialFiniteBall S T m ⊆
      globalObservableSpatialFiniteBall S T n := by
  intro x hx
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      simpa [hm] using hx
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · exact globalObservableSpatialFiniteBall_subset_succ S T n (ih hmn')
      · have hmnEq : m = n + 1 := by omega
        simpa [hmnEq] using hx

theorem walk_end_mem_globalObservableSpatialFiniteBall
    (S T : Finset (PositiveEdge d))
    {x y : GlobalBivariateObservableSpatialVertex d} (n : ℕ)
    (hx : x ∈ globalObservableSpatialFiniteBall S T n)
    (path : (globalBivariateObservableSpatialGraph S T).Walk x y) :
    y ∈ globalObservableSpatialFiniteBall S T (n + path.length) := by
  induction path generalizing n with
  | nil => simpa using hx
  | @cons u v w huv path ih =>
      have hv : v ∈ globalObservableSpatialFiniteBall S T (n + 1) := by
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr
          ⟨u, hx, mem_globalObservableSpatialNeighborCover_of_adj S T huv⟩
      have hend := ih (n + 1) hv
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend

/-- All positive edges on plaquette vertices in the finite ambient ball. -/
def globalObservableSpatialFiniteBallEdgeSupport
    (S T : Finset (PositiveEdge d)) (r : ℕ) :
    Finset (PositiveEdge d) :=
  (globalObservableSpatialFiniteBall S T r).biUnion fun x =>
    match x with
    | Sum.inl p => p.boundary.edgeSupport
    | Sum.inr _ => ∅

theorem plaquetteBoundary_subset_globalObservableSpatialFiniteBallEdgeSupport
    (S T : Finset (PositiveEdge d)) (r : ℕ) (p : Plaquette d)
    (hp : Sum.inl p ∈ globalObservableSpatialFiniteBall S T r) :
    p.boundary.edgeSupport ⊆
      globalObservableSpatialFiniteBallEdgeSupport S T r := by
  intro e he
  exact Finset.mem_biUnion.mpr ⟨Sum.inl p, hp, he⟩

/-- At every prescribed cluster radius, a sufficiently large centered box
puts every reachable boundary-disagreement plaquette beyond that radius. -/
theorem centered_boundaryDisagreement_distance_eventually
    (F : LocalObservable d G) (r : ℕ) :
    ∃ N, ∀ n, N ≤ n → ∀ η η' : Configuration d G,
      F.support ⊆ (centeredSpecification n η).dynamicEdges ∧
      ∀ p ∈ boundaryDisagreementPlaquettes
          (centeredSpecification n η) η η',
        (bivariateObservableSpatialGraph F F
          (centeredSpecification n η)).Reachable
            (Sum.inr 0) (Sum.inl p) →
          r + 1 ≤ (bivariateObservableSpatialGraph F F
            (centeredSpecification n η)).dist
              (Sum.inr 0) (Sum.inl p) := by
  classical
  let E := F.support ∪
    globalObservableSpatialFiniteBallEdgeSupport F.support F.support r
  obtain ⟨N, hN⟩ := finiteSupport_subset_centeredBox_eventually E
  refine ⟨N, fun n hn η η' => ⟨?_, ?_⟩⟩
  · intro e he
    exact hN n hn (Finset.mem_union_left _ he)
  · intro p hp hreach
    by_contra hnot
    have hdistLe : (bivariateObservableSpatialGraph F F
        (centeredSpecification n η)).dist
          (Sum.inr 0) (Sum.inl p) ≤ r := by omega
    obtain ⟨path, hpath⟩ := hreach.exists_walk_length_eq_dist
    let path' := path.map
      (bivariateObservableSpatialGraphToGlobalHom F F
        (centeredSpecification n η))
    change (globalBivariateObservableSpatialGraph F.support F.support).Walk
      (Sum.inr 0) (Sum.inl p.1) at path'
    have hpend : Sum.inl p.1 ∈
        globalObservableSpatialFiniteBall F.support F.support path'.length := by
      have hroot : Sum.inr (0 : Fin 2) ∈
          globalObservableSpatialFiniteBall F.support F.support 0 := by
        simp [globalObservableSpatialFiniteBall]
      simpa using
        (walk_end_mem_globalObservableSpatialFiniteBall
          F.support F.support 0 hroot path')
    have hlen : path'.length ≤ r := by
      change (path.map (bivariateObservableSpatialGraphToGlobalHom F F
        (centeredSpecification n η))).length ≤ r
      rw [SimpleGraph.Walk.length_map]
      exact hpath.le.trans hdistLe
    have hpBall : Sum.inl p.1 ∈
        globalObservableSpatialFiniteBall F.support F.support r :=
      globalObservableSpatialFiniteBall_mono F.support F.support hlen hpend
    obtain ⟨e, hep, hedyn, _hne⟩ :=
      (mem_boundaryDisagreementPlaquettes
        (centeredSpecification n η) η η' p).mp hp
    exact hedyn (hN n hn (Finset.mem_union_right _
      (plaquetteBoundary_subset_globalObservableSpatialFiniteBallEdgeSupport
        F.support F.support r p.1 hpBall hep)))

/-- The concrete one-root Mayer/KP estimate is uniform over both exterior
fields once a centered box contains the prescribed finite ambient ball. -/
theorem pow_mul_norm_centered_complexGibbsExpectation_boundary_sub_le_eventually
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) (r : ℕ) :
    ∃ N, ∀ n, N ≤ n → ∀ η η' : Configuration d G,
      plaquetteCardinalityTilt (d := d) Φ β ^ r *
          ‖complexGibbsExpectation F (centeredSpecification n η) Φ β -
            complexGibbsExpectation F (centeredSpecification n η') Φ β‖ ≤
        2 * observableCardinalityTiltDecorationBudget (d := d) F Φ β := by
  obtain ⟨N, hN⟩ := centered_boundaryDisagreement_distance_eventually F r
  refine ⟨N, fun n hn η η' => ?_⟩
  obtain ⟨hF, hdist⟩ := hN n hn η η'
  simpa [centeredSpecification, withExterior] using
    (pow_mul_norm_complexGibbsExpectation_withExterior_sub_le_boundaryBudget
      F (centeredSpecification n η) Φ hβ η η' hF r hdist)

/-- Ordinary inverse-tilt form of the uniform centered boundary estimate. -/
theorem norm_centered_complexGibbsExpectation_boundary_sub_le_eventually
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) (r : ℕ) :
    ∃ N, ∀ n, N ≤ n → ∀ η η' : Configuration d G,
      ‖complexGibbsExpectation F (centeredSpecification n η) Φ β -
        complexGibbsExpectation F (centeredSpecification n η') Φ β‖ ≤
      2 * observableCardinalityTiltDecorationBudget (d := d) F Φ β *
        plaquetteClusterDecayRate (d := d) Φ β ^ r := by
  obtain ⟨N, hN⟩ :=
    pow_mul_norm_centered_complexGibbsExpectation_boundary_sub_le_eventually
      F Φ hβ r
  refine ⟨N, fun n hn η η' => ?_⟩
  let t := plaquetteCardinalityTilt (d := d) Φ β
  let B := 2 * observableCardinalityTiltDecorationBudget (d := d) F Φ β
  let x := ‖complexGibbsExpectation F (centeredSpecification n η) Φ β -
    complexGibbsExpectation F (centeredSpecification n η') Φ β‖
  have ht : 0 < t := zero_lt_one.trans (one_lt_plaquetteCardinalityTilt Φ hβ)
  have htx : t ^ r * x ≤ B := by
    simpa [t, B, x] using hN n hn η η'
  calc
    x = (t ^ r)⁻¹ * (t ^ r * x) := by
      field_simp
    _ ≤ (t ^ r)⁻¹ * B :=
      mul_le_mul_of_nonneg_left htx (inv_nonneg.mpr (pow_nonneg ht.le r))
    _ = B * (t⁻¹) ^ r := by
      rw [inv_pow]
      ring
    _ = _ := by
      rfl

/-- Arbitrary centered boundary sequences become indistinguishable.  The
convergence is a direct consequence of the one-root cluster tail. -/
theorem tendsto_centered_complexGibbsExpectation_boundary_sub_zero
    (F : LocalObservable d G) (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (η η' : ℕ → Configuration d G) :
    Filter.Tendsto (fun n =>
      complexGibbsExpectation F (centeredSpecification n (η n)) Φ β -
        complexGibbsExpectation F (centeredSpecification n (η' n)) Φ β)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let B := 2 * observableCardinalityTiltDecorationBudget (d := d) F Φ β
  let q := plaquetteClusterDecayRate (d := d) Φ β
  have hq0 : 0 ≤ q := (plaquetteClusterDecayRate_pos Φ hβ).le
  have hq1 : q < 1 := plaquetteClusterDecayRate_lt_one Φ hβ
  have hmajorant : Filter.Tendsto (fun r : ℕ => B * q ^ r)
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul B
  have hevent : ∀ᶠ r in Filter.atTop, B * q ^ r < ε :=
    hmajorant (gt_mem_nhds hε)
  obtain ⟨r, hr⟩ := (Filter.eventually_atTop.1 hevent)
  obtain ⟨N, hN⟩ :=
    norm_centered_complexGibbsExpectation_boundary_sub_le_eventually
      F Φ hβ r
  refine ⟨max N r, fun n hn => ?_⟩
  rw [dist_zero_right]
  exact (hN n (Nat.le_max_left N r |>.trans hn) (η n) (η' n)).trans_lt
    (by simpa [B, q] using hr r le_rfl)

end

end YangMills.StrongCoupling
