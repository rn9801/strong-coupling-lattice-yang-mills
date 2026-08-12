/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.SpatialClusterGeometry
import YangMills.StrongCoupling.ThermodynamicBoxes

/-!
# Ambient cluster geometry along the centered exhaustion

A fixed finite walk in the ambient two-root plaquette graph uses only finitely
many plaquette-boundary edges.  Cofinality of the centered boxes therefore
makes every one of those edges dynamic eventually.  The walk then lifts to
the finite-volume graph, proving the eventual comparison between the ambient
support distance and the finite-volume cluster separation.

This is purely the cluster-expansion geometry; no influence matrix or
Dobrushin comparison theorem is imported.
-/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Polymer

noncomputable section

local instance centeredClusterGeometryDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-- All positive edges on ambient plaquette vertices visited by a walk. -/
def globalSpatialWalkEdgeSupport
    {S T : Finset (PositiveEdge d)} {u v}
    (path : (globalBivariateObservableSpatialGraph S T).Walk u v) :
    Finset (PositiveEdge d) :=
  path.support.toFinset.biUnion fun x => match x with
    | Sum.inl p => p.boundary.edgeSupport
    | Sum.inr _ => ∅

theorem plaquetteBoundary_subset_globalSpatialWalkEdgeSupport
    {S T : Finset (PositiveEdge d)} {u v}
    (path : (globalBivariateObservableSpatialGraph S T).Walk u v)
    (p : Plaquette d) (hp : Sum.inl p ∈ path.support) :
    p.boundary.edgeSupport ⊆ globalSpatialWalkEdgeSupport path := by
  classical
  intro e he
  unfold globalSpatialWalkEdgeSupport
  apply Finset.mem_biUnion.mpr
  exact ⟨Sum.inl p, by simpa using hp, he⟩

/-- A plaquette whose full boundary is dynamic belongs to the centered active
plaquette set. -/
theorem plaquette_mem_centeredActivePlaquettes_of_boundary_subset
    (n : ℕ) (p : Plaquette d)
    (hp : p.boundary.edgeSupport ⊆ (centeredBox d n).positiveEdges) :
    p ∈ centeredActivePlaquettes d n := by
  classical
  let e : PositiveEdge d := ⟨p.base, p.first⟩
  have hep : e ∈ p.boundary.edgeSupport := by
    simp [e, plaquette_boundary_edgeSupport]
  apply Finset.mem_biUnion.mpr
  exact ⟨e, hp hep, mem_incidentPlaquettes_of_mem_boundary e p hep⟩

/-- An ambient root-to-root walk lifts to every sufficiently large centered
finite-volume graph. -/
theorem globalBivariateObservable_reachable_centered_eventually
    (F H : LocalObservable d G) (η : ℕ → Configuration d G)
    (hreach : (globalBivariateObservableSpatialGraph F.support H.support).Reachable
      (Sum.inr 0) (Sum.inr 1)) :
    ∃ N, ∀ n, N ≤ n →
      (bivariateObservableSpatialGraph F H
        (centeredSpecification n (η n))).Reachable
          (Sum.inr 0) (Sum.inr 1) := by
  classical
  obtain ⟨path⟩ := hreach
  obtain ⟨N, hN⟩ := finiteSupport_subset_centeredBox_eventually
    (globalSpatialWalkEdgeSupport path)
  refine ⟨N, fun n hn => ?_⟩
  have hEdge : globalSpatialWalkEdgeSupport path ⊆
      (centeredBox d n).positiveEdges := hN n hn
  let K := globalBivariateObservableSpatialGraph F.support H.support
  let Λ := centeredSpecification n (η n)
  let W : Set (GlobalBivariateObservableSpatialVertex d) :=
    (path.support.toFinset : Set _)
  let liftVertex : W → BivariateObservableSpatialVertex Λ :=
    fun x => match hx : x.1 with
      | Sum.inl p =>
          Sum.inl ⟨p, by
            change p ∈ centeredActivePlaquettes d n
            apply plaquette_mem_centeredActivePlaquettes_of_boundary_subset
            exact fun e he => hEdge
              (plaquetteBoundary_subset_globalSpatialWalkEdgeSupport
                path p (by
                  have hxW : x.1 ∈ path.support.toFinset := x.2
                  simpa [hx] using hxW) he)⟩
      | Sum.inr i => Sum.inr i
  let liftHom : K.induce W →g bivariateObservableSpatialGraph F H Λ := by
    refine ⟨liftVertex, ?_⟩
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    change K.Adj x y at hxy
    rcases x with p | i
    · rcases y with q | j
      · change p ≠ q ∧
            ¬Disjoint p.boundary.edgeSupport q.boundary.edgeSupport at hxy
        have hxp : Sum.inl p ∈ path.support := by
          apply List.mem_toFinset.mp
          simpa [W] using hx
        have hyq : Sum.inl q ∈ path.support := by
          apply List.mem_toFinset.mp
          simpa [W] using hy
        simp only [liftVertex]
        change (plaquetteAdjacencyGraph Λ).Adj _ _
        refine ⟨?_, ?_⟩
        · intro hpq
          exact hxy.1 (congrArg Subtype.val hpq)
        · rw [Finset.not_disjoint_iff] at hxy ⊢
          obtain ⟨e, hep, heq⟩ := hxy.2
          refine ⟨e, ?_, ?_⟩
          · simp only [plaquetteDynamicSupport, Finset.mem_filter]
            exact ⟨hEdge
              (plaquetteBoundary_subset_globalSpatialWalkEdgeSupport
                path p hxp hep), hep⟩
          · simp only [plaquetteDynamicSupport, Finset.mem_filter]
            exact ⟨hEdge
              (plaquetteBoundary_subset_globalSpatialWalkEdgeSupport
                path q hyq heq), heq⟩
      · fin_cases j <;>
          simpa [K, Λ, liftVertex,
            globalBivariateObservableSpatialGraph,
            bivariateObservableSpatialGraph,
            bivariateObservableRootPlaquettes,
            mem_observableRootPlaquettes] using hxy
    · rcases y with q | j
      · fin_cases i <;>
          simpa [K, Λ, liftVertex,
            globalBivariateObservableSpatialGraph,
            bivariateObservableSpatialGraph,
            bivariateObservableRootPlaquettes,
            mem_observableRootPlaquettes] using hxy
      · exact hxy
  let pathW := path.induce W (by
    intro x hx
    exact (List.mem_toFinset.mpr hx : x ∈ path.support.toFinset))
  have lifted := pathW.map liftHom
  simpa [liftHom, liftVertex, W, Λ] using lifted.reachable

/-- The ambient support separation is eventually bounded by the finite-volume
separation along any centered exhaustion and arbitrary boundary sequence. -/
theorem globalObservablePlaquetteSeparation_le_centered_eventually
    (F H : LocalObservable d G) (η : ℕ → Configuration d G) :
    ∃ N, ∀ n, N ≤ n →
      globalObservablePlaquetteSeparation F.support H.support ≤
        bivariateObservablePlaquetteSeparation F H
          (centeredSpecification n (η n)) := by
  classical
  by_cases hreach :
      (globalBivariateObservableSpatialGraph F.support H.support).Reachable
        (Sum.inr 0) (Sum.inr 1)
  · obtain ⟨N, hN⟩ :=
      globalBivariateObservable_reachable_centered_eventually F H η hreach
    exact ⟨N, fun n hn =>
      globalObservablePlaquetteSeparation_le_finite F H
        (centeredSpecification n (η n)) (hN n hn)⟩
  · refine ⟨0, fun n _ => ?_⟩
    have hdist :
        (globalBivariateObservableSpatialGraph F.support H.support).dist
          (Sum.inr 0) (Sum.inr 1) = 0 :=
      SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mpr (Or.inr hreach)
    simp [globalObservablePlaquetteSeparation, hdist]

/-- Eventual finite-volume covariance decay in the ambient support distance,
with the explicit exponential-in-support complete-decoration amplitude. -/
theorem norm_centered_complexGibbsTruncatedCorrelation_le_globalSeparation_eventually
    (F H : LocalObservable d G) (η : ℕ → Configuration d G)
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hFH : Disjoint F.support H.support)
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    ∃ N, ∀ n, N ≤ n →
      ‖complexGibbsExpectation (F.mul H)
          (centeredSpecification n (η n)) Φ β -
        complexGibbsExpectation F (centeredSpecification n (η n)) Φ β *
          complexGibbsExpectation H (centeredSpecification n (η n)) Φ β‖ ≤
        bivariateDecoratedObservableUniformClusteringAmplitude
            (d := d) F H Φ β *
          plaquetteClusterDecayRate (d := d) Φ β ^
            globalObservablePlaquetteSeparation F.support H.support := by
  obtain ⟨N, hN⟩ :=
    globalObservablePlaquetteSeparation_le_centered_eventually F H η
  refine ⟨N, fun n hn => ?_⟩
  let r := plaquetteClusterDecayRate (d := d) Φ β
  have hr₀ : 0 ≤ r := (plaquetteClusterDecayRate_pos Φ hβ).le
  have hr₁ : r ≤ 1 := (plaquetteClusterDecayRate_lt_one Φ hβ).le
  calc
    _ ≤ bivariateDecoratedObservableUniformClusteringAmplitude
          (d := d) F H Φ β *
        r ^ bivariateObservablePlaquetteSeparation F H
          (centeredSpecification n (η n)) := by
      simpa [r] using
        norm_complexGibbsTruncatedCorrelation_le_uniformAmplitude_mul_rate_pow
          F H (centeredSpecification n (η n)) Φ hFH hβ
    _ ≤ bivariateDecoratedObservableUniformClusteringAmplitude
          (d := d) F H Φ β *
        r ^ globalObservablePlaquetteSeparation F.support H.support := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hr₀ hr₁ (hN n hn))
        (bivariateDecoratedObservableUniformClusteringAmplitude_nonneg
          (d := d) F H Φ β)
    _ = _ := rfl

/-- A harmless completion of the ambient separation: overlapping supports are
assigned distance zero, while disjoint supports retain their genuine
plaquette-incidence separation. -/
def centeredClusterSupportDistance
    (S T : Finset (PositiveEdge d)) : ℕ :=
  if Disjoint S T then globalObservablePlaquetteSeparation S T else 0

/-- Explicit distance-independent amplitude used for the concrete centered
two-root certificate.  The last two terms give the trivial covariance bound
when supports overlap. -/
def centeredClusterObservableAmplitude
    (F H : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℂ) : ℝ :=
  bivariateDecoratedObservableUniformClusteringAmplitude
      (d := d) F H Φ β +
    ‖(F.mul H).toBoundedContinuousMap‖ +
    ‖F.toBoundedContinuousMap‖ * ‖H.toBoundedContinuousMap‖

theorem centeredClusterObservableAmplitude_nonneg
    (F H : LocalObservable d G) (Φ : RealPlaquettePotential G) (β : ℂ) :
    0 ≤ centeredClusterObservableAmplitude (d := d) F H Φ β := by
  unfold centeredClusterObservableAmplitude
  exact add_nonneg
    (add_nonneg
      (bivariateDecoratedObservableUniformClusteringAmplitude_nonneg F H Φ β)
      (norm_nonneg _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The concrete two-root cluster-expansion certificate along arbitrary
centered exterior data, built on any one-root centered limit certificate.
No Dobrushin comparison estimate enters this construction. -/
def centeredObservableAmplitudeClusterCertificate
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (C : ClusterLimitCertificate (centeredGibbsSequence η Φ β)) :
    ObservableAmplitudeClusterCertificate (centeredGibbsSequence η Φ β) where
  toClusterLimitCertificate := C
  supportDistance := centeredClusterSupportDistance
  amplitude := fun F H => centeredClusterObservableAmplitude F H Φ (β : ℂ)
  amplitude_nonneg := fun F H =>
    centeredClusterObservableAmplitude_nonneg F H Φ (β : ℂ)
  rate := plaquetteClusterDecayRate (d := d) Φ (β : ℂ)
  rate_pos := plaquetteClusterDecayRate_pos Φ hβ
  rate_lt_one := plaquetteClusterDecayRate_lt_one Φ hβ
  eventual_truncatedCorrelation_bound := by
    intro F H
    by_cases hFH : Disjoint F.support H.support
    · obtain ⟨N, hN⟩ :=
        norm_centered_complexGibbsTruncatedCorrelation_le_globalSeparation_eventually
          F H η Φ hFH hβ
      refine ⟨N, fun n hn => ?_⟩
      have hcluster := hN n hn
      have hamp :
          bivariateDecoratedObservableUniformClusteringAmplitude
              (d := d) F H Φ (β : ℂ) ≤
            centeredClusterObservableAmplitude F H Φ (β : ℂ) := by
        unfold centeredClusterObservableAmplitude
        simpa [add_assoc] using
          (le_add_of_nonneg_right
            (add_nonneg (norm_nonneg ((F.mul H).toBoundedContinuousMap))
              (mul_nonneg (norm_nonneg F.toBoundedContinuousMap)
                (norm_nonneg H.toBoundedContinuousMap))) :
            bivariateDecoratedObservableUniformClusteringAmplitude
                (d := d) F H Φ (β : ℂ) ≤
              bivariateDecoratedObservableUniformClusteringAmplitude
                  (d := d) F H Φ (β : ℂ) +
                (‖(F.mul H).toBoundedContinuousMap‖ +
                  ‖F.toBoundedContinuousMap‖ * ‖H.toBoundedContinuousMap‖))
      have hpow : 0 ≤ plaquetteClusterDecayRate (d := d) Φ (β : ℂ) ^
          globalObservablePlaquetteSeparation F.support H.support :=
        pow_nonneg (plaquetteClusterDecayRate_pos Φ hβ).le _
      calc
        ‖truncatedCorrelation (centeredGibbsSequence η Φ β n) F H‖ =
            ‖complexGibbsExpectation (F.mul H)
                (centeredSpecification n (η n)) Φ (β : ℂ) -
              complexGibbsExpectation F
                  (centeredSpecification n (η n)) Φ (β : ℂ) *
                complexGibbsExpectation H
                  (centeredSpecification n (η n)) Φ (β : ℂ)‖ := by
          simp only [truncatedCorrelation, centeredGibbsSequence,
            localExpectation_fullGibbsProbability]
        _ ≤ bivariateDecoratedObservableUniformClusteringAmplitude
              (d := d) F H Φ (β : ℂ) *
            plaquetteClusterDecayRate (d := d) Φ (β : ℂ) ^
              globalObservablePlaquetteSeparation F.support H.support := hcluster
        _ ≤ centeredClusterObservableAmplitude F H Φ (β : ℂ) *
            plaquetteClusterDecayRate (d := d) Φ (β : ℂ) ^
              globalObservablePlaquetteSeparation F.support H.support :=
          mul_le_mul_of_nonneg_right hamp hpow
        _ = _ := by simp [centeredClusterSupportDistance, hFH]
    · refine ⟨0, fun n _ => ?_⟩
      let μ := centeredGibbsSequence η Φ β n
      have hmul : ‖localExpectation μ F * localExpectation μ H‖ ≤
          ‖F.toBoundedContinuousMap‖ * ‖H.toBoundedContinuousMap‖ := by
        rw [norm_mul]
        exact mul_le_mul (norm_localExpectation_le μ F)
          (norm_localExpectation_le μ H) (norm_nonneg _) (norm_nonneg _)
      have htrivial : ‖truncatedCorrelation μ F H‖ ≤
          ‖(F.mul H).toBoundedContinuousMap‖ +
            ‖F.toBoundedContinuousMap‖ * ‖H.toBoundedContinuousMap‖ := by
        exact (norm_sub_le _ _).trans
          (add_le_add (norm_localExpectation_le μ (F.mul H)) hmul)
      calc
        ‖truncatedCorrelation (centeredGibbsSequence η Φ β n) F H‖ ≤
            ‖(F.mul H).toBoundedContinuousMap‖ +
              ‖F.toBoundedContinuousMap‖ * ‖H.toBoundedContinuousMap‖ := htrivial
        _ ≤ centeredClusterObservableAmplitude F H Φ (β : ℂ) := by
          unfold centeredClusterObservableAmplitude
          have hnonneg :=
            bivariateDecoratedObservableUniformClusteringAmplitude_nonneg
              F H Φ (β : ℂ)
          linarith
        _ = _ := by simp [centeredClusterSupportDistance, hFH]

/-- The explicit positive mass supplied by the strict KP cardinality tilt. -/
def centeredClusterMass
    (Φ : RealPlaquettePotential G) (β : ℂ) : ℝ :=
  -Real.log (plaquetteClusterDecayRate (d := d) Φ β)

theorem centeredClusterMass_pos
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    0 < centeredClusterMass (d := d) Φ β := by
  exact neg_pos.mpr (Real.log_neg
    (plaquetteClusterDecayRate_pos Φ hβ)
    (plaquetteClusterDecayRate_lt_one Φ hβ))

/-- Concrete infinite-volume exponential clustering along centered boxes,
conditional only on the one-root centered limit certificate.  The two-root
input and its explicit mass are fully discharged by the cluster expansion. -/
theorem centeredClusterLimit_exponential_clustering_exp
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ)
    (hβ : ‖(β : ℂ)‖ < latticeStrongCouplingRadius d Φ.bound)
    (C : ClusterLimitCertificate (centeredGibbsSequence η Φ β))
    (F H : LocalObservable d G) :
    ‖C.stateTruncatedCorrelation F H‖ ≤
      centeredClusterObservableAmplitude F H Φ (β : ℂ) *
        Real.exp (-centeredClusterMass (d := d) Φ (β : ℂ) *
          (centeredClusterSupportDistance F.support H.support : ℝ)) := by
  let X := centeredObservableAmplitudeClusterCertificate η Φ β hβ C
  simpa [X, centeredClusterMass,
    ObservableAmplitudeClusterCertificate.clusteringMass] using
    (X.exponential_clustering_exp F H)

end

end YangMills.StrongCoupling
