/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.KoteckyPreiss
import YangMills.Polymer.OrderedComponentPartition
import YangMills.Polymer.RootedForestPartition
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Labelled-set summation for the KP rooted-tree recursion

This file supplies the exponential-species calculation absent from Mathlib:
an unordered family of labelled children is obtained from ordered labelings by
division by the factorial, and its sum is the exponential occurring in the
Kotecký--Preiss tree recursion.  The result is stated both as an analytic
`HasSum` and in the symmetric-multiset convention used by Mayer multi-indices.

This is the local branching half of the rooted-tree summation bridge.  The
remaining graph-theoretic half identifies a spanning tree, rooted at a chosen
occurrence, with its recursively partitioned child subtrees.
-/

namespace YangMills.Polymer

open scoped BigOperators

noncomputable section

namespace FinitePolymerModel

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The two finite presentations of spanning trees used by the Penrose and
root-decomposition modules coincide. -/
theorem graphSpanningTrees_eq_spanningTreeGraphs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    graphSpanningTrees G = spanningTreeGraphs G := by
  classical
  ext T
  simp [graphSpanningTrees, spanningTreeGraphs, spanningSubgraphs]

/-- Graph isomorphisms preserve the finite number of spanning trees. -/
theorem card_graphSpanningTrees_eq_of_iso
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    (graphSpanningTrees G).card = (graphSpanningTrees H).card := by
  classical
  rw [graphSpanningTrees_eq_spanningTreeGraphs,
    graphSpanningTrees_eq_spanningTreeGraphs]
  apply Finset.card_bij
      (fun T (_hT : T ∈ spanningTreeGraphs G) =>
        T.comap e.toEquiv.symm.toEmbedding)
  · intro T hT
    have hdata := (mem_spanningTreeGraphs G T).mp hT
    apply (mem_spanningTreeGraphs H _).mpr
    constructor
    · intro v w hTvw
      have hGvw : G.Adj (e.symm v) (e.symm w) := hdata.1 hTvw
      simpa using (e.map_rel_iff.mpr hGvw)
    · exact (SimpleGraph.Iso.comap e.toEquiv.symm T).isTree_iff.mpr hdata.2
  · intro T₁ _ T₂ _ heq
    ext v w
    have h := congrArg
      (fun U : SimpleGraph W => U.Adj (e v) (e w)) heq
    have hvw : T₁.Adj v w = T₂.Adj v w := by
      change T₁.Adj (e.symm (e v)) (e.symm (e w)) =
        T₂.Adj (e.symm (e v)) (e.symm (e w)) at h
      rw [e.symm_apply_apply v, e.symm_apply_apply w] at h
      exact h
    exact iff_of_eq hvw
  · intro U hU
    let T := U.comap e.toEquiv.toEmbedding
    have hmapT : T.comap e.toEquiv.symm.toEmbedding = U := by
      dsimp [T]
      ext v w
      change U.Adj (e (e.symm v)) (e (e.symm w)) ↔ U.Adj v w
      simp only [e.apply_symm_apply]
    refine ⟨T, ?_, hmapT⟩
    have hdata := (mem_spanningTreeGraphs H U).mp hU
    apply (mem_spanningTreeGraphs G T).mpr
    constructor
    · intro v w hUvw
      exact (e.map_rel_iff.mp (hdata.1 hUvw))
    · exact (SimpleGraph.Iso.comap e.toEquiv U).isTree_iff.mpr hdata.2

local instance labelledConnectedComponentFintype {V : Type*} [Finite V]
    (G : SimpleGraph V) : Fintype G.ConnectedComponent :=
  Fintype.ofFinite G.ConnectedComponent

local instance labelledConnectedComponentSupportFintype
    {V : Type*} [Finite V] (G : SimpleGraph V)
    (c : G.ConnectedComponent) : Fintype ↥c :=
  Fintype.ofFinite ↥c

/-- Histogram of labels on a finite vertex type.  This is the canonical
Mayer multi-index carried by a labelled child subtree. -/
def labelHistogram {V : Type*} [Fintype V]
    (label : V → P) : MayerMultiIndex P :=
  ∑ v : V, Finsupp.single (label v) 1

omit [Fintype P] in
@[simp]
theorem labelHistogram_apply {V : Type*} [Fintype V]
    (label : V → P) (child : P) :
    labelHistogram label child =
      ((Finset.univ : Finset V).filter (fun v => label v = child)).card := by
  classical
  rw [labelHistogram]
  change (Finsupp.applyAddHom child)
    (∑ v : V, Finsupp.single (label v) 1) = _
  rw [map_sum]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : label v = child
  · simp [h]
  · simp [h, Ne.symm h]

/-- The total multiplicity of a label histogram is the number of labelled
vertices. -/
theorem mayerDegree_labelHistogram {V : Type*} [Fintype V]
    (label : V → P) :
    mayerDegree (labelHistogram label) = Fintype.card V := by
  classical
  rw [mayerDegree]
  simp only [labelHistogram_apply]
  simpa using (Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset V)) (t := (Finset.univ : Finset P))
      (f := label) (by simp)).symm

/-- All labelings of `Fin n` with a prescribed histogram. -/
def labelingsWithHistogram (n : ℕ) (X : MayerMultiIndex P) :
    Finset (Fin n → P) :=
  Finset.univ.filter fun label => labelHistogram label = X

omit [Fintype P] [DecidableEq P] in
/-- The monomial carried by a labelled tuple is the monomial of its
histogram. -/
theorem prod_X_label_eq_monomial_labelHistogram
    (n : ℕ) (label : Fin n → P) :
    (∏ i : Fin n, MvPolynomial.X (label i) : MvPolynomial P ℕ) =
      MvPolynomial.monomial (labelHistogram label) 1 := by
  rw [labelHistogram, MvPolynomial.monomial_sum_one]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [pow_one] using
    (MvPolynomial.X_pow_eq_monomial (R := ℕ) (n := label i) (e := 1)).symm

/-- The histogram fiber has the expected multinomial cardinality.  This is
the actual labelled-orbit count, obtained coefficientwise from Mathlib's
multivariate multinomial theorem. -/
theorem card_labelingsWithHistogram_eq_countPerms
    (n : ℕ) (X : MayerMultiIndex P) (hX : mayerDegree X = n) :
    (labelingsWithHistogram n X).card = X.toMultiset.countPerms := by
  classical
  let polynomial : MvPolynomial P ℕ :=
    (∑ child : P, MvPolynomial.X child) ^ n
  have hexpand : polynomial =
      ∑ label : Fin n → P,
        MvPolynomial.monomial (labelHistogram label) 1 := by
    unfold polynomial
    rw [Fintype.sum_pow]
    apply Finset.sum_congr rfl
    intro label _
    exact prod_X_label_eq_monomial_labelHistogram n label
  have hcoeffMultinomial : MvPolynomial.coeff X polynomial =
      X.toMultiset.countPerms := by
    unfold polynomial
    rw [MvPolynomial.coeff_sum_X_pow_of_fintype, if_pos]
    · simp [Multiset.countPerms]
    · simpa [mayerDegree, Finsupp.sum_fintype X
        (fun _ n => n) (fun _ => rfl)] using hX
  have hcoeffFiber : MvPolynomial.coeff X polynomial =
      (labelingsWithHistogram n X).card := by
    rw [hexpand]
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [labelingsWithHistogram, Finset.card_filter]
  exact hcoeffFiber.symm.trans hcoeffMultinomial

/-- A symmetric weight with values in any additive commutative monoid can be
summed either over all labelled tuples or over multi-indices with their exact
orbit cardinality. -/
theorem sum_labelings_weight_eq_sum_countPerms_histogramWeight_generic
    {R : Type*} [AddCommMonoid R]
    (n : ℕ) (weight : MayerMultiIndex P → R) :
    ∑ label : Fin n → P, weight (labelHistogram label) =
      ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        X.toMultiset.countPerms • weight X := by
  classical
  calc
    ∑ label : Fin n → P, weight (labelHistogram label) =
        ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
          ∑ label ∈ labelingsWithHistogram n X,
            weight (labelHistogram label) := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro label _
      exact (mem_mayerMultiIndicesOfDegree n _).mpr <| by
        rw [mayerDegree_labelHistogram]
        simp
    _ = ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        X.toMultiset.countPerms • weight X := by
      apply Finset.sum_congr rfl
      intro X hX
      have hdegree := (mem_mayerMultiIndicesOfDegree n X).mp hX
      calc
        ∑ label ∈ labelingsWithHistogram n X,
            weight (labelHistogram label) =
            ∑ _label ∈ labelingsWithHistogram n X, weight X := by
          apply Finset.sum_congr rfl
          intro label hlabel
          rw [(Finset.mem_filter.mp hlabel).2]
        _ = X.toMultiset.countPerms • weight X := by
          rw [Finset.sum_const,
            card_labelingsWithHistogram_eq_countPerms n X hdegree]

/-- Real specialization of exact histogram-orbit regrouping. -/
theorem sum_labelings_weight_eq_sum_countPerms_histogramWeight
    (n : ℕ) (weight : MayerMultiIndex P → ℝ) :
    ∑ label : Fin n → P, weight (labelHistogram label) =
      ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        (X.toMultiset.countPerms : ℝ) * weight X := by
  simpa [nsmul_eq_mul] using
    sum_labelings_weight_eq_sum_countPerms_histogramWeight_generic
      (P := P) n weight

/-- Complex specialization of exact histogram-orbit regrouping. -/
theorem sum_labelings_weight_eq_sum_countPerms_histogramWeight_complex
    (n : ℕ) (weight : MayerMultiIndex P → ℂ) :
    ∑ label : Fin n → P, weight (labelHistogram label) =
      ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
        (X.toMultiset.countPerms : ℂ) * weight X := by
  simpa [nsmul_eq_mul] using
    sum_labelings_weight_eq_sum_countPerms_histogramWeight_generic
      (P := P) n weight

/-- The histogram of all labelled occurrences of `X` is `X` itself. -/
theorem labelHistogram_mayerVertex (X : MayerMultiIndex P) :
    labelHistogram (fun v : MayerVertex X => v.1) = X := by
  classical
  ext child
  rw [labelHistogram_apply, Finset.card_filter]
  calc
    (∑ i : MayerVertex X, if i.1 = child then 1 else 0) =
        ∑ γ : P, ∑ _i : Fin (X γ),
          if γ = child then 1 else 0 :=
      Fintype.sum_sigma' (fun γ (_i : Fin (X γ)) =>
        if γ = child then 1 else 0)
    _ = X child := by
      rw [Finset.sum_eq_single child]
      · simp
      · intro other _ hne
        simp [hne]
      · simp

/-- A finite labelled occurrence type is canonically equivalent, after a
choice of finite fiber enumerations, to the Mayer occurrence type of its
label histogram.  This is the fixed-labelled replacement for transporting
directly between the dependent types `MayerVertex X` as `X` varies. -/
noncomputable def histogramVertexEquiv {V : Type*} [Fintype V]
    (label : V → P) : V ≃ MayerVertex (labelHistogram label) :=
  (Equiv.sigmaFiberEquiv label).symm.trans <|
    Equiv.sigmaCongrRight fun child =>
      Fintype.equivOfCardEq <| by
        rw [labelHistogram_apply]
        simpa only [Fintype.card_fin] using
          Fintype.card_subtype (fun v => label v = child)

omit [Fintype P] in
@[simp]
theorem histogramVertexEquiv_fst {V : Type*} [Fintype V]
    (label : V → P) (v : V) :
    (histogramVertexEquiv label v).1 = label v := by
  rfl

/-- The incompatibility graph on a fixed finite occurrence type. -/
def labelledIncompatibilityGraph {V : Type*}
    (M : FinitePolymerModel P) (label : V → P) : SimpleGraph V where
  Adj v w := v ≠ w ∧ M.incompatible (label v) (label w)
  symm _v _w h := ⟨Ne.symm h.1, M.symmetric_incompatible h.2⟩
  loopless := ⟨fun _v h => h.1 rfl⟩

@[simp]
theorem labelledIncompatibilityGraph_adj {V : Type*}
    (M : FinitePolymerModel P) (label : V → P) (v w : V) :
    (labelledIncompatibilityGraph M label).Adj v w ↔
      v ≠ w ∧ M.incompatible (label v) (label w) :=
  Iff.rfl

/-- Relabelling fixed occurrences by their histogram fiber indices is a graph
isomorphism onto the usual dependent Mayer incompatibility graph. -/
noncomputable def labelledIncompatibilityGraphIso
    {V : Type*} [Fintype V]
    (M : FinitePolymerModel P) (label : V → P) :
    labelledIncompatibilityGraph M label ≃g
      M.mayerIncompatibilityGraph (labelHistogram label) where
  toEquiv := histogramVertexEquiv label
  map_rel_iff' := by
    intro v w
    simp [labelledIncompatibilityGraph, mayerIncompatibilityGraph]

/-- The connected signed graph weight of a fixed labelled tuple depends only
on its histogram. -/
theorem connectedSpanningGraphSum_labelledIncompatibilityGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : FinitePolymerModel P) (label : V → P) :
    connectedSpanningGraphSum (labelledIncompatibilityGraph M label) =
      M.mayerUrsell (labelHistogram label) := by
  exact connectedSpanningGraphSum_eq_of_iso
    (labelledIncompatibilityGraphIso M label)

/-- The fixed-labelled incompatibility graph has exactly the same spanning
trees as the Mayer graph of its histogram. -/
theorem card_labelledIncompatibilityGraph_eq_mayer
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : FinitePolymerModel P) (label : V → P) :
    (graphSpanningTrees (labelledIncompatibilityGraph M label)).card =
      (graphSpanningTrees
        (M.mayerIncompatibilityGraph (labelHistogram label))).card := by
  exact card_graphSpanningTrees_eq_of_iso
    (labelledIncompatibilityGraphIso M label)

/-- A Mayer occurrence type has cardinality equal to the degree of its
multi-index. -/
theorem card_mayerVertex (X : MayerMultiIndex P) :
    Fintype.card (MayerVertex X) = mayerDegree X := by
  classical
  rw [Fintype.card_sigma, mayerDegree]
  apply Finset.sum_congr rfl
  intro child _
  exact Fintype.card_fin (X child)

/-- A fixed `Fin n` enumeration of the occurrences of a degree-`n`
multi-index. -/
noncomputable def fixedMayerVertexEquiv
    (n : ℕ) (X : MayerMultiIndex P) (hX : mayerDegree X = n) :
    Fin n ≃ MayerVertex X :=
  Fintype.equivOfCardEq <| by
    rw [Fintype.card_fin, card_mayerVertex, hX]

/-- Polymer labels on the fixed occurrence type `Fin n`. -/
noncomputable def fixedMayerLabel
    (n : ℕ) (X : MayerMultiIndex P) (hX : mayerDegree X = n) :
    Fin n → P :=
  fun i => (fixedMayerVertexEquiv n X hX i).1

/-- The chosen fixed enumeration has exactly the prescribed histogram. -/
theorem labelHistogram_fixedMayerLabel
    (n : ℕ) (X : MayerMultiIndex P) (hX : mayerDegree X = n) :
    labelHistogram (fixedMayerLabel n X hX) = X := by
  classical
  unfold fixedMayerLabel labelHistogram
  calc
    (∑ i : Fin n,
        Finsupp.single ((fixedMayerVertexEquiv n X hX i).1) 1) =
      ∑ v : MayerVertex X, Finsupp.single v.1 1 :=
        Fintype.sum_equiv (fixedMayerVertexEquiv n X hX)
          _ _ (fun _ => rfl)
    _ = X := labelHistogram_mayerVertex X

/-- Add one distinguished root to a fixed residual occurrence type. -/
def fixedRootedMayerLabel
    (root : P) {n : ℕ} (label : Fin n → P) : Option (Fin n) → P
  | none => root
  | some i => label i

omit [Fintype P] [DecidableEq P] in
/-- The root-extended fixed label has residual histogram plus one root
occurrence. -/
theorem labelHistogram_fixedRootedMayerLabel
    (root : P) {n : ℕ} (label : Fin n → P) :
    labelHistogram (fixedRootedMayerLabel root label) =
      labelHistogram label + Finsupp.single root 1 := by
  classical
  unfold labelHistogram
  rw [Fintype.sum_option]
  simp only [fixedRootedMayerLabel]
  ac_rfl

/-- The graph on the fixed root plus `n` residual occurrences has the Mayer
spanning-tree count of the corresponding root-augmented multi-index. -/
theorem card_fixedRootedMayerGraph
    (M : FinitePolymerModel P) (root : P)
    (n : ℕ) (X : MayerMultiIndex P) (hX : mayerDegree X = n) :
    (graphSpanningTrees (labelledIncompatibilityGraph M
        (fixedRootedMayerLabel root (fixedMayerLabel n X hX)))).card =
      (graphSpanningTrees (M.mayerIncompatibilityGraph
        (X + Finsupp.single root 1))).card := by
  rw [card_labelledIncompatibilityGraph_eq_mayer,
    labelHistogram_fixedRootedMayerLabel,
    labelHistogram_fixedMayerLabel]

/-- Fixed-labelled residual activity products recover the multi-index
activity monomial. -/
theorem prod_fixedMayerLabel_norm_activity
    (M : FinitePolymerModel P)
    (n : ℕ) (X : MayerMultiIndex P) (hX : mayerDegree X = n) :
    ∏ i : Fin n, ‖M.activity (fixedMayerLabel n X hX i)‖ =
      ∏ child : P, ‖M.activity child‖ ^ X child := by
  calc
    (∏ i : Fin n, ‖M.activity (fixedMayerLabel n X hX i)‖) =
        ∏ v : MayerVertex X, ‖M.activity v.1‖ := by
      exact Fintype.prod_equiv (fixedMayerVertexEquiv n X hX)
        (fun i => ‖M.activity (fixedMayerLabel n X hX i)‖)
        (fun v => ‖M.activity v.1‖) (fun _ => rfl)
    _ = ∏ child : P, ‖M.activity child‖ ^ X child := by
      calc
        (∏ v : MayerVertex X, ‖M.activity v.1‖) =
            ∏ child : P, ∏ _i : Fin (X child), ‖M.activity child‖ :=
          Fintype.prod_sigma (fun v : MayerVertex X => ‖M.activity v.1‖)
        _ = ∏ child : P, ‖M.activity child‖ ^ X child := by
          apply Finset.prod_congr rfl
          intro child _
          simp

/-- A finite labelled sum can be regrouped by its label histogram. -/
theorem labelHistogram_weighted_sum {V : Type*} [Fintype V]
    (label : V → P) (weight : P → ℝ) :
    ∑ γ : P, (labelHistogram label γ : ℝ) * weight γ =
      ∑ v : V, weight (label v) := by
  classical
  calc
    ∑ γ : P, (labelHistogram label γ : ℝ) * weight γ =
        ∑ γ : P,
          ∑ v ∈ (Finset.univ : Finset V).filter (fun v => label v = γ),
            weight (label v) := by
      apply Finset.sum_congr rfl
      intro γ _hγ
      rw [labelHistogram_apply]
      calc
        (({v ∈ (Finset.univ : Finset V) | label v = γ}.card : ℝ) *
            weight γ) =
          ∑ v ∈ (Finset.univ : Finset V).filter (fun v => label v = γ),
            weight γ := by simp
        _ = ∑ v ∈ (Finset.univ : Finset V).filter (fun v => label v = γ),
            weight (label v) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [(Finset.mem_filter.mp hv).2]
    _ = ∑ γ : P, ∑ i : {v : V // label v = γ},
          weight (label i.1) := by
      apply Finset.sum_congr rfl
      intro γ _hγ
      rw [← Finset.sum_subtype
        ((Finset.univ : Finset V).filter fun v => label v = γ)
        (by simp) (fun v => weight (label v))]
    _ = ∑ v : V, weight (label v) :=
      Fintype.sum_fiberwise label (fun v => weight (label v))

omit [Fintype P] [DecidableEq P] in
/-- Splitting a finite labelled type into one distinguished root and its
complement splits its histogram additively. -/
theorem labelHistogram_away_add_single
    {V : Type*} [Fintype V] [DecidableEq V]
    (label : V → P) (root : V) :
    labelHistogram (fun v : {x : V // x ≠ root} => label v.1) +
        Finsupp.single (label root) 1 =
      labelHistogram label := by
  classical
  unfold labelHistogram
  rw [← Finset.sum_subtype ((Finset.univ : Finset V).erase root)
    (by simp) (fun v => Finsupp.single (label v) 1)]
  exact Finset.sum_erase_add (Finset.univ : Finset V)
    (fun v => Finsupp.single (label v) 1) (Finset.mem_univ root)

omit [Fintype P] [DecidableEq P] in
/-- Every labelled occurrence of a Mayer multi-index has a label in its
support. -/
theorem mayerVertex_fst_mem_support {X : MayerMultiIndex P}
    (v : MayerVertex X) : v.1 ∈ X.support := by
  rw [Finsupp.mem_support_iff]
  exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) v.2.isLt)

/-- Multi-index of polymer labels carried by one child component after a
Mayer spanning tree is cut at its root. -/
noncomputable def mayerChildMultiIndex
    {X : MayerMultiIndex P} {T : SimpleGraph (MayerVertex X)}
    (root : MayerVertex X)
    (c : (awayGraph T root).ConnectedComponent) : MayerMultiIndex P := by
  letI : Fintype ↥c := Fintype.ofFinite ↥c
  exact labelHistogram (fun v : ↥c => v.1.1.1)

/-- The degree of a child multi-index is exactly the number of occurrences in
that root-deleted component. -/
theorem mayerDegree_mayerChildMultiIndex
    {X : MayerMultiIndex P} {T : SimpleGraph (MayerVertex X)}
    (root : MayerVertex X)
    (c : (awayGraph T root).ConnectedComponent) :
    mayerDegree (mayerChildMultiIndex root c) = Nat.card ↥c := by
  classical
  letI : Fintype ↥c := Fintype.ofFinite ↥c
  rw [mayerChildMultiIndex, mayerDegree_labelHistogram,
    Nat.card_eq_fintype_card]

/-- The child histograms regroup exactly to the histogram of all non-root
occurrences.  No multiplicity is lost or duplicated when the rooted tree is
split into connected components. -/
theorem sum_mayerChildMultiIndex_eq_awayHistogram
    {X : MayerMultiIndex P} {T : SimpleGraph (MayerVertex X)}
    (root : MayerVertex X) :
    ∑ c : (awayGraph T root).ConnectedComponent,
        mayerChildMultiIndex root c =
      labelHistogram (fun v : {x : MayerVertex X // x ≠ root} => v.1.1) := by
  classical
  unfold mayerChildMultiIndex labelHistogram
  exact sum_connectedComponents_sum (awayGraph T root)
    (fun v => Finsupp.single v.1.1 1)

/-- Exact occurrence bookkeeping for root deletion: the unordered child
multi-indices, together with the distinguished root occurrence, sum to the
original Mayer multi-index. -/
theorem sum_mayerChildMultiIndex_add_root
    {X : MayerMultiIndex P} {T : SimpleGraph (MayerVertex X)}
    (root : MayerVertex X) :
    (∑ c : (awayGraph T root).ConnectedComponent,
        mayerChildMultiIndex root c) + Finsupp.single root.1 1 = X := by
  rw [sum_mayerChildMultiIndex_eq_awayHistogram]
  exact (labelHistogram_away_add_single
    (fun v : MayerVertex X => v.1) root).trans
      (labelHistogram_mayerVertex X)

/-- Equivalently, the sum of the child histograms is the multi-index obtained
by deleting the distinguished root occurrence. -/
theorem sum_mayerChildMultiIndex_eq_eraseRootOccurrence
    {X : MayerMultiIndex P} {T : SimpleGraph (MayerVertex X)}
    (root : MayerVertex X) :
    (∑ c : (awayGraph T root).ConnectedComponent,
        mayerChildMultiIndex root c) = eraseRootOccurrence X root.1 := by
  classical
  ext γ
  have h := congrArg (fun Y : MayerMultiIndex P => Y γ)
    (sum_mayerChildMultiIndex_add_root (T := T) root)
  change (∑ c : (awayGraph T root).ConnectedComponent,
    mayerChildMultiIndex root c) γ + (Finsupp.single root.1 1) γ = X γ at h
  rw [eraseRootOccurrence, Finsupp.update_apply]
  by_cases hγ : γ = root.1
  · subst γ
    rw [if_pos rfl]
    simp only [Finsupp.single_eq_same] at h
    omega
  · rw [if_neg hγ]
    have hγ' : root.1 ≠ γ := Ne.symm hγ
    rw [Finsupp.single_apply, if_neg hγ', add_zero] at h
    exact h

/-- The symmetry factor of the complete child family is exactly the residual
pinned symmetry factor. -/
theorem mayerSymmetryFactor_sum_mayerChildMultiIndex
    {X : MayerMultiIndex P} {T : SimpleGraph (MayerVertex X)}
    (root : MayerVertex X) :
    mayerSymmetryFactor
        (∑ c : (awayGraph T root).ConnectedComponent,
          mayerChildMultiIndex root c) =
      pinnedMayerSymmetryFactor X root.1 := by
  rw [sum_mayerChildMultiIndex_eq_eraseRootOccurrence]
  exact mayerSymmetryFactor_eraseRootOccurrence_eq_pinnedMayerSymmetryFactor
    X root.1

/-- Multiplicative weight of a label histogram. -/
def histogramWeight {R : Type*} [CommMonoid R]
    (w : P → R) (X : MayerMultiIndex P) : R :=
  X.prod fun γ n => w γ ^ n

@[simp]
theorem histogramWeight_eq_prod {R : Type*} [CommMonoid R]
    (w : P → R) (X : MayerMultiIndex P) :
    histogramWeight w X = ∏ γ : P, w γ ^ X γ :=
  Finsupp.prod_pow X w

omit [Fintype P] [DecidableEq P] in
@[simp]
theorem histogramWeight_add {R : Type*} [CommMonoid R]
    (w : P → R) (X Y : MayerMultiIndex P) :
    histogramWeight w (X + Y) =
      histogramWeight w X * histogramWeight w Y := by
  exact Finsupp.prod_add_index' (fun γ => pow_zero (w γ))
    (fun γ m n => pow_add (w γ) m n)

/-- The histogram weight is an additive-to-multiplicative homomorphism. -/
def histogramWeightAddHom {R : Type*} [CommMonoid R]
    (w : P → R) : (MayerMultiIndex P) →+ Additive R where
  toFun X := Additive.ofMul (histogramWeight w X)
  map_zero' := by simp [histogramWeight]
  map_add' X Y := by
    change histogramWeight w (X + Y) =
      histogramWeight w X * histogramWeight w Y
    exact histogramWeight_add w X Y

omit [Fintype P] [DecidableEq P] in
/-- Weights of a finite sum of histograms factor as the product of their
weights. -/
theorem histogramWeight_sum {R C : Type*} [CommMonoid R] [Fintype C]
    (w : P → R) (Y : C → MayerMultiIndex P) :
    histogramWeight w (∑ c : C, Y c) =
      ∏ c : C, histogramWeight w (Y c) := by
  change (histogramWeightAddHom w) (∑ c : C, Y c) =
    ∑ c : C, (histogramWeightAddHom w) (Y c)
  rw [map_sum]

omit [Fintype P] [DecidableEq P] in
/-- The multiplicative weight of a label histogram is the product of the
weights of its labelled occurrences. -/
theorem histogramWeight_labelHistogram
    {R V : Type*} [CommMonoid R] [Fintype V]
    (w : P → R) (label : V → P) :
    histogramWeight w (labelHistogram label) =
      ∏ v : V, w (label v) := by
  rw [labelHistogram, histogramWeight_sum]
  simp [histogramWeight]

/-- Splitting off a distinguished Mayer occurrence factors the activity
monomial into its root weight and the residual labelled-occurrence product. -/
theorem histogramWeight_mayerVertex_eq_root_mul_prod_away
    {R : Type*} [CommMonoid R] (w : P → R)
    (X : MayerMultiIndex P) (root : MayerVertex X) :
    histogramWeight w X = w root.1 *
      ∏ v : {v : MayerVertex X // v ≠ root}, w v.1.1 := by
  calc
    histogramWeight w X = histogramWeight w
        (labelHistogram (fun v : MayerVertex X => v.1)) := by
      rw [labelHistogram_mayerVertex]
    _ = histogramWeight w
        (labelHistogram
          (fun v : {x : MayerVertex X // x ≠ root} => v.1.1) +
          Finsupp.single root.1 1) := by
      rw [labelHistogram_away_add_single]
    _ = w root.1 *
        ∏ v : {v : MayerVertex X // v ≠ root}, w v.1.1 := by
      rw [histogramWeight_add, histogramWeight_labelHistogram]
      simp [histogramWeight, mul_comm]

/-- Norm-activity form of the preceding occurrence factorization. -/
theorem prod_norm_activity_pow_eq_root_mul_prod_away
    (M : FinitePolymerModel P) (X : MayerMultiIndex P)
    (root : MayerVertex X) :
    (∏ γ : P, ‖M.activity γ‖ ^ X γ) =
      ‖M.activity root.1‖ *
        ∏ v : {v : MayerVertex X // v ≠ root},
          ‖M.activity v.1.1‖ := by
  rw [← histogramWeight_eq_prod]
  exact histogramWeight_mayerVertex_eq_root_mul_prod_away
    (fun γ => ‖M.activity γ‖) X root

/-! ## Histograms of common-ambient component data -/

/-- Label histogram of every vertex carried by common-ambient component
data. -/
def componentDataLabelHistogram
    {W : Type*} [Fintype W] [DecidableEq W]
    (label : W → P) (D : ForestComponentData W) : MayerMultiIndex P :=
  labelHistogram (fun v : {x : W // x ∈ D.1} => label v.1)

/-- Label histogram of the vertices in component data that are allowed as
attachments to the parent root. -/
def componentDataAllowedLabelHistogram
    {W : Type*} [Fintype W] [DecidableEq W]
    (label : W → P) (allowed : Finset W)
    (D : ForestComponentData W) : MayerMultiIndex P :=
  labelHistogram
    (fun v : {x : W // x ∈ D.1.filter (· ∈ allowed)} => label v.1)

/-- Component vertex weights depend only on the component's label
histogram. -/
theorem componentDataVertexWeight_eq_histogramWeight
    {W : Type*} [Fintype W] [DecidableEq W]
    (label : W → P) (weight : P → ℝ) (D : ForestComponentData W) :
    componentDataVertexWeight (fun v => weight (label v)) D =
      histogramWeight weight (componentDataLabelHistogram label D) := by
  rw [componentDataLabelHistogram, histogramWeight_labelHistogram,
    componentDataVertexWeight]
  rw [← Finset.prod_subtype D.1 (by simp)
    (fun v => weight (label v))]

/-- The allowed attachment mass is the label-weighted sum of the allowed
attachment histogram, retaining the exact occurrence multiplicities. -/
theorem componentDataAttachmentMass_eq_allowedHistogram
    {W : Type*} [Fintype W] [DecidableEq W]
    (label : W → P) (allowed : Finset W) (weight : P → ℝ)
    (D : ForestComponentData W) :
    componentDataAttachmentMass allowed (fun v => weight (label v)) D =
      ∑ child : P,
        (componentDataAllowedLabelHistogram label allowed D child : ℝ) *
          weight child := by
  rw [componentDataAllowedLabelHistogram,
    labelHistogram_weighted_sum]
  rw [← Finset.sum_subtype (D.1.filter (· ∈ allowed))
    (by simp) (fun v => weight (label v))]
  rfl

/-- The full rooted component-tree weight has a completely symmetric
multi-index presentation. -/
theorem componentDataRootedTreeWeight_eq_histograms
    {W : Type*} [Fintype W] [DecidableEq W]
    (label : W → P) (allowed : Finset W)
    (attachmentWeight vertexWeight : P → ℝ)
    (D : ForestComponentData W) :
    componentDataRootedTreeWeight allowed
        (fun v => attachmentWeight (label v))
        (fun v => vertexWeight (label v)) D =
      (∑ child : P,
        (componentDataAllowedLabelHistogram label allowed D child : ℝ) *
          attachmentWeight child) *
      histogramWeight vertexWeight (componentDataLabelHistogram label D) := by
  rw [componentDataRootedTreeWeight,
    componentDataAttachmentMass_eq_allowedHistogram,
    componentDataVertexWeight_eq_histogramWeight]

/-- Exact weighted version of root deletion.  The activity monomial of the
whole Mayer multi-index is the root activity times the activity monomials of
the unordered child components. -/
theorem histogramWeight_mayerChild_factorization
    {R : Type*} [CommMonoid R] (w : P → R)
    {X : MayerMultiIndex P} {T : SimpleGraph (MayerVertex X)}
    (root : MayerVertex X) :
    histogramWeight w X = w root.1 *
      ∏ c : (awayGraph T root).ConnectedComponent,
        histogramWeight w (mayerChildMultiIndex root c) := by
  calc
    histogramWeight w X = histogramWeight w
        ((∑ c : (awayGraph T root).ConnectedComponent,
          mayerChildMultiIndex root c) + Finsupp.single root.1 1) :=
      congrArg (histogramWeight w)
        (sum_mayerChildMultiIndex_add_root root).symm
    _ = w root.1 *
        ∏ c : (awayGraph T root).ConnectedComponent,
          histogramWeight w (mayerChildMultiIndex root c) := by
      rw [histogramWeight_add, histogramWeight_sum]
      simp [histogramWeight, mul_comm]

/-- If a spanning tree of a Mayer incompatibility graph is cut at a root,
the canonical root of every resulting child component has a polymer label
incompatible with the parent label.  This is the precise graph-to-KP edge
condition used by the recursive summation. -/
theorem mayer_incompatible_childRoot
    (M : FinitePolymerModel P) (X : MayerMultiIndex P)
    {T : SimpleGraph (MayerVertex X)}
    (hT : T.IsTree) (hTG : T ≤ M.mayerIncompatibilityGraph X)
    (root : MayerVertex X)
    (c : (awayGraph T root).ConnectedComponent) :
    M.incompatible root.1 (IsTree.childRoot hT root c).1.1 := by
  exact (hTG (IsTree.adj_childRoot hT root c)).2

/-- The finite unordered-component theorem instantiated on an actual Mayer
incompatibility graph.  It bounds the exact spanning-tree count times the
residual occurrence activity monomial by the exponential of all admissible
rooted child-tree data. -/
theorem card_graphSpanningTrees_mul_prod_away_activity_le_exp_componentTreeSum
    (M : FinitePolymerModel P) (X : MayerMultiIndex P)
    (root : MayerVertex X) :
    (((graphSpanningTrees (M.mayerIncompatibilityGraph X)).card : ℝ) *
      ∏ v : {v : MayerVertex X // v ≠ root},
        ‖M.activity v.1.1‖) ≤
      Real.exp
        (∑ D ∈ treeComponentDataBelow
            (awayGraph (M.mayerIncompatibilityGraph X) root),
          componentDataRootedTreeWeight
            (rootNeighborFinset (M.mayerIncompatibilityGraph X) root)
            (fun _ => 1) (fun v => ‖M.activity v.1.1‖) D) := by
  rw [graphSpanningTrees_eq_spanningTreeGraphs]
  exact card_spanningTreeGraphs_mul_prod_away_le_exp
    (M.mayerIncompatibilityGraph X) root
    (fun v => ‖M.activity v.1.1‖) (fun _ => norm_nonneg _)

/-- Rooted component-tree choices in a Mayer incompatibility graph. -/
def mayerRootedChildTreeChoices
    (M : FinitePolymerModel P) (X : MayerMultiIndex P)
    (root : MayerVertex X) :=
  rootedTreeComponentChoices
    (awayGraph (M.mayerIncompatibilityGraph X) root)
    (rootNeighborFinset (M.mayerIncompatibilityGraph X) root)

/-- The distinguished child root in every Mayer rooted component choice is
incompatible with its parent label. -/
theorem incompatible_mayerRootedChildTreeChoice
    (M : FinitePolymerModel P) (X : MayerMultiIndex P)
    (root : MayerVertex X)
    {p : ForestComponentData {v : MayerVertex X // v ≠ root} ×
      {v : MayerVertex X // v ≠ root}}
    (hp : p ∈ M.mayerRootedChildTreeChoices X root) :
    M.incompatible root.1 p.2.1.1 := by
  have hpdata := (mem_rootedTreeComponentChoices
    (awayGraph (M.mayerIncompatibilityGraph X) root)
    (rootNeighborFinset (M.mayerIncompatibilityGraph X) root) p).mp hp
  exact ((mem_rootNeighborFinset (M.mayerIncompatibilityGraph X)
    root p.2).1 hpdata.2.1).2

/-- Every rooted component-tree occurrence weight is exactly the symmetric
weight of its label histogram. -/
theorem componentDataVertexWeight_mayer_eq_histogramWeight
    (M : FinitePolymerModel P) (X : MayerMultiIndex P)
    (root : MayerVertex X)
    (D : ForestComponentData {v : MayerVertex X // v ≠ root}) :
    componentDataVertexWeight (fun v => ‖M.activity v.1.1‖) D =
      histogramWeight (fun γ => ‖M.activity γ‖)
        (componentDataLabelHistogram (fun v => v.1.1) D) := by
  exact componentDataVertexWeight_eq_histogramWeight
    (fun v : {v : MayerVertex X // v ≠ root} => v.1.1)
    (fun γ => ‖M.activity γ‖) D

/-- Fixed Mayer spanning-tree enumeration in its final rooted-child,
label-histogram form. -/
theorem mayerSpanningTree_residual_le_exp_rootedChoices
    (M : FinitePolymerModel P) (X : MayerMultiIndex P)
    (root : MayerVertex X) :
    (((graphSpanningTrees (M.mayerIncompatibilityGraph X)).card : ℝ) *
      ∏ v : {v : MayerVertex X // v ≠ root},
        ‖M.activity v.1.1‖) ≤
      Real.exp
        (∑ p ∈ M.mayerRootedChildTreeChoices X root,
          histogramWeight (fun γ => ‖M.activity γ‖)
            (componentDataLabelHistogram (fun v => v.1.1) p.1)) := by
  rw [graphSpanningTrees_eq_spanningTreeGraphs]
  have h := card_spanningTreeGraphs_mul_prod_away_le_exp_rootedChoices
    (M.mayerIncompatibilityGraph X) root
    (fun v => ‖M.activity v.1.1‖) (fun _ => norm_nonneg _)
  apply h.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact componentDataVertexWeight_mayer_eq_histogramWeight M X root p.1

/-- A fixed multiplicity-pinned Mayer tree majorant is controlled by the
unordered component-tree exponential with the exact residual orbit factor. -/
theorem pinned_mayerTreeMajorant_le_componentTreeExp
    (M : FinitePolymerModel P) (X : MayerMultiIndex P)
    (root : MayerVertex X) :
    (X root.1 : ℝ) * M.mayerTreeMajorant X ≤
      (‖M.activity root.1‖ /
        (pinnedMayerSymmetryFactor X root.1 : ℝ)) *
      Real.exp
        (∑ D ∈ treeComponentDataBelow
            (awayGraph (M.mayerIncompatibilityGraph X) root),
          componentDataRootedTreeWeight
            (rootNeighborFinset (M.mayerIncompatibilityGraph X) root)
            (fun _ => 1) (fun v => ‖M.activity v.1.1‖) D) := by
  have hroot : X root.1 ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) root.2.isLt)
  have hpinned : (pinnedMayerSymmetryFactor X root.1 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_ne_zero (by
      exact mul_ne_zero (Nat.factorial_ne_zero _)
        (Finset.prod_ne_zero_iff.mpr
          (fun γ _ => Nat.factorial_ne_zero (X γ)))))
  have hrootCast : (X root.1 : ℝ) ≠ 0 := by exact_mod_cast hroot
  have hfactor :
      (X root.1 : ℝ) * M.mayerTreeMajorant X =
        (‖M.activity root.1‖ /
          (pinnedMayerSymmetryFactor X root.1 : ℝ)) *
        (((graphSpanningTrees (M.mayerIncompatibilityGraph X)).card : ℝ) *
          ∏ v : {v : MayerVertex X // v ≠ root},
            ‖M.activity v.1.1‖) := by
    rw [mayerTreeMajorant,
      mayerSymmetryFactor_eq_mul_pinnedMayerSymmetryFactor X root.1 hroot,
      prod_norm_activity_pow_eq_root_mul_prod_away M X root]
    push_cast
    field_simp
  rw [hfactor]
  exact mul_le_mul_of_nonneg_left
    (card_graphSpanningTrees_mul_prod_away_activity_le_exp_componentTreeSum
      M X root)
    (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))

/-- The sharp Whitney Mayer bound followed by the exact unordered rooted-tree
enumeration, still with the full pinned symmetry normalization. -/
theorem pinned_norm_mayerClusterTerm_le_componentTreeExp
    (M : FinitePolymerModel P) (X : MayerMultiIndex P)
    (root : MayerVertex X) :
    (X root.1 : ℝ) * ‖M.mayerClusterTerm X‖ ≤
      (‖M.activity root.1‖ /
        (pinnedMayerSymmetryFactor X root.1 : ℝ)) *
      Real.exp
        (∑ D ∈ treeComponentDataBelow
            (awayGraph (M.mayerIncompatibilityGraph X) root),
          componentDataRootedTreeWeight
            (rootNeighborFinset (M.mayerIncompatibilityGraph X) root)
            (fun _ => 1) (fun v => ‖M.activity v.1.1‖) D) := by
  exact (M.pinned_norm_mayerClusterTerm_le_tree root.1 X).trans
    (M.pinned_mayerTreeMajorant_le_componentTreeExp X root)

/-- Weight of one possible height-`h` child of a vertex labelled `root`. -/
def kpChildWeight (M : FinitePolymerModel P) (S : Finset P)
    (h : ℕ) (root child : P) : ℝ :=
  if child ∈ S.filter (M.incompatible root) then
    ‖M.activity child‖ * M.kpTreeIterate S h child
  else 0

/-- For one root-deleted component, summing the KP child weight over all
ambiently allowed attachment occurrences is exactly the histogram-weighted
sum.  The multiplicity `mayerChildMultiIndex root c child` is retained here;
it is the factor cancelled by the residual Mayer orbit normalization in the
global forest sum. -/
theorem sum_componentAttachmentChoices_kpChildWeight
    (M : FinitePolymerModel P) (S : Finset P)
    (X : MayerMultiIndex P) (hXS : X.support ⊆ S)
    {T : SimpleGraph (MayerVertex X)} (root : MayerVertex X)
    (c : (awayGraph T root).ConnectedComponent) (h : ℕ) :
    ∑ v ∈ componentAttachmentChoices (awayGraph T root)
          (rootNeighborFinset (M.mayerIncompatibilityGraph X) root) c,
        M.kpChildWeight S h root.1 v.1.1 =
      ∑ child : P,
        (mayerChildMultiIndex root c child : ℝ) *
          M.kpChildWeight S h root.1 child := by
  classical
  rw [sum_componentAttachmentChoices_eq_sum_component]
  · exact (labelHistogram_weighted_sum
      (fun v : ↑c => v.1.1.1)
      (M.kpChildWeight S h root.1)).symm
  · intro v _hvc hvnot
    have hsupport : v.1.1 ∈ X.support :=
      mayerVertex_fst_mem_support v.1
    have hmemS : v.1.1 ∈ S := hXS hsupport
    have hnotAdj : ¬(M.mayerIncompatibilityGraph X).Adj root v.1 := by
      intro hadj
      exact hvnot <| (mem_rootNeighborFinset
        (M.mayerIncompatibilityGraph X) root v).2 hadj
    have hcompatible : ¬M.incompatible root.1 v.1.1 := by
      intro hinc
      exact hnotAdj ⟨Ne.symm v.2, hinc⟩
    simp [kpChildWeight, hmemS, hcompatible]

/-- On a Mayer child attachment, the abstract KP child weight reduces to the
actual activity times the preceding tree iterate.  Thus both the support and
incompatibility tests in `kpChildWeight` are discharged by the rooted tree. -/
theorem kpChildWeight_childRoot_eq
    (M : FinitePolymerModel P) (S : Finset P)
    (X : MayerMultiIndex P) (hXS : X.support ⊆ S)
    {T : SimpleGraph (MayerVertex X)}
    (hT : T.IsTree) (hTG : T ≤ M.mayerIncompatibilityGraph X)
    (root : MayerVertex X)
    (c : (awayGraph T root).ConnectedComponent) (h : ℕ) :
    M.kpChildWeight S h root.1
        (IsTree.childRoot hT root c).1.1 =
      ‖M.activity (IsTree.childRoot hT root c).1.1‖ *
        M.kpTreeIterate S h (IsTree.childRoot hT root c).1.1 := by
  have hsupport : (IsTree.childRoot hT root c).1.1 ∈ X.support :=
    mayerVertex_fst_mem_support (IsTree.childRoot hT root c).1
  have hmem : (IsTree.childRoot hT root c).1.1 ∈ S := hXS hsupport
  have hinc := mayer_incompatible_childRoot M X hT hTG root c
  simp [kpChildWeight, hmem, hinc]

/-- Root deletion followed by the finite attachment-product enumeration gives
the exact multiplicity-aware KP bound for one fixed Mayer spanning tree. -/
theorem prod_childRoot_kpChildWeight_le_histogramForest
    (M : FinitePolymerModel P) (S : Finset P)
    (X : MayerMultiIndex P) (hXS : X.support ⊆ S)
    {T : SimpleGraph (MayerVertex X)}
    (hT : T.IsTree) (hTG : T ≤ M.mayerIncompatibilityGraph X)
    (root : MayerVertex X) (h : ℕ) :
    ∏ c : (awayGraph T root).ConnectedComponent,
        M.kpChildWeight S h root.1
          (IsTree.childRoot hT root c).1.1 ≤
      ∏ c : (awayGraph T root).ConnectedComponent,
        ∑ child : P,
          (mayerChildMultiIndex root c child : ℝ) *
            M.kpChildWeight S h root.1 child := by
  let occurrenceWeight : {v : MayerVertex X // v ≠ root} → ℝ :=
    fun v => M.kpChildWeight S h root.1 v.1.1
  have hnonneg : ∀ v, 0 ≤ occurrenceWeight v := by
    intro v
    simp only [occurrenceWeight, kpChildWeight]
    split_ifs
    · exact mul_nonneg (norm_nonneg _)
        (M.kpTreeIterate_pos S h _).le
    · exact le_rfl
  have hbound :=
    IsTree.prod_childRoot_le_prod_componentAttachmentChoices_sum
      hT hTG root occurrenceWeight hnonneg
  dsimp only [occurrenceWeight] at hbound
  calc
    ∏ c : (awayGraph T root).ConnectedComponent,
        M.kpChildWeight S h root.1
          (IsTree.childRoot hT root c).1.1 ≤
      ∏ c : (awayGraph T root).ConnectedComponent,
        ∑ v ∈ componentAttachmentChoices (awayGraph T root)
          (rootNeighborFinset (M.mayerIncompatibilityGraph X) root) c,
            M.kpChildWeight S h root.1 v.1.1 := hbound
    _ = ∏ c : (awayGraph T root).ConnectedComponent,
        ∑ child : P,
          (mayerChildMultiIndex root c child : ℝ) *
            M.kpChildWeight S h root.1 child := by
      apply Finset.prod_congr rfl
      intro c _hc
      exact sum_componentAttachmentChoices_kpChildWeight
        M S X hXS root c h

/-- On an actual spanning tree the left side of the preceding theorem is the
product of child activity/tree-iterate weights. -/
theorem prod_child_activity_treeIterate_le_histogramForest
    (M : FinitePolymerModel P) (S : Finset P)
    (X : MayerMultiIndex P) (hXS : X.support ⊆ S)
    {T : SimpleGraph (MayerVertex X)}
    (hT : T.IsTree) (hTG : T ≤ M.mayerIncompatibilityGraph X)
    (root : MayerVertex X) (h : ℕ) :
    ∏ c : (awayGraph T root).ConnectedComponent,
        (‖M.activity (IsTree.childRoot hT root c).1.1‖ *
          M.kpTreeIterate S h (IsTree.childRoot hT root c).1.1) ≤
      ∏ c : (awayGraph T root).ConnectedComponent,
        ∑ child : P,
          (mayerChildMultiIndex root c child : ℝ) *
            M.kpChildWeight S h root.1 child := by
  simpa only [kpChildWeight_childRoot_eq M S X hXS hT hTG root] using
    prod_childRoot_kpChildWeight_le_histogramForest
      M S X hXS hT hTG root h

/-- Total mass of all possible height-`h` children. -/
def kpChildMass (M : FinitePolymerModel P) (S : Finset P)
    (h : ℕ) (root : P) : ℝ :=
  ∑ child : P, M.kpChildWeight S h root child

theorem kpChildMass_eq_sum_filter (M : FinitePolymerModel P)
    (S : Finset P) (h : ℕ) (root : P) :
    M.kpChildMass S h root =
      ∑ child ∈ S.filter (M.incompatible root),
        ‖M.activity child‖ * M.kpTreeIterate S h child := by
  classical
  rw [kpChildMass]
  calc
    ∑ child : P, M.kpChildWeight S h root child =
        ∑ child ∈ S.filter (M.incompatible root),
          M.kpChildWeight S h root child := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro child _ hchild
      simp [kpChildWeight, hchild]
    _ = ∑ child ∈ S.filter (M.incompatible root),
        ‖M.activity child‖ * M.kpTreeIterate S h child := by
      apply Finset.sum_congr rfl
      intro child hchild
      simp [kpChildWeight, hchild]

/-- The contribution of a family of exactly `k` children.  The factorial is
the labelled-set symmetry factor. -/
def kpForestLayer (M : FinitePolymerModel P) (S : Finset P)
    (h : ℕ) (root : P) (k : ℕ) : ℝ :=
  (M.kpChildMass S h root) ^ k / k.factorial

theorem kpForestLayer_nonneg (M : FinitePolymerModel P) (S : Finset P)
    (h : ℕ) (root : P) (k : ℕ) :
    0 ≤ M.kpForestLayer S h root k := by
  exact div_nonneg (pow_nonneg (Finset.sum_nonneg fun _ _ => by
    simp only [kpChildWeight]
    split_ifs
    · exact mul_nonneg (norm_nonneg _) (M.kpTreeIterate_pos S h _).le
    · exact le_rfl) _) (Nat.cast_nonneg _)

/-- The factorially normalized child layers sum exactly to the next KP tree
iterate.  This is the analytic labelled-set exponential formula needed by
the rooted-tree proof. -/
theorem hasSum_kpForestLayer (M : FinitePolymerModel P) (S : Finset P)
    (h : ℕ) (root : P) :
    HasSum (M.kpForestLayer S h root) (M.kpTreeIterate S (h + 1) root) := by
  have hexp := NormedSpace.expSeries_div_hasSum_exp
    (M.kpChildMass S h root)
  rw [← Real.exp_eq_exp_ℝ] at hexp
  change HasSum
    (fun k : ℕ => M.kpChildMass S h root ^ k / (k.factorial : ℝ))
    (Real.exp (∑ child ∈ S.filter (M.incompatible root),
      ‖M.activity child‖ * M.kpTreeIterate S h child))
  simpa only [kpChildMass_eq_sum_filter] using hexp

theorem summable_kpForestLayer (M : FinitePolymerModel P)
    (S : Finset P) (h : ℕ) (root : P) :
    Summable (M.kpForestLayer S h root) :=
  (M.hasSum_kpForestLayer S h root).summable

theorem tsum_kpForestLayer (M : FinitePolymerModel P)
    (S : Finset P) (h : ℕ) (root : P) :
    ∑' k : ℕ, M.kpForestLayer S h root k =
      M.kpTreeIterate S (h + 1) root :=
  (M.hasSum_kpForestLayer S h root).tsum_eq

/-- Direct KP control of every complete labelled child-family sum. -/
theorem tsum_kpForestLayer_le_exp_of_koteckyPreiss
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate S a) (h : ℕ)
    (root : P) (hroot : root ∈ S) :
    ∑' k : ℕ, M.kpForestLayer S h root k ≤ Real.exp (a root) := by
  rw [M.tsum_kpForestLayer S h root]
  exact M.kpTreeIterate_le_exp_of_koteckyPreiss S a hKP (h + 1) root hroot

/-- Symmetric-multiset form of the `k`-child layer.  `Finset.sym` consists of
multisets of cardinality `k`, and `countPerms / k!` is their orbit weight. -/
def kpSymmetricForestLayer (M : FinitePolymerModel P) (S : Finset P)
    (h : ℕ) (root : P) (k : ℕ) : ℝ :=
  ∑ m ∈ (Finset.univ : Finset P).sym k,
    ((m.1.countPerms : ℝ) / (k.factorial : ℝ)) *
      (m.1.map (M.kpChildWeight S h root)).prod

/-- The ordered labelled-set power and the symmetric multiset sum agree
degree by degree. -/
theorem kpForestLayer_eq_kpSymmetricForestLayer
    (M : FinitePolymerModel P) (S : Finset P)
    (h : ℕ) (root : P) (k : ℕ) :
    M.kpForestLayer S h root k =
      M.kpSymmetricForestLayer S h root k := by
  classical
  rw [kpForestLayer, kpChildMass, kpSymmetricForestLayer]
  calc
    (∑ child : P, M.kpChildWeight S h root child) ^ k /
        (k.factorial : ℝ) =
      (∑ m ∈ (Finset.univ : Finset P).sym k,
        (m.1.countPerms : ℝ) *
          (m.1.map (M.kpChildWeight S h root)).prod) /
        (k.factorial : ℝ) := by
          congr 1
          simpa using (Finset.sum_pow
            (s := (Finset.univ : Finset P))
            (fun child => M.kpChildWeight S h root child) k)
    _ = ∑ m ∈ (Finset.univ : Finset P).sym k,
        ((m.1.countPerms : ℝ) / (k.factorial : ℝ)) *
          (m.1.map (M.kpChildWeight S h root)).prod := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro m _
      ring

/-- For a multiset, the orbit normalization is exactly the Mayer
multi-index symmetry factor of its counting function. -/
theorem sym_countPerms_div_factorial_eq_inv_mayerSymmetryFactor
    (m : Multiset P) :
    (m.countPerms : ℝ) / (m.card.factorial : ℝ) =
      1 / (mayerSymmetryFactor m.toFinsupp : ℝ) := by
  have hnat := mayerSymmetryFactor_mul_countPerms (P := P) m.toFinsupp
  have hdeg : mayerDegree m.toFinsupp = m.card := by
    rw [← card_toMultiset_eq_mayerDegree]
    simp
  rw [hdeg] at hnat
  have hfac : (m.card.factorial : ℝ) ≠ 0 := by positivity
  have hsym : (mayerSymmetryFactor m.toFinsupp : ℝ) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr
      (fun γ _ => Nat.factorial_ne_zero (m.toFinsupp γ))
  apply (div_eq_div_iff hfac hsym).mpr
  norm_cast
  simpa [mul_comm] using hnat

/-! ## Fixed-labelled pinned tree orbit normalization -/

/-! ### Relabelling a distinguished vertex as `none` -/

/-- Relabelling fixed vertices by an equivalence gives an isomorphic labelled
incompatibility graph. -/
def labelledIncompatibilityGraphIsoEquiv
    (M : FinitePolymerModel P) {V W : Type*}
    (e : V ≃ W) (label : V → P) :
    labelledIncompatibilityGraph M label ≃g
      labelledIncompatibilityGraph M (label ∘ e.symm) where
  toEquiv := e
  map_rel_iff' := by
    intro v w
    simp [labelledIncompatibilityGraph]

/-- Spanning-tree counts are invariant under a fixed-vertex relabelling. -/
theorem card_graphSpanningTrees_labelled_comp_equiv
    (M : FinitePolymerModel P) {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (e : V ≃ W) (label : V → P) :
    (graphSpanningTrees (labelledIncompatibilityGraph M label)).card =
      (graphSpanningTrees
        (labelledIncompatibilityGraph M (label ∘ e.symm))).card :=
  card_graphSpanningTrees_eq_of_iso
    (labelledIncompatibilityGraphIsoEquiv M e label)

/-- Delete a chosen position from a nonempty fixed label tuple. -/
def eraseFinLabel {n : ℕ} (label : Fin (n + 1) → P)
    (j : Fin (n + 1)) : Fin n → P :=
  fun k ↦ label (j.succAbove k)

/-- A label tuple with a distinguished position is equivalently its root
label and the residual tuple on `Fin n`. -/
def labelAtEraseEquiv (n : ℕ) (j : Fin (n + 1)) :
    (Fin (n + 1) → P) ≃ P × (Fin n → P) :=
  ((finSuccEquiv' j).arrowCongr (Equiv.refl P)).trans
    Equiv.piOptionEquivProd

omit [Fintype P] [DecidableEq P] in
@[simp]
theorem labelAtEraseEquiv_fst {n : ℕ} (j : Fin (n + 1))
    (label : Fin (n + 1) → P) :
    (labelAtEraseEquiv (P := P) n j label).1 = label j := by
  simp [labelAtEraseEquiv]

omit [Fintype P] [DecidableEq P] in
@[simp]
theorem labelAtEraseEquiv_snd {n : ℕ} (j : Fin (n + 1))
    (label : Fin (n + 1) → P) :
    (labelAtEraseEquiv (P := P) n j label).2 = eraseFinLabel label j := by
  funext k
  simp [labelAtEraseEquiv, eraseFinLabel]

omit [Fintype P] [DecidableEq P] in
/-- Transporting a label tuple along `finSuccEquiv'` produces exactly the
fixed-root label convention. -/
theorem comp_finSuccEquiv_symm_eq_fixedRootedMayerLabel
    {n : ℕ} (label : Fin (n + 1) → P) (j : Fin (n + 1)) :
    label ∘ (finSuccEquiv' j).symm =
      fixedRootedMayerLabel (label j) (eraseFinLabel label j) := by
  funext o
  cases o with
  | none => simp [fixedRootedMayerLabel]
  | some k => simp [eraseFinLabel, fixedRootedMayerLabel]

/-- After selecting one vertex, the full activity monomial splits into its
root activity and the residual fixed-label monomial. -/
theorem prod_fin_succ_norm_activity_eq_root_mul_erase
    (M : FinitePolymerModel P) {n : ℕ}
    (label : Fin (n + 1) → P) (j : Fin (n + 1)) :
    (∏ i : Fin (n + 1), ‖M.activity (label i)‖) =
      ‖M.activity (label j)‖ *
        ∏ k : Fin n, ‖M.activity (eraseFinLabel label j k)‖ := by
  calc
    (∏ i : Fin (n + 1), ‖M.activity (label i)‖) =
        ∏ o : Option (Fin n),
          ‖M.activity (label ((finSuccEquiv' j).symm o))‖ := by
      exact Fintype.prod_equiv (finSuccEquiv' j)
        (fun i ↦ ‖M.activity (label i)‖)
        (fun o ↦ ‖M.activity (label ((finSuccEquiv' j).symm o))‖)
        (fun i ↦ by simp)
    _ = ‖M.activity (label j)‖ *
        ∏ k : Fin n, ‖M.activity (eraseFinLabel label j k)‖ := by
      rw [Fintype.prod_option]
      simp [eraseFinLabel]

/-- Selecting a vertex and relabelling it as `none` turns the component-tree
count into the already normalized fixed-rooted tree count. -/
theorem card_labelledGraph_eq_fixedRooted_erase
    (M : FinitePolymerModel P) {n : ℕ}
    (label : Fin (n + 1) → P) (j : Fin (n + 1)) :
    (graphSpanningTrees
      (labelledIncompatibilityGraph M label)).card =
    (graphSpanningTrees
      (labelledIncompatibilityGraph M
        (fixedRootedMayerLabel (label j)
          (eraseFinLabel label j)))).card := by
  rw [← comp_finSuccEquiv_symm_eq_fixedRootedMayerLabel label j]
  exact M.card_graphSpanningTrees_labelled_comp_equiv
    (finSuccEquiv' j) label

/-- Polymer labels restricted to one canonical fixed-carrier component after
deleting the distinguished `none` root. -/
def orderedAwayComponentLabel {n : ℕ}
    (label : Fin n → P) (T : SimpleGraph (Option (Fin n)))
    (i : Fin (orderedAwayComponentPartition T).length) :
    Fin ((orderedAwayComponentPartition T).partSize i) → P :=
  fun j ↦ label ((orderedAwayComponentPartition T).emb i j)

/-- A root-deleted component of a spanning incompatibility tree is a
subgraph of the labelled incompatibility graph of its restricted labels. -/
theorem orderedAwayComponentGraph_le_labelledIncompatibilityGraph
    (M : FinitePolymerModel P) (root : P) {n : ℕ}
    (label : Fin n → P) {T : SimpleGraph (Option (Fin n))}
    (hTG : T ≤ labelledIncompatibilityGraph M
      (fixedRootedMayerLabel root label))
    (i : Fin (orderedAwayComponentPartition T).length) :
    orderedAwayComponentGraph T i ≤
      labelledIncompatibilityGraph M
        (orderedAwayComponentLabel label T i) := by
  intro v w hvw
  have hvwT : T.Adj
      (some ((orderedAwayComponentPartition T).emb i v))
      (some ((orderedAwayComponentPartition T).emb i w)) := hvw
  have hinc := hTG hvwT
  exact ⟨hvw.ne, hinc.2⟩

/-- The local fixed-carrier attachment label is incompatible with the parent
label, exactly as required by the KP child sum. -/
theorem incompatible_orderedAwayChildRootLabel
    (M : FinitePolymerModel P) (root : P) {n : ℕ}
    (label : Fin n → P) {T : SimpleGraph (Option (Fin n))}
    (hT : T.IsTree)
    (hTG : T ≤ labelledIncompatibilityGraph M
      (fixedRootedMayerLabel root label))
    (i : Fin (orderedAwayComponentPartition T).length) :
    M.incompatible root
      (orderedAwayComponentLabel label T i
        (orderedAwayChildRootIndex hT i)) := by
  have hinc := hTG (adj_orderedAwayChildRootVertex hT i)
  simpa [orderedAwayComponentLabel,
    orderedAwayComponentPartition_emb_childRootIndex] using hinc.2

/-- Every root-deleted fixed-carrier block is one of the spanning trees
counted by the child label's incompatibility graph. -/
theorem orderedAwayComponentGraph_mem_graphSpanningTrees
    (M : FinitePolymerModel P) (root : P) {n : ℕ}
    (label : Fin n → P) {T : SimpleGraph (Option (Fin n))}
    (hT : T.IsTree)
    (hTG : T ≤ labelledIncompatibilityGraph M
      (fixedRootedMayerLabel root label))
    (i : Fin (orderedAwayComponentPartition T).length) :
    orderedAwayComponentGraph T i ∈
      graphSpanningTrees
        (labelledIncompatibilityGraph M
          (orderedAwayComponentLabel label T i)) := by
  rw [graphSpanningTrees_eq_spanningTreeGraphs,
    mem_spanningTreeGraphs]
  exact ⟨M.orderedAwayComponentGraph_le_labelledIncompatibilityGraph
      root label hTG i,
    orderedAwayComponentGraph_isTree hT i⟩

/-- The residual activity monomial factors exactly over the canonical
root-deleted fixed-carrier blocks. -/
theorem prod_orderedAwayComponentLabel_norm_activity
    (M : FinitePolymerModel P) {n : ℕ}
    (label : Fin n → P) (T : SimpleGraph (Option (Fin n))) :
    (∏ i : Fin (orderedAwayComponentPartition T).length,
      ∏ j : Fin ((orderedAwayComponentPartition T).partSize i),
        ‖M.activity (orderedAwayComponentLabel label T i j)‖) =
      ∏ j : Fin n, ‖M.activity (label j)‖ := by
  exact (orderedAwayComponentPartition T).prod_sigma_eq_prod
    (fun j ↦ ‖M.activity (label j)‖)

/-- Weight of all spanning trees on one labelled residual tuple with an
additional distinguished root. -/
def labelledPinnedTreeWeight
    (M : FinitePolymerModel P) (root : P) {n : ℕ}
    (label : Fin n → P) : ℝ :=
    ((graphSpanningTrees (labelledIncompatibilityGraph M
      (fixedRootedMayerLabel root label))).card : ℝ) *
    ∏ i : Fin n, ‖M.activity (label i)‖

/-- Weight of a nonempty labelled component tree together with the choice of
an attachment vertex whose label is incompatible with the parent root. -/
def labelledAttachedComponentWeight
    (M : FinitePolymerModel P) (root : P) {s : ℕ}
    (label : Fin s → P) : ℝ :=
  ∑ j : Fin s,
    if M.incompatible root (label j) then
      ((graphSpanningTrees
        (labelledIncompatibilityGraph M label)).card : ℝ) *
        ∏ i : Fin s, ‖M.activity (label i)‖
    else 0

/-- Factorially normalized degree-`s` attached-component mass. -/
def factorialNormalizedLabelledAttachedComponentDegreeSum
    (M : FinitePolymerModel P) (root : P) (s : ℕ) : ℝ :=
  (∑ label : Fin s → P,
      M.labelledAttachedComponentWeight root label) /
    (s.factorial : ℝ)

/-- Direct exponential-generating-function sum over every labelling of the
fixed type `Fin n`. -/
def factorialNormalizedLabelledPinnedTreeDegreeSum
    (M : FinitePolymerModel P) (root : P) (n : ℕ) : ℝ :=
  (∑ label : Fin n → P, M.labelledPinnedTreeWeight root label) /
    (n.factorial : ℝ)

/-- Selecting one attachment vertex turns its component tree into the
fixed-rooted tree already used in the symmetric normalization. -/
theorem labelledAttachedComponentWeight_succ
    (M : FinitePolymerModel P) (root : P) {n : ℕ}
    (label : Fin (n + 1) → P) :
    M.labelledAttachedComponentWeight root label =
      ∑ j : Fin (n + 1),
        if M.incompatible root (label j) then
          ‖M.activity (label j)‖ *
            M.labelledPinnedTreeWeight (label j)
              (eraseFinLabel label j)
        else 0 := by
  classical
  unfold labelledAttachedComponentWeight
  apply Finset.sum_congr rfl
  intro j _
  by_cases hinc : M.incompatible root (label j)
  · rw [if_pos hinc, if_pos hinc]
    unfold labelledPinnedTreeWeight
    rw [← M.card_labelledGraph_eq_fixedRooted_erase label j,
      M.prod_fin_succ_norm_activity_eq_root_mul_erase label j]
    ring
  · simp [hinc]

/-- For a fixed distinguished position, summing over every label tuple is
the child-root activity times the preceding labelled rooted-tree degree sum.
The proof is the literal bijection
`(Fin (n+1) → P) ≃ P × (Fin n → P)`. -/
theorem sum_label_fixed_attachment
    (M : FinitePolymerModel P) (root : P) (n : ℕ)
    (j : Fin (n + 1)) :
    (∑ label : Fin (n + 1) → P,
      if M.incompatible root (label j) then
        ‖M.activity (label j)‖ *
          M.labelledPinnedTreeWeight (label j)
            (eraseFinLabel label j)
      else 0) =
    ∑ child ∈ (Finset.univ : Finset P).filter (M.incompatible root),
      ‖M.activity child‖ *
        ∑ residual : Fin n → P,
          M.labelledPinnedTreeWeight child residual := by
  classical
  let e := labelAtEraseEquiv (P := P) n j
  calc
    (∑ label : Fin (n + 1) → P,
        if M.incompatible root (label j) then
          ‖M.activity (label j)‖ *
            M.labelledPinnedTreeWeight (label j)
              (eraseFinLabel label j)
        else 0) =
      ∑ q : P × (Fin n → P),
        if M.incompatible root q.1 then
          ‖M.activity q.1‖ * M.labelledPinnedTreeWeight q.1 q.2
        else 0 := by
          exact Fintype.sum_equiv e _ _ (fun label ↦ by
            simp [e])
    _ = ∑ child : P, ∑ residual : Fin n → P,
        if M.incompatible root child then
          ‖M.activity child‖ *
            M.labelledPinnedTreeWeight child residual
        else 0 := by
          rw [Fintype.sum_prod_type]
    _ = ∑ child ∈ (Finset.univ : Finset P).filter (M.incompatible root),
        ∑ residual : Fin n → P,
          ‖M.activity child‖ *
            M.labelledPinnedTreeWeight child residual := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro child _
      by_cases hinc : M.incompatible root child
      · simp [hinc]
      · simp [hinc]
    _ = ∑ child ∈ (Finset.univ : Finset P).filter (M.incompatible root),
        ‖M.activity child‖ *
          ∑ residual : Fin n → P,
            M.labelledPinnedTreeWeight child residual := by
      apply Finset.sum_congr rfl
      intro child _
      rw [Finset.mul_sum]

/-- Summing all attached component trees of size `n+1` produces the expected
factor `n+1`, one copy for every possible distinguished attachment position. -/
theorem sum_labelledAttachedComponentWeight_succ
    (M : FinitePolymerModel P) (root : P) (n : ℕ) :
    (∑ label : Fin (n + 1) → P,
      M.labelledAttachedComponentWeight root label) =
    (n + 1 : ℝ) *
      ∑ child ∈ (Finset.univ : Finset P).filter (M.incompatible root),
        ‖M.activity child‖ *
          ∑ residual : Fin n → P,
            M.labelledPinnedTreeWeight child residual := by
  classical
  simp_rw [M.labelledAttachedComponentWeight_succ root]
  rw [Finset.sum_comm]
  simp_rw [M.sum_label_fixed_attachment root n]
  simp

/-- Exact normalized attached-component identity.  This is the crucial
`s/s! = 1/(s-1)!` cancellation: one selected attachment occurrence becomes
the child root of the preceding rooted-tree layer. -/
theorem factorialNormalizedLabelledAttachedComponentDegreeSum_succ
    (M : FinitePolymerModel P) (root : P) (n : ℕ) :
    M.factorialNormalizedLabelledAttachedComponentDegreeSum root (n + 1) =
      ∑ child ∈ (Finset.univ : Finset P).filter (M.incompatible root),
        ‖M.activity child‖ *
          M.factorialNormalizedLabelledPinnedTreeDegreeSum child n := by
  classical
  unfold factorialNormalizedLabelledAttachedComponentDegreeSum
    factorialNormalizedLabelledPinnedTreeDegreeSum
  rw [M.sum_labelledAttachedComponentWeight_succ root n,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ hn, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro child _
  ring

/-- The same tree/activity weight expressed only through the residual label
histogram. -/
def residualTreeHistogramWeight
    (M : FinitePolymerModel P) (root : P)
    (X : MayerMultiIndex P) : ℝ :=
  ((graphSpanningTrees (M.mayerIncompatibilityGraph
      (X + Finsupp.single root 1))).card : ℝ) *
    ∏ child : P, ‖M.activity child‖ ^ X child

/-- The labelled rooted-tree weight is genuinely symmetric: it depends only
on the tuple histogram. -/
theorem labelledPinnedTreeWeight_eq_residualTreeHistogramWeight
    (M : FinitePolymerModel P) (root : P) {n : ℕ}
    (label : Fin n → P) :
    M.labelledPinnedTreeWeight root label =
      M.residualTreeHistogramWeight root (labelHistogram label) := by
  unfold labelledPinnedTreeWeight residualTreeHistogramWeight
  rw [card_labelledIncompatibilityGraph_eq_mayer,
    labelHistogram_fixedRootedMayerLabel]
  congr 1
  rw [← histogramWeight_eq_prod, histogramWeight_labelHistogram]

/-- The factorial-normalized fixed-labelled rooted-tree orbit sum.  Each
residual multi-index is represented on `Fin n`; the distinguished root is
the `none` vertex of `Option (Fin n)`. -/
def fixedLabelledPinnedTreeOrbitDegreeSum
    (M : FinitePolymerModel P) (root : P) (n : ℕ) : ℝ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
    if hX : mayerDegree X = n then
      ((X.toMultiset.countPerms : ℝ) / (n.factorial : ℝ)) *
        (((graphSpanningTrees (labelledIncompatibilityGraph M
          (fixedRootedMayerLabel root
            (fixedMayerLabel n X hX)))).card : ℝ) *
          ∏ i : Fin n, ‖M.activity (fixedMayerLabel n X hX i)‖)
    else 0

/-- The fixed-representative orbit sum is exactly the sum over all labelled
tuples divided by `n!`; the multinomial fiber cardinality is now proved, not
assumed. -/
theorem factorialNormalizedLabelledPinnedTreeDegreeSum_eq_fixedOrbit
    (M : FinitePolymerModel P) (root : P) (n : ℕ) :
    M.factorialNormalizedLabelledPinnedTreeDegreeSum root n =
      M.fixedLabelledPinnedTreeOrbitDegreeSum root n := by
  classical
  unfold factorialNormalizedLabelledPinnedTreeDegreeSum
  simp_rw [labelledPinnedTreeWeight_eq_residualTreeHistogramWeight]
  rw [sum_labelings_weight_eq_sum_countPerms_histogramWeight]
  unfold fixedLabelledPinnedTreeOrbitDegreeSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro X hXouter
  have hdegree : mayerDegree X = n :=
    (mem_mayerMultiIndicesOfDegree n X).mp hXouter
  rw [dif_pos hdegree]
  unfold residualTreeHistogramWeight
  rw [card_fixedRootedMayerGraph M root n X hdegree,
    prod_fixedMayerLabel_norm_activity M n X hdegree]
  ring

/-- The same pinned tree orbit sum in the residual symmetric multi-index
presentation. -/
def residualSymmetricPinnedTreeDegreeSum
    (M : FinitePolymerModel P) (root : P) (n : ℕ) : ℝ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
    (((graphSpanningTrees (M.mayerIncompatibilityGraph
      (X + Finsupp.single root 1))).card : ℝ) *
      ∏ child : P, ‖M.activity child‖ ^ X child) /
        (mayerSymmetryFactor X : ℝ)

/-- Exact fixed-labelled orbit identity.  This is the global
`countPerms / n!` normalization with the graph and activity weights retained,
not merely a cardinality calculation. -/
theorem fixedLabelledPinnedTreeOrbitDegreeSum_eq_residual
    (M : FinitePolymerModel P) (root : P) (n : ℕ) :
    M.fixedLabelledPinnedTreeOrbitDegreeSum root n =
      M.residualSymmetricPinnedTreeDegreeSum root n := by
  classical
  unfold fixedLabelledPinnedTreeOrbitDegreeSum
    residualSymmetricPinnedTreeDegreeSum
  apply Finset.sum_congr rfl
  intro X hXouter
  have hdegree : mayerDegree X = n :=
    (mem_mayerMultiIndicesOfDegree n X).mp hXouter
  rw [dif_pos hdegree]
  have hcard : X.toMultiset.card = n := by
    rw [card_toMultiset_eq_mayerDegree, hdegree]
  rw [card_fixedRootedMayerGraph M root n X hdegree,
    prod_fixedMayerLabel_norm_activity M n X hdegree]
  rw [← hcard, sym_countPerms_div_factorial_eq_inv_mayerSymmetryFactor]
  simp only [Finsupp.toMultiset_toFinsupp]
  ring

/-- Final degreewise labelled-set normalization: summing all rooted labelled
trees on `Option (Fin n)` and dividing by `n!` is exactly the residual
symmetric Mayer tree layer. -/
theorem factorialNormalizedLabelledPinnedTreeDegreeSum_eq_residual
    (M : FinitePolymerModel P) (root : P) (n : ℕ) :
    M.factorialNormalizedLabelledPinnedTreeDegreeSum root n =
      M.residualSymmetricPinnedTreeDegreeSum root n :=
  (M.factorialNormalizedLabelledPinnedTreeDegreeSum_eq_fixedOrbit root n).trans
    (M.fixedLabelledPinnedTreeOrbitDegreeSum_eq_residual root n)

omit [Fintype P] [DecidableEq P] in
/-- Deleting the distinguished occurrence from a root-augmented residual
multi-index recovers that residual multi-index exactly. -/
theorem eraseRootOccurrence_add_single
    (X : MayerMultiIndex P) (root : P) :
    eraseRootOccurrence (X + Finsupp.single root 1) root = X := by
  classical
  ext child
  rw [eraseRootOccurrence, Finsupp.update_apply]
  by_cases hchild : child = root
  · subst child
    simp
  · simp [hchild]

/-- The pinned symmetry factor of a root-augmented multi-index is the
ordinary symmetry factor of the residual orbit. -/
theorem pinnedMayerSymmetryFactor_add_single
    (X : MayerMultiIndex P) (root : P) :
    pinnedMayerSymmetryFactor (X + Finsupp.single root 1) root =
      mayerSymmetryFactor X := by
  rw [← mayerSymmetryFactor_eraseRootOccurrence_eq_pinnedMayerSymmetryFactor,
    eraseRootOccurrence_add_single]

/-- Adding one root factors the norm-activity monomial into the root activity
and the residual monomial. -/
theorem prod_norm_activity_add_single
    (M : FinitePolymerModel P) (X : MayerMultiIndex P) (root : P) :
    (∏ child : P, ‖M.activity child‖ ^
        ((X + Finsupp.single root 1 : MayerMultiIndex P) child)) =
      ‖M.activity root‖ *
        ∏ child : P, ‖M.activity child‖ ^ X child := by
  rw [← histogramWeight_eq_prod, histogramWeight_add,
    histogramWeight_eq_prod]
  simp [histogramWeight, mul_comm]

/-- A residual symmetric rooted-tree term is exactly the multiplicity-pinned
Mayer tree majorant after adjoining its distinguished root occurrence. -/
theorem root_mul_residualTreeTerm_eq_pinned_mayerTreeMajorant
    (M : FinitePolymerModel P) (X : MayerMultiIndex P) (root : P) :
    ‖M.activity root‖ *
        ((((graphSpanningTrees (M.mayerIncompatibilityGraph
          (X + Finsupp.single root 1))).card : ℝ) *
          ∏ child : P, ‖M.activity child‖ ^ X child) /
            (mayerSymmetryFactor X : ℝ)) =
      (((X + Finsupp.single root 1 : MayerMultiIndex P) root : ℕ) : ℝ) *
        M.mayerTreeMajorant (X + Finsupp.single root 1) := by
  have hroot : ((X + Finsupp.single root 1 : MayerMultiIndex P) root) ≠ 0 := by
    simp
  have hpinned : (pinnedMayerSymmetryFactor
      (X + Finsupp.single root 1) root : ℝ) ≠ 0 := by
    rw [pinnedMayerSymmetryFactor_add_single]
    exact_mod_cast Finset.prod_ne_zero_iff.mpr
      (fun child _ => Nat.factorial_ne_zero (X child))
  rw [mayerTreeMajorant,
    mayerSymmetryFactor_eq_mul_pinnedMayerSymmetryFactor
      (X + Finsupp.single root 1) root hroot,
    pinnedMayerSymmetryFactor_add_single,
    prod_norm_activity_add_single]
  push_cast
  field_simp

/-- Adding one occurrence raises the total Mayer degree by one. -/
theorem mayerDegree_add_single
    (X : MayerMultiIndex P) (root : P) :
    mayerDegree (X + Finsupp.single root 1) = mayerDegree X + 1 := by
  classical
  unfold mayerDegree
  simp_rw [Finsupp.add_apply]
  rw [Finset.sum_add_distrib]
  simp

omit [Fintype P] in
/-- Adding back a deleted root occurrence recovers any multi-index in which
that root occurs. -/
theorem eraseRootOccurrence_add_single_eq
    (X : MayerMultiIndex P) (root : P) (hroot : X root ≠ 0) :
    eraseRootOccurrence X root + Finsupp.single root 1 = X := by
  classical
  ext child
  by_cases hchild : child = root
  · subst child
    simp [eraseRootOccurrence]
    omega
  · simp [eraseRootOccurrence, hchild]

/-- Deleting an occurring root from degree `n+1` leaves degree `n`. -/
theorem mayerDegree_eraseRootOccurrence
    (X : MayerMultiIndex P) (root : P) (n : ℕ)
    (hdegree : mayerDegree X = n + 1) (hroot : X root ≠ 0) :
    mayerDegree (eraseRootOccurrence X root) = n := by
  have hadd := mayerDegree_add_single (eraseRootOccurrence X root) root
  rw [eraseRootOccurrence_add_single_eq X root hroot, hdegree] at hadd
  omega

/-- Absolute spanning-tree majorants of one fixed total degree, with a root
occurrence distinguished by its multiplicity. -/
def pinnedMayerTreeDegreeSum
    (M : FinitePolymerModel P) (root : P) (n : ℕ) : ℝ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := P) n,
    (X root : ℝ) * M.mayerTreeMajorant X

/-- Exact residual reindexing of the pinned Mayer tree degree sum.  The
degree-`n` fixed-labelled orbit is precisely the degree-`n+1` pinned tree
majorant after the distinguished root activity is restored. -/
theorem pinnedMayerTreeDegreeSum_succ_eq_residual
    (M : FinitePolymerModel P) (root : P) (n : ℕ) :
    M.pinnedMayerTreeDegreeSum root (n + 1) =
      ‖M.activity root‖ * M.residualSymmetricPinnedTreeDegreeSum root n := by
  classical
  let source := mayerMultiIndicesOfDegree (P := P) n
  let target := (mayerMultiIndicesOfDegree (P := P) (n + 1)).filter
    (fun X => X root ≠ 0)
  have hreindex :
      (∑ Y ∈ source,
        (((Y + Finsupp.single root 1 : MayerMultiIndex P) root : ℕ) : ℝ) *
          M.mayerTreeMajorant (Y + Finsupp.single root 1)) =
      ∑ X ∈ target, (X root : ℝ) * M.mayerTreeMajorant X := by
    apply Finset.sum_bij
        (fun Y (_hY : Y ∈ source) => Y + Finsupp.single root 1)
    · intro Y hY
      apply Finset.mem_filter.mpr
      refine ⟨(mem_mayerMultiIndicesOfDegree (n + 1) _).mpr ?_, ?_⟩
      · rw [mayerDegree_add_single]
        exact congrArg (fun k => k + 1)
          ((mem_mayerMultiIndicesOfDegree n Y).mp hY)
      · simp
    · intro Y₁ _ Y₂ _ h
      exact add_right_cancel h
    · intro X hX
      have hdata := Finset.mem_filter.mp hX
      have hdegree := (mem_mayerMultiIndicesOfDegree (n + 1) X).mp hdata.1
      let Y := eraseRootOccurrence X root
      refine ⟨Y, (mem_mayerMultiIndicesOfDegree n Y).mpr
        (mayerDegree_eraseRootOccurrence X root n hdegree hdata.2), ?_⟩
      exact eraseRootOccurrence_add_single_eq X root hdata.2
    · intro Y _
      rfl
  unfold pinnedMayerTreeDegreeSum
  calc
    (∑ X ∈ mayerMultiIndicesOfDegree (P := P) (n + 1),
        (X root : ℝ) * M.mayerTreeMajorant X) =
      ∑ X ∈ target, (X root : ℝ) * M.mayerTreeMajorant X := by
        dsimp [target]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro X _
        by_cases hroot : X root ≠ 0
        · simp [hroot]
        · have hzero : X root = 0 := not_ne_iff.mp hroot
          simp [hzero]
    _ = ∑ Y ∈ source,
        (((Y + Finsupp.single root 1 : MayerMultiIndex P) root : ℕ) : ℝ) *
          M.mayerTreeMajorant (Y + Finsupp.single root 1) := hreindex.symm
    _ = ∑ Y ∈ source,
        ‖M.activity root‖ *
          ((((graphSpanningTrees (M.mayerIncompatibilityGraph
            (Y + Finsupp.single root 1))).card : ℝ) *
            ∏ child : P, ‖M.activity child‖ ^ Y child) /
              (mayerSymmetryFactor Y : ℝ)) := by
        apply Finset.sum_congr rfl
        intro Y _
        exact (root_mul_residualTreeTerm_eq_pinned_mayerTreeMajorant
          M Y root).symm
    _ = ‖M.activity root‖ * M.residualSymmetricPinnedTreeDegreeSum root n := by
      rw [residualSymmetricPinnedTreeDegreeSum, Finset.mul_sum]

/-- Partial residual rooted-tree orbit sum through degrees `< N`. -/
def residualPinnedTreePartialSum
    (M : FinitePolymerModel P) (root : P) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, M.residualSymmetricPinnedTreeDegreeSum root n

/-- The same partial sum in its literal labelled-set presentation. -/
def labelledPinnedTreePartialSum
    (M : FinitePolymerModel P) (root : P) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    M.factorialNormalizedLabelledPinnedTreeDegreeSum root n

theorem labelledPinnedTreePartialSum_eq_residual
    (M : FinitePolymerModel P) (root : P) (N : ℕ) :
    M.labelledPinnedTreePartialSum root N =
      M.residualPinnedTreePartialSum root N := by
  unfold labelledPinnedTreePartialSum residualPinnedTreePartialSum
  apply Finset.sum_congr rfl
  intro n _
  exact M.factorialNormalizedLabelledPinnedTreeDegreeSum_eq_residual root n

/-- Fixed-labelled statement of the root-deletion recurrence.  This is the
preferred formulation for the remaining combinatorics: every degree uses the
literal carrier `Fin n`, so no dependent Mayer occurrence type is transported
across the summation. -/
def LabelledRootedTreeRecurrence (M : FinitePolymerModel P) : Prop :=
  ∀ (root : P) (N : ℕ),
    M.labelledPinnedTreePartialSum root (N + 1) ≤
      Real.exp
        (∑ child ∈ (Finset.univ : Finset P).filter (M.incompatible root),
          ‖M.activity child‖ * M.labelledPinnedTreePartialSum child N)

/-- The exact cross-degree unordered-family recurrence left by root deletion.
This is now the sole unproved combinatorial bridge: once child components are
regrouped as symmetric fixed-labelled orbits, their family sum is the
displayed exponential. -/
def RootedTreeOrbitRecurrence (M : FinitePolymerModel P) : Prop :=
  ∀ (root : P) (N : ℕ),
    M.residualPinnedTreePartialSum root (N + 1) ≤
      Real.exp
        (∑ child ∈ (Finset.univ : Finset P).filter (M.incompatible root),
          ‖M.activity child‖ * M.residualPinnedTreePartialSum child N)

/-- The literal fixed-labelled recurrence and the residual symmetric-orbit
recurrence are exactly equivalent.  Thus proving the former closes the
remaining KP bridge without any additional normalization theorem. -/
theorem labelledRootedTreeRecurrence_iff_orbitRecurrence
    (M : FinitePolymerModel P) :
    M.LabelledRootedTreeRecurrence ↔ M.RootedTreeOrbitRecurrence := by
  constructor
  · intro h root N
    simpa only [M.labelledPinnedTreePartialSum_eq_residual] using h root N
  · intro h root N
    simpa only [M.labelledPinnedTreePartialSum_eq_residual] using h root N

/-- Every partial residual rooted-tree orbit sum is dominated by the
corresponding height-truncated KP iterate. -/
def RootedTreeOrbitBound (M : FinitePolymerModel P) : Prop :=
  ∀ (root : P) (N : ℕ),
    M.residualPinnedTreePartialSum root N ≤
      M.kpTreeIterate Finset.univ N root

/-- The cross-degree species recurrence closes by induction to the ordinary
height-truncated KP iteration. -/
theorem rootedTreeOrbitBound_of_recurrence
    (M : FinitePolymerModel P) (hrec : M.RootedTreeOrbitRecurrence) :
    M.RootedTreeOrbitBound := by
  intro root N
  induction N generalizing root with
  | zero =>
      simp [residualPinnedTreePartialSum]
  | succ N ih =>
      calc
        M.residualPinnedTreePartialSum root (N + 1) ≤
            Real.exp
              (∑ child ∈ (Finset.univ : Finset P).filter
                  (M.incompatible root),
                ‖M.activity child‖ *
                  M.residualPinnedTreePartialSum child N) := hrec root N
        _ ≤ Real.exp
              (∑ child ∈ (Finset.univ : Finset P).filter
                  (M.incompatible root),
                ‖M.activity child‖ * M.kpTreeIterate Finset.univ N child) := by
          apply Real.exp_le_exp.mpr
          apply Finset.sum_le_sum
          intro child _
          exact mul_le_mul_of_nonneg_left (ih child) (norm_nonneg _)
        _ = M.kpTreeIterate Finset.univ (N + 1) root := by
          rw [kpTreeIterate_succ]

theorem residualSymmetricPinnedTreeDegreeSum_nonneg
    (M : FinitePolymerModel P) (root : P) (n : ℕ) :
    0 ≤ M.residualSymmetricPinnedTreeDegreeSum root n := by
  classical
  unfold residualSymmetricPinnedTreeDegreeSum
  exact Finset.sum_nonneg fun X _ =>
    div_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (Finset.prod_nonneg fun child _ => pow_nonneg (norm_nonneg _) _))
      (Nat.cast_nonneg _)

/-- Once the finite rooted-tree species recurrence is available, the explicit
standard KP certificate gives genuine absolute summability of the residual
rooted-tree orbit series. -/
theorem summable_residualSymmetricPinnedTreeDegreeSum_of_koteckyPreiss
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hOrbit : M.RootedTreeOrbitBound)
    (hKP : M.KoteckyPreissCertificate Finset.univ a)
    (root : P) :
    Summable (M.residualSymmetricPinnedTreeDegreeSum root) := by
  apply summable_of_sum_range_le (c := Real.exp (a root))
  · exact M.residualSymmetricPinnedTreeDegreeSum_nonneg root
  · intro N
    exact (hOrbit root N).trans
      (M.kpTreeIterate_le_exp_of_koteckyPreiss Finset.univ a hKP N root
        (Finset.mem_univ root))

theorem tsum_residualSymmetricPinnedTreeDegreeSum_le_of_koteckyPreiss
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hOrbit : M.RootedTreeOrbitBound)
    (hKP : M.KoteckyPreissCertificate Finset.univ a)
    (root : P) :
    ∑' n : ℕ, M.residualSymmetricPinnedTreeDegreeSum root n ≤
      Real.exp (a root) := by
  apply Real.tsum_le_of_sum_range_le
    (M.residualSymmetricPinnedTreeDegreeSum_nonneg root)
  intro N
  exact (hOrbit root N).trans
    (M.kpTreeIterate_le_exp_of_koteckyPreiss Finset.univ a hKP N root
      (Finset.mem_univ root))

/-- Quantitative total mass of the positive-degree pinned tree series. -/
theorem tsum_pinnedMayerTreeDegreeSum_succ_le_of_koteckyPreiss
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hOrbit : M.RootedTreeOrbitBound)
    (hKP : M.KoteckyPreissCertificate Finset.univ a)
    (root : P) :
    ∑' n : ℕ, M.pinnedMayerTreeDegreeSum root (n + 1) ≤
      ‖M.activity root‖ * Real.exp (a root) := by
  simp_rw [M.pinnedMayerTreeDegreeSum_succ_eq_residual root]
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left
    (M.tsum_residualSymmetricPinnedTreeDegreeSum_le_of_koteckyPreiss
      a hOrbit hKP root)
    (norm_nonneg _)

/-- The standard KP certificate also sums the positive-degree pinned tree
majorant itself.  This is the positive majorant used when extracting more
than one labelled source coefficient. -/
theorem summable_pinnedMayerTreeDegreeSum_succ_of_koteckyPreiss
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hOrbit : M.RootedTreeOrbitBound)
    (hKP : M.KoteckyPreissCertificate Finset.univ a)
    (root : P) :
    Summable (fun n : ℕ => M.pinnedMayerTreeDegreeSum root (n + 1)) := by
  have hres :=
    M.summable_residualSymmetricPinnedTreeDegreeSum_of_koteckyPreiss
      a hOrbit hKP root
  have hmul : Summable (fun n : ℕ =>
      ‖M.activity root‖ * M.residualSymmetricPinnedTreeDegreeSum root n) :=
    hres.mul_left ‖M.activity root‖
  apply hmul.congr
  intro n
  exact (M.pinnedMayerTreeDegreeSum_succ_eq_residual root n).symm

/-- The orbit recurrence plus the sharp Whitney bound gives summability of
the actual multiplicity-pinned Mayer norm series. -/
theorem summable_pinnedNormMayerDegreeSum_succ_of_koteckyPreiss
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hOrbit : M.RootedTreeOrbitBound)
    (hKP : M.KoteckyPreissCertificate Finset.univ a)
    (root : P) :
    Summable (fun n : ℕ => M.pinnedNormMayerDegreeSum root (n + 1)) := by
  have htree :=
    M.summable_pinnedMayerTreeDegreeSum_succ_of_koteckyPreiss
      a hOrbit hKP root
  apply Summable.of_nonneg_of_le
    (fun n => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    (fun n => ?_) htree
  unfold pinnedMayerTreeDegreeSum
  apply Finset.sum_le_sum
  intro X _
  exact M.pinned_norm_mayerClusterTerm_le_tree root X

/-- Genuine KP/tree absolute summability of the full positive-degree Mayer
series, reduced only to the finite rooted-tree orbit recurrence. -/
theorem summable_normMayerDegreeSum_succ_of_koteckyPreiss
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hOrbit : M.RootedTreeOrbitBound)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    Summable (fun n : ℕ => M.normMayerDegreeSum (n + 1)) := by
  apply M.summable_normMayerDegreeSum_succ_of_pinned
  intro root
  exact M.summable_pinnedNormMayerDegreeSum_succ_of_koteckyPreiss
    a hOrbit hKP root

/-- End-to-end genuine KP/tree summability from the single finite-species
recurrence. -/
theorem summable_normMayerDegreeSum_succ_of_koteckyPreiss_recurrence
    (M : FinitePolymerModel P) (a : P → ℝ)
    (hrec : M.RootedTreeOrbitRecurrence)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    Summable (fun n : ℕ => M.normMayerDegreeSum (n + 1)) :=
  M.summable_normMayerDegreeSum_succ_of_koteckyPreiss a
    (M.rootedTreeOrbitBound_of_recurrence hrec) hKP

/-- A multiset product is the corresponding finite-type product of powers of
its counting multi-index. -/
theorem multiset_map_prod_eq_prod_toFinsupp
    (m : Multiset P) (w : P → ℝ) :
    (m.map w).prod = ∏ child : P, w child ^ m.toFinsupp child := by
  classical
  rw [Finset.prod_multiset_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro child _ hchild
  have hzero : m.count child = 0 := by
    exact Multiset.count_eq_zero.mpr (by simpa using hchild)
  simp [hzero]

/-- The child-family layer in the exact symmetric Mayer convention: one
factorial for every repeated child label. -/
theorem kpSymmetricForestLayer_eq_sum_inv_mayerSymmetryFactor
    (M : FinitePolymerModel P) (S : Finset P)
    (h : ℕ) (root : P) (k : ℕ) :
    M.kpSymmetricForestLayer S h root k =
      ∑ m ∈ (Finset.univ : Finset P).sym k,
        (m.1.map (M.kpChildWeight S h root)).prod /
          (mayerSymmetryFactor m.1.toFinsupp : ℝ) := by
  classical
  apply Finset.sum_congr rfl
  intro m hm
  have hfactorial : (k.factorial : ℝ) = (m.1.card.factorial : ℝ) := by
    rw [m.2]
  rw [hfactorial, sym_countPerms_div_factorial_eq_inv_mayerSymmetryFactor]
  ring

/-- The symmetric multiset layer is literally the Mayer multi-index layer of
the same total degree.  This is the global tuple-histogram normalization
needed when child subtrees are regrouped by repeated polymer labels. -/
theorem kpSymmetricForestLayer_eq_mayerMultiIndexSum
    (M : FinitePolymerModel P) (S : Finset P)
    (h : ℕ) (root : P) (k : ℕ) :
    M.kpSymmetricForestLayer S h root k =
      ∑ X ∈ mayerMultiIndicesOfDegree (P := P) k,
        (∏ child : P, M.kpChildWeight S h root child ^ X child) /
          (mayerSymmetryFactor X : ℝ) := by
  classical
  rw [kpSymmetricForestLayer_eq_sum_inv_mayerSymmetryFactor,
    Finset.sym_univ]
  apply Finset.sum_bij (fun m _ => m.1.toFinsupp)
  · intro m _
    apply (mem_mayerMultiIndicesOfDegree k m.1.toFinsupp).mpr
    rw [← card_toMultiset_eq_mayerDegree]
    simp only [Multiset.toFinsupp_toMultiset]
    exact m.2
  · intro m₁ _ m₂ _ heq
    apply Subtype.ext
    exact Multiset.toFinsupp.injective heq
  · intro X hX
    have hdegree := (mem_mayerMultiIndicesOfDegree k X).mp hX
    let m : Sym P k := ⟨X.toMultiset, by
      rw [card_toMultiset_eq_mayerDegree, hdegree]⟩
    refine ⟨m, Finset.mem_univ _, ?_⟩
    exact Finsupp.toMultiset_toFinsupp X
  · intro m _
    rw [multiset_map_prod_eq_prod_toFinsupp]

theorem kpForestLayer_eq_mayerMultiIndexSum
    (M : FinitePolymerModel P) (S : Finset P)
    (h : ℕ) (root : P) (k : ℕ) :
    M.kpForestLayer S h root k =
      ∑ X ∈ mayerMultiIndicesOfDegree (P := P) k,
        (∏ child : P, M.kpChildWeight S h root child ^ X child) /
          (mayerSymmetryFactor X : ℝ) := by
  rw [M.kpForestLayer_eq_kpSymmetricForestLayer S h root k,
    M.kpSymmetricForestLayer_eq_mayerMultiIndexSum S h root k]

/-- Degree-`k` symmetric Mayer sum for an unordered family of height-`h`
child subtrees. -/
def kpMayerForestDegreeSum (M : FinitePolymerModel P) (S : Finset P)
    (h : ℕ) (root : P) (k : ℕ) : ℝ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := P) k,
    (∏ child : P, M.kpChildWeight S h root child ^ X child) /
      (mayerSymmetryFactor X : ℝ)

theorem kpMayerForestDegreeSum_eq_kpForestLayer
    (M : FinitePolymerModel P) (S : Finset P)
    (h : ℕ) (root : P) (k : ℕ) :
    M.kpMayerForestDegreeSum S h root k =
      M.kpForestLayer S h root k := by
  exact (M.kpForestLayer_eq_mayerMultiIndexSum S h root k).symm

/-- Exact summability of the symmetric multi-index child-forest expansion. -/
theorem hasSum_kpMayerForestDegreeSum
    (M : FinitePolymerModel P) (S : Finset P)
    (h : ℕ) (root : P) :
    HasSum (M.kpMayerForestDegreeSum S h root)
      (M.kpTreeIterate S (h + 1) root) := by
  have heq : M.kpMayerForestDegreeSum S h root =
      M.kpForestLayer S h root := by
    funext k
    exact M.kpMayerForestDegreeSum_eq_kpForestLayer S h root k
  rw [heq]
  exact M.hasSum_kpForestLayer S h root

theorem summable_kpMayerForestDegreeSum
    (M : FinitePolymerModel P) (S : Finset P)
    (h : ℕ) (root : P) :
    Summable (M.kpMayerForestDegreeSum S h root) :=
  (M.hasSum_kpMayerForestDegreeSum S h root).summable

theorem tsum_kpMayerForestDegreeSum_le_exp_of_koteckyPreiss
    (M : FinitePolymerModel P) (S : Finset P) (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate S a) (h : ℕ)
    (root : P) (hroot : root ∈ S) :
    ∑' k : ℕ, M.kpMayerForestDegreeSum S h root k ≤
      Real.exp (a root) := by
  rw [(M.hasSum_kpMayerForestDegreeSum S h root).tsum_eq]
  exact M.kpTreeIterate_le_exp_of_koteckyPreiss
    S a hKP (h + 1) root hroot

end FinitePolymerModel

end

end YangMills.Polymer
