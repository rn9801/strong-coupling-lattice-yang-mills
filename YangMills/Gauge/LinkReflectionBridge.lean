/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.LinkReflectionPositivity
import YangMills.Gauge.SiteReflectionBridge

/-!
# Concrete finite-specification bridge for link reflection

This file identifies a finite specification symmetric through the
half-integer plane `x τ = k + 1/2` with the crossing-link/two-side normal form
used by the Taylor--Fubini proof of link-reflection positivity.  The extra
`PlaquetteClosed` condition says that every stored edge read by the action is
dynamic.  It is satisfied by the free-region specifications used in the
strong-coupling limit and is precisely what makes crossing-link gauge fixing
compatible with the finite boundary.
-/

open MeasureTheory

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

local instance linkReflectionBridgeDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

namespace FiniteSpecification

variable {d : ℕ} {G : Type*} [Group G]

/-- Local four-edge boundary formula, kept here to avoid a dependency from
the gauge layer on the strong-coupling counting modules. -/
private theorem linkBridge_plaquette_boundary_edgeSupport (p : Plaquette d) :
    p.boundary.edgeSupport =
      { ⟨p.base, p.first⟩,
        ⟨step p.base (.forward p.first), p.second⟩,
        ⟨step p.base (.forward p.second), p.first⟩,
        ⟨p.base, p.second⟩ } := by
  have h₃ : p.base + unitVector p.first + unitVector p.second +
      -unitVector p.first = p.base + unitVector p.second := by abel
  simp only [Plaquette.boundary, Path.rectangleBoundary,
    SignedDirection.forward, Path.advance, step, SignedDirection.delta,
    SignedDirection.backward, Path.rectangleRaw, Path.straight, Nat.reduceAdd,
    edgeFrom, SignedEdge.toArrow, SignedEdge.target, h₃,
    Quiver.Path.comp_cons, Quiver.Path.comp_nil, Path.edgeSupport_castTarget,
    Path.edgeSupport_cons, SignedEdge.positive, add_neg_cancel_right,
    Path.edgeSupport_nil, insert_empty_eq]
  apply Finset.ext
  intro e
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem linkBridge_plaquette_boundary_edgeSupport_translate
    (v : Site d) (p : Plaquette d) :
    (p.translate v).boundary.edgeSupport =
      p.boundary.edgeSupport.map
        (PositiveEdge.translationEquiv v).toEmbedding := by
  rw [linkBridge_plaquette_boundary_edgeSupport,
    linkBridge_plaquette_boundary_edgeSupport]
  simp [PositiveEdge.translationEquiv, PositiveEdge.translate,
    Plaquette.translate, translate_step]

/-- Dynamic links crossing the half-integer reflection plane. -/
def linkCrossingEdges (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ) :
    Finset (PositiveEdge d) :=
  Λ.dynamicEdges.filter fun e => e.direction = τ ∧ e.source τ = k

/-- Dynamic links strictly in the positive half-lattice. -/
def linkPositiveEdges (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ) :
    Finset (PositiveEdge d) :=
  Λ.dynamicEdges.filter fun e => k < e.source τ

/-- Active plaquettes strictly in the positive half-lattice. -/
def linkPositivePlaquettes (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ) :
    Finset (Plaquette d) :=
  Λ.activePlaquettes.filter fun p => k < p.base τ

/-- Active plaquettes cut by the half-integer plane. -/
def linkCrossPlaquettes (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ) :
    Finset (Plaquette d) :=
  Λ.activePlaquettes.filter fun p =>
    p.base τ = k ∧ (p.first = τ ∨ p.second = τ)

/-- The reflected copy of the strict positive plaquettes. -/
def linkNegativePlaquettes (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ) :
    Finset (Plaquette d) :=
  (Λ.linkPositivePlaquettes τ k).map
    (Plaquette.linkReflectionEquiv τ k).toEmbedding

/-- Reflection symmetry of a concrete finite specification. -/
def LinkSymmetric (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ) : Prop :=
  (∀ e, e ∈ Λ.dynamicEdges ↔ e.linkReflect τ k ∈ Λ.dynamicEdges) ∧
    (∀ p, p ∈ Λ.activePlaquettes ↔ p.linkReflect τ k ∈ Λ.activePlaquettes) ∧
    linkReflectConfiguration τ k Λ.exterior = Λ.exterior

/-- No active plaquette reads a frozen exterior link. -/
def PlaquetteClosed (Λ : FiniteSpecification d G) : Prop :=
  ∀ p ∈ Λ.activePlaquettes, p.boundary.edgeSupport ⊆ Λ.dynamicEdges

omit [Group G] in
theorem source_linkReflect_eq_of_direction_ne (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) (h : e.direction ≠ τ) :
    (e.linkReflect τ k).source = linkReflection τ k e.source := by
  simp [PositiveEdge.linkReflect, h]

omit [Group G] in
theorem source_linkReflect_eq_of_direction_eq (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) (h : e.direction = τ) :
    (e.linkReflect τ k).source τ = 2 * k - e.source τ := by
  subst τ
  simp only [PositiveEdge.linkReflect, if_pos, linkReflection_apply_eq]
  have ht : e.target e.direction = e.source e.direction + 1 := by
    change e.source e.direction + unitVector e.direction e.direction = _
    simp [unitVector]
  rw [ht]
  ring

omit [Group G] in
theorem linkReflect_eq_self_of_mem_linkCrossingEdges
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (e : Λ.linkCrossingEdges τ k) : e.1.linkReflect τ k = e.1 := by
  obtain ⟨_, hdir, hsource⟩ := Finset.mem_filter.mp e.2
  rw [PositiveEdge.linkReflect, if_pos hdir]
  congr 1
  ext i
  by_cases hi : i = τ
  · subst i
    simp only [linkReflection_apply_eq]
    have ht : e.1.target τ = e.1.source τ + 1 := by
      rw [PositiveEdge.target, hdir]
      simp [step, SignedDirection.delta_forward, unitVector]
    rw [ht, hsource]
    ring
  · rw [linkReflection_apply_ne hi]
    rw [PositiveEdge.target]
    have hid : i ≠ e.1.direction := fun hie => hi (hie.trans hdir)
    simp [step, SignedDirection.delta_forward, unitVector, hid]

omit [Group G] in
theorem linkReflect_mem_plaquette_boundary_iff (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) (p : Plaquette d) :
    e.linkReflect τ k ∈ (p.linkReflect τ k).boundary.edgeSupport ↔
      e ∈ p.boundary.edgeSupport := by
  rw [positiveEdge_linkReflect_eq_translate_siteReflect]
  rw [Plaquette.linkReflect,
    linkBridge_plaquette_boundary_edgeSupport_translate,
    Finset.mem_map_equiv]
  simpa [PositiveEdge.translationEquiv] using
    (siteReflect_mem_plaquette_boundary_iff τ k e p)

omit [Group G] in
theorem linkReflectPlaquette_base_eq_of_perpendicular (τ : Fin d) (k : ℤ)
    (p : Plaquette d) (hp : p.first = τ ∨ p.second = τ) :
    (p.linkReflect τ k).base τ = 2 * k - p.base τ := by
  rw [Plaquette.linkReflect, Plaquette.siteReflect, if_pos hp]
  simp [Plaquette.translate, Lattice.Cubic.translate, step,
    SignedDirection.delta_backward, unitVector, siteReflection_apply_eq]

omit [Group G] in
theorem linkReflectPlaquette_base_eq_of_not_perpendicular (τ : Fin d) (k : ℤ)
    (p : Plaquette d) (hp : ¬(p.first = τ ∨ p.second = τ)) :
    (p.linkReflect τ k).base τ = 2 * k + 1 - p.base τ := by
  rw [Plaquette.linkReflect, Plaquette.siteReflect, if_neg hp]
  simp [Plaquette.translate, Lattice.Cubic.translate, unitVector,
    siteReflection_apply_eq]
  ring

omit [Group G] in
theorem linkReflect_eq_self_of_crossPlaquette (τ : Fin d) (k : ℤ)
    (p : Plaquette d) (hp : p.base τ = k ∧
      (p.first = τ ∨ p.second = τ)) :
    p.linkReflect τ k = p := by
  rcases p with ⟨x, i, j, hij⟩
  simp only [Plaquette.linkReflect, Plaquette.siteReflect, hp.2, if_pos,
    Plaquette.translate]
  congr 1
  ext a
  by_cases ha : a = τ
  · subst a
    have hx : x τ = k := hp.1
    simp [Lattice.Cubic.translate, step, SignedDirection.delta,
      SignedDirection.backward, unitVector, hx]
    omega
  · simp [Lattice.Cubic.translate, step, SignedDirection.delta,
      SignedDirection.backward, unitVector, ha]

theorem linkReflect_mem_linkCrossPlaquettes_iff
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (p : Plaquette d) :
    p.linkReflect τ k ∈ Λ.linkCrossPlaquettes τ k ↔
      p ∈ Λ.linkCrossPlaquettes τ k := by
  simp only [linkCrossPlaquettes, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hbase, hperp⟩
    have hp' := (hΛ.2.1 p).mpr hp
    have hperp' : p.first = τ ∨ p.second = τ := by simpa using hperp
    rw [linkReflectPlaquette_base_eq_of_perpendicular τ k p hperp'] at hbase
    exact ⟨hp', by omega, hperp'⟩
  · rintro ⟨hp, hbase, hperp⟩
    refine ⟨(hΛ.2.1 p).mp hp, ?_, by simpa using hperp⟩
    rw [linkReflectPlaquette_base_eq_of_perpendicular τ k p hperp]
    omega

theorem activePlaquette_linkPartition (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.LinkSymmetric τ k) (p : Plaquette d) :
    p ∈ Λ.activePlaquettes ↔
      p ∈ Λ.linkCrossPlaquettes τ k ∨
      p ∈ Λ.linkPositivePlaquettes τ k ∨
      p.linkReflect τ k ∈ Λ.linkPositivePlaquettes τ k := by
  constructor
  · intro hp
    by_cases hplus : k < p.base τ
    · exact Or.inr <| Or.inl <| Finset.mem_filter.mpr ⟨hp, hplus⟩
    · by_cases hcross : p.base τ = k ∧ (p.first = τ ∨ p.second = τ)
      · exact Or.inl (Finset.mem_filter.mpr ⟨hp, hcross⟩)
      · right; right
        rw [linkPositivePlaquettes, Finset.mem_filter]
        refine ⟨(hΛ.2.1 p).mp hp, ?_⟩
        by_cases hperp : p.first = τ ∨ p.second = τ
        · rw [linkReflectPlaquette_base_eq_of_perpendicular τ k p hperp]
          have hne : p.base τ ≠ k := fun heq => hcross ⟨heq, hperp⟩
          omega
        · rw [linkReflectPlaquette_base_eq_of_not_perpendicular τ k p hperp]
          omega
  · rintro (hp | hp | hp)
    · exact (Finset.mem_filter.mp hp).1
    · exact (Finset.mem_filter.mp hp).1
    · exact (hΛ.2.1 p).mpr (Finset.mem_filter.mp hp).1

theorem activePlaquette_linkPartition_exclusive
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (p : Plaquette d) :
    (p ∈ Λ.linkCrossPlaquettes τ k →
      p ∉ Λ.linkPositivePlaquettes τ k ∧
      p.linkReflect τ k ∉ Λ.linkPositivePlaquettes τ k) ∧
    (p ∈ Λ.linkPositivePlaquettes τ k →
      p.linkReflect τ k ∉ Λ.linkPositivePlaquettes τ k) := by
  constructor
  · intro hp
    obtain ⟨_, hbase, hperp⟩ := Finset.mem_filter.mp hp
    constructor
    · intro hplus
      exact (by have := (Finset.mem_filter.mp hplus).2; omega)
    · intro hplus
      have hs := (Finset.mem_filter.mp hplus).2
      rw [linkReflectPlaquette_base_eq_of_perpendicular τ k p hperp,
        hbase] at hs
      omega
  · intro hp href
    have hs := (Finset.mem_filter.mp hp).2
    have hrs := (Finset.mem_filter.mp href).2
    by_cases hperp : p.first = τ ∨ p.second = τ
    · rw [linkReflectPlaquette_base_eq_of_perpendicular τ k p hperp] at hrs
      omega
    · rw [linkReflectPlaquette_base_eq_of_not_perpendicular τ k p hperp] at hrs
      omega

omit [Group G] in
@[simp]
theorem mem_linkNegativePlaquettes (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (p : Plaquette d) :
    p ∈ Λ.linkNegativePlaquettes τ k ↔
      p.linkReflect τ k ∈ Λ.linkPositivePlaquettes τ k := by
  rw [linkNegativePlaquettes, Finset.mem_map_equiv]
  rfl

theorem activePlaquettes_eq_linkReflection_union
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) :
    Λ.activePlaquettes = Λ.linkCrossPlaquettes τ k ∪
      (Λ.linkPositivePlaquettes τ k ∪ Λ.linkNegativePlaquettes τ k) := by
  ext p
  simp only [Finset.mem_union, mem_linkNegativePlaquettes]
  exact Λ.activePlaquette_linkPartition τ k hΛ p

theorem linkCrossPlaquettes_disjoint_linkSides
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) :
    Disjoint (Λ.linkCrossPlaquettes τ k)
      (Λ.linkPositivePlaquettes τ k ∪ Λ.linkNegativePlaquettes τ k) := by
  rw [Finset.disjoint_left]
  intro p hp hside
  rw [Finset.mem_union, mem_linkNegativePlaquettes] at hside
  exact hside.elim
    (Λ.activePlaquette_linkPartition_exclusive τ k hΛ p |>.1 hp |>.1)
    (Λ.activePlaquette_linkPartition_exclusive τ k hΛ p |>.1 hp |>.2)

theorem linkPositivePlaquettes_disjoint_linkNegativePlaquettes
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) :
    Disjoint (Λ.linkPositivePlaquettes τ k)
      (Λ.linkNegativePlaquettes τ k) := by
  rw [Finset.disjoint_left]
  intro p hp hneg
  rw [mem_linkNegativePlaquettes] at hneg
  exact Λ.activePlaquette_linkPartition_exclusive τ k hΛ p |>.2 hp hneg

omit [Group G] in
theorem linkReflect_not_mem_linkPositiveEdges
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (e : Λ.linkPositiveEdges τ k) :
    e.1.linkReflect τ k ∉ Λ.linkPositiveEdges τ k := by
  intro href
  have he := (Finset.mem_filter.mp e.2).2
  have href' := (Finset.mem_filter.mp href).2
  by_cases hdir : e.1.direction = τ
  · rw [source_linkReflect_eq_of_direction_eq τ k e.1 hdir] at href'
    omega
  · rw [source_linkReflect_eq_of_direction_ne τ k e.1 hdir,
      linkReflection_apply_eq] at href'
    omega

/-- The inverse of the crossing/negative/positive edge labeling. -/
def linkEdgeLabelInv (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) :
    (Λ.linkCrossingEdges τ k) ⊕
      ((Λ.linkPositiveEdges τ k) ⊕ (Λ.linkPositiveEdges τ k)) →
      Λ.dynamicEdges
  | Sum.inl e => ⟨e.1, (Finset.mem_filter.mp e.2).1⟩
  | Sum.inr (Sum.inl e) =>
      ⟨e.1.linkReflect τ k,
        (hΛ.1 e.1).mp (Finset.mem_filter.mp e.2).1⟩
  | Sum.inr (Sum.inr e) => ⟨e.1, (Finset.mem_filter.mp e.2).1⟩

@[simp]
theorem linkEdgeLabelInv_crossing (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.LinkSymmetric τ k)
    (e : Λ.linkCrossingEdges τ k) :
    Λ.linkEdgeLabelInv τ k hΛ (Sum.inl e) =
      ⟨e.1, (Finset.mem_filter.mp e.2).1⟩ := rfl

@[simp]
theorem linkEdgeLabelInv_negative_val (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.LinkSymmetric τ k)
    (e : Λ.linkPositiveEdges τ k) :
    (Λ.linkEdgeLabelInv τ k hΛ (Sum.inr (Sum.inl e))).1 =
      e.1.linkReflect τ k := rfl

@[simp]
theorem linkEdgeLabelInv_positive (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.LinkSymmetric τ k)
    (e : Λ.linkPositiveEdges τ k) :
    Λ.linkEdgeLabelInv τ k hΛ (Sum.inr (Sum.inr e)) =
      ⟨e.1, (Finset.mem_filter.mp e.2).1⟩ := rfl

/-- Every dynamic edge is uniquely crossing, positive, or the reflection of
a positive edge. -/
def linkEdgeLabelEquiv (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) :
    Λ.dynamicEdges ≃ (Λ.linkCrossingEdges τ k) ⊕
      ((Λ.linkPositiveEdges τ k) ⊕ (Λ.linkPositiveEdges τ k)) where
  toFun e := by
    if hcross : e.1 ∈ Λ.linkCrossingEdges τ k then
      exact Sum.inl ⟨e.1, hcross⟩
    else if hplus : e.1 ∈ Λ.linkPositiveEdges τ k then
      exact Sum.inr (Sum.inr ⟨e.1, hplus⟩)
    else
      refine Sum.inr (Sum.inl ⟨e.1.linkReflect τ k, ?_⟩)
      rw [linkPositiveEdges, Finset.mem_filter]
      refine ⟨(hΛ.1 e.1).mp e.2, ?_⟩
      by_cases hdir : e.1.direction = τ
      · have hsource : e.1.source τ < k := by
          by_contra hn
          have hge : k ≤ e.1.source τ := le_of_not_gt hn
          by_cases heq : e.1.source τ = k
          · exact hcross (Finset.mem_filter.mpr ⟨e.2, hdir, heq⟩)
          · exact hplus (Finset.mem_filter.mpr ⟨e.2, by omega⟩)
        rw [source_linkReflect_eq_of_direction_eq τ k e.1 hdir]
        omega
      · have hsource : e.1.source τ ≤ k := by
          by_contra hn
          exact hplus (Finset.mem_filter.mpr ⟨e.2, by omega⟩)
        rw [source_linkReflect_eq_of_direction_ne τ k e.1 hdir,
          linkReflection_apply_eq]
        omega
  invFun := Λ.linkEdgeLabelInv τ k hΛ
  left_inv e := by
    dsimp
    split_ifs with hcross hplus
    · rfl
    · rfl
    · apply Subtype.ext
      change (Λ.linkEdgeLabelInv τ k hΛ
        (Sum.inr (Sum.inl ⟨e.1.linkReflect τ k, _⟩))).1 = e.1
      rw [linkEdgeLabelInv_negative_val]
      exact PositiveEdge.linkReflect_linkReflect τ k e.1
    · apply Subtype.ext
      change (Λ.linkEdgeLabelInv τ k hΛ
        (Sum.inr (Sum.inl ⟨e.1.linkReflect τ k, _⟩))).1 = e.1
      rw [linkEdgeLabelInv_negative_val]
      exact PositiveEdge.linkReflect_linkReflect τ k e.1
  right_inv label := by
    rcases label with e | e
    · simp only [linkEdgeLabelInv_crossing]
      rw [dif_pos e.2]
    · rcases e with e | e
      · dsimp [linkEdgeLabelInv]
        rw [dif_neg]
        · rw [dif_neg]
          · simp
          · exact linkReflect_not_mem_linkPositiveEdges Λ τ k e
        · intro hcross
          obtain ⟨_, hdir, hsource⟩ := Finset.mem_filter.mp hcross
          have heplus := (Finset.mem_filter.mp e.2).2
          rw [source_linkReflect_eq_of_direction_eq τ k e.1
            (by simpa using hdir)] at hsource
          omega
      · simp only [linkEdgeLabelInv_positive]
        rw [dif_neg, dif_pos e.2]
        intro hcross
        have hsource := (Finset.mem_filter.mp e.2).2
        exact (by obtain ⟨_, _, hs⟩ := Finset.mem_filter.mp hcross; omega)

/-- Reflection fixes crossing labels and exchanges the two side labels. -/
def linkReflectLabelIndex {C P : Type*} : C ⊕ (P ⊕ P) → C ⊕ (P ⊕ P)
  | Sum.inl c => Sum.inl c
  | Sum.inr (Sum.inl p) => Sum.inr (Sum.inr p)
  | Sum.inr (Sum.inr p) => Sum.inr (Sum.inl p)

theorem linkEdgeLabelEquiv_linkReflect (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.LinkSymmetric τ k)
    (e : Λ.dynamicEdges) :
    Λ.linkEdgeLabelEquiv τ k hΛ
        ⟨e.1.linkReflect τ k, (hΛ.1 e.1).mp e.2⟩ =
      linkReflectLabelIndex (Λ.linkEdgeLabelEquiv τ k hΛ e) := by
  let E := Λ.linkEdgeLabelEquiv τ k hΛ
  generalize hlabel : E e = label
  rcases label with c | p
  · have hec : e.1 = c.1 := by
      have he : E.symm (Sum.inl c) = e := by
        apply E.injective
        simp [hlabel]
      have he' := congrArg Subtype.val he
      simpa only [linkEdgeLabelEquiv] using he'.symm
    have href : e.1.linkReflect τ k = e.1 := by
      rw [hec]
      exact linkReflect_eq_self_of_mem_linkCrossingEdges Λ τ k c
    have hsub : (⟨e.1.linkReflect τ k, (hΛ.1 e.1).mp e.2⟩ :
        Λ.dynamicEdges) = e := Subtype.ext href
    rw [hsub, hlabel]
    rfl
  · rcases p with p | p
    · have heval : e.1 = p.1.linkReflect τ k := by
        have he : E.symm (Sum.inr (Sum.inl p)) = e := by
          apply E.injective
          simp [hlabel]
        have he' := congrArg Subtype.val he
        simpa only [linkEdgeLabelEquiv] using he'.symm
      have href : e.1.linkReflect τ k = p.1 := by
        rw [heval]
        exact PositiveEdge.linkReflect_linkReflect τ k p.1
      have hsub : (⟨e.1.linkReflect τ k, (hΛ.1 e.1).mp e.2⟩ :
          Λ.dynamicEdges) = ⟨p.1, (Finset.mem_filter.mp p.2).1⟩ := by
        apply Subtype.ext
        exact href
      rw [hsub]
      change E ⟨p.1, _⟩ = _
      exact E.apply_symm_apply (Sum.inr (Sum.inr p))
    · have heval : e.1 = p.1 := by
        have he : E.symm (Sum.inr (Sum.inr p)) = e := by
          apply E.injective
          simp [hlabel]
        have he' := congrArg Subtype.val he
        simpa only [linkEdgeLabelEquiv] using he'.symm
      have hsub : (⟨e.1.linkReflect τ k, (hΛ.1 e.1).mp e.2⟩ :
          Λ.dynamicEdges) =
            ⟨p.1.linkReflect τ k,
              (hΛ.1 p.1).mp (Finset.mem_filter.mp p.2).1⟩ := by
        apply Subtype.ext
        exact congrArg (PositiveEdge.linkReflect τ k) heval
      rw [hsub]
      change E ⟨p.1.linkReflect τ k, _⟩ = _
      exact E.apply_symm_apply (Sum.inr (Sum.inl p))

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Assemble crossing/negative/positive variables into the original dynamic
edge family. -/
def linkAssemble (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) :
    C(LinkReflection.ReflectedConfiguration G
        (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k),
      DynamicConfiguration Λ) where
  toFun U e :=
    match Λ.linkEdgeLabelEquiv τ k hΛ e with
    | Sum.inl c => U.1 c
    | Sum.inr (Sum.inl p) =>
        if p.1.direction = τ then (U.2.1 p)⁻¹ else U.2.1 p
    | Sum.inr (Sum.inr p) => U.2.2 p
  continuous_toFun := by
    apply continuous_pi
    intro e
    generalize hlabel : Λ.linkEdgeLabelEquiv τ k hΛ e = label
    rcases label with c | p
    · simpa [hlabel] using (continuous_apply c).comp
        (continuous_fst : Continuous fun U :
          LinkReflection.ReflectedConfiguration G
            (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k) => U.1)
    · rcases p with p | p
      · by_cases hdir : p.1.direction = τ
        · simpa [hlabel, hdir] using continuous_inv.comp
            ((continuous_apply p).comp (continuous_fst.comp continuous_snd))
        · simpa [hlabel, hdir] using
            (continuous_apply p).comp (continuous_fst.comp continuous_snd)
      · simpa [hlabel] using
          (continuous_apply p).comp (continuous_snd.comp continuous_snd)

/-- Assembly intertwines the labelled link reflection with geometric
half-integer reflection of the evaluated full configuration. -/
theorem linkAssemble_reflect (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.LinkSymmetric τ k)
    (U : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k)) :
    Λ.evaluate (Λ.linkAssemble τ k hΛ (LinkReflection.reflect U)) =
      linkReflectConfiguration τ k
        (Λ.evaluate (Λ.linkAssemble τ k hΛ U)) := by
  funext e
  by_cases he : e ∈ Λ.dynamicEdges
  · rw [Λ.evaluate_of_mem _ e he]
    simp only [linkReflectConfiguration]
    have href : e.linkReflect τ k ∈ Λ.dynamicEdges := (hΛ.1 e).mp he
    rw [Λ.evaluate_of_mem _ (e.linkReflect τ k) href]
    let edyn : Λ.dynamicEdges := ⟨e, he⟩
    let eref : Λ.dynamicEdges := ⟨e.linkReflect τ k, href⟩
    have hlabel := linkEdgeLabelEquiv_linkReflect Λ τ k hΛ edyn
    change (Λ.linkAssemble τ k hΛ (LinkReflection.reflect U)) edyn =
      (if e.direction = τ then ((Λ.linkAssemble τ k hΛ U) eref)⁻¹
        else (Λ.linkAssemble τ k hΛ U) eref)
    unfold linkAssemble
    simp only [ContinuousMap.coe_mk]
    generalize heq : Λ.linkEdgeLabelEquiv τ k hΛ edyn = label
    rw [heq] at hlabel
    rcases label with c | p
    · rw [hlabel]
      have hdir : e.direction = τ := by
        have hcdir := (Finset.mem_filter.mp c.2).2.1
        have heval : e = c.1 := by
          have hsub : edyn = (Λ.linkEdgeLabelEquiv τ k hΛ).symm
              (Sum.inl c) := by
            apply (Λ.linkEdgeLabelEquiv τ k hΛ).injective
            rw [heq, (Λ.linkEdgeLabelEquiv τ k hΛ).apply_symm_apply]
          have := congrArg Subtype.val hsub
          simpa [edyn, linkEdgeLabelEquiv] using this
        simpa [heval] using hcdir
      simp [linkReflectLabelIndex, hdir, LinkReflection.reflect]
    · rcases p with p | p
      · rw [hlabel]
        have hdir : e.direction = p.1.direction := by
          have heval : e = p.1.linkReflect τ k := by
            have hsub : edyn = (Λ.linkEdgeLabelEquiv τ k hΛ).symm
                (Sum.inr (Sum.inl p)) := by
              apply (Λ.linkEdgeLabelEquiv τ k hΛ).injective
              rw [heq, (Λ.linkEdgeLabelEquiv τ k hΛ).apply_symm_apply]
            have := congrArg Subtype.val hsub
            simpa [edyn, linkEdgeLabelEquiv] using this
          rw [heval]
          simp
        by_cases hpdir : p.1.direction = τ <;>
          simp [linkReflectLabelIndex, hdir, hpdir, LinkReflection.reflect]
      · rw [hlabel]
        have hdir : e.direction = p.1.direction := by
          have heval : e = p.1 := by
            have hsub : edyn = (Λ.linkEdgeLabelEquiv τ k hΛ).symm
                (Sum.inr (Sum.inr p)) := by
              apply (Λ.linkEdgeLabelEquiv τ k hΛ).injective
              rw [heq, (Λ.linkEdgeLabelEquiv τ k hΛ).apply_symm_apply]
            have := congrArg Subtype.val hsub
            simpa [edyn, linkEdgeLabelEquiv] using this
          rw [heval]
        by_cases hpdir : p.1.direction = τ <;>
          simp [linkReflectLabelIndex, hdir, hpdir, LinkReflection.reflect]
  · rw [Λ.evaluate_of_not_mem _ e he]
    simp only [linkReflectConfiguration]
    rw [Λ.evaluate_of_not_mem]
    · exact congrFun hΛ.2.2 e |>.symm
    · exact fun href => he ((hΛ.1 e).mpr href)

/-- The full configuration visible from crossing and positive-side
variables, with the negative side filled by identity. -/
def linkEvaluatePositive (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.LinkSymmetric τ k) :
    C(LinkReflection.HalfConfiguration G
        (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k),
      Configuration d G) :=
  (⟨Λ.evaluate, Λ.continuous_evaluate⟩ : C(DynamicConfiguration Λ,
    Configuration d G)).comp <|
    (Λ.linkAssemble τ k hΛ).comp
      { toFun := fun U => (U.1, (1, U.2))
        continuous_toFun := by fun_prop }

/-- The crossing edge ending at a site in the first positive layer. -/
def linkIncomingCrossingEdge (τ : Fin d) (x : Site d) : PositiveEdge d :=
  ⟨step x (.backward τ), τ⟩

/-- Site gauge used to fix crossing links.  It is nontrivial only on the
first positive site layer and reads the incoming dynamic crossing link. -/
def linkCrossingGaugeValue (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ)
    (U : LinkReflection.CrossingConfiguration G (Λ.linkCrossingEdges τ k))
    (x : Site d) : G :=
  if hx : x τ = k + 1 then
    if he : linkIncomingCrossingEdge τ x ∈ Λ.linkCrossingEdges τ k then
      U ⟨linkIncomingCrossingEdge τ x, he⟩
    else 1
  else 1

theorem continuous_linkCrossingGaugeValue
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ) (x : Site d) :
    Continuous (fun U : LinkReflection.CrossingConfiguration G
      (Λ.linkCrossingEdges τ k) => Λ.linkCrossingGaugeValue τ k U x) := by
  by_cases hx : x τ = k + 1
  · by_cases he : linkIncomingCrossingEdge τ x ∈ Λ.linkCrossingEdges τ k
    · simpa [linkCrossingGaugeValue, hx, he] using
        (continuous_apply (⟨linkIncomingCrossingEdge τ x, he⟩ :
          Λ.linkCrossingEdges τ k))
    · simpa [linkCrossingGaugeValue, hx, he] using
        (continuous_const : Continuous fun _ :
          LinkReflection.CrossingConfiguration G
            (Λ.linkCrossingEdges τ k) => (1 : G))
  · simpa [linkCrossingGaugeValue, hx] using
      (continuous_const : Continuous fun _ :
        LinkReflection.CrossingConfiguration G
          (Λ.linkCrossingEdges τ k) => (1 : G))

/-- Coordinatewise positive-side change induced by the crossing-link gauge
transformation. -/
def linkCrossingGaugeFix (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) :
    LinkReflection.CrossingForestGaugeFix G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k) where
  leftMultiplier U e := Λ.linkCrossingGaugeValue τ k U e.1.source
  rightMultiplier U e :=
    (Λ.linkCrossingGaugeValue τ k U e.1.target)⁻¹
  continuous_leftMultiplier e :=
    Λ.continuous_linkCrossingGaugeValue τ k e.1.source
  continuous_rightMultiplier e := continuous_inv.comp
    (Λ.continuous_linkCrossingGaugeValue τ k e.1.target)

/-- The full-lattice gauge transformation used at a fixed crossing field. -/
def linkCrossingGaugeTransformation (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ)
    (U : LinkReflection.CrossingConfiguration G (Λ.linkCrossingEdges τ k)) :
    GaugeTransformation d G :=
  fun x => Λ.linkCrossingGaugeValue τ k U x

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem linkCrossingGaugeValue_of_coord_ne
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (U : LinkReflection.CrossingConfiguration G (Λ.linkCrossingEdges τ k))
    (x : Site d) (hx : x τ ≠ k + 1) :
    Λ.linkCrossingGaugeValue τ k U x = 1 := by
  simp [linkCrossingGaugeValue, hx]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem linkIncomingCrossingEdge_target (τ : Fin d) (x : Site d) :
    (linkIncomingCrossingEdge τ x).target = x := by
  exact step_reverse x (.backward τ)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem linkIncomingCrossingEdge_target_crossing
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (e : Λ.linkCrossingEdges τ k) :
    linkIncomingCrossingEdge τ e.1.target = e.1 := by
  obtain ⟨_, hdir, _⟩ := Finset.mem_filter.mp e.2
  rcases e with ⟨⟨x, i⟩, he⟩
  simp only at hdir
  subst i
  change (⟨step (step x (.forward τ)) (.backward τ), τ⟩ : PositiveEdge d) =
    (⟨x, τ⟩ : PositiveEdge d)
  congr 1
  simpa [SignedDirection.forward, SignedDirection.backward] using
    (step_reverse x (.forward τ))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem linkCrossingGaugeValue_crossing_source
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (U : LinkReflection.CrossingConfiguration G (Λ.linkCrossingEdges τ k))
    (e : Λ.linkCrossingEdges τ k) :
    Λ.linkCrossingGaugeValue τ k U e.1.source = 1 := by
  apply Λ.linkCrossingGaugeValue_of_coord_ne
  have hs := (Finset.mem_filter.mp e.2).2.2
  omega

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem linkCrossingGaugeValue_crossing_target
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (U : LinkReflection.CrossingConfiguration G (Λ.linkCrossingEdges τ k))
    (e : Λ.linkCrossingEdges τ k) :
    Λ.linkCrossingGaugeValue τ k U e.1.target = U e := by
  have hdir := (Finset.mem_filter.mp e.2).2.1
  have hs := (Finset.mem_filter.mp e.2).2.2
  have ht : e.1.target τ = k + 1 := by
    rw [PositiveEdge.target, hdir]
    simp [step, SignedDirection.delta_forward, unitVector, hs]
  simp only [linkCrossingGaugeValue, ht, ↓reduceDIte]
  have hin : linkIncomingCrossingEdge τ e.1.target ∈
      Λ.linkCrossingEdges τ k := by
    rw [linkIncomingCrossingEdge_target_crossing Λ τ k e]
    exact e.2
  rw [dif_pos hin]
  congr 1
  apply Subtype.ext
  exact linkIncomingCrossingEdge_target_crossing Λ τ k e

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem linkReflect_positiveEdge_endpoints_le
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (e : Λ.linkPositiveEdges τ k) :
    (e.1.linkReflect τ k).source τ ≤ k ∧
      (e.1.linkReflect τ k).target τ ≤ k := by
  have hs := (Finset.mem_filter.mp e.2).2
  by_cases hdir : e.1.direction = τ
  · have hrefs := source_linkReflect_eq_of_direction_eq τ k e.1 hdir
    have hd : (e.1.linkReflect τ k).direction = τ := by simpa using hdir
    constructor
    · omega
    · rw [PositiveEdge.target, hd]
      simp [step, SignedDirection.delta_forward, unitVector]
      omega
  · have hrefs := source_linkReflect_eq_of_direction_ne τ k e.1 hdir
    have hd : (e.1.linkReflect τ k).direction ≠ τ := by simpa using hdir
    constructor
    · rw [hrefs, linkReflection_apply_eq]
      omega
    · rw [PositiveEdge.target]
      change step (e.1.linkReflect τ k).source
        (.forward (e.1.linkReflect τ k).direction) τ ≤ k
      simp [step, SignedDirection.delta_forward, unitVector, Ne.symm hd]
      rw [hrefs, linkReflection_apply_eq]
      omega

/-- At every dynamic edge, the crossing-field gauge transform of the
assembled configuration is the assembly with crossing links fixed to `1`,
the negative side unchanged, and the positive side changed coordinatewise. -/
theorem gaugeTransform_linkAssemble_eq_fixed_on_dynamic
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k)
    (U : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k))
    (e : Λ.dynamicEdges) :
    gaugeTransform (Λ.linkCrossingGaugeTransformation τ k U.1)
        (Λ.evaluate (Λ.linkAssemble τ k hΛ U)) e.1 =
      Λ.evaluate (Λ.linkAssemble τ k hΛ
        (1, (U.2.1, (Λ.linkCrossingGaugeFix τ k).fixSide U.1 U.2.2))) e.1 := by
  rw [gaugeTransform_apply]
  rw [Λ.evaluate_of_mem _ e.1 e.2, Λ.evaluate_of_mem _ e.1 e.2]
  change Λ.linkCrossingGaugeValue τ k U.1 e.1.source *
      (Λ.linkAssemble τ k hΛ U) e *
        (Λ.linkCrossingGaugeValue τ k U.1 e.1.target)⁻¹ =
    (Λ.linkAssemble τ k hΛ
      (1, (U.2.1, (Λ.linkCrossingGaugeFix τ k).fixSide U.1 U.2.2))) e
  generalize hlabel : Λ.linkEdgeLabelEquiv τ k hΛ e = label
  rcases label with c | p
  · have heval : e.1 = c.1 := by
      have hsub : e = (Λ.linkEdgeLabelEquiv τ k hΛ).symm (Sum.inl c) := by
        apply (Λ.linkEdgeLabelEquiv τ k hΛ).injective
        rw [hlabel, (Λ.linkEdgeLabelEquiv τ k hΛ).apply_symm_apply]
      exact congrArg Subtype.val hsub
    rw [heval]
    simp only [linkAssemble, ContinuousMap.coe_mk, hlabel]
    rw [Λ.linkCrossingGaugeValue_crossing_source τ k U.1 c,
      Λ.linkCrossingGaugeValue_crossing_target τ k U.1 c]
    simp
  · rcases p with p | p
    · have heval : e.1 = p.1.linkReflect τ k := by
        have hsub : e = (Λ.linkEdgeLabelEquiv τ k hΛ).symm
            (Sum.inr (Sum.inl p)) := by
          apply (Λ.linkEdgeLabelEquiv τ k hΛ).injective
          rw [hlabel, (Λ.linkEdgeLabelEquiv τ k hΛ).apply_symm_apply]
        have := congrArg Subtype.val hsub
        simpa only [linkEdgeLabelEquiv] using this
      have hends := Λ.linkReflect_positiveEdge_endpoints_le τ k p
      have hsource : e.1.source τ ≠ k + 1 := by rw [heval]; omega
      have htarget : e.1.target τ ≠ k + 1 := by rw [heval]; omega
      rw [Λ.linkCrossingGaugeValue_of_coord_ne τ k U.1 e.1.source hsource,
        Λ.linkCrossingGaugeValue_of_coord_ne τ k U.1 e.1.target htarget]
      simp only [one_mul, inv_one, mul_one]
      unfold linkAssemble
      simp only [ContinuousMap.coe_mk, hlabel]
    · have heval : e.1 = p.1 := by
        have hsub : e = (Λ.linkEdgeLabelEquiv τ k hΛ).symm
            (Sum.inr (Sum.inr p)) := by
          apply (Λ.linkEdgeLabelEquiv τ k hΛ).injective
          rw [hlabel, (Λ.linkEdgeLabelEquiv τ k hΛ).apply_symm_apply]
        exact congrArg Subtype.val hsub
      unfold linkAssemble
      simp only [ContinuousMap.coe_mk, hlabel]
      change Λ.linkCrossingGaugeValue τ k U.1 e.1.source * U.2.2 p *
          (Λ.linkCrossingGaugeValue τ k U.1 e.1.target)⁻¹ =
        (Λ.linkCrossingGaugeFix τ k).fixSide U.1 U.2.2 p
      rw [LinkReflection.CrossingForestGaugeFix.fixSide_apply]
      rw [heval]
      rfl

/-- A full configuration carrying only one strict positive-side field. -/
def linkEvaluateSide (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.LinkSymmetric τ k) :
    C(LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k),
      Configuration d G) :=
  (Λ.linkEvaluatePositive τ k hΛ).comp
    { toFun := fun U => (1, U)
      continuous_toFun := by fun_prop }

/-- Positive-side Wilson action used after the crossing links are fixed. -/
def linkPositiveWilsonAction {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k)
    (ρ : Wilson.ContinuousUnitaryRepData G n) :
    C(LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k), ℝ) where
  toFun U := ∑ p ∈ Λ.linkPositivePlaquettes τ k,
    ρ.wilsonPotential (holonomy (Λ.linkEvaluateSide τ k hΛ U) p.boundary)
  continuous_toFun := by
    apply continuous_finsetSum _
    intro p _
    exact ρ.wilsonPotential.toContinuousMap.continuous.comp
      ((continuous_holonomy p.boundary).comp
        (Λ.linkEvaluateSide τ k hΛ).continuous)

/-- The tangential edge in the first positive layer of a cross plaquette. -/
def linkCrossPositiveEdge (τ : Fin d) (p : Plaquette d) : PositiveEdge d :=
  if p.first = τ then ⟨step p.base (.forward τ), p.second⟩
  else ⟨step p.base (.forward τ), p.first⟩

omit [Group G] in
theorem linkCrossPositiveEdge_direction_ne (τ : Fin d) (p : Plaquette d)
    (hp : p.first = τ ∨ p.second = τ) :
    (linkCrossPositiveEdge τ p).direction ≠ τ := by
  unfold linkCrossPositiveEdge
  by_cases hfirst : p.first = τ
  · simp only [hfirst, if_true]
    exact fun hsecond => p.distinct (hfirst.trans hsecond.symm)
  · simp only [hfirst, if_false]
    exact hfirst

omit [Group G] in
theorem linkCrossPositiveEdge_source_coord (τ : Fin d) (k : ℤ)
    (p : Plaquette d) (hbase : p.base τ = k) :
    (linkCrossPositiveEdge τ p).source τ = k + 1 := by
  unfold linkCrossPositiveEdge
  split <;> simp [step_forward_apply, hbase]

omit [Group G] in
theorem linkCrossPositiveEdge_mem_boundary (τ : Fin d) (p : Plaquette d)
    (hp : p.first = τ ∨ p.second = τ) :
    linkCrossPositiveEdge τ p ∈ p.boundary.edgeSupport := by
  rw [linkBridge_plaquette_boundary_edgeSupport]
  unfold linkCrossPositiveEdge
  by_cases hfirst : p.first = τ
  · simp [hfirst]
  · have hsecond : p.second = τ := hp.resolve_left hfirst
    simp [hfirst, hsecond]

omit [Group G] in
theorem linkCrossPositiveEdge_linkReflect (τ : Fin d) (k : ℤ)
    (p : Plaquette d) (hbase : p.base τ = k)
    (hp : p.first = τ ∨ p.second = τ) :
    (linkCrossPositiveEdge τ p).linkReflect τ k =
      (if p.first = τ then ⟨p.base, p.second⟩ else ⟨p.base, p.first⟩) := by
  have hdir := linkCrossPositiveEdge_direction_ne τ p hp
  rw [PositiveEdge.linkReflect, if_neg hdir]
  unfold linkCrossPositiveEdge
  by_cases hfirst : p.first = τ
  · simp only [hfirst, if_true]
    congr 1
    ext i
    by_cases hi : i = τ
    · subst i
      simp [linkReflection_apply_eq, step_forward_apply, hbase]
      omega
    · simp [linkReflection_apply_ne hi, step_forward_apply, hi]
  · simp only [hfirst, if_false]
    congr 1
    ext i
    by_cases hi : i = τ
    · subst i
      simp [linkReflection_apply_eq, step_forward_apply, hbase]
      omega
    · simp [linkReflection_apply_ne hi, step_forward_apply, hi]

/-- Positive half-holonomy attached to a cross plaquette after crossing-link
gauge fixing. -/
def linkCrossHolonomy
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k)
    (p : Λ.linkCrossPlaquettes τ k) :
    C(LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k), G) where
  toFun U := Λ.linkEvaluateSide τ k hΛ U (linkCrossPositiveEdge τ p.1)
  continuous_toFun := (continuous_apply (linkCrossPositiveEdge τ p.1)).comp
    (Λ.linkEvaluateSide τ k hΛ).continuous

/-- Concrete gauge-fixed Wilson data.  Only its gauge-fixed pairing is used:
the actual one-sided crossing gauge transformation is proved separately. -/
def linkWilsonDecomposition {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k)
    (ρ : Wilson.ContinuousUnitaryRepData G n) :
    LinkReflection.WilsonActionDecomposition G n
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k)
      (Λ.linkCrossPlaquettes τ k) where
  gaugeFix := Λ.linkCrossingGaugeFix τ k
  representation := ρ
  positiveAction := Λ.linkPositiveWilsonAction τ k hΛ ρ
  crossHolonomy := Λ.linkCrossHolonomy τ k hΛ

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem boundaryEdge_source_gt_of_mem_linkPositivePlaquettes
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (p : Plaquette d) (hp : p ∈ Λ.linkPositivePlaquettes τ k)
    (e : PositiveEdge d) (he : e ∈ p.boundary.edgeSupport) :
    k < e.source τ := by
  have hpbase := (Finset.mem_filter.mp hp).2
  rw [linkBridge_plaquette_boundary_edgeSupport] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact hpbase
  · change k < step p.base (.forward p.first) τ
    rw [step_forward_apply]
    split <;> omega
  · change k < step p.base (.forward p.second) τ
    rw [step_forward_apply]
    split <;> omega
  · exact hpbase

theorem linkAssemble_fixed_eq_linkEvaluateSide_of_source_gt
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k)
    (V : LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
      LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k))
    (e : PositiveEdge d) (hedyn : e ∈ Λ.dynamicEdges)
    (heside : k < e.source τ) :
    Λ.evaluate (Λ.linkAssemble τ k hΛ (1, V)) e =
      Λ.linkEvaluateSide τ k hΛ V.2 e := by
  rw [Λ.evaluate_of_mem _ e hedyn]
  change (Λ.linkAssemble τ k hΛ (1, V)) ⟨e, hedyn⟩ =
    Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (1, V.2))) e
  rw [Λ.evaluate_of_mem _ e hedyn]
  let edyn : Λ.dynamicEdges := ⟨e, hedyn⟩
  have hplus : e ∈ Λ.linkPositiveEdges τ k :=
    Finset.mem_filter.mpr ⟨hedyn, heside⟩
  have hlabel : Λ.linkEdgeLabelEquiv τ k hΛ edyn =
      Sum.inr (Sum.inr (⟨e, hplus⟩ : Λ.linkPositiveEdges τ k)) := by
    unfold linkEdgeLabelEquiv
    dsimp [edyn]
    rw [dif_neg, dif_pos hplus]
    intro hcross
    have hs := (Finset.mem_filter.mp hcross).2.2
    omega
  simp only [linkAssemble, ContinuousMap.coe_mk]
  rw [hlabel]

theorem plaquetteHolonomy_linkAssemble_fixed_eq_side
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (V : LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
      LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k))
    (p : Plaquette d) (hp : p ∈ Λ.linkPositivePlaquettes τ k) :
    FiniteVolume.plaquetteHolonomy Λ (Λ.linkAssemble τ k hΛ (1, V)) p =
      holonomy (Λ.linkEvaluateSide τ k hΛ V.2) p.boundary := by
  unfold FiniteVolume.plaquetteHolonomy
  apply holonomy_eq_of_eqOn_edgeSupport
  intro e he
  have hpactive := (Finset.mem_filter.mp hp).1
  have hedyn := hclosed p hpactive he
  exact Λ.linkAssemble_fixed_eq_linkEvaluateSide_of_source_gt τ k hΛ V e hedyn
    (Λ.boundaryEdge_source_gt_of_mem_linkPositivePlaquettes τ k p hp e he)

theorem plaquetteTerm_linkReflect_fixed
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n)
    (V : LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
      LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k))
    (p : Plaquette d) (hp : p ∈ Λ.linkPositivePlaquettes τ k) :
    ρ.wilsonPotential (FiniteVolume.plaquetteHolonomy Λ
        (Λ.linkAssemble τ k hΛ (1, V)) (p.linkReflect τ k)) =
      ρ.wilsonPotential
        (holonomy (Λ.linkEvaluateSide τ k hΛ V.1) p.boundary) := by
  unfold FiniteVolume.plaquetteHolonomy
  let U0 : LinkReflection.CrossingConfiguration G
      (Λ.linkCrossingEdges τ k) := 1
  have hreflect := Λ.linkAssemble_reflect τ k hΛ
    (U0, (V.1, V.2))
  have hpot := ρ.wilsonPotential.apply_holonomy_linkReflectConfiguration
    τ k (Λ.evaluate (Λ.linkAssemble τ k hΛ (U0, V))) p
  have hreflectU : LinkReflection.reflect
      (U0, (V.1, V.2)) = (U0, (V.2, V.1)) := by
    ext <;> simp [LinkReflection.reflect, U0]
  calc
    ρ.wilsonPotential
        (holonomy (Λ.evaluate (Λ.linkAssemble τ k hΛ (1, V)))
          (p.linkReflect τ k).boundary) =
      ρ.wilsonPotential
        (holonomy (linkReflectConfiguration τ k
          (Λ.evaluate (Λ.linkAssemble τ k hΛ (U0, V)))) p.boundary) :=
        hpot.symm
    _ = ρ.wilsonPotential
        (holonomy (Λ.evaluate (Λ.linkAssemble τ k hΛ
          (U0, (V.2, V.1)))) p.boundary) := by rw [← hreflect, hreflectU]
    _ = ρ.wilsonPotential
        (holonomy (Λ.linkEvaluateSide τ k hΛ V.1) p.boundary) :=
      congrArg ρ.wilsonPotential
        (Λ.plaquetteHolonomy_linkAssemble_fixed_eq_side τ k hΛ hclosed
          (V.2, V.1) p hp)

theorem linkCrossingEdge_value_fixed
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k)
    (V : LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
      LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k))
    (e : PositiveEdge d) (he : e ∈ Λ.linkCrossingEdges τ k) :
    Λ.evaluate (Λ.linkAssemble τ k hΛ (1, V)) e = 1 := by
  have hedyn := (Finset.mem_filter.mp he).1
  rw [Λ.evaluate_of_mem _ e hedyn]
  let edyn : Λ.dynamicEdges := ⟨e, hedyn⟩
  have hlabel : Λ.linkEdgeLabelEquiv τ k hΛ edyn =
      Sum.inl (⟨e, he⟩ : Λ.linkCrossingEdges τ k) := by
    unfold linkEdgeLabelEquiv
    dsimp [edyn]
    rw [dif_pos he]
  simp only [linkAssemble, ContinuousMap.coe_mk]
  rw [hlabel]
  rfl

theorem linkNegativeTangent_value_fixed
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k)
    (V : LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
      LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k))
    (e : Λ.linkPositiveEdges τ k) (hdir : e.1.direction ≠ τ) :
    Λ.evaluate (Λ.linkAssemble τ k hΛ (1, V))
        (e.1.linkReflect τ k) = V.1 e := by
  have hedyn : e.1.linkReflect τ k ∈ Λ.dynamicEdges :=
    (hΛ.1 e.1).mp (Finset.mem_filter.mp e.2).1
  rw [Λ.evaluate_of_mem _ _ hedyn]
  let edyn : Λ.dynamicEdges := ⟨e.1.linkReflect τ k, hedyn⟩
  have hlabel : Λ.linkEdgeLabelEquiv τ k hΛ edyn =
      Sum.inr (Sum.inl e) := by
    exact (Λ.linkEdgeLabelEquiv τ k hΛ).apply_symm_apply
      (Sum.inr (Sum.inl e))
  simp only [linkAssemble, ContinuousMap.coe_mk]
  rw [hlabel]
  change (if e.1.direction = τ then (V.1 e)⁻¹ else V.1 e) = V.1 e
  rw [if_neg hdir]

theorem wilsonPotential_crossPlaquette_linkAssemble_fixed
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n)
    (V : LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
      LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k))
    (p : Λ.linkCrossPlaquettes τ k) :
    ρ.wilsonPotential (FiniteVolume.plaquetteHolonomy Λ
        (Λ.linkAssemble τ k hΛ (1, V)) p.1) =
      ρ.wilsonPotential
        ((Λ.linkCrossHolonomy τ k hΛ p) V.2 *
          ((Λ.linkCrossHolonomy τ k hΛ p) V.1)⁻¹) := by
  obtain ⟨hpactive, hbase, hperp⟩ := Finset.mem_filter.mp p.2
  let etop := linkCrossPositiveEdge τ p.1
  have hetopBoundary : etop ∈ p.1.boundary.edgeSupport :=
    linkCrossPositiveEdge_mem_boundary τ p.1 hperp
  have hetopDyn : etop ∈ Λ.dynamicEdges :=
    hclosed p.1 hpactive hetopBoundary
  have hetopSource : k < etop.source τ := by
    rw [linkCrossPositiveEdge_source_coord τ k p.1 hbase]
    omega
  have hetopPlus : etop ∈ Λ.linkPositiveEdges τ k :=
    Finset.mem_filter.mpr ⟨hetopDyn, hetopSource⟩
  let et : Λ.linkPositiveEdges τ k := ⟨etop, hetopPlus⟩
  have hdir : et.1.direction ≠ τ :=
    linkCrossPositiveEdge_direction_ne τ p.1 hperp
  have hside (W : LinkReflection.SideConfiguration G
      (Λ.linkPositiveEdges τ k)) :
      Λ.linkEvaluateSide τ k hΛ W etop = W et := by
    change Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (1, W))) etop = W et
    rw [Λ.evaluate_of_mem _ etop hetopDyn]
    have hlabel : Λ.linkEdgeLabelEquiv τ k hΛ ⟨etop, hetopDyn⟩ =
        Sum.inr (Sum.inr et) := by
      unfold linkEdgeLabelEquiv
      dsimp [et]
      rw [dif_neg, dif_pos hetopPlus]
      intro hc
      have := (Finset.mem_filter.mp hc).2.2
      omega
    simp only [linkAssemble, ContinuousMap.coe_mk]
    rw [hlabel]
  have htop (W : LinkReflection.SideConfiguration G
      (Λ.linkPositiveEdges τ k)) :
      Λ.evaluate (Λ.linkAssemble τ k hΛ (1, (V.1, W))) etop = W et := by
    exact (Λ.linkAssemble_fixed_eq_linkEvaluateSide_of_source_gt
      τ k hΛ (V.1, W) etop hetopDyn hetopSource).trans (hside W)
  have hbottom :
      Λ.evaluate (Λ.linkAssemble τ k hΛ (1, V))
          (etop.linkReflect τ k) = V.1 et := by
    exact Λ.linkNegativeTangent_value_fixed τ k hΛ V et hdir
  have hcrossValue (e : PositiveEdge d)
      (he : e ∈ p.1.boundary.edgeSupport)
      (hdirE : e.direction = τ) (hsourceE : e.source τ = k) :
      Λ.evaluate (Λ.linkAssemble τ k hΛ (1, V)) e = 1 := by
    apply Λ.linkCrossingEdge_value_fixed τ k hΛ V e
    exact Finset.mem_filter.mpr ⟨hclosed p.1 hpactive he, hdirE, hsourceE⟩
  unfold FiniteVolume.plaquetteHolonomy
  rw [holonomy_plaquette_boundary]
  change ρ.wilsonPotential _ = ρ.wilsonPotential (_ * _⁻¹)
  unfold linkCrossHolonomy
  change ρ.wilsonPotential _ = ρ.wilsonPotential
    (Λ.linkEvaluateSide τ k hΛ V.2 etop *
      (Λ.linkEvaluateSide τ k hΛ V.1 etop)⁻¹)
  rw [hside V.2, hside V.1]
  by_cases hfirst : p.1.first = τ
  · have hsecond : p.1.second ≠ τ := fun hs => p.1.distinct (hfirst.trans hs.symm)
    have hc0 : Λ.evaluate (Λ.linkAssemble τ k hΛ (1, V))
        ⟨p.1.base, p.1.first⟩ = 1 := by
      apply hcrossValue
      · rw [linkBridge_plaquette_boundary_edgeSupport]; simp
      · exact hfirst
      · simpa [hfirst] using hbase
    have hc1 : Λ.evaluate (Λ.linkAssemble τ k hΛ (1, V))
        ⟨step p.1.base (.forward p.1.second), p.1.first⟩ = 1 := by
      apply hcrossValue
      · rw [linkBridge_plaquette_boundary_edgeSupport]; simp
      · exact hfirst
      · change step p.1.base (.forward p.1.second) τ = k
        rw [step_forward_apply]
        simp [Ne.symm hsecond, hbase]
    have hetopEq : etop =
        ⟨step p.1.base (.forward p.1.first), p.1.second⟩ := by
      simp [etop, linkCrossPositiveEdge, hfirst]
    have hbottomEq : etop.linkReflect τ k =
        ⟨p.1.base, p.1.second⟩ := by
      simpa [hfirst] using
        linkCrossPositiveEdge_linkReflect τ k p.1 hbase hperp
    rw [hc0, hc1]
    rw [← hetopEq, htop V.2, ← hbottomEq, hbottom]
    simp
  · have hsecond : p.1.second = τ := hperp.resolve_left hfirst
    have hc0 : Λ.evaluate (Λ.linkAssemble τ k hΛ (1, V))
        ⟨p.1.base, p.1.second⟩ = 1 := by
      apply hcrossValue
      · rw [linkBridge_plaquette_boundary_edgeSupport]; simp
      · exact hsecond
      · simpa [hsecond] using hbase
    have hc1 : Λ.evaluate (Λ.linkAssemble τ k hΛ (1, V))
        ⟨step p.1.base (.forward p.1.first), p.1.second⟩ = 1 := by
      apply hcrossValue
      · rw [linkBridge_plaquette_boundary_edgeSupport]; simp
      · exact hsecond
      · change step p.1.base (.forward p.1.first) τ = k
        rw [step_forward_apply]
        simp [Ne.symm hfirst, hbase]
    have hetopEq : etop =
        ⟨step p.1.base (.forward p.1.second), p.1.first⟩ := by
      simp [etop, linkCrossPositiveEdge, hfirst, hsecond]
    have hbottomEq : etop.linkReflect τ k =
        ⟨p.1.base, p.1.first⟩ := by
      simpa [hfirst] using
        linkCrossPositiveEdge_linkReflect τ k p.1 hbase hperp
    rw [hc0, hc1]
    rw [← hbottomEq, hbottom, ← hetopEq, htop V.2]
    simp only [one_mul, inv_one, mul_one]
    calc
      ρ.wilsonPotential (V.1 et * (V.2 et)⁻¹) =
          ρ.wilsonPotential ((V.1 et * (V.2 et)⁻¹)⁻¹) :=
        (ρ.wilsonPotential.inv_invariant _).symm
      _ = ρ.wilsonPotential (V.2 et * (V.1 et)⁻¹) := by simp

/-- After crossing-link gauge fixing, the concrete Wilson action is exactly
the two-side action plus the finite cross-plane kernel used by the Taylor
expansion. -/
theorem action_linkAssemble_fixed
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n)
    (V : LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
      LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k)) :
    FiniteVolume.action Λ ρ.wilsonPotential
        (Λ.linkAssemble τ k hΛ (1, V)) =
      (Λ.linkWilsonDecomposition τ k hΛ ρ).gaugeFixedAction V := by
  let f : Plaquette d → ℝ := fun p =>
    ρ.wilsonPotential (FiniteVolume.plaquetteHolonomy Λ
      (Λ.linkAssemble τ k hΛ (1, V)) p)
  let fplus : Plaquette d → ℝ := fun p =>
    ρ.wilsonPotential
      (holonomy (Λ.linkEvaluateSide τ k hΛ V.2) p.boundary)
  let fminus : Plaquette d → ℝ := fun p =>
    ρ.wilsonPotential
      (holonomy (Λ.linkEvaluateSide τ k hΛ V.1) p.boundary)
  change (∑ p ∈ Λ.activePlaquettes, f p) = _
  have hsplit : (∑ p ∈ Λ.activePlaquettes, f p) =
      (∑ p ∈ Λ.linkCrossPlaquettes τ k, f p) +
      (∑ p ∈ Λ.linkPositivePlaquettes τ k, f p) +
      ∑ p ∈ Λ.linkPositivePlaquettes τ k, f (p.linkReflect τ k) := by
    have hnegative : (∑ p ∈ Λ.linkNegativePlaquettes τ k, f p) =
        ∑ p ∈ Λ.linkPositivePlaquettes τ k, f (p.linkReflect τ k) := by
      change (∑ p ∈ (Λ.linkPositivePlaquettes τ k).map
          (Plaquette.linkReflectionEquiv τ k).toEmbedding, f p) = _
      rw [Finset.sum_map]
      rfl
    rw [Λ.activePlaquettes_eq_linkReflection_union τ k hΛ,
      Finset.sum_union (Λ.linkCrossPlaquettes_disjoint_linkSides τ k hΛ),
      Finset.sum_union
        (Λ.linkPositivePlaquettes_disjoint_linkNegativePlaquettes τ k hΛ),
      hnegative, add_assoc]
  rw [hsplit]
  have hplus : (∑ p ∈ Λ.linkPositivePlaquettes τ k, f p) =
      ∑ p ∈ Λ.linkPositivePlaquettes τ k, fplus p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact congrArg ρ.wilsonPotential
      (Λ.plaquetteHolonomy_linkAssemble_fixed_eq_side τ k hΛ hclosed V p hp)
  have hminus : (∑ p ∈ Λ.linkPositivePlaquettes τ k,
      f (p.linkReflect τ k)) =
      ∑ p ∈ Λ.linkPositivePlaquettes τ k, fminus p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact Λ.plaquetteTerm_linkReflect_fixed τ k hΛ hclosed ρ V p hp
  have hcross : (∑ p ∈ Λ.linkCrossPlaquettes τ k, f p) =
      ∑ p : Λ.linkCrossPlaquettes τ k,
        ρ.wilsonPotential
          ((Λ.linkCrossHolonomy τ k hΛ p) V.2 *
            ((Λ.linkCrossHolonomy τ k hΛ p) V.1)⁻¹) := by
    rw [← Finset.sum_attach]
    apply Finset.sum_congr Finset.attach_eq_univ
    intro p _hp
    exact Λ.wilsonPotential_crossPlaquette_linkAssemble_fixed
      τ k hΛ hclosed ρ V p
  rw [hplus, hminus, hcross]
  unfold linkWilsonDecomposition
  simp only [LinkReflection.WilsonActionDecomposition.gaugeFixedAction,
    linkPositiveWilsonAction, ContinuousMap.coe_mk, linkCrossHolonomy]
  ring

/-- A full one-sided gauge transformation removes the crossing field from
the concrete Wilson action.  `PlaquetteClosed` is exactly the hypothesis
needed to compare the transformed full configuration with the fixed
dynamic configuration on every edge read by an active plaquette. -/
theorem action_linkAssemble_eq_fixed
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n)
    (U : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k)) :
    FiniteVolume.action Λ ρ.wilsonPotential
        (Λ.linkAssemble τ k hΛ U) =
      FiniteVolume.action Λ ρ.wilsonPotential
        (Λ.linkAssemble τ k hΛ
          (1, (U.2.1, (Λ.linkCrossingGaugeFix τ k).fixSide U.1 U.2.2))) := by
  unfold FiniteVolume.action FiniteVolume.plaquetteHolonomy
  apply Finset.sum_congr rfl
  intro p hp
  let g := Λ.linkCrossingGaugeTransformation τ k U.1
  let A := Λ.evaluate (Λ.linkAssemble τ k hΛ U)
  let B := Λ.evaluate (Λ.linkAssemble τ k hΛ
    (1, (U.2.1, (Λ.linkCrossingGaugeFix τ k).fixSide U.1 U.2.2)))
  have hAB : holonomy (gaugeTransform g A) p.boundary =
      holonomy B p.boundary := by
    apply holonomy_eq_of_eqOn_edgeSupport
    intro e he
    exact Λ.gaugeTransform_linkAssemble_eq_fixed_on_dynamic τ k hΛ U
      ⟨e, hclosed p hp he⟩
  calc
    ρ.wilsonPotential (holonomy A p.boundary) =
        ρ.wilsonPotential
          (g p.base * holonomy A p.boundary * (g p.base)⁻¹) :=
      (ρ.wilsonPotential.conj_invariant (g p.base)
        (holonomy A p.boundary)).symm
    _ = ρ.wilsonPotential (holonomy (gaugeTransform g A) p.boundary) := by
      rw [holonomy_loop_gaugeTransform]
    _ = ρ.wilsonPotential (holonomy B p.boundary) := by rw [hAB]

/-- Restrict a full-lattice observable to the crossing and strict-positive
variables of a link-symmetric finite specification. -/
def linkRestrictObservable (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.LinkSymmetric τ k)
    (F : LocalObservable d G) :
    LinkReflection.WilsonActionDecomposition.PositiveObservable G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k) :=
  F.toContinuousMap.comp (Λ.linkEvaluatePositive τ k hΛ)

omit [IsTopologicalGroup G] in
/-- A dynamic edge in the link-positive algebra is either a crossing edge
or a strict positive-side edge. -/
theorem mem_linkCrossingEdges_or_linkPositiveEdges_of_target_gt
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) (hedyn : e ∈ Λ.dynamicEdges)
    (htarget : k < e.target τ) :
    e ∈ Λ.linkCrossingEdges τ k ∨ e ∈ Λ.linkPositiveEdges τ k := by
  by_cases hcross : e ∈ Λ.linkCrossingEdges τ k
  · exact Or.inl hcross
  · right
    rw [linkPositiveEdges, Finset.mem_filter]
    refine ⟨hedyn, ?_⟩
    by_cases hdir : e.direction = τ
    · have ht : e.target τ = e.source τ + 1 := by
        rw [PositiveEdge.target, hdir]
        simp [step, SignedDirection.forward, SignedDirection.delta, unitVector]
      have hsource_ne : e.source τ ≠ k := by
        intro hs
        exact hcross (Finset.mem_filter.mpr ⟨hedyn, hdir, hs⟩)
      omega
    · rw [PositiveEdge.target] at htarget
      simpa [step, SignedDirection.forward, SignedDirection.delta, unitVector,
        Ne.symm hdir] using htarget

/-- A positive-half observable does not see the negative coordinates
discarded by `linkEvaluatePositive`. -/
theorem linkRestrictObservable_apply_assemble
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (F : LocalObservable d G)
    (hF : F.SupportedInLinkPositiveHalf τ k)
    (U : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k)) :
    F (Λ.evaluate (Λ.linkAssemble τ k hΛ U)) =
      Λ.linkRestrictObservable τ k hΛ F (U.1, U.2.2) := by
  apply F.dependsOn_support
  intro e he
  change Λ.evaluate (Λ.linkAssemble τ k hΛ U) e =
    Λ.evaluate (Λ.linkAssemble τ k hΛ (U.1, (1, U.2.2))) e
  by_cases hedyn : e ∈ Λ.dynamicEdges
  · rw [Λ.evaluate_of_mem _ e hedyn, Λ.evaluate_of_mem _ e hedyn]
    let edyn : Λ.dynamicEdges := ⟨e, hedyn⟩
    rcases Λ.mem_linkCrossingEdges_or_linkPositiveEdges_of_target_gt τ k e
        hedyn (hF e he) with hcross | hplus
    · have hlabel : Λ.linkEdgeLabelEquiv τ k hΛ edyn =
          Sum.inl (⟨e, hcross⟩ : Λ.linkCrossingEdges τ k) := by
        unfold linkEdgeLabelEquiv
        dsimp [edyn]
        rw [dif_pos hcross]
      simp only [linkAssemble, ContinuousMap.coe_mk]
      rw [hlabel]
    · have hlabel : Λ.linkEdgeLabelEquiv τ k hΛ edyn =
          Sum.inr (Sum.inr (⟨e, hplus⟩ : Λ.linkPositiveEdges τ k)) := by
        unfold linkEdgeLabelEquiv
        dsimp [edyn]
        rw [dif_neg, dif_pos hplus]
        intro hcross
        have hs := (Finset.mem_filter.mp hplus).2
        have hs' := (Finset.mem_filter.mp hcross).2.2
        omega
      simp only [linkAssemble, ContinuousMap.coe_mk]
      rw [hlabel]
  · rw [Λ.evaluate_of_not_mem _ e hedyn, Λ.evaluate_of_not_mem _ e hedyn]

/-- Reflection preserves containment of an observable support in the dynamic
edge set of a link-symmetric specification. -/
theorem linkTheta_support_subset_dynamic
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (F : LocalObservable d G)
    (hF : F.support ⊆ Λ.dynamicEdges) :
    (F.linkTheta τ k).support ⊆ Λ.dynamicEdges := by
  intro e he
  change e ∈ F.support.image (PositiveEdge.linkReflect τ k) at he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  exact (hΛ.1 a).mp (hF ha)

/-- Gauge invariance replaces an assembled crossing field by the identity
for any observable whose recorded support is dynamic. -/
theorem gaugeInvariant_linkAssemble_eq_fixed
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (F : LocalObservable d G)
    (hGauge : IsGaugeInvariant F) (hF : F.support ⊆ Λ.dynamicEdges)
    (U : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k)) :
    F (Λ.evaluate (Λ.linkAssemble τ k hΛ U)) =
      F (Λ.evaluate (Λ.linkAssemble τ k hΛ
        (1, (U.2.1, (Λ.linkCrossingGaugeFix τ k).fixSide U.1 U.2.2)))) := by
  let g := Λ.linkCrossingGaugeTransformation τ k U.1
  let A := Λ.evaluate (Λ.linkAssemble τ k hΛ U)
  rw [← hGauge g A]
  apply F.dependsOn_support
  intro e he
  exact Λ.gaugeTransform_linkAssemble_eq_fixed_on_dynamic τ k hΛ U
    ⟨e, hF he⟩

/-- After the one-sided crossing gauge fix, the concrete reflected product
is the gauge-fixed two-side Gram integrand used by the Taylor expansion. -/
theorem linkReflectionProduct_assemble_eq_fixed
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (F H : LocalObservable d G)
    (hFhalf : F.SupportedInLinkPositiveHalf τ k)
    (hHhalf : H.SupportedInLinkPositiveHalf τ k)
    (hFgauge : IsGaugeInvariant F) (hHgauge : IsGaugeInvariant H)
    (hFdyn : F.support ⊆ Λ.dynamicEdges)
    (hHdyn : H.support ⊆ Λ.dynamicEdges)
    (U : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k)) :
    F.linkReflectionProduct τ k H
        (Λ.evaluate (Λ.linkAssemble τ k hΛ U)) =
      star (Λ.linkRestrictObservable τ k hΛ F (1, U.2.1)) *
        Λ.linkRestrictObservable τ k hΛ H
          (1, (Λ.linkCrossingGaugeFix τ k).fixSide U.1 U.2.2) := by
  let W : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k) :=
    (1, (U.2.1, (Λ.linkCrossingGaugeFix τ k).fixSide U.1 U.2.2))
  have htheta := Λ.gaugeInvariant_linkAssemble_eq_fixed τ k hΛ
    (F.linkTheta τ k)
    (LocalObservable.IsGaugeInvariant.linkTheta hFgauge τ k)
    (Λ.linkTheta_support_subset_dynamic τ k hΛ F hFdyn) U
  have hright := Λ.gaugeInvariant_linkAssemble_eq_fixed τ k hΛ H
    hHgauge hHdyn U
  change (F.linkTheta τ k)
      (Λ.evaluate (Λ.linkAssemble τ k hΛ U)) *
        H (Λ.evaluate (Λ.linkAssemble τ k hΛ U)) = _
  rw [htheta, hright]
  change star (F (linkReflectConfiguration τ k
      (Λ.evaluate (Λ.linkAssemble τ k hΛ W)))) *
        H (Λ.evaluate (Λ.linkAssemble τ k hΛ W)) = _
  rw [← Λ.linkAssemble_reflect τ k hΛ W]
  rw [Λ.linkRestrictObservable_apply_assemble τ k hΛ F hFhalf
      (LinkReflection.reflect W),
    Λ.linkRestrictObservable_apply_assemble τ k hΛ H hHhalf W]
  have hinvOne : LinkReflection.invertCrossing
      (1 : LinkReflection.CrossingConfiguration G
        (Λ.linkCrossingEdges τ k)) = 1 := by
    funext e
    simp [LinkReflection.invertCrossing]
  simp [W, LinkReflection.reflect, hinvOne]

end Topology

section Haar

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G]

/-- The crossing/two-side assembly preserves product Haar. -/
theorem measurePreserving_linkAssemble (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.LinkSymmetric τ k) :
    MeasurePreserving (Λ.linkAssemble τ k hΛ)
      (LinkReflection.WilsonActionDecomposition.reflectedHaar (G := G)
        (C := Λ.linkCrossingEdges τ k) (P := Λ.linkPositiveEdges τ k))
      Λ.haarMeasure := by
  let Label := (Λ.linkCrossingEdges τ k) ⊕
    ((Λ.linkPositiveEdges τ k) ⊕ (Λ.linkPositiveEdges τ k))
  let E := Λ.linkEdgeLabelEquiv τ k hΛ
  let R := ProductHaar.reindexEquiv (G := G) E.symm
  have hR := ProductHaar.measurePreserving_reindex (G := G) E.symm
  let I : (Label → G) → (Label → G) := fun V label =>
    match label with
    | Sum.inr (Sum.inl p) => if p.1.direction = τ then (V label)⁻¹ else V label
    | _ => V label
  have hI : MeasurePreserving I (ProductHaar.measure G Label)
      (ProductHaar.measure G Label) := by
    let f : Label → G → G := fun label x => match label with
      | Sum.inr (Sum.inl p) => if p.1.direction = τ then x⁻¹ else x
      | _ => x
    have hf : ∀ label, MeasurePreserving (f label)
        (GaugeHaarProbability.haar G) (GaugeHaarProbability.haar G) := by
      intro label
      rcases label with c | p
      · exact MeasurePreserving.id _
      · rcases p with p | p
        · by_cases hdir : p.1.direction = τ
          · simpa [f, hdir] using
              GaugeHaarProbability.measurePreserving_inv (G := G)
          · simpa [f, hdir] using
              (MeasurePreserving.id (GaugeHaarProbability.haar G))
        · exact MeasurePreserving.id _
    simpa only [ProductHaar.measure] using
      ProductHaar.measurePreserving_coordinatewise
        (G := G) (fun _ => GaugeHaarProbability.haar G) f hf
  let Eouter := MeasurableEquiv.sumPiEquivProdPi (fun _ : Label => G)
  let Esides := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : (Λ.linkPositiveEdges τ k) ⊕
      (Λ.linkPositiveEdges τ k) => G)
  let J : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k) → (Label → G) :=
    fun U => Eouter.symm (U.1, Esides.symm U.2)
  have hJ : MeasurePreserving J
      (LinkReflection.WilsonActionDecomposition.reflectedHaar (G := G)
        (C := Λ.linkCrossingEdges τ k) (P := Λ.linkPositiveEdges τ k))
      (ProductHaar.measure G Label) := by
    exact (MeasureTheory.measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Label => GaugeHaarProbability.haar G)).comp
      (MeasurePreserving.prod (MeasurePreserving.id _)
        (MeasureTheory.measurePreserving_sumPiEquivProdPi_symm
          (fun _ : (Λ.linkPositiveEdges τ k) ⊕
            (Λ.linkPositiveEdges τ k) => GaugeHaarProbability.haar G)))
  have hcomp := hR.comp (hI.comp hJ)
  refine ⟨(Λ.linkAssemble τ k hΛ).continuous.measurable, ?_⟩
  have heq : (Λ.linkAssemble τ k hΛ : _ → _) = R ∘ I ∘ J := by
    funext U e
    let label := E e
    generalize hlabel : E e = label
    rcases label with c | p
    · unfold linkAssemble
      simp only [ContinuousMap.coe_mk, Function.comp_apply]
      rw [hlabel]
      rw [show R (I (J U)) e = (I (J U)) (E e) by
        exact ProductHaar.reindex_apply E.symm (I (J U)) e]
      change U.1 c = (I (J U)) (E e)
      rw [hlabel]
      rfl
    · rcases p with p | p
      · unfold linkAssemble
        simp only [ContinuousMap.coe_mk, Function.comp_apply]
        rw [hlabel]
        rw [show R (I (J U)) e = (I (J U)) (E e) by
          exact ProductHaar.reindex_apply E.symm (I (J U)) e]
        change (if p.1.direction = τ then (U.2.1 p)⁻¹ else U.2.1 p) =
          (I (J U)) (E e)
        rw [hlabel]
        rfl
      · unfold linkAssemble
        simp only [ContinuousMap.coe_mk, Function.comp_apply]
        rw [hlabel]
        rw [show R (I (J U)) e = (I (J U)) (E e) by
          exact ProductHaar.reindex_apply E.symm (I (J U)) e]
        change U.2.2 p = (I (J U)) (E e)
        rw [hlabel]
        rfl
  rw [heq]
  exact hcomp.map_eq

/-- At fixed crossing field, the concrete one-sided gauge fix and Haar
invariance reduce the two side integrals to the Taylor/Fubini pairing. -/
theorem integral_linkSides_eq_gaugeFixed
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) (β : ℝ)
    (F H : LocalObservable d G)
    (hFhalf : F.SupportedInLinkPositiveHalf τ k)
    (hHhalf : H.SupportedInLinkPositiveHalf τ k)
    (hFgauge : IsGaugeInvariant F) (hHgauge : IsGaugeInvariant H)
    (hFdyn : F.support ⊆ Λ.dynamicEdges)
    (hHdyn : H.support ⊆ Λ.dynamicEdges)
    (Ucross : LinkReflection.CrossingConfiguration G
      (Λ.linkCrossingEdges τ k)) :
    (∫ V : LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
        LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k),
      (Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential
        (Λ.linkAssemble τ k hΛ (Ucross, V))) : ℂ) *
        F.linkReflectionProduct τ k H
          (Λ.evaluate (Λ.linkAssemble τ k hΛ (Ucross, V)))
      ∂(LinkReflection.WilsonActionDecomposition.sideHaar
          (G := G) (P := Λ.linkPositiveEdges τ k)).prod
        (LinkReflection.WilsonActionDecomposition.sideHaar
          (G := G) (P := Λ.linkPositiveEdges τ k))) =
      (Λ.linkWilsonDecomposition τ k hΛ ρ).gaugeFixedPairing β
        (Λ.linkRestrictObservable τ k hΛ F)
        (Λ.linkRestrictObservable τ k hΛ H) := by
  let D := Λ.linkWilsonDecomposition τ k hΛ ρ
  let sideMeasure := LinkReflection.WilsonActionDecomposition.sideHaar
    (G := G) (P := Λ.linkPositiveEdges τ k)
  let Eplus := (Λ.linkCrossingGaugeFix τ k).fixSideEquiv Ucross
  let E : (LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
      LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k)) ≃ᵐ
      (LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
      LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k)) :=
    (MeasurableEquiv.refl _).prodCongr Eplus
  have hE : MeasurePreserving E (sideMeasure.prod sideMeasure)
      (sideMeasure.prod sideMeasure) :=
    MeasurePreserving.prod (MeasurePreserving.id _)
      ((Λ.linkCrossingGaugeFix τ k).measurePreserving_fixSideEquiv Ucross)
  let K : LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) ×
      LinkReflection.SideConfiguration G (Λ.linkPositiveEdges τ k) → ℂ :=
    fun W => (Real.exp (β * D.gaugeFixedAction W) : ℂ) *
      star (Λ.linkRestrictObservable τ k hΛ F (1, W.1)) *
        Λ.linkRestrictObservable τ k hΛ H (1, W.2)
  have hpoint : ∀ V, (Real.exp (β * FiniteVolume.action Λ
        ρ.wilsonPotential (Λ.linkAssemble τ k hΛ (Ucross, V))) : ℂ) *
      F.linkReflectionProduct τ k H
        (Λ.evaluate (Λ.linkAssemble τ k hΛ (Ucross, V))) = K (E V) := by
    intro V
    rw [Λ.action_linkAssemble_eq_fixed τ k hΛ hclosed ρ (Ucross, V),
      Λ.action_linkAssemble_fixed τ k hΛ hclosed ρ
        (V.1, (Λ.linkCrossingGaugeFix τ k).fixSide Ucross V.2),
      Λ.linkReflectionProduct_assemble_eq_fixed τ k hΛ F H
        hFhalf hHhalf hFgauge hHgauge hFdyn hHdyn (Ucross, V)]
    have hEV : E V =
        (V.1, (Λ.linkCrossingGaugeFix τ k).fixSide Ucross V.2) := rfl
    rw [hEV]
    simp [K, D]
    ring
  simp_rw [hpoint]
  change (∫ V, K (E V) ∂sideMeasure.prod sideMeasure) = _
  rw [hE.integral_comp' K]
  rfl

/-- The unnormalized concrete finite-volume reflected integral is exactly
the gauge-fixed Taylor/Fubini pairing. -/
theorem integral_haar_linkReflectionProduct_eq_gaugeFixed
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) (β : ℝ)
    (F H : LocalObservable d G)
    (hFhalf : F.SupportedInLinkPositiveHalf τ k)
    (hHhalf : H.SupportedInLinkPositiveHalf τ k)
    (hFgauge : IsGaugeInvariant F) (hHgauge : IsGaugeInvariant H)
    (hFdyn : F.support ⊆ Λ.dynamicEdges)
    (hHdyn : H.support ⊆ Λ.dynamicEdges) :
    (∫ V, (Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential V) : ℂ) *
        F.linkReflectionProduct τ k H (Λ.evaluate V) ∂Λ.haarMeasure) =
      (Λ.linkWilsonDecomposition τ k hΛ ρ).gaugeFixedPairing β
        (Λ.linkRestrictObservable τ k hΛ F)
        (Λ.linkRestrictObservable τ k hΛ H) := by
  let Kdyn : DynamicConfiguration Λ → ℂ := fun V =>
    (Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential V) : ℂ) *
      F.linkReflectionProduct τ k H (Λ.evaluate V)
  have hKdyn : Continuous Kdyn := by
    unfold Kdyn
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp
        (continuous_const.mul
          (FiniteVolume.continuous_action Λ ρ.wilsonPotential)))).mul
      ((F.linkReflectionProduct τ k H).toContinuousMap.continuous.comp
        Λ.continuous_evaluate)
  have hchange :
      (∫ U, Kdyn (Λ.linkAssemble τ k hΛ U)
          ∂LinkReflection.WilsonActionDecomposition.reflectedHaar) =
        ∫ V, Kdyn V ∂Λ.haarMeasure := by
    rw [← (Λ.measurePreserving_linkAssemble τ k hΛ).map_eq]
    exact (MeasureTheory.integral_map
      (Λ.linkAssemble τ k hΛ).continuous.measurable.aemeasurable
      hKdyn.measurable.aestronglyMeasurable).symm
  rw [← hchange]
  let Kref : LinkReflection.ReflectedConfiguration G
      (Λ.linkCrossingEdges τ k) (Λ.linkPositiveEdges τ k) → ℂ := fun U =>
    (Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential
      (Λ.linkAssemble τ k hΛ U)) : ℂ) *
      F.linkReflectionProduct τ k H
        (Λ.evaluate (Λ.linkAssemble τ k hΛ U))
  have hKref : Integrable Kref
      LinkReflection.WilsonActionDecomposition.reflectedHaar := by
    apply Continuous.integrable_of_hasCompactSupport _
      (HasCompactSupport.of_compactSpace _)
    unfold Kref
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp
        (continuous_const.mul
          ((FiniteVolume.continuous_action Λ ρ.wilsonPotential).comp
            (Λ.linkAssemble τ k hΛ).continuous)))).mul
      ((F.linkReflectionProduct τ k H).toContinuousMap.continuous.comp
        (Λ.continuous_evaluate.comp (Λ.linkAssemble τ k hΛ).continuous))
  change (∫ U, Kref U
    ∂LinkReflection.WilsonActionDecomposition.reflectedHaar) = _
  unfold LinkReflection.WilsonActionDecomposition.reflectedHaar
  rw [integral_prod _ hKref]
  simp only [Kref]
  simp_rw [Λ.integral_linkSides_eq_gaugeFixed τ k hΛ hclosed ρ β F H
    hFhalf hHhalf hFgauge hHgauge hFdyn hHdyn]
  simp

/-- The normalized concrete link-reflection pairing is the positive real
partition-function factor times the gauge-fixed Taylor/Fubini pairing. -/
theorem integral_gibbsMeasure_linkReflectionProduct_eq
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) (β : ℝ)
    (F H : LocalObservable d G)
    (hFhalf : F.SupportedInLinkPositiveHalf τ k)
    (hHhalf : H.SupportedInLinkPositiveHalf τ k)
    (hFgauge : IsGaugeInvariant F) (hHgauge : IsGaugeInvariant H)
    (hFdyn : F.support ⊆ Λ.dynamicEdges)
    (hHdyn : H.support ⊆ Λ.dynamicEdges) :
    (∫ V, F.linkReflectionProduct τ k H (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) =
      (FiniteVolume.partitionFunction Λ ρ.wilsonPotential β : ℂ)⁻¹ *
        (Λ.linkWilsonDecomposition τ k hΛ ρ).gaugeFixedPairing β
          (Λ.linkRestrictObservable τ k hΛ F)
          (Λ.linkRestrictObservable τ k hΛ H) := by
  rw [FiniteVolume.gibbsMeasure, integral_tilted]
  let Z := FiniteVolume.partitionFunction Λ ρ.wilsonPotential β
  change (∫ V, (Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential V) /
      Z : ℝ) • F.linkReflectionProduct τ k H (Λ.evaluate V)
      ∂Λ.haarMeasure) = _
  calc
    _ = ∫ V, (Z : ℂ)⁻¹ *
        ((Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential V) : ℂ) *
          F.linkReflectionProduct τ k H (Λ.evaluate V))
        ∂Λ.haarMeasure := by
      apply integral_congr_ae
      filter_upwards with V
      change ((Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential V) /
          Z : ℝ) : ℂ) *
            F.linkReflectionProduct τ k H (Λ.evaluate V) = _
      rw [Complex.ofReal_div, div_eq_mul_inv]
      ring
    _ = (Z : ℂ)⁻¹ *
        (Λ.linkWilsonDecomposition τ k hΛ ρ).gaugeFixedPairing β
          (Λ.linkRestrictObservable τ k hΛ F)
          (Λ.linkRestrictObservable τ k hΛ H) := by
      rw [integral_const_mul,
        Λ.integral_haar_linkReflectionProduct_eq_gaugeFixed τ k hΛ hclosed
          ρ β F H hFhalf hHhalf hFgauge hHgauge hFdyn hHdyn]

/-- Concrete finite-volume link-reflection positivity for gauge-invariant
positive-half observables. -/
theorem linkReflectionPositive_gibbsMeasure
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) {β : ℝ} (hβ : 0 ≤ β)
    (F : LocalObservable d G)
    (hFhalf : F.SupportedInLinkPositiveHalf τ k)
    (hFgauge : IsGaugeInvariant F)
    (hFdyn : F.support ⊆ Λ.dynamicEdges) :
    Complex.im (∫ V, F.linkReflectionProduct τ k F (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) = 0 ∧
      0 ≤ Complex.re (∫ V,
        F.linkReflectionProduct τ k F (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) := by
  rw [Λ.integral_gibbsMeasure_linkReflectionProduct_eq τ k hΛ hclosed
    ρ β F F hFhalf hFhalf hFgauge hFgauge hFdyn hFdyn]
  let D := Λ.linkWilsonDecomposition τ k hΛ ρ
  let F' := Λ.linkRestrictObservable τ k hΛ F
  have hpos : Complex.im (D.gaugeFixedPairing β F' F') = 0 ∧
      0 ≤ Complex.re (D.gaugeFixedPairing β F' F') := by
    rw [D.gaugeFixedPairing_eq_taylorPairing]
    exact D.taylorPairing_self_nonneg hβ F'
  have hZ := FiniteVolume.partitionFunction_pos Λ ρ.wilsonPotential β
  have hscale :
      ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β : ℂ)⁻¹) =
        ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ : ℝ) := by
    symm
    exact Complex.ofReal_inv _
  rw [hscale]
  change Complex.im
      (((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ : ℝ) *
        D.gaugeFixedPairing β F' F') = 0 ∧
    0 ≤ Complex.re
      (((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ : ℝ) *
        D.gaugeFixedPairing β F' F')
  constructor
  · rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [hpos.1, mul_zero]
  · rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr hZ.le) hpos.2

/-- Concrete finite-volume Cauchy--Schwarz for the link-reflection pairing. -/
theorem normSq_integral_gibbsMeasure_linkReflectionProduct_le
    {n : ℕ}
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.LinkSymmetric τ k) (hclosed : Λ.PlaquetteClosed)
    (ρ : Wilson.ContinuousUnitaryRepData G n) {β : ℝ} (hβ : 0 ≤ β)
    (F H : LocalObservable d G)
    (hFhalf : F.SupportedInLinkPositiveHalf τ k)
    (hHhalf : H.SupportedInLinkPositiveHalf τ k)
    (hFgauge : IsGaugeInvariant F) (hHgauge : IsGaugeInvariant H)
    (hFdyn : F.support ⊆ Λ.dynamicEdges)
    (hHdyn : H.support ⊆ Λ.dynamicEdges) :
    Complex.normSq (∫ V, F.linkReflectionProduct τ k H (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) ≤
      Complex.re (∫ V, F.linkReflectionProduct τ k F (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) *
      Complex.re (∫ V, H.linkReflectionProduct τ k H (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) := by
  rw [Λ.integral_gibbsMeasure_linkReflectionProduct_eq τ k hΛ hclosed
      ρ β F H hFhalf hHhalf hFgauge hHgauge hFdyn hHdyn,
    Λ.integral_gibbsMeasure_linkReflectionProduct_eq τ k hΛ hclosed
      ρ β F F hFhalf hFhalf hFgauge hFgauge hFdyn hFdyn,
    Λ.integral_gibbsMeasure_linkReflectionProduct_eq τ k hΛ hclosed
      ρ β H H hHhalf hHhalf hHgauge hHgauge hHdyn hHdyn]
  let D := Λ.linkWilsonDecomposition τ k hΛ ρ
  let F' := Λ.linkRestrictObservable τ k hΛ F
  let H' := Λ.linkRestrictObservable τ k hΛ H
  have hCS := D.normSq_gaugeFixedPairing_le hβ F' H'
  have hZ := FiniteVolume.partitionFunction_pos Λ ρ.wilsonPotential β
  have hscale :
      ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β : ℂ)⁻¹) =
        ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ : ℝ) := by
    symm
    exact Complex.ofReal_inv _
  rw [hscale]
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have hs : 0 ≤ (FiniteVolume.partitionFunction Λ
      ρ.wilsonPotential β)⁻¹ := inv_nonneg.mpr hZ.le
  calc
    (FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
        (FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
          Complex.normSq (D.gaugeFixedPairing β F' H') ≤
      (FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
        (FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
          (Complex.re (D.gaugeFixedPairing β F' F') *
            Complex.re (D.gaugeFixedPairing β H' H')) := by
      gcongr
    _ = ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
          Complex.re (D.gaugeFixedPairing β F' F')) *
        ((FiniteVolume.partitionFunction Λ ρ.wilsonPotential β)⁻¹ *
          Complex.re (D.gaugeFixedPairing β H' H')) := by ring

end Haar

end FiniteSpecification

end

end YangMills.Gauge
