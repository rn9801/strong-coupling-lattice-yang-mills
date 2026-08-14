/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.SiteReflectionPositivity
import YangMills.Gauge.InfiniteReflection

/-!
# Concrete finite-specification bridge for site reflection

This file identifies a finite specification whose dynamic edges, active
plaquettes, and exterior field are invariant under reflection through an
integer coordinate plane with the labelled site-reflection normal form.
-/

open MeasureTheory

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

local instance siteReflectionBridgeDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

namespace FiniteSpecification

variable {d : ℕ} {G : Type*} [Group G]

/-- The four positive edges in a plaquette boundary.  This local geometric
normal form keeps the finite gauge bridge independent of `StrongCoupling/`. -/
private theorem siteBridge_plaquette_boundary_edgeSupport (p : Plaquette d) :
    p.boundary.edgeSupport =
      { ⟨p.base, p.first⟩,
        ⟨step p.base (.forward p.first), p.second⟩,
        ⟨step p.base (.forward p.second), p.first⟩,
        ⟨p.base, p.second⟩ } := by
  have h₃ : p.base + unitVector p.first + unitVector p.second +
      -unitVector p.first = p.base + unitVector p.second := by abel
  simp only [Plaquette.boundary, Path.rectangleBoundary, SignedDirection.forward,
    Path.advance, step, SignedDirection.delta, SignedDirection.backward,
    Path.rectangleRaw, Path.straight, Nat.reduceAdd, edgeFrom, SignedEdge.toArrow,
    SignedEdge.target, h₃, Quiver.Path.comp_cons, Quiver.Path.comp_nil,
    Path.edgeSupport_castTarget, Path.edgeSupport_cons, SignedEdge.positive,
    add_neg_cancel_right, Path.edgeSupport_nil, insert_empty_eq]
  apply Finset.ext
  intro e
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- Dynamic edges based in the site-reflection plane.  Perpendicular edges
leave the plane and hence are assigned to a strict side instead. -/
def sitePlaneEdges (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ) :
    Finset (PositiveEdge d) :=
  Λ.dynamicEdges.filter fun e => e.source τ = k ∧ e.direction ≠ τ

/-- A choice of one representative from every strict-side reflected pair. -/
def sitePositiveEdges (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ) :
    Finset (PositiveEdge d) :=
  Λ.dynamicEdges.filter fun e => k ≤ e.source τ ∧
    ¬(e.source τ = k ∧ e.direction ≠ τ)

/-- Active plaquettes contained in the reflection plane. -/
def sitePlanePlaquettes (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ) :
    Finset (Plaquette d) :=
  Λ.activePlaquettes.filter fun p => p.base τ = k ∧
    p.first ≠ τ ∧ p.second ≠ τ

/-- A choice of one plaquette from every off-plane reflected pair. -/
def sitePositivePlaquettes (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ) :
    Finset (Plaquette d) :=
  Λ.activePlaquettes.filter fun p => k ≤ p.base τ ∧
    ¬(p.base τ = k ∧ p.first ≠ τ ∧ p.second ≠ τ)

/-- The reflected copy of the chosen strict positive plaquettes. -/
def siteNegativePlaquettes (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ) :
    Finset (Plaquette d) :=
  (Λ.sitePositivePlaquettes τ k).map
    (Plaquette.siteReflectionEquiv τ k).toEmbedding

/-- Reflection symmetry of the concrete finite specification, including the
frozen exterior field. -/
def SiteSymmetric (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ) : Prop :=
  (∀ e, e ∈ Λ.dynamicEdges ↔ e.siteReflect τ k ∈ Λ.dynamicEdges) ∧
    (∀ p, p ∈ Λ.activePlaquettes ↔ p.siteReflect τ k ∈ Λ.activePlaquettes) ∧
    siteReflectConfiguration τ k Λ.exterior = Λ.exterior

omit [Group G] in
theorem source_siteReflect_eq_of_direction_ne (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) (h : e.direction ≠ τ) :
    (e.siteReflect τ k).source = siteReflection τ k e.source := by
  simp [PositiveEdge.siteReflect, h]

omit [Group G] in
theorem source_siteReflect_eq_of_direction_eq (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) (h : e.direction = τ) :
    (e.siteReflect τ k).source τ = 2 * k - e.source τ - 1 := by
  subst τ
  simp only [PositiveEdge.siteReflect, if_pos, siteReflection_apply_eq]
  have htarget : e.target e.direction = e.source e.direction + 1 := by
    change e.source e.direction + unitVector e.direction e.direction = _
    simp [unitVector]
  rw [htarget]
  ring

omit [Group G] in
theorem siteReflect_endpoints (τ : Fin d) (k : ℤ) (e : PositiveEdge d) :
    ((e.siteReflect τ k).source = siteReflection τ k e.source ∧
        (e.siteReflect τ k).target = siteReflection τ k e.target) ∨
      ((e.siteReflect τ k).source = siteReflection τ k e.target ∧
        (e.siteReflect τ k).target = siteReflection τ k e.source) := by
  by_cases hdir : e.direction = τ
  · right
    constructor
    · simp [PositiveEdge.siteReflect, hdir]
    · rw [PositiveEdge.siteReflect, if_pos hdir]
      change step (siteReflection τ k e.target) (.forward e.direction) =
        siteReflection τ k e.source
      rw [hdir]
      rw [show e.target = step e.source (.forward τ) by
        rw [PositiveEdge.target, hdir]]
      rw [siteReflection_step]
      simp only [SignedDirection.siteReflect, SignedDirection.forward, if_true]
      exact step_reverse (siteReflection τ k e.source) (.backward τ)
  · left
    constructor
    · exact source_siteReflect_eq_of_direction_ne τ k e hdir
    · simp only [PositiveEdge.target]
      rw [source_siteReflect_eq_of_direction_ne τ k e hdir]
      rw [PositiveEdge.direction_siteReflect]
      have hs := siteReflection_step τ k e.source (.forward e.direction)
      rw [hs]
      congr 1
      simp only [SignedDirection.siteReflect, SignedDirection.forward]
      simp [hdir]

omit [Group G] in
@[simp]
theorem siteReflection_step_forward_eq (τ : Fin d) (k : ℤ) (x : Site d) :
    siteReflection τ k (step x (.forward τ)) =
      step (siteReflection τ k x) (.backward τ) := by
  rw [siteReflection_step]
  congr 1
  change SignedDirection.mk τ
      (if τ = τ then Orientation.forward.reverse else Orientation.forward) =
    SignedDirection.mk τ Orientation.backward
  simp

omit [Group G] in
theorem siteReflection_step_forward_ne (τ : Fin d) (k : ℤ) (x : Site d)
    {i : Fin d} (hi : i ≠ τ) :
    siteReflection τ k (step x (.forward i)) =
      step (siteReflection τ k x) (.forward i) := by
  rw [siteReflection_step]
  congr 1
  change SignedDirection.mk i
      (if i = τ then Orientation.forward.reverse else Orientation.forward) =
    SignedDirection.mk i Orientation.forward
  simp [hi]

omit [Group G] in
@[simp]
theorem siteReflect_forward_eq (τ : Fin d) :
    (SignedDirection.forward τ).siteReflect τ = .backward τ := by
  change SignedDirection.mk τ
      (if τ = τ then Orientation.forward.reverse else Orientation.forward) =
    SignedDirection.mk τ Orientation.backward
  simp

omit [Group G] in
theorem step_backward_forward (x : Site d) (τ : Fin d) :
    step (step x (.backward τ)) (.forward τ) = x :=
  step_reverse x (.backward τ)

omit [Group G] in
theorem step_forward_comm (x : Site d) (i j : Fin d) :
    step (step x (.forward i)) (.forward j) =
      step (step x (.forward j)) (.forward i) := by
  simp only [step, SignedDirection.delta_forward]
  abel

omit [Group G] in
theorem step_backward_forward_comm (x : Site d) (τ : Fin d)
    {i : Fin d} :
    step (step x (.forward i)) (.backward τ) =
      step (step x (.backward τ)) (.forward i) := by
  simp only [step, SignedDirection.delta_forward, SignedDirection.delta_backward]
  abel

omit [Group G] in
theorem siteReflect_mem_plaquette_boundary_of_mem (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) (p : Plaquette d)
    (he : e ∈ p.boundary.edgeSupport) :
    e.siteReflect τ k ∈ (p.siteReflect τ k).boundary.edgeSupport := by
  rw [siteBridge_plaquette_boundary_edgeSupport] at he ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
  rcases p with ⟨x, i, j, hij⟩
  by_cases hi : i = τ
  · subst i
    have hj : j ≠ τ := fun h => hij h.symm
    simp only [Plaquette.siteReflect, true_or, if_pos]
    rcases he with rfl | rfl | rfl | rfl
    · exact Or.inl <| by
        simp only [PositiveEdge.siteReflect, if_pos, PositiveEdge.target]
        congr 1
        exact siteReflection_step_forward_eq τ k x
    · exact Or.inr <| Or.inr <| Or.inr <| by
        simp only [PositiveEdge.siteReflect, hj, if_false]
        congr 1
        exact siteReflection_step_forward_eq τ k x
    · exact Or.inr <| Or.inr <| Or.inl <| by
        simp only [PositiveEdge.siteReflect, if_pos, PositiveEdge.target,
          siteReflection_step_forward_ne τ k x hj,
          siteReflection_step_forward_eq]
        congr 1
        exact step_backward_forward_comm (siteReflection τ k x) τ
    · exact Or.inr <| Or.inl <| by
        simp only [PositiveEdge.siteReflect, hj, if_false, step_backward_forward]
  · by_cases hj : j = τ
    · subst j
      simp only [Plaquette.siteReflect, or_true, if_pos]
      rcases he with rfl | rfl | rfl | rfl
      · exact Or.inr <| Or.inr <| Or.inl <| by
          simp only [PositiveEdge.siteReflect, hi, if_false, step_backward_forward]
      · exact Or.inr <| Or.inl <| by
          simp only [PositiveEdge.siteReflect, if_pos, PositiveEdge.target,
            siteReflection_step_forward_ne τ k x hi,
            siteReflection_step_forward_eq]
          congr 1
          exact step_backward_forward_comm (siteReflection τ k x) τ
      · exact Or.inl <| by
          simp only [PositiveEdge.siteReflect, hi, if_false]
          congr 1
          exact siteReflection_step_forward_eq τ k x
      · exact Or.inr <| Or.inr <| Or.inr <| by
          simp only [PositiveEdge.siteReflect, if_pos, PositiveEdge.target,
            siteReflection_step_forward_eq]
    · simp only [Plaquette.siteReflect, hi, hj, or_false]
      rcases he with rfl | rfl | rfl | rfl
      · exact Or.inl <| by simp [PositiveEdge.siteReflect, hi]
      · exact Or.inr <| Or.inl <| by
          simp [PositiveEdge.siteReflect, hj,
            siteReflection_step_forward_ne τ k x hi]
      · exact Or.inr <| Or.inr <| Or.inl <| by
          simp [PositiveEdge.siteReflect, hi,
            siteReflection_step_forward_ne τ k x hj]
      · exact Or.inr <| Or.inr <| Or.inr <| by
          simp [PositiveEdge.siteReflect, hj]

omit [Group G] in
theorem siteReflect_mem_plaquette_boundary_iff (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) (p : Plaquette d) :
    e.siteReflect τ k ∈ (p.siteReflect τ k).boundary.edgeSupport ↔
      e ∈ p.boundary.edgeSupport := by
  constructor
  · intro he
    have href := siteReflect_mem_plaquette_boundary_of_mem τ k
      (e.siteReflect τ k) (p.siteReflect τ k) he
    rw [PositiveEdge.siteReflect_siteReflect,
      Plaquette.siteReflect_siteReflect] at href
    exact href
  · exact siteReflect_mem_plaquette_boundary_of_mem τ k e p

theorem siteReflect_mem_sitePlaneEdges_iff (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.SiteSymmetric τ k) (e : PositiveEdge d) :
    e.siteReflect τ k ∈ Λ.sitePlaneEdges τ k ↔ e ∈ Λ.sitePlaneEdges τ k := by
  simp only [sitePlaneEdges, Finset.mem_filter]
  constructor
  · rintro ⟨he, hsource, hdir⟩
    have he' := (hΛ.1 e).mpr he
    have hdir' : e.direction ≠ τ := by simpa using hdir
    have hsource' : e.source τ = k := by
      rw [source_siteReflect_eq_of_direction_ne τ k e hdir',
        siteReflection_apply_eq] at hsource
      omega
    exact ⟨he', hsource', hdir'⟩
  · rintro ⟨he, hsource, hdir⟩
    have he' := (hΛ.1 e).mp he
    have hsource' : (e.siteReflect τ k).source τ = k := by
      rw [source_siteReflect_eq_of_direction_ne τ k e hdir,
        siteReflection_apply_eq, hsource]
      omega
    exact ⟨he', hsource', by simpa using hdir⟩

omit [Group G] in
theorem siteReflect_not_mem_sitePositiveEdges (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (e : Λ.sitePositiveEdges τ k) :
    e.1.siteReflect τ k ∉ Λ.sitePositiveEdges τ k := by
  intro href
  have he := (Finset.mem_filter.mp e.2).2
  have hrefside := (Finset.mem_filter.mp href).2.1
  by_cases hdir : e.1.direction = τ
  · rw [source_siteReflect_eq_of_direction_eq τ k e.1 hdir] at hrefside
    omega
  · have hesource : k < e.1.source τ := by
      rcases he with ⟨hside, hnotplane⟩
      have hne : e.1.source τ ≠ k := fun heq => hnotplane ⟨heq, hdir⟩
      omega
    rw [source_siteReflect_eq_of_direction_ne τ k e.1 hdir,
      siteReflection_apply_eq] at hrefside
    omega

/-- The geometric inverse of the three-way site-reflection edge labeling. -/
def siteEdgeLabelInv (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) :
    SiteReflection.ReflectedLabel
        (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k) →
      Λ.dynamicEdges
  | Sum.inl e => ⟨e.1, (Finset.mem_filter.mp e.2).1⟩
  | Sum.inr (Sum.inl e) =>
      ⟨e.1.siteReflect τ k,
        (hΛ.1 e.1).mp (Finset.mem_filter.mp e.2).1⟩
  | Sum.inr (Sum.inr e) => ⟨e.1, (Finset.mem_filter.mp e.2).1⟩

@[simp]
theorem siteEdgeLabelInv_plane (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.SiteSymmetric τ k)
    (e : Λ.sitePlaneEdges τ k) :
    Λ.siteEdgeLabelInv τ k hΛ (Sum.inl e) =
      ⟨e.1, (Finset.mem_filter.mp e.2).1⟩ := rfl

@[simp]
theorem siteEdgeLabelInv_negative (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.SiteSymmetric τ k)
    (e : Λ.sitePositiveEdges τ k) :
    Λ.siteEdgeLabelInv τ k hΛ (Sum.inr (Sum.inl e)) =
      ⟨e.1.siteReflect τ k,
        (hΛ.1 e.1).mp (Finset.mem_filter.mp e.2).1⟩ := rfl

@[simp]
theorem siteEdgeLabelInv_negative_val (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.SiteSymmetric τ k)
    (e : Λ.sitePositiveEdges τ k) :
    (Λ.siteEdgeLabelInv τ k hΛ (Sum.inr (Sum.inl e))).1 =
      e.1.siteReflect τ k := rfl

@[simp]
theorem siteEdgeLabelInv_positive (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.SiteSymmetric τ k)
    (e : Λ.sitePositiveEdges τ k) :
    Λ.siteEdgeLabelInv τ k hΛ (Sum.inr (Sum.inr e)) =
      ⟨e.1, (Finset.mem_filter.mp e.2).1⟩ := rfl

/-- Every dynamic edge is uniquely a plane edge, a chosen positive-side edge,
or the reflection of a chosen positive-side edge. -/
def siteEdgeLabelEquiv (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) :
    Λ.dynamicEdges ≃ SiteReflection.ReflectedLabel
      (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k) where
  toFun e := by
    if hplane : e.1 ∈ Λ.sitePlaneEdges τ k then
      exact Sum.inl ⟨e.1, hplane⟩
    else if hplus : e.1 ∈ Λ.sitePositiveEdges τ k then
      exact Sum.inr (Sum.inr ⟨e.1, hplus⟩)
    else
      refine Sum.inr (Sum.inl ⟨e.1.siteReflect τ k, ?_⟩)
      rw [sitePositiveEdges, Finset.mem_filter]
      have hesym : e.1.siteReflect τ k ∈ Λ.dynamicEdges := (hΛ.1 e.1).mp e.2
      refine ⟨hesym, ?_⟩
      rw [sitePositiveEdges, Finset.mem_filter] at hplus
      by_cases hdir : e.1.direction = τ
      · have hsource : e.1.source τ < k := by
          by_contra hn
          have hle : k ≤ e.1.source τ := le_of_not_gt hn
          exact hplus ⟨e.2, hle, fun hp => hp.2 hdir⟩
        constructor
        · rw [source_siteReflect_eq_of_direction_eq τ k e.1 hdir]
          omega
        · intro hp
          exact hp.2 (by simpa using hdir)
      · have hsource : e.1.source τ < k := by
          by_contra hn
          have hle : k ≤ e.1.source τ := le_of_not_gt hn
          exact hplus ⟨e.2, hle, fun hp => hplane <|
            Finset.mem_filter.mpr ⟨e.2, hp.1, hp.2⟩⟩
        constructor
        · rw [source_siteReflect_eq_of_direction_ne τ k e.1 hdir,
            siteReflection_apply_eq]
          omega
        · intro hp
          have : e.1.source τ = k := by
            rw [source_siteReflect_eq_of_direction_ne τ k e.1 hdir,
              siteReflection_apply_eq] at hp
            omega
          omega
  invFun := Λ.siteEdgeLabelInv τ k hΛ
  left_inv e := by
    dsimp
    split_ifs with hplane hplus
    · rfl
    · rfl
    · apply Subtype.ext
      change (Λ.siteEdgeLabelInv τ k hΛ
        (Sum.inr (Sum.inl ⟨e.1.siteReflect τ k, _⟩))).1 = e.1
      rw [siteEdgeLabelInv_negative_val]
      exact PositiveEdge.siteReflect_siteReflect τ k e.1
    · apply Subtype.ext
      change (Λ.siteEdgeLabelInv τ k hΛ
        (Sum.inr (Sum.inl ⟨e.1.siteReflect τ k, _⟩))).1 = e.1
      rw [siteEdgeLabelInv_negative_val]
      exact PositiveEdge.siteReflect_siteReflect τ k e.1
  right_inv label := by
    rcases label with e | e
    · simp only [siteEdgeLabelInv_plane]
      rw [dif_pos e.2]
    · rcases e with e | e
      · simp only [siteEdgeLabelInv_negative]
        rw [dif_neg]
        · rw [dif_neg]
          · simp
          · exact siteReflect_not_mem_sitePositiveEdges Λ τ k e
        · intro h
          have href := siteReflect_mem_sitePlaneEdges_iff Λ τ k hΛ e.1
          have heplus := (Finset.mem_filter.mp e.2).2.2
          exact heplus (Finset.mem_filter.mp (href.mp h)).2
      · simp only [siteEdgeLabelInv_positive]
        rw [dif_neg]
        · rw [dif_pos e.2]
        · intro h
          exact (Finset.mem_filter.mp e.2).2.2 (Finset.mem_filter.mp h).2

omit [Group G] in
theorem siteReflect_eq_self_of_mem_sitePlaneEdges
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (e : Λ.sitePlaneEdges τ k) : e.1.siteReflect τ k = e.1 := by
  obtain ⟨_, hsource, hdir⟩ := Finset.mem_filter.mp e.2
  rw [PositiveEdge.siteReflect, if_neg hdir]
  congr 1
  ext i
  by_cases hi : i = τ
  · subst i
    rw [siteReflection_apply_eq, hsource]
    omega
  · simp [hi]

/-- Swap the two side labels while leaving plane labels fixed. -/
def siteReflectLabel {P O : Type*} :
    SiteReflection.ReflectedLabel P O → SiteReflection.ReflectedLabel P O
  | Sum.inl o => Sum.inl o
  | Sum.inr (Sum.inl p) => Sum.inr (Sum.inr p)
  | Sum.inr (Sum.inr p) => Sum.inr (Sum.inl p)

theorem siteEdgeLabelEquiv_siteReflect (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.SiteSymmetric τ k)
    (e : Λ.dynamicEdges) :
    Λ.siteEdgeLabelEquiv τ k hΛ
        ⟨e.1.siteReflect τ k, (hΛ.1 e.1).mp e.2⟩ =
      siteReflectLabel (Λ.siteEdgeLabelEquiv τ k hΛ e) := by
  let E := Λ.siteEdgeLabelEquiv τ k hΛ
  generalize hlabel : E e = label
  rcases label with o | p
  · have heo : e.1 = o.1 := by
      have he : E.symm (Sum.inl o) = e := by
        apply E.injective
        simp [hlabel]
      have he' := congrArg Subtype.val he
      simpa only [siteEdgeLabelEquiv] using he'.symm
    have href : e.1.siteReflect τ k = e.1 := by
      rw [heo]
      exact siteReflect_eq_self_of_mem_sitePlaneEdges Λ τ k o
    have hsub : (⟨e.1.siteReflect τ k, (hΛ.1 e.1).mp e.2⟩ :
        Λ.dynamicEdges) = e := Subtype.ext href
    rw [hsub, hlabel]
    rfl
  · rcases p with p | p
    · have heval : e.1 = p.1.siteReflect τ k := by
        have he : E.symm (Sum.inr (Sum.inl p)) = e := by
          apply E.injective
          simp [hlabel]
        have he' := congrArg Subtype.val he
        simpa only [siteEdgeLabelEquiv] using he'.symm
      have href : e.1.siteReflect τ k = p.1 := by
        rw [heval]
        exact PositiveEdge.siteReflect_siteReflect τ k p.1
      have hsub : (⟨e.1.siteReflect τ k, (hΛ.1 e.1).mp e.2⟩ :
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
        simpa only [siteEdgeLabelEquiv] using he'.symm
      have hsub : (⟨e.1.siteReflect τ k, (hΛ.1 e.1).mp e.2⟩ :
          Λ.dynamicEdges) =
            ⟨p.1.siteReflect τ k,
              (hΛ.1 p.1).mp (Finset.mem_filter.mp p.2).1⟩ := by
        apply Subtype.ext
        exact congrArg (PositiveEdge.siteReflect τ k) heval
      rw [hsub]
      change E ⟨p.1.siteReflect τ k, _⟩ = _
      exact E.apply_symm_apply (Sum.inr (Sum.inl p))

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Turn labelled plane/two-side fields into the dynamic variables of the
finite specification.  The negative representative is inverted exactly when
the corresponding stored edge is perpendicular to the reflection plane. -/
def siteAssemble (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) :
    C(SiteReflection.ReflectedConfiguration G
        (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k),
      DynamicConfiguration Λ) where
  toFun U e :=
    match Λ.siteEdgeLabelEquiv τ k hΛ e with
    | Sum.inl o => U.1 o
    | Sum.inr (Sum.inr p) => U.2.2 p
    | Sum.inr (Sum.inl p) =>
        if p.1.direction = τ then (U.2.1 p)⁻¹ else U.2.1 p
  continuous_toFun := by
    apply continuous_pi
    intro e
    generalize hlabel : Λ.siteEdgeLabelEquiv τ k hΛ e = label
    rcases label with o | p
    · simpa [hlabel] using
        (continuous_apply o).comp (continuous_fst : Continuous fun U :
          SiteReflection.ReflectedConfiguration G
            (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k) => U.1)
    · rcases p with p | p
      · by_cases hdir : p.1.direction = τ
        · simpa [hlabel, hdir] using continuous_inv.comp
            ((continuous_apply p).comp (continuous_fst.comp continuous_snd))
        · simpa [hlabel, hdir] using
            (continuous_apply p).comp (continuous_fst.comp continuous_snd)
      · simpa [hlabel] using
          (continuous_apply p).comp (continuous_snd.comp continuous_snd)

/-- The labelled-field assembly intertwines swapping the two strict sides
with the geometric site reflection of the evaluated full configuration. -/
theorem siteAssemble_reflect (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k)
    (U : SiteReflection.ReflectedConfiguration G
      (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k)) :
    Λ.evaluate (Λ.siteAssemble τ k hΛ
        (SiteReflection.WilsonActionDecomposition.reflect U)) =
      siteReflectConfiguration τ k
        (Λ.evaluate (Λ.siteAssemble τ k hΛ U)) := by
  funext e
  by_cases he : e ∈ Λ.dynamicEdges
  · rw [Λ.evaluate_of_mem _ e he]
    simp only [siteReflectConfiguration]
    have href : e.siteReflect τ k ∈ Λ.dynamicEdges := (hΛ.1 e).mp he
    rw [Λ.evaluate_of_mem _ (e.siteReflect τ k) href]
    let edyn : Λ.dynamicEdges := ⟨e, he⟩
    let eref : Λ.dynamicEdges := ⟨e.siteReflect τ k, href⟩
    have hlabel := siteEdgeLabelEquiv_siteReflect Λ τ k hΛ edyn
    change (Λ.siteAssemble τ k hΛ
      (SiteReflection.WilsonActionDecomposition.reflect U)) edyn =
        (if e.direction = τ then
          ((Λ.siteAssemble τ k hΛ U) eref)⁻¹
        else (Λ.siteAssemble τ k hΛ U) eref)
    unfold siteAssemble
    simp only [ContinuousMap.coe_mk]
    generalize heq : Λ.siteEdgeLabelEquiv τ k hΛ edyn = label
    rw [heq] at hlabel
    rcases label with o | p
    · rw [hlabel]
      have hdir : e.direction ≠ τ := by
        have := (Finset.mem_filter.mp o.2).2.2
        have heval : e = o.1 := by
          have hsub : edyn = (Λ.siteEdgeLabelEquiv τ k hΛ).symm (Sum.inl o) := by
            apply (Λ.siteEdgeLabelEquiv τ k hΛ).injective
            rw [heq, (Λ.siteEdgeLabelEquiv τ k hΛ).apply_symm_apply]
          have := congrArg Subtype.val hsub
          simpa [edyn, siteEdgeLabelEquiv] using this
        simpa [heval] using this
      simp [siteReflectLabel, hdir,
        SiteReflection.WilsonActionDecomposition.reflect]
    · rcases p with p | p
      · rw [hlabel]
        have hdir : e.direction = p.1.direction := by
          have heval : e = (p.1.siteReflect τ k) := by
            have hsub : edyn = (Λ.siteEdgeLabelEquiv τ k hΛ).symm
                (Sum.inr (Sum.inl p)) := by
              apply (Λ.siteEdgeLabelEquiv τ k hΛ).injective
              rw [heq, (Λ.siteEdgeLabelEquiv τ k hΛ).apply_symm_apply]
            have := congrArg Subtype.val hsub
            simpa [edyn, siteEdgeLabelEquiv] using this
          rw [heval]
          simp
        by_cases hpdir : p.1.direction = τ
        · simp [siteReflectLabel, hdir, hpdir,
            SiteReflection.WilsonActionDecomposition.reflect]
        · simp [siteReflectLabel, hdir, hpdir,
            SiteReflection.WilsonActionDecomposition.reflect]
      · rw [hlabel]
        have hdir : e.direction = p.1.direction := by
          have heval : e = p.1 := by
            have hsub : edyn = (Λ.siteEdgeLabelEquiv τ k hΛ).symm
                (Sum.inr (Sum.inr p)) := by
              apply (Λ.siteEdgeLabelEquiv τ k hΛ).injective
              rw [heq, (Λ.siteEdgeLabelEquiv τ k hΛ).apply_symm_apply]
            have := congrArg Subtype.val hsub
            simpa [edyn, siteEdgeLabelEquiv] using this
          rw [heval]
        by_cases hpdir : p.1.direction = τ
        · simp [siteReflectLabel, hdir, hpdir,
            SiteReflection.WilsonActionDecomposition.reflect]
        · simp [siteReflectLabel, hdir, hpdir,
            SiteReflection.WilsonActionDecomposition.reflect]
  · rw [Λ.evaluate_of_not_mem _ e he]
    simp only [siteReflectConfiguration]
    rw [Λ.evaluate_of_not_mem]
    · exact congrFun hΛ.2.2 e |>.symm
    · exact fun href => he ((hΛ.1 e).mpr href)

/-- Forget the negative-side variables, producing the full configuration
visible to a positive-side observable. -/
def siteEvaluatePositive (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) :
    C(SiteReflection.HalfConfiguration G
        (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k),
      Configuration d G) :=
  (⟨Λ.evaluate, Λ.continuous_evaluate⟩ : C(DynamicConfiguration Λ,
    Configuration d G)).comp <|
    (Λ.siteAssemble τ k hΛ).comp
      { toFun := fun U => (U.1, (1, U.2))
        continuous_toFun := by fun_prop }

/-- Keep only plane variables, filling both strict halves with the identity. -/
def siteEvaluatePlane (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) :
    C(SiteReflection.PlaneConfiguration G (Λ.sitePlaneEdges τ k),
      Configuration d G) :=
  (⟨Λ.evaluate, Λ.continuous_evaluate⟩ : C(DynamicConfiguration Λ,
    Configuration d G)).comp <|
    (Λ.siteAssemble τ k hΛ).comp
      { toFun := fun Uzero => (Uzero, (1, 1))
        continuous_toFun := by fun_prop }

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
theorem planePlaquette_base_siteReflect (τ : Fin d) (k : ℤ)
    (p : Plaquette d) (hplane : p.base τ = k ∧
      p.first ≠ τ ∧ p.second ≠ τ) :
    (p.siteReflect τ k).base τ = k := by
  rw [Plaquette.siteReflect, if_neg (not_or_intro hplane.2.1 hplane.2.2)]
  change siteReflection τ k p.base τ = k
  rw [siteReflection_apply_eq, hplane.1]
  omega

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem siteReflect_mem_sitePlanePlaquettes_iff
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) (p : Plaquette d) :
    p.siteReflect τ k ∈ Λ.sitePlanePlaquettes τ k ↔
      p ∈ Λ.sitePlanePlaquettes τ k := by
  simp only [sitePlanePlaquettes, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hbase, hfirst, hsecond⟩
    refine ⟨(hΛ.2.1 p).mpr hp, ?_, by simpa using hfirst, by simpa using hsecond⟩
    by_cases hperp : p.first = τ ∨ p.second = τ
    · rcases hperp with h | h <;> simp [h] at hfirst hsecond
    · rw [Plaquette.siteReflect] at hbase
      simp only [hperp, if_false, siteReflection_apply_eq] at hbase
      omega
  · rintro ⟨hp, hbase, hfirst, hsecond⟩
    refine ⟨(hΛ.2.1 p).mp hp, ?_, by simpa using hfirst, by simpa using hsecond⟩
    exact planePlaquette_base_siteReflect τ k p ⟨hbase, hfirst, hsecond⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Every active plaquette belongs to the plane family, the chosen positive
family, or the reflection of the chosen positive family. -/
theorem activePlaquette_partition (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.SiteSymmetric τ k) (p : Plaquette d) :
    p ∈ Λ.activePlaquettes ↔
      p ∈ Λ.sitePlanePlaquettes τ k ∨
      p ∈ Λ.sitePositivePlaquettes τ k ∨
      p.siteReflect τ k ∈ Λ.sitePositivePlaquettes τ k := by
  constructor
  · intro hp
    by_cases hplane : p.base τ = k ∧ p.first ≠ τ ∧ p.second ≠ τ
    · exact Or.inl (Finset.mem_filter.mpr ⟨hp, hplane⟩)
    · by_cases hside : k ≤ p.base τ
      · exact Or.inr <| Or.inl <| Finset.mem_filter.mpr ⟨hp, hside, hplane⟩
      · right; right
        rw [sitePositivePlaquettes, Finset.mem_filter]
        refine ⟨(hΛ.2.1 p).mp hp, ?_⟩
        by_cases hperp : p.first = τ ∨ p.second = τ
        · have hbase : (p.siteReflect τ k).base τ = 2 * k - p.base τ - 1 := by
            rw [Plaquette.siteReflect, if_pos hperp]
            simp only
            rw [show step (siteReflection τ k p.base) (.backward τ) τ =
                siteReflection τ k p.base τ - 1 by
              change siteReflection τ k p.base τ + (-unitVector τ) τ = _
              simp [unitVector]
              ring]
            rw [siteReflection_apply_eq]
          constructor
          · omega
          · intro hrefplane
            rcases hrefplane with ⟨_, hfirst, hsecond⟩
            rcases hperp with h | h <;> simp [h] at hfirst hsecond
        · have hbase : (p.siteReflect τ k).base τ = 2 * k - p.base τ := by
            rw [Plaquette.siteReflect, if_neg hperp]
            exact siteReflection_apply_eq τ k p.base
          constructor
          · omega
          · intro hrefplane
            exact hplane ⟨by omega, by simpa using hrefplane.2.1,
              by simpa using hrefplane.2.2⟩
  · rintro (hp | hp | hp)
    · exact (Finset.mem_filter.mp hp).1
    · exact (Finset.mem_filter.mp hp).1
    · exact (hΛ.2.1 p).mpr (Finset.mem_filter.mp hp).1

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The three plaquette pieces are pairwise disjoint. -/
theorem activePlaquette_partition_exclusive (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.SiteSymmetric τ k) (p : Plaquette d) :
    (p ∈ Λ.sitePlanePlaquettes τ k →
      p ∉ Λ.sitePositivePlaquettes τ k ∧
      p.siteReflect τ k ∉ Λ.sitePositivePlaquettes τ k) ∧
    (p ∈ Λ.sitePositivePlaquettes τ k →
      p.siteReflect τ k ∉ Λ.sitePositivePlaquettes τ k) := by
  constructor
  · intro hp
    have hp' := (Finset.mem_filter.mp hp).2
    constructor
    · intro hplus
      exact (Finset.mem_filter.mp hplus).2.2 hp'
    · intro hplus
      have hrefplane := (siteReflect_mem_sitePlanePlaquettes_iff Λ τ k hΛ p).2 hp
      exact (Finset.mem_filter.mp hplus).2.2 (Finset.mem_filter.mp hrefplane).2
  · intro hp href
    have hpside := (Finset.mem_filter.mp hp).2.1
    have hrefside := (Finset.mem_filter.mp href).2.1
    by_cases hperp : p.first = τ ∨ p.second = τ
    · have hbase : (p.siteReflect τ k).base τ = 2 * k - p.base τ - 1 := by
        rw [Plaquette.siteReflect, if_pos hperp]
        simp only
        rw [show step (siteReflection τ k p.base) (.backward τ) τ =
            siteReflection τ k p.base τ - 1 by
          change siteReflection τ k p.base τ + (-unitVector τ) τ = _
          simp [unitVector]
          ring]
        rw [siteReflection_apply_eq]
      omega
    · have hbase : (p.siteReflect τ k).base τ = 2 * k - p.base τ := by
        rw [Plaquette.siteReflect, if_neg hperp]
        exact siteReflection_apply_eq τ k p.base
      have hpnot := (Finset.mem_filter.mp hp).2.2
      have hpne : p.base τ ≠ k := fun heq => hpnot
        ⟨heq, not_or.mp hperp |>.1, not_or.mp hperp |>.2⟩
      omega

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem mem_siteNegativePlaquettes (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (p : Plaquette d) :
    p ∈ Λ.siteNegativePlaquettes τ k ↔
      p.siteReflect τ k ∈ Λ.sitePositivePlaquettes τ k := by
  rw [siteNegativePlaquettes, Finset.mem_map_equiv]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem activePlaquettes_eq_siteReflection_union
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) :
    Λ.activePlaquettes = Λ.sitePlanePlaquettes τ k ∪
      (Λ.sitePositivePlaquettes τ k ∪ Λ.siteNegativePlaquettes τ k) := by
  ext p
  simp only [Finset.mem_union, mem_siteNegativePlaquettes]
  exact Λ.activePlaquette_partition τ k hΛ p

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem sitePlanePlaquettes_disjoint_siteSides
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) :
    Disjoint (Λ.sitePlanePlaquettes τ k)
      (Λ.sitePositivePlaquettes τ k ∪ Λ.siteNegativePlaquettes τ k) := by
  rw [Finset.disjoint_left]
  intro p hp hside
  rw [Finset.mem_union, mem_siteNegativePlaquettes] at hside
  exact hside.elim
    (Λ.activePlaquette_partition_exclusive τ k hΛ p |>.1 hp |>.1)
    (Λ.activePlaquette_partition_exclusive τ k hΛ p |>.1 hp |>.2)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem sitePositivePlaquettes_disjoint_siteNegativePlaquettes
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) :
    Disjoint (Λ.sitePositivePlaquettes τ k) (Λ.siteNegativePlaquettes τ k) := by
  rw [Finset.disjoint_left]
  intro p hp hneg
  rw [mem_siteNegativePlaquettes] at hneg
  exact Λ.activePlaquette_partition_exclusive τ k hΛ p |>.2 hp hneg

/-- A reflected positive-side plaquette contributes the same Wilson potential
as its positive representative evaluated after swapping sides. -/
theorem plaquetteTerm_siteReflect_assemble
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) (Φ : RealPlaquettePotential G)
    (U : SiteReflection.ReflectedConfiguration G
      (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k))
    (p : Plaquette d) :
    Φ (FiniteVolume.plaquetteHolonomy Λ (Λ.siteAssemble τ k hΛ U)
        (p.siteReflect τ k)) =
      Φ (FiniteVolume.plaquetteHolonomy Λ
        (Λ.siteAssemble τ k hΛ
          (SiteReflection.WilsonActionDecomposition.reflect U)) p) := by
  unfold FiniteVolume.plaquetteHolonomy
  rw [Λ.siteAssemble_reflect τ k hΛ]
  exact (Φ.apply_holonomy_siteReflectConfiguration τ k
    (Λ.evaluate (Λ.siteAssemble τ k hΛ U)) p).symm

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
theorem step_forward_apply (x : Site d) (i j : Fin d) :
    step x (.forward i) j = x j + if j = i then 1 else 0 := by
  simp [step, SignedDirection.delta_forward, unitVector]

/-- An off-plane positive plaquette only reads the plane variables and the
chosen positive strict half of the concrete assembly. -/
theorem plaquetteHolonomy_siteAssemble_eq_evaluatePositive
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k)
    (U : SiteReflection.ReflectedConfiguration G
      (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k))
    (p : Plaquette d) (hp : p ∈ Λ.sitePositivePlaquettes τ k) :
    FiniteVolume.plaquetteHolonomy Λ (Λ.siteAssemble τ k hΛ U) p =
      holonomy (Λ.siteEvaluatePositive τ k hΛ (U.1, U.2.2)) p.boundary := by
  unfold FiniteVolume.plaquetteHolonomy siteEvaluatePositive
  change holonomy (Λ.evaluate (Λ.siteAssemble τ k hΛ U)) p.boundary =
    holonomy (Λ.evaluate (Λ.siteAssemble τ k hΛ
      (U.1, (1, U.2.2)))) p.boundary
  apply holonomy_eq_of_eqOn_edgeSupport
  intro e he
  have hsupport := he
  rw [siteBridge_plaquette_boundary_edgeSupport] at hsupport
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsupport
  have hpdata := (Finset.mem_filter.mp hp).2
  have heside : k ≤ e.source τ := by
    rcases hsupport with rfl | rfl | rfl | rfl
    · exact hpdata.1
    · by_cases hfirst : p.first = τ
      · change k ≤ step p.base (.forward p.first) τ
        rw [step_forward_apply, hfirst]
        simp
        omega
      · change k ≤ step p.base (.forward p.first) τ
        rw [step_forward_apply]
        simpa [Ne.symm hfirst] using hpdata.1
    · by_cases hsecond : p.second = τ
      · change k ≤ step p.base (.forward p.second) τ
        rw [step_forward_apply, hsecond]
        simp
        omega
      · change k ≤ step p.base (.forward p.second) τ
        rw [step_forward_apply]
        simpa [Ne.symm hsecond] using hpdata.1
    · exact hpdata.1
  by_cases hedyn : e ∈ Λ.dynamicEdges
  · rw [Λ.evaluate_of_mem _ e hedyn, Λ.evaluate_of_mem _ e hedyn]
    let edyn : Λ.dynamicEdges := ⟨e, hedyn⟩
    have hnotneg : e ∈ Λ.sitePlaneEdges τ k ∨
        e ∈ Λ.sitePositiveEdges τ k := by
      by_cases hplane : e.source τ = k ∧ e.direction ≠ τ
      · exact Or.inl (Finset.mem_filter.mpr ⟨hedyn, hplane⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hedyn, heside, hplane⟩)
    rcases hnotneg with hplane | hplus
    · have hlabel : Λ.siteEdgeLabelEquiv τ k hΛ edyn =
          Sum.inl (⟨e, hplane⟩ : Λ.sitePlaneEdges τ k) := by
        unfold siteEdgeLabelEquiv
        dsimp [edyn]
        rw [dif_pos hplane]
      simp only [siteAssemble, ContinuousMap.coe_mk]
      rw [hlabel]
    · have hlabel : Λ.siteEdgeLabelEquiv τ k hΛ edyn =
          Sum.inr (Sum.inr (⟨e, hplus⟩ : Λ.sitePositiveEdges τ k)) := by
        unfold siteEdgeLabelEquiv
        dsimp [edyn]
        rw [dif_neg, dif_pos hplus]
        intro hplane
        exact (Finset.mem_filter.mp hplus).2.2
          (Finset.mem_filter.mp hplane).2
      simp only [siteAssemble, ContinuousMap.coe_mk]
      rw [hlabel]
  · rw [Λ.evaluate_of_not_mem _ e hedyn, Λ.evaluate_of_not_mem _ e hedyn]

/-- A plane plaquette reads only the fixed plane coordinates. -/
theorem plaquetteHolonomy_siteAssemble_eq_evaluatePlane
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k)
    (U : SiteReflection.ReflectedConfiguration G
      (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k))
    (p : Plaquette d) (hp : p ∈ Λ.sitePlanePlaquettes τ k) :
    FiniteVolume.plaquetteHolonomy Λ (Λ.siteAssemble τ k hΛ U) p =
      holonomy (Λ.siteEvaluatePlane τ k hΛ U.1) p.boundary := by
  unfold FiniteVolume.plaquetteHolonomy siteEvaluatePlane
  change holonomy (Λ.evaluate (Λ.siteAssemble τ k hΛ U)) p.boundary =
    holonomy (Λ.evaluate (Λ.siteAssemble τ k hΛ
      (U.1, (1, 1)))) p.boundary
  apply holonomy_eq_of_eqOn_edgeSupport
  intro e he
  have hsupport := he
  rw [siteBridge_plaquette_boundary_edgeSupport] at hsupport
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsupport
  have hpdata := (Finset.mem_filter.mp hp).2
  have heplane : e.source τ = k ∧ e.direction ≠ τ := by
    rcases hsupport with rfl | rfl | rfl | rfl
    · exact ⟨hpdata.1, hpdata.2.1⟩
    · have hfirst := hpdata.2.1
      constructor
      · change step p.base (.forward p.first) τ = k
        rw [step_forward_apply]
        simp [Ne.symm hfirst, hpdata.1]
      · exact hpdata.2.2
    · have hsecond := hpdata.2.2
      constructor
      · change step p.base (.forward p.second) τ = k
        rw [step_forward_apply]
        simp [Ne.symm hsecond, hpdata.1]
      · exact hpdata.2.1
    · exact ⟨hpdata.1, hpdata.2.2⟩
  by_cases hedyn : e ∈ Λ.dynamicEdges
  · rw [Λ.evaluate_of_mem _ e hedyn, Λ.evaluate_of_mem _ e hedyn]
    let edyn : Λ.dynamicEdges := ⟨e, hedyn⟩
    have hplane : e ∈ Λ.sitePlaneEdges τ k :=
      Finset.mem_filter.mpr ⟨hedyn, heplane⟩
    have hlabel : Λ.siteEdgeLabelEquiv τ k hΛ edyn =
        Sum.inl (⟨e, hplane⟩ : Λ.sitePlaneEdges τ k) := by
      unfold siteEdgeLabelEquiv
      dsimp [edyn]
      rw [dif_pos hplane]
    simp only [siteAssemble, ContinuousMap.coe_mk]
    rw [hlabel]
  · rw [Λ.evaluate_of_not_mem _ e hedyn, Λ.evaluate_of_not_mem _ e hedyn]

/-- The actual finite Wilson action is exactly the labelled site-reflection
decomposition after the concrete change of variables. -/
theorem action_siteAssemble
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) (Φ : RealPlaquettePotential G)
    (U : SiteReflection.ReflectedConfiguration G
      (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k)) :
    FiniteVolume.action Λ Φ (Λ.siteAssemble τ k hΛ U) =
      (SiteReflection.WilsonActionDecomposition.ofWilsonPlaquettes Φ
        (Λ.siteEvaluatePositive τ k hΛ) (Λ.siteEvaluatePlane τ k hΛ)
        (Λ.sitePositivePlaquettes τ k) (Λ.sitePlanePlaquettes τ k)).action U := by
  let f : Plaquette d → ℝ := fun p =>
    Φ (FiniteVolume.plaquetteHolonomy Λ (Λ.siteAssemble τ k hΛ U) p)
  let fplane : Plaquette d → ℝ := fun p =>
    Φ (holonomy (Λ.siteEvaluatePlane τ k hΛ U.1) p.boundary)
  let fplus : Plaquette d → ℝ := fun p =>
    Φ (holonomy (Λ.siteEvaluatePositive τ k hΛ (U.1, U.2.2)) p.boundary)
  let fminus : Plaquette d → ℝ := fun p =>
    Φ (holonomy (Λ.siteEvaluatePositive τ k hΛ (U.1, U.2.1)) p.boundary)
  change (∑ p ∈ Λ.activePlaquettes, f p) =
    (∑ p ∈ Λ.sitePositivePlaquettes τ k, fminus p) +
      (∑ p ∈ Λ.sitePlanePlaquettes τ k, fplane p) +
      ∑ p ∈ Λ.sitePositivePlaquettes τ k, fplus p
  have hsplit : (∑ p ∈ Λ.activePlaquettes, f p) =
      (∑ p ∈ Λ.sitePlanePlaquettes τ k, f p) +
      (∑ p ∈ Λ.sitePositivePlaquettes τ k, f p) +
      ∑ p ∈ Λ.sitePositivePlaquettes τ k, f (p.siteReflect τ k) := by
    classical
    have hnegative : (∑ p ∈ Λ.siteNegativePlaquettes τ k, f p) =
        ∑ p ∈ Λ.sitePositivePlaquettes τ k, f (p.siteReflect τ k) := by
      change (∑ p ∈ (Λ.sitePositivePlaquettes τ k).map
          (Plaquette.siteReflectionEquiv τ k).toEmbedding, f p) = _
      rw [Finset.sum_map]
      rfl
    rw [Λ.activePlaquettes_eq_siteReflection_union τ k hΛ,
      Finset.sum_union (Λ.sitePlanePlaquettes_disjoint_siteSides τ k hΛ),
      Finset.sum_union
        (Λ.sitePositivePlaquettes_disjoint_siteNegativePlaquettes τ k hΛ),
      hnegative, add_assoc]
  rw [hsplit]
  have hplane : (∑ p ∈ Λ.sitePlanePlaquettes τ k, f p) =
      ∑ p ∈ Λ.sitePlanePlaquettes τ k, fplane p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact congrArg Φ (Λ.plaquetteHolonomy_siteAssemble_eq_evaluatePlane
      τ k hΛ U p hp)
  have hplus : (∑ p ∈ Λ.sitePositivePlaquettes τ k, f p) =
      ∑ p ∈ Λ.sitePositivePlaquettes τ k, fplus p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact congrArg Φ (Λ.plaquetteHolonomy_siteAssemble_eq_evaluatePositive
      τ k hΛ U p hp)
  have hminus : (∑ p ∈ Λ.sitePositivePlaquettes τ k,
      f (p.siteReflect τ k)) =
      ∑ p ∈ Λ.sitePositivePlaquettes τ k, fminus p := by
    apply Finset.sum_congr rfl
    intro p hp
    change Φ (FiniteVolume.plaquetteHolonomy Λ
      (Λ.siteAssemble τ k hΛ U) (p.siteReflect τ k)) = _
    rw [Λ.plaquetteTerm_siteReflect_assemble τ k hΛ Φ U p]
    exact congrArg Φ (Λ.plaquetteHolonomy_siteAssemble_eq_evaluatePositive
      τ k hΛ (SiteReflection.WilsonActionDecomposition.reflect U) p hp)
  rw [hplane, hplus, hminus]
  ring

end Topology

section Haar

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G]

/-- The concrete assembly from plane/two-side coordinates preserves product
Haar.  It is a relabeling followed by coordinatewise inversion on precisely
the negative perpendicular representatives. -/
theorem measurePreserving_siteAssemble (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.SiteSymmetric τ k) :
    MeasurePreserving (Λ.siteAssemble τ k hΛ)
      (SiteReflection.reflectedHaar (G := G)
        (P := Λ.sitePositiveEdges τ k) (O := Λ.sitePlaneEdges τ k))
      Λ.haarMeasure := by
  let E := Λ.siteEdgeLabelEquiv τ k hΛ
  let R := ProductHaar.reindexEquiv (G := G) E.symm
  have hR := ProductHaar.measurePreserving_reindex (G := G) E.symm
  let I : (SiteReflection.ReflectedLabel
      (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k) → G) →
      (SiteReflection.ReflectedLabel
      (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k) → G) :=
    fun V label => match label with
      | Sum.inr (Sum.inl p) => if p.1.direction = τ then (V label)⁻¹ else V label
      | _ => V label
  have hI : MeasurePreserving I
      (ProductHaar.measure G (SiteReflection.ReflectedLabel
        (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k)))
      (ProductHaar.measure G (SiteReflection.ReflectedLabel
        (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k))) := by
    let f : SiteReflection.ReflectedLabel
        (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k) → G → G :=
      fun label x => match label with
        | Sum.inr (Sum.inl p) => if p.1.direction = τ then x⁻¹ else x
        | _ => x
    have hf : ∀ label, MeasurePreserving (f label)
        (GaugeHaarProbability.haar G) (GaugeHaarProbability.haar G) := by
      intro label
      rcases label with o | p
      · exact MeasurePreserving.id _
      · rcases p with p | p
        · by_cases hdir : p.1.direction = τ
          · simpa [f, hdir] using GaugeHaarProbability.measurePreserving_inv (G := G)
          · simpa [f, hdir] using
              (MeasurePreserving.id (GaugeHaarProbability.haar G))
        · exact MeasurePreserving.id _
    have hcoord := ProductHaar.measurePreserving_coordinatewise
      (G := G) (fun _ => GaugeHaarProbability.haar G) f hf
    simpa only [ProductHaar.measure] using hcoord
  let Eouter := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : SiteReflection.ReflectedLabel
      (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k) => G)
  let Esides := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : (Λ.sitePositiveEdges τ k) ⊕ (Λ.sitePositiveEdges τ k) => G)
  let J : SiteReflection.ReflectedConfiguration G
      (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k) →
      (SiteReflection.ReflectedLabel
        (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k) → G) :=
    fun U => Eouter.symm (U.1, Esides.symm U.2)
  have hJ : MeasurePreserving J
      (SiteReflection.reflectedHaar (G := G)
        (P := Λ.sitePositiveEdges τ k) (O := Λ.sitePlaneEdges τ k))
      (ProductHaar.measure G (SiteReflection.ReflectedLabel
        (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k))) := by
    exact (MeasureTheory.measurePreserving_sumPiEquivProdPi_symm
      (fun _ : SiteReflection.ReflectedLabel
        (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k) =>
          GaugeHaarProbability.haar G)).comp
      (MeasurePreserving.prod (MeasurePreserving.id _)
        (MeasureTheory.measurePreserving_sumPiEquivProdPi_symm
          (fun _ : (Λ.sitePositiveEdges τ k) ⊕
            (Λ.sitePositiveEdges τ k) => GaugeHaarProbability.haar G)))
  have hcomp := hR.comp (hI.comp hJ)
  refine ⟨(Λ.siteAssemble τ k hΛ).continuous.measurable, ?_⟩
  have heq : (Λ.siteAssemble τ k hΛ : _ → _) =
      R ∘ I ∘ J := by
    funext U e
    let label := E e
    generalize hlabel : E e = label
    rcases label with o | p
    · unfold siteAssemble
      simp only [ContinuousMap.coe_mk, Function.comp_apply]
      rw [hlabel]
      simp only
      rw [show R (I (J U)) e = (I (J U)) (E e) by
        exact ProductHaar.reindex_apply E.symm (I (J U)) e]
      change U.1 o = (I (J U)) (E e)
      rw [hlabel]
      rfl
    · rcases p with p | p
      · unfold siteAssemble
        simp only [ContinuousMap.coe_mk, Function.comp_apply]
        rw [hlabel]
        simp only
        rw [show R (I (J U)) e = (I (J U)) (E e) by
          exact ProductHaar.reindex_apply E.symm (I (J U)) e]
        change (if p.1.direction = τ then (U.2.1 p)⁻¹ else U.2.1 p) =
          (I (J U)) (E e)
        rw [hlabel]
        rfl
      · unfold siteAssemble
        simp only [ContinuousMap.coe_mk, Function.comp_apply]
        rw [hlabel]
        simp only
        rw [show R (I (J U)) e = (I (J U)) (E e) by
          exact ProductHaar.reindex_apply E.symm (I (J U)) e]
        change U.2.2 p = (I (J U)) (E e)
        rw [hlabel]
        rfl
  rw [heq]
  exact hcomp.map_eq

/-- Restrict a full-lattice local observable to the plane and positive-side
variables of a symmetric finite specification. -/
def siteRestrictObservable (Λ : FiniteSpecification d G)
    (τ : Fin d) (k : ℤ) (hΛ : Λ.SiteSymmetric τ k)
    (F : LocalObservable d G) :
    SiteReflection.PositiveObservable G
      (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k) :=
  F.toContinuousMap.comp (Λ.siteEvaluatePositive τ k hΛ)

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G] in
/-- Positive-half observables do not see the negative coordinates discarded
by `siteEvaluatePositive`. -/
theorem siteRestrictObservable_apply_assemble
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) (F : LocalObservable d G)
    (hF : F.SupportedInSitePositiveHalf τ k)
    (U : SiteReflection.ReflectedConfiguration G
      (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k)) :
    F (Λ.evaluate (Λ.siteAssemble τ k hΛ U)) =
      Λ.siteRestrictObservable τ k hΛ F (U.1, U.2.2) := by
  apply F.dependsOn_support
  intro e he
  change Λ.evaluate (Λ.siteAssemble τ k hΛ U) e =
    Λ.evaluate (Λ.siteAssemble τ k hΛ (U.1, (1, U.2.2))) e
  by_cases hedyn : e ∈ Λ.dynamicEdges
  · rw [Λ.evaluate_of_mem _ e hedyn, Λ.evaluate_of_mem _ e hedyn]
    let edyn : Λ.dynamicEdges := ⟨e, hedyn⟩
    have heside : k ≤ e.source τ := hF e he
    by_cases heplane : e.source τ = k ∧ e.direction ≠ τ
    · have hplane : e ∈ Λ.sitePlaneEdges τ k :=
        Finset.mem_filter.mpr ⟨hedyn, heplane⟩
      have hlabel : Λ.siteEdgeLabelEquiv τ k hΛ edyn =
          Sum.inl (⟨e, hplane⟩ : Λ.sitePlaneEdges τ k) := by
        unfold siteEdgeLabelEquiv
        dsimp [edyn]
        rw [dif_pos hplane]
      simp only [siteAssemble, ContinuousMap.coe_mk]
      rw [hlabel]
    · have hplus : e ∈ Λ.sitePositiveEdges τ k :=
        Finset.mem_filter.mpr ⟨hedyn, heside, heplane⟩
      have hlabel : Λ.siteEdgeLabelEquiv τ k hΛ edyn =
          Sum.inr (Sum.inr (⟨e, hplus⟩ : Λ.sitePositiveEdges τ k)) := by
        unfold siteEdgeLabelEquiv
        dsimp [edyn]
        rw [dif_neg, dif_pos hplus]
        intro hplane
        exact heplane (Finset.mem_filter.mp hplane).2
      simp only [siteAssemble, ContinuousMap.coe_mk]
      rw [hlabel]
  · rw [Λ.evaluate_of_not_mem _ e hedyn, Λ.evaluate_of_not_mem _ e hedyn]

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G] in
/-- The concrete reflected product becomes the abstract labelled reflected
product after assembly. -/
theorem siteReflectionProduct_assemble
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) (F H : LocalObservable d G)
    (hF : F.SupportedInSitePositiveHalf τ k)
    (hH : H.SupportedInSitePositiveHalf τ k)
    (U : SiteReflection.ReflectedConfiguration G
      (Λ.sitePositiveEdges τ k) (Λ.sitePlaneEdges τ k)) :
    F.siteReflectionProduct τ k H
        (Λ.evaluate (Λ.siteAssemble τ k hΛ U)) =
      SiteReflection.theta (SiteReflection.liftPositive
          (Λ.siteRestrictObservable τ k hΛ F)) U *
        SiteReflection.liftPositive
          (Λ.siteRestrictObservable τ k hΛ H) U := by
  rw [LocalObservable.siteReflectionProduct_apply,
    ← Λ.siteAssemble_reflect τ k hΛ]
  rw [Λ.siteRestrictObservable_apply_assemble τ k hΛ F hF
      (SiteReflection.WilsonActionDecomposition.reflect U),
    Λ.siteRestrictObservable_apply_assemble τ k hΛ H hH U]
  rfl

/-- The concrete and labelled partition functions agree under the
reflection-adapted change of variables. -/
theorem partitionFunction_eq_siteDecomposition
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) (Φ : RealPlaquettePotential G) (β : ℝ) :
    FiniteVolume.partitionFunction Λ Φ β =
      (SiteReflection.WilsonActionDecomposition.ofWilsonPlaquettes Φ
        (Λ.siteEvaluatePositive τ k hΛ) (Λ.siteEvaluatePlane τ k hΛ)
        (Λ.sitePositivePlaquettes τ k) (Λ.sitePlanePlaquettes τ k)).partitionFunction β := by
  let D := SiteReflection.WilsonActionDecomposition.ofWilsonPlaquettes Φ
    (Λ.siteEvaluatePositive τ k hΛ) (Λ.siteEvaluatePlane τ k hΛ)
    (Λ.sitePositivePlaquettes τ k) (Λ.sitePlanePlaquettes τ k)
  have hchange :
      (∫ U, FiniteVolume.boltzmannWeight Λ Φ β
          (Λ.siteAssemble τ k hΛ U) ∂SiteReflection.reflectedHaar) =
        ∫ V, FiniteVolume.boltzmannWeight Λ Φ β V ∂Λ.haarMeasure := by
    rw [← (Λ.measurePreserving_siteAssemble τ k hΛ).map_eq]
    exact (MeasureTheory.integral_map
      (Λ.siteAssemble τ k hΛ).continuous.measurable.aemeasurable
      (FiniteVolume.continuous_boltzmannWeight Λ Φ β).aestronglyMeasurable).symm
  change (∫ V, FiniteVolume.boltzmannWeight Λ Φ β V ∂Λ.haarMeasure) =
    ∫ U, D.boltzmannWeight β U ∂SiteReflection.reflectedHaar
  rw [← hchange]
  apply integral_congr_ae
  filter_upwards with U
  simp only [FiniteVolume.boltzmannWeight,
    SiteReflection.WilsonActionDecomposition.boltzmannWeight]
  rw [Λ.action_siteAssemble τ k hΛ Φ U]

/-- Concrete finite-volume reflection pairing equals the normalized labelled
pairing whose Fubini factorization was proved in `SiteReflectionPositivity`. -/
theorem integral_gibbsMeasure_siteReflectionProduct_eq
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) (Φ : RealPlaquettePotential G) (β : ℝ)
    (F H : LocalObservable d G)
    (hF : F.SupportedInSitePositiveHalf τ k)
    (hH : H.SupportedInSitePositiveHalf τ k) :
    (∫ V, F.siteReflectionProduct τ k H (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ Φ β) =
      let D := SiteReflection.WilsonActionDecomposition.ofWilsonPlaquettes Φ
        (Λ.siteEvaluatePositive τ k hΛ) (Λ.siteEvaluatePlane τ k hΛ)
        (Λ.sitePositivePlaquettes τ k) (Λ.sitePlanePlaquettes τ k)
      D.reflectionInnerProduct β
        (Λ.siteRestrictObservable τ k hΛ F)
        (Λ.siteRestrictObservable τ k hΛ H) := by
  let D := SiteReflection.WilsonActionDecomposition.ofWilsonPlaquettes Φ
    (Λ.siteEvaluatePositive τ k hΛ) (Λ.siteEvaluatePlane τ k hΛ)
    (Λ.sitePositivePlaquettes τ k) (Λ.sitePlanePlaquettes τ k)
  rw [FiniteVolume.gibbsMeasure, integral_tilted]
  change (∫ V, (Real.exp (β * FiniteVolume.action Λ Φ V) /
      FiniteVolume.partitionFunction Λ Φ β : ℝ) •
        F.siteReflectionProduct τ k H (Λ.evaluate V) ∂Λ.haarMeasure) = _
  let K : DynamicConfiguration Λ → ℂ := fun V =>
    (Real.exp (β * FiniteVolume.action Λ Φ V) /
      FiniteVolume.partitionFunction Λ Φ β : ℝ) •
        F.siteReflectionProduct τ k H (Λ.evaluate V)
  have hK : Continuous K := by
    unfold K
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp
        (continuous_const.mul (FiniteVolume.continuous_action Λ Φ))).div_const _)).mul
      ((F.siteReflectionProduct τ k H).toContinuousMap.continuous.comp
        Λ.continuous_evaluate)
  have hchange :
      (∫ U, K (Λ.siteAssemble τ k hΛ U)
          ∂SiteReflection.reflectedHaar) = ∫ V, K V ∂Λ.haarMeasure := by
    rw [← (Λ.measurePreserving_siteAssemble τ k hΛ).map_eq]
    exact (MeasureTheory.integral_map
      (Λ.siteAssemble τ k hΛ).continuous.measurable.aemeasurable
      hK.measurable.aestronglyMeasurable).symm
  rw [← hchange]
  change (∫ U, (Real.exp (β * FiniteVolume.action Λ Φ
      (Λ.siteAssemble τ k hΛ U)) /
        FiniteVolume.partitionFunction Λ Φ β : ℝ) •
      F.siteReflectionProduct τ k H
        (Λ.evaluate (Λ.siteAssemble τ k hΛ U))
      ∂SiteReflection.reflectedHaar) = _
  unfold SiteReflection.WilsonActionDecomposition.reflectionInnerProduct
  unfold SiteReflection.WilsonActionDecomposition.gibbsReflectionPairing
  rw [Λ.partitionFunction_eq_siteDecomposition τ k hΛ Φ β]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with U
  rw [Λ.action_siteAssemble τ k hΛ Φ U,
    Λ.siteReflectionProduct_assemble τ k hΛ F H hF hH U]
  simp only [SiteReflection.WilsonActionDecomposition.boltzmannWeight]
  norm_cast
  simp only [div_eq_mul_inv, Complex.ofReal_inv]
  change ((Real.exp (β * D.action U) * (D.partitionFunction β)⁻¹ : ℝ) : ℂ) * _ = _
  rw [Complex.ofReal_mul, Complex.ofReal_inv]
  ring

/-- Reflection positivity of every symmetric concrete finite specification. -/
theorem siteReflectionPositive_gibbsMeasure
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) (Φ : RealPlaquettePotential G) (β : ℝ)
    (F : LocalObservable d G) (hF : F.SupportedInSitePositiveHalf τ k) :
    Complex.im (∫ V, F.siteReflectionProduct τ k F (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ Φ β) = 0 ∧
      0 ≤ Complex.re (∫ V, F.siteReflectionProduct τ k F (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ Φ β) := by
  rw [Λ.integral_gibbsMeasure_siteReflectionProduct_eq τ k hΛ Φ β F F hF hF]
  exact (SiteReflection.WilsonActionDecomposition.ofWilsonPlaquettes Φ
    (Λ.siteEvaluatePositive τ k hΛ) (Λ.siteEvaluatePlane τ k hΛ)
    (Λ.sitePositivePlaquettes τ k) (Λ.sitePlanePlaquettes τ k))
      |>.reflectionInnerProduct_self_nonneg β
        (Λ.siteRestrictObservable τ k hΛ F)

/-- Concrete finite-volume Cauchy--Schwarz for the site-reflection pairing. -/
theorem normSq_integral_gibbsMeasure_siteReflectionProduct_le
    (Λ : FiniteSpecification d G) (τ : Fin d) (k : ℤ)
    (hΛ : Λ.SiteSymmetric τ k) (Φ : RealPlaquettePotential G) (β : ℝ)
    (F H : LocalObservable d G)
    (hF : F.SupportedInSitePositiveHalf τ k)
    (hH : H.SupportedInSitePositiveHalf τ k) :
    Complex.normSq (∫ V, F.siteReflectionProduct τ k H (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ Φ β) ≤
      Complex.re (∫ V, F.siteReflectionProduct τ k F (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ Φ β) *
      Complex.re (∫ V, H.siteReflectionProduct τ k H (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ Φ β) := by
  rw [Λ.integral_gibbsMeasure_siteReflectionProduct_eq τ k hΛ Φ β F H hF hH,
    Λ.integral_gibbsMeasure_siteReflectionProduct_eq τ k hΛ Φ β F F hF hF,
    Λ.integral_gibbsMeasure_siteReflectionProduct_eq τ k hΛ Φ β H H hH hH]
  exact (SiteReflection.WilsonActionDecomposition.ofWilsonPlaquettes Φ
    (Λ.siteEvaluatePositive τ k hΛ) (Λ.siteEvaluatePlane τ k hΛ)
    (Λ.sitePositivePlaquettes τ k) (Λ.sitePlanePlaquettes τ k))
      |>.normSq_reflectionInnerProduct_le β
        (Λ.siteRestrictObservable τ k hΛ F)
        (Λ.siteRestrictObservable τ k hΛ H)

end Haar

end FiniteSpecification

end

end YangMills.Gauge
