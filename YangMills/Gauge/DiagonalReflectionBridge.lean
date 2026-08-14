/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.DiagonalReflectionPositivity

/-!
# Concrete finite-specification bridge for diagonal reflection

This file supplies the geometric transport from a diagonally symmetric cubic
`FiniteSpecification` to the fixed-plane/two-side normal form used by the
Taylor/Fubini proof of diagonal reflection positivity.
-/

open MeasureTheory

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

local instance diagonalReflectionBridgeDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

namespace FiniteSpecification

variable {d : ℕ} {G : Type*} [Group G]

/-- The four stored positive edges read by a plaquette boundary. -/
private theorem diagonalBridge_plaquette_boundary_edgeSupport (p : Plaquette d) :
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

/-- Signed affine distance from the diagonal plane `x τ - x σ = k`. -/
def diagonalHeight (τ σ : Fin d) (k : ℤ) (x : Site d) : ℤ :=
  x τ - x σ - k

omit [Group G] in
@[simp]
theorem diagonalHeight_reflect {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ)
    (x : Site d) :
    diagonalHeight τ σ k (diagonalReflection τ σ k x) =
      -diagonalHeight τ σ k x := by
  unfold diagonalHeight
  rw [diagonalReflection_difference hτσ]
  ring

/-- Tangential dynamic edges lying in the fixed diagonal plane. -/
def diagonalPlaneEdges (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) : Finset (PositiveEdge d) :=
  Λ.dynamicEdges.filter fun e =>
    diagonalHeight τ σ k e.source = 0 ∧
      diagonalHeight τ σ k e.target = 0

/-- One representative from every non-plane reflected dynamic-edge pair. -/
def diagonalPositiveEdges (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) : Finset (PositiveEdge d) :=
  Λ.dynamicEdges.filter fun e =>
    0 ≤ diagonalHeight τ σ k e.source ∧
      0 ≤ diagonalHeight τ σ k e.target ∧
      ¬(diagonalHeight τ σ k e.source = 0 ∧
        diagonalHeight τ σ k e.target = 0)

/-- Height increment of one positive coordinate step relative to the
diagonal plane. -/
def diagonalDirectionIncrement (τ σ i : Fin d) : ℤ :=
  if i = τ then 1 else if i = σ then -1 else 0

omit [Group G] in
theorem diagonalHeight_step_forward {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ)
    (x : Site d) (i : Fin d) :
    diagonalHeight τ σ k (step x (.forward i)) =
      diagonalHeight τ σ k x + diagonalDirectionIncrement τ σ i := by
  unfold diagonalHeight diagonalDirectionIncrement
  simp only [step, SignedDirection.delta_forward]
  by_cases hiτ : i = τ
  · subst i
    simp [unitVector, hτσ.symm]
    ring
  · by_cases hiσ : i = σ
    · subst i
      simp [unitVector, hτσ, hτσ.symm]
      ring
    · simp [unitVector, hiτ, hiσ, Ne.symm hiτ, Ne.symm hiσ]

omit [Group G] in
@[simp]
theorem diagonalDirectionIncrement_eq_one_iff {τ σ : Fin d}
    (hτσ : τ ≠ σ) (i : Fin d) :
    diagonalDirectionIncrement τ σ i = 1 ↔ i = τ := by
  unfold diagonalDirectionIncrement
  by_cases hiτ : i = τ
  · simp [hiτ]
  · by_cases hiσ : i = σ
    · simp [hiτ, hiσ]
    · simp [hiτ, hiσ]

omit [Group G] in
@[simp]
theorem diagonalDirectionIncrement_eq_neg_one_iff {τ σ : Fin d}
    (hτσ : τ ≠ σ) (i : Fin d) :
    diagonalDirectionIncrement τ σ i = -1 ↔ i = σ := by
  unfold diagonalDirectionIncrement
  by_cases hiτ : i = τ
  · subst i
    simp [hτσ]
  · by_cases hiσ : i = σ
    · subst i
      simp [diagonalDirectionIncrement, hτσ.symm]
    · simp [hiτ, hiσ]

omit [Group G] in
@[simp]
theorem diagonalDirectionIncrement_eq_zero_iff {τ σ : Fin d}
    (hτσ : τ ≠ σ) (i : Fin d) :
    diagonalDirectionIncrement τ σ i = 0 ↔ i ≠ τ ∧ i ≠ σ := by
  unfold diagonalDirectionIncrement
  by_cases hiτ : i = τ
  · simp [hiτ]
  · by_cases hiσ : i = σ
    · subst i
      simp [diagonalDirectionIncrement, hτσ.symm]
    · simp [hiτ, hiσ]

omit [Group G] in
theorem diagonalDirectionIncrement_cases {τ σ : Fin d}
    (hτσ : τ ≠ σ) (i : Fin d) :
    diagonalDirectionIncrement τ σ i = 1 ∨
      diagonalDirectionIncrement τ σ i = -1 ∨
      diagonalDirectionIncrement τ σ i = 0 := by
  by_cases hiτ : i = τ
  · exact Or.inl ((diagonalDirectionIncrement_eq_one_iff hτσ i).2 hiτ)
  · by_cases hiσ : i = σ
    · exact Or.inr <| Or.inl <|
        (diagonalDirectionIncrement_eq_neg_one_iff hτσ i).2 hiσ
    · exact Or.inr <| Or.inr <|
        (diagonalDirectionIncrement_eq_zero_iff hτσ i).2 ⟨hiτ, hiσ⟩

omit [Group G] in
@[simp]
theorem diagonalDirectionIncrement_swap {τ σ : Fin d} (hτσ : τ ≠ σ)
    (i : Fin d) :
    diagonalDirectionIncrement τ σ (Equiv.swap τ σ i) =
      -diagonalDirectionIncrement τ σ i := by
  by_cases hiτ : i = τ
  · subst i
    simp [diagonalDirectionIncrement, hτσ.symm]
  · by_cases hiσ : i = σ
    · subst i
      simp [diagonalDirectionIncrement, hτσ.symm]
    · simp [diagonalDirectionIncrement, Equiv.swap_apply_def, hiτ, hiσ,
        hτσ, hτσ.symm]

/-- All four vertices of a plaquette lie in the closed positive diagonal
half-lattice. -/
def DiagonalPlaquetteNonnegative (τ σ : Fin d) (k : ℤ)
    (p : Plaquette d) : Prop :=
  0 ≤ diagonalHeight τ σ k p.base ∧
    0 ≤ diagonalHeight τ σ k (step p.base (.forward p.first)) ∧
    0 ≤ diagonalHeight τ σ k (step p.base (.forward p.second)) ∧
    0 ≤ diagonalHeight τ σ k
      (step (step p.base (.forward p.first)) (.forward p.second))

omit [Group G] in
theorem diagonalPlaquetteNonnegative_iff {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (p : Plaquette d) :
    DiagonalPlaquetteNonnegative τ σ k p ↔
      0 ≤ diagonalHeight τ σ k p.base ∧
      0 ≤ diagonalHeight τ σ k p.base +
        diagonalDirectionIncrement τ σ p.first ∧
      0 ≤ diagonalHeight τ σ k p.base +
        diagonalDirectionIncrement τ σ p.second ∧
      0 ≤ diagonalHeight τ σ k p.base +
        diagonalDirectionIncrement τ σ p.first +
        diagonalDirectionIncrement τ σ p.second := by
  unfold DiagonalPlaquetteNonnegative
  rw [diagonalHeight_step_forward hτσ, diagonalHeight_step_forward hτσ,
    diagonalHeight_step_forward hτσ, diagonalHeight_step_forward hτσ]

omit [Group G] in
theorem diagonalPlaquetteNonnegative_reflect_iff {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (p : Plaquette d) :
    DiagonalPlaquetteNonnegative τ σ k (p.diagonalReflect τ σ k) ↔
      diagonalHeight τ σ k p.base ≤ 0 ∧
      diagonalHeight τ σ k p.base +
          diagonalDirectionIncrement τ σ p.first ≤ 0 ∧
      diagonalHeight τ σ k p.base +
          diagonalDirectionIncrement τ σ p.second ≤ 0 ∧
      diagonalHeight τ σ k p.base +
          diagonalDirectionIncrement τ σ p.first +
          diagonalDirectionIncrement τ σ p.second ≤ 0 := by
  rw [diagonalPlaquetteNonnegative_iff hτσ]
  simp only [Plaquette.diagonalReflect, diagonalHeight_reflect hτσ,
    diagonalDirectionIncrement_swap hτσ]
  omega

omit [Group G] in
theorem diagonalPlanePredicate_reflect_iff {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (p : Plaquette d) :
    (diagonalHeight τ σ k (p.diagonalReflect τ σ k).base = 0 ∧
        diagonalDirectionIncrement τ σ (p.diagonalReflect τ σ k).first = 0 ∧
        diagonalDirectionIncrement τ σ (p.diagonalReflect τ σ k).second = 0) ↔
      (diagonalHeight τ σ k p.base = 0 ∧
        diagonalDirectionIncrement τ σ p.first = 0 ∧
        diagonalDirectionIncrement τ σ p.second = 0) := by
  simp only [Plaquette.diagonalReflect, diagonalHeight_reflect hτσ,
    diagonalDirectionIncrement_swap hτσ]
  omega

omit [Group G] in
theorem diagonalCutPredicate_reflect_iff {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (p : Plaquette d) :
    (diagonalHeight τ σ k (p.diagonalReflect τ σ k).base = 0 ∧
        (((p.diagonalReflect τ σ k).first = τ ∧
            (p.diagonalReflect τ σ k).second = σ) ∨
          ((p.diagonalReflect τ σ k).first = σ ∧
            (p.diagonalReflect τ σ k).second = τ))) ↔
      (diagonalHeight τ σ k p.base = 0 ∧
        ((p.first = τ ∧ p.second = σ) ∨
          (p.first = σ ∧ p.second = τ))) := by
  simp only [Plaquette.diagonalReflect, diagonalHeight_reflect hτσ]
  constructor
  · rintro ⟨hbase, h | h⟩
    · refine ⟨by omega, Or.inr ?_⟩
      exact ⟨by simpa using congrArg (Equiv.swap τ σ) h.1,
        by simpa using congrArg (Equiv.swap τ σ) h.2⟩
    · refine ⟨by omega, Or.inl ?_⟩
      exact ⟨by simpa using congrArg (Equiv.swap τ σ) h.1,
        by simpa using congrArg (Equiv.swap τ σ) h.2⟩
  · rintro ⟨hbase, h | h⟩
    · exact ⟨by omega, Or.inr ⟨by simp [h.1], by simp [h.2]⟩⟩
    · exact ⟨by omega, Or.inl ⟨by simp [h.1], by simp [h.2]⟩⟩

/-- Plaquettes lying entirely in the fixed diagonal plane. -/
def diagonalPlanePlaquettes (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) : Finset (Plaquette d) :=
  Λ.activePlaquettes.filter fun p =>
    diagonalHeight τ σ k p.base = 0 ∧
      diagonalDirectionIncrement τ σ p.first = 0 ∧
      diagonalDirectionIncrement τ σ p.second = 0

/-- Plaquettes wholly in the closed positive half, excluding the fixed
plane. -/
def diagonalPositivePlaquettes (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) : Finset (Plaquette d) :=
  by
    classical
    exact Λ.activePlaquettes.filter fun p =>
      DiagonalPlaquetteNonnegative τ σ k p ∧
        ¬(diagonalHeight τ σ k p.base = 0 ∧
          diagonalDirectionIncrement τ σ p.first = 0 ∧
          diagonalDirectionIncrement τ σ p.second = 0)

/-- Plaquettes cut genuinely through the diagonal plane.  Their two axes are
the exchanged axes and their base lies in the plane. -/
def diagonalCutPlaquettes (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) : Finset (Plaquette d) :=
  Λ.activePlaquettes.filter fun p =>
    diagonalHeight τ σ k p.base = 0 ∧
      ((p.first = τ ∧ p.second = σ) ∨
        (p.first = σ ∧ p.second = τ))

/-- Reflected copy of the chosen strict positive plaquettes. -/
def diagonalNegativePlaquettes (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (hτσ : τ ≠ σ) (k : ℤ) : Finset (Plaquette d) :=
  (Λ.diagonalPositivePlaquettes τ σ k).map
    (Plaquette.diagonalReflectionEquiv τ σ hτσ k).toEmbedding

omit [Group G] in
/-- Every plaquette is either fixed-plane, wholly positive, genuinely cut,
or the reflection of a wholly positive plaquette. -/
theorem diagonalPlaquette_partition_predicates {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (p : Plaquette d) :
    (diagonalHeight τ σ k p.base = 0 ∧
        diagonalDirectionIncrement τ σ p.first = 0 ∧
        diagonalDirectionIncrement τ σ p.second = 0) ∨
      (DiagonalPlaquetteNonnegative τ σ k p ∧
        ¬(diagonalHeight τ σ k p.base = 0 ∧
          diagonalDirectionIncrement τ σ p.first = 0 ∧
          diagonalDirectionIncrement τ σ p.second = 0)) ∨
      (diagonalHeight τ σ k p.base = 0 ∧
        ((p.first = τ ∧ p.second = σ) ∨
          (p.first = σ ∧ p.second = τ))) ∨
      (DiagonalPlaquetteNonnegative τ σ k (p.diagonalReflect τ σ k) ∧
        ¬(diagonalHeight τ σ k (p.diagonalReflect τ σ k).base = 0 ∧
          diagonalDirectionIncrement τ σ
              (p.diagonalReflect τ σ k).first = 0 ∧
          diagonalDirectionIncrement τ σ
              (p.diagonalReflect τ σ k).second = 0)) := by
  by_cases hplane : diagonalHeight τ σ k p.base = 0 ∧
      diagonalDirectionIncrement τ σ p.first = 0 ∧
      diagonalDirectionIncrement τ σ p.second = 0
  · exact Or.inl hplane
  by_cases hplus : DiagonalPlaquetteNonnegative τ σ k p
  · exact Or.inr <| Or.inl ⟨hplus, hplane⟩
  by_cases hminus :
      DiagonalPlaquetteNonnegative τ σ k (p.diagonalReflect τ σ k)
  · exact Or.inr <| Or.inr <| Or.inr ⟨hminus, fun hrefplane =>
      hplane ((diagonalPlanePredicate_reflect_iff hτσ k p).mp hrefplane)⟩
  right
  right
  left
  rw [diagonalPlaquetteNonnegative_iff hτσ] at hplus
  rw [diagonalPlaquetteNonnegative_reflect_iff hτσ] at hminus
  rcases diagonalDirectionIncrement_cases hτσ p.first with hfirst | hfirst | hfirst <;>
    rcases diagonalDirectionIncrement_cases hτσ p.second with
      hsecond | hsecond | hsecond
  · have heq : p.first = p.second := by
      rw [(diagonalDirectionIncrement_eq_one_iff hτσ _).mp hfirst,
        (diagonalDirectionIncrement_eq_one_iff hτσ _).mp hsecond]
    exact False.elim (p.distinct heq)
  · refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩
    · rw [hfirst, hsecond] at hplus hminus
      omega
    · exact (diagonalDirectionIncrement_eq_one_iff hτσ _).mp hfirst
    · exact (diagonalDirectionIncrement_eq_neg_one_iff hτσ _).mp hsecond
  · rw [hfirst, hsecond] at hplus hminus
    omega
  · refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
    · rw [hfirst, hsecond] at hplus hminus
      omega
    · exact (diagonalDirectionIncrement_eq_neg_one_iff hτσ _).mp hfirst
    · exact (diagonalDirectionIncrement_eq_one_iff hτσ _).mp hsecond
  · have heq : p.first = p.second := by
      rw [(diagonalDirectionIncrement_eq_neg_one_iff hτσ _).mp hfirst,
        (diagonalDirectionIncrement_eq_neg_one_iff hτσ _).mp hsecond]
    exact False.elim (p.distinct heq)
  · rw [hfirst, hsecond] at hplus hminus
    omega
  · rw [hfirst, hsecond] at hplus hminus
    omega
  · rw [hfirst, hsecond] at hplus hminus
    omega
  · rw [hfirst, hsecond] at hplus hminus
    omega

omit [Group G] in
@[simp]
theorem mem_diagonalNegativePlaquettes
    (Λ : FiniteSpecification d G) {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (p : Plaquette d) :
    p ∈ Λ.diagonalNegativePlaquettes τ σ hτσ k ↔
      p.diagonalReflect τ σ k ∈ Λ.diagonalPositivePlaquettes τ σ k := by
  classical
  rw [diagonalNegativePlaquettes, Finset.mem_map_equiv]
  rfl

omit [Group G] in
theorem diagonalReflect_mem_diagonalPlanePlaquettes_iff
    (Λ : FiniteSpecification d G) {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k) (p : Plaquette d) :
    p.diagonalReflect τ σ k ∈ Λ.diagonalPlanePlaquettes τ σ k ↔
      p ∈ Λ.diagonalPlanePlaquettes τ σ k := by
  classical
  simp only [diagonalPlanePlaquettes, Finset.mem_filter]
  rw [(hΛ.2.2.1 p).symm, diagonalPlanePredicate_reflect_iff hτσ]

omit [Group G] in
theorem diagonalReflect_mem_diagonalCutPlaquettes_iff
    (Λ : FiniteSpecification d G) {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k) (p : Plaquette d) :
    p.diagonalReflect τ σ k ∈ Λ.diagonalCutPlaquettes τ σ k ↔
      p ∈ Λ.diagonalCutPlaquettes τ σ k := by
  classical
  simp only [diagonalCutPlaquettes, Finset.mem_filter]
  rw [(hΛ.2.2.1 p).symm, diagonalCutPredicate_reflect_iff hτσ]

omit [Group G] in
theorem diagonalPositivePlaquette_reflect_exclusive
    (Λ : FiniteSpecification d G) {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (p : Plaquette d)
    (hp : p ∈ Λ.diagonalPositivePlaquettes τ σ k) :
    p.diagonalReflect τ σ k ∉ Λ.diagonalPositivePlaquettes τ σ k := by
  classical
  intro href
  have hpdata := (Finset.mem_filter.mp hp).2
  have hrefdata := (Finset.mem_filter.mp href).2
  rw [diagonalPlaquetteNonnegative_iff hτσ] at hpdata
  rw [diagonalPlaquetteNonnegative_reflect_iff hτσ] at hrefdata
  exact hpdata.2 (by omega)

omit [Group G] in
theorem diagonalCutPlaquette_not_positive
    (Λ : FiniteSpecification d G) {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (p : Plaquette d)
    (hp : p ∈ Λ.diagonalCutPlaquettes τ σ k) :
    p ∉ Λ.diagonalPositivePlaquettes τ σ k ∧
      p.diagonalReflect τ σ k ∉ Λ.diagonalPositivePlaquettes τ σ k := by
  classical
  have hcut := (Finset.mem_filter.mp hp).2
  constructor
  · intro hplus
    have hn := (Finset.mem_filter.mp hplus).2.1
    rw [diagonalPlaquetteNonnegative_iff hτσ] at hn
    rcases hcut.2 with haxes | haxes <;>
      simp [hcut.1, haxes.1, haxes.2, diagonalDirectionIncrement,
        hτσ, hτσ.symm] at hn
  · intro hplus
    have hn := (Finset.mem_filter.mp hplus).2.1
    rw [diagonalPlaquetteNonnegative_reflect_iff hτσ] at hn
    rcases hcut.2 with haxes | haxes <;>
      simp [hcut.1, haxes.1, haxes.2, diagonalDirectionIncrement,
        hτσ, hτσ.symm] at hn

omit [Group G] in
theorem diagonalPlanePlaquette_exclusive
    (Λ : FiniteSpecification d G) {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (p : Plaquette d)
    (hp : p ∈ Λ.diagonalPlanePlaquettes τ σ k) :
    p ∉ Λ.diagonalPositivePlaquettes τ σ k ∧
      p ∉ Λ.diagonalCutPlaquettes τ σ k ∧
      p.diagonalReflect τ σ k ∉ Λ.diagonalPositivePlaquettes τ σ k := by
  classical
  have hplane := (Finset.mem_filter.mp hp).2
  constructor
  · intro hplus
    exact (Finset.mem_filter.mp hplus).2.2 hplane
  constructor
  · intro hcut
    have haxes := (Finset.mem_filter.mp hcut).2.2
    rcases haxes with haxes | haxes
    · have hinc := hplane.2.1
      simp [haxes.1, diagonalDirectionIncrement] at hinc
    · have hinc := hplane.2.1
      simp [haxes.1, diagonalDirectionIncrement, hτσ.symm] at hinc
  · intro hplus
    have hrefplane :
        diagonalHeight τ σ k (p.diagonalReflect τ σ k).base = 0 ∧
          diagonalDirectionIncrement τ σ
              (p.diagonalReflect τ σ k).first = 0 ∧
          diagonalDirectionIncrement τ σ
              (p.diagonalReflect τ σ k).second = 0 :=
      (diagonalPlanePredicate_reflect_iff hτσ k p).2 hplane
    exact (Finset.mem_filter.mp hplus).2.2 hrefplane

omit [Group G] in
/-- Exact four-way partition of the active plaquettes. -/
theorem activePlaquettes_eq_diagonal_union
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) :
    Λ.activePlaquettes =
      Λ.diagonalPlanePlaquettes τ σ k ∪
        (Λ.diagonalPositivePlaquettes τ σ k ∪
          (Λ.diagonalCutPlaquettes τ σ k ∪
            Λ.diagonalNegativePlaquettes τ σ hΛ.1 k)) := by
  classical
  ext p
  simp only [Finset.mem_union, mem_diagonalNegativePlaquettes]
  constructor
  · intro hp
    rcases diagonalPlaquette_partition_predicates hΛ.1 k p with
      hplane | hplus | hcut | hminus
    · exact Or.inl (Finset.mem_filter.mpr ⟨hp, hplane⟩)
    · exact Or.inr <| Or.inl (Finset.mem_filter.mpr ⟨hp, hplus⟩)
    · exact Or.inr <| Or.inr <| Or.inl
        (Finset.mem_filter.mpr ⟨hp, hcut⟩)
    · exact Or.inr <| Or.inr <| Or.inr <|
        Finset.mem_filter.mpr ⟨(hΛ.2.2.1 p).mp hp, hminus⟩
  · rintro (hp | hp | hp | hp)
    · exact (Finset.mem_filter.mp hp).1
    · exact (Finset.mem_filter.mp hp).1
    · exact (Finset.mem_filter.mp hp).1
    · exact (hΛ.2.2.1 p).mpr (Finset.mem_filter.mp hp).1

omit [Group G] in
theorem diagonalPlanePlaquettes_disjoint_diagonalSides
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) :
    Disjoint (Λ.diagonalPlanePlaquettes τ σ k)
      (Λ.diagonalPositivePlaquettes τ σ k ∪
        (Λ.diagonalCutPlaquettes τ σ k ∪
          Λ.diagonalNegativePlaquettes τ σ hΛ.1 k)) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hside
  rw [Finset.mem_union, Finset.mem_union, mem_diagonalNegativePlaquettes]
    at hside
  have hex := Λ.diagonalPlanePlaquette_exclusive hΛ.1 k p hp
  exact hside.elim hex.1 fun h => h.elim hex.2.1 hex.2.2

omit [Group G] in
theorem diagonalPositivePlaquettes_disjoint_cutNegative
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) :
    Disjoint (Λ.diagonalPositivePlaquettes τ σ k)
      (Λ.diagonalCutPlaquettes τ σ k ∪
        Λ.diagonalNegativePlaquettes τ σ hΛ.1 k) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hside
  rw [Finset.mem_union, mem_diagonalNegativePlaquettes] at hside
  exact hside.elim
    (fun hcut => (Λ.diagonalCutPlaquette_not_positive hΛ.1 k p hcut).1 hp)
    (Λ.diagonalPositivePlaquette_reflect_exclusive hΛ.1 k p hp)

omit [Group G] in
theorem diagonalCutPlaquettes_disjoint_negative
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) :
    Disjoint (Λ.diagonalCutPlaquettes τ σ k)
      (Λ.diagonalNegativePlaquettes τ σ hΛ.1 k) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hneg
  rw [mem_diagonalNegativePlaquettes] at hneg
  exact (Λ.diagonalCutPlaquette_not_positive hΛ.1 k p hp).2 hneg

omit [Group G] in
theorem diagonalHeight_source_edge_reflect {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (e : PositiveEdge d) :
    diagonalHeight τ σ k (e.diagonalReflect τ σ k).source =
      -diagonalHeight τ σ k e.source := by
  simp [diagonalHeight_reflect hτσ]

omit [Group G] in
theorem diagonalHeight_target_edge_reflect {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (e : PositiveEdge d) :
    diagonalHeight τ σ k (e.diagonalReflect τ σ k).target =
      -diagonalHeight τ σ k e.target := by
  rw [PositiveEdge.target_diagonalReflect hτσ]
  exact diagonalHeight_reflect hτσ k e.target

omit [Group G] in
theorem diagonalPlaneEdge_reflect_iff {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (e : PositiveEdge d) :
    (diagonalHeight τ σ k (e.diagonalReflect τ σ k).source = 0 ∧
        diagonalHeight τ σ k (e.diagonalReflect τ σ k).target = 0) ↔
      (diagonalHeight τ σ k e.source = 0 ∧
        diagonalHeight τ σ k e.target = 0) := by
  rw [diagonalHeight_source_edge_reflect hτσ,
    diagonalHeight_target_edge_reflect hτσ]
  omega

omit [Group G] in
theorem edge_diagonalHeight_adjacent {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ)
    (e : PositiveEdge d) :
    |diagonalHeight τ σ k e.target - diagonalHeight τ σ k e.source| ≤ 1 := by
  rcases e with ⟨x, i⟩
  unfold PositiveEdge.target diagonalHeight
  simp only [step, SignedDirection.delta_forward]
  by_cases hiτ : i = τ
  · subst i
    simp [unitVector, hτσ.symm]
  · by_cases hiσ : i = σ
    · subst i
      simp [unitVector, hτσ]
    · have hτi : τ ≠ i := Ne.symm hiτ
      have hσi : σ ≠ i := Ne.symm hiσ
      simp [unitVector, hτi, hσi]

omit [Group G] in
theorem edge_diagonal_side_trichotomy {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (e : PositiveEdge d) :
    (diagonalHeight τ σ k e.source = 0 ∧
        diagonalHeight τ σ k e.target = 0) ∨
      (0 ≤ diagonalHeight τ σ k e.source ∧
        0 ≤ diagonalHeight τ σ k e.target ∧
        ¬(diagonalHeight τ σ k e.source = 0 ∧
          diagonalHeight τ σ k e.target = 0)) ∨
      (0 ≤ diagonalHeight τ σ k (e.diagonalReflect τ σ k).source ∧
        0 ≤ diagonalHeight τ σ k (e.diagonalReflect τ σ k).target ∧
        ¬(diagonalHeight τ σ k (e.diagonalReflect τ σ k).source = 0 ∧
          diagonalHeight τ σ k (e.diagonalReflect τ σ k).target = 0)) := by
  have hadj := abs_le.mp (edge_diagonalHeight_adjacent hτσ k e)
  rw [diagonalHeight_source_edge_reflect hτσ,
    diagonalHeight_target_edge_reflect hτσ]
  omega

/-- The reflected diagonal-plane/negative/positive labels. -/
abbrev DiagonalReflectedLabel (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) :=
  (Λ.diagonalPlaneEdges τ σ k) ⊕
    ((Λ.diagonalPositiveEdges τ σ k) ⊕
      (Λ.diagonalPositiveEdges τ σ k))

omit [Group G] in
theorem diagonalReflect_mem_diagonalPlaneEdges_iff
    (Λ : FiniteSpecification d G) {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k) (e : PositiveEdge d) :
    e.diagonalReflect τ σ k ∈ Λ.diagonalPlaneEdges τ σ k ↔
      e ∈ Λ.diagonalPlaneEdges τ σ k := by
  simp only [diagonalPlaneEdges, Finset.mem_filter]
  rw [(hΛ.2.1 e).symm, diagonalPlaneEdge_reflect_iff hτσ]

omit [Group G] in
theorem diagonalReflect_not_mem_diagonalPositiveEdges
    (Λ : FiniteSpecification d G) {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (e : Λ.diagonalPositiveEdges τ σ k) :
    e.1.diagonalReflect τ σ k ∉ Λ.diagonalPositiveEdges τ σ k := by
  intro href
  obtain ⟨_, hs, ht, hnot⟩ := Finset.mem_filter.mp e.2
  obtain ⟨_, hrs, hrt, _⟩ := Finset.mem_filter.mp href
  rw [diagonalHeight_source_edge_reflect hτσ] at hrs
  rw [diagonalHeight_target_edge_reflect hτσ] at hrt
  exact hnot ⟨by omega, by omega⟩

/-- The geometric inverse of the diagonal three-way edge labelling. -/
def diagonalEdgeLabelInv (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k) :
    DiagonalReflectedLabel Λ τ σ k → Λ.dynamicEdges
  | Sum.inl e => ⟨e.1, (Finset.mem_filter.mp e.2).1⟩
  | Sum.inr (Sum.inl e) =>
      ⟨e.1.diagonalReflect τ σ k,
        (hΛ.2.1 e.1).mp (Finset.mem_filter.mp e.2).1⟩
  | Sum.inr (Sum.inr e) => ⟨e.1, (Finset.mem_filter.mp e.2).1⟩

omit [Group G] in
@[simp]
theorem diagonalEdgeLabelInv_plane (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k)
    (e : Λ.diagonalPlaneEdges τ σ k) :
    Λ.diagonalEdgeLabelInv τ σ k hΛ (Sum.inl e) =
      ⟨e.1, (Finset.mem_filter.mp e.2).1⟩ := rfl

omit [Group G] in
@[simp]
theorem diagonalEdgeLabelInv_negative (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k)
    (e : Λ.diagonalPositiveEdges τ σ k) :
    Λ.diagonalEdgeLabelInv τ σ k hΛ (Sum.inr (Sum.inl e)) =
      ⟨e.1.diagonalReflect τ σ k,
        (hΛ.2.1 e.1).mp (Finset.mem_filter.mp e.2).1⟩ := rfl

omit [Group G] in
@[simp]
theorem diagonalEdgeLabelInv_negative_val (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k)
    (e : Λ.diagonalPositiveEdges τ σ k) :
    (Λ.diagonalEdgeLabelInv τ σ k hΛ (Sum.inr (Sum.inl e))).1 =
      e.1.diagonalReflect τ σ k := rfl

omit [Group G] in
@[simp]
theorem diagonalEdgeLabelInv_positive (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k)
    (e : Λ.diagonalPositiveEdges τ σ k) :
    Λ.diagonalEdgeLabelInv τ σ k hΛ (Sum.inr (Sum.inr e)) =
      ⟨e.1, (Finset.mem_filter.mp e.2).1⟩ := rfl

/-- Dynamic edges are exactly plane edges and two reflected strict sides. -/
def diagonalEdgeLabelEquiv (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k) :
    Λ.dynamicEdges ≃ DiagonalReflectedLabel Λ τ σ k where
  toFun e :=
    if hplane : e.1 ∈ Λ.diagonalPlaneEdges τ σ k then
      Sum.inl ⟨e.1, hplane⟩
    else if hplus : e.1 ∈ Λ.diagonalPositiveEdges τ σ k then
      Sum.inr (Sum.inr ⟨e.1, hplus⟩)
    else
      Sum.inr (Sum.inl ⟨e.1.diagonalReflect τ σ k, by
        rw [diagonalPositiveEdges, Finset.mem_filter]
        have hdyn : e.1.diagonalReflect τ σ k ∈ Λ.dynamicEdges :=
          (hΛ.2.1 e.1).mp e.2
        refine ⟨hdyn, ?_⟩
        have htri := edge_diagonal_side_trichotomy hΛ.1 k e.1
        rcases htri with hp | hp | hp
        · exact False.elim <| hplane (Finset.mem_filter.mpr ⟨e.2, hp⟩)
        · exact False.elim <| hplus (Finset.mem_filter.mpr ⟨e.2, hp⟩)
        · exact hp⟩)
  invFun := Λ.diagonalEdgeLabelInv τ σ k hΛ
  left_inv e := by
    dsimp
    split_ifs with hplane hplus
    · rfl
    · rfl
    · apply Subtype.ext
      change (Λ.diagonalEdgeLabelInv τ σ k hΛ
        (Sum.inr (Sum.inl ⟨e.1.diagonalReflect τ σ k, _⟩))).1 = e.1
      rw [diagonalEdgeLabelInv_negative_val]
      exact PositiveEdge.diagonalReflect_diagonalReflect hΛ.1 k e.1
  right_inv label := by
    rcases label with e | e
    · simp only [diagonalEdgeLabelInv_plane]
      rw [dif_pos e.2]
    · rcases e with e | e
      · simp only [diagonalEdgeLabelInv_negative]
        have hnotplane : e.1.diagonalReflect τ σ k ∉
            Λ.diagonalPlaneEdges τ σ k := by
          intro hp
          have href := diagonalReflect_mem_diagonalPlaneEdges_iff
            Λ hΛ.1 k hΛ e.1
          exact (Finset.mem_filter.mp e.2).2.2.2
            (Finset.mem_filter.mp (href.mp hp)).2
        have hnotplus :=
          diagonalReflect_not_mem_diagonalPositiveEdges Λ hΛ.1 k e
        rw [dif_neg hnotplane, dif_neg hnotplus]
        apply congrArg (fun x => Sum.inr (Sum.inl x))
        apply Subtype.ext
        exact PositiveEdge.diagonalReflect_diagonalReflect hΛ.1 k e.1
      · simp only [diagonalEdgeLabelInv_positive]
        rw [dif_neg]
        · rw [dif_pos e.2]
        · intro hp
          exact (Finset.mem_filter.mp e.2).2.2.2
            (Finset.mem_filter.mp hp).2

omit [Group G] in
theorem diagonalBridge_step_forward_comm (x : Site d) (i j : Fin d) :
    step (step x (.forward i)) (.forward j) =
      step (step x (.forward j)) (.forward i) := by
  simp only [step, SignedDirection.delta_forward]
  abel

omit [Group G] in
/-- Every stored edge read by a nonnegative plaquette has both endpoints in
the nonnegative half-lattice. -/
theorem diagonalPlaquetteNonnegative_edgeSupport {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (p : Plaquette d)
    (hp : DiagonalPlaquetteNonnegative τ σ k p)
    (e : PositiveEdge d) (he : e ∈ p.boundary.edgeSupport) :
    0 ≤ diagonalHeight τ σ k e.source ∧
      0 ≤ diagonalHeight τ σ k e.target := by
  rw [diagonalBridge_plaquette_boundary_edgeSupport] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases hp with ⟨hbase, hfirst, hsecond, hcorner⟩
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨hbase, hfirst⟩
  · exact ⟨hfirst, hcorner⟩
  · refine ⟨hsecond, ?_⟩
    rw [PositiveEdge.target, diagonalBridge_step_forward_comm]
    exact hcorner
  · exact ⟨hbase, hsecond⟩

omit [Group G] in
/-- Every stored edge read by a plane plaquette lies in the fixed plane. -/
theorem diagonalPlanePlaquette_edgeSupport {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (p : Plaquette d)
    (hp : diagonalHeight τ σ k p.base = 0 ∧
      diagonalDirectionIncrement τ σ p.first = 0 ∧
      diagonalDirectionIncrement τ σ p.second = 0)
    (e : PositiveEdge d) (he : e ∈ p.boundary.edgeSupport) :
    diagonalHeight τ σ k e.source = 0 ∧
      diagonalHeight τ σ k e.target = 0 := by
  have hfirst := diagonalHeight_step_forward hτσ k p.base p.first
  have hsecond := diagonalHeight_step_forward hτσ k p.base p.second
  have hcorner := diagonalHeight_step_forward hτσ k
    (step p.base (.forward p.first)) p.second
  rw [hfirst, hp.1, hp.2.1, hp.2.2] at hcorner
  rw [diagonalBridge_plaquette_boundary_edgeSupport] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · change diagonalHeight τ σ k p.base = 0 ∧
      diagonalHeight τ σ k (step p.base (.forward p.first)) = 0
    exact ⟨hp.1, by omega⟩
  · change diagonalHeight τ σ k (step p.base (.forward p.first)) = 0 ∧
      diagonalHeight τ σ k
        (step (step p.base (.forward p.first)) (.forward p.second)) = 0
    exact ⟨by omega, by omega⟩
  · change diagonalHeight τ σ k (step p.base (.forward p.second)) = 0 ∧
      diagonalHeight τ σ k
        (step (step p.base (.forward p.second)) (.forward p.first)) = 0
    refine ⟨by omega, ?_⟩
    rw [diagonalBridge_step_forward_comm]
    omega
  · change diagonalHeight τ σ k p.base = 0 ∧
      diagonalHeight τ σ k (step p.base (.forward p.second)) = 0
    exact ⟨hp.1, by omega⟩

omit [Group G] in
/-- Diagonal reflection carries the four stored boundary edges of a
plaquette to the boundary edges of the reflected plaquette. -/
theorem diagonalReflect_mem_plaquette_boundary_of_mem
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ)
    (e : PositiveEdge d) (p : Plaquette d)
    (he : e ∈ p.boundary.edgeSupport) :
    e.diagonalReflect τ σ k ∈
      (p.diagonalReflect τ σ k).boundary.edgeSupport := by
  rw [diagonalBridge_plaquette_boundary_edgeSupport] at he ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
  rcases he with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr <| Or.inl <| by
      simp only [PositiveEdge.diagonalReflect, Plaquette.diagonalReflect]
      congr 1
      exact diagonalReflection_step hτσ k p.base (.forward p.first)
  · exact Or.inr <| Or.inr <| Or.inl <| by
      simp only [PositiveEdge.diagonalReflect, Plaquette.diagonalReflect]
      congr 1
      exact diagonalReflection_step hτσ k p.base (.forward p.second)
  · exact Or.inr <| Or.inr <| Or.inr rfl

omit [Group G] in
theorem diagonalReflect_mem_plaquette_boundary_iff
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ)
    (e : PositiveEdge d) (p : Plaquette d) :
    e.diagonalReflect τ σ k ∈
        (p.diagonalReflect τ σ k).boundary.edgeSupport ↔
      e ∈ p.boundary.edgeSupport := by
  constructor
  · intro he
    have href := diagonalReflect_mem_plaquette_boundary_of_mem hτσ k
      (e.diagonalReflect τ σ k) (p.diagonalReflect τ σ k) he
    rw [PositiveEdge.diagonalReflect_diagonalReflect hτσ,
      Plaquette.diagonalReflect_diagonalReflect hτσ] at href
    exact href
  · exact diagonalReflect_mem_plaquette_boundary_of_mem hτσ k e p

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Assemble plane and two strict-side fields into concrete dynamic labels. -/
def diagonalAssemble (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k) :
    C(DiagonalReflection.ReflectedConfiguration G
        (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k),
      DynamicConfiguration Λ) where
  toFun U e := match Λ.diagonalEdgeLabelEquiv τ σ k hΛ e with
    | Sum.inl o => U.1 o
    | Sum.inr (Sum.inl p) => U.2.1 p
    | Sum.inr (Sum.inr p) => U.2.2 p
  continuous_toFun := by
    apply continuous_pi
    intro e
    generalize hlabel : Λ.diagonalEdgeLabelEquiv τ σ k hΛ e = label
    rcases label with o | p
    · simpa [hlabel] using
        (continuous_apply o).comp (continuous_fst : Continuous fun U :
          DiagonalReflection.ReflectedConfiguration G
            (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k) => U.1)
    · rcases p with p | p
      · simpa [hlabel] using
          (continuous_apply p).comp (continuous_fst.comp continuous_snd)
      · simpa [hlabel] using
          (continuous_apply p).comp (continuous_snd.comp continuous_snd)

/-- Evaluate a positive half field by filling the negative side with `1`. -/
def diagonalEvaluatePositive (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k) :
    C(DiagonalReflection.HalfConfiguration G
        (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k),
      Configuration d G) :=
  (⟨Λ.evaluate, Λ.continuous_evaluate⟩ : C(DynamicConfiguration Λ,
    Configuration d G)).comp <|
    (Λ.diagonalAssemble τ σ k hΛ).comp
      { toFun := fun U => (U.1, (1, U.2))
        continuous_toFun := by fun_prop }

/-- Evaluate only the common diagonal-plane variables. -/
def diagonalEvaluatePlane (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k) :
    C(DiagonalReflection.PlaneConfiguration G
        (Λ.diagonalPlaneEdges τ σ k), Configuration d G) :=
  (⟨Λ.evaluate, Λ.continuous_evaluate⟩ : C(DynamicConfiguration Λ,
    Configuration d G)).comp <|
    (Λ.diagonalAssemble τ σ k hΛ).comp
      { toFun := fun Uzero => (Uzero, (1, 1))
        continuous_toFun := by fun_prop }

/-- Wilson action contributed by plaquettes wholly in one closed diagonal
half-lattice. -/
def diagonalPositiveAction (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k)
    {n : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G n) :
    C(DiagonalReflection.HalfConfiguration G
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k), ℝ) where
  toFun U := ∑ p ∈ Λ.diagonalPositivePlaquettes τ σ k,
    ρ.wilsonPotential (holonomy (Λ.diagonalEvaluatePositive τ σ k hΛ U)
      p.boundary)
  continuous_toFun := by
    apply continuous_finsetSum
    intro p _hp
    exact ρ.wilsonPotential.toContinuousMap.continuous.comp <|
      (continuous_holonomy p.boundary).comp
        (Λ.diagonalEvaluatePositive τ σ k hΛ).continuous

/-- Wilson action intrinsic to the common fixed diagonal plane. -/
def diagonalPlaneAction (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k)
    {n : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G n) :
    C(DiagonalReflection.PlaneConfiguration G
      (Λ.diagonalPlaneEdges τ σ k), ℝ) where
  toFun Uzero := ∑ p ∈ Λ.diagonalPlanePlaquettes τ σ k,
    ρ.wilsonPotential (holonomy (Λ.diagonalEvaluatePlane τ σ k hΛ Uzero)
      p.boundary)
  continuous_toFun := by
    apply continuous_finsetSum
    intro p _hp
    exact ρ.wilsonPotential.toContinuousMap.continuous.comp <|
      (continuous_holonomy p.boundary).comp
        (Λ.diagonalEvaluatePlane τ σ k hΛ).continuous

/-- Positive-side two-edge half-holonomy of a plaquette cut by the diagonal
plane.  Both orderings of the two axes use the same positive path; the
opposite ordering contributes its inverse, which has the same real Wilson
potential. -/
def diagonalCutHolonomy (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k)
    (p : Λ.diagonalCutPlaquettes τ σ k) :
    C(DiagonalReflection.HalfConfiguration G
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k), G) where
  toFun U :=
    Λ.diagonalEvaluatePositive τ σ k hΛ U ⟨p.1.base, τ⟩ *
      Λ.diagonalEvaluatePositive τ σ k hΛ U
        ⟨step p.1.base (.forward τ), σ⟩
  continuous_toFun :=
    ((continuous_apply (⟨p.1.base, τ⟩ : PositiveEdge d)).comp
      (Λ.diagonalEvaluatePositive τ σ k hΛ).continuous).mul <|
    (continuous_apply
      (⟨step p.1.base (.forward τ), σ⟩ : PositiveEdge d)).comp
        (Λ.diagonalEvaluatePositive τ σ k hΛ).continuous

/-- Concrete diagonal Wilson-action data obtained from the cubic finite
specification. -/
def diagonalWilsonDecomposition (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k)
    {n : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G n) :
    DiagonalReflection.WilsonActionDecomposition G n
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k)
      (Λ.diagonalCutPlaquettes τ σ k) where
  representation := ρ
  positiveAction := Λ.diagonalPositiveAction τ σ k hΛ ρ
  planeAction := Λ.diagonalPlaneAction τ σ k hΛ ρ
  cutHolonomy := Λ.diagonalCutHolonomy τ σ k hΛ

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
theorem diagonalReflect_eq_self_of_mem_diagonalPlaneEdges
    (Λ : FiniteSpecification d G) {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (e : Λ.diagonalPlaneEdges τ σ k) :
    e.1.diagonalReflect τ σ k = e.1 := by
  obtain ⟨_, hs, ht⟩ := Finset.mem_filter.mp e.2
  have hdirτ : e.1.direction ≠ τ := by
    intro h
    have hstep : diagonalHeight τ σ k e.1.target =
        diagonalHeight τ σ k e.1.source + 1 := by
      simpa [PositiveEdge.target, h, diagonalDirectionIncrement] using
        diagonalHeight_step_forward hτσ k e.1.source e.1.direction
    omega
  have hdirσ : e.1.direction ≠ σ := by
    intro h
    have hstep : diagonalHeight τ σ k e.1.target =
        diagonalHeight τ σ k e.1.source - 1 := by
      simpa [PositiveEdge.target, h, diagonalDirectionIncrement, hτσ.symm] using
        diagonalHeight_step_forward hτσ k e.1.source e.1.direction
    omega
  change PositiveEdge.mk (diagonalReflection τ σ k e.1.source)
      (Equiv.swap τ σ e.1.direction) =
    PositiveEdge.mk e.1.source e.1.direction
  congr 1
  · ext i
    by_cases hiτ : i = τ
    · subst i
      rw [diagonalReflection_apply_first]
      unfold diagonalHeight at hs
      omega
    · by_cases hiσ : i = σ
      · subst i
        rw [diagonalReflection_apply_second hτσ]
        unfold diagonalHeight at hs
        omega
      · simp [PositiveEdge.diagonalReflect, diagonalReflection, hiτ, hiσ]
  · simp [Equiv.swap_apply_def, hdirτ, hdirσ]

/-- Swap diagonal strict-side labels and fix plane labels. -/
def diagonalReflectLabel {P O : Type*} :
    O ⊕ (P ⊕ P) → O ⊕ (P ⊕ P)
  | Sum.inl o => Sum.inl o
  | Sum.inr (Sum.inl p) => Sum.inr (Sum.inr p)
  | Sum.inr (Sum.inr p) => Sum.inr (Sum.inl p)

theorem diagonalEdgeLabelEquiv_diagonalReflect
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) (e : Λ.dynamicEdges) :
    Λ.diagonalEdgeLabelEquiv τ σ k hΛ
        ⟨e.1.diagonalReflect τ σ k, (hΛ.2.1 e.1).mp e.2⟩ =
      diagonalReflectLabel (Λ.diagonalEdgeLabelEquiv τ σ k hΛ e) := by
  let E := Λ.diagonalEdgeLabelEquiv τ σ k hΛ
  generalize hlabel : E e = label
  rcases label with o | p
  · have heo : e.1 = o.1 := by
      have he : E.symm (Sum.inl o) = e := by
        apply E.injective
        simp [hlabel]
      have he' := congrArg Subtype.val he
      simpa only [diagonalEdgeLabelEquiv] using he'.symm
    have href : e.1.diagonalReflect τ σ k = e.1 := by
      rw [heo]
      exact diagonalReflect_eq_self_of_mem_diagonalPlaneEdges
        Λ hΛ.1 k o
    have hsub : (⟨e.1.diagonalReflect τ σ k,
        (hΛ.2.1 e.1).mp e.2⟩ : Λ.dynamicEdges) = e := Subtype.ext href
    rw [hsub, hlabel]
    rfl
  · rcases p with p | p
    · have heval : e.1 = p.1.diagonalReflect τ σ k := by
        have he : E.symm (Sum.inr (Sum.inl p)) = e := by
          apply E.injective
          simp [hlabel]
        have he' := congrArg Subtype.val he
        simpa only [diagonalEdgeLabelEquiv] using he'.symm
      have href : e.1.diagonalReflect τ σ k = p.1 := by
        rw [heval]
        exact PositiveEdge.diagonalReflect_diagonalReflect hΛ.1 k p.1
      have hsub : (⟨e.1.diagonalReflect τ σ k,
          (hΛ.2.1 e.1).mp e.2⟩ : Λ.dynamicEdges) =
            ⟨p.1, (Finset.mem_filter.mp p.2).1⟩ := Subtype.ext href
      rw [hsub]
      change E ⟨p.1, _⟩ = _
      exact E.apply_symm_apply (Sum.inr (Sum.inr p))
    · have heval : e.1 = p.1 := by
        have he : E.symm (Sum.inr (Sum.inr p)) = e := by
          apply E.injective
          simp [hlabel]
        have he' := congrArg Subtype.val he
        simpa only [diagonalEdgeLabelEquiv] using he'.symm
      have hsub : (⟨e.1.diagonalReflect τ σ k,
          (hΛ.2.1 e.1).mp e.2⟩ : Λ.dynamicEdges) =
            ⟨p.1.diagonalReflect τ σ k,
              (hΛ.2.1 p.1).mp (Finset.mem_filter.mp p.2).1⟩ := by
        apply Subtype.ext
        exact congrArg (PositiveEdge.diagonalReflect τ σ k) heval
      rw [hsub]
      change E ⟨p.1.diagonalReflect τ σ k, _⟩ = _
      exact E.apply_symm_apply (Sum.inr (Sum.inl p))

/-- The diagonal assembly intertwines side swapping and geometric reflection. -/
theorem diagonalAssemble_reflect
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k)
    (U : DiagonalReflection.ReflectedConfiguration G
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k)) :
    Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ
        (DiagonalReflection.reflect U)) =
      diagonalReflectConfiguration τ σ k
        (Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ U)) := by
  funext e
  by_cases he : e ∈ Λ.dynamicEdges
  · rw [Λ.evaluate_of_mem _ e he]
    simp only [diagonalReflectConfiguration]
    have href : e.diagonalReflect τ σ k ∈ Λ.dynamicEdges :=
      (hΛ.2.1 e).mp he
    rw [Λ.evaluate_of_mem _ (e.diagonalReflect τ σ k) href]
    let edyn : Λ.dynamicEdges := ⟨e, he⟩
    have hlabel := diagonalEdgeLabelEquiv_diagonalReflect
      Λ τ σ k hΛ edyn
    unfold diagonalAssemble
    simp only [ContinuousMap.coe_mk]
    generalize heq : Λ.diagonalEdgeLabelEquiv τ σ k hΛ edyn = label
    rw [heq] at hlabel
    rcases label with o | p
    · rw [hlabel]
      rfl
    · rcases p with p | p <;> rw [hlabel] <;> rfl
  · rw [Λ.evaluate_of_not_mem _ e he]
    simp only [diagonalReflectConfiguration]
    rw [Λ.evaluate_of_not_mem]
    · exact congrFun hΛ.2.2.2 e |>.symm
    · exact fun href => he ((hΛ.2.1 e).mpr href)

/-- A positive diagonal plaquette reads only the plane and selected positive
side coordinates. -/
theorem plaquetteHolonomy_diagonalAssemble_eq_evaluatePositive
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k)
    (U : DiagonalReflection.ReflectedConfiguration G
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k))
    (p : Plaquette d) (hp : p ∈ Λ.diagonalPositivePlaquettes τ σ k) :
    FiniteVolume.plaquetteHolonomy Λ (Λ.diagonalAssemble τ σ k hΛ U) p =
      holonomy (Λ.diagonalEvaluatePositive τ σ k hΛ (U.1, U.2.2))
        p.boundary := by
  classical
  unfold FiniteVolume.plaquetteHolonomy diagonalEvaluatePositive
  change holonomy (Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ U)) p.boundary =
    holonomy (Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ
      (U.1, (1, U.2.2)))) p.boundary
  apply holonomy_eq_of_eqOn_edgeSupport
  intro e he
  have hends := diagonalPlaquetteNonnegative_edgeSupport hΛ.1 k p
    (Finset.mem_filter.mp hp).2.1 e he
  by_cases hedyn : e ∈ Λ.dynamicEdges
  · rw [Λ.evaluate_of_mem _ e hedyn, Λ.evaluate_of_mem _ e hedyn]
    let edyn : Λ.dynamicEdges := ⟨e, hedyn⟩
    by_cases hplane : diagonalHeight τ σ k e.source = 0 ∧
        diagonalHeight τ σ k e.target = 0
    · have heplane : e ∈ Λ.diagonalPlaneEdges τ σ k :=
        Finset.mem_filter.mpr ⟨hedyn, hplane⟩
      have hlabel : Λ.diagonalEdgeLabelEquiv τ σ k hΛ edyn =
          Sum.inl (⟨e, heplane⟩ : Λ.diagonalPlaneEdges τ σ k) := by
        unfold diagonalEdgeLabelEquiv
        dsimp [edyn]
        rw [dif_pos heplane]
      simp only [diagonalAssemble, ContinuousMap.coe_mk]
      rw [hlabel]
    · have heplus : e ∈ Λ.diagonalPositiveEdges τ σ k :=
        Finset.mem_filter.mpr ⟨hedyn, hends.1, hends.2, hplane⟩
      have hlabel : Λ.diagonalEdgeLabelEquiv τ σ k hΛ edyn =
          Sum.inr (Sum.inr
            (⟨e, heplus⟩ : Λ.diagonalPositiveEdges τ σ k)) := by
        unfold diagonalEdgeLabelEquiv
        dsimp [edyn]
        rw [dif_neg, dif_pos heplus]
        intro hp'
        exact hplane (Finset.mem_filter.mp hp').2
      simp only [diagonalAssemble, ContinuousMap.coe_mk]
      rw [hlabel]
  · rw [Λ.evaluate_of_not_mem _ e hedyn, Λ.evaluate_of_not_mem _ e hedyn]

/-- A fixed-plane diagonal plaquette reads only the common plane field. -/
theorem plaquetteHolonomy_diagonalAssemble_eq_evaluatePlane
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k)
    (U : DiagonalReflection.ReflectedConfiguration G
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k))
    (p : Plaquette d) (hp : p ∈ Λ.diagonalPlanePlaquettes τ σ k) :
    FiniteVolume.plaquetteHolonomy Λ (Λ.diagonalAssemble τ σ k hΛ U) p =
      holonomy (Λ.diagonalEvaluatePlane τ σ k hΛ U.1) p.boundary := by
  unfold FiniteVolume.plaquetteHolonomy diagonalEvaluatePlane
  change holonomy (Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ U)) p.boundary =
    holonomy (Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ
      (U.1, (1, 1)))) p.boundary
  apply holonomy_eq_of_eqOn_edgeSupport
  intro e he
  have hends := diagonalPlanePlaquette_edgeSupport hΛ.1 k p
    (Finset.mem_filter.mp hp).2 e he
  by_cases hedyn : e ∈ Λ.dynamicEdges
  · rw [Λ.evaluate_of_mem _ e hedyn, Λ.evaluate_of_mem _ e hedyn]
    let edyn : Λ.dynamicEdges := ⟨e, hedyn⟩
    have heplane : e ∈ Λ.diagonalPlaneEdges τ σ k :=
      Finset.mem_filter.mpr ⟨hedyn, hends⟩
    have hlabel : Λ.diagonalEdgeLabelEquiv τ σ k hΛ edyn =
        Sum.inl (⟨e, heplane⟩ : Λ.diagonalPlaneEdges τ σ k) := by
      unfold diagonalEdgeLabelEquiv
      dsimp [edyn]
      rw [dif_pos heplane]
    simp only [diagonalAssemble, ContinuousMap.coe_mk]
    rw [hlabel]
  · rw [Λ.evaluate_of_not_mem _ e hedyn, Λ.evaluate_of_not_mem _ e hedyn]

/-- Pointwise version of the positive-half restriction: a nonnegative edge
has the same value in the full assembly and in the field with the negative
side discarded. -/
theorem diagonalAssemble_apply_eq_evaluatePositive
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k)
    (U : DiagonalReflection.ReflectedConfiguration G
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k))
    (e : PositiveEdge d)
    (hsource : 0 ≤ diagonalHeight τ σ k e.source)
    (htarget : 0 ≤ diagonalHeight τ σ k e.target) :
    Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ U) e =
      Λ.diagonalEvaluatePositive τ σ k hΛ (U.1, U.2.2) e := by
  unfold diagonalEvaluatePositive
  change Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ U) e =
    Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ (U.1, (1, U.2.2))) e
  by_cases hedyn : e ∈ Λ.dynamicEdges
  · rw [Λ.evaluate_of_mem _ e hedyn, Λ.evaluate_of_mem _ e hedyn]
    let edyn : Λ.dynamicEdges := ⟨e, hedyn⟩
    by_cases hplane : diagonalHeight τ σ k e.source = 0 ∧
        diagonalHeight τ σ k e.target = 0
    · have heplane : e ∈ Λ.diagonalPlaneEdges τ σ k :=
        Finset.mem_filter.mpr ⟨hedyn, hplane⟩
      have hlabel : Λ.diagonalEdgeLabelEquiv τ σ k hΛ edyn =
          Sum.inl (⟨e, heplane⟩ : Λ.diagonalPlaneEdges τ σ k) := by
        unfold diagonalEdgeLabelEquiv
        dsimp [edyn]
        rw [dif_pos heplane]
      simp only [diagonalAssemble, ContinuousMap.coe_mk]
      rw [hlabel]
    · have heplus : e ∈ Λ.diagonalPositiveEdges τ σ k :=
        Finset.mem_filter.mpr ⟨hedyn, hsource, htarget, hplane⟩
      have hlabel : Λ.diagonalEdgeLabelEquiv τ σ k hΛ edyn =
          Sum.inr (Sum.inr
            (⟨e, heplus⟩ : Λ.diagonalPositiveEdges τ σ k)) := by
        unfold diagonalEdgeLabelEquiv
        dsimp [edyn]
        rw [dif_neg, dif_pos heplus]
        intro hp'
        exact hplane (Finset.mem_filter.mp hp').2
      simp only [diagonalAssemble, ContinuousMap.coe_mk]
      rw [hlabel]
  · rw [Λ.evaluate_of_not_mem _ e hedyn, Λ.evaluate_of_not_mem _ e hedyn]

omit [IsTopologicalGroup G] in
/-- A site in the diagonal plane is fixed pointwise. -/
theorem diagonalReflection_eq_self_of_height_zero
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) (x : Site d)
    (hx : diagonalHeight τ σ k x = 0) :
    diagonalReflection τ σ k x = x := by
  ext i
  by_cases hiτ : i = τ
  · subst i
    rw [diagonalReflection_apply_first]
    unfold diagonalHeight at hx
    omega
  · by_cases hiσ : i = σ
    · subst i
      rw [diagonalReflection_apply_second hτσ]
      unfold diagonalHeight at hx
      omega
    · exact diagonalReflection_apply_other hiτ hiσ k x

omit [IsTopologicalGroup G] in
theorem diagonalReflect_cutPositiveFirstEdge
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) (x : Site d)
    (hx : diagonalHeight τ σ k x = 0) :
    (⟨x, τ⟩ : PositiveEdge d).diagonalReflect τ σ k = ⟨x, σ⟩ := by
  simp [PositiveEdge.diagonalReflect,
    diagonalReflection_eq_self_of_height_zero hτσ k x hx]

omit [IsTopologicalGroup G] in
theorem diagonalReflect_cutPositiveSecondEdge
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) (x : Site d)
    (hx : diagonalHeight τ σ k x = 0) :
    (⟨step x (.forward τ), σ⟩ : PositiveEdge d).diagonalReflect τ σ k =
      ⟨step x (.forward σ), τ⟩ := by
  change PositiveEdge.mk
      (diagonalReflection τ σ k (step x (.forward τ)))
      (Equiv.swap τ σ σ) = _
  rw [diagonalReflection_step hτσ,
    diagonalReflection_eq_self_of_height_zero hτσ k x hx]
  simp [SignedDirection.diagonalReflect, SignedDirection.forward]

/-- On a cut plaquette, the actual Wilson term is precisely the real
normalized-character kernel of the two reflected half-holonomies. -/
theorem wilsonPotential_cutPlaquette_diagonalAssemble
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) {n : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G n)
    (U : DiagonalReflection.ReflectedConfiguration G
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k))
    (p : Λ.diagonalCutPlaquettes τ σ k) :
    ρ.wilsonPotential
        (FiniteVolume.plaquetteHolonomy Λ
          (Λ.diagonalAssemble τ σ k hΛ U) p.1) =
      ρ.wilsonPotential
        (Λ.diagonalCutHolonomy τ σ k hΛ p (U.1, U.2.2) *
          (Λ.diagonalCutHolonomy τ σ k hΛ p (U.1, U.2.1))⁻¹) := by
  let A := Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ U)
  let Aplus := Λ.diagonalEvaluatePositive τ σ k hΛ (U.1, U.2.2)
  let Aminus := Λ.diagonalEvaluatePositive τ σ k hΛ (U.1, U.2.1)
  let e₁ : PositiveEdge d := ⟨p.1.base, τ⟩
  let e₂ : PositiveEdge d := ⟨step p.1.base (.forward τ), σ⟩
  have hcut := (Finset.mem_filter.mp p.2).2
  have hbase := hcut.1
  have he₁source : diagonalHeight τ σ k e₁.source = 0 := hbase
  have he₁target : diagonalHeight τ σ k e₁.target = 1 := by
    change diagonalHeight τ σ k (step p.1.base (.forward τ)) = 1
    rw [diagonalHeight_step_forward hΛ.1, hbase]
    simp [diagonalDirectionIncrement]
  have he₂source : diagonalHeight τ σ k e₂.source = 1 := he₁target
  have he₂target : diagonalHeight τ σ k e₂.target = 0 := by
    change diagonalHeight τ σ k
      (step (step p.1.base (.forward τ)) (.forward σ)) = 0
    rw [diagonalHeight_step_forward hΛ.1, he₂source]
    simp [diagonalDirectionIncrement, hΛ.1.symm]
  have hplus₁ : A e₁ = Aplus e₁ :=
    Λ.diagonalAssemble_apply_eq_evaluatePositive τ σ k hΛ U e₁
      (by omega) (by omega)
  have hplus₂ : A e₂ = Aplus e₂ :=
    Λ.diagonalAssemble_apply_eq_evaluatePositive τ σ k hΛ U e₂
      (by omega) (by omega)
  have hswap := Λ.diagonalAssemble_reflect τ σ k hΛ U
  have hminus₁raw := Λ.diagonalAssemble_apply_eq_evaluatePositive
    τ σ k hΛ (DiagonalReflection.reflect U) e₁ (by omega) (by omega)
  have hminus₂raw := Λ.diagonalAssemble_apply_eq_evaluatePositive
    τ σ k hΛ (DiagonalReflection.reflect U) e₂ (by omega) (by omega)
  have hminus₁ : A (e₁.diagonalReflect τ σ k) = Aminus e₁ := by
    have hswap₁ := congrFun hswap e₁
    simp only [diagonalReflectConfiguration] at hswap₁
    calc
      A (e₁.diagonalReflect τ σ k) =
          Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ
            (DiagonalReflection.reflect U)) e₁ := by
        exact hswap₁.symm
      _ = Aminus e₁ := by
        simpa [Aminus, DiagonalReflection.reflect] using hminus₁raw
  have hminus₂ : A (e₂.diagonalReflect τ σ k) = Aminus e₂ := by
    have hswap₂ := congrFun hswap e₂
    simp only [diagonalReflectConfiguration] at hswap₂
    calc
      A (e₂.diagonalReflect τ σ k) =
          Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ
            (DiagonalReflection.reflect U)) e₂ := by
        exact hswap₂.symm
      _ = Aminus e₂ := by
        simpa [Aminus, DiagonalReflection.reflect] using hminus₂raw
  have href₁ : e₁.diagonalReflect τ σ k =
      (⟨p.1.base, σ⟩ : PositiveEdge d) :=
    diagonalReflect_cutPositiveFirstEdge hΛ.1 k p.1.base hbase
  have href₂ : e₂.diagonalReflect τ σ k =
      (⟨step p.1.base (.forward σ), τ⟩ : PositiveEdge d) :=
    diagonalReflect_cutPositiveSecondEdge hΛ.1 k p.1.base hbase
  unfold FiniteVolume.plaquetteHolonomy
  rw [holonomy_plaquette_boundary_explicit]
  change ρ.wilsonPotential
      (A ⟨p.1.base, p.1.first⟩ *
        A ⟨step p.1.base (.forward p.1.first), p.1.second⟩ *
        (A ⟨step p.1.base (.forward p.1.second), p.1.first⟩)⁻¹ *
        (A ⟨p.1.base, p.1.second⟩)⁻¹) = _
  rcases hcut.2 with haxes | haxes
  · rw [haxes.1, haxes.2]
    rw [← href₂, ← href₁]
    change ρ.wilsonPotential
      (A e₁ * A e₂ *
        (A (e₂.diagonalReflect τ σ k))⁻¹ *
        (A (e₁.diagonalReflect τ σ k))⁻¹) =
      ρ.wilsonPotential
        ((Aplus e₁ * Aplus e₂) * (Aminus e₁ * Aminus e₂)⁻¹)
    rw [hplus₁, hplus₂, hminus₁, hminus₂]
    simp only [mul_inv_rev]
    congr 1
    group
  · rw [haxes.1, haxes.2]
    rw [← href₁, ← href₂]
    change ρ.wilsonPotential
      (A (e₁.diagonalReflect τ σ k) *
        A (e₂.diagonalReflect τ σ k) *
        (A e₂)⁻¹ * (A e₁)⁻¹) =
      ρ.wilsonPotential
        ((Aplus e₁ * Aplus e₂) * (Aminus e₁ * Aminus e₂)⁻¹)
    rw [hplus₁, hplus₂, hminus₁, hminus₂]
    rw [← ρ.wilsonPotential.inv_invariant]
    congr 1
    group

/-- A reflected positive plaquette has the same Wilson term as its positive
representative after the two side fields are exchanged. -/
theorem plaquetteTerm_diagonalReflect_assemble
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) (Φ : RealPlaquettePotential G)
    (U : DiagonalReflection.ReflectedConfiguration G
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k))
    (p : Plaquette d) :
    Φ (FiniteVolume.plaquetteHolonomy Λ (Λ.diagonalAssemble τ σ k hΛ U)
        (p.diagonalReflect τ σ k)) =
      Φ (FiniteVolume.plaquetteHolonomy Λ
        (Λ.diagonalAssemble τ σ k hΛ (DiagonalReflection.reflect U)) p) := by
  unfold FiniteVolume.plaquetteHolonomy
  rw [Λ.diagonalAssemble_reflect τ σ k hΛ]
  rw [holonomy_diagonalReflectConfiguration hΛ.1]

/-- The concrete finite Wilson action is exactly the fixed-plane/two-side/cut
action used by the diagonal Taylor/Fubini theorem. -/
theorem action_diagonalAssemble
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) {n : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G n)
    (U : DiagonalReflection.ReflectedConfiguration G
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k)) :
    FiniteVolume.action Λ ρ.wilsonPotential
        (Λ.diagonalAssemble τ σ k hΛ U) =
      (Λ.diagonalWilsonDecomposition τ σ k hΛ ρ).action U := by
  classical
  let f : Plaquette d → ℝ := fun p =>
    ρ.wilsonPotential
      (FiniteVolume.plaquetteHolonomy Λ (Λ.diagonalAssemble τ σ k hΛ U) p)
  let fplane : Plaquette d → ℝ := fun p =>
    ρ.wilsonPotential
      (holonomy (Λ.diagonalEvaluatePlane τ σ k hΛ U.1) p.boundary)
  let fplus : Plaquette d → ℝ := fun p =>
    ρ.wilsonPotential
      (holonomy (Λ.diagonalEvaluatePositive τ σ k hΛ (U.1, U.2.2))
        p.boundary)
  let fminus : Plaquette d → ℝ := fun p =>
    ρ.wilsonPotential
      (holonomy (Λ.diagonalEvaluatePositive τ σ k hΛ (U.1, U.2.1))
        p.boundary)
  change (∑ p ∈ Λ.activePlaquettes, f p) =
    (∑ p ∈ Λ.diagonalPlanePlaquettes τ σ k, fplane p) +
      ((∑ p ∈ Λ.diagonalPositivePlaquettes τ σ k, fminus p) +
        (∑ p ∈ Λ.diagonalPositivePlaquettes τ σ k, fplus p) +
        ∑ p : Λ.diagonalCutPlaquettes τ σ k,
          ρ.wilsonPotential
            (Λ.diagonalCutHolonomy τ σ k hΛ p (U.1, U.2.2) *
              (Λ.diagonalCutHolonomy τ σ k hΛ p (U.1, U.2.1))⁻¹))
  have hnegative :
      (∑ p ∈ Λ.diagonalNegativePlaquettes τ σ hΛ.1 k, f p) =
        ∑ p ∈ Λ.diagonalPositivePlaquettes τ σ k,
          f (p.diagonalReflect τ σ k) := by
    change (∑ p ∈ (Λ.diagonalPositivePlaquettes τ σ k).map
        (Plaquette.diagonalReflectionEquiv τ σ hΛ.1 k).toEmbedding, f p) = _
    rw [Finset.sum_map]
    rfl
  have hsplit : (∑ p ∈ Λ.activePlaquettes, f p) =
      (∑ p ∈ Λ.diagonalPlanePlaquettes τ σ k, f p) +
      (∑ p ∈ Λ.diagonalPositivePlaquettes τ σ k, f p) +
      (∑ p ∈ Λ.diagonalCutPlaquettes τ σ k, f p) +
      ∑ p ∈ Λ.diagonalPositivePlaquettes τ σ k,
        f (p.diagonalReflect τ σ k) := by
    rw [Λ.activePlaquettes_eq_diagonal_union τ σ k hΛ,
      Finset.sum_union
        (Λ.diagonalPlanePlaquettes_disjoint_diagonalSides τ σ k hΛ),
      Finset.sum_union
        (Λ.diagonalPositivePlaquettes_disjoint_cutNegative τ σ k hΛ),
      Finset.sum_union
        (Λ.diagonalCutPlaquettes_disjoint_negative τ σ k hΛ),
      hnegative]
    ring
  rw [hsplit]
  have hplane : (∑ p ∈ Λ.diagonalPlanePlaquettes τ σ k, f p) =
      ∑ p ∈ Λ.diagonalPlanePlaquettes τ σ k, fplane p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact congrArg ρ.wilsonPotential <|
      Λ.plaquetteHolonomy_diagonalAssemble_eq_evaluatePlane
        τ σ k hΛ U p hp
  have hplus : (∑ p ∈ Λ.diagonalPositivePlaquettes τ σ k, f p) =
      ∑ p ∈ Λ.diagonalPositivePlaquettes τ σ k, fplus p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact congrArg ρ.wilsonPotential <|
      Λ.plaquetteHolonomy_diagonalAssemble_eq_evaluatePositive
        τ σ k hΛ U p hp
  have hminus : (∑ p ∈ Λ.diagonalPositivePlaquettes τ σ k,
      f (p.diagonalReflect τ σ k)) =
      ∑ p ∈ Λ.diagonalPositivePlaquettes τ σ k, fminus p := by
    apply Finset.sum_congr rfl
    intro p hp
    change ρ.wilsonPotential
      (FiniteVolume.plaquetteHolonomy Λ
        (Λ.diagonalAssemble τ σ k hΛ U) (p.diagonalReflect τ σ k)) = _
    rw [Λ.plaquetteTerm_diagonalReflect_assemble τ σ k hΛ
      ρ.wilsonPotential U p]
    exact congrArg ρ.wilsonPotential <|
      Λ.plaquetteHolonomy_diagonalAssemble_eq_evaluatePositive
        τ σ k hΛ (DiagonalReflection.reflect U) p hp
  have hcut : (∑ p ∈ Λ.diagonalCutPlaquettes τ σ k, f p) =
      ∑ p : Λ.diagonalCutPlaquettes τ σ k,
        ρ.wilsonPotential
          (Λ.diagonalCutHolonomy τ σ k hΛ p (U.1, U.2.2) *
            (Λ.diagonalCutHolonomy τ σ k hΛ p (U.1, U.2.1))⁻¹) := by
    calc
      (∑ p ∈ Λ.diagonalCutPlaquettes τ σ k, f p) =
          ∑ p : Λ.diagonalCutPlaquettes τ σ k, f p.1 := by
        exact Finset.sum_subtype (Λ.diagonalCutPlaquettes τ σ k)
          (fun _ => Iff.rfl) f
      _ = _ := by
        apply Fintype.sum_congr
        intro p
        exact Λ.wilsonPotential_cutPlaquette_diagonalAssemble
          τ σ k hΛ ρ U p
  rw [hplane, hplus, hminus, hcut]
  ring

end Topology

section Haar

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [CompactSpace G] [GaugeHaarProbability G]

/-- Diagonal plane/two-side assembly is a pure relabelling of product Haar. -/
theorem measurePreserving_diagonalAssemble
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) :
    MeasurePreserving (Λ.diagonalAssemble τ σ k hΛ)
      (DiagonalReflection.WilsonActionDecomposition.reflectedHaar (G := G)
        (O := Λ.diagonalPlaneEdges τ σ k)
        (P := Λ.diagonalPositiveEdges τ σ k)) Λ.haarMeasure := by
  let E := Λ.diagonalEdgeLabelEquiv τ σ k hΛ
  let R := ProductHaar.reindexEquiv (G := G) E.symm
  have hR := ProductHaar.measurePreserving_reindex (G := G) E.symm
  let Eouter := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : DiagonalReflectedLabel Λ τ σ k => G)
  let Esides := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : (Λ.diagonalPositiveEdges τ σ k) ⊕
      (Λ.diagonalPositiveEdges τ σ k) => G)
  let J : DiagonalReflection.ReflectedConfiguration G
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k) →
      (DiagonalReflectedLabel Λ τ σ k → G) :=
    fun U => Eouter.symm (U.1, Esides.symm U.2)
  have hJ : MeasurePreserving J
      (DiagonalReflection.WilsonActionDecomposition.reflectedHaar (G := G)
        (O := Λ.diagonalPlaneEdges τ σ k)
        (P := Λ.diagonalPositiveEdges τ σ k))
      (ProductHaar.measure G (DiagonalReflectedLabel Λ τ σ k)) := by
    exact (MeasureTheory.measurePreserving_sumPiEquivProdPi_symm
      (fun _ : DiagonalReflectedLabel Λ τ σ k =>
        GaugeHaarProbability.haar G)).comp
      (MeasurePreserving.prod (MeasurePreserving.id _)
        (MeasureTheory.measurePreserving_sumPiEquivProdPi_symm
          (fun _ : (Λ.diagonalPositiveEdges τ σ k) ⊕
            (Λ.diagonalPositiveEdges τ σ k) =>
              GaugeHaarProbability.haar G)))
  have hcomp := hR.comp hJ
  refine ⟨(Λ.diagonalAssemble τ σ k hΛ).continuous.measurable, ?_⟩
  have heq : (Λ.diagonalAssemble τ σ k hΛ : _ → _) = R ∘ J := by
    funext U e
    let label := E e
    generalize hlabel : E e = label
    rcases label with o | p
    · unfold diagonalAssemble
      simp only [ContinuousMap.coe_mk, Function.comp_apply]
      rw [hlabel]
      rw [show R (J U) e = (J U) (E e) by
        exact ProductHaar.reindex_apply E.symm (J U) e]
      rw [hlabel]
      rfl
    · rcases p with p | p
      · unfold diagonalAssemble
        simp only [ContinuousMap.coe_mk, Function.comp_apply]
        rw [hlabel]
        rw [show R (J U) e = (J U) (E e) by
          exact ProductHaar.reindex_apply E.symm (J U) e]
        rw [hlabel]
        rfl
      · unfold diagonalAssemble
        simp only [ContinuousMap.coe_mk, Function.comp_apply]
        rw [hlabel]
        rw [show R (J U) e = (J U) (E e) by
          exact ProductHaar.reindex_apply E.symm (J U) e]
        rw [hlabel]
        rfl
  rw [heq]
  exact hcomp.map_eq

/-- Restrict a full-lattice observable to the fixed-plane and positive-side
variables of a diagonally symmetric finite specification. -/
def diagonalRestrictObservable (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) (hΛ : Λ.DiagonalSymmetric τ σ k)
    (F : LocalObservable d G) :
    DiagonalReflection.PositiveObservable G
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k) :=
  F.toContinuousMap.comp (Λ.diagonalEvaluatePositive τ σ k hΛ)

/-- Positive-half observables are unchanged when the discarded negative side
is filled with the identity field. -/
theorem diagonalRestrictObservable_apply_assemble
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) (F : LocalObservable d G)
    (hF : F.SupportedInDiagonalPositiveHalf τ σ k)
    (U : DiagonalReflection.ReflectedConfiguration G
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k)) :
    F (Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ U)) =
      Λ.diagonalRestrictObservable τ σ k hΛ F (U.1, U.2.2) := by
  apply F.dependsOn_support
  intro e he
  apply Λ.diagonalAssemble_apply_eq_evaluatePositive τ σ k hΛ U e
  · have hs := (hF e he).1
    unfold diagonalHeight
    omega
  · have ht := (hF e he).2
    unfold diagonalHeight
    omega

/-- The concrete diagonal reflected product becomes the labelled normal-form
product under the geometric assembly. -/
theorem diagonalReflectionProduct_assemble
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) (F H : LocalObservable d G)
    (hF : F.SupportedInDiagonalPositiveHalf τ σ k)
    (hH : H.SupportedInDiagonalPositiveHalf τ σ k)
    (U : DiagonalReflection.ReflectedConfiguration G
      (Λ.diagonalPlaneEdges τ σ k) (Λ.diagonalPositiveEdges τ σ k)) :
    F.diagonalReflectionProduct τ σ k H
        (Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ U)) =
      DiagonalReflection.theta (DiagonalReflection.liftPositive
          (Λ.diagonalRestrictObservable τ σ k hΛ F)) U *
        DiagonalReflection.liftPositive
          (Λ.diagonalRestrictObservable τ σ k hΛ H) U := by
  rw [LocalObservable.diagonalReflectionProduct_apply,
    ← Λ.diagonalAssemble_reflect τ σ k hΛ]
  rw [Λ.diagonalRestrictObservable_apply_assemble τ σ k hΛ F hF
      (DiagonalReflection.reflect U),
    Λ.diagonalRestrictObservable_apply_assemble τ σ k hΛ H hH U]
  rfl

/-- Concrete and labelled diagonal partition functions agree. -/
theorem partitionFunction_eq_diagonalDecomposition
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) {n : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G n) (β : ℝ) :
    FiniteVolume.partitionFunction Λ ρ.wilsonPotential β =
      (Λ.diagonalWilsonDecomposition τ σ k hΛ ρ).partitionFunction β := by
  let D := Λ.diagonalWilsonDecomposition τ σ k hΛ ρ
  have hchange :
      (∫ U, FiniteVolume.boltzmannWeight Λ ρ.wilsonPotential β
          (Λ.diagonalAssemble τ σ k hΛ U)
        ∂DiagonalReflection.WilsonActionDecomposition.reflectedHaar) =
        ∫ V, FiniteVolume.boltzmannWeight Λ ρ.wilsonPotential β V
          ∂Λ.haarMeasure := by
    rw [← (Λ.measurePreserving_diagonalAssemble τ σ k hΛ).map_eq]
    have hmeas : AEStronglyMeasurable
        (FiniteVolume.boltzmannWeight Λ ρ.wilsonPotential β)
        (Measure.map (Λ.diagonalAssemble τ σ k hΛ)
          DiagonalReflection.WilsonActionDecomposition.reflectedHaar) :=
      (FiniteVolume.continuous_boltzmannWeight
        Λ ρ.wilsonPotential β).aestronglyMeasurable
    exact (MeasureTheory.integral_map
      (Λ.diagonalAssemble τ σ k hΛ).continuous.measurable.aemeasurable
      hmeas).symm
  change (∫ V, FiniteVolume.boltzmannWeight Λ ρ.wilsonPotential β V
      ∂Λ.haarMeasure) =
    ∫ U, D.boltzmannWeight β U
      ∂DiagonalReflection.WilsonActionDecomposition.reflectedHaar
  rw [← hchange]
  apply integral_congr_ae
  filter_upwards with U
  simp only [FiniteVolume.boltzmannWeight,
    DiagonalReflection.WilsonActionDecomposition.boltzmannWeight]
  rw [Λ.action_diagonalAssemble τ σ k hΛ ρ U]

/-- Concrete finite diagonal pairing equals the normalized labelled pairing
proved positive by the Taylor/Fubini expansion. -/
theorem integral_gibbsMeasure_diagonalReflectionProduct_eq
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) {n : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G n) (β : ℝ)
    (F H : LocalObservable d G)
    (hF : F.SupportedInDiagonalPositiveHalf τ σ k)
    (hH : H.SupportedInDiagonalPositiveHalf τ σ k) :
    (∫ V, F.diagonalReflectionProduct τ σ k H (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) =
      (Λ.diagonalWilsonDecomposition τ σ k hΛ ρ).reflectionInnerProduct β
        (Λ.diagonalRestrictObservable τ σ k hΛ F)
        (Λ.diagonalRestrictObservable τ σ k hΛ H) := by
  let D := Λ.diagonalWilsonDecomposition τ σ k hΛ ρ
  rw [FiniteVolume.gibbsMeasure, integral_tilted]
  change (∫ V, (Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential V) /
      FiniteVolume.partitionFunction Λ ρ.wilsonPotential β : ℝ) •
        F.diagonalReflectionProduct τ σ k H (Λ.evaluate V)
      ∂Λ.haarMeasure) = _
  let K : DynamicConfiguration Λ → ℂ := fun V =>
    (Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential V) /
      FiniteVolume.partitionFunction Λ ρ.wilsonPotential β : ℝ) •
        F.diagonalReflectionProduct τ σ k H (Λ.evaluate V)
  have hK : Continuous K := by
    unfold K
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp
        (continuous_const.mul
          (FiniteVolume.continuous_action Λ ρ.wilsonPotential))).div_const _)).mul
      ((F.diagonalReflectionProduct τ σ k H).toContinuousMap.continuous.comp
        Λ.continuous_evaluate)
  have hchange :
      (∫ U, K (Λ.diagonalAssemble τ σ k hΛ U)
          ∂DiagonalReflection.WilsonActionDecomposition.reflectedHaar) =
        ∫ V, K V ∂Λ.haarMeasure := by
    rw [← (Λ.measurePreserving_diagonalAssemble τ σ k hΛ).map_eq]
    exact (MeasureTheory.integral_map
      (Λ.diagonalAssemble τ σ k hΛ).continuous.measurable.aemeasurable
      hK.measurable.aestronglyMeasurable).symm
  rw [← hchange]
  change (∫ U, (Real.exp (β * FiniteVolume.action Λ ρ.wilsonPotential
      (Λ.diagonalAssemble τ σ k hΛ U)) /
        FiniteVolume.partitionFunction Λ ρ.wilsonPotential β : ℝ) •
      F.diagonalReflectionProduct τ σ k H
        (Λ.evaluate (Λ.diagonalAssemble τ σ k hΛ U))
      ∂DiagonalReflection.WilsonActionDecomposition.reflectedHaar) = _
  unfold DiagonalReflection.WilsonActionDecomposition.reflectionInnerProduct
  unfold DiagonalReflection.WilsonActionDecomposition.gibbsReflectionPairing
  rw [Λ.partitionFunction_eq_diagonalDecomposition τ σ k hΛ ρ β]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with U
  rw [Λ.action_diagonalAssemble τ σ k hΛ ρ U,
    Λ.diagonalReflectionProduct_assemble τ σ k hΛ F H hF hH U]
  simp only [DiagonalReflection.WilsonActionDecomposition.boltzmannWeight]
  norm_cast
  simp only [div_eq_mul_inv, Complex.ofReal_inv]
  change ((Real.exp (β * D.action U) * (D.partitionFunction β)⁻¹ : ℝ) : ℂ) * _ = _
  rw [Complex.ofReal_mul, Complex.ofReal_inv]
  ring

/-- Reflection positivity for every concrete diagonally symmetric finite
Wilson specification. -/
theorem diagonalReflectionPositive_gibbsMeasure
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) {n : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G n) {β : ℝ} (hβ : 0 ≤ β)
    (F : LocalObservable d G)
    (hF : F.SupportedInDiagonalPositiveHalf τ σ k) :
    Complex.im (∫ V, F.diagonalReflectionProduct τ σ k F (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) = 0 ∧
      0 ≤ Complex.re (∫ V,
        F.diagonalReflectionProduct τ σ k F (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) := by
  rw [Λ.integral_gibbsMeasure_diagonalReflectionProduct_eq
    τ σ k hΛ ρ β F F hF hF]
  exact (Λ.diagonalWilsonDecomposition τ σ k hΛ ρ)
    |>.reflectionInnerProduct_self_nonneg hβ
      (Λ.diagonalRestrictObservable τ σ k hΛ F)

/-- Concrete finite Cauchy--Schwarz for the diagonal reflection pairing. -/
theorem normSq_integral_gibbsMeasure_diagonalReflectionProduct_le
    (Λ : FiniteSpecification d G) (τ σ : Fin d) (k : ℤ)
    (hΛ : Λ.DiagonalSymmetric τ σ k) {n : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G n) {β : ℝ} (hβ : 0 ≤ β)
    (F H : LocalObservable d G)
    (hF : F.SupportedInDiagonalPositiveHalf τ σ k)
    (hH : H.SupportedInDiagonalPositiveHalf τ σ k) :
    Complex.normSq (∫ V,
        F.diagonalReflectionProduct τ σ k H (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) ≤
      Complex.re (∫ V,
        F.diagonalReflectionProduct τ σ k F (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) *
      Complex.re (∫ V,
        H.diagonalReflectionProduct τ σ k H (Λ.evaluate V)
        ∂FiniteVolume.gibbsMeasure Λ ρ.wilsonPotential β) := by
  rw [Λ.integral_gibbsMeasure_diagonalReflectionProduct_eq
      τ σ k hΛ ρ β F H hF hH,
    Λ.integral_gibbsMeasure_diagonalReflectionProduct_eq
      τ σ k hΛ ρ β F F hF hF,
    Λ.integral_gibbsMeasure_diagonalReflectionProduct_eq
      τ σ k hΛ ρ β H H hH hH]
  exact (Λ.diagonalWilsonDecomposition τ σ k hΛ ρ)
    |>.normSq_reflectionInnerProduct_le hβ
      (Λ.diagonalRestrictObservable τ σ k hΛ F)
      (Λ.diagonalRestrictObservable τ σ k hΛ H)

end Haar

end FiniteSpecification

end

end YangMills.Gauge
