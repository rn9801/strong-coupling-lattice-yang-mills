/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Lattice.CubicalCharge
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Rectangular center-charge fillings

A half-hyperplane flux functional proves that every finite plaquette field
screening an `r`-by-`s` rectangle contains at least `r * s` Taylor
occurrences. Plaquettes transverse to the rectangle plane cancel in the flux,
so the result applies to arbitrary finite fields in the full cubic lattice.
-/

namespace YangMills.Lattice.Cubic

open YangMills.Basic

noncomputable section

theorem plaquette_boundary_edgeChain {d : ℕ} (R : Type*) [CommRing R]
    (p : Plaquette d) :
    Path.edgeChain R p.boundary =
      Finsupp.single ⟨p.base, p.first⟩ 1 +
        Finsupp.single ⟨step p.base (.forward p.first), p.second⟩ 1 +
        Finsupp.single ⟨step p.base (.forward p.second), p.first⟩ (-1) +
        Finsupp.single ⟨p.base, p.second⟩ (-1) := by
  have h₃ : p.base + unitVector p.first + unitVector p.second +
      -unitVector p.first = p.base + unitVector p.second := by abel
  simp only [Plaquette.boundary, Path.rectangleBoundary, SignedDirection.forward,
    Path.advance, step, SignedDirection.delta, SignedDirection.backward,
    Path.rectangleRaw, Path.straight, Nat.reduceAdd, edgeFrom, SignedEdge.toArrow,
    SignedEdge.target, h₃, Quiver.Path.comp_cons, Quiver.Path.comp_nil,
    Path.edgeChain_castTarget, Path.edgeChain_cons, SignedEdge.edgeChain,
    SignedEdge.positive, SignedEdge.target, Path.edgeChain_nil]
  abel

/-- Flux through the half-hyperplane of positive `i`-edges at fixed
`i`-coordinate and bounded-above `j`-coordinate. -/
def coordinateCutFlux {d : ℕ} (R : Type*) [CommRing R]
    (i j : Fin d) (u v : ℤ) (c : EdgeChain d R) : R :=
  c.sum fun e z ↦ if e.direction = i ∧ e.source i = u ∧ e.source j ≤ v then z else 0

@[simp]
theorem coordinateCutFlux_single {d : ℕ} (R : Type*) [CommRing R]
    (i j : Fin d) (u v : ℤ) (e : PositiveEdge d) (z : R) :
    coordinateCutFlux R i j u v (Finsupp.single e z) =
      if e.direction = i ∧ e.source i = u ∧ e.source j ≤ v then z else 0 := by
  classical
  simp [coordinateCutFlux]

@[simp]
theorem coordinateCutFlux_zero {d : ℕ} (R : Type*) [CommRing R]
    (i j : Fin d) (u v : ℤ) :
    coordinateCutFlux R i j u v (0 : EdgeChain d R) = 0 := by
  simp [coordinateCutFlux]

theorem coordinateCutFlux_add {d : ℕ} (R : Type*) [CommRing R]
    (i j : Fin d) (u v : ℤ) (c c' : EdgeChain d R) :
    coordinateCutFlux R i j u v (c + c') =
      coordinateCutFlux R i j u v c + coordinateCutFlux R i j u v c' := by
  classical
  unfold coordinateCutFlux
  apply Finsupp.sum_add_index
  · intro e
    split <;> simp
  · intro e x y
    split <;> simp

theorem coordinateCutFlux_neg {d : ℕ} (R : Type*) [CommRing R]
    (i j : Fin d) (u v : ℤ) (c : EdgeChain d R) :
    coordinateCutFlux R i j u v (-c) = -coordinateCutFlux R i j u v c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add e z c he hz ih =>
      rw [neg_add_rev, coordinateCutFlux_add, coordinateCutFlux_add, ih]
      rw [show -Finsupp.single e z = Finsupp.single e (-z) by ext; simp]
      simp only [coordinateCutFlux_single]
      split <;> simp

theorem coordinateCutFlux_smul {d : ℕ} (R : Type*) [CommRing R]
    (i j : Fin d) (u v : ℤ) (z : R) (c : EdgeChain d R) :
    coordinateCutFlux R i j u v (z • c) =
      z * coordinateCutFlux R i j u v c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add e w c he hw ih =>
      rw [smul_add, coordinateCutFlux_add, coordinateCutFlux_add, ih]
      rw [show z • Finsupp.single e w = Finsupp.single e (z * w) by ext; simp]
      simp only [coordinateCutFlux_single]
      split <;> ring

theorem coordinateCutFlux_sub {d : ℕ} (R : Type*) [CommRing R]
    (i j : Fin d) (u v : ℤ) (c c' : EdgeChain d R) :
    coordinateCutFlux R i j u v (c - c') =
      coordinateCutFlux R i j u v c - coordinateCutFlux R i j u v c' := by
  rw [sub_eq_add_neg, coordinateCutFlux_add, coordinateCutFlux_neg, sub_eq_add_neg]

theorem coordinateCutFlux_sum {d : ℕ} (R : Type*) [CommRing R]
    {α : Type*} (i j : Fin d) (u v : ℤ) (s : Finset α)
    (c : α → EdgeChain d R) :
    coordinateCutFlux R i j u v (∑ a ∈ s, c a) =
      ∑ a ∈ s, coordinateCutFlux R i j u v (c a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, coordinateCutFlux_add, ih]

/-- A plaquette projects onto the indicated elementary cell in the ordered
`i,j` coordinate plane, in either orientation. -/
def Plaquette.spansCoordinateCell {d : ℕ} (i j : Fin d) (u v : ℤ)
    (p : Plaquette d) : Prop :=
  ((p.first = i ∧ p.second = j) ∨ (p.first = j ∧ p.second = i)) ∧
    p.base i = u ∧ p.base j = v

theorem coordinateCutFlux_plaquette_boundary_eq_zero_of_not_spans
    {d : ℕ} (R : Type*) [CommRing R]
    (i j : Fin d) (hij : i ≠ j) (u v : ℤ) (p : Plaquette d)
    (hp : ¬ p.spansCoordinateCell i j u v) :
    coordinateCutFlux R i j u v (Path.edgeChain R p.boundary) = 0 := by
  rcases p with ⟨base, first, second, hdistinct⟩
  dsimp only at hp ⊢
  rw [plaquette_boundary_edgeChain, coordinateCutFlux_add,
    coordinateCutFlux_add, coordinateCutFlux_add]
  simp only [coordinateCutFlux_single]
  by_cases hfi : first = i
  · subst first
    have hsi : second ≠ i := hdistinct.symm
    by_cases hsj : second = j
    · subst second
      simp only [Plaquette.spansCoordinateCell, true_and, true_or] at hp
      by_cases hbi : base i = u
      · have hbj : base j ≠ v := by simpa [hbi] using hp
        simp only [step, Pi.add_apply, SignedDirection.delta_forward]
        simp only [unitVector, if_neg hij, if_neg hij.symm, hbi]
        by_cases hbv : base j ≤ v
        · have hb1v : base j + 1 ≤ v := by omega
          simp [hbv, hb1v, hsi]
        · have hb1v : ¬ base j + 1 ≤ v := by omega
          simp [hbv, hb1v, hsi]
      · simp only [step, Pi.add_apply]
        simp [unitVector, hij, hij.symm, hbi]
    · have his : i ≠ second := fun h ↦ hsi h.symm
      have hjs : j ≠ second := fun h ↦ hsj h.symm
      simp only [step, Pi.add_apply, SignedDirection.delta_forward]
      simp [unitVector, hsi, his, hjs]
      split <;> simp_all
  · by_cases hsi : second = i
    · subst second
      have hfj_ne_i : first ≠ i := hdistinct
      by_cases hfj : first = j
      · subst first
        simp only [Plaquette.spansCoordinateCell, true_and, or_true] at hp
        by_cases hbi : base i = u
        · have hbj : base j ≠ v := by simpa [hbi] using hp
          simp only [step, Pi.add_apply, SignedDirection.delta_forward]
          simp only [unitVector, if_neg hij, if_neg hij.symm, hbi]
          by_cases hbv : base j ≤ v
          · have hb1v : base j + 1 ≤ v := by omega
            simp [hbv, hb1v, hfj_ne_i]
          · have hb1v : ¬ base j + 1 ≤ v := by omega
            simp [hbv, hb1v, hfj_ne_i]
        · simp only [step, Pi.add_apply]
          simp [unitVector, hij, hij.symm, hbi]
      · have hif : i ≠ first := fun h ↦ hfi h.symm
        have hjf : j ≠ first := fun h ↦ hfj h.symm
        simp only [step, Pi.add_apply, SignedDirection.delta_forward]
        simp [unitVector, hfi, hif, hjf]
        split <;> simp_all
    · simp [hfi, hsi]

theorem coordinateCutFlux_plaquetteBoundary_eq_zero_of_no_spanning_support
    {d : ℕ} (R : Type*) [CommRing R]
    (i j : Fin d) (hij : i ≠ j) (u v : ℤ) (c : PlaquetteChain d R)
    (h : ∀ p ∈ c.support, ¬ p.spansCoordinateCell i j u v) :
    coordinateCutFlux R i j u v (plaquetteBoundary c) = 0 := by
  classical
  unfold plaquetteBoundary
  rw [Finsupp.sum, coordinateCutFlux_sum]
  apply Finset.sum_eq_zero
  intro p hp
  rw [coordinateCutFlux_smul,
    coordinateCutFlux_plaquette_boundary_eq_zero_of_not_spans R i j hij u v p (h p hp)]
  simp

theorem Path.edgeChain_straight_forward {d : ℕ} (R : Type*) [CommRing R]
    (x : Site d) (i : Fin d) (n : ℕ) :
    Path.edgeChain R (Path.straight x (.forward i) n) =
      ∑ k ∈ Finset.range n,
        Finsupp.single (⟨x + k • unitVector i, i⟩ : PositiveEdge d) 1 := by
  induction n with
  | zero => simp [Path.straight, Path.edgeChain]
  | succ n ih =>
      rw [Path.straight, Path.edgeChain_cons, ih]
      rw [Finset.sum_range_succ]
      congr 1
      simp only [edgeFrom, SignedEdge.toArrow, SignedEdge.edgeChain_forward]
      rw [Path.advance_eq, SignedDirection.delta_forward]

theorem Path.edgeChain_straight_backward {d : ℕ} (R : Type*) [CommRing R]
    (x : Site d) (i : Fin d) (n : ℕ) :
    Path.edgeChain R (Path.straight x (.backward i) n) =
      ∑ k ∈ Finset.range n,
        Finsupp.single (⟨x - (k + 1) • unitVector i, i⟩ : PositiveEdge d) (-1) := by
  induction n with
  | zero => simp [Path.straight, Path.edgeChain]
  | succ n ih =>
      rw [Path.straight, Path.edgeChain_cons, ih]
      rw [Finset.sum_range_succ]
      congr 2
      apply congrArg₂ Finsupp.single
      · simp only [edgeFrom, SignedEdge.toArrow,
          SignedEdge.positive, SignedEdge.target, step, SignedDirection.delta_backward,
          Path.advance_eq]
        apply congrArg (fun z ↦ (⟨z, i⟩ : PositiveEdge d))
        ext q
        simp
        ring
      · rfl

theorem Path.edgeChain_rectangleBoundary {d : ℕ} (R : Type*) [CommRing R]
    (x : Site d) (i j : Fin d) (m n : ℕ) :
    Path.edgeChain R (Path.rectangleBoundary x i j m n) =
      Path.edgeChain R (Path.straight x (.forward i) m) +
      Path.edgeChain R (Path.straight (Path.advance x (.forward i) m) (.forward j) n) +
      Path.edgeChain R (Path.straight
        (Path.advance (Path.advance x (.forward i) m) (.forward j) n)
        (.backward i) m) +
      Path.edgeChain R (Path.straight
        (Path.advance
          (Path.advance (Path.advance x (.forward i) m) (.forward j) n)
          (.backward i) m) (.backward j) n) := by
  simp only [Path.rectangleBoundary, Path.rectangleRaw, Path.edgeChain_castTarget,
    Path.edgeChain_comp]
  abel

theorem coordinateCutFlux_rectangleBoundary_cell {d : ℕ}
    (R : Type*) [CommRing R] (x : Site d) (i j : Fin d) (hij : i ≠ j)
    (m n : ℕ) (a : Fin m) (b : Fin n) :
    coordinateCutFlux R i j (x i + a) (x j + b)
      (Path.edgeChain R (Path.rectangleBoundary x i j m n)) = 1 := by
  rw [Path.edgeChain_rectangleBoundary, coordinateCutFlux_add,
    coordinateCutFlux_add, coordinateCutFlux_add,
    Path.edgeChain_straight_forward, Path.edgeChain_straight_forward,
    Path.edgeChain_straight_backward, Path.edgeChain_straight_backward,
    coordinateCutFlux_sum, coordinateCutFlux_sum, coordinateCutFlux_sum,
    coordinateCutFlux_sum]
  simp only [coordinateCutFlux_single]
  have hai : (a : ℕ) < m := a.isLt
  have hbj : (b : ℕ) < n := b.isLt
  have hji : j ≠ i := hij.symm
  simp only [Path.advance_eq, SignedDirection.delta_forward,
    SignedDirection.delta_backward]
  -- Only the bottom horizontal side crosses the cut.  The top horizontal
  -- side lies strictly above it, and the two vertical sides have direction
  -- `j`.
  have hbottom :
      (∑ k ∈ Finset.range m,
        if (x + k • unitVector i) i = x i + (a : ℤ) ∧
            (x + k • unitVector i) j ≤ x j + (b : ℤ)
        then (1 : R) else 0) = 1 := by
    simp [unitVector, hji, hai]
  simp only [true_and]
  rw [hbottom]
  have hright :
      (∑ k ∈ Finset.range n,
        if (⟨x + m • unitVector i + k • unitVector j, j⟩ : PositiveEdge d).direction = i ∧
            (x + m • unitVector i + k • unitVector j) i = x i + (a : ℤ) ∧
            (x + m • unitVector i + k • unitVector j) j ≤ x j + (b : ℤ)
        then (1 : R) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [hji]
  rw [hright, add_zero]
  have htop :
      (∑ k ∈ Finset.range m,
        if (x + m • unitVector i + n • unitVector j -
              (k + 1) • unitVector i) i = x i + (a : ℤ) ∧
            (x + m • unitVector i + n • unitVector j -
              (k + 1) • unitVector i) j ≤ x j + (b : ℤ)
        then (-1 : R) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hnot : ¬ x j + (n : ℤ) ≤ x j + (b : ℤ) := by omega
    simp [unitVector, hij, hji, hnot]
  rw [htop, add_zero]
  have hleft :
      (∑ k ∈ Finset.range n,
        if j = i ∧
            (x + m • unitVector i + n • unitVector j + m • -unitVector i -
              (k + 1) • unitVector j) i = x i + (a : ℤ) ∧
            (x + m • unitVector i + n • unitVector j + m • -unitVector i -
              (k + 1) • unitVector j) j ≤ x j + (b : ℤ)
        then (-1 : R) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [hji]
  rw [hleft, add_zero]

theorem exists_charge_support_spanning_rectangle_cell_of_taylorScreens
    {d : ℕ} (m : ℕ) (hm : m ≠ 1) (x : Site d)
    (i j : Fin d) (hij : i ≠ j) (r s : ℕ)
    (a b : Plaquette d →₀ ℕ)
    (hscreen : TaylorScreens m (Path.rectangleBoundary x i j r s) a b)
    (u : Fin r) (v : Fin s) :
    ∃ p ∈ (taylorChargeChain m a b).support,
      p.spansCoordinateCell i j (x i + u) (x j + v) := by
  have hone : (1 : ZMod m) ≠ 0 := by
    intro h
    have hdvd : m ∣ 1 := by
      rw [← CharP.cast_eq_zero_iff (ZMod m) m]
      simpa using h
    exact hm (Nat.dvd_one.mp hdvd)
  by_contra hnone
  push Not at hnone
  have hzero := coordinateCutFlux_plaquetteBoundary_eq_zero_of_no_spanning_support
    (ZMod m) i j hij (x i + u) (x j + v) (taylorChargeChain m a b) hnone
  have hchain := (taylorScreens_iff_edgeChain_add_boundary_eq_zero
    m (Path.rectangleBoundary x i j r s) a b).mp hscreen
  have hflux := congrArg (coordinateCutFlux (ZMod m) i j (x i + u) (x j + v)) hchain
  rw [coordinateCutFlux_add,
    coordinateCutFlux_rectangleBoundary_cell (ZMod m) x i j hij r s u v,
    hzero, coordinateCutFlux_zero] at hflux
  exact hone (by simpa using hflux)

theorem taylorChargeChain_support_subset (d m : ℕ) [DecidableEq (Plaquette d)]
    (a b : Plaquette d →₀ ℕ) :
    (taylorChargeChain m a b).support ⊆ a.support ∪ b.support := by
  classical
  intro p hp
  rw [Finset.mem_union]
  by_contra hab
  push Not at hab
  have ha : a p = 0 := by simpa using hab.1
  have hb : b p = 0 := by simpa using hab.2
  apply (Finsupp.mem_support_iff.mp hp)
  rw [taylorChargeChain, taylorMultiplicityChain_eq_mapRange,
    taylorMultiplicityChain_eq_mapRange]
  simp [ha, hb]

theorem Finsupp.card_support_le_sum {α : Type*} (a : α →₀ ℕ) :
    a.support.card ≤ a.sum (fun _ k ↦ k) := by
  classical
  rw [Finsupp.sum, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro p hp
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)

theorem rectangle_area_le_taylorOrder_of_taylorScreens
    {d : ℕ} (m : ℕ) (hm : m ≠ 1) (x : Site d)
    (i j : Fin d) (hij : i ≠ j) (r s : ℕ)
    (a b : Plaquette d →₀ ℕ)
    (hscreen : TaylorScreens m (Path.rectangleBoundary x i j r s) a b) :
    r * s ≤ taylorOrder a b := by
  classical
  let c := taylorChargeChain m a b
  choose p hp hspan using fun q : Fin r × Fin s ↦
    exists_charge_support_spanning_rectangle_cell_of_taylorScreens
      m hm x i j hij r s a b hscreen q.1 q.2
  let f : Fin r × Fin s → {q // q ∈ c.support} := fun q ↦ ⟨p q, hp q⟩
  have hf : Function.Injective f := by
    intro q q' hqq
    have hpq : p q = p q' := congrArg Subtype.val hqq
    have hi := (hspan q).2.1
    have hi' := (hspan q').2.1
    have hj := (hspan q).2.2
    have hj' := (hspan q').2.2
    rw [hpq] at hi
    have hqu : (q.1 : ℤ) = q'.1 := by omega
    rw [hpq] at hj
    have hqv : (q.2 : ℤ) = q'.2 := by omega
    apply Prod.ext
    · apply Fin.ext
      exact_mod_cast hqu
    · apply Fin.ext
      exact_mod_cast hqv
  have hcard : r * s ≤ c.support.card := by
    simpa [f, c] using Fintype.card_le_of_injective f hf
  have hsupp : c.support.card ≤ a.support.card + b.support.card := by
    calc
      c.support.card ≤ (a.support ∪ b.support).card :=
        Finset.card_le_card (taylorChargeChain_support_subset d m a b)
      _ ≤ a.support.card + b.support.card := Finset.card_union_le _ _
  exact hcard.trans (hsupp.trans (Nat.add_le_add
    (Finsupp.card_support_le_sum a) (Finsupp.card_support_le_sum b)))

end
end YangMills.Lattice.Cubic
