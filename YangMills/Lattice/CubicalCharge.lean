/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.Holonomy
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ZMod.Basic

/-!
# Finite cubical charge chains

This file contains only the small cellular-chain fragment needed by the
center-selection argument.  A path is sent to its signed incidence 1-chain
on stored positive edges, and the boundary of a finitely supported
plaquette 2-chain is obtained by linear extension.  No general homology API
is introduced.

The orientation convention agrees with `Gauge.signedEdgeValue`: a forward
edge has coefficient `+1`, while a backward edge has coefficient `-1` on
the same stored positive edge.
-/

namespace YangMills.Lattice.Cubic

open scoped BigOperators

noncomputable section

/-- Finitely supported edge-valued cubical 1-chains. -/
abbrev EdgeChain (d : ℕ) (R : Type*) [Zero R] := PositiveEdge d →₀ R

/-- Finitely supported plaquette-valued cubical 2-chains. -/
abbrev PlaquetteChain (d : ℕ) (R : Type*) [Zero R] := Plaquette d →₀ R

variable {d : ℕ} {R : Type*} [CommRing R]

/-- The signed incidence chain of one oriented edge. -/
def SignedEdge.edgeChain (R : Type*) [CommRing R] (e : SignedEdge d) :
    EdgeChain d R :=
  match e.direction.orientation with
  | .forward => Finsupp.single e.positive 1
  | .backward => Finsupp.single e.positive (-1)

namespace SignedEdge

@[simp]
theorem edgeChain_forward (R : Type*) [CommRing R] (x : Site d) (i : Fin d) :
    (SignedEdge.mk x (.forward i)).edgeChain R =
      Finsupp.single ⟨x, i⟩ 1 :=
  rfl

@[simp]
theorem edgeChain_backward (R : Type*) [CommRing R] (x : Site d) (i : Fin d) :
    (SignedEdge.mk x (.backward i)).edgeChain R =
      Finsupp.single (SignedEdge.mk x (.backward i)).positive (-1) :=
  rfl

end SignedEdge

namespace Path

/-- Signed positive-edge incidence chain of a typed cubic path. -/
def edgeChain (R : Type*) [CommRing R] {x : Site d} :
    {y : Site d} → Path x y → EdgeChain d R
  | _, .nil => 0
  | _, .cons p e => edgeChain R p + e.1.edgeChain R

@[simp]
theorem edgeChain_nil (R : Type*) [CommRing R] (x : Site d) :
    edgeChain R (.nil : Path x x) = 0 :=
  rfl

@[simp]
theorem edgeChain_cons (R : Type*) [CommRing R]
    {x y z : Site d} (p : Path x y) (e : EdgeBetween y z) :
    edgeChain R (p.cons e) = edgeChain R p + e.1.edgeChain R :=
  rfl

@[simp]
theorem edgeChain_castTarget (R : Type*) [CommRing R]
    {x y z : Site d} (p : Path x y) (h : y = z) :
    edgeChain R (YangMills.Basic.OrientedPath.castTarget p h) = edgeChain R p := by
  subst h
  rfl

@[simp]
theorem edgeChain_comp (R : Type*) [CommRing R]
    {x y z : Site d} (p : Path x y) (q : Path y z) :
    edgeChain R (p.comp q) = edgeChain R p + edgeChain R q := by
  induction q with
  | nil => simp
  | cons q e ih => simp [ih, add_assoc]

/-- A path incidence coefficient vanishes away from the path's stored-edge
support. -/
theorem edgeChain_apply_eq_zero_of_not_mem_edgeSupport
    (R : Type*) [CommRing R] {x y : Site d} (p : Path x y)
    (e : PositiveEdge d) (he : e ∉ p.edgeSupport) :
    edgeChain R p e = 0 := by
  induction p with
  | nil => simp
  | cons p q ih =>
      simp only [edgeSupport_cons, Finset.mem_insert, not_or] at he
      rw [edgeChain_cons, Finsupp.add_apply, ih he.2]
      have hne : q.1.positive ≠ e := fun h ↦ he.1 h.symm
      cases hq : q.1.direction.orientation <;>
        simp [SignedEdge.edgeChain, hq, Finsupp.single_apply, hne]

/-- The integer incidence number of a path at one stored positive edge. -/
def edgeIncidence {x y : Site d} (p : Path x y) (e : PositiveEdge d) : ℤ :=
  edgeChain ℤ p e

@[simp]
theorem edgeIncidence_nil (x : Site d) (e : PositiveEdge d) :
    edgeIncidence (.nil : Path x x) e = 0 := by
  simp [edgeIncidence]

@[simp]
theorem edgeIncidence_cons {x y z : Site d}
    (p : Path x y) (q : EdgeBetween y z) (e : PositiveEdge d) :
    edgeIncidence (p.cons q) e =
      edgeIncidence p e + q.1.edgeChain ℤ e := by
  simp [edgeIncidence]

end Path

/-- Cellular boundary of a finite plaquette 2-chain, by linear extension of
the oriented four-edge plaquette boundary. -/
def plaquetteBoundary (c : PlaquetteChain d R) : EdgeChain d R :=
  c.sum fun p a ↦ (a • Path.edgeChain R p.boundary : EdgeChain d R)

@[simp]
theorem plaquetteBoundary_zero :
    plaquetteBoundary (0 : PlaquetteChain d R) = 0 := by
  simp [plaquetteBoundary]

@[simp]
theorem plaquetteBoundary_single (p : Plaquette d) (a : R) :
    plaquetteBoundary (Finsupp.single p a : PlaquetteChain d R) =
      (a • Path.edgeChain R p.boundary : EdgeChain d R) := by
  simp [plaquetteBoundary]

theorem plaquetteBoundary_add (c c' : PlaquetteChain d R) :
    plaquetteBoundary (c + c') = plaquetteBoundary c + plaquetteBoundary c' := by
  classical
  unfold plaquetteBoundary
  apply Finsupp.sum_add_index
  · intro p _
    exact zero_smul R (Path.edgeChain R p.boundary)
  · intro p _ a b
    exact add_smul a b (Path.edgeChain R p.boundary)

theorem plaquetteBoundary_neg (c : PlaquetteChain d R) :
    plaquetteBoundary (-c) = -plaquetteBoundary c := by
  classical
  rw [← neg_one_smul R c, ← neg_one_smul R (plaquetteBoundary c)]
  unfold plaquetteBoundary
  rw [Finsupp.sum_smul_index']
  · simp only [neg_smul, one_smul]
    change (∑ p ∈ c.support,
        -(c p • Path.edgeChain R p.boundary)) =
      -∑ p ∈ c.support, c p • Path.edgeChain R p.boundary
    exact (Finset.sum_neg_distrib
      (f := fun p ↦ (c p • Path.edgeChain R p.boundary : EdgeChain d R)))
  · intro p
    exact zero_smul R (Path.edgeChain R p.boundary)

theorem plaquetteBoundary_sub (c c' : PlaquetteChain d R) :
    plaquetteBoundary (c - c') = plaquetteBoundary c - plaquetteBoundary c' := by
  rw [sub_eq_add_neg, plaquetteBoundary_add, plaquetteBoundary_neg, sub_eq_add_neg]

/-! ## Finite-order center-charge fillings -/

/-- The charge 2-chain associated with the two Taylor multiplicity fields.
`a` counts character insertions and `b` conjugate-character insertions. -/
def taylorChargeChain (m : ℕ)
    (a b : Plaquette d →₀ ℕ) : PlaquetteChain d (ZMod m) :=
  a.sum (fun p k ↦ Finsupp.single p (k : ZMod m)) -
    b.sum (fun p k ↦ Finsupp.single p (k : ZMod m))

/-- Total Taylor order of two finitely supported multiplicity fields. -/
def taylorOrder (a b : Plaquette d →₀ ℕ) : ℕ :=
  a.sum (fun _ k ↦ k) + b.sum (fun _ k ↦ k)

/-- Net integer center charge of a Wilson-source Taylor monomial at one
stored positive edge. -/
def taylorChargeAt {x : Site d} (C : Path x x)
    (a b : Plaquette d →₀ ℕ) (e : PositiveEdge d) : ℤ :=
  C.edgeIncidence e +
    a.sum (fun p k ↦ (k : ℤ) * p.boundary.edgeIncidence e) -
    b.sum (fun p k ↦ (k : ℤ) * p.boundary.edgeIncidence e)

/-- A pair of Taylor multiplicities screens a loop modulo the center phase
order when its charged plaquette boundary cancels the loop 1-chain.  This
coefficientwise form is exactly `∂(a-b) = -[C]` in `ZMod m` and is
convenient for the edgewise Haar argument. -/
def TaylorScreens (m : ℕ) {x : Site d} (C : Path x x)
    (a b : Plaquette d →₀ ℕ) : Prop :=
  ∀ e : PositiveEdge d, (taylorChargeAt C a b e : ZMod m) = 0

/-- Reduction modulo `m` commutes with the path incidence chain. -/
theorem edgeChain_zmod_eq_mapRange {x y : Site d} (C : Path x y)
    (m : ℕ) :
    Path.edgeChain (ZMod m) C =
      Finsupp.mapRange (fun z : ℤ ↦ (z : ZMod m)) (by simp)
        (Path.edgeChain ℤ C) := by
  induction C with
  | nil => simp
  | cons C q ih =>
      rw [Path.edgeChain_cons, Path.edgeChain_cons, ih,
        Finsupp.mapRange_add (by simp)]
      cases hq : q.1.direction.orientation
      · simp [SignedEdge.edgeChain, hq]
      · rw [show q.1.edgeChain ℤ =
            -Finsupp.single q.1.positive 1 by
          simp [SignedEdge.edgeChain, hq]]
        ext e
        by_cases he : q.1.positive = e
        · subst e
          simp [SignedEdge.edgeChain, hq]
        · simp [SignedEdge.edgeChain, hq, he]

theorem edgeChain_zmod_apply {x y : Site d} (C : Path x y)
    (m : ℕ) (e : PositiveEdge d) :
    Path.edgeChain (ZMod m) C e = (Path.edgeIncidence C e : ZMod m) := by
  rw [edgeChain_zmod_eq_mapRange]
  rfl

/-- Boundary of one Taylor multiplicity field after reduction modulo `m`. -/
theorem taylorMultiplicityChain_eq_mapRange
    (m : ℕ) (a : Plaquette d →₀ ℕ) :
    (a.sum fun p k ↦ Finsupp.single p (k : ZMod m)) =
      Finsupp.mapRange (fun k : ℕ ↦ (k : ZMod m)) (by simp) a := by
  classical
  induction a using Finsupp.induction with
  | zero => simp
  | @single_add p k a hp hk ih =>
      rw [Finsupp.sum_add_index (by simp) (by simp), ih,
        Finsupp.mapRange_add (by simp)]
      simp

theorem plaquetteBoundary_taylorMultiplicity_apply
    (m : ℕ) (a : Plaquette d →₀ ℕ) (e : PositiveEdge d) :
    plaquetteBoundary
        (a.sum fun p k ↦ Finsupp.single p (k : ZMod m)) e =
      a.sum (fun p k ↦
        (((k : ℤ) * p.boundary.edgeIncidence e : ℤ) : ZMod m)) := by
  classical
  rw [taylorMultiplicityChain_eq_mapRange]
  unfold plaquetteBoundary
  rw [Finsupp.sum_mapRange_index (fun _ ↦ by simp)]
  rw [Finsupp.sum_apply]
  rw [Finsupp.sum]
  simp only [Finsupp.smul_apply, edgeChain_zmod_apply]
  apply Finset.sum_congr rfl
  intro p hp
  change (a p : ZMod m) * (p.boundary.edgeIncidence e : ZMod m) = _
  norm_cast

theorem cast_taylorMultiplicitySum
    (m : ℕ) (a : Plaquette d →₀ ℕ) (e : PositiveEdge d) :
    ((a.sum fun p k ↦ (k : ℤ) * p.boundary.edgeIncidence e : ℤ) : ZMod m) =
      a.sum (fun p k ↦
        (((k : ℤ) * p.boundary.edgeIncidence e : ℤ) : ZMod m)) := by
  classical
  rw [Finsupp.sum]
  exact map_sum (Int.castAddHom (ZMod m)) _ _

/-- Chain form of the coefficientwise Taylor screening equation. -/
theorem taylorScreens_iff_edgeChain_add_boundary_eq_zero
    (m : ℕ) {x : Site d} (C : Path x x)
    (a b : Plaquette d →₀ ℕ) :
    TaylorScreens m C a b ↔
      Path.edgeChain (ZMod m) C +
        plaquetteBoundary (taylorChargeChain m a b) = 0 := by
  rw [Finsupp.ext_iff]
  simp only [Finsupp.add_apply, Finsupp.zero_apply]
  unfold TaylorScreens taylorChargeAt taylorChargeChain
  simp_rw [edgeChain_zmod_apply, plaquetteBoundary_sub, Finsupp.sub_apply,
    plaquetteBoundary_taylorMultiplicity_apply]
  constructor
  · intro h e
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_neg, sub_eq_add_neg, add_assoc,
      cast_taylorMultiplicitySum] using h e
  · intro h e
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_neg, sub_eq_add_neg, add_assoc,
      cast_taylorMultiplicitySum] using h e

/-- The algebraically natural center filling area: the least total Taylor
order among finite charge fields that screen the loop.  As usual for
`Nat.sInf`, this is `0` if no screening field exists; every application below
produces a screening field from a nonzero Taylor monomial. -/
def centerFillingArea (m : ℕ) {x : Site d} (C : Path x x) : ℕ :=
  sInf {N : ℕ | ∃ a b : Plaquette d →₀ ℕ,
    TaylorScreens m C a b ∧ taylorOrder a b = N}

/-- Every screening Taylor field has order at least the center filling area. -/
theorem centerFillingArea_le_taylorOrder (m : ℕ) {x : Site d}
    (C : Path x x) (a b : Plaquette d →₀ ℕ)
    (h : TaylorScreens m C a b) :
    centerFillingArea m C ≤ taylorOrder a b := by
  apply Nat.sInf_le
  exact ⟨a, b, h, rfl⟩

/-- The number of distinct stored positive edges read by a path is bounded by
its path length. -/
theorem Path.card_edgeSupport_le_length {x y : Site d} (C : Path x y) :
    C.edgeSupport.card ≤ C.length := by
  induction C with
  | nil => simp
  | cons C e ih =>
      rw [Path.edgeSupport_cons, Quiver.Path.length_cons]
      exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ih 1)

end

end YangMills.Lattice.Cubic
