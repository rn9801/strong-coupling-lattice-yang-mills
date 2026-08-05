/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Basic.OrientedPath
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Abel

/-!
# Oriented edges of the infinite cubic lattice

A site in dimension `d` is a point of `ℤ^d`. A positive edge is based at a site
and points in one positive coordinate direction. A signed edge has a source and
a signed coordinate direction; its `positive` projection identifies the unique
positive edge on which a future gauge configuration is evaluated. Reversal
therefore changes orientation, not the set of stored variables.

This file is original project infrastructure and does not import the periodic
Douglas compatibility layer.
-/

namespace YangMills.Lattice.Cubic

/-- A site of the infinite `d`-dimensional cubic lattice. -/
abbrev Site (d : ℕ) := Fin d → ℤ

/-- The coordinate unit vector in direction `i`. -/
def unitVector {d : ℕ} (i : Fin d) : Site d :=
  fun j => if j = i then 1 else 0

/-- Orientation relative to a canonical positive edge. -/
inductive Orientation where
  | forward
  | backward
  deriving DecidableEq, Repr

namespace Orientation

/-- Reverse an orientation. -/
@[simp]
def reverse : Orientation → Orientation
  | forward => backward
  | backward => forward

@[simp]
theorem reverse_reverse (o : Orientation) : o.reverse.reverse = o := by
  cases o <;> rfl

end Orientation

/-- A coordinate direction together with an orientation. -/
structure SignedDirection (d : ℕ) where
  axis : Fin d
  orientation : Orientation
  deriving DecidableEq, Repr

namespace SignedDirection

/-- The positive signed coordinate direction. -/
def forward {d : ℕ} (i : Fin d) : SignedDirection d :=
  ⟨i, .forward⟩

/-- The negative signed coordinate direction. -/
def backward {d : ℕ} (i : Fin d) : SignedDirection d :=
  ⟨i, .backward⟩

/-- Reverse a signed coordinate direction. -/
@[simp]
def reverse {d : ℕ} (s : SignedDirection d) : SignedDirection d :=
  ⟨s.axis, s.orientation.reverse⟩

@[simp]
theorem reverse_reverse {d : ℕ} (s : SignedDirection d) : s.reverse.reverse = s := by
  cases s with
  | mk axis orientation => cases orientation <;> rfl

/-- Displacement vector of a signed coordinate step. -/
def delta {d : ℕ} (s : SignedDirection d) : Site d :=
  match s.orientation with
  | .forward => unitVector s.axis
  | .backward => -unitVector s.axis

@[simp]
theorem delta_forward {d : ℕ} (i : Fin d) : delta (forward i) = unitVector i :=
  rfl

@[simp]
theorem delta_backward {d : ℕ} (i : Fin d) : delta (backward i) = -unitVector i :=
  rfl

@[simp]
theorem delta_reverse {d : ℕ} (s : SignedDirection d) : delta s.reverse = -delta s := by
  cases s with
  | mk axis orientation => cases orientation <;> simp [delta]

end SignedDirection

/-- Translate `x` by an arbitrary lattice vector `v`. -/
def translate {d : ℕ} (v x : Site d) : Site d :=
  x + v

/-- Take one signed coordinate step from `x`. -/
def step {d : ℕ} (x : Site d) (s : SignedDirection d) : Site d :=
  x + s.delta

@[simp]
theorem step_reverse {d : ℕ} (x : Site d) (s : SignedDirection d) :
    step (step x s) s.reverse = x := by
  simp only [step, SignedDirection.delta_reverse]
  abel

@[simp]
theorem translate_step {d : ℕ} (v x : Site d) (s : SignedDirection d) :
    translate v (step x s) = step (translate v x) s := by
  simp only [translate, step]
  abel

/-- A canonical positively oriented lattice edge. -/
structure PositiveEdge (d : ℕ) where
  source : Site d
  direction : Fin d
  deriving DecidableEq

namespace PositiveEdge

/-- Terminal site of a positive edge. -/
def target {d : ℕ} (e : PositiveEdge d) : Site d :=
  step e.source (.forward e.direction)

/-- Translate a positive edge without changing its coordinate direction. -/
def translate {d : ℕ} (v : Site d) (e : PositiveEdge d) : PositiveEdge d :=
  ⟨Cubic.translate v e.source, e.direction⟩

@[simp]
theorem source_translate {d : ℕ} (v : Site d) (e : PositiveEdge d) :
    (e.translate v).source = Cubic.translate v e.source :=
  rfl

@[simp]
theorem target_translate {d : ℕ} (v : Site d) (e : PositiveEdge d) :
    (e.translate v).target = Cubic.translate v e.target := by
  exact (translate_step v e.source (.forward e.direction)).symm

end PositiveEdge

/-- A located oriented edge. Its positive representative is computed below. -/
structure SignedEdge (d : ℕ) where
  source : Site d
  direction : SignedDirection d
  deriving DecidableEq

namespace SignedEdge

/-- Terminal site of a signed edge. -/
def target {d : ℕ} (e : SignedEdge d) : Site d :=
  step e.source e.direction

/-- Reverse an edge, exchanging its source and target. -/
def reverse {d : ℕ} (e : SignedEdge d) : SignedEdge d :=
  ⟨e.target, e.direction.reverse⟩

@[simp]
theorem source_reverse {d : ℕ} (e : SignedEdge d) : e.reverse.source = e.target :=
  rfl

@[simp]
theorem target_reverse {d : ℕ} (e : SignedEdge d) : e.reverse.target = e.source :=
  step_reverse e.source e.direction

@[simp]
theorem reverse_reverse {d : ℕ} (e : SignedEdge d) : e.reverse.reverse = e := by
  cases e with
  | mk source direction =>
      change SignedEdge.mk (step (step source direction) direction.reverse)
          direction.reverse.reverse = SignedEdge.mk source direction
      rw [step_reverse, SignedDirection.reverse_reverse]

/-- The canonical positive edge underlying a signed edge. -/
def positive {d : ℕ} (e : SignedEdge d) : PositiveEdge d :=
  match e.direction.orientation with
  | .forward => ⟨e.source, e.direction.axis⟩
  | .backward => ⟨e.target, e.direction.axis⟩

/-- Reversing an edge does not change the positive edge storing its variable. -/
@[simp]
theorem positive_reverse {d : ℕ} (e : SignedEdge d) : e.reverse.positive = e.positive := by
  cases e with
  | mk source direction =>
      cases direction with
      | mk axis orientation =>
          cases orientation with
          | forward =>
              change PositiveEdge.mk
                  (step (step source (.forward axis)) (.backward axis)) axis =
                PositiveEdge.mk source axis
              exact congrArg (fun z => PositiveEdge.mk z axis)
                (step_reverse source (.forward axis))
          | backward => rfl

/-- Translate a signed edge without changing its signed direction. -/
def translate {d : ℕ} (v : Site d) (e : SignedEdge d) : SignedEdge d :=
  ⟨Cubic.translate v e.source, e.direction⟩

@[simp]
theorem source_translate {d : ℕ} (v : Site d) (e : SignedEdge d) :
    (e.translate v).source = Cubic.translate v e.source :=
  rfl

@[simp]
theorem target_translate {d : ℕ} (v : Site d) (e : SignedEdge d) :
    (e.translate v).target = Cubic.translate v e.target := by
  exact (translate_step v e.source e.direction).symm

/-- Translation commutes with passage to the stored positive edge. -/
@[simp]
theorem positive_translate {d : ℕ} (v : Site d) (e : SignedEdge d) :
    (e.translate v).positive = e.positive.translate v := by
  cases e with
  | mk source direction =>
      cases direction with
      | mk axis orientation =>
          cases orientation <;>
            simp [positive, SignedEdge.translate, PositiveEdge.translate, target]

@[simp]
theorem translate_reverse {d : ℕ} (v : Site d) (e : SignedEdge d) :
    e.reverse.translate v = (e.translate v).reverse := by
  cases e
  simp [reverse, translate, target]

end SignedEdge

/-- Signed cubic edges form the arrows of the cubic-site quiver. -/
instance instQuiverSite (d : ℕ) : Quiver (Site d) where
  Hom x y := {e : SignedEdge d // e.source = x ∧ e.target = y}

/-- A signed edge with endpoints enforced by its type. -/
abbrev EdgeBetween {d : ℕ} (x y : Site d) := x ⟶ y

/-- Regard a located signed edge as a typed cubic arrow. -/
def SignedEdge.toArrow {d : ℕ} (e : SignedEdge d) : EdgeBetween e.source e.target :=
  ⟨e, rfl, rfl⟩

/-- The signed edge starting at `x` in direction `s`. -/
def edgeFrom {d : ℕ} (x : Site d) (s : SignedDirection d) :
    EdgeBetween x (step x s) :=
  (SignedEdge.mk x s).toArrow

@[simp]
theorem edgeFrom_direction {d : ℕ} (x : Site d) (s : SignedDirection d) :
    (edgeFrom x s).1.direction = s :=
  rfl

/-- Reverse typed cubic arrows. -/
instance instHasInvolutiveReverseSite (d : ℕ) : Quiver.HasInvolutiveReverse (Site d) where
  reverse' := fun e =>
    ⟨e.1.reverse, by simpa using e.2.2, by simpa using e.2.1⟩
  inv' := fun e => by
    apply Subtype.ext
    exact SignedEdge.reverse_reverse e.1

/-- Translation as a morphism of cubic-site quivers. -/
def translationPrefunctor {d : ℕ} (v : Site d) : Site d ⥤q Site d where
  obj := Cubic.translate v
  map := fun e =>
    ⟨e.1.translate v,
      by simpa only [SignedEdge.source_translate] using congrArg (Cubic.translate v) e.2.1,
      by simpa only [SignedEdge.target_translate] using congrArg (Cubic.translate v) e.2.2⟩

end YangMills.Lattice.Cubic
