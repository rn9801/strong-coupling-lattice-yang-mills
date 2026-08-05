/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Lattice.Cubic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Group

/-!
# Cubic-lattice gauge configurations

A configuration stores one group element on each canonical positive edge of
the infinite cubic lattice. Values on negatively oriented edges are obtained by
inversion. Site fields act by left multiplication at the source and inverse
right multiplication at the target.
-/

namespace YangMills.Gauge

open Lattice.Cubic

/-- A gauge configuration on the infinite cubic lattice. -/
abbrev Configuration (d : ℕ) (G : Type*) := PositiveEdge d → G

/-- A sitewise gauge transformation on the infinite cubic lattice. -/
abbrev GaugeTransformation (d : ℕ) (G : Type*) := Site d → G

variable {d : ℕ} {G : Type*} [Group G]

/-- Evaluate a stored positive-edge configuration on an oriented edge. -/
def signedEdgeValue (A : Configuration d G) (e : SignedEdge d) : G :=
  match e.direction.orientation with
  | .forward => A ⟨e.source, e.direction.axis⟩
  | .backward => (A ⟨e.target, e.direction.axis⟩)⁻¹

@[simp]
theorem signedEdgeValue_forward (A : Configuration d G) (x : Site d) (i : Fin d) :
    signedEdgeValue A ⟨x, .forward i⟩ = A ⟨x, i⟩ :=
  rfl

@[simp]
theorem signedEdgeValue_backward (A : Configuration d G) (x : Site d) (i : Fin d) :
    signedEdgeValue A ⟨x, .backward i⟩ =
      (A ⟨step x (.backward i), i⟩)⁻¹ :=
  rfl

/-- Reversing an oriented edge inverts its evaluated group element. -/
@[simp]
theorem signedEdgeValue_reverse (A : Configuration d G) (e : SignedEdge d) :
    signedEdgeValue A e.reverse = (signedEdgeValue A e)⁻¹ := by
  cases e with
  | mk source direction =>
      cases direction with
      | mk axis orientation =>
          cases orientation with
          | forward =>
              simp only [SignedEdge.reverse, SignedDirection.reverse, Orientation.reverse,
                signedEdgeValue, SignedEdge.target]
              change (A ⟨step (step source (.forward axis)) (.backward axis), axis⟩)⁻¹ =
                (A ⟨source, axis⟩)⁻¹
              have hstep : step (step source (.forward axis)) (.backward axis) = source :=
                step_reverse source (.forward axis)
              rw [hstep]
          | backward =>
              simp [SignedEdge.reverse, SignedDirection.reverse, signedEdgeValue,
                SignedEdge.target]

/-- A signed-edge value only reads its underlying stored positive edge. -/
theorem signedEdgeValue_eq_of_eq_positive
    {A B : Configuration d G} (e : SignedEdge d) (h : A e.positive = B e.positive) :
    signedEdgeValue A e = signedEdgeValue B e := by
  cases e with
  | mk source direction =>
      cases direction with
      | mk axis orientation =>
          cases orientation with
          | forward => exact h
          | backward => exact congrArg Inv.inv h

/-- Apply a site gauge transformation to every stored positive edge. -/
def gaugeTransform (g : GaugeTransformation d G) (A : Configuration d G) :
    Configuration d G :=
  fun e => g e.source * A e * (g e.target)⁻¹

@[simp]
theorem gaugeTransform_apply (g : GaugeTransformation d G) (A : Configuration d G)
    (e : PositiveEdge d) :
    gaugeTransform g A e = g e.source * A e * (g e.target)⁻¹ :=
  rfl

/-- The identity site field acts trivially. -/
@[simp]
theorem gaugeTransform_one (A : Configuration d G) :
    gaugeTransform (1 : GaugeTransformation d G) A = A := by
  funext e
  simp [gaugeTransform]

/-- Pointwise multiplication of site fields agrees with composition of their actions. -/
theorem gaugeTransform_mul (g h : GaugeTransformation d G) (A : Configuration d G) :
    gaugeTransform (g * h) A = gaugeTransform g (gaugeTransform h A) := by
  funext e
  simp only [gaugeTransform, Pi.mul_apply, mul_inv_rev]
  group

instance instSMulGaugeTransformationConfiguration :
    SMul (GaugeTransformation d G) (Configuration d G) :=
  ⟨gaugeTransform⟩

/-- Gauge transformations form a genuine left action on configurations. -/
instance instMulActionGaugeTransformationConfiguration :
    MulAction (GaugeTransformation d G) (Configuration d G) where
  one_smul := gaugeTransform_one
  mul_smul := gaugeTransform_mul

@[simp]
theorem smul_configuration_apply (g : GaugeTransformation d G) (A : Configuration d G)
    (e : PositiveEdge d) :
    (g • A) e = g e.source * A e * (g e.target)⁻¹ :=
  rfl

/-- Gauge covariance for the value of a single signed edge. -/
theorem signedEdgeValue_gaugeTransform
    (g : GaugeTransformation d G) (A : Configuration d G) (e : SignedEdge d) :
    signedEdgeValue (gaugeTransform g A) e =
      g e.source * signedEdgeValue A e * (g e.target)⁻¹ := by
  cases e with
  | mk source direction =>
      cases direction with
      | mk axis orientation =>
          cases orientation with
          | forward => rfl
          | backward =>
              change
                (g (step source (.backward axis)) *
                  A ⟨step source (.backward axis), axis⟩ *
                    (g (step (step source (.backward axis)) (.forward axis)))⁻¹)⁻¹ =
                  g source * (A ⟨step source (.backward axis), axis⟩)⁻¹ *
                    (g (step source (.backward axis)))⁻¹
              have hstep : step (step source (.backward axis)) (.forward axis) = source :=
                step_reverse source (.backward axis)
              rw [hstep]
              group

end YangMills.Gauge
