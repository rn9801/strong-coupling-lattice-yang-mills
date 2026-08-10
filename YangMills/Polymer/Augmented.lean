/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.Mayer

/-!
# Finite polymer gases with distinguished source roots

This polymer-only construction adjoins a finite type of source vertices to a
hard-core gas.  Distinct roots are mutually compatible; a root is connected
to a bulk polymer precisely when the supplied `touches` relation holds.  The
source activities are independent variables, so the linear and bilinear
coefficients are selected by the source-scaling lemmas in `Polymer.Mayer`.
-/

namespace YangMills.Polymer

noncomputable section

namespace FinitePolymerModel

variable {P R : Type*} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]

/-- A bulk polymer or an adjoined observable/source root. -/
abbrev AugmentedPolymer (P R : Type*) := P ⊕ R

/-- Add finitely many source roots to a hard-core polymer model. -/
def augmentRoots (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) :
    FinitePolymerModel (AugmentedPolymer P R) where
  incompatible x y := match x, y with
    | Sum.inl γ, Sum.inl δ => M.incompatible γ δ
    | Sum.inl γ, Sum.inr r => touches r γ
    | Sum.inr r, Sum.inl γ => touches r γ
    | Sum.inr r, Sum.inr s => r = s
  decidableIncompatible := fun x y => by
    cases x <;> cases y <;> infer_instance
  symmetric_incompatible := by
    rintro (x | r) (y | s) h
    · exact M.symmetric_incompatible h
    · exact h
    · exact h
    · exact h.symm
  self_incompatible := by
    rintro (x | r)
    · exact M.self_incompatible x
    · rfl
  activity x := match x with
    | Sum.inl γ => M.activity γ
    | Sum.inr r => rootActivity r

@[simp]
theorem augmentRoots_incompatible_bulk_bulk
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (γ δ : P) :
    (M.augmentRoots touches rootActivity).incompatible (Sum.inl γ) (Sum.inl δ) ↔
      M.incompatible γ δ := Iff.rfl

@[simp]
theorem augmentRoots_incompatible_root_bulk
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (r : R) (γ : P) :
    (M.augmentRoots touches rootActivity).incompatible (Sum.inr r) (Sum.inl γ) ↔
      touches r γ := Iff.rfl

@[simp]
theorem augmentRoots_incompatible_bulk_root
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (γ : P) (r : R) :
    (M.augmentRoots touches rootActivity).incompatible (Sum.inl γ) (Sum.inr r) ↔
      touches r γ := Iff.rfl

@[simp]
theorem augmentRoots_incompatible_root_root
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (r s : R) :
    (M.augmentRoots touches rootActivity).incompatible (Sum.inr r) (Sum.inr s) ↔
      r = s := Iff.rfl

@[simp]
theorem augmentRoots_activity_bulk
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (γ : P) :
    (M.augmentRoots touches rootActivity).activity (Sum.inl γ) = M.activity γ := rfl

@[simp]
theorem augmentRoots_activity_root
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (r : R) :
    (M.augmentRoots touches rootActivity).activity (Sum.inr r) = rootActivity r := rfl

end FinitePolymerModel

end

end YangMills.Polymer
