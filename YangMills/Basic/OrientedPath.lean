/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib.Combinatorics.Quiver.Symmetric

/-!
# Typed oriented paths

This module fixes the project's generic path convention. A path is Mathlib's
endpoint-indexed `Quiver.Path`: composability is enforced by its type, paths are
composed with `Quiver.Path.comp`, and a quiver with involutive edge reversal
inherits `Quiver.Path.reverse`.

The small casting operations below are useful when a geometric endpoint is
propositionally, rather than definitionally, equal to its normalized form.
-/

namespace YangMills.Basic

universe u v

/-- A typed composable word of arrows in a quiver. -/
abbrev OrientedPath {V : Type u} [Quiver.{v} V] (x y : V) := Quiver.Path x y

namespace OrientedPath

variable {V : Type u} [Quiver.{v} V] {w x y z : V}

/-- Change the recorded terminal vertex along an equality. -/
def castTarget (p : OrientedPath x y) (h : y = z) : OrientedPath x z :=
  h ▸ p

/-- Change the recorded initial vertex along an equality. -/
def castSource (p : OrientedPath x z) (h : x = w) : OrientedPath w z :=
  h ▸ p

@[simp]
theorem castTarget_rfl (p : OrientedPath x y) : castTarget p rfl = p :=
  rfl

@[simp]
theorem castSource_rfl (p : OrientedPath x y) : castSource p rfl = p :=
  rfl

@[simp]
theorem length_castTarget (p : OrientedPath x y) (h : y = z) :
    (castTarget p h).length = p.length := by
  subst h
  rfl

@[simp]
theorem length_castSource (p : OrientedPath x y) (h : x = w) :
    (castSource p h).length = p.length := by
  subst h
  rfl

end OrientedPath

end YangMills.Basic
