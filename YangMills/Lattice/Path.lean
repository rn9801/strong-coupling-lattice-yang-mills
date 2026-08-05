/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Lattice.Cubic

/-!
# Paths on the cubic lattice

Cubic paths are endpoint-indexed composable words of signed edges. This module
provides their visible direction word, straight coordinate segments, and
translations. Concatenation and reversal are the audited Mathlib operations
`Quiver.Path.comp` and `Quiver.Path.reverse`.
-/

namespace YangMills.Lattice.Cubic

open YangMills.Basic

/-- A typed path between two cubic-lattice sites. -/
abbrev Path {d : ℕ} (x y : Site d) := OrientedPath x y

namespace Path

variable {d : ℕ} {w x y z : Site d}

/-- The signed coordinate word traversed by a path, in traversal order. -/
def directions {x : Site d} : {y : Site d} → Path x y → List (SignedDirection d)
  | _, .nil => []
  | _, .cons p e => directions p ++ [e.1.direction]

@[simp]
theorem directions_nil (x : Site d) : directions (.nil : Path x x) = [] :=
  rfl

@[simp]
theorem directions_cons (p : Path x y) (e : EdgeBetween y z) :
    directions (p.cons e) = directions p ++ [e.1.direction] :=
  rfl

@[simp]
theorem direction_reverse_edge (e : EdgeBetween x y) :
    (Quiver.reverse e).1.direction = e.1.direction.reverse :=
  rfl

@[simp]
theorem directions_toPath (e : EdgeBetween x y) :
    directions e.toPath = [e.1.direction] :=
  rfl

@[simp]
theorem directions_comp (p : Path x y) (q : Path y z) :
    directions (p.comp q) = directions p ++ directions q := by
  induction q with
  | nil => simp
  | cons q e ih => simp [ih, List.append_assoc]

@[simp]
theorem directions_castTarget (p : Path x y) (h : y = z) :
    directions (OrientedPath.castTarget p h) = directions p := by
  subst h
  rfl

/-- Reversal reverses the direction word and every individual direction. -/
@[simp]
theorem directions_reverse (p : Path x y) :
    directions p.reverse = p.directions.reverse.map SignedDirection.reverse := by
  induction p with
  | nil => simp
  | cons p e ih =>
      simp [ih]

/-- Repeatedly take the same signed coordinate step. -/
def advance (x : Site d) (s : SignedDirection d) : ℕ → Site d
  | 0 => x
  | n + 1 => step (advance x s n) s

/-- The straight length-`n` path starting at `x` in signed direction `s`. -/
def straight (x : Site d) (s : SignedDirection d) :
    (n : ℕ) → Path x (advance x s n)
  | 0 => .nil
  | n + 1 => (straight x s n).cons (edgeFrom (advance x s n) s)

@[simp]
theorem length_straight (x : Site d) (s : SignedDirection d) (n : ℕ) :
    (straight x s n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [straight, ih]

@[simp]
theorem directions_straight (x : Site d) (s : SignedDirection d) (n : ℕ) :
    directions (straight x s n) = List.replicate n s := by
  induction n with
  | zero => rfl
  | succ n ih => simp [straight, ih, List.replicate_succ']

/-- Closed form for the endpoint of a straight segment. -/
theorem advance_eq (x : Site d) (s : SignedDirection d) (n : ℕ) :
    advance x s n = x + n • s.delta := by
  induction n with
  | zero => simp [advance]
  | succ n ih =>
      simp only [advance, ih, step, succ_nsmul]
      abel

/-- Translate every edge of a path by the same lattice vector. -/
def translate (v : Site d) (p : Path x y) :
    Path (Cubic.translate v x) (Cubic.translate v y) :=
  (translationPrefunctor v).mapPath p

@[simp]
theorem directions_translate (v : Site d) (p : Path x y) :
    directions (translate v p) = directions p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change directions (translate v p) ++
          [((translationPrefunctor v).map e).1.direction] =
        directions p ++ [e.1.direction]
      rw [ih]
      rfl

end Path

end YangMills.Lattice.Cubic
