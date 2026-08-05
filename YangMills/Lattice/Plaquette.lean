/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Lattice.Path

/-!
# Plaquettes and rectangular boundary paths

A plaquette is based at a cubic site and spans two distinct coordinate axes.
Its positively oriented boundary first follows the first axis, then the second,
and returns along the corresponding negative directions. More generally,
`rectangleBoundary` constructs the boundary of an `m`-by-`n` coordinate
rectangle. Closure is proved in `ℤ^d`, while the direction-word lemmas expose
the boundary computation used by later holonomy proofs.
-/

namespace YangMills.Lattice.Cubic

open YangMills.Basic

/-- A positively oriented coordinate plaquette. -/
structure Plaquette (d : ℕ) where
  base : Site d
  first : Fin d
  second : Fin d
  distinct : first ≠ second

namespace Path

variable {d : ℕ}

/-- The unnormalized four-sided path around an `m`-by-`n` rectangle. -/
def rectangleRaw (x : Site d) (i j : Fin d) (m n : ℕ) :
    Path x
      (advance
        (advance
          (advance
            (advance x (.forward i) m)
            (.forward j) n)
          (.backward i) m)
        (.backward j) n) :=
  let x₁ := advance x (.forward i) m
  let x₂ := advance x₁ (.forward j) n
  let x₃ := advance x₂ (.backward i) m
  (straight x (.forward i) m).comp
    ((straight x₁ (.forward j) n).comp
      ((straight x₂ (.backward i) m).comp
        (straight x₃ (.backward j) n)))

/-- Four coordinate sides with opposite pairs of equal length close exactly. -/
theorem rectangle_closes (x : Site d) (i j : Fin d) (m n : ℕ) :
    advance
        (advance
          (advance
            (advance x (.forward i) m)
            (.forward j) n)
          (.backward i) m)
        (.backward j) n = x := by
  rw [advance_eq, advance_eq, advance_eq, advance_eq]
  ext k
  by_cases hi : k = i <;> by_cases hj : k = j <;>
    simp [SignedDirection.delta_forward, SignedDirection.delta_backward, unitVector, hi, hj] <;>
    abel

/-- Positively oriented boundary path of an `m`-by-`n` coordinate rectangle. -/
def rectangleBoundary (x : Site d) (i j : Fin d) (m n : ℕ) : Path x x :=
  OrientedPath.castTarget (rectangleRaw x i j m n) (rectangle_closes x i j m n)

/-- The rectangle boundary computes to its four signed coordinate runs. -/
@[simp]
theorem directions_rectangleBoundary (x : Site d) (i j : Fin d) (m n : ℕ) :
    directions (rectangleBoundary x i j m n) =
      List.replicate m (.forward i) ++
      List.replicate n (.forward j) ++
      List.replicate m (.backward i) ++
      List.replicate n (.backward j) := by
  simp [rectangleBoundary, rectangleRaw]

/-- The rectangle boundary has perimeter `2m + 2n`. -/
@[simp]
theorem length_rectangleBoundary (x : Site d) (i j : Fin d) (m n : ℕ) :
    (rectangleBoundary x i j m n).length = m + n + m + n := by
  simp [rectangleBoundary, rectangleRaw, Nat.add_assoc]

end Path

namespace Plaquette

/-- Translate a plaquette without changing its ordered coordinate directions. -/
def translate {d : ℕ} (v : Site d) (p : Plaquette d) : Plaquette d :=
  ⟨Cubic.translate v p.base, p.first, p.second, p.distinct⟩

/-- The positively oriented four-edge boundary of a plaquette. -/
def boundary {d : ℕ} (p : Plaquette d) : Path p.base p.base :=
  Path.rectangleBoundary p.base p.first p.second 1 1

/-- A plaquette boundary computes to the expected signed four-edge word. -/
@[simp]
theorem directions_boundary {d : ℕ} (p : Plaquette d) :
    Path.directions p.boundary =
      [.forward p.first, .forward p.second, .backward p.first, .backward p.second] := by
  simp [boundary]

/-- A plaquette boundary has four edges. -/
@[simp]
theorem length_boundary {d : ℕ} (p : Plaquette d) : p.boundary.length = 4 := by
  simp [boundary]

/-- Translation preserves the signed boundary word. -/
@[simp]
theorem directions_boundary_translate {d : ℕ} (v : Site d) (p : Plaquette d) :
    Path.directions (p.translate v).boundary = Path.directions p.boundary := by
  simp [Plaquette.translate]

end Plaquette

end YangMills.Lattice.Cubic
