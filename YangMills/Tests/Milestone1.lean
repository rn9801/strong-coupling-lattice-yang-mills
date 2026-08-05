/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Lattice.Box
import YangMills.Lattice.Plaquette

/-!
# Milestone 1 executable regressions

These examples lock the public computation rules required by the roadmap: a
plaquette boundary is the expected four-edge signed word, and an arbitrary
coordinate rectangle has the expected four runs and closes at its base point.
-/

namespace YangMills.Tests.Milestone1

open YangMills.Lattice.Cubic

example {d : ℕ} (p : Plaquette d) :
    Path.directions p.boundary =
      [.forward p.first, .forward p.second, .backward p.first, .backward p.second] := by
  simp

example {d : ℕ} (x : Site d) (i j : Fin d) (m n : ℕ) :
    Path.directions (Path.rectangleBoundary x i j m n) =
      List.replicate m (.forward i) ++
      List.replicate n (.forward j) ++
      List.replicate m (.backward i) ++
      List.replicate n (.backward j) := by
  simp

example {d : ℕ} (x : Site d) (i j : Fin d) (m n : ℕ) :
    (Path.rectangleBoundary x i j m n).length = m + n + m + n := by
  simp

#print axioms YangMills.Lattice.Cubic.Plaquette.directions_boundary
#print axioms YangMills.Lattice.Cubic.Path.directions_rectangleBoundary
#print axioms YangMills.Lattice.Cubic.Path.rectangle_closes

end YangMills.Tests.Milestone1
