/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import LGT.Lattice.LatticeDistance
import LGT.MassGap.Locality

/-!
# Geometry compatibility with Douglas `LGT`

This file is the narrow adapter for finite periodic-torus links, plaquettes,
finite supports, and graph distances in Michael R. Douglas's `LGT` repository.
It introduces project-facing wrapper names and proves their exact relationship
to upstream support and distance declarations.

Upstream: <https://github.com/mrdouglasny/lgt>
Pinned commit: `b8793ccf6a51e00e9e2b1685ba191b8626e37137`
License: Apache-2.0

These wrappers are regression infrastructure only. The project's eventual
cubic-lattice API lives on `ℤ^d` and will not import this module.
-/

namespace YangMills.Compat.Douglas

noncomputable section

/-- The native upstream type of canonical links on a periodic cubic lattice. -/
abbrev PeriodicLink := LatticeLink

/-- The native upstream type of canonical plaquettes on a periodic cubic lattice. -/
abbrev PeriodicPlaquette := LatticePlaquette

/-- Project-facing finite support of an upstream periodic plaquette. -/
def periodicPlaquetteSupport {d N : ℕ} [DecidableEq (PeriodicLink d N)]
    (p : PeriodicPlaquette d N) : Finset (PeriodicLink d N) :=
  p.boundaryLinkFinset

/-- The finite plaquette support viewed as a set for Mathlib's `DependsOn`. -/
def periodicPlaquetteSupportSet {d N : ℕ} [DecidableEq (PeriodicLink d N)]
    (p : PeriodicPlaquette d N) : Set (PeriodicLink d N) :=
  periodicPlaquetteSupport p

/-- Our finite-support wrapper agrees exactly with Douglas's locality support. -/
theorem periodicPlaquetteSupportSet_eq_upstream {d N : ℕ}
    [DecidableEq (PeriodicLink d N)] (p : PeriodicPlaquette d N) :
    periodicPlaquetteSupportSet p = plaquetteLinkSupport p := by
  ext e
  simp only [periodicPlaquetteSupportSet, periodicPlaquetteSupport,
    LatticePlaquette.boundaryLinkFinset, Finset.coe_image, Finset.coe_univ,
    Set.image_univ, Set.mem_range, plaquetteLinkSupport]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with he | he | he | he
    · exact ⟨0, he.symm⟩
    · exact ⟨1, he.symm⟩
    · exact ⟨2, he.symm⟩
    · exact ⟨3, he.symm⟩

/-- Project-facing name for Douglas's shared-plaquette link-graph distance. -/
abbrev periodicLinkDistance (d N : ℕ) := linkGraphDist d N

/-- Project-facing name for the periodic `L¹` distance between plaquette anchors. -/
abbrev periodicPlaquetteDistance (d N : ℕ) := latticePlaquetteDist d N

/--
Douglas's support-distance comparison transported through our finite-support
wrapper: boundary links of two plaquettes are separated in the link graph by at
least half their anchor distance, up to the upstream truncation convention.
-/
theorem periodicPlaquetteDistance_support_lowerBound
    (d N : ℕ) [NeZero N] [DecidableEq (PeriodicLink d N)]
    (hd : 2 ≤ d) (hN : 2 < N)
    {p q : PeriodicPlaquette d N} {x y : PeriodicLink d N}
    (hx : x ∈ periodicPlaquetteSupport p)
    (hy : y ∈ periodicPlaquetteSupport q) :
    (periodicPlaquetteDistance d N p q - 1) / 2 ≤
      periodicLinkDistance d N x y := by
  exact linkGraphDist_boundary_lower_bound d N hd hN hx hy

end

end YangMills.Compat.Douglas
