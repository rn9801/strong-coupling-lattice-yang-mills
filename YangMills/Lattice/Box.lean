/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Lattice.Cubic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Pi.Interval

/-!
# Finite cubic boxes

A box is a nonempty coordinatewise closed interval in `ℤ^d`. Its site set is a
`Finset`, and its positive-edge set contains precisely the canonical edges whose
two endpoints lie in the box. This is the finite index set on which later gauge
configurations and product Haar measures will be built.
-/

namespace YangMills.Lattice.Cubic

/-- A nonempty coordinatewise closed box in `ℤ^d`. -/
structure Box (d : ℕ) where
  lower : Site d
  upper : Site d
  lower_le_upper : lower ≤ upper

namespace Box

/-- The finite set of lattice sites in a box. -/
def sites {d : ℕ} (b : Box d) : Finset (Site d) :=
  Finset.Icc b.lower b.upper

@[simp]
theorem mem_sites {d : ℕ} (b : Box d) (x : Site d) :
    x ∈ b.sites ↔ b.lower ≤ x ∧ x ≤ b.upper := by
  simp [sites]

/-- The lower corner witnesses that every box has a site. -/
theorem sites_nonempty {d : ℕ} (b : Box d) : b.sites.Nonempty := by
  exact ⟨b.lower, by simp [b.lower_le_upper]⟩

/-- A positive edge is internal when both endpoints lie in the box. -/
def ContainsPositiveEdge {d : ℕ} (b : Box d) (e : PositiveEdge d) : Prop :=
  e.source ∈ b.sites ∧ e.target ∈ b.sites

/-- The finite set of canonical positive edges internal to a box. -/
def positiveEdges {d : ℕ} (b : Box d) : Finset (PositiveEdge d) :=
  (((b.sites.product (Finset.univ : Finset (Fin d))).filter fun p =>
      step p.1 (.forward p.2) ∈ b.sites).image fun p =>
        PositiveEdge.mk p.1 p.2)

@[simp]
theorem mem_positiveEdges {d : ℕ} (b : Box d) (e : PositiveEdge d) :
    e ∈ b.positiveEdges ↔ b.ContainsPositiveEdge e := by
  constructor
  · intro he
    simp only [positiveEdges, Finset.mem_image] at he
    obtain ⟨p, hp, rfl⟩ := he
    have hpFilter := Finset.mem_filter.mp hp
    have hpSource := (Finset.mem_product.mp hpFilter.1).1
    exact ⟨hpSource, hpFilter.2⟩
  · rintro ⟨hsource, htarget⟩
    simp only [positiveEdges, Finset.mem_image]
    refine ⟨(e.source, e.direction), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨hsource, Finset.mem_univ _⟩, htarget⟩
    · cases e
      rfl

/-- Translate a box by a lattice vector. -/
def translate {d : ℕ} (v : Site d) (b : Box d) : Box d where
  lower := Cubic.translate v b.lower
  upper := Cubic.translate v b.upper
  lower_le_upper := fun i => by
    simpa only [Cubic.translate, Pi.add_apply, add_comm] using
      add_le_add_right (b.lower_le_upper i) (v i)

end Box

end YangMills.Lattice.Cubic
