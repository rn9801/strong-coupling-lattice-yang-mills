/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.InfiniteReflection
import YangMills.StrongCoupling.ThermodynamicBoxes

/-!
# Symmetric cofinal boxes for reflection positivity

The centered box `[-n,n]^d` is invariant under coordinate reflection through
the origin.  For link reflection through `1/2`, the distinguished coordinate
is instead `[-n,n+1]`; all other coordinates remain `[-n,n]`.
-/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

/-- A box symmetric about `x τ = 1/2`. -/
def linkSymmetricBox (d n : ℕ) (τ : Fin d) : Box d where
  lower := fun _ => -(n : ℤ)
  upper := fun i => if i = τ then (n : ℤ) + 1 else (n : ℤ)
  lower_le_upper := fun i => by
    by_cases hi : i = τ
    · simp [hi]
      omega
    · simp [hi]

@[simp]
theorem mem_linkSymmetricBox_sites {d n : ℕ} (τ : Fin d) (x : Site d) :
    x ∈ (linkSymmetricBox d n τ).sites ↔
      -(n : ℤ) ≤ x τ ∧ x τ ≤ (n : ℤ) + 1 ∧
        ∀ i, i ≠ τ → -(n : ℤ) ≤ x i ∧ x i ≤ (n : ℤ) := by
  rw [Box.mem_sites]
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨hl τ, by simpa [linkSymmetricBox] using hu τ,
      fun i hi => ⟨hl i, by simpa [linkSymmetricBox, hi] using hu i⟩⟩
  · rintro ⟨hl, hu, hrest⟩
    constructor
    · intro i
      by_cases hi : i = τ
      · subst i
        exact hl
      · exact (hrest i hi).1
    · intro i
      by_cases hi : i = τ
      · subst i
        simpa [linkSymmetricBox] using hu
      · simpa [linkSymmetricBox, hi] using (hrest i hi).2

/-- Centered site boxes are invariant under site reflection at zero. -/
theorem siteReflection_mem_centeredBox_iff {d n : ℕ} (τ : Fin d)
    (x : Site d) :
    siteReflection τ 0 x ∈ (centeredBox d n).sites ↔
      x ∈ (centeredBox d n).sites := by
  simp only [mem_centeredBox_sites]
  constructor <;> intro h i
  · by_cases hi : i = τ
    · subst i
      have hi := h τ
      simp only [siteReflection_apply_eq] at hi
      omega
    · simpa [hi] using h i
  · by_cases hi : i = τ
    · subst i
      have hi := h τ
      simp only [siteReflection_apply_eq]
      omega
    · simpa [hi] using h i

/-- Link-symmetric site boxes are invariant under link reflection at `1/2`. -/
theorem linkReflection_mem_linkSymmetricBox_iff {d n : ℕ} (τ : Fin d)
    (x : Site d) :
    linkReflection τ 0 x ∈ (linkSymmetricBox d n τ).sites ↔
      x ∈ (linkSymmetricBox d n τ).sites := by
  simp only [mem_linkSymmetricBox_sites]
  constructor
  · rintro ⟨hl, hu, hrest⟩
    have hl' : -(n : ℤ) ≤ x τ := by
      simp only [linkReflection_apply_eq] at hu
      omega
    have hu' : x τ ≤ (n : ℤ) + 1 := by
      simp only [linkReflection_apply_eq] at hl
      omega
    exact ⟨hl', hu', fun i hi => by simpa [hi] using hrest i hi⟩
  · rintro ⟨hl, hu, hrest⟩
    have hl' : -(n : ℤ) ≤ linkReflection τ 0 x τ := by
      simp only [linkReflection_apply_eq]
      omega
    have hu' : linkReflection τ 0 x τ ≤ (n : ℤ) + 1 := by
      simp only [linkReflection_apply_eq]
      omega
    exact ⟨hl', hu', fun i hi => by simpa [hi] using hrest i hi⟩

/-- Every finite edge support is contained in a link-symmetric box. -/
theorem finiteSupport_subset_linkSymmetricBox {d : ℕ} (τ : Fin d)
    (S : Finset (PositiveEdge d)) :
    ∃ n, S ⊆ (linkSymmetricBox d n τ).positiveEdges := by
  obtain ⟨n, hn⟩ := finiteSupport_subset_centeredBox S
  refine ⟨n, fun e he => ?_⟩
  have he' := hn he
  rw [Box.mem_positiveEdges] at he' ⊢
  change e.source ∈ (centeredBox d n).sites ∧
    e.target ∈ (centeredBox d n).sites at he'
  change e.source ∈ (linkSymmetricBox d n τ).sites ∧
    e.target ∈ (linkSymmetricBox d n τ).sites
  simp only [mem_centeredBox_sites] at he'
  constructor
  · rw [mem_linkSymmetricBox_sites]
    exact ⟨(he'.1 τ).1, (he'.1 τ).2.trans (by omega),
      fun i _ => he'.1 i⟩
  · rw [mem_linkSymmetricBox_sites]
    exact ⟨(he'.2 τ).1, (he'.2 τ).2.trans (by omega),
      fun i _ => he'.2 i⟩

end

end YangMills.StrongCoupling
