/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.InfiniteReflection

/-!
# Reflection through diagonal lattice hyperplanes

For distinct coordinate directions `τ` and `σ`, the affine diagonal plane

`x τ - x σ = k`

is preserved by the lattice involution

`(x τ, x σ) ↦ (x σ + k, x τ - k)`.

Unlike a half-integer coordinate reflection, this map permutes positive
coordinate edges without reversing their stored orientation.  Consequently
there is no crossing-link gauge fix and the positive observable algebra is
the full local algebra supported in the corresponding closed half-lattice.
-/

namespace YangMills.Lattice.Cubic

/-- Reflection through the affine diagonal plane `x τ - x σ = k`. -/
def diagonalReflection {d : ℕ} (τ σ : Fin d) (k : ℤ) (x : Site d) : Site d :=
  fun i => if i = τ then x σ + k else if i = σ then x τ - k else x i

@[simp]
theorem diagonalReflection_apply_first {d : ℕ} (τ σ : Fin d)
    (k : ℤ) (x : Site d) :
    diagonalReflection τ σ k x τ = x σ + k := by
  simp [diagonalReflection]

@[simp]
theorem diagonalReflection_apply_second {d : ℕ} {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (x : Site d) :
    diagonalReflection τ σ k x σ = x τ - k := by
  simp [diagonalReflection, hτσ.symm]

@[simp]
theorem diagonalReflection_apply_other {d : ℕ} {τ σ i : Fin d}
    (hiτ : i ≠ τ) (hiσ : i ≠ σ) (k : ℤ) (x : Site d) :
    diagonalReflection τ σ k x i = x i := by
  simp [diagonalReflection, hiτ, hiσ]

@[simp]
theorem diagonalReflection_involutive {d : ℕ} {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (x : Site d) :
    diagonalReflection τ σ k (diagonalReflection τ σ k x) = x := by
  ext i
  by_cases hiτ : i = τ
  · subst i
    simp [hτσ]
  · by_cases hiσ : i = σ
    · subst i
      simp [hτσ]
    · simp [diagonalReflection, hiτ, hiσ]

/-- Diagonal reflection reverses the signed displacement from its affine
fixed plane. -/
theorem diagonalReflection_difference {d : ℕ} {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (x : Site d) :
    diagonalReflection τ σ k x τ - diagonalReflection τ σ k x σ =
      2 * k - (x τ - x σ) := by
  simp [hτσ]
  ring

/-- Diagonal reflection as an involutive equivalence of lattice sites. -/
def diagonalReflectionEquiv {d : ℕ} (τ σ : Fin d) (hτσ : τ ≠ σ) (k : ℤ) :
    Site d ≃ Site d where
  toFun := diagonalReflection τ σ k
  invFun := diagonalReflection τ σ k
  left_inv := diagonalReflection_involutive hτσ k
  right_inv := diagonalReflection_involutive hτσ k

/-- Translating by `-k` in the first coordinate conjugates the affine
diagonal reflection to reflection through `x τ = x σ`. -/
theorem diagonalReflection_translate_axis_neg {d : ℕ} {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (x : Site d) :
    diagonalReflection τ σ 0 (translate (axisTranslation τ (-k)) x) =
      translate (axisTranslation τ (-k)) (diagonalReflection τ σ k x) := by
  ext i
  by_cases hiτ : i = τ
  · subst i
    simp [translate, axisTranslation, hτσ.symm]
  · by_cases hiσ : i = σ
    · subst i
      simp [translate, hτσ, hτσ.symm]
      ring
    · simp [translate, diagonalReflection, hiτ, hiσ]

namespace SignedDirection

/-- A diagonal reflection swaps the two coordinate axes and preserves the
orientation relative to the resulting positive edge. -/
def diagonalReflect {d : ℕ} (τ σ : Fin d) (s : SignedDirection d) :
    SignedDirection d :=
  ⟨Equiv.swap τ σ s.axis, s.orientation⟩

@[simp]
theorem diagonalReflect_axis {d : ℕ} (τ σ : Fin d) (s : SignedDirection d) :
    (s.diagonalReflect τ σ).axis = Equiv.swap τ σ s.axis := rfl

@[simp]
theorem diagonalReflect_diagonalReflect {d : ℕ} (τ σ : Fin d)
    (s : SignedDirection d) :
    (s.diagonalReflect τ σ).diagonalReflect τ σ = s := by
  rcases s with ⟨i, o⟩
  simp [diagonalReflect]

@[simp]
theorem diagonalReflect_reverse {d : ℕ} (τ σ : Fin d)
    (s : SignedDirection d) :
    s.reverse.diagonalReflect τ σ = (s.diagonalReflect τ σ).reverse := by
  rfl

@[simp]
theorem delta_diagonalReflect {d : ℕ} (τ σ : Fin d)
    (s : SignedDirection d) (i : Fin d) :
    (s.diagonalReflect τ σ).delta i = s.delta (Equiv.swap τ σ i) := by
  rcases s with ⟨a, o⟩
  have heq : i = Equiv.swap τ σ a ↔ Equiv.swap τ σ i = a := by
    constructor
    · intro h
      simpa using congrArg (Equiv.swap τ σ) h
    · intro h
      exact (Equiv.swap τ σ).injective <| by simpa using h
  cases o <;> simp [diagonalReflect, delta, unitVector, heq]

end SignedDirection

/-- Diagonal reflection commutes with a signed step after swapping its axis. -/
@[simp]
theorem diagonalReflection_step {d : ℕ} {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (x : Site d) (s : SignedDirection d) :
    diagonalReflection τ σ k (step x s) =
      step (diagonalReflection τ σ k x) (s.diagonalReflect τ σ) := by
  ext i
  by_cases hiτ : i = τ
  · subst i
    simp [step, SignedDirection.delta_diagonalReflect]
    ring
  · by_cases hiσ : i = σ
    · subst i
      simp [step, hτσ, SignedDirection.delta_diagonalReflect]
      ring
    · simp [step, diagonalReflection, hiτ, hiσ,
        SignedDirection.delta_diagonalReflect, Equiv.swap_apply_def]

namespace SignedEdge

/-- Reflect a located signed edge through an affine diagonal plane. -/
def diagonalReflect {d : ℕ} (τ σ : Fin d) (k : ℤ) (e : SignedEdge d) :
    SignedEdge d :=
  ⟨diagonalReflection τ σ k e.source, e.direction.diagonalReflect τ σ⟩

@[simp]
theorem source_diagonalReflect {d : ℕ} (τ σ : Fin d) (k : ℤ)
    (e : SignedEdge d) :
    (e.diagonalReflect τ σ k).source = diagonalReflection τ σ k e.source := rfl

@[simp]
theorem target_diagonalReflect {d : ℕ} {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (e : SignedEdge d) :
    (e.diagonalReflect τ σ k).target = diagonalReflection τ σ k e.target := by
  exact (diagonalReflection_step hτσ k e.source e.direction).symm

@[simp]
theorem diagonalReflect_diagonalReflect {d : ℕ} {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (e : SignedEdge d) :
    (e.diagonalReflect τ σ k).diagonalReflect τ σ k = e := by
  rcases e with ⟨x, s⟩
  simp [diagonalReflect, diagonalReflection_involutive hτσ]

@[simp]
theorem diagonalReflect_reverse {d : ℕ} {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (e : SignedEdge d) :
    e.reverse.diagonalReflect τ σ k = (e.diagonalReflect τ σ k).reverse := by
  rcases e with ⟨x, s⟩
  change SignedEdge.mk (diagonalReflection τ σ k (step x s))
      (s.reverse.diagonalReflect τ σ) =
    SignedEdge.mk (step (diagonalReflection τ σ k x) (s.diagonalReflect τ σ))
      (s.diagonalReflect τ σ).reverse
  rw [diagonalReflection_step hτσ, SignedDirection.diagonalReflect_reverse]

end SignedEdge

namespace PositiveEdge

/-- Diagonal reflection permutes stored positive edges without inversion. -/
def diagonalReflect {d : ℕ} (τ σ : Fin d) (k : ℤ) (e : PositiveEdge d) :
    PositiveEdge d :=
  ⟨diagonalReflection τ σ k e.source, Equiv.swap τ σ e.direction⟩

@[simp]
theorem source_diagonalReflect {d : ℕ} (τ σ : Fin d) (k : ℤ)
    (e : PositiveEdge d) :
    (e.diagonalReflect τ σ k).source = diagonalReflection τ σ k e.source := rfl

@[simp]
theorem direction_diagonalReflect {d : ℕ} (τ σ : Fin d) (k : ℤ)
    (e : PositiveEdge d) :
    (e.diagonalReflect τ σ k).direction = Equiv.swap τ σ e.direction := rfl

@[simp]
theorem target_diagonalReflect {d : ℕ} {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (e : PositiveEdge d) :
    (e.diagonalReflect τ σ k).target = diagonalReflection τ σ k e.target := by
  change step (diagonalReflection τ σ k e.source)
      (.forward (Equiv.swap τ σ e.direction)) = _
  simpa [SignedDirection.diagonalReflect] using
    (diagonalReflection_step hτσ k e.source (.forward e.direction)).symm

@[simp]
theorem diagonalReflect_diagonalReflect {d : ℕ} {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (e : PositiveEdge d) :
    (e.diagonalReflect τ σ k).diagonalReflect τ σ k = e := by
  rcases e with ⟨x, i⟩
  simp [diagonalReflect, diagonalReflection_involutive hτσ]

/-- Diagonal reflection as an involutive equivalence of stored edges. -/
def diagonalReflectionEquiv {d : ℕ} (τ σ : Fin d) (hτσ : τ ≠ σ) (k : ℤ) :
    PositiveEdge d ≃ PositiveEdge d where
  toFun := diagonalReflect τ σ k
  invFun := diagonalReflect τ σ k
  left_inv := diagonalReflect_diagonalReflect hτσ k
  right_inv := diagonalReflect_diagonalReflect hτσ k

/-- Edge form of conjugating an affine diagonal reflection to the plane
through the origin. -/
theorem translate_diagonalReflect_axis_neg {d : ℕ} {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (e : PositiveEdge d) :
    (e.translate (axisTranslation τ (-k))).diagonalReflect τ σ 0 =
      (e.diagonalReflect τ σ k).translate (axisTranslation τ (-k)) := by
  rcases e with ⟨x, i⟩
  simp only [diagonalReflect, PositiveEdge.translate]
  congr 1
  exact diagonalReflection_translate_axis_neg hτσ k x

end PositiveEdge

namespace Plaquette

/-- Reflect a canonical plaquette by swapping the two diagonal axes. -/
def diagonalReflect {d : ℕ} (τ σ : Fin d) (k : ℤ) (p : Plaquette d) :
    Plaquette d where
  base := diagonalReflection τ σ k p.base
  first := Equiv.swap τ σ p.first
  second := Equiv.swap τ σ p.second
  distinct := fun h => p.distinct ((Equiv.swap τ σ).injective h)

@[simp]
theorem diagonalReflect_diagonalReflect {d : ℕ} {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (p : Plaquette d) :
    (p.diagonalReflect τ σ k).diagonalReflect τ σ k = p := by
  rcases p with ⟨x, i, j, hij⟩
  simp [diagonalReflect, diagonalReflection_involutive hτσ]

/-- Diagonal reflection as an involutive equivalence of plaquettes. -/
def diagonalReflectionEquiv {d : ℕ} (τ σ : Fin d) (hτσ : τ ≠ σ) (k : ℤ) :
    Plaquette d ≃ Plaquette d where
  toFun := diagonalReflect τ σ k
  invFun := diagonalReflect τ σ k
  left_inv := diagonalReflect_diagonalReflect hτσ k
  right_inv := diagonalReflect_diagonalReflect hτσ k

end Plaquette

end YangMills.Lattice.Cubic

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Diagonal reflection of a stored-edge configuration.  No coordinate is
inverted: the two diagonal axes are exchanged as positive directions. -/
def diagonalReflectConfiguration (τ σ : Fin d) (k : ℤ)
    (A : Configuration d G) : Configuration d G :=
  fun e => A (e.diagonalReflect τ σ k)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Explicit stored-edge word for a canonical plaquette holonomy. -/
theorem holonomy_plaquette_boundary_explicit
    (A : Configuration d G) (p : Plaquette d) :
    holonomy A p.boundary =
      A ⟨p.base, p.first⟩ *
        A ⟨step p.base (.forward p.first), p.second⟩ *
        (A ⟨step p.base (.forward p.second), p.first⟩)⁻¹ *
        (A ⟨p.base, p.second⟩)⁻¹ := by
  have h₃ : p.base + unitVector p.first + unitVector p.second +
      -unitVector p.first = p.base + unitVector p.second := by abel
  simp [Plaquette.boundary, Path.rectangleBoundary, Path.rectangleRaw,
    Path.straight, Path.advance, SignedDirection.forward,
    SignedDirection.backward, SignedDirection.delta, signedEdgeValue, edgeFrom,
    SignedEdge.toArrow, SignedEdge.target, h₃, step]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Plaquette holonomy is covariant under diagonal reflection.  Swapping the
two diagonal axes in the plaquette label accounts for the reflected boundary
word. -/
theorem holonomy_diagonalReflectConfiguration {τ σ : Fin d}
    (hτσ : τ ≠ σ) (k : ℤ) (A : Configuration d G) (p : Plaquette d) :
    holonomy (diagonalReflectConfiguration τ σ k A) p.boundary =
      holonomy A (p.diagonalReflect τ σ k).boundary := by
  rw [holonomy_plaquette_boundary_explicit,
    holonomy_plaquette_boundary_explicit]
  simp only [diagonalReflectConfiguration, Plaquette.diagonalReflect,
    PositiveEdge.diagonalReflect]
  rw [diagonalReflection_step hτσ, diagonalReflection_step hτσ]
  rfl

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem diagonalReflectConfiguration_diagonalReflectConfiguration
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) (A : Configuration d G) :
    diagonalReflectConfiguration τ σ k
      (diagonalReflectConfiguration τ σ k A) = A := by
  funext e
  simp [diagonalReflectConfiguration, hτσ]

omit [Group G] [IsTopologicalGroup G] in
/-- Diagonal reflection is continuous in the product topology. -/
theorem continuous_diagonalReflectConfiguration (τ σ : Fin d) (k : ℤ) :
    Continuous (diagonalReflectConfiguration (G := G) τ σ k) := by
  exact continuous_pi fun e => continuous_apply (e.diagonalReflect τ σ k)

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Configuration form of conjugating the affine diagonal plane to the
origin plane by an axial translation. -/
theorem translateConfiguration_diagonalReflect_axis_neg
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) (A : Configuration d G) :
    LocalObservable.translateConfiguration (axisTranslation τ (-k))
        (diagonalReflectConfiguration τ σ 0 A) =
      diagonalReflectConfiguration τ σ k
        (LocalObservable.translateConfiguration (axisTranslation τ (-k)) A) := by
  funext e
  unfold LocalObservable.translateConfiguration diagonalReflectConfiguration
  rw [PositiveEdge.translate_diagonalReflect_axis_neg hτσ]

namespace LocalObservable

/-- Anti-linear reflection of a local observable through
`x τ - x σ = k`. -/
def diagonalTheta (τ σ : Fin d) (k : ℤ) (F : LocalObservable d G) :
    LocalObservable d G where
  toContinuousMap :=
    { toFun := fun A => star (F (diagonalReflectConfiguration τ σ k A))
      continuous_toFun := Complex.continuous_conj.comp
        (F.toContinuousMap.continuous.comp
          (continuous_diagonalReflectConfiguration τ σ k)) }
  support := F.support.image (PositiveEdge.diagonalReflect τ σ k)
  dependsOn_support := by
    intro A B hAB
    apply congrArg star
    apply F.dependsOn_support
    intro e he
    exact hAB (e.diagonalReflect τ σ k)
      (Finset.mem_image.mpr ⟨e, he, rfl⟩)

omit [Group G] [IsTopologicalGroup G] in
@[simp]
theorem diagonalTheta_apply (τ σ : Fin d) (k : ℤ)
    (F : LocalObservable d G) (A : Configuration d G) :
    F.diagonalTheta τ σ k A =
      star (F (diagonalReflectConfiguration τ σ k A)) := rfl

omit [Group G] [IsTopologicalGroup G] in
@[simp]
theorem diagonalTheta_diagonalTheta_apply {τ σ : Fin d} (hτσ : τ ≠ σ)
    (k : ℤ) (F : LocalObservable d G) (A : Configuration d G) :
    (F.diagonalTheta τ σ k).diagonalTheta τ σ k A = F A := by
  simp [diagonalTheta, hτσ]

/-- The local integrand in a diagonal-reflection pairing. -/
def diagonalReflectionProduct (τ σ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) : LocalObservable d G :=
  (F.diagonalTheta τ σ k).mul H

omit [Group G] [IsTopologicalGroup G] in
@[simp]
theorem diagonalReflectionProduct_apply (τ σ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) (A : Configuration d G) :
    F.diagonalReflectionProduct τ σ k H A =
      star (F (diagonalReflectConfiguration τ σ k A)) * H A := rfl

/-- A local observable lies in the positive algebra of
`x τ - x σ = k` when every recorded edge, including both endpoints, lies in
the closed positive half-lattice. -/
def SupportedInDiagonalPositiveHalf (τ σ : Fin d) (k : ℤ)
    (F : LocalObservable d G) : Prop :=
  ∀ e ∈ F.support,
    k ≤ e.source τ - e.source σ ∧ k ≤ e.target τ - e.target σ

end LocalObservable

namespace FiniteSpecification

/-- A finite specification is geometrically symmetric about an affine
diagonal plane when its dynamic edges and active plaquettes are preserved by
the reflection and its exterior field is reflected.  The last condition is
needed because a finite specification freezes every nondynamic edge. -/
def DiagonalSymmetric (Λ : FiniteSpecification d G)
    (τ σ : Fin d) (k : ℤ) : Prop :=
  τ ≠ σ ∧
    (∀ e, e ∈ Λ.dynamicEdges ↔ e.diagonalReflect τ σ k ∈ Λ.dynamicEdges) ∧
    (∀ p, p ∈ Λ.activePlaquettes ↔
      p.diagonalReflect τ σ k ∈ Λ.activePlaquettes) ∧
    diagonalReflectConfiguration τ σ k Λ.exterior = Λ.exterior

end FiniteSpecification

end

end YangMills.Gauge
