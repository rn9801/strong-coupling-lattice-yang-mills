/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.FiniteVolume

/-!
# Reflection through an integer lattice hyperplane

For a coordinate `τ` and an integer `k`, `siteReflection τ k` reflects sites
through the hyperplane `x τ = k`.  The reflection is defined first on signed
edges.  Its action on stored positive-edge variables consequently includes
group inversion on edges perpendicular to the plane.

These conventions are independent of gauge transformations.  In particular,
the reflected observable algebra developed from them is the full local algebra
on the positive half-lattice, not merely its gauge-invariant subalgebra.
-/

namespace YangMills.Lattice.Cubic

/-- Reflection of sites through the integer hyperplane `x τ = k`. -/
def siteReflection {d : ℕ} (τ : Fin d) (k : ℤ) (x : Site d) : Site d :=
  fun i => if i = τ then 2 * k - x i else x i

@[simp]
theorem siteReflection_apply_eq {d : ℕ} (τ : Fin d) (k : ℤ) (x : Site d) :
    siteReflection τ k x τ = 2 * k - x τ := by
  simp [siteReflection]

@[simp]
theorem siteReflection_apply_ne {d : ℕ} {τ i : Fin d} (h : i ≠ τ)
    (k : ℤ) (x : Site d) :
    siteReflection τ k x i = x i := by
  simp [siteReflection, h]

@[simp]
theorem siteReflection_involutive {d : ℕ} (τ : Fin d) (k : ℤ) (x : Site d) :
    siteReflection τ k (siteReflection τ k x) = x := by
  ext i
  by_cases hi : i = τ
  · subst i
    simp
  · simp [hi]

/-- Site reflection as an involutive equivalence. -/
def siteReflectionEquiv {d : ℕ} (τ : Fin d) (k : ℤ) : Site d ≃ Site d where
  toFun := siteReflection τ k
  invFun := siteReflection τ k
  left_inv := siteReflection_involutive τ k
  right_inv := siteReflection_involutive τ k

namespace SignedDirection

/-- Reflection reverses precisely the direction perpendicular to the plane. -/
def siteReflect {d : ℕ} (τ : Fin d) (s : SignedDirection d) : SignedDirection d :=
  ⟨s.axis, if s.axis = τ then s.orientation.reverse else s.orientation⟩

@[simp]
theorem siteReflect_axis {d : ℕ} (τ : Fin d) (s : SignedDirection d) :
    (s.siteReflect τ).axis = s.axis := by
  rfl

@[simp]
theorem siteReflect_siteReflect {d : ℕ} (τ : Fin d) (s : SignedDirection d) :
    (s.siteReflect τ).siteReflect τ = s := by
  rcases s with ⟨axis, orientation⟩
  by_cases h : axis = τ
  · cases orientation <;> simp [siteReflect, h]
  · simp [siteReflect, h]

@[simp]
theorem siteReflect_reverse {d : ℕ} (τ : Fin d) (s : SignedDirection d) :
    s.reverse.siteReflect τ = (s.siteReflect τ).reverse := by
  rcases s with ⟨axis, orientation⟩
  by_cases h : axis = τ <;> cases orientation <;> simp [siteReflect, h]

end SignedDirection

/-- Site reflection commutes with one signed step after reflecting its direction. -/
@[simp]
theorem siteReflection_step {d : ℕ} (τ : Fin d) (k : ℤ)
    (x : Site d) (s : SignedDirection d) :
    siteReflection τ k (step x s) =
      step (siteReflection τ k x) (s.siteReflect τ) := by
  ext i
  by_cases hi : i = τ
  · subst i
    cases s with
    | mk axis orientation =>
        by_cases ha : axis = τ
        · subst axis
          cases orientation <;>
            simp [step, SignedDirection.siteReflect, SignedDirection.delta,
              unitVector] <;> abel
        · cases orientation <;>
            simp [step, SignedDirection.siteReflect, SignedDirection.delta,
              unitVector, ha, Ne.symm ha] <;> abel
  · cases s with
    | mk axis orientation =>
        by_cases ha : axis = τ
        · subst axis
          cases orientation <;>
            simp [step, SignedDirection.siteReflect, SignedDirection.delta,
              unitVector, hi]
        · cases orientation <;>
            by_cases hia : i = axis <;>
              simp [step, SignedDirection.siteReflect, SignedDirection.delta,
                unitVector, hi, ha, hia]

namespace SignedEdge

/-- Reflect a located signed edge, including its traversal orientation. -/
def siteReflect {d : ℕ} (τ : Fin d) (k : ℤ) (e : SignedEdge d) : SignedEdge d :=
  ⟨siteReflection τ k e.source, e.direction.siteReflect τ⟩

@[simp]
theorem source_siteReflect {d : ℕ} (τ : Fin d) (k : ℤ) (e : SignedEdge d) :
    (e.siteReflect τ k).source = siteReflection τ k e.source :=
  rfl

@[simp]
theorem target_siteReflect {d : ℕ} (τ : Fin d) (k : ℤ) (e : SignedEdge d) :
    (e.siteReflect τ k).target = siteReflection τ k e.target := by
  exact (siteReflection_step τ k e.source e.direction).symm

@[simp]
theorem siteReflect_siteReflect {d : ℕ} (τ : Fin d) (k : ℤ)
    (e : SignedEdge d) :
    (e.siteReflect τ k).siteReflect τ k = e := by
  cases e
  simp [siteReflect]

@[simp]
theorem siteReflect_reverse {d : ℕ} (τ : Fin d) (k : ℤ)
    (e : SignedEdge d) :
    e.reverse.siteReflect τ k = (e.siteReflect τ k).reverse := by
  rcases e with ⟨source, direction⟩
  change SignedEdge.mk (siteReflection τ k (step source direction))
      (direction.reverse.siteReflect τ) =
    SignedEdge.mk (step (siteReflection τ k source) (direction.siteReflect τ))
      (direction.siteReflect τ).reverse
  congr 1
  · exact siteReflection_step τ k source direction
  · exact SignedDirection.siteReflect_reverse τ direction

end SignedEdge

namespace PositiveEdge

/-- The stored positive edge underlying the reflection of a positive edge. -/
def siteReflect {d : ℕ} (τ : Fin d) (k : ℤ) (e : PositiveEdge d) :
    PositiveEdge d :=
  if e.direction = τ then ⟨siteReflection τ k e.target, e.direction⟩
  else ⟨siteReflection τ k e.source, e.direction⟩

@[simp]
theorem direction_siteReflect {d : ℕ} (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) :
    (e.siteReflect τ k).direction = e.direction := by
  by_cases h : e.direction = τ <;> simp [siteReflect, h]

@[simp]
theorem siteReflect_siteReflect {d : ℕ} (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) :
    (e.siteReflect τ k).siteReflect τ k = e := by
  rcases e with ⟨x, i⟩
  by_cases h : i = τ
  · subst i
    simp only [siteReflect, if_pos]
    congr 1
    calc
      siteReflection τ k
          (PositiveEdge.target ⟨siteReflection τ k (PositiveEdge.target ⟨x, τ⟩), τ⟩) =
          siteReflection τ k (siteReflection τ k x) := by
            congr 1
            have hs := siteReflection_step τ k x (.forward τ)
            change step (siteReflection τ k (step x (.forward τ))) (.forward τ) =
              siteReflection τ k x
            rw [hs]
            rw [show SignedDirection.siteReflect τ (.forward τ) = .backward τ by
              simp only [SignedDirection.siteReflect, SignedDirection.forward]
              simp only [if_true]
              rfl]
            exact step_reverse (siteReflection τ k x) (.backward τ)
      _ = x := siteReflection_involutive τ k x
  · congr 1
    simp [siteReflect, h]

/-- Site reflection as an involutive equivalence of stored positive edges. -/
def siteReflectionEquiv {d : ℕ} (τ : Fin d) (k : ℤ) :
    PositiveEdge d ≃ PositiveEdge d where
  toFun := siteReflect τ k
  invFun := siteReflect τ k
  left_inv := siteReflect_siteReflect τ k
  right_inv := siteReflect_siteReflect τ k

end PositiveEdge

/-- Site reflection as a morphism of the cubic-site quiver. -/
def siteReflectionPrefunctor {d : ℕ} (τ : Fin d) (k : ℤ) : Site d ⥤q Site d where
  obj := siteReflection τ k
  map := fun e =>
    ⟨e.1.siteReflect τ k,
      by simpa using congrArg (siteReflection τ k) e.2.1,
      by simpa using congrArg (siteReflection τ k) e.2.2⟩

namespace Path

/-- Reflect every traversed signed edge of a path. -/
def siteReflect {d : ℕ} {x y : Site d} (τ : Fin d) (k : ℤ) (p : Path x y) :
    Path (siteReflection τ k x) (siteReflection τ k y) :=
  (siteReflectionPrefunctor τ k).mapPath p

end Path

namespace Plaquette

/-- Reflect a canonical plaquette through a site hyperplane.  When the
plaquette is perpendicular to the plane, its reflected minimal corner is one
step below the reflected base. -/
def siteReflect {d : ℕ} (τ : Fin d) (k : ℤ) (p : Plaquette d) : Plaquette d :=
  if p.first = τ ∨ p.second = τ then
    ⟨step (siteReflection τ k p.base) (.backward τ),
      p.first, p.second, p.distinct⟩
  else
    ⟨siteReflection τ k p.base, p.first, p.second, p.distinct⟩

@[simp]
theorem first_siteReflect {d : ℕ} (τ : Fin d) (k : ℤ) (p : Plaquette d) :
    (p.siteReflect τ k).first = p.first := by
  by_cases h : p.first = τ ∨ p.second = τ <;> simp [siteReflect, h]

@[simp]
theorem second_siteReflect {d : ℕ} (τ : Fin d) (k : ℤ) (p : Plaquette d) :
    (p.siteReflect τ k).second = p.second := by
  by_cases h : p.first = τ ∨ p.second = τ <;> simp [siteReflect, h]

@[simp]
theorem siteReflect_siteReflect {d : ℕ} (τ : Fin d) (k : ℤ)
    (p : Plaquette d) :
    (p.siteReflect τ k).siteReflect τ k = p := by
  rcases p with ⟨x, i, j, hij⟩
  by_cases h : i = τ ∨ j = τ
  · simp only [siteReflect, h, if_pos]
    congr 1
    calc
      step (siteReflection τ k (step (siteReflection τ k x) (.backward τ)))
          (.backward τ) =
          step (step x (.forward τ)) (.backward τ) := by
            congr 1
            rw [siteReflection_step]
            simp only [siteReflection_involutive]
            congr 1
            simp only [SignedDirection.siteReflect, SignedDirection.backward, if_true]
            rfl
      _ = x := step_reverse x (.forward τ)
  · simp [siteReflect, h]

/-- Reflection as an involutive equivalence of canonical plaquettes. -/
def siteReflectionEquiv {d : ℕ} (τ : Fin d) (k : ℤ) :
    Plaquette d ≃ Plaquette d where
  toFun := siteReflect τ k
  invFun := siteReflect τ k
  left_inv := siteReflect_siteReflect τ k
  right_inv := siteReflect_siteReflect τ k

end Plaquette

end YangMills.Lattice.Cubic

namespace YangMills.Gauge

open Lattice.Cubic

variable {d : ℕ} {G : Type*} [Group G]

/-- Reflect a configuration.  Perpendicular positive edges are evaluated with
the reversed orientation and hence with group inversion. -/
def siteReflectConfiguration (τ : Fin d) (k : ℤ) (A : Configuration d G) :
    Configuration d G :=
  fun e => if e.direction = τ then (A (e.siteReflect τ k))⁻¹
    else A (e.siteReflect τ k)

/-- Signed-edge evaluation is covariant under site reflection. -/
@[simp]
theorem signedEdgeValue_siteReflectConfiguration
    (τ : Fin d) (k : ℤ) (A : Configuration d G) (e : SignedEdge d) :
    signedEdgeValue (siteReflectConfiguration τ k A) e =
      signedEdgeValue A (e.siteReflect τ k) := by
  rcases e with ⟨x, ⟨i, o⟩⟩
  cases o with
  | forward =>
      by_cases h : i = τ
      · subst i
        change (if τ = τ then (A ((PositiveEdge.mk x τ).siteReflect τ k))⁻¹
          else A ((PositiveEdge.mk x τ).siteReflect τ k)) = _
        rw [if_pos rfl]
        unfold PositiveEdge.siteReflect SignedEdge.siteReflect SignedDirection.siteReflect
        simp only [if_pos]
        change (A ⟨siteReflection τ k (step x (.forward τ)), τ⟩)⁻¹ =
          signedEdgeValue A ⟨siteReflection τ k x, .backward τ⟩
        change (A ⟨siteReflection τ k (step x (.forward τ)), τ⟩)⁻¹ =
          (A ⟨step (siteReflection τ k x) (.backward τ), τ⟩)⁻¹
        congr 2
        rw [siteReflection_step]
        rw [show SignedDirection.siteReflect τ (.forward τ) = .backward τ by
          simp only [SignedDirection.siteReflect, SignedDirection.forward]
          simp only [if_true]
          rfl]
      · simp [signedEdgeValue, siteReflectConfiguration,
          PositiveEdge.siteReflect, SignedEdge.siteReflect,
          SignedDirection.siteReflect, SignedEdge.target, h]
  | backward =>
      by_cases h : i = τ
      · subst i
        change (if τ = τ then
            (A ((PositiveEdge.mk (step x (.backward τ)) τ).siteReflect τ k))⁻¹
          else A ((PositiveEdge.mk (step x (.backward τ)) τ).siteReflect τ k))⁻¹ = _
        rw [if_pos rfl]
        rw [inv_inv]
        unfold PositiveEdge.siteReflect SignedEdge.siteReflect SignedDirection.siteReflect
        simp only [if_pos]
        change A ⟨siteReflection τ k
            (step (step x (.backward τ)) (.forward τ)), τ⟩ =
          A ⟨siteReflection τ k x, τ⟩
        congr 2
        exact congrArg (siteReflection τ k) (step_reverse x (.backward τ))
      · change (if i = τ then
            (A ((PositiveEdge.mk (step x (.backward i)) i).siteReflect τ k))⁻¹
          else A ((PositiveEdge.mk (step x (.backward i)) i).siteReflect τ k))⁻¹ = _
        rw [if_neg h]
        unfold PositiveEdge.siteReflect
        rw [if_neg h]
        change (A ⟨siteReflection τ k (step x (.backward i)), i⟩)⁻¹ =
          signedEdgeValue A ((SignedEdge.mk x (.backward i)).siteReflect τ k)
        rw [show ((SignedEdge.mk x (.backward i)).siteReflect τ k) =
            SignedEdge.mk (siteReflection τ k x) (.backward i) by
          unfold SignedEdge.siteReflect SignedDirection.siteReflect
          simp only [SignedDirection.backward, h, if_false]]
        rw [signedEdgeValue_backward]
        change (A ⟨siteReflection τ k (step x (.backward i)), i⟩)⁻¹ =
          (A ⟨step (siteReflection τ k x) (.backward i), i⟩)⁻¹
        congr 2
        rw [siteReflection_step]
        congr 1
        simp only [SignedDirection.siteReflect, SignedDirection.backward, h, if_false]

@[simp]
theorem siteReflectConfiguration_siteReflectConfiguration
    (τ : Fin d) (k : ℤ) (A : Configuration d G) :
    siteReflectConfiguration τ k (siteReflectConfiguration τ k A) = A := by
  funext e
  by_cases h : e.direction = τ
  · simp [siteReflectConfiguration, h]
  · simp [siteReflectConfiguration, h]

/-- Holonomy of a reflected configuration is holonomy along the reflected path. -/
@[simp]
theorem holonomy_siteReflectConfiguration
    (τ : Fin d) (k : ℤ) (A : Configuration d G)
    {x y : Site d} (p : Lattice.Cubic.Path x y) :
    holonomy (siteReflectConfiguration τ k A) p =
      holonomy A (p.siteReflect τ k) := by
  induction p with
  | nil =>
      change (1 : G) = 1
      rfl
  | cons p e ih =>
      rw [holonomy_cons, ih, signedEdgeValue_siteReflectConfiguration]
      change holonomy A (Path.siteReflect τ k p) *
          signedEdgeValue A (e.1.siteReflect τ k) =
        holonomy A ((Path.siteReflect τ k p).cons
          ((siteReflectionPrefunctor τ k).map e))
      rfl

/-- Explicit four-link formula for canonical plaquette holonomy. -/
theorem holonomy_plaquette_boundary (A : Configuration d G) (p : Plaquette d) :
    holonomy A p.boundary =
      A ⟨p.base, p.first⟩ *
      A ⟨step p.base (.forward p.first), p.second⟩ *
      (A ⟨step p.base (.forward p.second), p.first⟩)⁻¹ *
      (A ⟨p.base, p.second⟩)⁻¹ := by
  rcases p with ⟨x, i, j, hij⟩
  simp [Plaquette.boundary, Path.rectangleBoundary, Path.rectangleRaw,
    Path.straight, Path.advance, signedEdgeValue, edgeFrom,
    SignedEdge.toArrow, SignedEdge.target, SignedDirection.forward,
    SignedDirection.backward]
  congr 4
  · congr 1
    ext a
    simp [step, SignedDirection.delta, unitVector]
    abel
  · congr 1
    ext a
    simp [step, SignedDirection.delta, unitVector]
    abel

/-- A reflection-invariant real plaquette potential assigns the same value to
a plaquette before and after reflecting both the field and the plaquette. -/
@[simp]
theorem RealPlaquettePotential.apply_holonomy_siteReflectConfiguration
    [TopologicalSpace G] (Φ : RealPlaquettePotential G)
    (τ : Fin d) (k : ℤ) (A : Configuration d G) (p : Plaquette d) :
    Φ (holonomy (siteReflectConfiguration τ k A) p.boundary) =
      Φ (holonomy A (p.siteReflect τ k).boundary) := by
  rcases p with ⟨x, i, j, hij⟩
  by_cases hi : i = τ
  · subst i
    have hi : τ = τ := rfl
    have hj : j ≠ τ := fun h ↦ hij h.symm
    rw [holonomy_plaquette_boundary, holonomy_plaquette_boundary]
    simp only [siteReflectConfiguration, Plaquette.siteReflect, hi, true_or,
      if_pos, Plaquette.base, Plaquette.first, Plaquette.second]
    simp only [PositiveEdge.siteReflect, hj, if_pos, if_neg]
    simp only [if_false]
    rw [show (PositiveEdge.mk x τ).target = step x (.forward τ) by rfl]
    rw [show (PositiveEdge.mk (step x (.forward j)) τ).target =
        step (step x (.forward j)) (.forward τ) by rfl]
    rw [siteReflection_step τ k x (.forward τ)]
    rw [show SignedDirection.siteReflect τ (.forward τ) = .backward τ by
      simp only [SignedDirection.siteReflect, SignedDirection.forward, if_true]
      rfl]
    have hcomm : step (step x (.forward j)) (.forward τ) =
        step (step x (.forward τ)) (.forward j) := by
      ext a
      simp [step, SignedDirection.delta, unitVector]
      abel
    rw [show siteReflection τ k
          (step (step x (.forward j)) (.forward τ)) =
        step (siteReflection τ k (step x (.forward τ))) (.forward j) by
      rw [hcomm, siteReflection_step]
      rw [show SignedDirection.siteReflect τ (.forward j) = .forward j by
        simp only [SignedDirection.siteReflect, SignedDirection.forward, hj, if_false]]]
    rw [siteReflection_step τ k x (.forward τ)]
    rw [show SignedDirection.siteReflect τ (.forward τ) = .backward τ by
      simp only [SignedDirection.siteReflect, SignedDirection.forward, if_true]
      rfl]
    simp only [inv_inv]
    let a : G := A ⟨step (siteReflection τ k x) (.backward τ), τ⟩
    let b : G := A ⟨step (siteReflection τ k x) (.backward τ), j⟩
    let c : G := A ⟨step (step (siteReflection τ k x) (.backward τ)) (.forward j), τ⟩
    let q : G := A ⟨siteReflection τ k x, j⟩
    have harg :
        (A ⟨step (siteReflection τ k x) (.backward τ), τ⟩)⁻¹ *
          A ⟨step (siteReflection τ k x) (.backward τ), j⟩ *
          A ⟨step (step (siteReflection τ k x) (.backward τ)) (.forward j), τ⟩ *
          (A ⟨siteReflection τ k x, j⟩)⁻¹ =
        a⁻¹ *
          ((a * q * c⁻¹ * b⁻¹)⁻¹) * a := by
      dsimp [a, b, c, q]
      group
    have hstepτ : step (step (siteReflection τ k x) (.backward τ)) (.forward τ) =
        siteReflection τ k x := step_reverse (siteReflection τ k x) (.backward τ)
    rw [hstepτ]
    rw [harg]
    rw [show a⁻¹ * (a * q * c⁻¹ * b⁻¹)⁻¹ * a =
        a⁻¹ * (a * q * c⁻¹ * b⁻¹)⁻¹ * (a⁻¹)⁻¹ by rw [inv_inv]]
    rw [Φ.conj_invariant, Φ.inv_invariant]
  · by_cases hj : j = τ
    · subst j
      rw [holonomy_plaquette_boundary, holonomy_plaquette_boundary]
      simp only [siteReflectConfiguration, Plaquette.siteReflect, hi, or_true,
        if_pos, Plaquette.base, Plaquette.first, Plaquette.second]
      simp only [PositiveEdge.siteReflect, hi, if_neg, if_pos]
      simp only [if_false]
      rw [show (PositiveEdge.mk (step x (.forward i)) τ).target =
          step (step x (.forward i)) (.forward τ) by rfl]
      rw [show (PositiveEdge.mk x τ).target = step x (.forward τ) by rfl]
      rw [show step (step x (.forward i)) (.forward τ) =
          step (step x (.forward τ)) (.forward i) by
        ext a
        simp [step, SignedDirection.delta, unitVector]
        abel]
      rw [show siteReflection τ k
            (step (step x (.forward τ)) (.forward i)) =
          step (siteReflection τ k (step x (.forward τ))) (.forward i) by
        rw [siteReflection_step]
        rw [show SignedDirection.siteReflect τ (.forward i) = .forward i by
          simp only [SignedDirection.siteReflect, SignedDirection.forward, hi, if_false]]]
      rw [siteReflection_step τ k x (.forward τ)]
      rw [show SignedDirection.siteReflect τ (.forward τ) = .backward τ by
        simp only [SignedDirection.siteReflect, SignedDirection.forward, if_true]
        rfl]
      simp only [inv_inv]
      let a : G := A ⟨step (siteReflection τ k x) (.backward τ), τ⟩
      let b : G := A ⟨siteReflection τ k x, i⟩
      let c : G := A ⟨step (step (siteReflection τ k x) (.backward τ)) (.forward i), τ⟩
      let q : G := A ⟨step (siteReflection τ k x) (.backward τ), i⟩
      have harg :
          b * c⁻¹ * q⁻¹ * a =
            a⁻¹ * ((q * c * b⁻¹ * a⁻¹)⁻¹) * a := by
        dsimp [a, b, c, q]
        group
      have hstepτ : step (step (siteReflection τ k x) (.backward τ)) (.forward τ) =
          siteReflection τ k x := step_reverse (siteReflection τ k x) (.backward τ)
      rw [hstepτ]
      rw [harg]
      rw [show a⁻¹ * (q * c * b⁻¹ * a⁻¹)⁻¹ * a =
          a⁻¹ * (q * c * b⁻¹ * a⁻¹)⁻¹ * (a⁻¹)⁻¹ by rw [inv_inv]]
      rw [Φ.conj_invariant, Φ.inv_invariant]
    · rw [holonomy_plaquette_boundary, holonomy_plaquette_boundary]
      simp only [siteReflectConfiguration, Plaquette.siteReflect, hi, hj,
        or_false, if_neg, Plaquette.base, Plaquette.first, Plaquette.second]
      simp only [PositiveEdge.siteReflect, hi, hj, if_neg]
      simp only [if_false]
      rw [siteReflection_step τ k x (.forward i)]
      rw [show SignedDirection.siteReflect τ (.forward i) = .forward i by
        simp only [SignedDirection.siteReflect, SignedDirection.forward, hi, if_false]]
      rw [siteReflection_step τ k x (.forward j)]
      rw [show SignedDirection.siteReflect τ (.forward j) = .forward j by
        simp only [SignedDirection.siteReflect, SignedDirection.forward, hj, if_false]]

end YangMills.Gauge
