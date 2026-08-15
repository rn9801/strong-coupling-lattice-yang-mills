/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.Observable
import YangMills.Gauge.SiteReflection

/-!
# Reflections of infinite-lattice local observables

This file supplies the geometric observable layer needed to pass finite-volume
reflection positivity to the cluster-constructed infinite-volume state.  Site
reflection is through `x τ = k`; link reflection is through
`x τ = k + 1/2`.  Both act on stored positive edges with inversion in the
perpendicular direction, and `siteTheta`/`linkTheta` additionally conjugate
the observable value.

The support predicates include the plane variables in the positive algebra.
For a site plane this is `k ≤ e.source τ`.  For a link plane it is
`k < e.target τ`, which includes a perpendicular edge crossing the plane but
excludes tangential edges based on its negative side.
-/

namespace YangMills.Lattice.Cubic

/-- Translation by `a` lattice spacings along the coordinate `τ`. -/
def axisTranslation {d : ℕ} (τ : Fin d) (a : ℤ) : Site d :=
  fun i => if i = τ then a else 0

@[simp]
theorem axisTranslation_apply_eq {d : ℕ} (τ : Fin d) (a : ℤ) :
    axisTranslation τ a τ = a := by
  simp [axisTranslation]

@[simp]
theorem axisTranslation_apply_ne {d : ℕ} {τ i : Fin d} (h : i ≠ τ)
    (a : ℤ) : axisTranslation τ a i = 0 := by
  simp [axisTranslation, h]

/-- Reflection of sites through the half-integer plane `x τ = k + 1/2`.
It is the integer reflection through `k`, followed by one positive step. -/
def linkReflection {d : ℕ} (τ : Fin d) (k : ℤ) (x : Site d) : Site d :=
  translate (unitVector τ) (siteReflection τ k x)

@[simp]
theorem linkReflection_apply_eq {d : ℕ} (τ : Fin d) (k : ℤ) (x : Site d) :
    linkReflection τ k x τ = 2 * k + 1 - x τ := by
  simp [linkReflection, translate, unitVector]
  ring

@[simp]
theorem linkReflection_apply_ne {d : ℕ} {τ i : Fin d} (h : i ≠ τ)
    (k : ℤ) (x : Site d) :
    linkReflection τ k x i = x i := by
  simp [linkReflection, translate, unitVector, h]

@[simp]
theorem linkReflection_involutive {d : ℕ} (τ : Fin d) (k : ℤ) (x : Site d) :
    linkReflection τ k (linkReflection τ k x) = x := by
  ext i
  by_cases hi : i = τ
  · subst i
    simp
  · simp [hi]

/-- Translating an integer reflection at `k` by `-k` conjugates it to the
reflection at the origin. -/
theorem siteReflection_translate_axis_neg {d : ℕ} (τ : Fin d) (k : ℤ)
    (x : Site d) :
    siteReflection τ 0 (translate (axisTranslation τ (-k)) x) =
      translate (axisTranslation τ (-k)) (siteReflection τ k x) := by
  ext i
  by_cases hi : i = τ
  · subst i
    simp [translate]
    ring
  · simp [translate, hi]

/-- Translating a link reflection at `k + 1/2` by `-k` conjugates it to the
link reflection at `1/2`. -/
theorem linkReflection_translate_axis_neg {d : ℕ} (τ : Fin d) (k : ℤ)
    (x : Site d) :
    linkReflection τ 0 (translate (axisTranslation τ (-k)) x) =
      translate (axisTranslation τ (-k)) (linkReflection τ k x) := by
  ext i
  by_cases hi : i = τ
  · subst i
    simp [translate]
    ring
  · simp [translate, hi]

namespace PositiveEdge

/-- The stored positive edge underlying half-integer/link reflection. -/
def linkReflect {d : ℕ} (τ : Fin d) (k : ℤ) (e : PositiveEdge d) :
    PositiveEdge d :=
  if e.direction = τ then ⟨linkReflection τ k e.target, e.direction⟩
  else ⟨linkReflection τ k e.source, e.direction⟩

@[simp]
theorem direction_linkReflect {d : ℕ} (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) :
    (e.linkReflect τ k).direction = e.direction := by
  by_cases h : e.direction = τ <;> simp [linkReflect, h]

@[simp]
theorem linkReflect_linkReflect {d : ℕ} (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) :
    (e.linkReflect τ k).linkReflect τ k = e := by
  rcases e with ⟨x, i⟩
  by_cases h : i = τ
  · subst i
    simp only [linkReflect, if_pos]
    congr 1
    calc
      linkReflection τ k
          (PositiveEdge.target ⟨linkReflection τ k
            (PositiveEdge.target ⟨x, τ⟩), τ⟩) =
          linkReflection τ k (linkReflection τ k x) := by
            congr 1
            ext j
            by_cases hj : j = τ
            · subst j
              simp [PositiveEdge.target, step, SignedDirection.forward,
                SignedDirection.delta, unitVector]
              ring
            · simp [PositiveEdge.target, step, SignedDirection.forward,
                SignedDirection.delta, unitVector, hj]
      _ = x := linkReflection_involutive τ k x
  · simp [linkReflect, h]

/-- Edge form of conjugating integer reflection at `k` to the origin. -/
theorem translate_siteReflect_axis_neg {d : ℕ} (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) :
    (e.translate (axisTranslation τ (-k))).siteReflect τ 0 =
      (e.siteReflect τ k).translate (axisTranslation τ (-k)) := by
  rcases e with ⟨x, i⟩
  by_cases hi : i = τ
  · subst i
    simp only [siteReflect, translate, if_pos]
    congr 1
    ext j
    by_cases hj : j = τ
    · subst j
      simp [PositiveEdge.target, step, SignedDirection.forward,
        SignedDirection.delta, unitVector, Lattice.Cubic.translate]
      ring
    · simp [PositiveEdge.target, step, SignedDirection.forward,
        SignedDirection.delta, unitVector, Lattice.Cubic.translate, hj]
  · simp only [siteReflect, translate, hi, if_false]
    congr 1
    exact siteReflection_translate_axis_neg τ k x

/-- Edge form of conjugating link reflection at `k + 1/2` to `1/2`. -/
theorem translate_linkReflect_axis_neg {d : ℕ} (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) :
    (e.translate (axisTranslation τ (-k))).linkReflect τ 0 =
      (e.linkReflect τ k).translate (axisTranslation τ (-k)) := by
  rcases e with ⟨x, i⟩
  by_cases hi : i = τ
  · subst i
    simp only [linkReflect, translate, if_pos]
    congr 1
    ext j
    by_cases hj : j = τ
    · subst j
      simp [PositiveEdge.target, step, SignedDirection.forward,
        SignedDirection.delta, unitVector, Lattice.Cubic.translate]
      ring
    · simp [PositiveEdge.target, step, SignedDirection.forward,
        SignedDirection.delta, unitVector, Lattice.Cubic.translate, hj]
  · simp only [linkReflect, translate, hi, if_false]
    congr 1
    exact linkReflection_translate_axis_neg τ k x

/-- Half-integer reflection as an involutive equivalence of stored edges. -/
def linkReflectionEquiv {d : ℕ} (τ : Fin d) (k : ℤ) :
    PositiveEdge d ≃ PositiveEdge d where
  toFun := linkReflect τ k
  invFun := linkReflect τ k
  left_inv := linkReflect_linkReflect τ k
  right_inv := linkReflect_linkReflect τ k

theorem linkReflect_endpoints {d : ℕ} (τ : Fin d) (k : ℤ)
    (e : PositiveEdge d) :
    ((e.linkReflect τ k).source = linkReflection τ k e.source ∧
        (e.linkReflect τ k).target = linkReflection τ k e.target) ∨
      ((e.linkReflect τ k).source = linkReflection τ k e.target ∧
        (e.linkReflect τ k).target = linkReflection τ k e.source) := by
  rcases e with ⟨x, i⟩
  by_cases hi : i = τ
  · subst i
    right
    constructor
    · simp [PositiveEdge.linkReflect]
    · simp only [PositiveEdge.linkReflect, if_pos, PositiveEdge.target]
      ext j
      by_cases hj : j = τ
      · subst j
        simp [step, SignedDirection.forward, SignedDirection.delta, unitVector]
        ring
      · simp [step, SignedDirection.forward, SignedDirection.delta, unitVector, hj]
  · left
    constructor
    · simp [PositiveEdge.linkReflect, hi]
    · simp only [PositiveEdge.linkReflect, hi, if_false, PositiveEdge.target]
      ext j
      by_cases hj : j = τ
      · subst j
        simp [step, SignedDirection.forward, SignedDirection.delta, unitVector,
          Ne.symm hi]
      · simp [step, SignedDirection.forward, SignedDirection.delta, unitVector, hj]

end PositiveEdge

namespace Plaquette

/-- The canonical plaquette obtained by reflection through the half-integer
plane `x τ = k + 1/2`.  It is the integer-reflected plaquette translated by
one lattice unit in the perpendicular direction. -/
def linkReflect {d : ℕ} (τ : Fin d) (k : ℤ) (p : Plaquette d) : Plaquette d :=
  (p.siteReflect τ k).translate (unitVector τ)

@[simp]
theorem first_linkReflect {d : ℕ} (τ : Fin d) (k : ℤ) (p : Plaquette d) :
    (p.linkReflect τ k).first = p.first := by
  simp only [linkReflect, Plaquette.translate, Plaquette.first_siteReflect]

@[simp]
theorem second_linkReflect {d : ℕ} (τ : Fin d) (k : ℤ) (p : Plaquette d) :
    (p.linkReflect τ k).second = p.second := by
  simp only [linkReflect, Plaquette.translate, Plaquette.second_siteReflect]

@[simp]
theorem linkReflect_linkReflect {d : ℕ} (τ : Fin d) (k : ℤ)
    (p : Plaquette d) :
    (p.linkReflect τ k).linkReflect τ k = p := by
  rcases p with ⟨x, i, j, hij⟩
  by_cases h : i = τ ∨ j = τ
  · simp only [linkReflect, Plaquette.siteReflect, h, if_pos,
      Plaquette.translate]
    congr 1
    ext a
    by_cases ha : a = τ
    · subst a
      simp [Lattice.Cubic.translate, step, SignedDirection.delta,
        unitVector]
      ring
    · simp [Lattice.Cubic.translate, step, SignedDirection.delta,
        SignedDirection.backward, unitVector, ha]
  · simp only [linkReflect, Plaquette.siteReflect, h, if_false,
      Plaquette.translate]
    congr 1
    ext a
    by_cases ha : a = τ
    · subst a
      simp [Lattice.Cubic.translate, unitVector]
      ring
    · simp [Lattice.Cubic.translate, unitVector, ha]

/-- Half-integer reflection as an involutive equivalence of canonical
plaquettes. -/
def linkReflectionEquiv {d : ℕ} (τ : Fin d) (k : ℤ) :
    Plaquette d ≃ Plaquette d where
  toFun := linkReflect τ k
  invFun := linkReflect τ k
  left_inv := linkReflect_linkReflect τ k
  right_inv := linkReflect_linkReflect τ k

end Plaquette

end YangMills.Lattice.Cubic

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Half-integer reflection of a full stored-edge configuration. -/
def linkReflectConfiguration (τ : Fin d) (k : ℤ) (A : Configuration d G) :
    Configuration d G :=
  fun e => if e.direction = τ then (A (e.linkReflect τ k))⁻¹
    else A (e.linkReflect τ k)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem positiveEdge_linkReflect_eq_translate_siteReflect
    (τ : Fin d) (k : ℤ) (e : PositiveEdge d) :
    e.linkReflect τ k = (e.siteReflect τ k).translate (unitVector τ) := by
  rcases e with ⟨x, i⟩
  by_cases hi : i = τ
  · subst i
    simp only [PositiveEdge.linkReflect, PositiveEdge.siteReflect, if_pos,
      PositiveEdge.translate]
    congr 1
  · simp only [PositiveEdge.linkReflect, PositiveEdge.siteReflect, hi,
      if_false, PositiveEdge.translate]
    congr 1

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Link reflection is integer reflection applied after translating the
underlying field by one perpendicular lattice unit. -/
theorem linkReflectConfiguration_eq_siteReflect_translate
    (τ : Fin d) (k : ℤ) (A : Configuration d G) :
    linkReflectConfiguration τ k A =
      siteReflectConfiguration τ k
        (fun e => A (e.translate (unitVector τ))) := by
  funext e
  by_cases he : e.direction = τ
  · simp only [linkReflectConfiguration, siteReflectConfiguration, he,
      if_pos]
    rw [positiveEdge_linkReflect_eq_translate_siteReflect]
  · simp only [linkReflectConfiguration, siteReflectConfiguration, he,
      if_false]
    rw [positiveEdge_linkReflect_eq_translate_siteReflect]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Reflection transports a gauge transformation by reflecting its site
argument. -/
theorem linkReflectConfiguration_gaugeTransform
    (τ : Fin d) (k : ℤ) (g : GaugeTransformation d G)
    (A : Configuration d G) :
    linkReflectConfiguration τ k (gaugeTransform g A) =
      gaugeTransform (fun x => g (linkReflection τ k x))
        (linkReflectConfiguration τ k A) := by
  funext e
  by_cases hdir : e.direction = τ
  · have hend :
        (e.linkReflect τ k).source = linkReflection τ k e.target ∧
          (e.linkReflect τ k).target = linkReflection τ k e.source := by
      rcases e with ⟨x, i⟩
      simp only at hdir
      subst i
      constructor
      · simp [PositiveEdge.linkReflect]
      · simp only [PositiveEdge.linkReflect, if_pos, PositiveEdge.target]
        ext j
        by_cases hj : j = τ
        · subst j
          simp [step, SignedDirection.forward, SignedDirection.delta, unitVector]
          ring
        · simp [step, SignedDirection.forward, SignedDirection.delta, unitVector, hj]
    simp only [linkReflectConfiguration, hdir, if_true, gaugeTransform_apply,
      mul_inv_rev]
    rw [hend.1, hend.2]
    group
  · have hend :
        (e.linkReflect τ k).source = linkReflection τ k e.source ∧
          (e.linkReflect τ k).target = linkReflection τ k e.target := by
      rcases e with ⟨x, i⟩
      simp only at hdir
      constructor
      · simp [PositiveEdge.linkReflect, hdir]
      · simp only [PositiveEdge.linkReflect, hdir, if_false,
          PositiveEdge.target]
        ext j
        by_cases hj : j = τ
        · subst j
          simp [step, SignedDirection.forward, SignedDirection.delta, unitVector,
            Ne.symm hdir]
        · simp [step, SignedDirection.forward, SignedDirection.delta, unitVector, hj]
    simp only [linkReflectConfiguration, hdir, if_false, gaugeTransform_apply]
    rw [hend.1, hend.2]

/-- Wilson plaquette potentials are covariant under half-integer reflection.
This follows from the integer-reflection identity and translation covariance
of plaquette holonomy. -/
@[simp]
theorem RealPlaquettePotential.apply_holonomy_linkReflectConfiguration
    (Φ : RealPlaquettePotential G) (τ : Fin d) (k : ℤ)
    (A : Configuration d G) (p : Plaquette d) :
    Φ (holonomy (linkReflectConfiguration τ k A) p.boundary) =
      Φ (holonomy A (p.linkReflect τ k).boundary) := by
  rw [linkReflectConfiguration_eq_siteReflect_translate]
  rw [Φ.apply_holonomy_siteReflectConfiguration]
  rw [holonomy_plaquette_translate]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem linkReflectConfiguration_linkReflectConfiguration
    (τ : Fin d) (k : ℤ) (A : Configuration d G) :
    linkReflectConfiguration τ k (linkReflectConfiguration τ k A) = A := by
  funext e
  by_cases h : e.direction = τ
  · simp [linkReflectConfiguration, h]
  · simp [linkReflectConfiguration, h]

/-- Integer reflection is continuous in the product topology. -/
theorem continuous_siteReflectConfiguration (τ : Fin d) (k : ℤ) :
    Continuous (siteReflectConfiguration (G := G) τ k) := by
  apply continuous_pi
  intro e
  by_cases h : e.direction = τ
  · simp only [siteReflectConfiguration, h, if_pos]
    exact continuous_inv.comp (continuous_apply (e.siteReflect τ k))
  · simp only [siteReflectConfiguration, h]
    exact continuous_apply (e.siteReflect τ k)

/-- Half-integer reflection is continuous in the product topology. -/
theorem continuous_linkReflectConfiguration (τ : Fin d) (k : ℤ) :
    Continuous (linkReflectConfiguration (G := G) τ k) := by
  apply continuous_pi
  intro e
  by_cases h : e.direction = τ
  · simp only [linkReflectConfiguration, h, if_pos]
    exact continuous_inv.comp (continuous_apply (e.linkReflect τ k))
  · simp only [linkReflectConfiguration, h]
    exact continuous_apply (e.linkReflect τ k)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Configuration form of conjugating site reflection at `k` to the origin
by an axial translation. -/
theorem translateConfiguration_siteReflect_axis_neg
    (τ : Fin d) (k : ℤ) (A : Configuration d G) :
    LocalObservable.translateConfiguration (axisTranslation τ (-k))
        (siteReflectConfiguration τ 0 A) =
      siteReflectConfiguration τ k
        (LocalObservable.translateConfiguration (axisTranslation τ (-k)) A) := by
  funext e
  have hdir : (e.translate (axisTranslation τ (-k))).direction = e.direction := rfl
  by_cases hd : e.direction = τ
  · simp only [LocalObservable.translateConfiguration,
      siteReflectConfiguration, hdir, hd, if_pos]
    rw [PositiveEdge.translate_siteReflect_axis_neg]
  · simp only [LocalObservable.translateConfiguration,
      siteReflectConfiguration, hdir, hd]
    rw [PositiveEdge.translate_siteReflect_axis_neg]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Configuration form of conjugating link reflection at `k + 1/2` to
reflection at `1/2` by an axial translation. -/
theorem translateConfiguration_linkReflect_axis_neg
    (τ : Fin d) (k : ℤ) (A : Configuration d G) :
    LocalObservable.translateConfiguration (axisTranslation τ (-k))
        (linkReflectConfiguration τ 0 A) =
      linkReflectConfiguration τ k
        (LocalObservable.translateConfiguration (axisTranslation τ (-k)) A) := by
  funext e
  have hdir : (e.translate (axisTranslation τ (-k))).direction = e.direction := rfl
  by_cases hd : e.direction = τ
  · simp only [LocalObservable.translateConfiguration,
      linkReflectConfiguration, hdir, hd, if_pos]
    rw [PositiveEdge.translate_linkReflect_axis_neg]
  · simp only [LocalObservable.translateConfiguration,
      linkReflectConfiguration, hdir, hd]
    rw [PositiveEdge.translate_linkReflect_axis_neg]

namespace LocalObservable

/-- Anti-linear reflection of a local observable through `x τ = k`. -/
def siteTheta (τ : Fin d) (k : ℤ) (F : LocalObservable d G) :
    LocalObservable d G where
  toContinuousMap :=
    { toFun := fun A => star (F (siteReflectConfiguration τ k A))
      continuous_toFun := Complex.continuous_conj.comp
        (F.toContinuousMap.continuous.comp
          (continuous_siteReflectConfiguration τ k)) }
  support := F.support.image (PositiveEdge.siteReflect τ k)
  dependsOn_support := by
    intro A B hAB
    apply congrArg star
    apply F.dependsOn_support
    intro e he
    have hrefl : e.siteReflect τ k ∈
        F.support.image (PositiveEdge.siteReflect τ k) :=
      Finset.mem_image.mpr ⟨e, he, rfl⟩
    by_cases hd : e.direction = τ
    · simp only [siteReflectConfiguration, hd, if_pos]
      rw [hAB (e.siteReflect τ k) hrefl]
    · simp only [siteReflectConfiguration, hd]
      exact hAB (e.siteReflect τ k) hrefl

/-- Anti-linear reflection of a local observable through `x τ = k + 1/2`. -/
def linkTheta (τ : Fin d) (k : ℤ) (F : LocalObservable d G) :
    LocalObservable d G where
  toContinuousMap :=
    { toFun := fun A => star (F (linkReflectConfiguration τ k A))
      continuous_toFun := Complex.continuous_conj.comp
        (F.toContinuousMap.continuous.comp
          (continuous_linkReflectConfiguration τ k)) }
  support := F.support.image (PositiveEdge.linkReflect τ k)
  dependsOn_support := by
    intro A B hAB
    apply congrArg star
    apply F.dependsOn_support
    intro e he
    have hrefl : e.linkReflect τ k ∈
        F.support.image (PositiveEdge.linkReflect τ k) :=
      Finset.mem_image.mpr ⟨e, he, rfl⟩
    by_cases hd : e.direction = τ
    · simp only [linkReflectConfiguration, hd, if_pos]
      rw [hAB (e.linkReflect τ k) hrefl]
    · simp only [linkReflectConfiguration, hd]
      exact hAB (e.linkReflect τ k) hrefl

@[simp]
theorem siteTheta_apply (τ : Fin d) (k : ℤ) (F : LocalObservable d G)
    (A : Configuration d G) :
    F.siteTheta τ k A = star (F (siteReflectConfiguration τ k A)) :=
  rfl

@[simp]
theorem linkTheta_apply (τ : Fin d) (k : ℤ) (F : LocalObservable d G)
    (A : Configuration d G) :
    F.linkTheta τ k A = star (F (linkReflectConfiguration τ k A)) :=
  rfl

@[simp]
theorem siteTheta_siteTheta_apply (τ : Fin d) (k : ℤ)
    (F : LocalObservable d G) (A : Configuration d G) :
    (F.siteTheta τ k).siteTheta τ k A = F A := by
  simp [siteTheta]

@[simp]
theorem linkTheta_linkTheta_apply (τ : Fin d) (k : ℤ)
    (F : LocalObservable d G) (A : Configuration d G) :
    (F.linkTheta τ k).linkTheta τ k A = F A := by
  simp [linkTheta]

/-- The local integrand in the integer-reflection pairing. -/
def siteReflectionProduct (τ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) : LocalObservable d G :=
  (F.siteTheta τ k).mul H

/-- The local integrand in the half-integer-reflection pairing. -/
def linkReflectionProduct (τ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) : LocalObservable d G :=
  (F.linkTheta τ k).mul H

@[simp]
theorem siteReflectionProduct_apply (τ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) (A : Configuration d G) :
    F.siteReflectionProduct τ k H A =
      star (F (siteReflectConfiguration τ k A)) * H A :=
  rfl

@[simp]
theorem linkReflectionProduct_apply (τ : Fin d) (k : ℤ)
    (F H : LocalObservable d G) (A : Configuration d G) :
    F.linkReflectionProduct τ k H A =
      star (F (linkReflectConfiguration τ k A)) * H A :=
  rfl

omit [IsTopologicalGroup G] in
/-- Pointwise products of gauge-invariant observables are gauge invariant. -/
theorem IsGaugeInvariant.mul {F H : LocalObservable d G}
    (hF : IsGaugeInvariant F) (hH : IsGaugeInvariant H) :
    IsGaugeInvariant (F.mul H) := by
  intro g A
  change F (gaugeTransform g A) * H (gaugeTransform g A) = F A * H A
  rw [hF, hH]

omit [IsTopologicalGroup G] in
/-- Complex conjugation preserves gauge invariance. -/
theorem IsGaugeInvariant.conj {F : LocalObservable d G}
    (hF : IsGaugeInvariant F) : IsGaugeInvariant F.conj := by
  intro g A
  exact congrArg star (hF g A)

/-- Half-integer reflection preserves full local gauge invariance. -/
theorem IsGaugeInvariant.linkTheta {F : LocalObservable d G}
    (hF : IsGaugeInvariant F) (τ : Fin d) (k : ℤ) :
    IsGaugeInvariant (F.linkTheta τ k) := by
  intro g A
  change star (F (linkReflectConfiguration τ k (gaugeTransform g A))) =
    star (F (linkReflectConfiguration τ k A))
  rw [linkReflectConfiguration_gaugeTransform]
  exact congrArg star
    (hF (fun x => g (linkReflection τ k x))
      (linkReflectConfiguration τ k A))

omit [IsTopologicalGroup G] in
/-- Translation preserves full local gauge invariance. -/
theorem IsGaugeInvariant.translatePullback {F : LocalObservable d G}
    (hF : IsGaugeInvariant F) (v : Site d) :
    IsGaugeInvariant (F.translatePullback v) := by
  intro g A
  change F (translateConfiguration v (gaugeTransform g A)) =
    F (translateConfiguration v A)
  have hcov : translateConfiguration v (gaugeTransform g A) =
      gaugeTransform (fun x => g (Lattice.Cubic.translate v x))
        (translateConfiguration v A) := by
    funext e
    simp only [translateConfiguration, gaugeTransform_apply,
      PositiveEdge.source_translate, PositiveEdge.target_translate]
  rw [hcov]
  exact hF (fun x => g (Lattice.Cubic.translate v x))
    (translateConfiguration v A)

/-- A local observable belongs to the positive algebra of the site plane
`x τ = k` when its recorded support is on or above that plane. -/
def SupportedInSitePositiveHalf (τ : Fin d) (k : ℤ)
    (F : LocalObservable d G) : Prop :=
  ∀ e ∈ F.support, k ≤ e.source τ

/-- A local observable belongs to the positive algebra of the link plane
`x τ = k + 1/2`.  Crossing perpendicular links are included. -/
def SupportedInLinkPositiveHalf (τ : Fin d) (k : ℤ)
    (F : LocalObservable d G) : Prop :=
  ∀ e ∈ F.support, k < e.target τ

end LocalObservable

end

end YangMills.Gauge
