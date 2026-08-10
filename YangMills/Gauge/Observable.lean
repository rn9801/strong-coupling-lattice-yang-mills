/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.Holonomy
import YangMills.Lattice.Plaquette
import Mathlib.Analysis.Complex.Basic
import Mathlib.Logic.Function.DependsOn
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Star

/-!
# Local gauge observables

A local observable is a continuous complex-valued function on the infinite
positive-edge configuration space, together with a finite (not necessarily
minimal) support. Continuous class functions of loop holonomy give the basic
gauge-invariant examples.

The generic `wilsonLoop` constructor is labelled by a continuous class
function. Milestone 5 will construct such class functions from normalized
characters of continuous unitary representations without changing this local
observable API.
-/

namespace YangMills.Gauge

open Lattice.Cubic

noncomputable section

/-- A continuous complex-valued class function on a topological group. -/
structure ContinuousClassFunction (G : Type*) [Group G] [TopologicalSpace G] where
  toContinuousMap : C(G, ℂ)
  map_conj : ∀ a x, toContinuousMap (a * x * a⁻¹) = toContinuousMap x

namespace ContinuousClassFunction

variable {G : Type*} [Group G] [TopologicalSpace G]

instance : CoeFun (ContinuousClassFunction G) fun _ => G → ℂ :=
  ⟨fun φ => φ.toContinuousMap⟩

@[simp]
theorem coe_apply (φ : ContinuousClassFunction G) (x : G) :
    φ.toContinuousMap x = φ x :=
  rfl

/-- A constant is a continuous class function. -/
def const (z : ℂ) : ContinuousClassFunction G where
  toContinuousMap := ContinuousMap.const _ z
  map_conj := fun _ _ => rfl

end ContinuousClassFunction

/-- A complex observable is gauge invariant when every site field fixes it. -/
def IsGaugeInvariant {d : ℕ} {G : Type*} [Group G]
    (F : Configuration d G → ℂ) : Prop :=
  ∀ g A, F (gaugeTransform g A) = F A

/-- A continuous observable with an explicit finite edge support. The support
is not required to be minimal. -/
structure LocalObservable (d : ℕ) (G : Type*) [TopologicalSpace G] where
  toContinuousMap : C(Configuration d G, ℂ)
  support : Finset (PositiveEdge d)
  dependsOn_support : DependsOn toContinuousMap (support : Set (PositiveEdge d))

namespace LocalObservable

variable {d : ℕ} {G : Type*} [TopologicalSpace G]

instance : CoeFun (LocalObservable d G) fun _ => Configuration d G → ℂ :=
  ⟨fun F => F.toContinuousMap⟩

@[simp]
theorem coe_apply (F : LocalObservable d G) (A : Configuration d G) :
    F.toContinuousMap A = F A :=
  rfl

omit [TopologicalSpace G] in
/-- Dependence on a finite support persists after enlarging that support. -/
theorem dependsOn_mono {F : Configuration d G → ℂ}
    {S T : Finset (PositiveEdge d)} (hF : DependsOn F (S : Set (PositiveEdge d)))
    (hST : S ⊆ T) :
    DependsOn F (T : Set (PositiveEdge d)) := by
  intro A B h
  exact hF fun e he => h e (hST he)

/-- Replace an observable's recorded support by a larger convenient support. -/
def enlarge (F : LocalObservable d G) (T : Finset (PositiveEdge d))
    (h : F.support ⊆ T) : LocalObservable d G where
  toContinuousMap := F.toContinuousMap
  support := T
  dependsOn_support := dependsOn_mono F.dependsOn_support h

/-- The constant local observable. -/
def const (z : ℂ) : LocalObservable d G where
  toContinuousMap := ContinuousMap.const _ z
  support := ∅
  dependsOn_support := by
    intro A B h
    rfl

/-- Sum of two local observables, supported on the union. -/
def add (F H : LocalObservable d G) : LocalObservable d G where
  toContinuousMap := F.toContinuousMap + H.toContinuousMap
  support := F.support ∪ H.support
  dependsOn_support := by
    intro A B h
    simp only [ContinuousMap.add_apply]
    rw [F.dependsOn_support (fun e he => h e (Finset.mem_union_left _ he)),
      H.dependsOn_support (fun e he => h e (Finset.mem_union_right _ he))]

@[simp]
theorem add_apply (F H : LocalObservable d G) (A : Configuration d G) :
    add F H A = F A + H A :=
  rfl

/-- Scalar multiplication of a local observable does not enlarge its support. -/
def smul (z : ℂ) (F : LocalObservable d G) : LocalObservable d G where
  toContinuousMap := z • F.toContinuousMap
  support := F.support
  dependsOn_support := by
    intro A B h
    simp only [ContinuousMap.smul_apply]
    rw [F.dependsOn_support h]

/-- Pointwise negation of a local observable. -/
def neg (F : LocalObservable d G) : LocalObservable d G :=
  smul (-1) F

/-- Difference of two local observables, supported on the union. -/
def sub (F H : LocalObservable d G) : LocalObservable d G :=
  add F (neg H)

@[simp]
theorem smul_apply (z : ℂ) (F : LocalObservable d G)
    (A : Configuration d G) : smul z F A = z * F A :=
  rfl

@[simp]
theorem neg_apply (F : LocalObservable d G) (A : Configuration d G) :
    neg F A = -F A := by
  simp [neg, smul]

@[simp]
theorem sub_apply (F H : LocalObservable d G) (A : Configuration d G) :
    sub F H A = F A - H A := by
  change F A + (-1 : ℂ) * H A = F A - H A
  ring

/-- Product of two local observables, supported on the union. -/
def mul (F H : LocalObservable d G) : LocalObservable d G where
  toContinuousMap := F.toContinuousMap * H.toContinuousMap
  support := F.support ∪ H.support
  dependsOn_support := by
    intro A B h
    simp only [ContinuousMap.mul_apply]
    rw [F.dependsOn_support (fun e he => h e (Finset.mem_union_left _ he)),
      H.dependsOn_support (fun e he => h e (Finset.mem_union_right _ he))]

/-- Pointwise complex conjugate of a local observable. -/
def conj (F : LocalObservable d G) : LocalObservable d G where
  toContinuousMap := star F.toContinuousMap
  support := F.support
  dependsOn_support := by
    intro A B h
    simp only [ContinuousMap.star_apply]
    exact congrArg star (F.dependsOn_support h)

section Bounds

variable [CompactSpace G]

/-- A local observable on a compact gauge group, viewed as a bounded continuous map. -/
def toBoundedContinuousMap (F : LocalObservable d G) :
    BoundedContinuousFunction (Configuration d G) ℂ :=
  BoundedContinuousFunction.mkOfCompact F.toContinuousMap

/-- The canonical sup norm controls every pointwise observable value. -/
theorem norm_apply_le (F : LocalObservable d G) (A : Configuration d G) :
    ‖F A‖ ≤ ‖F.toBoundedContinuousMap‖ :=
  BoundedContinuousFunction.norm_coe_le_norm F.toBoundedContinuousMap A

end Bounds

section Translation

/-- Pull a configuration back along translation of positive edges. -/
def translateConfiguration (v : Site d) (A : Configuration d G) : Configuration d G :=
  fun e => A (e.translate v)

/-- Translation pullback is continuous in the product topology. -/
theorem continuous_translateConfiguration (v : Site d) :
    Continuous (translateConfiguration (G := G) v) :=
  continuous_pi fun e => continuous_apply (e.translate v)

/-- Pull a local observable back along lattice translation. -/
def translatePullback (v : Site d) (F : LocalObservable d G) : LocalObservable d G where
  toContinuousMap := F.toContinuousMap.comp
    ⟨translateConfiguration v, continuous_translateConfiguration v⟩
  support := F.support.image (PositiveEdge.translate v)
  dependsOn_support := by
    intro A B h
    apply F.dependsOn_support
    intro e he
    exact h (e.translate v) (Finset.mem_image.mpr ⟨e, he, rfl⟩)

end Translation

section GaugePullback

variable [Group G] [IsTopologicalGroup G]

/-- A fixed gauge transformation is a continuous self-map of configuration space. -/
def gaugeTransformContinuous (g : GaugeTransformation d G) :
    C(Configuration d G, Configuration d G) where
  toFun := gaugeTransform g
  continuous_toFun := continuous_pi fun e =>
    (continuous_const.mul (continuous_apply e)).mul continuous_const

/-- Pull a local observable back along a fixed gauge transformation. -/
def gaugePullback (g : GaugeTransformation d G) (F : LocalObservable d G) :
    LocalObservable d G where
  toContinuousMap := F.toContinuousMap.comp (gaugeTransformContinuous g)
  support := F.support
  dependsOn_support := by
    intro A B h
    apply F.dependsOn_support
    intro e he
    change gaugeTransform g A e = gaugeTransform g B e
    simp only [gaugeTransform_apply]
    rw [h e he]

end GaugePullback

section LoopObservables

variable [Group G] [IsTopologicalGroup G]

/-- A continuous class function evaluated on a based loop holonomy. -/
def loopClassFunction (φ : ContinuousClassFunction G) {x : Site d}
    (p : Lattice.Cubic.Path x x) :
    LocalObservable d G where
  toContinuousMap := φ.toContinuousMap.comp
    ⟨(fun A => holonomy A p), continuous_holonomy p⟩
  support := p.edgeSupport
  dependsOn_support := by
    intro A B h
    exact congrArg φ (holonomy_eq_of_eqOn_edgeSupport p h)

@[simp]
theorem loopClassFunction_apply (φ : ContinuousClassFunction G)
    {x : Site d} (p : Lattice.Cubic.Path x x) (A : Configuration d G) :
    loopClassFunction φ p A = φ (holonomy A p) :=
  by simp [loopClassFunction]

/-- Every continuous class function of loop holonomy is gauge invariant. -/
theorem loopClassFunction_gaugeInvariant (φ : ContinuousClassFunction G)
    {x : Site d} (p : Lattice.Cubic.Path x x) :
    IsGaugeInvariant (loopClassFunction φ p) := by
  intro g A
  simp only [loopClassFunction_apply, holonomy_loop_gaugeTransform]
  exact φ.map_conj (g x) (holonomy A p)

/-- The class-function observable associated with one coordinate plaquette. -/
def plaquetteClassFunction (φ : ContinuousClassFunction G) (p : Plaquette d) :
    LocalObservable d G :=
  loopClassFunction φ p.boundary

/-- A one-plaquette class-function observable is gauge invariant. -/
theorem plaquetteClassFunction_gaugeInvariant
    (φ : ContinuousClassFunction G) (p : Plaquette d) :
    IsGaugeInvariant (plaquetteClassFunction φ p) :=
  loopClassFunction_gaugeInvariant φ p.boundary

/-- Wilson loop labelled by a continuous class function. Representation
characters will supply the canonical labels in Milestone 5. -/
def wilsonLoop (χ : ContinuousClassFunction G) {x : Site d}
    (C : Lattice.Cubic.Path x x) :
    LocalObservable d G :=
  loopClassFunction χ C

/-- Wilson loops are gauge invariant. -/
theorem wilsonLoop_gaugeInvariant
    (χ : ContinuousClassFunction G) {x : Site d} (C : Lattice.Cubic.Path x x) :
    IsGaugeInvariant (wilsonLoop χ C) :=
  loopClassFunction_gaugeInvariant χ C

end LoopObservables

end LocalObservable

end

end YangMills.Gauge
