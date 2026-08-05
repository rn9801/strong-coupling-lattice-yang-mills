/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.Configuration
import YangMills.Lattice.Path
import Mathlib.Data.Finset.Insert
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Path holonomy and gauge covariance

Holonomy is the ordered product of signed-edge values along Mathlib's typed
quiver paths. The endpoint indices make the telescoping proof of gauge
covariance available for every composable cubic path, rather than only for a
hard-coded plaquette word.
-/

namespace YangMills.Lattice.Cubic.Path

variable {d : ℕ} {x : Site d}

/-- The finite set of stored positive edges read by a path. -/
def edgeSupport : {y : Site d} → Path x y → Finset (PositiveEdge d)
  | _, .nil => ∅
  | _, .cons p e => insert e.1.positive (edgeSupport p)

@[simp]
theorem edgeSupport_nil (x : Site d) : edgeSupport (.nil : Path x x) = ∅ :=
  rfl

@[simp]
theorem edgeSupport_cons {y z : Site d} (p : Path x y) (e : EdgeBetween y z) :
    edgeSupport (p.cons e) = insert e.1.positive (edgeSupport p) :=
  rfl

end YangMills.Lattice.Cubic.Path

namespace YangMills.Gauge

open Lattice.Cubic

variable {d : ℕ} {G : Type*} [Group G]

/-- Ordered parallel transport along a typed cubic path. -/
def holonomy (A : Configuration d G) {x : Site d} : {y : Site d} → Path x y → G
  | _, .nil => 1
  | _, .cons p e => holonomy A p * signedEdgeValue A e.1

@[simp]
theorem holonomy_nil (A : Configuration d G) (x : Site d) :
    holonomy A (.nil : Path x x) = 1 :=
  rfl

@[simp]
theorem holonomy_cons (A : Configuration d G) {x y z : Site d}
    (p : Path x y) (e : EdgeBetween y z) :
    holonomy A (p.cons e) = holonomy A p * signedEdgeValue A e.1 :=
  rfl

@[simp]
theorem holonomy_toPath (A : Configuration d G) {x y : Site d} (e : EdgeBetween x y) :
    holonomy A e.toPath = signedEdgeValue A e.1 := by
  simp [Quiver.Hom.toPath]

/-- Holonomy turns path concatenation into group multiplication. -/
@[simp]
theorem holonomy_comp (A : Configuration d G) {x y z : Site d}
    (p : Path x y) (q : Path y z) :
    holonomy A (p.comp q) = holonomy A p * holonomy A q := by
  induction q with
  | nil => simp
  | cons q e ih => simp [ih, mul_assoc]

/-- Reversing a path inverts its holonomy. -/
@[simp]
theorem holonomy_reverse (A : Configuration d G) {x y : Site d} (p : Path x y) :
    holonomy A p.reverse = (holonomy A p)⁻¹ := by
  induction p with
  | nil => simp
  | cons p e ih =>
      rw [Quiver.Path.reverse, holonomy_comp, holonomy_toPath, ih, holonomy_cons]
      change signedEdgeValue A e.1.reverse * (holonomy A p)⁻¹ =
        (holonomy A p * signedEdgeValue A e.1)⁻¹
      rw [signedEdgeValue_reverse]
      group

/-- Path holonomy reads only the finite positive-edge support of the path. -/
theorem holonomy_eq_of_eqOn_edgeSupport
    {A B : Configuration d G} {x y : Site d} (p : Path x y)
    (h : ∀ e ∈ p.edgeSupport, A e = B e) :
    holonomy A p = holonomy B p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [holonomy_cons, holonomy_cons]
      congr 1
      · exact ih fun a ha => h a (by simp [ha])
      · exact signedEdgeValue_eq_of_eq_positive e.1 (h e.1.positive (by simp))

section GaugeCovariance

/-- Holonomy transforms at its two endpoints; all interior site factors telescope. -/
theorem holonomy_gaugeTransform
    (g : GaugeTransformation d G) (A : Configuration d G)
    {x y : Site d} (p : Path x y) :
    holonomy (gaugeTransform g A) p =
      g x * holonomy A p * (g y)⁻¹ := by
  induction p with
  | nil => simp
  | cons p e ih =>
      rw [holonomy_cons, ih, signedEdgeValue_gaugeTransform]
      have hsource : e.1.source = _ := e.2.1
      have htarget : e.1.target = _ := e.2.2
      rw [hsource, htarget]
      rw [holonomy_cons]
      group

/-- A based loop transforms by conjugation at its base point. -/
theorem holonomy_loop_gaugeTransform
    (g : GaugeTransformation d G) (A : Configuration d G)
    {x : Site d} (p : Path x x) :
    holonomy (gaugeTransform g A) p =
      g x * holonomy A p * (g x)⁻¹ :=
  holonomy_gaugeTransform g A p

end GaugeCovariance

section Continuity

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Evaluating a fixed signed edge is continuous in the product topology. -/
theorem continuous_signedEdgeValue (e : SignedEdge d) :
    Continuous (fun A : Configuration d G => signedEdgeValue A e) := by
  cases e with
  | mk source direction =>
      cases direction with
      | mk axis orientation =>
          cases orientation with
          | forward => exact continuous_apply _
          | backward => exact (continuous_apply _).inv

/-- Holonomy of a fixed finite path is continuous in the configuration. -/
theorem continuous_holonomy {x y : Site d} (p : Path x y) :
    Continuous (fun A : Configuration d G => holonomy A p) := by
  induction p with
  | nil => exact continuous_const
  | cons p e ih => exact ih.mul (continuous_signedEdgeValue e.1)

end Continuity

end YangMills.Gauge
