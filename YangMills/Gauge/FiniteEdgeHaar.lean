/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.ProductHaar
import YangMills.Lattice.Box

/-!
# Haar probability on finite edge configurations

This module puts independent Haar variables on the positive edges of a finite
cubic box. A finite gauge field assigns a group element to each site in the
box. Its action on an edge variable is left multiplication at the source and
right multiplication by the inverse value at the target.

The main theorem, `productHaar_map_gaugeTransform`, is the exit theorem for
Milestone 2: a finite gauge transformation sends the joint law of independent
Haar edge variables to the same product Haar law.
-/

open MeasureTheory

namespace YangMills.Gauge

namespace FiniteEdgeHaar

open Lattice.Cubic

/-- Gauge-group assignments to the sites of a finite box. -/
abbrev SiteField {d : ℕ} (b : Box d) (G : Type*) := b.sites → G

/-- Gauge-group assignments to the canonical positive edges of a finite box. -/
abbrev EdgeField {d : ℕ} (b : Box d) (G : Type*) := b.positiveEdges → G

/-- The source endpoint of an internal positive edge, including its proof of
membership in the finite box. -/
def sourceSite {d : ℕ} (b : Box d) (e : b.positiveEdges) : b.sites :=
  ⟨e.1.source, (b.mem_positiveEdges e.1).mp e.2 |>.1⟩

/-- The target endpoint of an internal positive edge, including its proof of
membership in the finite box. -/
def targetSite {d : ℕ} (b : Box d) (e : b.positiveEdges) : b.sites :=
  ⟨e.1.target, (b.mem_positiveEdges e.1).mp e.2 |>.2⟩

variable {G : Type*} [Group G] [MeasurableSpace G] [GaugeHaarProbability G]

/-- The product Haar probability on all positive edge variables in `b`. -/
noncomputable abbrev edgeMeasure {d : ℕ} (b : Box d) : Measure (EdgeField b G) :=
  ProductHaar.measure G b.positiveEdges

/-- The action of a finite site gauge field on positive edge variables. -/
def gaugeTransform {d : ℕ} (b : Box d) (g : SiteField b G) (U : EdgeField b G) :
    EdgeField b G :=
  fun e => g (sourceSite b e) * U e * (g (targetSite b e))⁻¹

section MeasurableMul

variable [MeasurableMul G]

/-- Every finite gauge transformation preserves product Haar probability. -/
theorem measurePreserving_gaugeTransform {d : ℕ} (b : Box d) (g : SiteField b G) :
    MeasurePreserving (gaugeTransform b g) (edgeMeasure (G := G) b)
      (edgeMeasure (G := G) b) := by
  simpa only [edgeMeasure, gaugeTransform, ProductHaar.measure] using
    (ProductHaar.measurePreserving_coordinatewise
      (G := G) (fun _ : b.positiveEdges => GaugeHaarProbability.haar G)
      (fun e x => g (sourceSite b e) * x * (g (targetSite b e))⁻¹)
      (fun e => GaugeHaarProbability.measurePreserving_mulLeft_mulRight G
        (g (sourceSite b e)) (g (targetSite b e))⁻¹))

/-- Independent Haar edge variables remain product Haar after applying a
finite gauge transformation. -/
theorem productHaar_map_gaugeTransform {d : ℕ} (b : Box d) (g : SiteField b G) :
    Measure.map (gaugeTransform b g) (edgeMeasure (G := G) b) =
      edgeMeasure (G := G) b :=
  (measurePreserving_gaugeTransform (G := G) b g).map_eq

end MeasurableMul

end FiniteEdgeHaar

end YangMills.Gauge
