/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Lattice.Box
import YangMills.StrongCoupling.Counting
import YangMills.StrongCoupling.ExponentialClustering
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Centered cubic exhaustion for the cluster thermodynamic limit

The box of radius `n` is the coordinate interval `[-n,n]^d`.  Its dynamic
edges are the positive edges with both endpoints in the box.  Its active
plaquettes are all plaquettes incident to at least one such edge, so boundary
plaquettes may read the explicitly frozen exterior field.

The exhaustion is nested and cofinal on every finite recorded edge support.
These are the geometric inputs needed to instantiate the one- and two-root
cluster certificates in the Yang--Mills model.
-/

namespace YangMills.StrongCoupling

open MeasureTheory
open Gauge Lattice.Cubic

noncomputable section

local instance thermodynamicBoxDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

/-- The centered cubic box `[-n,n]^d`. -/
def centeredBox (d n : ℕ) : Box d where
  lower := fun _ => -(n : ℤ)
  upper := fun _ => (n : ℤ)
  lower_le_upper := fun _ =>
    (neg_nonpos.mpr (Int.natCast_nonneg n)).trans (Int.natCast_nonneg n)

@[simp]
theorem mem_centeredBox_sites {d n : ℕ} (x : Site d) :
    x ∈ (centeredBox d n).sites ↔
      ∀ i, -(n : ℤ) ≤ x i ∧ x i ≤ (n : ℤ) := by
  rw [Box.mem_sites]
  constructor
  · intro h i
    exact ⟨h.1 i, h.2 i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

/-- Centered site sets are nested. -/
theorem centeredBox_sites_mono {d m n : ℕ} (hmn : m ≤ n) :
    (centeredBox d m).sites ⊆ (centeredBox d n).sites := by
  intro x hx
  rw [mem_centeredBox_sites] at hx ⊢
  intro i
  have hcast : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
  exact ⟨(neg_le_neg hcast).trans (hx i).1, (hx i).2.trans hcast⟩

/-- Centered positive-edge sets are nested. -/
theorem centeredBox_positiveEdges_mono {d m n : ℕ} (hmn : m ≤ n) :
    (centeredBox d m).positiveEdges ⊆ (centeredBox d n).positiveEdges := by
  intro e he
  rw [Box.mem_positiveEdges] at he ⊢
  exact ⟨centeredBox_sites_mono hmn he.1,
    centeredBox_sites_mono hmn he.2⟩

/-- Every lattice site lies in some centered box. -/
theorem site_mem_centeredBox_eventually {d : ℕ} (x : Site d) :
    ∃ n, x ∈ (centeredBox d n).sites := by
  let n : ℕ := ∑ i : Fin d, (x i).natAbs
  refine ⟨n, (mem_centeredBox_sites x).2 fun i => ?_⟩
  have hi : (x i).natAbs ≤ n := by
    dsimp [n]
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin d)))
      (f := fun j : Fin d => (x j).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hi' : ((x i).natAbs : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast hi
  have habs : |x i| ≤ (n : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact hi'
  exact (abs_le.mp habs)

/-- Every positive edge lies in some centered box. -/
theorem positiveEdge_mem_centeredBox_eventually {d : ℕ}
    (e : PositiveEdge d) :
    ∃ n, e ∈ (centeredBox d n).positiveEdges := by
  obtain ⟨m, hm⟩ := site_mem_centeredBox_eventually e.source
  obtain ⟨n, hn⟩ := site_mem_centeredBox_eventually e.target
  refine ⟨max m n, ?_⟩
  rw [Box.mem_positiveEdges]
  exact ⟨centeredBox_sites_mono (Nat.le_max_left m n) hm,
    centeredBox_sites_mono (Nat.le_max_right m n) hn⟩

/-- Every finite edge support is contained in one centered box. -/
theorem finiteSupport_subset_centeredBox {d : ℕ}
    (S : Finset (PositiveEdge d)) :
    ∃ n, S ⊆ (centeredBox d n).positiveEdges := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert e S he ih =>
      obtain ⟨m, hm⟩ := positiveEdge_mem_centeredBox_eventually e
      obtain ⟨n, hn⟩ := ih
      refine ⟨max m n, ?_⟩
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact centeredBox_positiveEdges_mono (Nat.le_max_left m n) hm
      · exact centeredBox_positiveEdges_mono (Nat.le_max_right m n) (hn hx)

/-- Once a finite support enters the exhaustion, it remains inside every
larger centered box. -/
theorem finiteSupport_subset_centeredBox_eventually {d : ℕ}
    (S : Finset (PositiveEdge d)) :
    ∃ N, ∀ n, N ≤ n → S ⊆ (centeredBox d n).positiveEdges := by
  obtain ⟨N, hN⟩ := finiteSupport_subset_centeredBox S
  exact ⟨N, fun n hn => hN.trans (centeredBox_positiveEdges_mono hn)⟩

/-- Plaquettes active in the radius-`n` specification: every plaquette
incident to at least one dynamic positive edge. -/
def centeredActivePlaquettes (d n : ℕ) : Finset (Plaquette d) :=
  (centeredBox d n).positiveEdges.biUnion incidentPlaquettes

/-- The arbitrary-box specification associated with the centered exhaustion
and a frozen exterior field. -/
def centeredSpecification {d : ℕ} {G : Type*}
    (n : ℕ) (η : Configuration d G) : FiniteSpecification d G where
  dynamicEdges := (centeredBox d n).positiveEdges
  activePlaquettes := centeredActivePlaquettes d n
  exterior := η

@[simp]
theorem centeredSpecification_dynamicEdges {d : ℕ} {G : Type*}
    (n : ℕ) (η : Configuration d G) :
    (centeredSpecification n η).dynamicEdges =
      (centeredBox d n).positiveEdges :=
  rfl

@[simp]
theorem centeredSpecification_activePlaquettes {d : ℕ} {G : Type*}
    (n : ℕ) (η : Configuration d G) :
    (centeredSpecification n η).activePlaquettes =
      centeredActivePlaquettes d n :=
  rfl

/-- The full-space Yang--Mills probability sequence along centered boxes. -/
def centeredGibbsSequence {d : ℕ} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G]
    (η : ℕ → Configuration d G) (Φ : RealPlaquettePotential G) (β : ℝ) :
    ℕ → ProbabilityMeasure (Configuration d G) :=
  fun n => fullGibbsProbability (centeredSpecification n (η n)) Φ β

end

end YangMills.StrongCoupling
