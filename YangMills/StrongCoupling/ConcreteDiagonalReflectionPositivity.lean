/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.DiagonalReflectionBridge
import YangMills.StrongCoupling.InfiniteVolumeDiagonalReflectionPositivity
import YangMills.StrongCoupling.SymmetricReflectionBoxes

/-!
# Concrete diagonal reflection positivity at strong coupling

Centered boxes with identity exterior are invariant under every coordinate
diagonal through the origin.  The concrete finite bridge identifies their
Wilson action with the cut-plaquette Taylor/Fubini normal form.  The KP local
limit, boundary independence, and translation invariance then give diagonal
reflection positivity and Cauchy--Schwarz for every affine parallel plane.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- Centered site boxes are invariant under a coordinate-diagonal reflection
through the origin. -/
theorem diagonalReflection_mem_centeredBox_iff
    {τ σ : Fin d} (hτσ : τ ≠ σ) (n : ℕ) (x : Site d) :
    diagonalReflection τ σ 0 x ∈ (centeredBox d n).sites ↔
      x ∈ (centeredBox d n).sites := by
  simp only [mem_centeredBox_sites]
  constructor <;> intro hx i
  · by_cases hiτ : i = τ
    · subst i
      simpa [hτσ] using hx σ
    · by_cases hiσ : i = σ
      · subst i
        simpa [hτσ] using hx τ
      · simpa [diagonalReflection_apply_other hiτ hiσ] using hx i
  · by_cases hiτ : i = τ
    · subst i
      simpa using hx σ
    · by_cases hiσ : i = σ
      · subst i
        simpa [hτσ] using hx τ
      · simpa [diagonalReflection_apply_other hiτ hiσ] using hx i

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem diagonalReflect_mem_centeredBox_positiveEdges_iff
    {τ σ : Fin d} (hτσ : τ ≠ σ) (n : ℕ) (e : PositiveEdge d) :
    e.diagonalReflect τ σ 0 ∈ (centeredBox d n).positiveEdges ↔
      e ∈ (centeredBox d n).positiveEdges := by
  rw [Box.mem_positiveEdges, Box.mem_positiveEdges]
  change ((e.diagonalReflect τ σ 0).source ∈ (centeredBox d n).sites ∧
      (e.diagonalReflect τ σ 0).target ∈ (centeredBox d n).sites) ↔
    (e.source ∈ (centeredBox d n).sites ∧
      e.target ∈ (centeredBox d n).sites)
  rw [PositiveEdge.source_diagonalReflect,
    PositiveEdge.target_diagonalReflect hτσ,
    diagonalReflection_mem_centeredBox_iff hτσ,
    diagonalReflection_mem_centeredBox_iff hτσ]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem diagonalReflect_mem_centeredActivePlaquettes_of_mem
    {τ σ : Fin d} (hτσ : τ ≠ σ) (n : ℕ) (p : Plaquette d) :
    p ∈ centeredActivePlaquettes d n →
      p.diagonalReflect τ σ 0 ∈ centeredActivePlaquettes d n := by
  simp only [centeredActivePlaquettes, Finset.mem_biUnion]
  rintro ⟨e, hebox, hep⟩
  refine ⟨e.diagonalReflect τ σ 0, ?_, ?_⟩
  · rw [diagonalReflect_mem_centeredBox_positiveEdges_iff hτσ]
    exact hebox
  · rw [mem_incidentPlaquettes_iff_mem_boundary] at hep ⊢
    exact Gauge.FiniteSpecification.diagonalReflect_mem_plaquette_boundary_of_mem
      hτσ 0 e p hep

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
theorem diagonalReflect_mem_centeredActivePlaquettes_iff
    {τ σ : Fin d} (hτσ : τ ≠ σ) (n : ℕ) (p : Plaquette d) :
    p.diagonalReflect τ σ 0 ∈ centeredActivePlaquettes d n ↔
      p ∈ centeredActivePlaquettes d n := by
  constructor
  · intro hp
    have href := diagonalReflect_mem_centeredActivePlaquettes_of_mem hτσ n
      (p.diagonalReflect τ σ 0) hp
    rw [Plaquette.diagonalReflect_diagonalReflect hτσ] at href
    exact href
  · exact diagonalReflect_mem_centeredActivePlaquettes_of_mem hτσ n p

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G] in
/-- Every centered identity-exterior specification has exact diagonal
symmetry through the origin. -/
theorem centeredSpecification_one_diagonalSymmetric
    (n : ℕ) {τ σ : Fin d} (hτσ : τ ≠ σ) :
    (centeredSpecification n (1 : Configuration d G)).DiagonalSymmetric
      τ σ 0 := by
  refine ⟨hτσ, ?_, ?_, ?_⟩
  · intro e
    exact (diagonalReflect_mem_centeredBox_positiveEdges_iff hτσ n e).symm
  · intro p
    exact (diagonalReflect_mem_centeredActivePlaquettes_iff hτσ n p).symm
  · funext e
    simp [diagonalReflectConfiguration, centeredSpecification]

/-- Every centered identity-exterior Wilson law is diagonally reflection
positive at nonnegative coupling. -/
theorem centeredGibbsSequence_one_diagonalReflectionPositive
    {nρ : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G nρ)
    {β : ℝ} (hβ : 0 ≤ β) (m : ℕ) {τ σ : Fin d} (hτσ : τ ≠ σ) :
    DiagonalReflectionPositive
      (centeredGibbsSequence (fun _ => (1 : Configuration d G))
        ρ.wilsonPotential β m : Measure (Configuration d G)) τ σ 0 := by
  intro _ F hF
  let Λ := centeredSpecification m (1 : Configuration d G)
  have hfinite := Λ.diagonalReflectionPositive_gibbsMeasure τ σ 0
    (centeredSpecification_one_diagonalSymmetric m hτσ) ρ hβ F hF
  change Complex.im (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (F.diagonalReflectionProduct τ σ 0 F)) = 0 ∧
    0 ≤ Complex.re (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (F.diagonalReflectionProduct τ σ 0 F))
  rw [localExpectation_fullGibbsProbability,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact hfinite

/-- Finite centered identity-exterior Wilson laws satisfy diagonal
Cauchy--Schwarz. -/
theorem centeredGibbsSequence_one_diagonalReflectionCauchySchwarz
    {nρ : ℕ} (ρ : Wilson.ContinuousUnitaryRepData G nρ)
    {β : ℝ} (hβ : 0 ≤ β) (m : ℕ) {τ σ : Fin d} (hτσ : τ ≠ σ) :
    DiagonalReflectionCauchySchwarz
      (centeredGibbsSequence (fun _ => (1 : Configuration d G))
        ρ.wilsonPotential β m : Measure (Configuration d G)) τ σ 0 := by
  intro _ F H hF hH
  let Λ := centeredSpecification m (1 : Configuration d G)
  have hfinite := Λ.normSq_integral_gibbsMeasure_diagonalReflectionProduct_le
    τ σ 0 (centeredSpecification_one_diagonalSymmetric m hτσ)
    ρ hβ F H hF hH
  unfold diagonalReflectionPairing
  simp only [centeredGibbsSequence]
  change Complex.normSq (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (F.diagonalReflectionProduct τ σ 0 H)) ≤
    Complex.re (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (F.diagonalReflectionProduct τ σ 0 F)) *
    Complex.re (localExpectation
      (fullGibbsProbability Λ ρ.wilsonPotential β)
        (H.diagonalReflectionProduct τ σ 0 H))
  rw [localExpectation_fullGibbsProbability,
    localExpectation_fullGibbsProbability,
    localExpectation_fullGibbsProbability,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure,
    complexGibbsExpectation_ofReal_eq_integral_gibbsMeasure]
  exact hfinite

/-- Concrete strong-coupling diagonal reflection positivity on every affine
parallel plane, with arbitrary centered exterior sequence. -/
theorem centeredInfiniteVolume_diagonalReflectionPositive
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) :
    DiagonalReflectionPositive
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) τ σ k := by
  let oneExterior : ℕ → Configuration d G := fun _ => 1
  have hzeroOne : DiagonalReflectionPositive
      (centeredInfiniteVolumeMeasure oneExterior ρ.wilsonPotential β hβ)
        τ σ 0 := by
    apply centeredInfiniteVolume_diagonalReflectionPositive_of_eventually
    exact Filter.Eventually.of_forall fun m =>
      centeredGibbsSequence_one_diagonalReflectionPositive ρ hβ0 m hτσ
  have hzero :=
    centeredInfiniteVolume_diagonalReflectionPositive_boundary_independent
      oneExterior η ρ.wilsonPotential β hβ τ σ 0 hzeroOne
  exact centeredInfiniteVolume_diagonalReflectionPositive_all_planes
    η ρ.wilsonPotential β hβ hτσ hzero k

/-- Concrete infinite-volume diagonal reflection Cauchy--Schwarz on every
affine parallel plane. -/
theorem centeredInfiniteVolume_diagonalReflectionCauchySchwarz
    (η : ℕ → Configuration d G) {nρ : ℕ}
    (ρ : Wilson.ContinuousUnitaryRepData G nρ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ‖(β : ℂ)‖ <
      latticeStrongCouplingRadius d ρ.wilsonPotential.bound)
    {τ σ : Fin d} (hτσ : τ ≠ σ) (k : ℤ) :
    DiagonalReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure η ρ.wilsonPotential β hβ) τ σ k := by
  let oneExterior : ℕ → Configuration d G := fun _ => 1
  have hzeroOne : DiagonalReflectionCauchySchwarz
      (centeredInfiniteVolumeMeasure oneExterior ρ.wilsonPotential β hβ)
        τ σ 0 := by
    apply centeredInfiniteVolume_diagonalReflectionCauchySchwarz_of_eventually
    exact Filter.Eventually.of_forall fun m =>
      centeredGibbsSequence_one_diagonalReflectionCauchySchwarz ρ hβ0 m hτσ
  have hzero :=
    centeredInfiniteVolume_diagonalReflectionCauchySchwarz_boundary_independent
      oneExterior η ρ.wilsonPotential β hβ τ σ 0 hzeroOne
  exact centeredInfiniteVolume_diagonalReflectionCauchySchwarz_all_planes
    η ρ.wilsonPotential β hβ hτσ hzero k

end

end YangMills.StrongCoupling
