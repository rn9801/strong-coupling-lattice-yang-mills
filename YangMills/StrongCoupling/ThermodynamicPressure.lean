/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.ThermodynamicCluster
import YangMills.StrongCoupling.ThermodynamicBoxes
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Thermodynamic pressure from the anchored cluster series

The finite free-region Mayer logarithm is averaged over plaquettes based in a
centered box. Translation invariance identifies every rooted coefficient with
its representative at the origin. The only finite-volume error is the
indicator that the translated finite carrier still fits in the box. Its bad
root density vanishes by the elementary inner-box/outer-box estimate, and the
existing rooted KP norm sum supplies the dominating summable function.
-/

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic Gauge.FiniteVolume Polymer
open Filter
open scoped BigOperators Topology

noncomputable section

local instance pressureDecidableEqPlaquette {d : ℕ} :
    DecidableEq (Plaquette d) := Classical.decEq _

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [GaugeHaarProbability G]

/-- All ordered plaquettes whose base lies in the centered site box. This is
the free region used for the pressure exhaustion. -/
def centeredBasePlaquettes (d n : ℕ) : Finset (Plaquette d) :=
  ((centeredBox d n).sites.product
      (Finset.univ : Finset (PlaquetteOrientation d))).map
    (plaquetteDecompositionEquiv d).toEmbedding

@[simp]
theorem mem_centeredBasePlaquettes (p : Plaquette d) (n : ℕ) :
    p ∈ centeredBasePlaquettes d n ↔ p.base ∈ (centeredBox d n).sites := by
  simp [centeredBasePlaquettes, plaquetteDecompositionEquiv]

theorem card_centeredBasePlaquettes (d n : ℕ) :
    (centeredBasePlaquettes d n).card =
      (2 * n + 1) ^ d * Fintype.card (PlaquetteOrientation d) := by
  simp [centeredBasePlaquettes, card_centeredBox_sites]

theorem card_centeredBasePlaquettes_eq_site_mul_orientation (d n : ℕ) :
    (centeredBasePlaquettes d n).card =
      (centeredBox d n).sites.card *
        Fintype.card (PlaquetteOrientation d) := by
  simp [centeredBasePlaquettes]

/-- Reindex a sum over the centered plaquette region by base site and ordered
orientation. -/
theorem sum_centeredBasePlaquettes_eq_sum_site_orientation
    (n : ℕ) (f : Plaquette d → ℂ) :
    ∑ p ∈ centeredBasePlaquettes d n, f p =
      ∑ x ∈ (centeredBox d n).sites,
        ∑ o : PlaquetteOrientation d, f (o.atOrigin.translate x) := by
  unfold centeredBasePlaquettes
  rw [Finset.sum_map]
  calc
    _ = ∑ x ∈ (centeredBox d n).sites,
        ∑ o ∈ (Finset.univ : Finset (PlaquetteOrientation d)),
          f ((plaquetteDecompositionEquiv d) (x, o)) :=
      Finset.sum_product _ _ _
    _ = _ := by
      simp [plaquetteDecompositionEquiv]

/-- Adding sites from centered boxes of radii `m` and `n` stays in the box of
radius `m+n`. -/
theorem add_mem_centeredBox {x y : Site d} {m n : ℕ}
    (hx : x ∈ (centeredBox d m).sites)
    (hy : y ∈ (centeredBox d n).sites) :
    x + y ∈ (centeredBox d (m + n)).sites := by
  rw [mem_centeredBox_sites] at hx hy ⊢
  intro i
  constructor
  · simpa only [Pi.add_apply, Int.natCast_add, neg_add_rev, add_comm] using
      (add_le_add (hx i).1 (hy i).1 :
        -(m : ℤ) + -(n : ℤ) ≤ x i + y i)
  · simpa only [Pi.add_apply, Int.natCast_add] using
      add_le_add (hx i).2 (hy i).2

/-- Base sites of the plaquettes in a finite Mayer carrier. -/
def infinitePlaquetteMayerCarrierBases
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) : Finset (Site d) :=
  (infinitePlaquetteMayerCarrier X).image Plaquette.base

/-- Every finite Mayer carrier has all of its base sites in one centered
box. -/
theorem infinitePlaquetteMayerCarrierBases_bounded
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) :
    ∃ r, infinitePlaquetteMayerCarrierBases X ⊆
      (centeredBox d r).sites := by
  let S := infinitePlaquetteMayerCarrierBases X
  change ∃ r, S ⊆ (centeredBox d r).sites
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x S hx ih =>
      obtain ⟨m, hm⟩ := site_mem_centeredBox_eventually x
      obtain ⟨n, hn⟩ := ih
      refine ⟨max m n, ?_⟩
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact centeredBox_sites_mono (Nat.le_max_left m n) hm
      · exact centeredBox_sites_mono (Nat.le_max_right m n) (hn hy)

/-- Base sites whose translate of a fixed Mayer carrier fits completely in
the radius-`n` plaquette region. -/
def centeredClusterFitSites (n : ℕ)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) : Finset (Site d) :=
  (centeredBox d n).sites.filter fun x ↦
    infinitePlaquetteMayerCarrier
        (translateInfinitePlaquetteMayerMultiIndex x X) ⊆
      centeredBasePlaquettes d n

@[simp]
theorem mem_centeredClusterFitSites (n : ℕ) (x : Site d)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) :
    x ∈ centeredClusterFitSites n X ↔
      x ∈ (centeredBox d n).sites ∧
      infinitePlaquetteMayerCarrier
          (translateInfinitePlaquetteMayerMultiIndex x X) ⊆
        centeredBasePlaquettes d n := by
  simp [centeredClusterFitSites]

/-- If the carrier offsets fit in radius `r`, every anchor in the radius-`n`
inner box gives a translated carrier fitting in the radius-`n+r` outer box. -/
theorem centeredBox_subset_centeredClusterFitSites_add
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) (r : ℕ)
    (hX : infinitePlaquetteMayerCarrierBases X ⊆
      (centeredBox d r).sites) (n : ℕ) :
    (centeredBox d n).sites ⊆ centeredClusterFitSites (n + r) X := by
  intro x hx
  rw [mem_centeredClusterFitSites]
  constructor
  · exact centeredBox_sites_mono (Nat.le_add_right n r) hx
  · intro p hp
    rw [infinitePlaquetteMayerCarrier_translate,
      Finset.mem_map_equiv] at hp
    rw [mem_centeredBasePlaquettes]
    let q := (Plaquette.translationEquiv x).symm p
    have hqbase : q.base ∈ infinitePlaquetteMayerCarrierBases X := by
      exact Finset.mem_image.mpr ⟨q, hp, rfl⟩
    have hadd := add_mem_centeredBox (hX hqbase) hx
    change p.base ∈ (centeredBox d (n + r)).sites
    have hbase : x + q.base = p.base := by
      simp [q, Plaquette.translationEquiv, Plaquette.translate,
        Lattice.Cubic.translate]
    rw [← hbase]
    simpa only [add_comm] using hadd

/-- Fraction of anchor sites for which the translated carrier fits. -/
def centeredClusterFitFraction (n : ℕ)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) : ℝ :=
  (centeredClusterFitSites n X).card / (centeredBox d n).sites.card

theorem centeredClusterFitFraction_nonneg (n : ℕ)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) :
    0 ≤ centeredClusterFitFraction n X := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem centeredClusterFitFraction_le_one (n : ℕ)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) :
    centeredClusterFitFraction n X ≤ 1 := by
  unfold centeredClusterFitFraction
  apply (div_le_one (by
    exact_mod_cast (Box.sites_nonempty (centeredBox d n)).card_pos)).2
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

theorem coe_centeredClusterFitFraction (n : ℕ)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) :
    (centeredClusterFitFraction n X : ℂ) =
      (((centeredBox d n).sites.card : ℂ)⁻¹) *
        ((centeredClusterFitSites n X).card : ℂ) := by
  rw [centeredClusterFitFraction, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_natCast,
    div_eq_inv_mul]

/-- Elementary centered-box boundary/volume ratio. -/
theorem tendsto_centeredBox_inner_outer_ratio (r : ℕ) :
    Tendsto (fun n : ℕ ↦
      (((centeredBox d n).sites.card : ℝ) /
        (centeredBox d (n + r)).sites.card)) atTop (𝓝 1) := by
  simp_rw [card_centeredBox_sites]
  have hbase : Tendsto (fun n : ℕ ↦
      ((2 * n + 1 : ℕ) : ℝ) /
        (((2 * (n + r) + 1 : ℕ) : ℕ) : ℝ)) atTop (𝓝 1) := by
    have hm : Tendsto (fun n : ℕ ↦ 2 * n + 1) atTop atTop :=
      tendsto_atTop_mono (fun n ↦ by dsimp; omega) tendsto_id
    have h := (tendsto_natCast_div_add_atTop ((2 * r : ℕ) : ℝ)).comp hm
    convert h using 1
    ext n
    norm_num
    ring
  simpa only [Nat.cast_pow, div_pow, one_pow] using hbase.pow d

/-- The fit fraction for every fixed finite cluster tends to one. This is the
precise boundary/volume estimate used below. -/
theorem tendsto_centeredClusterFitFraction
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) :
    Tendsto (fun n ↦ centeredClusterFitFraction n X) atTop (𝓝 1) := by
  obtain ⟨r, hr⟩ := infinitePlaquetteMayerCarrierBases_bounded X
  rw [← (tendsto_add_atTop_iff_nat r)]
  apply Tendsto.squeeze (tendsto_centeredBox_inner_outer_ratio (d := d) r)
      tendsto_const_nhds
  · intro n
    unfold centeredClusterFitFraction
    have hden : (0 : ℝ) < ((centeredBox d (n + r)).sites.card : ℝ) := by
      exact_mod_cast (Box.sites_nonempty (centeredBox d (n + r))).card_pos
    apply (div_le_div_iff_of_pos_right hden).2
    exact_mod_cast Finset.card_le_card
      (centeredBox_subset_centeredClusterFitSites_add X r hr n)
  · exact fun n ↦ centeredClusterFitFraction_le_one (n + r) X

/-- Finite-volume anchored pressure after translation reindexing: every
infinite rooted coefficient is multiplied by the fraction of base sites at
which its translated carrier fits in the centered region. -/
def centeredFiniteRootedPressure
    (Φ : RealPlaquettePotential G) (β : ℂ) (n : ℕ) : ℂ :=
  ((Fintype.card (PlaquetteOrientation d) : ℂ)⁻¹) *
    ∑ o : PlaquetteOrientation d,
      ∑' X : CountablePolymerModel.MayerMultiIndex
          (InfinitePlaquettePolymer d),
        (centeredClusterFitFraction n X : ℂ) *
          plaquetteRootedMayerTerm Φ β o.atOrigin X

/-- Translate a finite-volume plaquette-rooted cutoff back to its orientation
representative at the origin. -/
theorem tsum_centeredCarrierCutoff_translate
    (Φ : RealPlaquettePotential G) (β : ℂ) (n : ℕ)
    (x : Site d) (o : PlaquetteOrientation d) :
    (∑' X : CountablePolymerModel.MayerMultiIndex
        (InfinitePlaquettePolymer d),
      if infinitePlaquetteMayerCarrier X ⊆ centeredBasePlaquettes d n then
        plaquetteRootedMayerTerm Φ β (o.atOrigin.translate x) X else 0) =
    ∑' X : CountablePolymerModel.MayerMultiIndex
        (InfinitePlaquettePolymer d),
      if infinitePlaquetteMayerCarrier
          (translateInfinitePlaquetteMayerMultiIndex x X) ⊆
          centeredBasePlaquettes d n then
        plaquetteRootedMayerTerm Φ β o.atOrigin X else 0 := by
  calc
    _ = ∑' X, if infinitePlaquetteMayerCarrier
          (translateInfinitePlaquetteMayerMultiIndex x X) ⊆
          centeredBasePlaquettes d n then
        plaquetteRootedMayerTerm Φ β (o.atOrigin.translate x)
          (translateInfinitePlaquetteMayerMultiIndex x X) else 0 :=
      (Equiv.tsum_eq (translateInfinitePlaquetteMayerMultiIndex x)
        (fun X ↦ if infinitePlaquetteMayerCarrier X ⊆
            centeredBasePlaquettes d n then
          plaquetteRootedMayerTerm Φ β (o.atOrigin.translate x) X else 0)).symm
    _ = _ := by
      apply tsum_congr
      intro X
      by_cases hX : infinitePlaquetteMayerCarrier
          (translateInfinitePlaquetteMayerMultiIndex x X) ⊆
          centeredBasePlaquettes d n
      · simp only [hX, if_true]
        exact plaquetteRootedMayerTerm_translate Φ β x o.atOrigin X
      · simp [hX]

/-- At a site in the outer box, the carrier-containment indicator is exactly
membership in the fit-site finset. -/
theorem carrierCutoff_eq_fitSiteIndicator
    (n : ℕ) (x : Site d) (hx : x ∈ (centeredBox d n).sites)
    (X : CountablePolymerModel.MayerMultiIndex
      (InfinitePlaquettePolymer d)) (z : ℂ) :
    (if infinitePlaquetteMayerCarrier
          (translateInfinitePlaquetteMayerMultiIndex x X) ⊆
          centeredBasePlaquettes d n then z else 0) =
      if x ∈ centeredClusterFitSites n X then z else 0 := by
  by_cases hX : infinitePlaquetteMayerCarrier
      (translateInfinitePlaquetteMayerMultiIndex x X) ⊆
      centeredBasePlaquettes d n
  · have hmem : x ∈ centeredClusterFitSites n X := by
      exact (mem_centeredClusterFitSites n x X).mpr ⟨hx, hX⟩
    rw [if_pos hX, if_pos hmem]
  · have hmem : x ∉ centeredClusterFitSites n X := by
      intro hmem
      exact hX ((mem_centeredClusterFitSites n x X).mp hmem).2
    rw [if_neg hX, if_neg hmem]

/-- Summing the cutoff rooted series over anchor sites counts the fitting
sites of each fixed cluster. -/
theorem sum_tsum_centeredCarrierCutoff_eq_tsum_card_fit
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (n : ℕ) (o : PlaquetteOrientation d) :
    (∑ x ∈ (centeredBox d n).sites,
      ∑' X : CountablePolymerModel.MayerMultiIndex
          (InfinitePlaquettePolymer d),
        if infinitePlaquetteMayerCarrier X ⊆ centeredBasePlaquettes d n then
          plaquetteRootedMayerTerm Φ β (o.atOrigin.translate x) X else 0) =
      ∑' X : CountablePolymerModel.MayerMultiIndex
          (InfinitePlaquettePolymer d),
        ((centeredClusterFitSites n X).card : ℂ) *
          plaquetteRootedMayerTerm Φ β o.atOrigin X := by
  simp_rw [tsum_centeredCarrierCutoff_translate Φ β n]
  have hsummable (x : Site d) : Summable
      (fun X : CountablePolymerModel.MayerMultiIndex
          (InfinitePlaquettePolymer d) ↦
        if infinitePlaquetteMayerCarrier
            (translateInfinitePlaquetteMayerMultiIndex x X) ⊆
            centeredBasePlaquettes d n then
          plaquetteRootedMayerTerm Φ β o.atOrigin X else 0) := by
    apply Summable.of_norm_bounded
      (summable_norm_plaquetteRootedMayerTerm Φ hβ o.atOrigin)
    intro X
    split_ifs <;> simp
  rw [← Summable.tsum_finsetSum (s := (centeredBox d n).sites)
    (fun x _ ↦ hsummable x)]
  apply tsum_congr
  intro X
  rw [show ∑ x ∈ (centeredBox d n).sites,
      (if infinitePlaquetteMayerCarrier
          (translateInfinitePlaquetteMayerMultiIndex x X) ⊆
          centeredBasePlaquettes d n then
        plaquetteRootedMayerTerm Φ β o.atOrigin X else 0) =
      ∑ x ∈ (centeredBox d n).sites,
        if x ∈ centeredClusterFitSites n X then
          plaquetteRootedMayerTerm Φ β o.atOrigin X else 0 by
    apply Finset.sum_congr rfl
    intro x hx
    exact carrierCutoff_eq_fitSiteIndicator n x hx X _]
  rw [← Finset.sum_filter]
  have hfilter : (centeredBox d n).sites.filter
      (fun x ↦ x ∈ centeredClusterFitSites n X) =
      centeredClusterFitSites n X := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · exact fun h ↦ h.2
    · intro hxfit
      exact ⟨(mem_centeredClusterFitSites n x X).mp hxfit |>.1, hxfit⟩
  rw [hfilter]
  simp

/-- The exact centered finite-volume logarithm, reindexed by translation
orbits, is the sum of each rooted cluster coefficient times its number of
fitting anchor sites. -/
theorem symmetricMayerSum_restrict_centeredBasePlaquettes_eq_sum_tsum_card_fit
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) (n : ℕ) :
    ((infinitePlaquettePolymerModel (d := d) Φ β).restrict
      (InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G)
        (centeredBasePlaquettes d n))).symmetricMayerSum =
      ∑ o : PlaquetteOrientation d,
        ∑' X : CountablePolymerModel.MayerMultiIndex
            (InfinitePlaquettePolymer d),
          ((centeredClusterFitSites n X).card : ℂ) *
            plaquetteRootedMayerTerm Φ β o.atOrigin X := by
  rw [symmetricMayerSum_restrict_freeRegion_eq_sum_tsum_rooted Φ hβ]
  rw [sum_centeredBasePlaquettes_eq_sum_site_orientation]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  exact sum_tsum_centeredCarrierCutoff_eq_tsum_card_fit Φ hβ n o

/-- Dividing the exact finite Mayer logarithm by the number of plaquettes in
the centered region gives exactly the finite fit-fraction pressure. -/
theorem normalized_symmetricMayerSum_restrict_centeredBasePlaquettes
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) (n : ℕ) :
    (((centeredBasePlaquettes d n).card : ℂ)⁻¹) *
        ((infinitePlaquettePolymerModel (d := d) Φ β).restrict
          (InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G)
            (centeredBasePlaquettes d n))).symmetricMayerSum =
      centeredFiniteRootedPressure (d := d) Φ β n := by
  rw [symmetricMayerSum_restrict_centeredBasePlaquettes_eq_sum_tsum_card_fit
    Φ hβ n]
  rw [card_centeredBasePlaquettes_eq_site_mul_orientation, Nat.cast_mul,
    mul_inv]
  unfold centeredFiniteRootedPressure
  simp_rw [coe_centeredClusterFitFraction]
  calc
    _ = ((Fintype.card (PlaquetteOrientation d) : ℂ)⁻¹) *
        ((((centeredBox d n).sites.card : ℂ)⁻¹) *
          ∑ o : PlaquetteOrientation d,
            ∑' X : CountablePolymerModel.MayerMultiIndex
                (InfinitePlaquettePolymer d),
              ((centeredClusterFitSites n X).card : ℂ) *
                plaquetteRootedMayerTerm Φ β o.atOrigin X) := by ring
    _ = ((Fintype.card (PlaquetteOrientation d) : ℂ)⁻¹) *
        ∑ o : PlaquetteOrientation d,
          ∑' X : CountablePolymerModel.MayerMultiIndex
              (InfinitePlaquettePolymer d),
            (((centeredBox d n).sites.card : ℂ)⁻¹ *
              ((centeredClusterFitSites n X).card : ℂ)) *
                plaquetteRootedMayerTerm Φ β o.atOrigin X := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro o _
      rw [← tsum_mul_left]
      apply tsum_congr
      intro X
      ring

/-- For a fixed orientation, the finite fit-fraction series tends to the full
anchored rooted series. This is Tannery dominated convergence with precisely
the rooted KP norm sum already used for pressure analyticity. -/
theorem tendsto_centeredFiniteRootedPressure_orientation
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound)
    (o : PlaquetteOrientation d) :
    Tendsto (fun n ↦
      ∑' X : CountablePolymerModel.MayerMultiIndex
          (InfinitePlaquettePolymer d),
        (centeredClusterFitFraction n X : ℂ) *
          plaquetteRootedMayerTerm Φ β o.atOrigin X) atTop
      (𝓝 (∑' X, plaquetteRootedMayerTerm Φ β o.atOrigin X)) := by
  apply tendsto_tsum_of_dominated_convergence
    (summable_norm_plaquetteRootedMayerTerm Φ hβ o.atOrigin)
  · intro X
    have hfit := tendsto_centeredClusterFitFraction (d := d) X
    simpa only [Function.comp_apply, Complex.ofReal_one, one_mul] using
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hfit).mul_const
        (plaquetteRootedMayerTerm Φ β o.atOrigin X))
  · filter_upwards [] with n
    intro X
    rw [norm_mul, Complex.norm_real]
    calc
      |centeredClusterFitFraction n X| *
          ‖plaquetteRootedMayerTerm Φ β o.atOrigin X‖ =
          centeredClusterFitFraction n X *
            ‖plaquetteRootedMayerTerm Φ β o.atOrigin X‖ := by
        rw [abs_of_nonneg (centeredClusterFitFraction_nonneg n X)]
      _ ≤ 1 * ‖plaquetteRootedMayerTerm Φ β o.atOrigin X‖ := by
        exact mul_le_mul_of_nonneg_right
          (centeredClusterFitFraction_le_one n X) (norm_nonneg _)
      _ = _ := one_mul _

/-- The translated finite rooted pressure converges to the analytic anchored
pressure on the full explicit strong-coupling disk. -/
theorem tendsto_centeredFiniteRootedPressure
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Tendsto (centeredFiniteRootedPressure (d := d) Φ β) atTop
      (𝓝 (anchoredPressure (d := d) Φ β)) := by
  unfold centeredFiniteRootedPressure anchoredPressure
    anchoredPressurePerSite
  exact (tendsto_const_nhds.mul
    (tendsto_finsetSum _ fun o _ ↦
      tendsto_centeredFiniteRootedPressure_orientation Φ hβ o))

/-- The symmetry-normalized finite connected logarithms converge to the
anchored pressure.  The logarithm branch is the Mayer series normalized at
`β = 0`, rather than an independently chosen complex logarithm. -/
theorem tendsto_normalized_symmetricMayerSum_centeredBasePlaquettes
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Tendsto (fun n ↦
      (((centeredBasePlaquettes d n).card : ℂ)⁻¹) *
        ((infinitePlaquettePolymerModel (d := d) Φ β).restrict
          (InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G)
            (centeredBasePlaquettes d n))).symmetricMayerSum) atTop
      (𝓝 (anchoredPressure (d := d) Φ β)) := by
  apply (tendsto_centeredFiniteRootedPressure (d := d) Φ hβ).congr'
  filter_upwards [] with n
  exact (normalized_symmetricMayerSum_restrict_centeredBasePlaquettes
    Φ hβ n).symm

/-- Dividing the exact finite connected logarithm by the number of anchor
sites gives the fit-fraction series in the usual per-site normalization. -/
theorem normalized_symmetricMayerSum_restrict_centeredBasePlaquettes_perSite
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) (n : ℕ) :
    (((centeredBox d n).sites.card : ℂ)⁻¹) *
        ((infinitePlaquettePolymerModel (d := d) Φ β).restrict
          (InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G)
            (centeredBasePlaquettes d n))).symmetricMayerSum =
      ∑ o : PlaquetteOrientation d,
        ∑' X : CountablePolymerModel.MayerMultiIndex
            (InfinitePlaquettePolymer d),
          (centeredClusterFitFraction n X : ℂ) *
            plaquetteRootedMayerTerm Φ β o.atOrigin X := by
  rw [symmetricMayerSum_restrict_centeredBasePlaquettes_eq_sum_tsum_card_fit
    Φ hβ n]
  simp_rw [coe_centeredClusterFitFraction]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro X
  ring

/-- The exact finite connected logarithms per lattice site converge to the
analytic per-site anchored pressure. -/
theorem tendsto_normalized_symmetricMayerSum_centeredBasePlaquettes_perSite
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) :
    Tendsto (fun n ↦
      (((centeredBox d n).sites.card : ℂ)⁻¹) *
        ((infinitePlaquettePolymerModel (d := d) Φ β).restrict
          (InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G)
            (centeredBasePlaquettes d n))).symmetricMayerSum) atTop
      (nhds (anchoredPressurePerSite (d := d) Φ β)) := by
  unfold anchoredPressurePerSite
  apply (tendsto_finsetSum _ fun o _ ↦
    tendsto_centeredFiniteRootedPressure_orientation Φ hβ o).congr'
  filter_upwards [] with n
  exact (normalized_symmetricMayerSum_restrict_centeredBasePlaquettes_perSite
    Φ hβ n).symm

/-- The exact finite connected logarithm occurring in the pressure limit
exponentiates to the centered free-region Yang--Mills partition function. -/
theorem exp_symmetricMayerSum_centeredBasePlaquettes_eq_partitionFunction
    (Φ : RealPlaquettePotential G) {β : ℂ}
    (hβ : ‖β‖ < latticeStrongCouplingRadius d Φ.bound) (n : ℕ) :
    Complex.exp
        (((infinitePlaquettePolymerModel (d := d) Φ β).restrict
          (InfinitePlaquettePolymer.freeRegionGlobalPolymers (G := G)
            (centeredBasePlaquettes d n))).symmetricMayerSum) =
      complexPartitionFunction
        (InfinitePlaquettePolymer.freeRegionSpecification (G := G)
          (centeredBasePlaquettes d n)) Φ β :=
  exp_symmetricMayerSum_restrict_freeRegion_eq_complexPartitionFunction
    Φ hβ (centeredBasePlaquettes d n)

end

end YangMills.StrongCoupling
