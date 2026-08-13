/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Lattice.CubicalCharge
import YangMills.Probability.CenterSelection
import YangMills.Wilson.Loop
import Mathlib.GroupTheory.OrderOfElement

/-!
# Center twists and Wilson charge selection

Multiplying one stored positive edge by a chosen central element multiplies
the holonomy of a path by the corresponding signed incidence power.  This is
the local algebraic input for the edgewise Haar selection rule.
-/

namespace YangMills.Wilson

open YangMills.Gauge YangMills.Lattice.Cubic

noncomputable section

/-- Multiply one stored positive edge on the left by `z`. -/
def twistEdge {d : ℕ} {G : Type*} [Group G]
    (z : G) (e : PositiveEdge d) (A : Configuration d G) : Configuration d G :=
  fun q ↦ if q = e then z * A q else A q

@[simp]
theorem twistEdge_same {d : ℕ} {G : Type*} [Group G]
    (z : G) (e : PositiveEdge d) (A : Configuration d G) :
    twistEdge z e A e = z * A e := by
  simp [twistEdge]

theorem twistEdge_of_ne {d : ℕ} {G : Type*} [Group G]
    (z : G) {e q : PositiveEdge d} (h : q ≠ e) (A : Configuration d G) :
    twistEdge z e A q = A q := by
  simp [twistEdge, h]

/-- One oriented edge acquires the signed center-incidence power under an
edge twist. -/
theorem signedEdgeValue_twistEdge
    {d : ℕ} {G : Type*} [Group G] (z : G)
    (hz : ∀ g : G, z * g = g * z)
    (e : PositiveEdge d) (A : Configuration d G) (q : SignedEdge d) :
    signedEdgeValue (twistEdge z e A) q =
      z ^ (q.edgeChain ℤ e) * signedEdgeValue A q := by
  cases q with
  | mk source direction =>
      cases direction with
      | mk axis orientation =>
          cases orientation with
          | forward =>
              let q : PositiveEdge d := ⟨source, axis⟩
              change twistEdge z e A q =
                z ^ ((Finsupp.single q 1 : EdgeChain d ℤ) e) * A q
              by_cases h : q = e
              · subst e
                simp [twistEdge]
              · simp [twistEdge, h, Ne.symm h, Finsupp.single_apply]
          | backward =>
              let q : PositiveEdge d :=
                (SignedEdge.mk source (.backward axis)).positive
              change (twistEdge z e A q)⁻¹ =
                z ^ ((Finsupp.single q (-1) : EdgeChain d ℤ) e) * (A q)⁻¹
              by_cases h : q = e
              · subst e
                have hc : Commute z (A q) := hz (A q)
                rw [twistEdge_same]
                rw [Finsupp.single_eq_same]
                rw [mul_inv_rev, zpow_neg_one, hc.inv_inv.eq]
              ·
                rw [twistEdge_of_ne z h A]
                simp [Finsupp.single_apply, h, Ne.symm h]

/-- A center twist of one stored edge multiplies path holonomy by the center
element raised to that edge's signed incidence number. -/
theorem holonomy_twistEdge
    {d : ℕ} {G : Type*} [Group G] (z : G)
    (hz : ∀ g : G, z * g = g * z)
    (e : PositiveEdge d) (A : Configuration d G)
    {x y : Site d} (C : Lattice.Cubic.Path x y) :
    holonomy (twistEdge z e A) C =
      z ^ C.edgeIncidence e * holonomy A C := by
  induction C with
  | nil => simp [Path.edgeIncidence]
  | cons C q ih =>
      rw [holonomy_cons, holonomy_cons, ih,
        signedEdgeValue_twistEdge z hz e A q.1]
      simp only [Path.edgeIncidence, Path.edgeChain_cons, Finsupp.add_apply]
      rw [zpow_add]
      have hc : Commute (z ^ (q.1.edgeChain ℤ e)) (holonomy A C) :=
        (show Commute z (holonomy A C) from hz (holonomy A C)).zpow_left _
      calc
        z ^ (Path.edgeChain ℤ C) e * holonomy A C *
              (z ^ (q.1.edgeChain ℤ e) * signedEdgeValue A q.1) =
            z ^ (Path.edgeChain ℤ C) e *
              (holonomy A C * z ^ (q.1.edgeChain ℤ e)) *
                signedEdgeValue A q.1 := by group
        _ = z ^ (Path.edgeChain ℤ C) e *
              (z ^ (q.1.edgeChain ℤ e) * holonomy A C) *
                signedEdgeValue A q.1 := by rw [hc.eq]
        _ = z ^ (Path.edgeChain ℤ C) e * z ^ (q.1.edgeChain ℤ e) *
              (holonomy A C * signedEdgeValue A q.1) := by group

namespace CenterChargeData

variable {n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  {rho : ContinuousUnitaryRepData G n}

/-- The scalar center action extends from the chosen generator to every
integer power. -/
theorem normalizedCharacter_zpow_mul (kappa : CenterChargeData rho)
    (q : ℤ) (g : G) :
    rho.normalizedCharacter (kappa.z ^ q * g) =
      kappa.omega ^ q * rho.normalizedCharacter g := by
  have homega : kappa.omega ≠ 0 := by
    intro h
    simpa [h] using kappa.norm_omega
  have hpos : ∀ k : ℕ, ∀ h : G,
      rho.normalizedCharacter (kappa.z ^ k * h) =
        kappa.omega ^ k * rho.normalizedCharacter h := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro h
        rw [pow_succ', pow_succ']
        rw [mul_assoc]
        rw [kappa.normalizedCharacter_center_mul, ih]
        ring
  have hinv : ∀ h : G,
      rho.normalizedCharacter (kappa.z⁻¹ * h) =
        kappa.omega⁻¹ * rho.normalizedCharacter h := by
    intro h
    have hc := kappa.normalizedCharacter_center_mul (kappa.z⁻¹ * h)
    have hc' : rho.normalizedCharacter h =
        kappa.omega * rho.normalizedCharacter (kappa.z⁻¹ * h) := by
      simpa [mul_assoc] using hc
    calc
      rho.normalizedCharacter (kappa.z⁻¹ * h) =
          kappa.omega⁻¹ *
            (kappa.omega * rho.normalizedCharacter (kappa.z⁻¹ * h)) := by
        rw [← mul_assoc, inv_mul_cancel₀ homega, one_mul]
      _ = kappa.omega⁻¹ * rho.normalizedCharacter h := by rw [← hc']
  have hneg : ∀ k : ℕ, ∀ h : G,
      rho.normalizedCharacter ((kappa.z⁻¹) ^ k * h) =
        (kappa.omega⁻¹) ^ k * rho.normalizedCharacter h := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro h
        rw [pow_succ', pow_succ']
        rw [mul_assoc]
        rw [hinv, ih]
        ring
  cases q with
  | ofNat k => simpa using hpos k g
  | negSucc k =>
      simpa [zpow_negSucc, inv_pow] using hneg (k + 1) g

/-- The chosen center phase is unitary, so complex conjugation reverses its
integer charge. -/
theorem star_omega_zpow (kappa : CenterChargeData rho) (q : ℤ) :
    star (kappa.omega ^ q) = kappa.omega ^ (-q) := by
  have homega : kappa.omega ≠ 0 := by
    intro h
    simpa [h] using kappa.norm_omega
  have hstar : star kappa.omega = kappa.omega⁻¹ := by
    apply (mul_left_cancel₀ homega)
    rw [mul_inv_cancel₀ homega]
    simpa [Complex.mul_conj', kappa.norm_omega]
  cases q with
  | ofNat k =>
      simp [zpow_natCast, hstar, zpow_neg, inv_pow]
  | negSucc k =>
      have hneg : -(Int.negSucc k) = ((k + 1 : ℕ) : ℤ) := by omega
      rw [hneg, zpow_natCast, zpow_negSucc]
      calc
        star ((kappa.omega ^ (k + 1))⁻¹) =
            (star (kappa.omega ^ (k + 1)))⁻¹ := by
          change (starRingEnd ℂ) ((kappa.omega ^ (k + 1))⁻¹) = _
          rw [map_inv₀, starRingEnd_apply]
        _ = kappa.omega ^ (k + 1) := by
          change ((starRingEnd ℂ) (kappa.omega ^ (k + 1)))⁻¹ = _
          rw [map_pow, starRingEnd_apply, hstar, inv_pow, inv_inv]

/-- Wilson normalized characters transform by the signed path incidence
phase under a one-edge center twist. -/
theorem normalizedCharacter_holonomy_twistEdge
    [IsTopologicalGroup G] (kappa : CenterChargeData rho)
    {d : ℕ} (e : PositiveEdge d) (A : Configuration d G)
    {x y : Site d} (C : Lattice.Cubic.Path x y) :
    rho.normalizedCharacter (holonomy (twistEdge kappa.z e A) C) =
      kappa.omega ^ C.edgeIncidence e *
        rho.normalizedCharacter (holonomy A C) := by
  rw [holonomy_twistEdge kappa.z kappa.central_z e A C]
  exact kappa.normalizedCharacter_zpow_mul _ _

end CenterChargeData

end

end YangMills.Wilson
