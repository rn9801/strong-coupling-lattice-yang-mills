/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Polymer.LabelledMayerExponential
import YangMills.Polymer.LabelledTreeSummation
import YangMills.Polymer.SourcePowerSeries

/-!
# Finite polymer gases with distinguished source roots

This polymer-only construction adjoins a finite type of source vertices to a
hard-core gas.  Distinct roots are mutually compatible; a root is connected
to a bulk polymer precisely when the supplied `touches` relation holds.  The
source activities are independent variables, so the linear and bilinear
coefficients are selected by the source-scaling lemmas in `Polymer.Mayer`.
-/

namespace YangMills.Polymer

noncomputable section

namespace FinitePolymerModel

variable {P R : Type*} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]

/-- A bulk polymer or an adjoined observable/source root. -/
abbrev AugmentedPolymer (P R : Type*) := P ⊕ R

/-- Add finitely many source roots to a hard-core polymer model. -/
def augmentRoots (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) :
    FinitePolymerModel (AugmentedPolymer P R) where
  incompatible x y := match x, y with
    | Sum.inl γ, Sum.inl δ => M.incompatible γ δ
    | Sum.inl γ, Sum.inr r => touches r γ
    | Sum.inr r, Sum.inl γ => touches r γ
    | Sum.inr r, Sum.inr s => r = s
  decidableIncompatible := fun x y => by
    cases x <;> cases y <;> infer_instance
  symmetric_incompatible := by
    rintro (x | r) (y | s) h
    · exact M.symmetric_incompatible h
    · exact h
    · exact h
    · exact h.symm
  self_incompatible := by
    rintro (x | r)
    · exact M.self_incompatible x
    · rfl
  activity x := match x with
    | Sum.inl γ => M.activity γ
    | Sum.inr r => rootActivity r

/-- Add a finite family of mutually exclusive source roots.  Unlike
`augmentRoots`, every pair of root values is incompatible, so a compatible
family contains at most one root.  This is the form used when a root value
itself records a complete marked decoration. -/
def augmentExclusiveRoots (M : FinitePolymerModel P)
    (touches : R → P → Prop) [DecidableRel touches]
    (rootActivity : R → ℂ) : FinitePolymerModel (AugmentedPolymer P R) where
  incompatible x y := match x, y with
    | Sum.inl γ, Sum.inl δ => M.incompatible γ δ
    | Sum.inl γ, Sum.inr r => touches r γ
    | Sum.inr r, Sum.inl γ => touches r γ
    | Sum.inr _, Sum.inr _ => True
  decidableIncompatible := fun x y => by
    cases x <;> cases y <;> infer_instance
  symmetric_incompatible := by
    rintro (x | r) (y | s) h
    · exact M.symmetric_incompatible h
    · exact h
    · exact h
    · trivial
  self_incompatible := by
    rintro (x | r)
    · exact M.self_incompatible x
    · trivial
  activity x := match x with
    | Sum.inl γ => M.activity γ
    | Sum.inr r => rootActivity r

/-- Adjoin two colours of source roots.  Roots of the same colour are
mutually exclusive, while a left and a right root use the supplied cross
incompatibility relation.  This is the source geometry needed for exact
two-observable cumulants with decoration-valued roots. -/
def twoColorRightTouches {S : Type*}
    (touchesRight : S → P → Prop) (crossIncompatible : R → S → Prop)
    (s : S) : P ⊕ R → Prop
  | Sum.inl gamma => touchesRight s gamma
  | Sum.inr r => crossIncompatible r s

instance {S : Type*} (touchesRight : S → P → Prop)
    (crossIncompatible : R → S → Prop)
    [DecidableRel touchesRight] [DecidableRel crossIncompatible] :
    DecidableRel (twoColorRightTouches touchesRight crossIncompatible) :=
  fun _ x => by cases x <;> simp only [twoColorRightTouches] <;> infer_instance

def augmentTwoColorExclusiveRoots {S : Type*} [Fintype S] [DecidableEq S]
    (M : FinitePolymerModel P)
    (touchesLeft : R → P → Prop) [DecidableRel touchesLeft]
    (touchesRight : S → P → Prop) [DecidableRel touchesRight]
    (crossIncompatible : R → S → Prop) [DecidableRel crossIncompatible]
    (leftActivity : R → ℂ) (rightActivity : S → ℂ) :
    FinitePolymerModel ((P ⊕ R) ⊕ S) :=
  (M.augmentExclusiveRoots touchesLeft leftActivity).augmentExclusiveRoots
    (twoColorRightTouches touchesRight crossIncompatible) rightActivity

@[simp]
theorem augmentTwoColorExclusiveRoots_incompatible_left_left
    {S : Type*} [Fintype S] [DecidableEq S]
    (M : FinitePolymerModel P)
    (touchesLeft : R → P → Prop) [DecidableRel touchesLeft]
    (touchesRight : S → P → Prop) [DecidableRel touchesRight]
    (crossIncompatible : R → S → Prop) [DecidableRel crossIncompatible]
    (leftActivity : R → ℂ) (rightActivity : S → ℂ) (r r' : R) :
    (M.augmentTwoColorExclusiveRoots touchesLeft touchesRight crossIncompatible
      leftActivity rightActivity).incompatible
        (Sum.inl (Sum.inr r)) (Sum.inl (Sum.inr r')) := by
  trivial

@[simp]
theorem augmentTwoColorExclusiveRoots_incompatible_right_right
    {S : Type*} [Fintype S] [DecidableEq S]
    (M : FinitePolymerModel P)
    (touchesLeft : R → P → Prop) [DecidableRel touchesLeft]
    (touchesRight : S → P → Prop) [DecidableRel touchesRight]
    (crossIncompatible : R → S → Prop) [DecidableRel crossIncompatible]
    (leftActivity : R → ℂ) (rightActivity : S → ℂ) (s s' : S) :
    (M.augmentTwoColorExclusiveRoots touchesLeft touchesRight crossIncompatible
      leftActivity rightActivity).incompatible
        (Sum.inr s) (Sum.inr s') := by
  trivial

@[simp]
theorem augmentTwoColorExclusiveRoots_incompatible_left_right
    {S : Type*} [Fintype S] [DecidableEq S]
    (M : FinitePolymerModel P)
    (touchesLeft : R → P → Prop) [DecidableRel touchesLeft]
    (touchesRight : S → P → Prop) [DecidableRel touchesRight]
    (crossIncompatible : R → S → Prop) [DecidableRel crossIncompatible]
    (leftActivity : R → ℂ) (rightActivity : S → ℂ) (r : R) (s : S) :
    (M.augmentTwoColorExclusiveRoots touchesLeft touchesRight crossIncompatible
      leftActivity rightActivity).incompatible
        (Sum.inl (Sum.inr r)) (Sum.inr s) ↔
      crossIncompatible r s := Iff.rfl

@[simp]
theorem augmentTwoColorExclusiveRoots_incompatible_left_bulk
    {S : Type*} [Fintype S] [DecidableEq S]
    (M : FinitePolymerModel P)
    (touchesLeft : R → P → Prop) [DecidableRel touchesLeft]
    (touchesRight : S → P → Prop) [DecidableRel touchesRight]
    (crossIncompatible : R → S → Prop) [DecidableRel crossIncompatible]
    (leftActivity : R → ℂ) (rightActivity : S → ℂ) (r : R) (gamma : P) :
    (M.augmentTwoColorExclusiveRoots touchesLeft touchesRight crossIncompatible
      leftActivity rightActivity).incompatible
        (Sum.inl (Sum.inr r)) (Sum.inl (Sum.inl gamma)) ↔
      touchesLeft r gamma := Iff.rfl

@[simp]
theorem augmentTwoColorExclusiveRoots_incompatible_right_bulk
    {S : Type*} [Fintype S] [DecidableEq S]
    (M : FinitePolymerModel P)
    (touchesLeft : R → P → Prop) [DecidableRel touchesLeft]
    (touchesRight : S → P → Prop) [DecidableRel touchesRight]
    (crossIncompatible : R → S → Prop) [DecidableRel crossIncompatible]
    (leftActivity : R → ℂ) (rightActivity : S → ℂ) (s : S) (gamma : P) :
    (M.augmentTwoColorExclusiveRoots touchesLeft touchesRight crossIncompatible
      leftActivity rightActivity).incompatible
        (Sum.inr s) (Sum.inl (Sum.inl gamma)) ↔
      touchesRight s gamma := Iff.rfl

/-- A bridge root touches an augmented one-sided polymer if it touches its
bulk support, and it touches every one-sided source root. -/
def bivariateBridgeTouches {S T : Type*}
    (touchesBridge : T → P → Prop) (t : T) : (P ⊕ R) ⊕ S → Prop
  | Sum.inl (Sum.inl gamma) => touchesBridge t gamma
  | Sum.inl (Sum.inr _) => True
  | Sum.inr _ => True

instance {S T : Type*} (touchesBridge : T → P → Prop)
    [DecidableRel touchesBridge] :
    DecidableRel (bivariateBridgeTouches (R := R) (S := S) touchesBridge) :=
  fun t x => by
    rcases x with (gamma | r) | s
    · exact inferInstanceAs (Decidable (touchesBridge t gamma))
    · exact isTrue trivial
    · exact isTrue trivial

/-- Adjoin left, right, and bridge source roots to a bulk gas.  First the two
one-sided exclusive colours are adjoined; then the bridge colour is adjoined
as an exclusive root which conflicts with every one-sided root.  This nested
construction lets the exact partition decomposition reuse the generic
exclusive-root theorem. -/
def augmentBivariateExclusiveRoots {S T : Type*}
    [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (M : FinitePolymerModel P)
    (touchesLeft : R → P → Prop) [DecidableRel touchesLeft]
    (touchesRight : S → P → Prop) [DecidableRel touchesRight]
    (touchesBridge : T → P → Prop) [DecidableRel touchesBridge]
    (crossIncompatible : R → S → Prop) [DecidableRel crossIncompatible]
    (leftActivity : R → ℂ) (rightActivity : S → ℂ)
    (bridgeActivity : T → ℂ) :
    FinitePolymerModel (((P ⊕ R) ⊕ S) ⊕ T) :=
  (M.augmentTwoColorExclusiveRoots touchesLeft touchesRight crossIncompatible
      leftActivity rightActivity).augmentExclusiveRoots
    (bivariateBridgeTouches touchesBridge) bridgeActivity

@[simp]
theorem augmentBivariateExclusiveRoots_incompatible_left_right
    {S T : Type*} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T]
    (M : FinitePolymerModel P)
    (touchesLeft : R → P → Prop) [DecidableRel touchesLeft]
    (touchesRight : S → P → Prop) [DecidableRel touchesRight]
    (touchesBridge : T → P → Prop) [DecidableRel touchesBridge]
    (crossIncompatible : R → S → Prop) [DecidableRel crossIncompatible]
    (leftActivity : R → ℂ) (rightActivity : S → ℂ)
    (bridgeActivity : T → ℂ) (r : R) (s : S) :
    (M.augmentBivariateExclusiveRoots touchesLeft touchesRight touchesBridge
      crossIncompatible leftActivity rightActivity bridgeActivity).incompatible
        (Sum.inl (Sum.inl (Sum.inr r)))
        (Sum.inl (Sum.inr s)) ↔ crossIncompatible r s := Iff.rfl

@[simp]
theorem augmentBivariateExclusiveRoots_incompatible_bridge_left
    {S T : Type*} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T]
    (M : FinitePolymerModel P)
    (touchesLeft : R → P → Prop) [DecidableRel touchesLeft]
    (touchesRight : S → P → Prop) [DecidableRel touchesRight]
    (touchesBridge : T → P → Prop) [DecidableRel touchesBridge]
    (crossIncompatible : R → S → Prop) [DecidableRel crossIncompatible]
    (leftActivity : R → ℂ) (rightActivity : S → ℂ)
    (bridgeActivity : T → ℂ) (t : T) (r : R) :
    (M.augmentBivariateExclusiveRoots touchesLeft touchesRight touchesBridge
      crossIncompatible leftActivity rightActivity bridgeActivity).incompatible
        (Sum.inr t) (Sum.inl (Sum.inl (Sum.inr r))) := by
  trivial

@[simp]
theorem augmentBivariateExclusiveRoots_incompatible_bridge_right
    {S T : Type*} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T]
    (M : FinitePolymerModel P)
    (touchesLeft : R → P → Prop) [DecidableRel touchesLeft]
    (touchesRight : S → P → Prop) [DecidableRel touchesRight]
    (touchesBridge : T → P → Prop) [DecidableRel touchesBridge]
    (crossIncompatible : R → S → Prop) [DecidableRel crossIncompatible]
    (leftActivity : R → ℂ) (rightActivity : S → ℂ)
    (bridgeActivity : T → ℂ) (t : T) (s : S) :
    (M.augmentBivariateExclusiveRoots touchesLeft touchesRight touchesBridge
      crossIncompatible leftActivity rightActivity bridgeActivity).incompatible
        (Sum.inr t) (Sum.inl (Sum.inr s)) := by
  trivial

@[simp]
theorem augmentBivariateExclusiveRoots_incompatible_bridge_bulk
    {S T : Type*} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T]
    (M : FinitePolymerModel P)
    (touchesLeft : R → P → Prop) [DecidableRel touchesLeft]
    (touchesRight : S → P → Prop) [DecidableRel touchesRight]
    (touchesBridge : T → P → Prop) [DecidableRel touchesBridge]
    (crossIncompatible : R → S → Prop) [DecidableRel crossIncompatible]
    (leftActivity : R → ℂ) (rightActivity : S → ℂ)
    (bridgeActivity : T → ℂ) (t : T) (gamma : P) :
    (M.augmentBivariateExclusiveRoots touchesLeft touchesRight touchesBridge
      crossIncompatible leftActivity rightActivity bridgeActivity).incompatible
        (Sum.inr t) (Sum.inl (Sum.inl (Sum.inl gamma))) ↔
      touchesBridge t gamma := Iff.rfl

@[simp]
theorem augmentExclusiveRoots_incompatible_root_root
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (r s : R) :
    (M.augmentExclusiveRoots touches rootActivity).incompatible
      (Sum.inr r) (Sum.inr s) := by
  trivial

@[simp]
theorem augmentExclusiveRoots_incompatible_root_bulk
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (r : R) (γ : P) :
    (M.augmentExclusiveRoots touches rootActivity).incompatible
      (Sum.inr r) (Sum.inl γ) ↔ touches r γ := Iff.rfl

@[simp]
theorem augmentExclusiveRoots_activity_root
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (r : R) :
    (M.augmentExclusiveRoots touches rootActivity).activity (Sum.inr r) =
      rootActivity r := rfl

@[simp]
theorem augmentExclusiveRoots_activity_bulk
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (γ : P) :
    (M.augmentExclusiveRoots touches rootActivity).activity (Sum.inl γ) =
      M.activity γ := rfl

/-! ## Exact partition function of an exclusive-root gas -/

/-- Admissible pairs consisting of one exclusive root and a compatible bulk
family which does not touch that root. -/
def exclusiveRootPairs (M : FinitePolymerModel P)
    (touches : R → P → Prop) [DecidableRel touches] :
    Finset (R × Finset P) :=
  Finset.univ.filter fun pair =>
    M.Compatible pair.2 ∧ ∀ γ ∈ pair.2, ¬touches pair.1 γ

/-- Total multiplicity of all exclusive-root values in a Mayer multi-index. -/
def exclusiveRootMultiplicity
    (X : MayerMultiIndex (AugmentedPolymer P R)) : ℕ :=
  ∑ r : R, X (Sum.inr r)

/-- Adjoining one occurrence of a specified exclusive root raises the total
exclusive-root multiplicity by one. -/
theorem exclusiveRootMultiplicity_add_single_root
    (X : MayerMultiIndex (AugmentedPolymer P R)) (r : R) :
    exclusiveRootMultiplicity (X + Finsupp.single (Sum.inr r) 1) =
      exclusiveRootMultiplicity X + 1 := by
  classical
  unfold exclusiveRootMultiplicity
  simp_rw [Finsupp.add_apply]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ s : R, (Finsupp.single (Sum.inr r) 1) (Sum.inr s)) =
        (Finsupp.single (Sum.inr r) 1) (Sum.inr r) := by
      apply Finset.sum_eq_single r
      · intro s _ hrs
        simp [Finsupp.single_apply, hrs.symm]
      · intro hr
        exact (hr (Finset.mem_univ r)).elim
    _ = 1 := by simp [Finsupp.single_apply]

/-- Total exclusive-root multiplicity zero means that every root coordinate
vanishes. -/
theorem exclusiveRootMultiplicity_eq_zero_apply
    {X : MayerMultiIndex (AugmentedPolymer P R)}
    (hX : exclusiveRootMultiplicity X = 0) (r : R) :
    X (Sum.inr r) = 0 := by
  unfold exclusiveRootMultiplicity at hX
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Nat.zero_le _)).mp hX r (Finset.mem_univ r)

/-- Multiplying every exclusive-root activity by one source variable records
the total root multiplicity in the activity monomial. -/
theorem mayerActivityMonomial_augmentExclusiveRoots_mul
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (α : ℂ)
    (X : MayerMultiIndex (AugmentedPolymer P R)) :
    (M.augmentExclusiveRoots touches (fun r => α * rootActivity r)).mayerActivityMonomial X =
      α ^ exclusiveRootMultiplicity X *
        (M.augmentExclusiveRoots touches rootActivity).mayerActivityMonomial X := by
  classical
  unfold mayerActivityMonomial exclusiveRootMultiplicity
  simp only [Fintype.prod_sum_type, augmentExclusiveRoots, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

/-- The same source law holds for normalized connected Mayer terms. -/
theorem mayerClusterTerm_augmentExclusiveRoots_mul
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (α : ℂ)
    (X : MayerMultiIndex (AugmentedPolymer P R)) :
    (M.augmentExclusiveRoots touches (fun r => α * rootActivity r)).mayerClusterTerm X =
      α ^ exclusiveRootMultiplicity X *
        (M.augmentExclusiveRoots touches rootActivity).mayerClusterTerm X := by
  unfold mayerClusterTerm
  rw [M.mayerActivityMonomial_augmentExclusiveRoots_mul touches rootActivity α X]
  change ((M.augmentExclusiveRoots touches rootActivity).mayerUrsell X : ℂ) /
      (mayerSymmetryFactor X : ℂ) *
        (α ^ exclusiveRootMultiplicity X *
          (M.augmentExclusiveRoots touches rootActivity).mayerActivityMonomial X) = _
  ring

/-- The finite degree sum selected by the coefficient linear in the common
exclusive-root source. -/
def exclusiveRootLinearMayerDegreeSum
    (M : FinitePolymerModel (AugmentedPolymer P R)) (n : ℕ) : ℂ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := AugmentedPolymer P R) n,
    if exclusiveRootMultiplicity X = 1 then M.mayerClusterTerm X else 0

/-- Absolute multiplicity-one connected coefficient at one fixed Mayer
degree.  Unlike the norm of `exclusiveRootLinearMayerDegreeSum`, this keeps
the individual cluster norms and therefore controls arbitrary localized
subfamilies before cancellation. -/
def exclusiveRootLinearNormMayerDegreeSum
    (M : FinitePolymerModel (AugmentedPolymer P R)) (n : ℕ) : ℝ :=
  ∑ X ∈ mayerMultiIndicesOfDegree (P := AugmentedPolymer P R) n,
    if exclusiveRootMultiplicity X = 1 then ‖M.mayerClusterTerm X‖ else 0

/-- Degree by degree, common source scaling is graded by total exclusive-root
multiplicity.  In particular `exclusiveRootLinearMayerDegreeSum` is exactly
the coefficient of the first source power in this displayed finite sum. -/
theorem symmetricMayerDegreeSum_augmentExclusiveRoots_mul
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (α : ℂ) (n : ℕ) :
    (M.augmentExclusiveRoots touches
        (fun r => α * rootActivity r)).symmetricMayerDegreeSum n =
      ∑ X ∈ mayerMultiIndicesOfDegree (P := AugmentedPolymer P R) n,
        α ^ exclusiveRootMultiplicity X *
          (M.augmentExclusiveRoots touches rootActivity).mayerClusterTerm X := by
  unfold symmetricMayerDegreeSum
  apply Finset.sum_congr rfl
  intro X _hX
  exact M.mayerClusterTerm_augmentExclusiveRoots_mul
    touches rootActivity α X

/-! ## Polynomial source grading and the pointed exponential formula -/

/-- Polynomial activity product of an augmented family: bulk activities are
constant and every root activity carries the common polynomial source. -/
def exclusiveRootSourceFamilyWeight
    (M : FinitePolymerModel P) (rootActivity : R → ℂ)
    (Γ : Finset (AugmentedPolymer P R)) : Polynomial ℂ :=
  ∏ x ∈ Γ, match x with
    | Sum.inl γ => Polynomial.C (M.activity γ)
    | Sum.inr r => Polynomial.X * Polynomial.C (rootActivity r)

/-- Evaluating the polynomial source recovers the corresponding scaled
exclusive-root family weight. -/
theorem eval_exclusiveRootSourceFamilyWeight
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ)
    (α : ℂ) (Γ : Finset (AugmentedPolymer P R)) :
    Polynomial.eval α (M.exclusiveRootSourceFamilyWeight rootActivity Γ) =
      (M.augmentExclusiveRoots touches
        (fun r => α * rootActivity r)).familyWeight Γ := by
  classical
  unfold exclusiveRootSourceFamilyWeight familyWeight
  change (Polynomial.evalRingHom α)
      (∏ x ∈ Γ, match x with
        | Sum.inl γ => Polynomial.C (M.activity γ)
        | Sum.inr r => Polynomial.X * Polynomial.C (rootActivity r)) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  rintro (x | r) _
  · change Polynomial.eval α (Polynomial.C (M.activity x)) = M.activity x
    simp
  · change Polynomial.eval α
      (Polynomial.X * Polynomial.C (rootActivity r)) = α * rootActivity r
    rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]

/-- The total-activity power series with the common exclusive-root source
kept as a polynomial coefficient variable. -/
def exclusiveRootSourcePartitionPowerSeries
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) :
    PowerSeries (Polynomial ℂ) :=
  let A := M.augmentExclusiveRoots touches rootActivity
  PowerSeries.mk fun n =>
    ∑ Γ ∈ (A.compatibleFamilies Finset.univ).filter
        (fun Γ => Γ.card = n),
      M.exclusiveRootSourceFamilyWeight rootActivity Γ

/-- The connected total-activity power series with the common root source
kept as a polynomial coefficient variable. -/
def exclusiveRootSourceMayerPowerSeries
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) :
    PowerSeries (Polynomial ℂ) :=
  PowerSeries.mk fun
    | 0 => 0
    | n + 1 =>
        ∑ X ∈ mayerMultiIndicesOfDegree
            (P := AugmentedPolymer P R) (n + 1),
          Polynomial.X ^ exclusiveRootMultiplicity X *
            Polynomial.C
              ((M.augmentExclusiveRoots touches rootActivity).mayerClusterTerm X)

@[simp]
theorem constantCoeff_exclusiveRootSourceMayerPowerSeries
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) :
    PowerSeries.constantCoeff
      (M.exclusiveRootSourceMayerPowerSeries touches rootActivity) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [exclusiveRootSourceMayerPowerSeries]

/-- Evaluating the polynomial source in the partition series gives the
ordinary complex partition power series of the scaled augmented model. -/
theorem map_exclusiveRootSourcePartitionPowerSeries_eval
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (α : ℂ) :
    (M.exclusiveRootSourcePartitionPowerSeries touches rootActivity).map
        (Polynomial.evalRingHom α) =
      (M.augmentExclusiveRoots touches
        (fun r => α * rootActivity r)).partitionPowerSeries Finset.univ := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map, coeff_partitionPowerSeries]
  simp only [exclusiveRootSourcePartitionPowerSeries,
    PowerSeries.coeff_mk]
  unfold partitionDegreeCoefficient
  simp only [map_sum]
  apply Finset.sum_congr
  · rfl
  · intro Γ _
    exact M.eval_exclusiveRootSourceFamilyWeight
      touches rootActivity α Γ

/-- Evaluating the polynomial source in the connected series gives the
ordinary symmetric Mayer power series of the scaled augmented model. -/
theorem map_exclusiveRootSourceMayerPowerSeries_eval
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (α : ℂ) :
    (M.exclusiveRootSourceMayerPowerSeries touches rootActivity).map
        (Polynomial.evalRingHom α) =
      (M.augmentExclusiveRoots touches
        (fun r => α * rootActivity r)).restrictedSymmetricMayerPowerSeries
          Finset.univ := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [exclusiveRootSourceMayerPowerSeries,
        restrictedSymmetricMayerPowerSeries,
        restrictedSymmetricMayerCoefficient]
  | succ n =>
      rw [PowerSeries.coeff_map]
      simp only [exclusiveRootSourceMayerPowerSeries,
        PowerSeries.coeff_mk]
      simp only [restrictedSymmetricMayerPowerSeries,
        PowerSeries.coeff_mk]
      simp only [map_sum, map_mul, map_pow,
        Polynomial.coe_evalRingHom, Polynomial.eval_X,
        Polynomial.eval_C]
      change (∑ x ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P R) (n + 1),
          α ^ exclusiveRootMultiplicity x *
            (M.augmentExclusiveRoots touches rootActivity).mayerClusterTerm x) =
        ∑ X ∈ (mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P R) (n + 1)).filter
            (fun X => X.support ⊆ Finset.univ),
          (M.augmentExclusiveRoots touches
            (fun r => α * rootActivity r)).mayerClusterTerm X
      rw [Finset.filter_eq_self.2]
      · apply Finset.sum_congr rfl
        intro X _
        rw [M.mayerClusterTerm_augmentExclusiveRoots_mul
          touches rootActivity α X]
      · intro X _
        exact Finset.subset_univ _

/-- The fixed-labelled exponential theorem holds before source extraction,
with the source retained as a genuine polynomial coefficient variable. -/
theorem expOf_exclusiveRootSourceMayerPowerSeries
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) :
    SourcePowerSeries.expOf
        (M.exclusiveRootSourceMayerPowerSeries touches rootActivity) =
      M.exclusiveRootSourcePartitionPowerSeries touches rootActivity := by
  apply PowerSeries.ext
  intro n
  apply Polynomial.funext
  intro α
  have hcomplex :
      PowerSeriesBridge.expOf
          ((M.augmentExclusiveRoots touches
            (fun r => α * rootActivity r)).restrictedSymmetricMayerPowerSeries
              Finset.univ) =
        (M.augmentExclusiveRoots touches
          (fun r => α * rootActivity r)).partitionPowerSeries Finset.univ := by
    rw [(M.augmentExclusiveRoots touches
      (fun r => α * rootActivity r)).restrictedSymmetricMayerPowerSeries_eq_formalMayerLog]
    exact (M.augmentExclusiveRoots touches
      (fun r => α * rootActivity r)).expOf_formalMayerLog_eq_partitionPowerSeries
        Finset.univ
  have hmapped :
      (SourcePowerSeries.expOf
          (M.exclusiveRootSourceMayerPowerSeries touches rootActivity)).map
            (Polynomial.evalRingHom α) =
        (M.exclusiveRootSourcePartitionPowerSeries touches rootActivity).map
          (Polynomial.evalRingHom α) := by
    rw [SourcePowerSeries.map_expOf_eval _
      (M.constantCoeff_exclusiveRootSourceMayerPowerSeries
        touches rootActivity) α,
      M.map_exclusiveRootSourceMayerPowerSeries_eval
        touches rootActivity α,
      M.map_exclusiveRootSourcePartitionPowerSeries_eval
        touches rootActivity α]
    exact hcomplex
  exact congrArg (PowerSeries.coeff n) hmapped

/-- Pointed labelled-set exponential formula: the source-linear partition
series is the zero-source partition series times the source-linear connected
Mayer series. -/
theorem linearCoefficient_exclusiveRootSourcePartitionPowerSeries
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) :
    SourcePowerSeries.linearCoefficient
        (M.exclusiveRootSourcePartitionPowerSeries touches rootActivity) =
      SourcePowerSeries.constantSource
          (M.exclusiveRootSourcePartitionPowerSeries touches rootActivity) *
        SourcePowerSeries.linearCoefficient
          (M.exclusiveRootSourceMayerPowerSeries touches rootActivity) := by
  rw [← M.expOf_exclusiveRootSourceMayerPowerSeries
    touches rootActivity]
  exact SourcePowerSeries.linearCoefficient_expOf
    (M.constantCoeff_exclusiveRootSourceMayerPowerSeries
      touches rootActivity)

/-- Source-linear extraction of the connected polynomial series is exactly
the multiplicity-one symmetric Mayer degree sum. -/
theorem coeff_linearCoefficient_exclusiveRootSourceMayerPowerSeries
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (n : ℕ) :
    PowerSeries.coeff n
        (SourcePowerSeries.linearCoefficient
          (M.exclusiveRootSourceMayerPowerSeries touches rootActivity)) =
      (M.augmentExclusiveRoots touches rootActivity).exclusiveRootLinearMayerDegreeSum n := by
  rw [SourcePowerSeries.coeff_linearCoefficient]
  cases n with
  | zero =>
      unfold exclusiveRootLinearMayerDegreeSum
      simp only [exclusiveRootSourceMayerPowerSeries,
        PowerSeries.coeff_mk, Polynomial.coeff_zero]
      symm
      apply Finset.sum_eq_zero
      intro X hX
      have hdegree : mayerDegree X = 0 :=
        (mem_mayerMultiIndicesOfDegree 0 X).mp hX
      have hx : ∀ x : AugmentedPolymer P R, X x = 0 := by
        intro x
        unfold mayerDegree at hdegree
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => Nat.zero_le _)).mp hdegree x (Finset.mem_univ x)
      have hm : exclusiveRootMultiplicity X = 0 := by
        unfold exclusiveRootMultiplicity
        simp [hx]
      simp [hm]
  | succ n =>
      simp only [exclusiveRootSourceMayerPowerSeries,
        PowerSeries.coeff_mk]
      unfold exclusiveRootLinearMayerDegreeSum
      rw [Polynomial.finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro X _
      by_cases hm : exclusiveRootMultiplicity X = 1
      · rw [hm, Polynomial.coeff_mul_C]
        simp
      · have hcoeff :
            ((Polynomial.X : Polynomial ℂ) ^
              exclusiveRootMultiplicity X).coeff 1 = 0 := by
          have hm' : 1 ≠ exclusiveRootMultiplicity X := fun h => hm h.symm
          simp [Polynomial.coeff_X_pow, hm']
        rw [Polynomial.coeff_mul_C]
        rw [if_neg hm]
        exact (congrArg
          (fun z : ℂ => z *
            (M.augmentExclusiveRoots touches rootActivity).mayerClusterTerm X)
          hcoeff).trans (zero_mul _)

/-! ## The multiplicity-one sector and residual rooted trees -/

/-- After a unique exclusive root of value `r` is distinguished, its
degree-`n+1` pinned tree contribution is bounded by its activity norm times
the zero-source residual rooted-tree orbit of degree `n`.  The zero source is
essential: it deletes every residual term containing another root. -/
theorem exclusiveRoot_linearPinnedMayerTreeDegreeSum_le
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (r : R) (n : ℕ) :
    (∑ X ∈ mayerMultiIndicesOfDegree (P := AugmentedPolymer P R) (n + 1),
        if exclusiveRootMultiplicity X = 1 then
          (X (Sum.inr r) : ℝ) *
            (M.augmentExclusiveRoots touches rootActivity).mayerTreeMajorant X
        else 0) ≤
      ‖rootActivity r‖ *
        (M.augmentExclusiveRoots touches (fun _ => 0)).residualSymmetricPinnedTreeDegreeSum
          (Sum.inr r) n := by
  classical
  let A₁ := M.augmentExclusiveRoots touches rootActivity
  let A₀ := M.augmentExclusiveRoots touches (fun _ => 0)
  let root : AugmentedPolymer P R := Sum.inr r
  let source :=
    (mayerMultiIndicesOfDegree (P := AugmentedPolymer P R) n).filter
      (fun Y => exclusiveRootMultiplicity Y = 0)
  let target :=
    (mayerMultiIndicesOfDegree (P := AugmentedPolymer P R) (n + 1)).filter
      (fun X => exclusiveRootMultiplicity X = 1 ∧ X root ≠ 0)
  let residualTerm (Y : MayerMultiIndex (AugmentedPolymer P R)) : ℝ :=
    (((graphSpanningTrees (A₀.mayerIncompatibilityGraph
      (Y + Finsupp.single root 1))).card : ℝ) *
      ∏ child : AugmentedPolymer P R, ‖A₀.activity child‖ ^ Y child) /
        (mayerSymmetryFactor Y : ℝ)
  have hsourceSubset : source ⊆
      mayerMultiIndicesOfDegree (P := AugmentedPolymer P R) n :=
    Finset.filter_subset _ _
  have hreindex :
      (∑ Y ∈ source,
          (((Y + Finsupp.single root 1 :
              MayerMultiIndex (AugmentedPolymer P R)) root : ℕ) : ℝ) *
            A₁.mayerTreeMajorant (Y + Finsupp.single root 1)) =
        ∑ X ∈ target, (X root : ℝ) * A₁.mayerTreeMajorant X := by
    apply Finset.sum_bij
        (fun Y (_hY : Y ∈ source) => Y + Finsupp.single root 1)
    · intro Y hY
      have hdata := Finset.mem_filter.mp hY
      apply Finset.mem_filter.mpr
      refine ⟨(mem_mayerMultiIndicesOfDegree (n + 1) _).mpr ?_, ?_, by simp [root]⟩
      · rw [mayerDegree_add_single]
        exact congrArg (fun k => k + 1)
          ((mem_mayerMultiIndicesOfDegree n Y).mp hdata.1)
      · simpa [root, hdata.2] using
          exclusiveRootMultiplicity_add_single_root Y r
    · intro Y₁ _ Y₂ _ h
      exact add_right_cancel h
    · intro X hX
      have hdata := Finset.mem_filter.mp hX
      let Y := eraseRootOccurrence X root
      have hback : Y + Finsupp.single root 1 = X :=
        eraseRootOccurrence_add_single_eq X root hdata.2.2
      have hdegree := (mem_mayerMultiIndicesOfDegree (n + 1) X).mp hdata.1
      have hzero : exclusiveRootMultiplicity Y = 0 := by
        have hm := congrArg exclusiveRootMultiplicity hback
        rw [exclusiveRootMultiplicity_add_single_root] at hm
        rw [hdata.2.1] at hm
        omega
      refine ⟨Y, Finset.mem_filter.mpr
        ⟨(mem_mayerMultiIndicesOfDegree n Y).mpr
          (mayerDegree_eraseRootOccurrence X root n hdegree hdata.2.2), hzero⟩, hback⟩
    · intro Y _
      rfl
  have hrestrict :
      (∑ X ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P R) (n + 1),
          if exclusiveRootMultiplicity X = 1 then
            (X root : ℝ) * A₁.mayerTreeMajorant X else 0) =
        ∑ X ∈ target, (X root : ℝ) * A₁.mayerTreeMajorant X := by
    dsimp [target]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro X _
    by_cases hm : exclusiveRootMultiplicity X = 1
    · by_cases hr : X root ≠ 0
      · simp [hm, hr]
      · have hrzero : X root = 0 := not_ne_iff.mp hr
        simp [hm, hr, hrzero]
    · simp [hm]
  have hresidual (Y : MayerMultiIndex (AugmentedPolymer P R))
      (hYzero : exclusiveRootMultiplicity Y = 0) :
      ((((graphSpanningTrees (A₁.mayerIncompatibilityGraph
          (Y + Finsupp.single root 1))).card : ℝ) *
          ∏ child : AugmentedPolymer P R, ‖A₁.activity child‖ ^ Y child) /
            (mayerSymmetryFactor Y : ℝ)) = residualTerm Y := by
    have hactivity :
        (∏ child : AugmentedPolymer P R, ‖A₁.activity child‖ ^ Y child) =
          ∏ child : AugmentedPolymer P R, ‖A₀.activity child‖ ^ Y child := by
      apply Finset.prod_congr rfl
      rintro (child | s) _
      · rfl
      · simp [A₁, A₀, augmentExclusiveRoots,
          exclusiveRootMultiplicity_eq_zero_apply hYzero s]
    unfold residualTerm
    rw [hactivity]
    rfl
  have hterm (Y : MayerMultiIndex (AugmentedPolymer P R))
      (hY : Y ∈ source) :
      (((Y + Finsupp.single root 1 :
          MayerMultiIndex (AugmentedPolymer P R)) root : ℕ) : ℝ) *
          A₁.mayerTreeMajorant (Y + Finsupp.single root 1) =
        ‖rootActivity r‖ * residualTerm Y := by
    have hdata := Finset.mem_filter.mp hY
    have hrootIdentity :=
      A₁.root_mul_residualTreeTerm_eq_pinned_mayerTreeMajorant Y root
    have hrootActivity : ‖A₁.activity root‖ = ‖rootActivity r‖ := by
      rfl
    rw [hrootActivity, hresidual Y hdata.2] at hrootIdentity
    exact hrootIdentity.symm
  have hnonneg (Y : MayerMultiIndex (AugmentedPolymer P R)) :
      0 ≤ residualTerm Y := by
    unfold residualTerm
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (Finset.prod_nonneg fun child _ => pow_nonneg (norm_nonneg _) _))
      (Nat.cast_nonneg _)
  rw [show Sum.inr r = root by rfl]
  rw [hrestrict, ← hreindex]
  calc
    (∑ Y ∈ source,
        (((Y + Finsupp.single root 1 :
            MayerMultiIndex (AugmentedPolymer P R)) root : ℕ) : ℝ) *
          A₁.mayerTreeMajorant (Y + Finsupp.single root 1)) =
        ∑ Y ∈ source, ‖rootActivity r‖ * residualTerm Y := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = ‖rootActivity r‖ * ∑ Y ∈ source, residualTerm Y := by
      rw [Finset.mul_sum]
    _ ≤ ‖rootActivity r‖ *
        ∑ Y ∈ mayerMultiIndicesOfDegree
          (P := AugmentedPolymer P R) n, residualTerm Y := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsourceSubset
        (fun Y _ _ => hnonneg Y)
    _ = ‖rootActivity r‖ *
        A₀.residualSymmetricPinnedTreeDegreeSum root n := by
      rfl

/-- The norm of the total multiplicity-one connected coefficient is bounded
degree by degree by the sum of zero-source residual rooted-tree orbits, one
for each possible exclusive-root value. -/
theorem norm_exclusiveRootLinearMayerDegreeSum_succ_le
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (n : ℕ) :
    ‖(M.augmentExclusiveRoots touches rootActivity).exclusiveRootLinearMayerDegreeSum
        (n + 1)‖ ≤
      ∑ r : R, ‖rootActivity r‖ *
        (M.augmentExclusiveRoots touches (fun _ => 0)).residualSymmetricPinnedTreeDegreeSum
          (Sum.inr r) n := by
  classical
  let A := M.augmentExclusiveRoots touches rootActivity
  let degree := mayerMultiIndicesOfDegree (P := AugmentedPolymer P R) (n + 1)
  unfold exclusiveRootLinearMayerDegreeSum
  calc
    ‖∑ X ∈ degree,
        if exclusiveRootMultiplicity X = 1 then A.mayerClusterTerm X else 0‖ ≤
      ∑ X ∈ degree,
        ‖if exclusiveRootMultiplicity X = 1 then A.mayerClusterTerm X else 0‖ :=
      norm_sum_le degree _
    _ ≤ ∑ X ∈ degree,
        if exclusiveRootMultiplicity X = 1 then A.mayerTreeMajorant X else 0 := by
      apply Finset.sum_le_sum
      intro X _
      by_cases hm : exclusiveRootMultiplicity X = 1
      · simp only [hm, if_true]
        exact A.norm_mayerClusterTerm_le_mayerTreeMajorant X
      · simp [hm]
    _ = ∑ r : R, ∑ X ∈ degree,
        if exclusiveRootMultiplicity X = 1 then
          (X (Sum.inr r) : ℝ) * A.mayerTreeMajorant X else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro X _
      by_cases hm : exclusiveRootMultiplicity X = 1
      · simp only [hm, if_true]
        rw [← Finset.sum_mul]
        have hcast : (∑ r : R, (X (Sum.inr r) : ℝ)) = 1 := by
          exact_mod_cast hm
        rw [hcast, one_mul]
      · simp [hm]
    _ ≤ ∑ r : R, ‖rootActivity r‖ *
        (M.augmentExclusiveRoots touches (fun _ => 0)).residualSymmetricPinnedTreeDegreeSum
          (Sum.inr r) n := by
      exact Finset.sum_le_sum fun r _ =>
        M.exclusiveRoot_linearPinnedMayerTreeDegreeSum_le
          touches rootActivity r n

/-- The absolute multiplicity-one coefficient is bounded degree by degree by
the same zero-source residual rooted-tree orbit.  This is the form needed to
bound a selected spatial tail of one-root clusters. -/
theorem exclusiveRootLinearNormMayerDegreeSum_succ_le
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (n : ℕ) :
    (M.augmentExclusiveRoots touches rootActivity).exclusiveRootLinearNormMayerDegreeSum
        (n + 1) ≤
      ∑ r : R, ‖rootActivity r‖ *
        (M.augmentExclusiveRoots touches (fun _ => 0)).residualSymmetricPinnedTreeDegreeSum
          (Sum.inr r) n := by
  classical
  let A := M.augmentExclusiveRoots touches rootActivity
  let degree := mayerMultiIndicesOfDegree (P := AugmentedPolymer P R) (n + 1)
  unfold exclusiveRootLinearNormMayerDegreeSum
  calc
    (∑ X ∈ degree,
        if exclusiveRootMultiplicity X = 1 then ‖A.mayerClusterTerm X‖ else 0) ≤
      ∑ X ∈ degree,
        if exclusiveRootMultiplicity X = 1 then A.mayerTreeMajorant X else 0 := by
      apply Finset.sum_le_sum
      intro X _
      by_cases hm : exclusiveRootMultiplicity X = 1
      · simp only [hm, if_true]
        exact A.norm_mayerClusterTerm_le_mayerTreeMajorant X
      · simp [hm]
    _ = ∑ r : R, ∑ X ∈ degree,
        if exclusiveRootMultiplicity X = 1 then
          (X (Sum.inr r) : ℝ) * A.mayerTreeMajorant X else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro X _
      by_cases hm : exclusiveRootMultiplicity X = 1
      · simp only [hm, if_true]
        rw [← Finset.sum_mul]
        have hcast : (∑ r : R, (X (Sum.inr r) : ℝ)) = 1 := by
          exact_mod_cast hm
        rw [hcast, one_mul]
      · simp [hm]
    _ ≤ ∑ r : R, ‖rootActivity r‖ *
        (M.augmentExclusiveRoots touches (fun _ => 0)).residualSymmetricPinnedTreeDegreeSum
          (Sum.inr r) n := by
      exact Finset.sum_le_sum fun r _ =>
        M.exclusiveRoot_linearPinnedMayerTreeDegreeSum_le
          touches rootActivity r n

/-- Compatibility of a split augmented family is exactly bulk compatibility,
at most one exclusive root, and absence of root--bulk contacts. -/
theorem augmentExclusiveRoots_compatible_disjSum_iff
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ)
    (Gamma : Finset P) (Delta : Finset R) :
    (M.augmentExclusiveRoots touches rootActivity).Compatible
        (Gamma.disjSum Delta) ↔
      M.Compatible Gamma ∧ Delta.card ≤ 1 ∧
        ∀ r ∈ Delta, ∀ gamma ∈ Gamma, ¬touches r gamma := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro gamma hgamma delta hdelta hne
      have hx : (Sum.inl gamma : P ⊕ R) ∈ Gamma.disjSum Delta := by
        exact Finset.inl_mem_disjSum.mpr hgamma
      have hy : (Sum.inl delta : P ⊕ R) ∈ Gamma.disjSum Delta := by
        exact Finset.inl_mem_disjSum.mpr hdelta
      have hxy : (Sum.inl gamma : P ⊕ R) ≠ Sum.inl delta := by
        simpa using hne
      exact h hx hy hxy
    · rw [Finset.card_le_one]
      intro r hr s hs
      by_contra hrs
      have hx : (Sum.inr r : P ⊕ R) ∈ Gamma.disjSum Delta :=
        Finset.inr_mem_disjSum.mpr hr
      have hy : (Sum.inr s : P ⊕ R) ∈ Gamma.disjSum Delta :=
        Finset.inr_mem_disjSum.mpr hs
      have hxy : (Sum.inr r : P ⊕ R) ≠ Sum.inr s := by simpa using hrs
      have hnot := h hx hy hxy
      exact hnot trivial
    · intro r hr gamma hgamma
      have hx : (Sum.inr r : P ⊕ R) ∈ Gamma.disjSum Delta :=
        Finset.inr_mem_disjSum.mpr hr
      have hy : (Sum.inl gamma : P ⊕ R) ∈ Gamma.disjSum Delta := by
        exact Finset.inl_mem_disjSum.mpr hgamma
      have hxy : (Sum.inr r : P ⊕ R) ≠ Sum.inl gamma := by simp
      exact h hx hy hxy
  · rintro ⟨hGamma, hDelta, htouch⟩
    intro x hx y hy hxy
    rcases x with gamma | r <;> rcases y with delta | s
    · exact hGamma (by simpa using hx) (by simpa using hy)
        (by simpa using hxy)
    · exact htouch s (by simpa using hy) gamma (by simpa using hx)
    · exact htouch r (by simpa using hx) delta (by simpa using hy)
    · have hrs : r = s :=
        (Finset.card_le_one.mp hDelta) r (by simpa using hx) s (by simpa using hy)
      exact (hxy (by simpa using hrs)).elim

/-- Activities factor over the bulk and root parts of an augmented family. -/
theorem augmentExclusiveRoots_familyWeight_disjSum
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ)
    (Gamma : Finset P) (Delta : Finset R) :
    (M.augmentExclusiveRoots touches rootActivity).familyWeight
        (Gamma.disjSum Delta) =
      M.familyWeight Gamma * ∏ r ∈ Delta, rootActivity r := by
  simp [familyWeight, Finset.prod_disjSum, augmentExclusiveRoots]

/-- The partition function of an exclusive-root augmentation is affine in
the root activities.  Its constant term is the bulk partition function, and
its root term is indexed by a unique root together with an allowed compatible
bulk family. -/
theorem augmentExclusiveRoots_partitionFunction
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) :
    (M.augmentExclusiveRoots touches rootActivity).partitionFunction =
      M.partitionFunction +
        ∑ pair ∈ M.exclusiveRootPairs touches,
          rootActivity pair.1 * M.familyWeight pair.2 := by
  classical
  let A := M.augmentExclusiveRoots touches rootActivity
  let bulkFamilies : Finset (Finset (P ⊕ R)) :=
    (M.compatibleFamilies Finset.univ).image fun Gamma =>
      Gamma.disjSum ∅
  let rootedFamilies : Finset (Finset (P ⊕ R)) :=
    (M.exclusiveRootPairs touches).image fun pair =>
      pair.2.disjSum {pair.1}
  have hfamilies : A.compatibleFamilies Finset.univ =
      bulkFamilies ∪ rootedFamilies := by
    ext Xi
    constructor
    · intro hXi
      have hcompatible : A.Compatible Xi :=
        (Finset.mem_filter.mp hXi).2
      have hsplit : A.Compatible (Xi.toLeft.disjSum Xi.toRight) := by
        simpa only [Finset.toLeft_disjSum_toRight] using hcompatible
      rcases (M.augmentExclusiveRoots_compatible_disjSum_iff touches
        rootActivity Xi.toLeft Xi.toRight).mp hsplit with
        ⟨hbulk, hcard, htouch⟩
      by_cases hempty : Xi.toRight = ∅
      · apply Finset.mem_union_left rootedFamilies
        apply Finset.mem_image.mpr
        refine ⟨Xi.toLeft, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
            (Finset.subset_univ _), hbulk⟩
        · simpa only [hempty] using
            (Finset.toLeft_disjSum_toRight (u := Xi))
      · obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have hsingleton : Xi.toRight = {r} :=
          Finset.eq_singleton_iff_unique_mem.mpr
            ⟨hr, fun s hs => (Finset.card_le_one.mp hcard) s hs r hr⟩
        apply Finset.mem_union_right bulkFamilies
        apply Finset.mem_image.mpr
        refine ⟨(r, Xi.toLeft), ?_, ?_⟩
        · rw [exclusiveRootPairs, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hbulk,
            fun gamma hgamma => htouch r hr gamma hgamma⟩
        · simpa only [hsingleton] using
            (Finset.toLeft_disjSum_toRight (u := Xi))
    · intro hXi
      rcases Finset.mem_union.mp hXi with hbulk | hroot
      · rcases Finset.mem_image.mp hbulk with ⟨Gamma, hGamma, rfl⟩
        have hGammaCompatible := (Finset.mem_filter.mp hGamma).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
        exact (M.augmentExclusiveRoots_compatible_disjSum_iff touches
          rootActivity Gamma ∅).mpr ⟨hGammaCompatible, by simp, by simp⟩
      · rcases Finset.mem_image.mp hroot with ⟨pair, hpair, rfl⟩
        have hpairData := (Finset.mem_filter.mp hpair).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
        apply (M.augmentExclusiveRoots_compatible_disjSum_iff touches
          rootActivity pair.2 {pair.1}).mpr
        exact ⟨hpairData.1, by simp,
          fun r hr gamma hgamma => by
            have hr' : r = pair.1 := by simpa using hr
            subst r
            exact hpairData.2 gamma hgamma⟩
  have hdisjoint : Disjoint bulkFamilies rootedFamilies := by
    rw [Finset.disjoint_left]
    intro Xi hbulk hroot
    rcases Finset.mem_image.mp hbulk with ⟨Gamma, _hGamma, hGammaXi⟩
    rcases Finset.mem_image.mp hroot with ⟨pair, _hpair, hpairXi⟩
    have heq : Gamma.disjSum (∅ : Finset R) =
        pair.2.disjSum {pair.1} := hGammaXi.trans hpairXi.symm
    have hright := (Finset.disjSum_inj.mp heq).2
    simpa using hright
  have hbulkSum :
      ∑ Xi ∈ bulkFamilies, A.familyWeight Xi = M.partitionFunction := by
    unfold bulkFamilies
    rw [Finset.sum_image]
    · unfold FinitePolymerModel.partitionFunction
      apply Finset.sum_congr rfl
      intro Gamma _hGamma
      have hweight := M.augmentExclusiveRoots_familyWeight_disjSum
        touches rootActivity Gamma (∅ : Finset R)
      simpa [A] using hweight
    · intro Gamma _hGamma Delta _hDelta heq
      exact (Finset.disjSum_inj.mp heq).1
  have hrootSum :
      ∑ Xi ∈ rootedFamilies, A.familyWeight Xi =
        ∑ pair ∈ M.exclusiveRootPairs touches,
          rootActivity pair.1 * M.familyWeight pair.2 := by
    unfold rootedFamilies
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro pair _hpair
      simp [A, M.augmentExclusiveRoots_familyWeight_disjSum, mul_comm]
    · intro pair _hpair other _hother heq
      have hparts := Finset.disjSum_inj.mp heq
      apply Prod.ext
      · simpa using hparts.2
      · exact hparts.1
  change A.partitionOn Finset.univ =
    M.partitionFunction +
      ∑ pair ∈ M.exclusiveRootPairs touches,
        rootActivity pair.1 * M.familyWeight pair.2
  unfold FinitePolymerModel.partitionOn
  rw [hfamilies, Finset.sum_union hdisjoint, hbulkSum, hrootSum]

/-! ## Summing the pointed exponential formula at unit total activity -/

/-- Coefficient of the common root source in the exclusive-root partition
function. -/
def exclusiveRootPartitionCoefficient
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) : ℂ :=
  ∑ pair ∈ M.exclusiveRootPairs touches,
    rootActivity pair.1 * M.familyWeight pair.2

/-- The polynomial-source partition series is supported in the same finite
total-activity range as the augmented hard-core gas. -/
theorem coeff_exclusiveRootSourcePartitionPowerSeries_eq_zero_of_card_lt
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) {n : ℕ}
    (hcard : (Finset.univ : Finset (AugmentedPolymer P R)).card < n) :
    PowerSeries.coeff n
        (M.exclusiveRootSourcePartitionPowerSeries touches rootActivity) = 0 := by
  apply Polynomial.funext
  intro α
  have hmapped := congrArg (PowerSeries.coeff n)
    (M.map_exclusiveRootSourcePartitionPowerSeries_eval
      touches rootActivity α)
  calc
    Polynomial.eval α
        (PowerSeries.coeff n
          (M.exclusiveRootSourcePartitionPowerSeries touches rootActivity)) =
      PowerSeries.coeff n
        ((M.augmentExclusiveRoots touches
          (fun r => α * rootActivity r)).partitionPowerSeries Finset.univ) := by
      simpa only [PowerSeries.coeff_map,
        Polynomial.coe_evalRingHom] using hmapped
    _ = 0 := by
      rw [coeff_partitionPowerSeries]
      exact (M.augmentExclusiveRoots touches
        (fun r => α * rootActivity r)).partitionDegreeCoefficient_eq_zero_of_card_lt
          Finset.univ hcard
    _ = Polynomial.eval α 0 := by simp

/-- Summing every total-activity coefficient while retaining the polynomial
source gives the affine exclusive-root partition polynomial. -/
theorem sum_coeff_exclusiveRootSourcePartitionPowerSeries
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) :
    (∑ n ∈ Finset.range
        ((Finset.univ : Finset (AugmentedPolymer P R)).card + 1),
      PowerSeries.coeff n
        (M.exclusiveRootSourcePartitionPowerSeries touches rootActivity)) =
      Polynomial.C M.partitionFunction +
        Polynomial.X * Polynomial.C
          (M.exclusiveRootPartitionCoefficient touches rootActivity) := by
  apply Polynomial.funext
  intro α
  calc
    Polynomial.eval α
        (∑ n ∈ Finset.range
            ((Finset.univ : Finset (AugmentedPolymer P R)).card + 1),
          PowerSeries.coeff n
            (M.exclusiveRootSourcePartitionPowerSeries touches rootActivity)) =
      ∑ n ∈ Finset.range
          ((Finset.univ : Finset (AugmentedPolymer P R)).card + 1),
        PowerSeries.coeff n
          ((M.augmentExclusiveRoots touches
            (fun r => α * rootActivity r)).partitionPowerSeries Finset.univ) := by
      change (Polynomial.evalRingHom α)
          (∑ n ∈ Finset.range
              ((Finset.univ : Finset (AugmentedPolymer P R)).card + 1),
            PowerSeries.coeff n
              (M.exclusiveRootSourcePartitionPowerSeries touches rootActivity)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n _
      have hmapped := congrArg (PowerSeries.coeff n)
        (M.map_exclusiveRootSourcePartitionPowerSeries_eval
          touches rootActivity α)
      simpa only [PowerSeries.coeff_map] using hmapped
    _ = (M.augmentExclusiveRoots touches
          (fun r => α * rootActivity r)).partitionFunction := by
      simpa only [coeff_partitionPowerSeries] using
        (M.augmentExclusiveRoots touches
          (fun r => α * rootActivity r)).sum_partitionDegreeCoefficient_range
            Finset.univ
    _ = M.partitionFunction +
        α * M.exclusiveRootPartitionCoefficient touches rootActivity := by
      rw [M.augmentExclusiveRoots_partitionFunction]
      unfold exclusiveRootPartitionCoefficient
      rw [Finset.mul_sum]
      apply congrArg (fun z : ℂ => M.partitionFunction + z)
      apply Finset.sum_congr rfl
      intro pair _
      ring
    _ = Polynomial.eval α
        (Polynomial.C M.partitionFunction +
          Polynomial.X * Polynomial.C
            (M.exclusiveRootPartitionCoefficient touches rootActivity)) := by
      simp only [Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X]

/-- The finite sum of the source-linear partition coefficients is the exact
exclusive-root coefficient. -/
theorem sum_coeff_linearCoefficient_exclusiveRootSourcePartitionPowerSeries
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) :
    (∑ n ∈ Finset.range
        ((Finset.univ : Finset (AugmentedPolymer P R)).card + 1),
      PowerSeries.coeff n
        (SourcePowerSeries.linearCoefficient
          (M.exclusiveRootSourcePartitionPowerSeries touches rootActivity))) =
      M.exclusiveRootPartitionCoefficient touches rootActivity := by
  simp_rw [SourcePowerSeries.coeff_linearCoefficient]
  rw [← Polynomial.finsetSum_coeff,
    M.sum_coeff_exclusiveRootSourcePartitionPowerSeries
      touches rootActivity]
  rw [Polynomial.coeff_add, Polynomial.coeff_C_of_ne_zero one_ne_zero,
    Polynomial.coeff_X_mul, Polynomial.coeff_C_zero, zero_add]

/-- The finite sum of the zero-source partition coefficients is the bulk
partition function. -/
theorem sum_coeff_constantSource_exclusiveRootSourcePartitionPowerSeries
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) :
    (∑ n ∈ Finset.range
        ((Finset.univ : Finset (AugmentedPolymer P R)).card + 1),
      PowerSeries.coeff n
        (SourcePowerSeries.constantSource
          (M.exclusiveRootSourcePartitionPowerSeries touches rootActivity))) =
      M.partitionFunction := by
  unfold SourcePowerSeries.constantSource
  simp_rw [PowerSeries.coeff_map]
  change (∑ n ∈ Finset.range
      ((Finset.univ : Finset (AugmentedPolymer P R)).card + 1),
    (Polynomial.evalRingHom 0)
      (PowerSeries.coeff n
        (M.exclusiveRootSourcePartitionPowerSeries touches rootActivity))) = _
  rw [← map_sum]
  change Polynomial.eval 0
      (∑ n ∈ Finset.range
        ((Finset.univ : Finset (AugmentedPolymer P R)).card + 1),
        PowerSeries.coeff n
          (M.exclusiveRootSourcePartitionPowerSeries touches rootActivity)) = _
  rw [← Polynomial.coeff_zero_eq_eval_zero,
    M.sum_coeff_exclusiveRootSourcePartitionPowerSeries
      touches rootActivity]
  rw [Polynomial.coeff_add, Polynomial.coeff_C_zero,
    Polynomial.coeff_X_mul_zero, add_zero]

/-- After absolute convergence of the multiplicity-one connected sector is
known, the pointed exponential formula can be evaluated at unit total
activity.  The exact root coefficient is the bulk partition function times
the full connected one-root Mayer sum. -/
theorem exclusiveRootPartitionCoefficient_eq_partitionFunction_mul_tsum
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ)
    (hsummable : Summable (fun n : ℕ =>
      ‖(M.augmentExclusiveRoots touches rootActivity).exclusiveRootLinearMayerDegreeSum
        (n + 1)‖)) :
    M.exclusiveRootPartitionCoefficient touches rootActivity =
      M.partitionFunction *
        ∑' n : ℕ,
          (M.augmentExclusiveRoots touches rootActivity).exclusiveRootLinearMayerDegreeSum n := by
  let sourcePartition :=
    M.exclusiveRootSourcePartitionPowerSeries touches rootActivity
  let sourceConnected :=
    M.exclusiveRootSourceMayerPowerSeries touches rootActivity
  let B : ℕ → ℂ := fun n => PowerSeries.coeff n
    (SourcePowerSeries.constantSource sourcePartition)
  let C : ℕ → ℂ := fun n => PowerSeries.coeff n
    (SourcePowerSeries.linearCoefficient sourceConnected)
  let Rlin : ℕ → ℂ := fun n => PowerSeries.coeff n
    (SourcePowerSeries.linearCoefficient sourcePartition)
  let cutoff := (Finset.univ : Finset (AugmentedPolymer P R)).card + 1
  have hsourceZero {n : ℕ} (hn : n ∉ Finset.range cutoff) :
      PowerSeries.coeff n sourcePartition = 0 := by
    apply M.coeff_exclusiveRootSourcePartitionPowerSeries_eq_zero_of_card_lt
      touches rootActivity
    exact Nat.lt_of_not_ge fun hle => hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
  have hBzero {n : ℕ} (hn : n ∉ Finset.range cutoff) : B n = 0 := by
    unfold B SourcePowerSeries.constantSource
    rw [PowerSeries.coeff_map, hsourceZero hn, map_zero]
  have hRzero {n : ℕ} (hn : n ∉ Finset.range cutoff) : Rlin n = 0 := by
    unfold Rlin
    rw [SourcePowerSeries.coeff_linearCoefficient, hsourceZero hn]
    simp
  have hBnorm : Summable (fun n => ‖B n‖) :=
    summable_of_ne_finset_zero (s := Finset.range cutoff) fun n hn => by
      rw [hBzero hn, norm_zero]
  have hCnorm : Summable (fun n => ‖C n‖) := by
    have htail : Summable (fun n => ‖C (n + 1)‖) := by
      apply hsummable.congr
      intro n
      unfold C sourceConnected
      rw [M.coeff_linearCoefficient_exclusiveRootSourceMayerPowerSeries
        touches rootActivity]
    exact (summable_nat_add_iff (f := fun n => ‖C n‖) 1).mp htail
  have hBsum : HasSum B M.partitionFunction := by
    have hfinite : HasSum B (∑ n ∈ Finset.range cutoff, B n) :=
      hasSum_sum_of_ne_finset_zero
        (s := Finset.range cutoff) (fun n hn => hBzero hn)
    rw [show ∑ n ∈ Finset.range cutoff, B n = M.partitionFunction by
      simpa only [B, sourcePartition, cutoff] using
        M.sum_coeff_constantSource_exclusiveRootSourcePartitionPowerSeries
          touches rootActivity] at hfinite
    exact hfinite
  have hRsum : HasSum Rlin
      (M.exclusiveRootPartitionCoefficient touches rootActivity) := by
    have hfinite : HasSum Rlin (∑ n ∈ Finset.range cutoff, Rlin n) :=
      hasSum_sum_of_ne_finset_zero
        (s := Finset.range cutoff) (fun n hn => hRzero hn)
    rw [show ∑ n ∈ Finset.range cutoff, Rlin n =
        M.exclusiveRootPartitionCoefficient touches rootActivity by
      simpa only [Rlin, sourcePartition, cutoff] using
        M.sum_coeff_linearCoefficient_exclusiveRootSourcePartitionPowerSeries
          touches rootActivity] at hfinite
    exact hfinite
  have hpoint :
      SourcePowerSeries.linearCoefficient sourcePartition =
        SourcePowerSeries.constantSource sourcePartition *
          SourcePowerSeries.linearCoefficient sourceConnected := by
    exact M.linearCoefficient_exclusiveRootSourcePartitionPowerSeries
      touches rootActivity
  have hproduct :
      (∑' n, B n) * (∑' n, C n) = ∑' n, Rlin n := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      hBnorm hCnorm]
    apply tsum_congr
    intro n
    have hcoeff := congrArg (PowerSeries.coeff n) hpoint
    simpa only [B, C, Rlin, PowerSeries.coeff_mul] using hcoeff.symm
  calc
    M.exclusiveRootPartitionCoefficient touches rootActivity =
        ∑' n, Rlin n := hRsum.tsum_eq.symm
    _ = (∑' n, B n) * (∑' n, C n) := hproduct.symm
    _ = M.partitionFunction * (∑' n, C n) := by rw [hBsum.tsum_eq]
    _ = M.partitionFunction *
        ∑' n : ℕ,
          (M.augmentExclusiveRoots touches rootActivity).exclusiveRootLinearMayerDegreeSum n := by
      congr 1
      apply tsum_congr
      intro n
      exact M.coeff_linearCoefficient_exclusiveRootSourceMayerPowerSeries
        touches rootActivity n

@[simp]
theorem augmentRoots_incompatible_bulk_bulk
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (γ δ : P) :
    (M.augmentRoots touches rootActivity).incompatible (Sum.inl γ) (Sum.inl δ) ↔
      M.incompatible γ δ := Iff.rfl

@[simp]
theorem augmentRoots_incompatible_root_bulk
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (r : R) (γ : P) :
    (M.augmentRoots touches rootActivity).incompatible (Sum.inr r) (Sum.inl γ) ↔
      touches r γ := Iff.rfl

@[simp]
theorem augmentRoots_incompatible_bulk_root
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (γ : P) (r : R) :
    (M.augmentRoots touches rootActivity).incompatible (Sum.inl γ) (Sum.inr r) ↔
      touches r γ := Iff.rfl

@[simp]
theorem augmentRoots_incompatible_root_root
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (r s : R) :
    (M.augmentRoots touches rootActivity).incompatible (Sum.inr r) (Sum.inr s) ↔
      r = s := Iff.rfl

@[simp]
theorem augmentRoots_activity_bulk
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (γ : P) :
    (M.augmentRoots touches rootActivity).activity (Sum.inl γ) = M.activity γ := rfl

@[simp]
theorem augmentRoots_activity_root
    (M : FinitePolymerModel P) (touches : R → P → Prop)
    [DecidableRel touches] (rootActivity : R → ℂ) (r : R) :
    (M.augmentRoots touches rootActivity).activity (Sum.inr r) = rootActivity r := rfl

/-! ## Lifting the genuine KP certificate at zero source -/

/-- KP weight on the augmented type.  Bulk polymers retain their old weight;
a source root receives exactly the tilted mass of the bulk polymers it
touches. -/
def augmentRootKPWeight (M : FinitePolymerModel P)
    (touches : R → P → Prop) [DecidableRel touches]
    (a : P → ℝ) : AugmentedPolymer P R → ℝ
  | Sum.inl γ => a γ
  | Sum.inr r =>
      ∑ γ : P, if touches r γ then
        ‖M.activity γ‖ * Real.exp (a γ) else 0

theorem augmentRootKPWeight_nonneg
    (M : FinitePolymerModel P)
    (touches : R → P → Prop) [DecidableRel touches]
    (a : P → ℝ) (ha : ∀ γ, 0 ≤ a γ) :
    ∀ x, 0 ≤ M.augmentRootKPWeight touches a x := by
  rintro (x | r)
  · exact ha x
  · exact Finset.sum_nonneg fun γ _ => by
      split_ifs
      · exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      · exact le_rfl

/-- A full-volume KP certificate lifts to finitely many zero-activity source
roots.  Bulk inequalities are unchanged because source activities vanish;
the source inequality is an equality by the definition of
`augmentRootKPWeight`. -/
theorem koteckyPreissCertificate_augmentRoots_zero
    (M : FinitePolymerModel P)
    (touches : R → P → Prop) [DecidableRel touches]
    (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    (M.augmentRoots touches (fun _ => 0)).KoteckyPreissCertificate
      Finset.univ (M.augmentRootKPWeight touches a) := by
  classical
  refine ⟨M.augmentRootKPWeight_nonneg touches a hKP.1, ?_⟩
  rintro (x | r) _hx
  · rw [Finset.sum_filter]
    rw [Fintype.sum_sum_type]
    have hbase := hKP.2 x (Finset.mem_univ x)
    rw [Finset.sum_filter] at hbase
    simpa [augmentRootKPWeight] using hbase
  · rw [Finset.sum_filter]
    rw [Fintype.sum_sum_type]
    simp [augmentRootKPWeight]

/-- A KP certificate also lifts to mutually exclusive zero-activity roots.
Root exclusivity changes only root--root incompatibilities, whose summands
vanish at the zero-source expansion point. -/
theorem koteckyPreissCertificate_augmentExclusiveRoots_zero
    (M : FinitePolymerModel P)
    (touches : R → P → Prop) [DecidableRel touches]
    (a : P → ℝ)
    (hKP : M.KoteckyPreissCertificate Finset.univ a) :
    (M.augmentExclusiveRoots touches (fun _ => 0)).KoteckyPreissCertificate
      Finset.univ (M.augmentRootKPWeight touches a) := by
  classical
  refine ⟨M.augmentRootKPWeight_nonneg touches a hKP.1, ?_⟩
  rintro (x | r) _hx
  · rw [Finset.sum_filter]
    rw [Fintype.sum_sum_type]
    have hbase := hKP.2 x (Finset.mem_univ x)
    rw [Finset.sum_filter] at hbase
    simpa [augmentExclusiveRoots, augmentRootKPWeight] using hbase
  · rw [Finset.sum_filter]
    rw [Fintype.sum_sum_type]
    simp [augmentExclusiveRoots, augmentRootKPWeight]

end FinitePolymerModel

end

end YangMills.Polymer
