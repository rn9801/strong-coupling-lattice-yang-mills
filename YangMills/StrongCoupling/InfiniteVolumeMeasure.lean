/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.ClusterState
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Infinite-volume probability represented by a weak cluster point

This is the compactness route allowed by Milestone 12.  Every finite Gibbs law
has already been pushed to the compact full configuration space.  Compactness
of its probability-measure space supplies a weak cluster point.  The one-root
cluster-expansion tail then forces every local observable to have the same
limit along the full sequence, so the cluster point represents the local
state and is independent of the chosen cluster point.

No Dobrushin or Douglas module is imported here.
-/

open Filter MeasureTheory

namespace YangMills.StrongCoupling

open Gauge Lattice.Cubic

noncomputable section

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [GaugeHaarProbability G]

/-! ## Density of local real continuous functions -/

/-- Real continuous cylinder functions: the function is required to depend on
some finite set of positive edges, but that set is not part of the bundled
data.  This is the real Stone--Weierstrass algebra used to prove uniqueness of
the representing measure. -/
def localRealContinuousSubalgebra :
    Subalgebra ℝ C(Configuration d G, ℝ) where
  carrier := {f | ∃ S : Finset (PositiveEdge d),
    DependsOn f (S : Set (PositiveEdge d))}
  zero_mem' := ⟨∅, fun _ _ _ => rfl⟩
  one_mem' := ⟨∅, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨S, hf⟩ ⟨T, hg⟩
    refine ⟨S ∪ T, fun A B hAB => ?_⟩
    change f A + g A = f B + g B
    rw [hf (fun e he => hAB e (Finset.mem_union_left T he)),
      hg (fun e he => hAB e (Finset.mem_union_right S he))]
  mul_mem' := by
    rintro f g ⟨S, hf⟩ ⟨T, hg⟩
    refine ⟨S ∪ T, fun A B hAB => ?_⟩
    change f A * g A = f B * g B
    rw [hf (fun e he => hAB e (Finset.mem_union_left T he)),
      hg (fun e he => hAB e (Finset.mem_union_right S he))]
  algebraMap_mem' := fun _ => ⟨∅, fun _ _ _ => rfl⟩

/-- Cylinder functions separate full configurations: a differing edge is
detected by a real continuous function on the compact Hausdorff gauge group. -/
theorem localRealContinuousSubalgebra_separatesPoints :
    (localRealContinuousSubalgebra (d := d) (G := G)).SeparatesPoints := by
  intro A B hAB
  have hedge : ∃ e : PositiveEdge d, A e ≠ B e := by
    by_contra h
    push Not at h
    exact hAB (funext h)
  obtain ⟨e, he⟩ := hedge
  obtain ⟨f, hfcont, hfne⟩ :=
    (separatesPoints_continuous_of_t35Space (X := G)) he
  let g : C(Configuration d G, ℝ) :=
    ⟨fun C => f (C e), hfcont.comp (continuous_apply e)⟩
  refine ⟨g, ?_, hfne⟩
  refine ⟨g, ⟨?_, rfl⟩⟩
  refine ⟨{e}, fun C D hCD => ?_⟩
  exact congrArg f (hCD e (by simp))

/-- Every real continuous function on the compact full configuration space is
uniformly approximable by a finite-edge cylinder function. -/
theorem exists_localRealContinuous_near
    (f : C(Configuration d G, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : localRealContinuousSubalgebra (d := d) (G := G),
      ‖(g : C(Configuration d G, ℝ)) - f‖ < ε :=
  ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (localRealContinuousSubalgebra (d := d) (G := G))
    localRealContinuousSubalgebra_separatesPoints f ε hε

/-- Regard a member of the real cylinder algebra as a complex local
observable, retaining one finite support witnessing its locality. -/
def localObservableOfLocalReal
    (g : localRealContinuousSubalgebra (d := d) (G := G)) :
    LocalObservable d G where
  toContinuousMap :=
    ⟨fun A => (g.1 A : ℂ), Complex.continuous_ofReal.comp g.1.continuous⟩
  support := Classical.choose g.2
  dependsOn_support := by
    intro A B hAB
    exact congrArg (fun x : ℝ => (x : ℂ))
      (Classical.choose_spec g.2 hAB)

@[simp]
theorem localObservableOfLocalReal_apply
    (g : localRealContinuousSubalgebra (d := d) (G := G))
    (A : Configuration d G) :
    localObservableOfLocalReal g A = (g.1 A : ℂ) :=
  rfl

/-- Finite Borel measures on the full configuration space are determined by
their integrals on local continuous observables.  The proof is the missing
Milestone 12 density step: real cylinder functions are Stone--Weierstrass
dense, and uniform approximation controls integrals of finite measures. -/
theorem measure_eq_of_integral_localObservable_eq
    (μ ν : Measure (Configuration d G))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hlocal : ∀ F : LocalObservable d G,
      ∫ A, F A ∂μ = ∫ A, F A ∂ν) :
    μ = ν := by
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  apply eq_of_forall_dist_le
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨g, hgf⟩ := exists_localRealContinuous_near
    (d := d) (G := G) f.toContinuousMap hhalf
  let gb : BoundedContinuousFunction (Configuration d G) ℝ :=
    BoundedContinuousFunction.mkOfCompact g.1
  have hfg : ∀ A : Configuration d G, ‖f A - g.1 A‖ ≤ ε / 2 := by
    intro A
    have hpoint := (ContinuousMap.norm_lt_iff
      (f := (g : C(Configuration d G, ℝ)) - f.toContinuousMap) hhalf).mp hgf A
    have hneg : ‖f A - g.1 A‖ = ‖g.1 A - f A‖ := by
      rw [← norm_neg]
      congr 1
      ring
    rw [hneg]
    exact hpoint.le
  have hfμ : Integrable f μ := f.integrable μ
  have hfν : Integrable f ν := f.integrable ν
  have hgμ : Integrable gb μ := gb.integrable μ
  have hgν : Integrable gb ν := gb.integrable ν
  have hgμ' : Integrable (fun A => g.1 A) μ := by simpa [gb] using hgμ
  have hgν' : Integrable (fun A => g.1 A) ν := by simpa [gb] using hgν
  have hμ : dist (∫ A, f A ∂μ) (∫ A, g.1 A ∂μ) ≤ ε / 2 := by
    rw [dist_eq_norm, ← MeasureTheory.integral_sub hfμ hgμ']
    simpa [gb] using
      (MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
        (ae_of_all μ hfg))
  have hν : dist (∫ A, g.1 A ∂ν) (∫ A, f A ∂ν) ≤ ε / 2 := by
    rw [dist_comm, dist_eq_norm, ← MeasureTheory.integral_sub hfν hgν']
    simpa [gb] using
      (MeasureTheory.norm_integral_le_of_norm_le_const (μ := ν)
        (ae_of_all ν hfg))
  have hg : (∫ A, g.1 A ∂μ) = ∫ A, g.1 A ∂ν := by
    have hc := hlocal (localObservableOfLocalReal g)
    simp only [localObservableOfLocalReal_apply] at hc
    simpa only [integral_complex_ofReal, Complex.ofReal_inj] using hc
  calc
    dist (∫ A, f A ∂μ) (∫ A, f A ∂ν) ≤
        dist (∫ A, f A ∂μ) (∫ A, g.1 A ∂μ) +
          dist (∫ A, g.1 A ∂μ) (∫ A, f A ∂ν) :=
      dist_triangle _ _ _
    _ = dist (∫ A, f A ∂μ) (∫ A, g.1 A ∂μ) +
          dist (∫ A, g.1 A ∂ν) (∫ A, f A ∂ν) := by rw [hg]
    _ ≤ ε / 2 + ε / 2 := add_le_add hμ hν
    _ = ε := by ring

namespace ClusterLimitCertificate

variable {measure : ℕ → ProbabilityMeasure (Configuration d G)}

/-- The local expectation is continuous for the weak topology on probability
measures. -/
theorem continuous_localExpectation (F : LocalObservable d G) :
    Continuous (fun μ : ProbabilityMeasure (Configuration d G) =>
      localExpectation μ F) := by
  rw [continuous_iff_continuousAt]
  intro μ
  unfold ContinuousAt
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
    tendsto_id F.toBoundedContinuousMap

/-- A weak cluster point of the full-space finite-volume Gibbs laws. -/
def infiniteVolumeProbability (C : ClusterLimitCertificate measure) :
    ProbabilityMeasure (Configuration d G) := by
  let h := isCompact_univ.exists_mapClusterPt
    (f := atTop) (u := measure) (by simp)
  exact Classical.choose h

/-- The selected probability is indeed a weak cluster point. -/
theorem infiniteVolumeProbability_isClusterPoint
    (C : ClusterLimitCertificate measure) :
    MapClusterPt C.infiniteVolumeProbability atTop measure := by
  unfold infiniteVolumeProbability
  exact (Classical.choose_spec (isCompact_univ.exists_mapClusterPt
    (f := atTop) (u := measure) (by simp))).2

/-- The weak cluster point represents every local cluster-state expectation. -/
theorem localExpectation_infiniteVolumeProbability
    (C : ClusterLimitCertificate measure) (F : LocalObservable d G) :
    localExpectation C.infiniteVolumeProbability F = C.localState F := by
  let u : ℕ → ℂ := fun n => localExpectation (measure n) F
  have hcluster : MapClusterPt
      (localExpectation C.infiniteVolumeProbability F) atTop u := by
    exact (C.infiniteVolumeProbability_isClusterPoint.continuousAt_comp
      (continuous_localExpectation F).continuousAt)
  apply eq_of_nhds_neBot
  have hc : NeBot
      (nhds (localExpectation C.infiniteVolumeProbability F) ⊓ map u atTop) :=
    hcluster
  have hle :
      nhds (localExpectation C.infiniteVolumeProbability F) ⊓ map u atTop ≤
        nhds (localExpectation C.infiniteVolumeProbability F) ⊓
          nhds (C.localState F) :=
    inf_le_inf_left _ (C.tendsto_localState F)
  exact NeBot.mono hc hle

/-- The represented infinite-volume Borel measure. -/
def infiniteVolumeMeasure (C : ClusterLimitCertificate measure) :
    Measure (Configuration d G) :=
  C.infiniteVolumeProbability

instance infiniteVolumeMeasure_isProbability
    (C : ClusterLimitCertificate measure) :
    IsProbabilityMeasure C.infiniteVolumeMeasure :=
  C.infiniteVolumeProbability.property

/-- Integrals against the infinite-volume measure agree with the cluster
state on all local continuous observables. -/
theorem integral_infiniteVolumeMeasure
    (C : ClusterLimitCertificate measure) (F : LocalObservable d G) :
    ∫ A, F A ∂C.infiniteVolumeMeasure = C.localState F :=
  C.localExpectation_infiniteVolumeProbability F

/-- The representing Borel probability is unique.  Agreement on the local
state first gives agreement on every local continuous observable; the
Stone--Weierstrass density theorem above then determines the measure. -/
theorem infiniteVolumeMeasure_unique
    (C : ClusterLimitCertificate measure)
    (μ : Measure (Configuration d G)) [IsProbabilityMeasure μ]
    (hμ : ∀ F : LocalObservable d G,
      ∫ A, F A ∂μ = C.localState F) :
    μ = C.infiniteVolumeMeasure := by
  apply measure_eq_of_integral_localObservable_eq
  intro F
  rw [hμ F, C.integral_infiniteVolumeMeasure F]

/-- Positivity of the represented state on the real part of a pointwise
nonnegative local observable. -/
theorem localState_re_nonneg
    (C : ClusterLimitCertificate measure) (F : LocalObservable d G)
    (hF : ∀ A, 0 ≤ (F A).re) :
    0 ≤ (C.localState F).re := by
  rw [← C.integral_infiniteVolumeMeasure F]
  have hInt : Integrable F C.infiniteVolumeMeasure := by
    simpa [infiniteVolumeMeasure] using
      integrable_localObservable C.infiniteVolumeProbability F
  change 0 ≤ RCLike.re (∫ A, F A ∂C.infiniteVolumeMeasure)
  rw [← integral_re hInt]
  exact integral_nonneg hF

/-- A real-valued local observable has a real cluster-state expectation. -/
theorem localState_im_eq_zero
    (C : ClusterLimitCertificate measure) (F : LocalObservable d G)
    (hF : ∀ A, (F A).im = 0) :
    (C.localState F).im = 0 := by
  rw [← C.integral_infiniteVolumeMeasure F]
  have hInt : Integrable F C.infiniteVolumeMeasure := by
    simpa [infiniteVolumeMeasure] using
      integrable_localObservable C.infiniteVolumeProbability F
  change RCLike.im (∫ A, F A ∂C.infiniteVolumeMeasure) = 0
  rw [← integral_im hInt]
  simpa using integral_congr_ae (ae_of_all C.infiniteVolumeMeasure hF)

end ClusterLimitCertificate

end

end YangMills.StrongCoupling
