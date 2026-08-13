import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Locally uniform analytic limits

This file packages the analytic limit argument used by the cluster expansion.
The substantive input remains the rooted-cluster estimate: pointwise convergence
and a uniform Cauchy estimate on every compact subset of the convergence disk.
The package below turns those estimates into an analytic limiting function.
-/

open Filter Metric Set
open scoped Topology

namespace YangMills

/-- A certificate that a sequence of analytic functions has a locally uniformly
convergent limit on an open set.  The two Cauchy hypotheses are deliberately
separated: cluster estimates normally prove the compact-uniform estimate, while
coefficient stabilization identifies the pointwise limit. -/
structure LocallyUniformAnalyticLimitCertificate
    (f : ℕ → ℂ → ℂ) (domain : Set ℂ) where
  isOpen_domain : IsOpen domain
  analytic_sequence : ∀ n, AnalyticOnNhd ℂ (f n) domain
  pointwise_cauchy : ∀ z ∈ domain, CauchySeq (fun n ↦ f n z)
  uniform_cauchy_on_compact :
    ∀ K : Set ℂ, K ⊆ domain → IsCompact K → UniformCauchySeqOn f atTop K

namespace LocallyUniformAnalyticLimitCertificate

variable {f : ℕ → ℂ → ℂ} {domain : Set ℂ}

/-- The limiting function selected by completeness of `ℂ`. -/
noncomputable def limit
    (h : LocallyUniformAnalyticLimitCertificate f domain) (z : ℂ) : ℂ :=
  limUnder atTop (fun n ↦ f n z)

theorem tendsto_limit (h : LocallyUniformAnalyticLimitCertificate f domain)
    {z : ℂ} (hz : z ∈ domain) :
    Tendsto (fun n ↦ f n z) atTop (nhds (h.limit z)) :=
  (h.pointwise_cauchy z hz).tendsto_limUnder

theorem tendstoLocallyUniformlyOn_limit
    (h : LocallyUniformAnalyticLimitCertificate f domain) :
    TendstoLocallyUniformlyOn f h.limit atTop domain := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact h.isOpen_domain]
  intro K hK hKcompact
  exact (h.uniform_cauchy_on_compact K hK hKcompact).tendstoUniformlyOn_of_tendsto
    (fun z hz ↦ h.tendsto_limit (hK hz))

theorem analyticOnNhd_limit
    (h : LocallyUniformAnalyticLimitCertificate f domain) :
    AnalyticOnNhd ℂ h.limit domain :=
  (h.tendstoLocallyUniformlyOn_limit.differentiableOn
      (Eventually.of_forall fun n ↦ (h.analytic_sequence n).differentiableOn)
      h.isOpen_domain).analyticOnNhd h.isOpen_domain

end LocallyUniformAnalyticLimitCertificate

/-! ## Vitali convergence on a complex disk

The pinned Mathlib revision has the Weierstrass theorem for an already locally
uniform limit, but not the normal-family/Vitali theorem which produces that
limit from local boundedness and convergence on a real interval.  The short
package below fills exactly that gap.  Cauchy's derivative estimate makes each
closed-disk restriction equicontinuous, Arzelà--Ascoli makes its closure
compact, and the analytic identity theorem makes every cluster point unique.
-/

namespace VitaliOnDisk

noncomputable section

/-- Restriction of a continuous function to a compact closed disk. -/
def restriction (f : ℂ → ℂ) (r : ℝ)
    (hf : ContinuousOn f (closedBall 0 r)) :
    BoundedContinuousFunction (closedBall (0 : ℂ) r) ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z ↦ f z.1, hf.restrict⟩

/-- A closed-disk function, extended by zero only so that Mathlib's locally
uniform convergence API can regard it as a function on `ℂ`.  All uses below
are inside the disk. -/
def extension (r : ℝ)
    (g : BoundedContinuousFunction (closedBall (0 : ℂ) r) ℂ)
    (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ closedBall (0 : ℂ) r then g ⟨z, hz⟩ else 0

@[simp]
theorem extension_apply {r : ℝ}
    (g : BoundedContinuousFunction (closedBall (0 : ℂ) r) ℂ) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) r) :
    extension r g z = g ⟨z, hz⟩ := by
  simp [extension, hz]

theorem tendstoUniformlyOn_extension_of_tendsto_restriction
    {f : ℕ → ℂ → ℂ} {r : ℝ}
    (hf : ∀ n, ContinuousOn (f n) (closedBall 0 r))
    {g : BoundedContinuousFunction (closedBall (0 : ℂ) r) ℂ}
    (h : Tendsto (fun n ↦ restriction (f n) r (hf n)) atTop (nhds g)) :
    TendstoUniformlyOn f (extension r g) atTop (closedBall 0 r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h ε hε
  filter_upwards [eventually_atTop.2 ⟨N, fun n hn ↦ hn⟩] with n hn z hz
  rw [extension_apply g hz]
  exact lt_of_le_of_lt
    (BoundedContinuousFunction.dist_coe_le_dist
      (f := g) (g := restriction (f n) r (hf n)) ⟨z, hz⟩)
    (by simpa [dist_comm] using hN n hn)

theorem analyticOnNhd_extension_of_tendsto_restriction
    {f : ℕ → ℂ → ℂ} {R r : ℝ} (hrR : r < R)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (ball 0 R))
    {g : BoundedContinuousFunction (closedBall (0 : ℂ) r) ℂ}
    (h : Tendsto (fun n ↦ restriction (f n) r
      ((hf n).continuousOn.mono (closedBall_subset_ball hrR))) atTop (nhds g)) :
    AnalyticOnNhd ℂ (extension r g) (ball 0 r) := by
  have hu := tendstoUniformlyOn_extension_of_tendsto_restriction
    (fun n ↦ (hf n).continuousOn.mono (closedBall_subset_ball hrR)) h
  exact (hu.tendstoLocallyUniformlyOn.mono ball_subset_closedBall).differentiableOn
    (Eventually.of_forall fun n ↦
      (hf n).differentiableOn.mono (ball_subset_ball hrR.le))
    isOpen_ball |>.analyticOnNhd isOpen_ball

theorem exists_uniform_limit_closedBall
    {f : ℕ → ℂ → ℂ} {R : ℝ}
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (ball 0 R))
    (hbounded : ∀ r, 0 ≤ r → r < R → ∃ C, 0 ≤ C ∧
      ∀ n z, z ∈ closedBall (0 : ℂ) r → ‖f n z‖ ≤ C)
    (g : ℝ → ℂ)
    (hreal : ∀ x : ℝ, |x| < R →
      Tendsto (fun n ↦ f n (x : ℂ)) atTop (nhds (g x)))
    {r : ℝ} (hr0 : 0 < r) (hrR : r < R) :
    ∃ u : BoundedContinuousFunction (closedBall (0 : ℂ) r) ℂ,
      Tendsto (fun n ↦ restriction (f n) r
        ((hf n).continuousOn.mono (closedBall_subset_ball hrR)))
        atTop (nhds u) := by
  let s : ℝ := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  have hs0 : 0 ≤ s := le_trans hr0.le hrs.le
  obtain ⟨C, hC0, hC⟩ := hbounded s hs0 hsR
  let K : Set ℂ := closedBall 0 r
  let seq : ℕ → BoundedContinuousFunction K ℂ := fun n ↦ restriction (f n) r
    ((hf n).continuousOn.mono (closedBall_subset_ball hrR))
  have hderiv (n : ℕ) (z : ℂ) (hz : z ∈ K) :
      ‖deriv (f n) z‖ ≤ C / (s - r) := by
    have hdelta : 0 < s - r := sub_pos.mpr hrs
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hdelta
    · apply DifferentiableOn.diffContOnCl
      exact (hf n).differentiableOn.mono (by
        intro w hw
        have hw' := closure_ball_subset_closedBall hw
        rw [mem_closedBall] at hw' hz
        rw [mem_ball]
        calc
          dist w 0 ≤ dist w z + dist z 0 := dist_triangle _ _ _
          _ ≤ (s - r) + r := add_le_add hw' hz
          _ = s := sub_add_cancel s r
          _ < R := hsR)
    · intro w hw
      apply hC n w
      rw [mem_closedBall] at hz ⊢
      rw [mem_sphere] at hw
      calc
        dist w 0 ≤ dist w z + dist z 0 := dist_triangle _ _ _
        _ ≤ (s - r) + r := add_le_add hw.le hz
        _ = s := sub_add_cancel s r
  have hdiff (n : ℕ) (z : ℂ) (hz : z ∈ K) : DifferentiableAt ℂ (f n) z := by
    exact (hf n).differentiableOn.differentiableAt
      (isOpen_ball.mem_nhds (closedBall_subset_ball hrR hz))
  let L : NNReal := ⟨C / (s - r), div_nonneg hC0 (sub_nonneg.mpr hrs.le)⟩
  have hlip (n : ℕ) : LipschitzWith L (seq n) := by
    apply (convex_closedBall (0 : ℂ) r).lipschitzOnWith_of_nnnorm_deriv_le
      (fun z hz ↦ hdiff n z hz)
      (fun z hz ↦ by
        exact_mod_cast hderiv n z hz) |>.to_restrict
  have hequi : Equicontinuous ((↑) : Set.range seq → K → ℂ) := by
    apply (LipschitzWith.uniformEquicontinuous
      (fun v : Set.range seq ↦ fun z ↦ v.1 z) L ?_).equicontinuous
    rintro ⟨v, n, rfl⟩
    exact hlip n
  have hin (v : BoundedContinuousFunction K ℂ) (z : K) (hv : v ∈ Set.range seq) :
      v z ∈ closedBall (0 : ℂ) C := by
    obtain ⟨n, rfl⟩ := hv
    rw [mem_closedBall, dist_zero_right]
    change ‖f n z.1‖ ≤ C
    apply hC n z.1
    exact closedBall_subset_closedBall hrs.le z.2
  have hcompact : IsCompact (closure (Set.range seq)) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) C)
      (isCompact_closedBall 0 C) (Set.range seq) hin hequi
  obtain ⟨uLim, _huLimMem, ψ, hψmono, hψ⟩ := hcompact.tendsto_subseq
    (fun n ↦ subset_closure (show seq n ∈ Set.range seq from ⟨n, rfl⟩))
  refine ⟨uLim, hcompact.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n ↦
      subset_closure (show seq n ∈ Set.range seq from ⟨n, rfl⟩)) ?_⟩
  intro v _hv hcluster
  obtain ⟨φ, hφmono, hφ⟩ := hcluster.tendsto_subseq
  have hvAnalytic : AnalyticOnNhd ℂ (extension r v) (ball 0 r) := by
    apply analyticOnNhd_extension_of_tendsto_restriction hrR
      (fun n ↦ hf (φ n))
    simpa [Function.comp_def, seq] using hφ
  have huLimAnalytic : AnalyticOnNhd ℂ (extension r uLim) (ball 0 r) := by
    apply analyticOnNhd_extension_of_tendsto_restriction hrR
      (fun n ↦ hf (ψ n))
    simpa [Function.comp_def, seq] using hψ
  have hreal_v (x : ℝ) (hx : |x| < r) :
      extension r v (x : ℂ) = g x := by
    have hxK : (x : ℂ) ∈ closedBall (0 : ℂ) r := by
      rw [mem_closedBall, dist_zero_right, Complex.norm_real]
      exact hx.le
    have hsub := (hreal x (lt_trans hx hrR)).comp hφmono.tendsto_atTop
    have heval := (BoundedContinuousFunction.lipschitz_eval_const
      ⟨(x : ℂ), hxK⟩).continuous.continuousAt.tendsto.comp hφ
    rw [extension_apply v hxK]
    apply tendsto_nhds_unique heval
    simpa [Function.comp_def, seq, restriction] using hsub
  have hreal_uLim (x : ℝ) (hx : |x| < r) :
      extension r uLim (x : ℂ) = g x := by
    have hxK : (x : ℂ) ∈ closedBall (0 : ℂ) r := by
      rw [mem_closedBall, dist_zero_right, Complex.norm_real]
      exact hx.le
    have hsub := (hreal x (lt_trans hx hrR)).comp hψmono.tendsto_atTop
    have heval := (BoundedContinuousFunction.lipschitz_eval_const
      ⟨(x : ℂ), hxK⟩).continuous.continuousAt.tendsto.comp hψ
    rw [extension_apply uLim hxK]
    apply tendsto_nhds_unique heval
    simpa [Function.comp_def, seq, restriction] using hsub
  apply BoundedContinuousFunction.ext
  intro z
  have heqOn : Set.EqOn (extension r v) (extension r uLim) (ball 0 r) := by
    apply hvAnalytic.eqOn_of_preconnected_of_mem_closure huLimAnalytic
      isPreconnected_ball (mem_ball_self hr0)
    let a : ℕ → ℝ := fun n ↦ (r / 2) * (1 / ((n + 1 : ℕ) : ℝ))
    have ha0 : Tendsto a atTop (nhds 0) := by
      simpa [a] using (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (nhds 0)))
    have hac : Tendsto (fun n ↦ (a n : ℂ)) atTop (nhds 0) := by
      simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp ha0
    apply mem_closure_of_tendsto hac
    filter_upwards [] with n
    have ha_pos : 0 < a n := by
      dsimp [a]
      positivity
    have ha_lt : |a n| < r := by
      rw [abs_of_pos ha_pos]
      calc
        a n ≤ r / 2 := by
          dsimp [a]
          have hone : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 :=
            (div_le_one (by positivity)).mpr (by norm_num)
          simpa using mul_le_mul_of_nonneg_left hone
            (div_nonneg hr0.le (by norm_num))
        _ < r := by linarith
    constructor
    · change extension r v (a n : ℂ) = extension r uLim (a n : ℂ)
      rw [hreal_v (a n) ha_lt, hreal_uLim (a n) ha_lt]
    · simpa using ha_pos.ne'
  have hzclosed : (z : ℂ) ∈ closedBall 0 r := z.2
  have hzlim : Tendsto (fun n : ℕ ↦ ((1 - 1 / ((n + 1 : ℕ) : ℝ)) : ℝ) •
      (z : ℂ)) atTop (nhds (z : ℂ)) := by
    have hone : Tendsto (fun n : ℕ ↦ (1 : ℝ) - 1 / ((n + 1 : ℕ) : ℝ))
        atTop (nhds 1) := by
      convert ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat :
            Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (nhds 0))) using 1
      · ext n
        simp only [Nat.cast_add, Nat.cast_one]
      · simp
    simpa using hone.smul_const (z : ℂ)
  have hinside (n : ℕ) :
      ((1 - 1 / ((n + 1 : ℕ) : ℝ)) : ℝ) • (z : ℂ) ∈ ball 0 r := by
    rw [mem_ball, dist_zero_right, norm_smul]
    have hfac0 : 0 ≤ (1 : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
      apply sub_nonneg.mpr
      exact (div_le_one (by positivity)).mpr (by norm_num)
    rw [Real.norm_eq_abs, abs_of_nonneg hfac0]
    have hfaclt : (1 : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) < 1 := by
      linarith [one_div_pos.mpr (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
    have hznorm : ‖(z : ℂ)‖ ≤ r := by
      simpa only [mem_closedBall, dist_zero_right] using hzclosed
    calc
      ((1 : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) * ‖(z : ℂ)‖ ≤
          ((1 : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) * r :=
        mul_le_mul_of_nonneg_left hznorm hfac0
      _ < 1 * r := mul_lt_mul_of_pos_right hfaclt hr0
      _ = r := one_mul r
  let zseq : ℕ → K := fun n ↦
    ⟨((1 - 1 / ((n + 1 : ℕ) : ℝ)) : ℝ) • (z : ℂ),
      ball_subset_closedBall (hinside n)⟩
  have hzseq : Tendsto zseq atTop (nhds z) := by
    rw [tendsto_subtype_rng]
    exact hzlim
  have hvlim : Tendsto (fun n ↦ v (zseq n)) atTop (nhds (v z)) :=
    v.continuous.continuousAt.tendsto.comp hzseq
  have hulim : Tendsto (fun n ↦ uLim (zseq n)) atTop (nhds (uLim z)) :=
    uLim.continuous.continuousAt.tendsto.comp hzseq
  apply tendsto_nhds_unique hvlim
  apply hulim.congr'
  filter_upwards [] with n
  have hn := hinside n
  have heq := heqOn hn
  rw [extension_apply v (ball_subset_closedBall hn),
    extension_apply uLim (ball_subset_closedBall hn)] at heq
  exact heq.symm

/-- The pointwise limit selected by completeness.  The Vitali theorem below
proves that local boundedness upgrades it to a locally uniform analytic limit. -/
def limit (f : ℕ → ℂ → ℂ) (z : ℂ) : ℂ :=
  limUnder atTop (fun n ↦ f n z)

/-- Vitali convergence on a disk, in the form used by the cluster expansion:
analytic functions which are uniformly bounded on every smaller closed disk
and converge on the real diameter converge locally uniformly to an analytic
function on the full disk. -/
theorem analytic_limit_and_tendstoLocallyUniformlyOn
    {f : ℕ → ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (ball 0 R))
    (hbounded : ∀ r, 0 ≤ r → r < R → ∃ C, 0 ≤ C ∧
      ∀ n z, z ∈ closedBall (0 : ℂ) r → ‖f n z‖ ≤ C)
    (g : ℝ → ℂ)
    (hreal : ∀ x : ℝ, |x| < R →
      Tendsto (fun n ↦ f n (x : ℂ)) atTop (nhds (g x))) :
    AnalyticOnNhd ℂ (limit f) (ball 0 R) ∧
      TendstoLocallyUniformlyOn f (limit f) atTop (ball 0 R) ∧
      ∀ x : ℝ, |x| < R → limit f (x : ℂ) = g x := by
  let F : ℂ → ℂ := limit f
  have hpoint (z : ℂ) (hz : z ∈ ball 0 R) :
      Tendsto (fun n ↦ f n z) atTop (nhds (F z)) := by
    obtain ⟨t, ht0, htR, hzt⟩ : ∃ t : ℝ, 0 < t ∧ t < R ∧ z ∈ closedBall 0 t := by
      refine ⟨(‖z‖ + R) / 2, ?_, ?_, ?_⟩
      · positivity
      · rw [mem_ball, dist_zero_right] at hz
        linarith
      · rw [mem_closedBall, dist_zero_right]
        rw [mem_ball, dist_zero_right] at hz
        linarith
    obtain ⟨v, hv⟩ := exists_uniform_limit_closedBall hf hbounded g hreal ht0 htR
    have hval := (BoundedContinuousFunction.lipschitz_eval_const
      ⟨z, hzt⟩).continuous.continuousAt.tendsto.comp hv
    exact (hval.cauchySeq.tendsto_limUnder :
      Tendsto (fun n ↦ f n z) atTop (nhds (F z)))
  have hcompactUniform (K : Set ℂ) (hK : K ⊆ ball 0 R)
      (hKcompact : IsCompact K) : TendstoUniformlyOn f F atTop K := by
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact tendstoUniformlyOn_empty
    obtain ⟨zmax, hzmax, hzmaxBound⟩ := hKcompact.exists_isMaxOn hKne
      continuous_norm.continuousOn
    let t : ℝ := (‖zmax‖ + R) / 2
    have hzmaxR : ‖zmax‖ < R := by
      simpa only [mem_ball, dist_zero_right] using hK hzmax
    have ht0 : 0 < t := by
      dsimp [t]
      exact div_pos (add_pos_of_nonneg_of_pos (norm_nonneg _) hR) (by norm_num)
    have htR : t < R := by dsimp [t]; linarith
    have hKt : K ⊆ closedBall (0 : ℂ) t := by
      intro z hz
      rw [mem_closedBall, dist_zero_right]
      exact (hzmaxBound hz).trans (by dsimp [t]; linarith)
    obtain ⟨v, hv⟩ := exists_uniform_limit_closedBall hf hbounded g hreal ht0 htR
    have hvUniform := tendstoUniformlyOn_extension_of_tendsto_restriction
      (fun n ↦ (hf n).continuousOn.mono (closedBall_subset_ball htR)) hv
    apply (hvUniform.mono hKt).congr_right
    intro z hz
    exact tendsto_nhds_unique (hpoint z (hK hz))
      (hvUniform.tendsto_at (hKt hz)) |>.symm
  refine ⟨?_, ?_, ?_⟩
  · have hloc : TendstoLocallyUniformlyOn f F atTop (ball 0 R) := by
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball]
      exact hcompactUniform
    exact hloc.differentiableOn
        (Eventually.of_forall fun n ↦ (hf n).differentiableOn) isOpen_ball
      |>.analyticOnNhd isOpen_ball
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball]
    exact hcompactUniform
  · intro x hx
    exact tendsto_nhds_unique (hpoint x (by
      simpa [mem_ball, dist_zero_left, Complex.norm_real] using hx)) (hreal x hx)

end

end VitaliOnDisk

end YangMills
