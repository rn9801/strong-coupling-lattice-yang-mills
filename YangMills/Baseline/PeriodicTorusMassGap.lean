/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Compat.DouglasDobrushin

/-!
# Douglas periodic-torus regression baseline

This file deliberately stays in the upstream model. It proves that the pinned
Douglas mass-gap and DLR theorems remain available unchanged. It is not the
general local-observable or infinite-volume theorem targeted by this project.
-/

namespace YangMills.Baseline

/-- Regression alias for Douglas's finite-periodic-torus strong-coupling bound. -/
theorem douglas_periodicTorus_massGap_regression
    (n : ℕ) (hn : 1 ≤ n)
    (d N : ℕ) (hd : 2 ≤ d) (hN : 2 < N) [NeZero N]
    [CompactSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    [SecondCountableTopology (Matrix.unitaryGroup (Fin n) ℂ)]
    [HasHaarProbability (Matrix.unitaryGroup (Fin n) ℂ)]
    [Fintype (LatticeLink d N)]
    (β : ℝ) (hβ : 0 ≤ β)
    (hβ_small : β < 1 / (4 * ↑n * ↑(maxNeighbors d)))
    (plaq : Finset (LatticePlaquette d N))
    (p q : LatticePlaquette d N) :
    |connected2pt (Matrix.unitaryGroup (Fin n) ℂ) n d N β plaq
        (plaqObs (Matrix.unitaryGroup (Fin n) ℂ) n d N p)
        (plaqObs (Matrix.unitaryGroup (Fin n) ℂ) n d N q)| ≤
      32 * (↑n : ℝ) ^ 2 / (1 - dobrushinAlpha n d β) *
        dobrushinAlpha n d β ^ ((latticePlaquetteDist d N p q - 1) / 2) := by
  classical
  exact ym_mass_gap_exponential_decay n hn d N hd hN β hβ hβ_small plaq p q

/-- Regression alias for the upstream finite-volume Gibbs/DLR theorem. -/
theorem douglas_ymMeasure_isGibbs_regression
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [HasHaarProbability G]
    (n d N : ℕ) [HasGaugeTrace G n] [Fintype (LatticeLink d N)]
    [DecidableEq (LatticeLink d N)]
    (plaq : Finset (LatticePlaquette d N))
    (β : ℝ) (hβ : 0 ≤ β)
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hIntegrable_w : MeasureTheory.Integrable
      (fun U => boltzmannWeight G n d N β U plaq) (productHaar G d N))
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (hZcond_pos : ∀ (Λ : Finset (LatticeLink d N)) (σ : GaugeConnection G d N),
      0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_integrable_cond : ∀ (Λ : Finset (LatticeLink d N))
      (σ : GaugeConnection G d N),
      MeasureTheory.Integrable
        (fun uΛ : LatticeLink d N → G =>
          gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
        (MeasureTheory.Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (hmeas_condDist : ∀ (Λ : Finset (LatticeLink d N))
      (A : Set (GaugeConnection G d N)), MeasurableSet A →
      Measurable (fun σ : GaugeConnection G d N =>
        (gibbsCondMeasure G n d N plaq β Λ σ A).toReal))
    (hZcond_meas : ∀ Λ : Finset (LatticeLink d N),
      Measurable (fun σ : GaugeConnection G d N =>
        gibbsConditionalZ G n d N plaq β Λ σ))
    (hinner_meas : ∀ (Λ : Finset (LatticeLink d N))
      (A : Set (GaugeConnection G d N)), MeasurableSet A →
      Measurable (fun σ : GaugeConnection G d N =>
        ∫ uΛ, Set.indicator A
            (fun U => boltzmannWeight G n d N β U plaq)
            (gluedConfig G d N Λ uΛ σ) ∂(productHaar G d N)))
    (hindA_fub_int : ∀ (A : Set (GaugeConnection G d N)), MeasurableSet A →
      MeasureTheory.Integrable
        (Set.indicator A (fun U => boltzmannWeight G n d N β U plaq))
        (productHaar G d N))
    (hinner_w_over_Z_int : ∀ (Λ : Finset (LatticeLink d N))
      (A : Set (GaugeConnection G d N)), MeasurableSet A →
      MeasureTheory.Integrable (fun σ : GaugeConnection G d N =>
        (∫ uΛ, Set.indicator A
            (fun U => boltzmannWeight G n d N β U plaq)
            (gluedConfig G d N Λ uΛ σ) ∂(productHaar G d N)) /
          gibbsConditionalZ G n d N plaq β Λ σ *
          boltzmannWeight G n d N β σ plaq)
        (productHaar G d N))
    (hμ_prob : MeasureTheory.IsProbabilityMeasure (ymMeasure G n d N β plaq)) :
    @IsGibbsMeasure _ _ _ _
      (ymGibbsSpec G n d N plaq β
        hZcond_pos hw_meas hw_integrable_cond hmeas_condDist)
      (ymMeasure G n d N β plaq) hμ_prob := by
  exact ymMeasure_isGibbs G n d N plaq β hβ hTrace_upper hTrace_lower
    hIntegrable_w hw_meas hZcond_pos hw_integrable_cond hmeas_condDist
    hZcond_meas hinner_meas hindA_fub_int hinner_w_over_Z_int hμ_prob

end YangMills.Baseline
