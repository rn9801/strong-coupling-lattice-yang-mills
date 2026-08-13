/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.StrongCoupling.WilsonAreaLaw

/-! Executable regressions for Milestone 16: center-charged Wilson area law. -/

namespace YangMills.Tests

open Gauge Lattice.Cubic StrongCoupling Wilson

noncomputable section

variable {d n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [CompactSpace G] [T2Space G]
  [GaugeHaarProbability G]
  {rho : ContinuousUnitaryRepData G n}

example (m : ℕ) (hm : m ≠ 1) (x : Site d)
    (i j : Fin d) (hij : i ≠ j) (R T : ℕ)
    (a b : Plaquette d →₀ ℕ)
    (h : TaylorScreens m (Path.rectangleBoundary x i j R T) a b) :
    R * T ≤ taylorOrder a b :=
  rectangle_area_le_taylorOrder_of_taylorScreens m hm x i j hij R T a b h

example (kappa : FiniteCenterChargeData rho)
    (Lambda : FiniteSpecification d G) (x : Site d)
    (i j : Fin d) (hij : i ≠ j) (R T N : ℕ)
    (hC : (Path.rectangleBoundary x i j R T).edgeSupport ⊆
      Lambda.dynamicEdges)
    (hactive : ∀ p ∈ Lambda.activePlaquettes,
      p.boundary.edgeSupport ⊆ Lambda.dynamicEdges)
    (hN : N < R * T) :
    iteratedDeriv N
      (complexGibbsExpectation
        (rho.wilsonLoop (Path.rectangleBoundary x i j R T))
        Lambda rho.wilsonPotential) 0 = 0 :=
  iteratedDeriv_complexGibbsExpectation_wilsonRectangle_zero_of_lt_area
    kappa Lambda x i j hij R T N hC hactive hN

example (kappa : FiniteCenterChargeData rho) (x : Site d)
    (i j : Fin d) (hij : i ≠ j) (R T : ℕ)
    (eta : ℕ → Configuration d G) {r : ℝ} (hr0 : 0 < r)
    (hr : r < latticeStrongCouplingRadius d rho.wilsonPotential.bound)
    (beta : ℂ) (hbeta : ‖beta‖ < r) :
    ‖analyticInfiniteVolumeLocalExpectation
        (rho.wilsonLoop (Path.rectangleBoundary x i j R T))
        eta rho.wilsonPotential beta‖ ≤
      wilsonAreaPerimeterConstant (d := d) rho.wilsonPotential r ^
          (2 * (R + T)) *
        Real.exp (-Real.log (r / ‖beta‖) * (R * T)) :=
  norm_analyticInfiniteVolumeWilsonRectangle_le_areaLaw
    kappa x i j hij R T eta hr0 hr beta hbeta

example (kappa : FiniteCenterChargeData rho) (x : Site d)
    (i j : Fin d) (hij : i ≠ j) (R T : ℕ)
    (eta : ℕ → Configuration d G) {r : ℝ} (hr0 : 0 < r)
    (hr : r < latticeStrongCouplingRadius d rho.wilsonPotential.bound)
    (beta : ℝ) (hbeta : |beta| < r) :
    ‖∫ A, rho.wilsonLoop (Path.rectangleBoundary x i j R T) A
        ∂centeredInfiniteVolumeMeasure eta rho.wilsonPotential beta
          (by simpa [Complex.norm_real] using hbeta.trans hr)‖ ≤
      wilsonAreaPerimeterConstant (d := d) rho.wilsonPotential r ^
          (2 * (R + T)) *
        Real.exp (-Real.log (r / |beta|) * (R * T)) :=
  norm_integral_wilsonRectangle_le_areaLaw
    kappa x i j hij R T eta hr0 hr beta hbeta

#print axioms
  YangMills.Lattice.Cubic.rectangle_area_le_taylorOrder_of_taylorScreens
#print axioms
  YangMills.StrongCoupling.iteratedDeriv_complexGibbsExpectation_wilsonRectangle_zero_of_lt_area
#print axioms
  YangMills.StrongCoupling.iteratedDeriv_analyticInfiniteVolumeWilsonRectangle_zero_of_lt_area
#print axioms
  YangMills.StrongCoupling.norm_analyticInfiniteVolumeWilsonRectangle_le_areaPower
#print axioms
  YangMills.StrongCoupling.norm_analyticInfiniteVolumeWilsonRectangle_le_areaLaw
#print axioms
  YangMills.StrongCoupling.norm_integral_wilsonRectangle_le_areaLaw

end

end YangMills.Tests
