/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Gauge.FiniteEdgeHaar
import YangMills.Gauge.LinkReflectionPositivity
import YangMills.Gauge.SiteReflectionPositivity
import YangMills.StrongCoupling.ThermodynamicPressure
import YangMills.StrongCoupling.WilsonAreaLaw

/-!
# Strong-coupling lattice Yang--Mills theory

The public root import for the project-native theory.  It exports the finite
Haar/gauge layer, site and link reflection positivity, thermodynamic pressure, and the
strong-coupling Wilson area law; their transitive imports contain the native
foundations and cluster expansion.

The optional Douglas/Dobrushin comparison route, axiom audits, and milestone
regressions live behind `YangMills.Regression`.  Keeping that upstream stack
out of this root makes ordinary incremental builds substantially smaller.
-/
