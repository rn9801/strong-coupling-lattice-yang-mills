/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Baseline.PeriodicTorusMassGap

/-!
# Douglas declaration and axiom audit

Build this module directly to print the exact declaration signatures and axiom
footprints selected for the compatibility baseline.
-/

#check LatticeLink
#check LatticePlaquette
#check LatticePlaquette.boundaryLinks
#check plaquetteHolonomy
#check holonomy_gauge_covariant
#check productHaar
#check partitionFn
#check ymMeasure
#check ymMeasure_isProbabilityMeasure
#check plaquetteHolonomy_dependsOn
#check integral_mul_of_disjoint_dependsOn
#check gluedConfig
#check glue_measurePreserving
#check integral_glue_split_eq
#check ymGibbsSpec
#check ymMeasure_isGibbs
#check ymDobrushinCondition
#check linkGraphDist
#check linkGraphDist_support
#check boundary_sum_bound
#check ym_mass_gap_exponential_decay
#check ym_mass_gap_rate_exists
#check YangMills.Compat.Douglas.periodicPlaquetteSupportSet_eq_upstream
#check YangMills.Compat.Douglas.periodicPlaquetteDistance_support_lowerBound

#print axioms ymMeasure_isProbabilityMeasure
#print axioms ymMeasure_isGibbs
#print axioms ymDobrushinCondition
#print axioms ym_mass_gap_exponential_decay
#print axioms ym_mass_gap_rate_exists
#print axioms YangMills.Baseline.douglas_periodicTorus_massGap_regression
#print axioms YangMills.Baseline.douglas_ymMeasure_isGibbs_regression
#print axioms YangMills.Compat.Douglas.periodicPlaquetteSupportSet_eq_upstream
#print axioms YangMills.Compat.Douglas.periodicPlaquetteDistance_support_lowerBound
