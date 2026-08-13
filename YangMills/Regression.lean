/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills
import YangMills.Audit.DouglasAxioms
import YangMills.Audit.MathlibSmoke
import YangMills.Baseline.PeriodicTorusMassGap
import YangMills.Compat.DouglasLGT
import YangMills.StrongCoupling.BoundaryDecay
import YangMills.StrongCoupling.BoxDobrushin
import YangMills.Tests.Milestone1
import YangMills.Tests.Milestone2
import YangMills.Tests.Milestone3
import YangMills.Tests.Milestone4
import YangMills.Tests.Milestone5
import YangMills.Tests.Milestone6
import YangMills.Tests.Milestone7
import YangMills.Tests.Milestone8
import YangMills.Tests.Milestone9
import YangMills.Tests.Milestone10Foundations
import YangMills.Tests.Milestones11To13Foundations
import YangMills.Tests.Milestone14
import YangMills.Tests.Milestone16
import YangMills.Tests.Milestone17
import YangMills.Tests.Milestone18
import YangMills.Tests.Milestone19
import YangMills.Tests.ReviewerSmoke

/-!
# Comprehensive regression umbrella

This opt-in root compiles every milestone regression together with the
periodic-torus Douglas baseline and the older finite-box Dobrushin comparison
route.  None of these imports is needed by the project-native cluster proofs
of the thermodynamic limit, clustering, analyticity, pressure, or area law.

Use `lake build +YangMills.Regression` before merging a release or changing a
shared foundational API.  For ordinary development, `lake build` checks the
smaller public root `YangMills`.
-/
