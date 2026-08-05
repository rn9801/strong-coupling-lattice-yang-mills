/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Milestone 0 Mathlib smoke checks

These checks pin the APIs that the foundational phases are expected to use.
They intentionally contain no project theorem architecture.
-/

#check MeasureTheory.MeasurePreserving
#check MeasureTheory.Measure.pi
#check MeasureTheory.Measure.prod
#check MeasureTheory.IsProbabilityMeasure
#check Complex.exp
#check ContinuousMap
