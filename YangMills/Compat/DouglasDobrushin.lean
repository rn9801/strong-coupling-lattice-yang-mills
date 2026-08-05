/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import LGT.Gibbs.YMDobrushin
import LGT.MassGap.StrongCoupling
import YangMills.Compat.DouglasGeometry
import YangMills.Compat.DouglasGibbs

/-!
# Dobrushin compatibility with Douglas `LGT`

This is the narrow import boundary for the upstream influence estimates,
Dobrushin condition, graph-distance support theorem, and finite-periodic-torus
mass-gap results.

Upstream: <https://github.com/mrdouglasny/lgt>
Pinned commit: `b8793ccf6a51e00e9e2b1685ba191b8626e37137`
License: Apache-2.0

The headline theorem controls two plaquette trace observables on `(ZMod N)^d`.
It does not establish the roadmap's general local-observable cluster theorem,
box boundary mixing, thermodynamic limit, analyticity, or area law.
-/

namespace YangMills.Compat.Douglas

/-- Project-facing name for the upstream Dobrushin column-sum parameter. -/
noncomputable abbrev periodicDobrushinAlpha := dobrushinAlpha

end YangMills.Compat.Douglas
