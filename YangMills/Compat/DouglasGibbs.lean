/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import LGT.Gibbs.YMIsGibbs

/-!
# Gibbs compatibility with Douglas `LGT`

This is the narrow import boundary for the upstream product Haar measure,
finite periodic Wilson measure, configuration gluing, Gibbs specification, and
DLR theorem.

Upstream: <https://github.com/mrdouglasny/lgt>
Pinned commit: `b8793ccf6a51e00e9e2b1685ba191b8626e37137`
License: Apache-2.0

All imported constructions remain specialized to a finite periodic torus, the
upstream `HasGaugeTrace` Wilson observable, and real nonnegative coupling.
-/

namespace YangMills.Compat.Douglas

/-- The native upstream periodic gauge-connection type. -/
abbrev PeriodicConnection := GaugeConnection

end YangMills.Compat.Douglas
