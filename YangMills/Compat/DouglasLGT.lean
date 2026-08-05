/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import YangMills.Compat.DouglasDobrushin
import YangMills.Compat.DouglasGeometry
import YangMills.Compat.DouglasGibbs

/-!
# Compatibility boundary for Michael R. Douglas's `LGT`

This convenience umbrella imports the three narrow upstream adapters. New code
should import `DouglasGeometry`, `DouglasGibbs`, or `DouglasDobrushin` directly.
Core generic modules must not import any compatibility module.

Upstream: <https://github.com/mrdouglasny/lgt>
Pinned commit: `b8793ccf6a51e00e9e2b1685ba191b8626e37137`
License: Apache-2.0
-/
