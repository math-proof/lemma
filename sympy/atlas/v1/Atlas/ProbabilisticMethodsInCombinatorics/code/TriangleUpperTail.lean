/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TriangleUpperTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option maxHeartbeats 400000

noncomputable section

open Filter Asymptotics Real

namespace TriangleUpperTail

/-- Probability that the Erdős–Rényi random graph $G(n, p)$ has at least
$(1 + \delta) \binom{n}{3} p^3$ triangles (the upper tail event). -/
end TriangleUpperTail
